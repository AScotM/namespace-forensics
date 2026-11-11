package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"syscall"
	"time"
)

const version = "1.0.0"

var nsTypes = []string{"cgroup", "ipc", "mnt", "net", "pid", "pid_for_children", "time", "time_for_children", "user", "uts"}

type Namespace struct {
	Type string `json:"type"`
	ID   string `json:"id"`
}
type Process struct {
	PID            int               `json:"pid"`
	PPID           int               `json:"ppid"`
	Name           string            `json:"name"`
	Cmdline        string            `json:"cmdline,omitempty"`
	UID            string            `json:"uid,omitempty"`
	GID            string            `json:"gid,omitempty"`
	State          string            `json:"state,omitempty"`
	Threads        int               `json:"threads,omitempty"`
	NSpid          string            `json:"nspid,omitempty"`
	NoNewPrivs     string            `json:"no_new_privs,omitempty"`
	Seccomp        string            `json:"seccomp,omitempty"`
	SeccompFilters string            `json:"seccomp_filters,omitempty"`
	CapEff         string            `json:"cap_eff,omitempty"`
	CapBnd         string            `json:"cap_bnd,omitempty"`
	CapPrm         string            `json:"cap_prm,omitempty"`
	CapAmb         string            `json:"cap_amb,omitempty"`
	SELinux        string            `json:"selinux,omitempty"`
	Cgroups        []string          `json:"cgroups,omitempty"`
	Namespaces     map[string]string `json:"namespaces"`
	Root           string            `json:"root,omitempty"`
	Exe            string            `json:"exe,omitempty"`
	ContainerHint  string            `json:"container_hint,omitempty"`
	Errors         []string          `json:"errors,omitempty"`
}
type Group struct {
	Type       string `json:"type"`
	ID         string `json:"id"`
	PIDs       []int  `json:"pids"`
	Members    int    `json:"members"`
	SharesHost bool   `json:"shares_host"`
}
type Finding struct {
	Severity string `json:"severity"`
	Code     string `json:"code"`
	PID      int    `json:"pid,omitempty"`
	Message  string `json:"message"`
}
type Container struct {
	ID     string `json:"id"`
	Name   string `json:"name"`
	PID    int    `json:"pid"`
	Image  string `json:"image,omitempty"`
	Status string `json:"status,omitempty"`
	Engine string `json:"engine"`
}
type Snapshot struct {
	Version        string            `json:"version"`
	Timestamp      time.Time         `json:"timestamp"`
	Hostname       string            `json:"hostname"`
	Kernel         string            `json:"kernel"`
	HostNamespaces map[string]string `json:"host_namespaces"`
	Processes      []Process         `json:"processes"`
	Groups         []Group           `json:"groups"`
	Findings       []Finding         `json:"findings"`
	Containers     []Container       `json:"containers,omitempty"`
	ScanErrors     []string          `json:"scan_errors,omitempty"`
	Fingerprint    string            `json:"fingerprint"`
}
type Change struct {
	Kind   string `json:"kind"`
	PID    int    `json:"pid,omitempty"`
	Field  string `json:"field,omitempty"`
	Before string `json:"before,omitempty"`
	After  string `json:"after,omitempty"`
}
type Diff struct {
	Previous string   `json:"previous"`
	Current  string   `json:"current"`
	Changes  []Change `json:"changes"`
}
type options struct {
	command    string
	output     string
	input      string
	baseline   string
	interval   time.Duration
	count      int
	limit      int
	pid        int
	includeCmd bool
	podman     bool
	all        bool
	strict     bool
}

func readTrim(path string) (string, error) {
	b, e := os.ReadFile(path)
	if e != nil {
		return "", e
	}
	return strings.TrimSpace(string(b)), nil
}
func link(path string) string {
	s, e := os.Readlink(path)
	if e != nil {
		return ""
	}
	return s
}
func parseStatus(path string) (map[string]string, error) {
	f, e := os.Open(path)
	if e != nil {
		return nil, e
	}
	defer f.Close()
	m := map[string]string{}
	s := bufio.NewScanner(f)
	s.Buffer(make([]byte, 4096), 1024*1024)
	for s.Scan() {
		p := strings.SplitN(s.Text(), ":", 2)
		if len(p) == 2 {
			m[p[0]] = strings.TrimSpace(p[1])
		}
	}
	return m, s.Err()
}
func parseInt(s string) int { n, _ := strconv.Atoi(strings.Fields(s)[0]); return n }
func safeInt(s string) int {
	f := strings.Fields(s)
	if len(f) == 0 {
		return 0
	}
	n, _ := strconv.Atoi(f[0])
	return n
}
func kernel() string {
	b, e := readTrim("/proc/sys/kernel/osrelease")
	if e != nil {
		return "unknown"
	}
	return b
}
func hostNamespaces() map[string]string {
	m := map[string]string{}
	for _, t := range nsTypes {
		if v := link("/proc/1/ns/" + t); v != "" {
			m[t] = v
		}
	}
	return m
}
func procPIDs() ([]int, error) {
	d, e := os.ReadDir("/proc")
	if e != nil {
		return nil, e
	}
	var out []int
	for _, x := range d {
		n, e := strconv.Atoi(x.Name())
		if e == nil && n > 0 {
			out = append(out, n)
		}
	}
	sort.Ints(out)
	return out, nil
}
func getCgroups(pid int) []string {
	b, e := readTrim(fmt.Sprintf("/proc/%d/cgroup", pid))
	if e != nil {
		return nil
	}
	if b == "" {
		return nil
	}
	return strings.Split(b, "\n")
}
func hint(p Process) string {
	s := strings.ToLower(strings.Join(p.Cgroups, " ") + " " + p.Cmdline)
	switch {
	case strings.Contains(s, "libpod-"):
		return "podman"
	case strings.Contains(s, "docker-") || strings.Contains(s, "/docker/"):
		return "docker"
	case strings.Contains(s, "kubepods"):
		return "kubernetes"
	case strings.Contains(s, "lxc"):
		return "lxc"
	case strings.Contains(s, "containerd"):
		return "containerd"
	}
	return ""
}
func collectProcess(pid int, cmd bool) (Process, error) {
	base := fmt.Sprintf("/proc/%d", pid)
	p := Process{PID: pid, Namespaces: map[string]string{}}
	m, e := parseStatus(base + "/status")
	if e != nil {
		return p, e
	}
	p.Name = m["Name"]
	p.State = m["State"]
	p.PPID = safeInt(m["PPid"])
	p.UID = m["Uid"]
	p.GID = m["Gid"]
	p.Threads = safeInt(m["Threads"])
	p.NSpid = m["NSpid"]
	p.NoNewPrivs = m["NoNewPrivs"]
	p.Seccomp = m["Seccomp"]
	p.SeccompFilters = m["Seccomp_filters"]
	p.CapEff = m["CapEff"]
	p.CapBnd = m["CapBnd"]
	p.CapPrm = m["CapPrm"]
	p.CapAmb = m["CapAmb"]
	for _, t := range nsTypes {
		if v := link(base + "/ns/" + t); v != "" {
			p.Namespaces[t] = v
		}
	}
	if cmd {
		if b, e := os.ReadFile(base + "/cmdline"); e == nil {
			p.Cmdline = strings.TrimSpace(strings.ReplaceAll(string(b), "\x00", " "))
		}
	}
	p.Cgroups = getCgroups(pid)
	p.SELinux, _ = readTrim(base + "/attr/current")
	p.Root = link(base + "/root")
	p.Exe = link(base + "/exe")
	p.ContainerHint = hint(p)
	return p, nil
}
func podmanContainers() ([]Container, error) {
	path, e := exec.LookPath("podman")
	if e != nil {
		return nil, e
	}
	cmd := exec.Command(path, "ps", "--all", "--format", "json")
	b, e := cmd.Output()
	if e != nil {
		return nil, e
	}
	var raw []map[string]any
	if e = json.Unmarshal(b, &raw); e != nil {
		return nil, e
	}
	out := []Container{}
	for _, v := range raw {
		c := Container{Engine: "podman", ID: asString(v["Id"]), Name: asString(v["Names"]), Image: asString(v["Image"]), Status: asString(v["Status"])}
		if c.ID == "" {
			c.ID = asString(v["ID"])
		}
		if c.Name == "" {
			c.Name = asString(v["Names"])
		}
		if names, ok := v["Names"].([]any); ok && len(names) > 0 {
			c.Name = asString(names[0])
		}
		if id, ok := v["Pid"].(float64); ok {
			c.PID = int(id)
		}
		out = append(out, c)
	}
	return out, nil
}
func asString(v any) string {
	if v == nil {
		return ""
	}
	return fmt.Sprint(v)
}
func groups(ps []Process, host map[string]string) []Group {
	m := map[string]*Group{}
	for _, p := range ps {
		for t, id := range p.Namespaces {
			k := t + "|" + id
			g := m[k]
			if g == nil {
				g = &Group{Type: t, ID: id, SharesHost: id == host[t]}
				m[k] = g
			}
			g.PIDs = append(g.PIDs, p.PID)
		}
	}
	out := make([]Group, 0, len(m))
	for _, g := range m {
		g.Members = len(g.PIDs)
		sort.Ints(g.PIDs)
		out = append(out, *g)
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].Type == out[j].Type {
			return out[i].ID < out[j].ID
		}
		return out[i].Type < out[j].Type
	})
	return out
}
func findings(ps []Process, host map[string]string) []Finding {
	var out []Finding
	for _, p := range ps {
		if p.ContainerHint == "" {
			continue
		}
		if p.Namespaces["net"] != "" && p.Namespaces["net"] == host["net"] {
			out = append(out, Finding{"info", "SHARED_HOST_NET", p.PID, "Container-associated process shares PID 1 network namespace"})
		}
		if p.Namespaces["pid"] != "" && p.Namespaces["pid"] == host["pid"] {
			out = append(out, Finding{"info", "SHARED_HOST_PID", p.PID, "Container-associated process shares PID 1 PID namespace"})
		}
		if p.Namespaces["mnt"] != "" && p.Namespaces["mnt"] == host["mnt"] {
			out = append(out, Finding{"info", "SHARED_HOST_MOUNT", p.PID, "Container-associated process shares PID 1 mount namespace"})
		}
		if p.NoNewPrivs == "0" {
			out = append(out, Finding{"info", "NO_NEW_PRIVS_DISABLED", p.PID, "NoNewPrivs is disabled; inspect policy before treating this as a risk"})
		}
		if p.Seccomp == "0" {
			out = append(out, Finding{"info", "SECCOMP_DISABLED", p.PID, "Seccomp filtering is disabled for this process"})
		}
		if p.Namespaces["user"] == host["user"] {
			out = append(out, Finding{"info", "SHARED_USER_NS", p.PID, "Process shares PID 1 user namespace"})
		}
	}
	sort.Slice(out, func(i, j int) bool {
		if out[i].PID == out[j].PID {
			return out[i].Code < out[j].Code
		}
		return out[i].PID < out[j].PID
	})
	return out
}
func fingerprint(s Snapshot) string {
	h := sha256.New()
	for _, p := range s.Processes {
		fmt.Fprintf(h, "%d:%s:%s:%s\n", p.PID, p.Name, p.CapEff, p.Seccomp)
		for _, t := range nsTypes {
			fmt.Fprintf(h, "%s=%s;", t, p.Namespaces[t])
		}
	}
	return hex.EncodeToString(h.Sum(nil))
}
func scan(o options) (Snapshot, error) {
	h, _ := os.Hostname()
	s := Snapshot{Version: version, Timestamp: time.Now().UTC(), Hostname: h, Kernel: kernel(), HostNamespaces: hostNamespaces(), Processes: []Process{}, Groups: []Group{}, Findings: []Finding{}}
	pids, e := procPIDs()
	if e != nil {
		return s, e
	}
	for _, pid := range pids {
		if o.pid > 0 && pid != o.pid {
			continue
		}
		p, e := collectProcess(pid, o.includeCmd)
		if e != nil {
			if o.strict {
				s.ScanErrors = append(s.ScanErrors, fmt.Sprintf("pid %d: %v", pid, e))
			}
			continue
		}
		s.Processes = append(s.Processes, p)
		if o.limit > 0 && len(s.Processes) >= o.limit {
			break
		}
	}
	s.Groups = groups(s.Processes, s.HostNamespaces)
	s.Findings = findings(s.Processes, s.HostNamespaces)
	if o.podman {
		c, e := podmanContainers()
		if e != nil {
			s.ScanErrors = append(s.ScanErrors, "podman: "+e.Error())
		} else {
			s.Containers = c
		}
	}
	s.Fingerprint = fingerprint(s)
	return s, nil
}
func save(path string, v any) error {
	if path == "" {
		return nil
	}
	b, e := json.MarshalIndent(v, "", "  ")
	if e != nil {
		return e
	}
	if path == "-" {
		_, e = os.Stdout.Write(append(b, '\n'))
		return e
	}
	dir := filepath.Dir(path)
	if e = os.MkdirAll(dir, 0750); e != nil {
		return e
	}
	f, e := os.CreateTemp(dir, ".namespace-forensics-*")
	if e != nil {
		return e
	}
	tmp := f.Name()
	defer os.Remove(tmp)
	if _, e = f.Write(append(b, '\n')); e != nil {
		f.Close()
		return e
	}
	if e = f.Sync(); e != nil {
		f.Close()
		return e
	}
	if e = f.Close(); e != nil {
		return e
	}
	return os.Rename(tmp, path)
}
func load(path string) (Snapshot, error) {
	var s Snapshot
	f, e := os.Open(path)
	if e != nil {
		return s, e
	}
	defer f.Close()
	e = json.NewDecoder(io.LimitReader(f, 128<<20)).Decode(&s)
	return s, e
}
func compare(a, b Snapshot) Diff {
	d := Diff{Previous: a.Timestamp.Format(time.RFC3339), Current: b.Timestamp.Format(time.RFC3339), Changes: []Change{}}
	am := map[int]Process{}
	bm := map[int]Process{}
	for _, p := range a.Processes {
		am[p.PID] = p
	}
	for _, p := range b.Processes {
		bm[p.PID] = p
	}
	for pid, p := range bm {
		old, ok := am[pid]
		if !ok {
			d.Changes = append(d.Changes, Change{Kind: "process_added", PID: pid, After: p.Name})
			continue
		}
		if old.Name != p.Name {
			d.Changes = append(d.Changes, Change{Kind: "process_replaced", PID: pid, Before: old.Name, After: p.Name})
		}
		for _, t := range nsTypes {
			if old.Namespaces[t] != p.Namespaces[t] {
				d.Changes = append(d.Changes, Change{Kind: "namespace_changed", PID: pid, Field: t, Before: old.Namespaces[t], After: p.Namespaces[t]})
			}
		}
		for _, f := range []struct{ name, x, y string }{{"seccomp", old.Seccomp, p.Seccomp}, {"cap_eff", old.CapEff, p.CapEff}, {"no_new_privs", old.NoNewPrivs, p.NoNewPrivs}, {"selinux", old.SELinux, p.SELinux}, {"cgroup", strings.Join(old.Cgroups, "|"), strings.Join(p.Cgroups, "|")}} {
			if f.x != f.y {
				d.Changes = append(d.Changes, Change{Kind: "security_changed", PID: pid, Field: f.name, Before: f.x, After: f.y})
			}
		}
	}
	for pid, p := range am {
		if _, ok := bm[pid]; !ok {
			d.Changes = append(d.Changes, Change{Kind: "process_removed", PID: pid, Before: p.Name})
		}
	}
	sort.Slice(d.Changes, func(i, j int) bool {
		if d.Changes[i].PID == d.Changes[j].PID {
			return d.Changes[i].Kind < d.Changes[j].Kind
		}
		return d.Changes[i].PID < d.Changes[j].PID
	})
	return d
}
func printSummary(s Snapshot, o options) {
	fmt.Printf("NAMESPACE FORENSICS %s\nHost: %s  Kernel: %s  Time: %s\nProcesses: %d  Namespace groups: %d  Findings: %d  Scan errors: %d\nFingerprint: %s\n", s.Version, s.Hostname, s.Kernel, s.Timestamp.Format(time.RFC3339), len(s.Processes), len(s.Groups), len(s.Findings), len(s.ScanErrors), s.Fingerprint)
	fmt.Println("\nNAMESPACE TOPOLOGY")
	fmt.Printf("%-18s %-20s %8s %8s\n", "TYPE", "IDENTIFIER", "MEMBERS", "HOST")
	for _, g := range s.Groups {
		fmt.Printf("%-18s %-20s %8d %8t\n", g.Type, g.ID, g.Members, g.SharesHost)
	}
	if o.all || o.pid > 0 {
		fmt.Println("\nPROCESSES")
		fmt.Printf("%-8s %-8s %-22s %-8s %-8s %-12s %s\n", "PID", "PPID", "NAME", "SECCOMP", "NNP", "CONTAINER", "CGROUP")
		for _, p := range s.Processes {
			cg := ""
			if len(p.Cgroups) > 0 {
				cg = p.Cgroups[0]
			}
			fmt.Printf("%-8d %-8d %-22.22s %-8s %-8s %-12s %.90s\n", p.PID, p.PPID, p.Name, p.Seccomp, p.NoNewPrivs, p.ContainerHint, cg)
		}
	}
	if len(s.Containers) > 0 {
		fmt.Println("\nPODMAN CONTAINERS")
		for _, c := range s.Containers {
			fmt.Printf("%-20s %-20s %s\n", c.ID, c.Name, c.Status)
		}
	}
	if len(s.Findings) > 0 {
		fmt.Println("\nISOLATION OBSERVATIONS")
		n := len(s.Findings)
		if !o.all && n > 40 {
			n = 40
		}
		for _, f := range s.Findings[:n] {
			fmt.Printf("[%s] pid=%d %s: %s\n", f.Severity, f.PID, f.Code, f.Message)
		}
		if n < len(s.Findings) {
			fmt.Printf("... %d more; use --all\n", len(s.Findings)-n)
		}
	}
	for _, e := range s.ScanErrors {
		fmt.Fprintln(os.Stderr, "scan warning:", e)
	}
}
func printDiff(d Diff) {
	fmt.Printf("DRIFT %s -> %s: %d changes\n", d.Previous, d.Current, len(d.Changes))
	for _, c := range d.Changes {
		fmt.Printf("%-20s pid=%-8d %-18s %s -> %s\n", c.Kind, c.PID, c.Field, c.Before, c.After)
	}
}
func run(o options) error {
	switch o.command {
	case "scan":
		s, e := scan(o)
		if e != nil {
			return e
		}
		if o.output != "-" {
			printSummary(s, o)
		}
		return save(o.output, s)
	case "inspect":
		if o.pid <= 0 {
			return errors.New("inspect requires --pid")
		}
		o.all = true
		s, e := scan(o)
		if e != nil {
			return e
		}
		if len(s.Processes) == 0 {
			return errors.New("process not accessible")
		}
		if o.output != "-" {
			printSummary(s, o)
		}
		return save(o.output, s)
	case "diff":
		if o.baseline == "" || o.input == "" {
			return errors.New("diff requires --baseline and --input")
		}
		a, e := load(o.baseline)
		if e != nil {
			return e
		}
		b, e := load(o.input)
		if e != nil {
			return e
		}
		d := compare(a, b)
		if o.output != "-" {
			printDiff(d)
		}
		return save(o.output, d)
	case "watch":
		if o.interval <= 0 {
			return errors.New("interval must be positive")
		}
		sig := make(chan os.Signal, 1)
		signal.Notify(sig, syscall.SIGINT, syscall.SIGTERM)
		defer signal.Stop(sig)
		var prev *Snapshot
		for i := 0; o.count == 0 || i < o.count; i++ {
			s, e := scan(o)
			if e != nil {
				return e
			}
			if o.output != "-" {
				printSummary(s, o)
			}
			if prev != nil {
				d := compare(*prev, s)
				if o.output != "-" {
					printDiff(d)
				}
			}
			if o.output != "" {
				p := o.output
				if p != "-" {
					p = fmt.Sprintf("%s.%s.json", strings.TrimSuffix(o.output, ".json"), s.Timestamp.Format("20060102T150405.000000000"))
				}
				if e = save(p, s); e != nil {
					return e
				}
			}
			prev = &s
			if o.count > 0 && i+1 >= o.count {
				break
			}
			select {
			case <-sig:
				return nil
			case <-time.After(o.interval):
			}
		}
		return nil
	case "report":
		if o.input == "" {
			return errors.New("report requires --input")
		}
		s, e := load(o.input)
		if e != nil {
			return e
		}
		printSummary(s, o)
		return nil
	case "version":
		fmt.Println(version)
		return nil
	}
	return fmt.Errorf("unknown command %q", o.command)
}
func main() {
	o := options{}
	flag.StringVar(&o.output, "output", "", "JSON output file, or - for stdout")
	flag.StringVar(&o.input, "input", "", "input snapshot JSON")
	flag.StringVar(&o.baseline, "baseline", "", "baseline snapshot JSON")
	flag.DurationVar(&o.interval, "interval", 5*time.Second, "watch interval")
	flag.IntVar(&o.count, "count", 0, "watch sample count; 0 means unlimited")
	flag.IntVar(&o.limit, "limit", 0, "maximum processes to inspect; 0 means all")
	flag.IntVar(&o.pid, "pid", 0, "inspect only this PID")
	flag.BoolVar(&o.includeCmd, "cmdline", false, "collect command lines (potentially sensitive)")
	flag.BoolVar(&o.podman, "podman", false, "include Podman container inventory")
	flag.BoolVar(&o.all, "all", false, "show processes and all observations")
	flag.BoolVar(&o.strict, "strict", false, "record inaccessible process errors")
	flag.Usage = func() {
		fmt.Fprintln(os.Stderr, "namespace-forensics [scan|inspect|watch|diff|report|version] [options]")
		flag.PrintDefaults()
	}
	args := os.Args[1:]
	if len(args) > 0 && !strings.HasPrefix(args[0], "-") {
		o.command = args[0]
		args = args[1:]
	} else {
		o.command = "scan"
	}
	if e := flag.CommandLine.Parse(args); e != nil {
		os.Exit(2)
	}
	if e := run(o); e != nil {
		fmt.Fprintln(os.Stderr, "error:", e)
		os.Exit(1)
	}
}
