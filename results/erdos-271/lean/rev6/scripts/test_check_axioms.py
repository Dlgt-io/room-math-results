#!/usr/bin/env python3
"""Regression tests for scripts/check_axioms.py (strict exact-name audit, adopted round 34).
Synthetic logs only: these fixtures are NOT Lean compiler evidence. Run: python3 scripts/test_check_axioms.py [real_log]"""
import importlib.util, os, sys, unittest
sys.dont_write_bytecode=True
HERE=os.path.dirname(os.path.abspath(__file__))
spec=importlib.util.spec_from_file_location('ca',os.path.join(HERE,'check_axioms.py')); ca=importlib.util.module_from_spec(spec); spec.loader.exec_module(ca)
STD='[propext, Classical.choice, Quot.sound]'
def rep(n,ax=STD): return f"'{n}' depends on axioms: {ax}"
def log(names,ax=STD): return '\n'.join(rep(n,ax) for n in names)+'\n'
E=list(ca.EXPECTED)
REAL=sys.argv.pop(1) if len(sys.argv)>1 else None
class T(unittest.TestCase):
    def ok(self,t): r=ca.audit_text(t); self.assertEqual(r['status'],'PASS',r['problems'])
    def bad(self,t,frag=''):
        r=ca.audit_text(t); self.assertEqual(r['status'],'FAIL')
        if frag: self.assertTrue(any(frag in p for p in r['problems']),r['problems'])
    def test_exact_expected(self): self.assertEqual(len(E),26); self.assertEqual(len(set(E)),26); self.ok(log(E))   # rev 6 candidate: 24 + 2
    def test_duplicated_report_attack(self): self.bad(log([E[0]]*len(E)),'duplicate')       # the r4 finding
    def test_23_plus_duplicate(self): self.bad(log(E[:-1]+[E[0]]),'duplicate')
    def test_missing(self): self.bad(log(E[:-1]),'missing')
    def test_substituted(self): self.bad(log(E[:-1]+['Erdos271.Fake.thm']),'unexpected')
    def test_extra(self): self.bad(log(E+['Erdos271.Extra.thm']),'unexpected')
    def test_forbidden_axiom(self): self.bad(log(E[:-1])+rep(E[-1],'[propext, sorryAx]')+'\n','forbidden')
    def test_native_axiom(self): self.bad(log(E[:-1])+rep(E[-1],'[propext, Lean.ofReduceBool]')+'\n','forbidden')
    def test_truncated(self): self.bad(log(E[:-1])+f"'{E[-1]}' depends on axioms: [propext,")
    def test_error_line(self): self.bad(log(E)+"Composed.lean:1:0: error: unknown identifier\n",'error')
    def test_no_axiom_report(self): self.ok(log(E[:-1])+f"'{E[-1]}' does not depend on any axioms\n")
    def test_multiline_list(self): self.ok(log(E[:-1])+f"'{E[-1]}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n")
    def test_empty(self): self.bad('','missing')
    def test_interleaved_check_output(self):
        self.ok('\n'.join(f"{n} : True\n"+rep(n) for n in E)+'\n')
    def test_report_not_at_line_start(self): self.bad(log(E[:-1])+'x '+rep(E[-1])+'\n')
    def test_rev5_list_insufficient(self): self.bad(log(E[:24]),'missing')   # a rev-5 (24-name) log must fail the rev-6 list
    @unittest.skipIf(REAL is None,'no real log given')
    def test_real_log(self): self.ok(open(REAL,encoding='utf-8').read())
if __name__=='__main__': unittest.main(verbosity=1)
