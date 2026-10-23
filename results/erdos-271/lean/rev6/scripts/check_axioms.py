#!/usr/bin/env python3
from __future__ import annotations
import argparse
import collections
import json
import re
from pathlib import Path

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
EXPECTED = (
 'Erdos271.Final.erdos271_limsup',
 'Erdos271.Final.erdos271_ak',
 'Erdos271.Final.erdos271_limsup_any',
 'Erdos271.Final.erdos271_limsup_ge_any',
 'Erdos271.Final.erdos271_ak_any',
 'Erdos271.Stanley.stanley_limsup',
 'Erdos271.Stanley.stanley_ak',
 'Erdos271.Stanley.stanley_std_limsup',
 'Erdos271.Stanley.stanley_std_ak',
 'Erdos271.Stanley.two_seed_limsup',
 'Erdos271.Stanley.two_seed_ak',
 'Erdos271.IndependentEndgame.arbitrarily_large_witnesses',
 'Erdos271.IndependentEndgame.fixed_error_budget',
 'Erdos271.Liminf.StaticCert.liminf_of_cert',
 'Erdos271.Liminf.liminf_construction_1889',
 'Erdos271.Liminf.liminf_construction_1894',
 'Erdos271.Liminf.liminf_construction_1912',
 'Erdos271.Liminf.liminf_construction',
 'Erdos271.B16.B16_main',
 'Erdos271.B16.B16_exists',
 'Erdos271.B16.mem_iff_blocks',
 'Erdos271.B16.B16_limsup',
 'Erdos271.B16.S16_limsup',
 'ComposedC9.composed',
 'Erdos271.FiniteIntegrals.finite_weighted_integral_identity',
 'Erdos271.Liminf1675.liminf_construction_1675',
)
REPORT = re.compile(r"^'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$", re.M)

def audit_text(text: str) -> dict:
    problems = []
    if re.search(r'\b(error|panic|exception)\b', text, re.I):
        problems.append('error/panic/exception in transcript')
    reports = list(REPORT.finditer(text))
    names = [m.group(1) for m in reports]
    counts = collections.Counter(names)
    duplicates = sorted(n for n,c in counts.items() if c != 1)
    missing = sorted(set(EXPECTED)-set(names))
    unexpected = sorted(set(names)-set(EXPECTED))
    if duplicates: problems.append('duplicate theorem names: '+', '.join(duplicates))
    if missing: problems.append('missing theorem names: '+', '.join(missing))
    if unexpected: problems.append('unexpected theorem names: '+', '.join(unexpected))
    residue = REPORT.sub('',text)
    if 'depends on axioms' in residue or 'does not depend on any axioms' in residue:
        problems.append('malformed or truncated axiom report')
    axioms = {}
    for m in reports:
        ax = [s.strip() for s in (m.group(2) or '').split(',') if s.strip()]
        extra = sorted(set(ax)-ALLOWED)
        if extra: problems.append(f'{m.group(1)} has forbidden axioms: {extra}')
        axioms[m.group(1)] = sorted(set(ax))
    return {'status':'FAIL' if problems else 'PASS', 'expected_count':len(EXPECTED),
            'parsed_count':len(reports), 'unique_count':len(counts),
            'problems':problems, 'axioms':axioms}

def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument('transcript',type=Path)
    a=p.parse_args()
    result=audit_text(a.transcript.read_text(encoding='utf-8'))
    print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['status']=='PASS' else 1)

if __name__=='__main__':
    main()
