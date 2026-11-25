#!/usr/bin/env python3
"""Validate theorem types and axiom dependencies in a fresh CompleteAudit log."""
import re, sys, pathlib
if len(sys.argv)!=2: raise SystemExit('Usage: python3 scripts/check_fresh_audit.py CompleteAudit.log')
t=pathlib.Path(sys.argv[1]).read_text(errors='replace')
count=re.findall(r'^AUDIT_PUBLIC_THEOREM_COUNT\s+(\d+)\s*$',t,re.M)
if count!=['1195']: raise SystemExit(f'FAIL: unexpected public theorem count: {count}')
name_types=set(re.findall(r'^AUDIT_TYPE\s+([^\s:]+)\s*:',t,re.M))
a=re.findall(r'^AUDIT_AXIOMS\s+([^\s:]+)\s*:=\s*\[(.*?)\]\s*$',t,re.M)
if len(name_types)!=1195 or len(a)!=1195: raise SystemExit(f'FAIL: expected 1195 type and axiom lines, got {len(name_types)} / {len(a)}')
if name_types != set(n for n,_ in a): raise SystemExit('FAIL: type and axiom theorem sets differ')
allowed={'propext','Classical.choice','Quot.sound'}
for n,s in a:
 vals=set(x.strip() for x in s.split(',') if x.strip())
 if vals-allowed: raise SystemExit(f'FAIL: unexpected axiom for {n}: {vals-allowed}')
if re.search(r'sorryAx|Lean\.sorryAx|(?:^|\n)error:',t): raise SystemExit('FAIL: sorry/error marker detected')
print(f'PASS: {len(name_types)} theorem types, {len(a)} allowed-axiom declarations')
