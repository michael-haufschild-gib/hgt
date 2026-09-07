"""Runpod: prepare symbolic raw-coordinate and Horner incidence candidates."""
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json
import os
import time

Z=(0,0,0)

def add(*ps):
    out={}
    for p in ps:
        for e,c in p.items(): out[e]=out.get(e,F(0))+c
    return {e:c for e,c in out.items() if c}

def scale(p,c): return {e:c*v for e,v in p.items() if c*v}

def mul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            g=tuple(a+b for a,b in zip(e,f))
            out[g]=out.get(g,F(0))+c*d
    return {e:c for e,c in out.items() if c}

def from_rows(rows): return {tuple(e):F(c) for e,c in rows}
def rows(p): return [[list(e),str(c)] for e,c in sorted(p.items())]

def bal(ts):
    if not ts: return '(0 : ℝ)'
    if len(ts)==1: return ts[0]
    n=len(ts)//2
    return '('+bal(ts[:n])+' +\n    '+bal(ts[n:])+' : ℝ)'

def term(e,c,names):
    coeff=str(c.numerator) if c.denominator==1 else f'{c.numerator}/{c.denominator}'
    s=f'({coeff} : ℝ)'
    for x,k in zip(names,e):
        if k: s+=f'*{x}^({k} : ℕ)'
    return s

def expr(p,names): return bal([term(e,c,names) for e,c in sorted(p.items())])
def grade_name(n): return f'evenCompactRawGapGrade{n}'
def rel_name(n): return f'evenCompactRelativeGapGrade{n}'
def rc_name(n,i): return f'evenCompactRelativeGapGrade{n}Coeff{i}'
def module_name(n): return f'PolynomialODEEvenCompactGapGrade{n}'


def make_grade(job):
    n,raw_rows=job
    raw=from_rows(raw_rows)
    relative={}
    for (ue,_,we),c in raw.items():
        assert (ue+we)%2==0
        for j in range(we+1):
            e=((ue+we)//2,0,j)
            relative[e]=relative.get(e,F(0))+c*comb(we,j)/4**j
    relative={e:c for e,c in relative.items() if c}
    coefficients=defaultdict(dict)
    for (re,_,ve),c in relative.items(): coefficients[re][(ve,)]=c
    ns=sorted(coefficients)
    u_arg='u' if any(e[0] for e in raw) else '_u'
    w_arg='w' if any(e[2] for e in raw) else '_w'
    text='''import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Exact relative-shear substitution at one modular gap degree -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

'''
    text+=f'/-- Gap-degree {n} of the full corrected raw determinant, in fixed units. -/\ndef {grade_name(n)} ({u_arg} {w_arg} : ℝ) : ℝ :=\n  '+expr(raw,('u','a','w'))+'\n\n'
    for i in ns:
        var='v' if any(e[0] for e in coefficients[i]) else '_v'
        text+=f'/-- Exact drift-degree {i} coefficient after relative-shear substitution. -/\ndef {rc_name(n,i)} ({var} : ℝ) : ℝ :=\n  '+expr(coefficients[i],('v',))+'\n\n'
    rarg='r' if any(ns) else '_r'
    text+=f'/-- The relative-shear polynomial retains drift grading. -/\ndef {rel_name(n)} ({rarg} v : ℝ) : ℝ :=\n  '+bal([f'(r^({i} : ℕ)*{rc_name(n,i)} v)' if i else f'{rc_name(n,i)} v' for i in ns])+'\n\n'
    text+=f'''/-- Exact symbolic relative-shear identity at this entire gap degree. -/
theorem {grade_name(n)}_relative_eq (u v : ℝ) :
    {grade_name(n)} u (u*(1+v/4)) = {rel_name(n)} (u^2) v := by
  unfold {grade_name(n)} {rel_name(n)} '''+' '.join(rc_name(n,i) for i in ns)+'''
  ring1

end
end HTGeometry
'''
    Path('output',module_name(n)+'.lean').write_text(text)
    return {'gap_degree':n,'raw':rows(raw),'relative':rows(relative),'r_degrees':ns}


if __name__=='__main__':
    started=time.monotonic()
    data=json.loads(Path('clg_even_inner_det.json').read_text())
    D=from_rows(data['D']); H=from_rows(data['head'])
    Q=from_rows(json.loads(Path('clg_even_inner_polys.json').read_text())['p'][0])
    old_slope={(0,1,1):F(1,8),(1,0,0):F(5,16)}
    G0=scale(mul(Q,old_slope),F(-137,1000))
    G1=scale(Q,F(-6,19))
    D=scale(add(D,scale(mul(H,add(G1,scale(G0,-1))),10**12)),F(1,10**24))
    raw_groups=defaultdict(dict)
    for (ue,ae,we),c in D.items(): raw_groups[ae][(ue,0,we)]=c
    Path('output').mkdir(exist_ok=True)
    with ProcessPoolExecutor(max_workers=min(16,os.cpu_count() or 1)) as pool:
        grades=list(pool.map(make_grade,[(n,rows(p)) for n,p in sorted(raw_groups.items())]))
    P={g['gap_degree']:from_rows(g['relative']) for g in grades}
    A={(0,0,0):F(191,10),(1,0,0):F(-12,5),(0,1,0):F(1,10),(1,1,0):F(16,15)}
    horner={}; current={}
    top=max(P)
    for n in range(top,-1,-1):
        current=add(P.get(n,{}),mul(A,current))
        horner[n]=rows(current)
    result={'raw':rows(D),'grades':grades,'horner':horner,'top_gap_degree':top,
            'seconds':time.monotonic()-started,'workers':min(16,os.cpu_count() or 1)}
    Path('output/incidence.json').write_text(json.dumps(result)+'\n')
    print(json.dumps({'raw_terms':len(D),'top_gap_degree':top,
          'grade_sizes':[(g['gap_degree'],len(g['raw']),len(g['relative'])) for g in grades],
          'horner_sizes':[(n,len(horner[n])) for n in sorted(horner,reverse=True)],
          'seconds':result['seconds'],'workers':result['workers']},indent=2),flush=True)
