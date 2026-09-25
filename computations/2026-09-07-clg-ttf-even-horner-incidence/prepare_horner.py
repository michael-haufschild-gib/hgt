"""Render bounded symbolic coefficient proofs from the Runpod incidence tables."""
import json
from collections import defaultdict
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from generate import F, from_rows, expr, bal, grade_name, rel_name, rc_name, module_name

head='''namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

'''
tail='\nend\nend HTGeometry\n'

def hn(n): return f'evenCompactHorner{n}'
def hc(n,i): return f'evenCompactHorner{n}Coeff{i}'
def hm(n): return f'PolynomialODEEvenCompactHorner{n}'

def coeffs(rows):
    out=defaultdict(dict)
    for e,c in rows: out[e[0]][tuple(e[1:])]=F(c)
    return dict(out)


def render_step(job):
    n,current,previous,grade=job
    co=coeffs(current); po=coeffs(previous)
    degree=max(co) if co else 0
    prev_degree=max(po) if po else -1
    rd=set(grade['r_degrees'])
    s=f'import GaloisForLFunctions.HTGeometry.{module_name(n)}\n'
    s+=f'import GaloisForLFunctions.HTGeometry.{hm(n+1)}\n'
    s+='import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates\n\n'
    s+='/-! # A single linear-factor Horner step for the compact determinant -/\n'+head
    for i in range(degree+1):
        p=co.get(i,{})
        ta='t' if any(e[0] for e in p) else '_t'
        va='v' if any(e[1] for e in p) else '_v'
        s+=f'/-- Drift-degree {i} in this exact Horner remainder. -/\ndef {hc(n,i)} ({ta} {va} : ℝ) : ℝ :=\n  '+expr(p,('t','v'))+'\n\n'
        pterm=rc_name(n,i)+' v' if i in rd else '(0 : ℝ)'
        qterm=hc(n+1,i)+' t v' if i<=prev_degree else '(0 : ℝ)'
        rterm=hc(n+1,i-1)+' t v' if 0<=i-1<=prev_degree else '(0 : ℝ)'
        unfolds=[hc(n,i)]
        if i in rd: unfolds.append(rc_name(n,i))
        if i<=prev_degree: unfolds.append(hc(n+1,i))
        if 0<=i-1<=prev_degree: unfolds.append(hc(n+1,i-1))
        s+=f'''/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem {hc(n,i)}_eq (t v : ℝ) :
    {hc(n,i)} t v = ({pterm})+
      (191/10+t/10)*({qterm})+(-12/5+(16/15)*t)*({rterm}) := by
  unfold '''+' '.join(unfolds)+'''
  ring1

'''
    rarg='r' if degree else '_r'
    s+=f'/-- The exact Horner polynomial retains its drift grading. -/\ndef {hn(n)} ({rarg} t v : ℝ) : ℝ :=\n  '+bal([f'(r^({i} : ℕ)*{hc(n,i)} t v)' if i else f'{hc(n,i)} t v' for i in range(degree+1)])+'\n\n'
    s+=f'''/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem {hn(n)}_step (r t v : ℝ) :
    {hn(n)} r t v = {rel_name(n)} r v+
      evenCompactUnitGap r t*{hn(n+1)} r t v := by
  unfold {hn(n)} {hn(n+1)}
  rw ['''+', '.join(hc(n,i)+'_eq' for i in range(degree+1))+f''']
  unfold {rel_name(n)} evenCompactUnitGap
  ring1
'''+tail
    Path('output',hm(n)+'.lean').write_text(s)
    return {'step':n,'drift_degrees':degree+1,'max_coefficient_terms':max(map(len,co.values())) if co else 0}


if __name__=='__main__':
    data=json.loads(Path('output/incidence.json').read_text())
    gs={g['gap_degree']:g for g in data['grades']}
    top=data['top_gap_degree']; hs={int(k):v for k,v in data['horner'].items()}
    Path('output',hm(top+1)+'.lean').write_text('import Mathlib.Data.Real.Basic\n\n'+head+f'/-- Terminal zero of the finite exact Horner recurrence. -/\ndef {hn(top+1)} (_r _t _v : ℝ) : ℝ := 0\n'+tail)
    with ProcessPoolExecutor(max_workers=16) as pool:
        summary=list(pool.map(render_step,[(n,hs[n],hs.get(n+1,[]),gs[n]) for n in range(top,-1,-1)]))
    ns=sorted(gs)
    imports=''.join(f'import GaloisForLFunctions.HTGeometry.{module_name(n)}\n' for n in ns)
    s=imports+'import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactModel\n\n'
    s+='/-! # Full corrected determinant in the original modular coordinates -/\n'+head+'open GaloisForLFunctions.HTGeometry\n\n'
    s+='''/-- Full signed source determinant with the stronger correction, in fixed units. -/
def evenCompactRawDet (u a w : ℝ) : ℝ :=
  hankelFourDet ((oddCompactSourceZero u a)^2) (-oddCompactReflectedScalar2 u a w)
    (oddCompactReflectedScalar4 u a w) (-oddCompactReflectedScalar6 u a w)
    (oddCompactReflectedScalar8 u a w) (-oddCompactReflectedScalar10 u a w)
    (evenCompactReflectedScalar12 u a w+1000000000000*oddCompactSourceZero u a*
      (3*oddCompactSourceZero u a-6/19))/(100 : ℝ)^12

/-- Gap grading of every coefficient of the corrected raw determinant. -/
def evenCompactRawPolynomial (u a w : ℝ) : ℝ :=
  '''+bal([f'(a^({n} : ℕ)*{grade_name(n)} u w)' if n else f'{grade_name(n)} u w' for n in ns])+'''

/-- Exact original-coordinate determinant identity before the coupled gap is substituted. -/
theorem evenCompactRawDet_eq_polynomial (u a w : ℝ) :
    evenCompactRawDet u a w = evenCompactRawPolynomial u a w := by
  unfold evenCompactRawDet hankelFourDet oddCompactSourceZero
    oddCompactReflectedScalar2 oddCompactReflectedScalar4 oddCompactReflectedScalar6
    oddCompactReflectedScalar8 oddCompactReflectedScalar10 evenCompactReflectedScalar12
    evenCompactRawPolynomial '''+' '.join(grade_name(n) for n in ns)+'''
  ring1
'''+tail
    s=s.replace('maxHeartbeats 2000000','maxHeartbeats 5000000')
    Path('output/PolynomialODEEvenCompactRawDeterminant.lean').write_text(s)
    expression='(0 : ℝ)'
    for n in range(top,-1,-1): expression=f'({rel_name(n)} r v+a*{expression})'
    s='import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactRawDeterminant\n\n'+head
    s+='''/-- Relative-shear determinant, retaining the Horner structure in the gap coordinate. -/
def evenCompactRelativeDet (r a v : ℝ) : ℝ :=
  '''+expression+'''

/-- All gap-grade shear identities assemble before the gap itself is substituted. -/
theorem evenCompactRawPolynomial_relative_eq (u a v : ℝ) :
    evenCompactRawPolynomial u a (u*(1+v/4)) = evenCompactRelativeDet (u^2) a v := by
  unfold evenCompactRawPolynomial
  rw ['''+', '.join(grade_name(n)+'_relative_eq' for n in ns)+''']
  unfold evenCompactRelativeDet
  ring1
'''+tail
    Path('output/PolynomialODEEvenCompactRelativeDeterminant.lean').write_text(s)
    Path('output/horner-generation-log.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)
