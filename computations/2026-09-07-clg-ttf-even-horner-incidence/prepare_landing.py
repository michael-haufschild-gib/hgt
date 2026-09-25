"""Render exact drift-grade landing in the independently positive unit polynomial."""
import json
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from generate import F, expr, bal
from prepare_horner import head, tail, hc, hn


def bc(j,i): return f'evenCompactUnitBlock{j}DriftCoeff{i}'
def bm(j): return f'PolynomialODEEvenCompactBlockGrades{j}'


def render_block(job):
    j,rows=job
    co=defaultdict(dict)
    for e,c in rows: co[e[0]][tuple(e[1:])]=F(c)
    s=f'import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBlock{j}\n\n'+head
    for i,p in sorted(co.items()):
        ta='t' if any(e[0] for e in p) else '_t'
        va='v' if any(e[1] for e in p) else '_v'
        s+=f'/-- Exact drift-degree {i} of the already proved positive-polynomial block. -/\ndef {bc(j,i)} ({ta} {va} : ℝ) : ℝ :=\n  '+expr(p,('t','v'))+'\n\n'
    s+=f'''/-- Exact drift grading of this full block, retaining every coefficient. -/
theorem evenCompactUnitBlock{j}_drift_eq (r t v : ℝ) :
    evenCompactUnitBlock{j} r t v =
      '''+bal([f'(r^({i} : ℕ)*{bc(j,i)} t v)' if i else f'{bc(j,i)} t v' for i in sorted(co)])+''' := by
  unfold evenCompactUnitBlock'''+str(j)+' '+' '.join(bc(j,i) for i in sorted(co))+'''
  ring1
'''+tail
    Path('output',bm(j)+'.lean').write_text(s)
    return j,sorted(co)


if __name__=='__main__':
    T=json.loads(Path('clg_even_inner_unit.json').read_text())
    with ProcessPoolExecutor(max_workers=12) as pool:
        blocks=list(pool.map(render_block,[(j,T[k:k+448]) for j,k in enumerate(range(0,len(T),448))]))
    index=defaultdict(list)
    for j,ids in blocks:
        for i in ids: index[i].append(j)
    s='import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactHorner0\n'
    s+='import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitReserve\n'
    s+=''.join(f'import GaloisForLFunctions.HTGeometry.{bm(j)}\n' for j,_ in blocks)+'\n'+head
    for i,js in sorted(index.items()):
        rhs=bal([bc(j,i)+' t v' for j in js])
        s+=f'''/-- Exact landing of drift-degree {i} in the positive polynomial certificate. -/
theorem evenCompactHornerLandingCoeff{i} (t v : ℝ) :
    {hc(0,i)} t v = {rhs} := by
  first
  | rfl
  | unfold {hc(0,i)} '''+' '.join(bc(j,i) for j in js)+'''
    ring1

'''
    s+='''/-- All drift coefficients land exactly in the independently proved positive polynomial. -/
theorem evenCompactHorner0_eq_unitPolynomial (r t v : ℝ) :
    evenCompactHorner0 r t v = evenCompactUnitPolynomial r t v := by
  unfold evenCompactHorner0
  rw ['''+', '.join('evenCompactHornerLandingCoeff'+str(i) for i in sorted(index))+''']
  unfold evenCompactUnitPolynomial
  rw ['''+', '.join('evenCompactUnitBlock'+str(j)+'_drift_eq' for j,_ in blocks)+''']
  ring1
'''+tail
    Path('output/PolynomialODEEvenCompactHornerLanding.lean').write_text(s)
    Path('output/landing-generation-log.json').write_text(json.dumps({'blocks':blocks,'drift_grades':len(index)},indent=2)+'\n')
    print('Prepared',len(blocks),'block gradings and',len(index),'coefficient landing identities.',flush=True)
