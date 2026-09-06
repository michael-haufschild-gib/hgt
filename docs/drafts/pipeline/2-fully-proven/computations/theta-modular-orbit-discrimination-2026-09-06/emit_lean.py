"""Emit symbolic candidate identities; Lean must prove every identity and inequality.

Run this algebraic construction on Runpod. No evaluation oracle or numerical
result is embedded in the Lean proofs: only ring identities and ordered-field laws.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, math
import sympy as sy
ROOT=Path(__file__).resolve().parent

def scalar(rows,variables=('S','A','W'),typ='ℝ'):
    terms=[]
    for e,c in rows:
        c=Q(str(c));fs=[f'({c.numerator} / {c.denominator} : {typ})']
        fs += [f'{v}^{n}' for v,n in zip(variables,e) if n]
        terms.append(' * '.join(fs))
    return ' +\n    '.join(terms) or '0'

def mv(rows):
    terms=[]
    for e,c in rows:
        c=Q(str(c));fs=[f'C ({c.numerator} / {c.denominator} : ℂ)']
        fs += [f'X ModularThetaLyapunovState.{v}^{n}' for v,n in zip(('S','A','W'),e) if n]
        terms.append(' * '.join(fs))
    return ' +\n    '.join(terms) or '0'

if __name__=='__main__':
    S,A,W=sy.symbols('S A W');vs=(S,A,W)
    F=(3-S*S/3-3*A/4,-2*A*W,2+A/2+2*S*S/9-2*S*W/3)
    H=[sy.Integer(1)]
    for n in range(10):H.append(sy.Poly(sum(sy.diff(H[-1],v)*g for v,g in zip(vs,F))-S*H[-1]/6,*vs).as_expr())
    P=[(tuple(r['exponents']),Q(r['coefficient'])) for r in json.loads((ROOT/'d1_polynomial.json').read_text())]
    header='''import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeLyapunovClosure
import Mathlib.Algebra.MvPolynomial.Funext

open MvPolynomial
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

'''
    out=[header]
    for n,h in enumerate(H):
        out.append(f'private def compactH{n} : ModularThetaLyapunovPolynomial :=\n  '+mv(sy.Poly(h,*vs).terms())+'\n')
        out.append(f'private theorem compactH{n}_eq : modularThetaLyapunovNormalizedHJet {n} = compactH{n} := by\n')
        if n==0:out.append('  simp [modularThetaLyapunovNormalizedHJet, compactH0]\n')
        else:
            out.append(f'''  rw [modularThetaLyapunovNormalizedHJet, compactH{n-1}_eq]
  apply MvPolynomial.funext
  intro v
  simp [compactH{n-1}, compactH{n}, modularThetaLyapunovNormalizedLie,
    modularThetaLyapunovLie, pderiv_mul, pderiv_pow, pderiv_C,
    modularThetaLyapunovVectorField,
    show (Finset.univ : Finset ModularThetaLyapunovState) = {{.S, .A, .W}} by decide]
  <;> ring
''')
    out.append('/-- Explicit real polynomial for the mass-normalized reflected rank-three determinant. -/\n')
    out.append('def modularThetaCompactD1 (S A W : ℝ) : ℝ :=\n  '+scalar(P)+'\n')
    out.append('''/-- Exact symbolic expansion; no source or positivity assumption. -/
theorem modularThetaLyapunovReflectedEighthPolynomial_eval_ofReal (S A W : ℝ) :
    MvPolynomial.eval (fun i : ModularThetaLyapunovState =>
      match i with | .S => (S : ℂ) | .A => (A : ℂ) | .W => (W : ℂ))
        modularThetaLyapunovReflectedEighthPolynomial = (modularThetaCompactD1 S A W : ℂ) := by
  unfold modularThetaLyapunovReflectedEighthPolynomial
  simp only [modularThetaLyapunovNormalizedSourceJet]
  norm_num only [Nat.reduceAdd]
''')
    out.append('  rw ['+', '.join(f'compactH{n}_eq' for n in range(11))+']\n')
    out.append('  simp only ['+', '.join(f'compactH{n}' for n in range(11))+''', map_add, map_sub, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  dsimp only
  unfold modularThetaCompactD1
  push_cast
  ring
end
end HTGeometry
''')
    (ROOT/'JetCandidate.lean').write_text('\n'.join(out))
    slices=json.loads((ROOT/'slices.json').read_text())['slices']
    out=['''import GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeCompactExpansion
open HTGeometry
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

''']
    for row in slices:
        j=row['j'];ns=row['bernstein_degrees'];mask=row['mask']
        original=[((r['index'][0],r['index'][2]),Q(r['value'])) for r in row['original']]
        bs=[]
        for r in row['coefficients']:
            i,_,k=r['index'];c=Q(r['value'])
            if j==0:c-=1
            assert c>=0
            for axis,e in enumerate((i,k)):
                if mask>>axis&1:c*=math.comb(ns[axis],e)
            bs.append(((i,k),c))
        den=1
        for e,c in bs:den=den*c.denominator//math.gcd(den,c.denominator)
        # Split each S row for small, reusable positivity proofs.
        rownames=[]
        for i in sorted({e[0] for e,c in bs}):
            terms=[]
            for (ii,k),c in bs:
                if ii!=i or not c:continue
                fs=[str(int(c*den))]
                if k:fs.append(f'z^{k}')
                if mask&2 and ns[1]-k:fs.append(f'(1-z)^{ns[1]-k}')
                terms.append(' * '.join(fs))
            name=f'compactRow{j}_{i}';rownames.append((i,name))
            out.append(f'private def {name} (z : ℝ) : ℝ :=\n  '+' +\n    '.join(terms)+'\n')
            out.append(f'''private theorem {name}_nonneg (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ {name} z := by
  have h1 : 0 ≤ 1-z := sub_nonneg.mpr hz1
  unfold {name}
  positivity
''')
        name=f'compactSlice{j}';cert=f'compactCert{j}'
        out.append(f'private def {name} (t z : ℝ) : ℝ :=\n  '+scalar(original,('t','z'))+'\n')
        terms=[]
        for i,rowname in rownames:
            fs=[f'{rowname} z']
            if i:fs.append(f't^{i}')
            if mask&1 and ns[0]-i:fs.append(f'(1-t)^{ns[0]-i}')
            terms.append(' * '.join(fs))
        out.append(f'private def {cert} (t z : ℝ) : ℝ :=\n  '+' +\n    '.join(terms)+'\n')
        out.append(f'''private theorem {cert}_nonneg (t z : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ {cert} t z := by
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht1
''')
        for i,rowname in rownames:out.append(f'  have h{i} := {rowname}_nonneg z hz hz1\n')
        out.append(f'  unfold {cert}\n  positivity\n')
        out.append(f'''private theorem {name}_identity (t z : ℝ) :
    {den} * {name} t z = {den if j==0 else 0} + {cert} t z := by
  unfold {name} {cert} {' '.join(n for i,n in rownames)}
  ring
private theorem {name}_lower (t z : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : {1 if j==0 else 0} ≤ {name} t z := by
  have hc := {cert}_nonneg t z ht ht1 hz hz1
  have hi := {name}_identity t z
  linarith only [hc, hi]
''')
    out.append('''/-- The compact certificate in fact allows any amplitude A ≥ 17. -/
theorem modularThetaCompactD1_pos (S A W : ℝ) (hS : -1 ≤ S) (hS0 : S ≤ 0)
    (hA : 17 ≤ A) (hW : 0 ≤ W) (hW1 : W ≤ 6/5) :
    0 < modularThetaCompactD1 S A W := by
  have ht : 0 ≤ -S := by linarith
  have ht1 : -S ≤ 1 := by linarith
  have hz : 0 ≤ 5*W/6 := by linarith
  have hz1 : 5*W/6 ≤ 1 := by linarith
  have ha : 0 ≤ A-17 := by linarith
''')
    for j in range(13):out.append(f'  have h{j} := compactSlice{j}_lower (-S) (5*W/6) ht ht1 hz hz1\n')
    out.append('  have hid : modularThetaCompactD1 S A W =\n    '+' +\n    '.join(f'(A-17)^{j} * compactSlice{j} (-S) (5*W/6)' for j in range(13))+' := by\n')
    out.append('    unfold modularThetaCompactD1 '+' '.join(f'compactSlice{j}' for j in range(13))+'\n    ring\n')
    out.append('  rw [hid]\n  have hpos : 0 < compactSlice0 (-S) (5*W/6) := by linarith\n  positivity\nend\nend HTGeometry\n')
    (ROOT/'BoxCandidate.lean').write_text('\n'.join(out))
    print('emitted',len((ROOT/'JetCandidate.lean').read_text()),len((ROOT/'BoxCandidate.lean').read_text()))
