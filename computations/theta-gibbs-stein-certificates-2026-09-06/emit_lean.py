"""Render candidate rational identities as ordinary Lean proof terms.

Run on Runpod. The output uses ring, positivity and rational arithmetic;
it neither trusts these scripts nor calls an evaluator as a proof oracle.
"""
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path


def rat(v):
    v = F(v)
    return f'({v.numerator} / {v.denominator} : ℝ)'


out = ['import GaloisForLFunctions.RHTower.ThetaGibbsSteinIntegral',
       '', 'open Real MeasureTheory Set Filter Topology Polynomial',
       'open scoped BigOperators', 'namespace RHTower', 'noncomputable section',
       'set_option maxHeartbeats 8000000', '']
polys = {'mass': [(1, 0)], 'ward1': [(4, 1), (-1, 2)],
         'ward2': [(-8, 3), (1, 4)], 'ward3': [(12, 5), (-1, 6)]}
for cert in json.loads(Path('rational-certificates.json').read_text()):
    assert cert['exact_residuals_nonnegative']
    name, n = cert['which'], cert['degree']
    sig = 1 if cert['direction'] == 'lower' else -1
    coeff = [[F(c) for c in row] for row in cert['coefficients']]
    p = []
    for j in range(n):
        p.append(' + '.join(f'C {rat(sig * coeff[k][j] * 4**k)} * X^{k}'
                            for k in range(len(coeff))))
    out += [f'private def {name}SteinWitness : Fin {n} → ℝ[X] :=',
            '  ![' + ',\n    '.join(p) + ']', '']
    qexpr = ' + '.join(f'C {rat(c)} * X^{k}' for c, k in polys[name])
    out += [f'private def {name}SteinTarget : ℝ[X] := {qexpr}', '']
    rnames = []
    for label, res in zip(['Lo', 'Hi'], cert['residuals']):
        rname = name + 'SteinResidual' + label
        rnames.append(rname)
        rows = []
        for k, row in enumerate(res):
            terms = [f'{rat(F(c) * comb(n, i))} * t^{i} * (1-t)^{n-i}'
                     for i, c in enumerate(row)]
            rows.append(f'(4*x)^{k} * (' + ' +\n      '.join(terms) + ')')
        out += [f'private def {rname} (x t : ℝ) : ℝ :=',
                '  ' + ' +\n  '.join(rows), '']
        hx_name = '_hx' if name == 'mass' else 'hx'
        out += [f'private theorem {rname}_nonneg (x t : ℝ) ({hx_name} : 0 ≤ x)',
                '    (ht : 0 ≤ t) (ht1 : t ≤ 1) :',
                f'    0 ≤ {rname} x t := by',
                '  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht1',
                f'  unfold {rname}', '  positivity', '']
    lo, hi = rnames
    out += [f'private theorem {name}Stein_remainder_nonneg (x t : ℝ)',
            '    (hx : 0 ≤ x) (ht : 0 ≤ t) (ht1 : t ≤ 1) :',
            f'    0 ≤ {name}SteinTarget.eval x -',
            f'      thetaGibbsSteinPolynomial Real.pi {name}SteinWitness x t := by',
            '  have hpilo : (314159/100000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]',
            '  have hpihi : Real.pi ≤ (3927/1250 : ℝ) := by linarith [Real.pi_lt_d4]',
            '  have hm := add_nonneg',
            f'    (mul_nonneg (sub_nonneg.mpr hpihi) ({lo}_nonneg x t hx ht ht1))',
            f'    (mul_nonneg (sub_nonneg.mpr hpilo) ({hi}_nonneg x t hx ht ht1))',
            f'  have hid : (1/100000 : ℝ) * ({name}SteinTarget.eval x -',
            f'      thetaGibbsSteinPolynomial Real.pi {name}SteinWitness x t) =',
            f'      ((3927/1250 : ℝ)-Real.pi)*{lo} x t +',
            f'        (Real.pi-(314159/100000 : ℝ))*{hi} x t := by',
            f'    norm_num [{name}SteinTarget, {name}SteinWitness, {lo}, {hi},',
            '      thetaGibbsSteinPolynomial, Fin.sum_univ_succ, Polynomial.derivative_pow]',
            '    ring',
            '  nlinarith only [hm, hid]', '']
    target = rat(sig * F(cert['target']))
    out += [f'private theorem {name}Stein_integral_lower :',
            f'    {target} * Real.exp (-Real.pi) ≤',
            f'      thetaGibbsPolynomialIntegral {name}SteinTarget := by',
            f'  have h := thetaGibbsPolynomialIntegral_lower_of_stein',
            f'    {name}SteinTarget {name}SteinWitness (fun x hx =>',
            f'      {name}Stein_remainder_nonneg x (Real.exp (-2*x)) hx',
            '        (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)))',
            f'  norm_num [{name}SteinWitness, Fin.sum_univ_succ] at h',
            '  simpa only [neg_div, neg_mul] using h', '']
out += ['end', 'end RHTower', '']
Path('ThetaGibbsSteinSourceMinor.lean').write_text('\n'.join(out))
print('Wrote ordinary Lean rational-identity proof candidates.', flush=True)
