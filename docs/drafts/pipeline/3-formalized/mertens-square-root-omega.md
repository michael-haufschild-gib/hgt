# Mertens function: M(x) = Ω±(√x)

Stage: 3-formalized (2026-10-03). Loop cycle 228 (MUST-727).

## Statement
Unconditionally there is `c > 0` with `M(x) > c√x` and `M(x) < −c√x` for arbitrarily large `x`;
`M(x) ≠ o(√x)`. A one-sided bound `±M(x) ≤ c√x` (eventually) implies RH and simplicity of every
zero on the critical line, with `1/|ρζ'(ρ)| ≤ c`.

## Proof (paper)
1. Mellin: `∫_0^∞ M(e^u)e^{−su}du = 1/(sζ(s))` for `Re s > 1` (corpus
   `inv_riemannZeta_eq_mul_integral_mertens` + change of variables `t = e^u`).
2. One-sided bound ⇒ density `εe^{t/2} − ηM(e^t) + K ≥ (ε−ε')e^{t/2} > 0`; abscissa ≥ ½; transform
   `ε/(s−½) + K/s − η/(sζ(s))` analytic at real points of `(½, ∞)`; Landau ⇒ abscissa = ½.
3. Identity theorem: `H(z)·z(z−1)ζ(z) = η(z−1)` on `Re z > ½` ⇒ RH.
4. At a zero `ρ` on the line: positivity `|N(ρ+r)| ≤ N(½+r) = ε/r + O(1)` against
   `r^m|H(ρ+r)| → |ρ−1|/(|ρ||G(ρ)|)`; `m ≥ 2` impossible, `m = 1` gives the residue bound ≤ ε, all ε > ε'.
5. Hardy's zero `ρ = ½ + it`; `c` = half its residue.

## Lean
`formal/GaloisForLFunctions/RHTower/MertensSquareRootOmega.lean` (wired after
`PrimeCountingLogIntegralNegativeValues`): `integral_mertensFunctionReal_exp_mul_cexp`,
`abscissa_mertensMeasure_eq`, `mertens_continuation_identity`, `eventually_mertens_local_le`,
`mertens_zero_simple_of_oneSided`, `mertens_omega_pm_sqrt`, `not_mertensFunctionReal_isLittleO_sqrt`,
`riemannHypothesis_of_mertens_oneSided`, `deriv_zetaResidueUnit_ne_zero_of_mertens_oneSided`.
Axioms `[propext, Classical.choice, Quot.sound]`.

## Positive survivor / reading
The residue mechanism (step 4) is generic: any one-sided `O(x^{1/2})` bound on a summatory function
whose Mellin transform has poles on the line bounds the residues uniformly. For `ψ` the residues are
`1` (Schmidt, MUST-721), for `M` they are `1/(ρζ'(ρ))`.
