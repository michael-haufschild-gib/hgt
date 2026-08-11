# The explicit-formula glue theorem landed (2026-08-11)

Module: `formal/GaloisForLFunctions/RHTower/XiExplicitFormulaLogDeriv.lean` (wired into RHTower,
umbrella green 18916 jobs, all 4 theorems `[propext, Classical.choice, Quot.sound]`).

## The theorems
- `xi_eq_XiC_comp : xi s = XiC ((s − 1/2)·(−i))` — coordinate bridge.
- `resolvent_coordinate_transport` — hypothesis-FREE rotation algebra for resolvent differences
  (mul_inv works with junk values; no nonvanishing needed).
- `logDeriv_xi_eq_partialFraction {s} (hs : xi s ≠ 0)`:
  `logDeriv xi s = Σ'_{q : XiZeroCopy} (1/(ρ_q − 1/2) + 1/(s − ρ_q))` — the classical
  multiplicity-exact Hadamard partial fraction, NO linear term (evenness killed it upstream in
  `xiHadamardQuotient_constant`).
- `logDeriv_xi_split {s} (hs : 1 < s.re)`:
  `logDeriv xi s = 1/s + 1/(s−1) + logDeriv Γℝ s + logDeriv ζ s`.
- **`xi_explicitFormula_logDeriv {s} (hs : 1 < s.re)`**:
  `Σ'_ρ (1/(ρ−1/2) + 1/(s−ρ)) = 1/s + 1/(s−1) + logDeriv Γℝ s − LSeries (↑Λ) s`
  — the corpus's FIRST unconditional zero-sum = prime-sum identity (Guinand–Weil trunk).

## Assembly sources
Corpus: `logDeriv_XiC_eq_relativeResolventTrace` (XiRelativeResolventTrace.lean),
`hasDerivAt_Gammaℝ_of_re_pos` (ArchEnvelope.lean), `xi_eq_half_mul`, `xi_ne_zero_of_one_le_re`
(RHLadderTheory), `XiC_analytic`. Mathlib: `logDeriv_comp`, `logDeriv_mul`, `logDeriv_apply`,
`riemannZeta_def_of_ne_zero`, `Gammaℝ_ne_zero_of_re_pos`, `riemannZeta_ne_zero_of_one_lt_re`,
`differentiableAt_riemannZeta`, `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

## Lean traps encountered
- `rw [xi = XiC ∘ h]` in any goal mentioning `XiZeroCopy` FAILS (divisor type depends on xi →
  motive not type-correct). Isolate the head rewrite in a `have` whose statement has no divisor.
- `logDeriv_mul` higher-order unification mis-splits nested products — pass `(f := ...) (g := ...)`.
- `HasDerivAt` combinator values arrive beta-unreduced (`(fun w => w) s` atoms): `ring` fails.
  Pattern: type-ascribe the combinator output to the raw value shape, then `rw` the value equation.
- Corpus owns Γℝ-differentiability (`hasDerivAt_Gammaℝ_of_re_pos`); mathlib only has the inverse.

## Next limbs (separate bricks)
1. s-derivatives of the identity ⇒ Li-type coefficient identities (zero power sums — corpus
   already has `tsum_xiZeroCopyReciprocalSquare_pow` on the zero side).
2. Pairing against test families (Dirichlet-polynomial × rational kernels) → toward Weil-form
   arithmetic side for the deviation-moment socket (attempts 11–15 lane).
3. Contour motion past Re = 1 (the analytically hard limb; PNTPlus `LogDerivZetaHolcLargeT` is
   the germ).
