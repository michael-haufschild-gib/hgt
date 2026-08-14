# The three open ht cards — state and next bricks (updated 2026-08-14, late)

Cards 6, 4, 2 are PROMOTED to `3-formalized`, each with a `-formalized.md` certificate.
The full `GaloisForLFunctions.HTGeometry` umbrella builds (19 499 jobs); none of the modules below
appears in the lint gate's error list.

## Card 1 `helson-universal-ht-arbitrary-divisor-orthogonality`

**DONE this session — the DENSE half of the seam, unconditionally.**  It was never one of the
card's three classical inputs; it is the card's own finite-Euler-modification argument.
- `RiemannZetaMeromorphic.lean` — `analyticAt_riemannZeta`, `analyticAt_Gammaℝ`,
  **`meromorphicOn_riemannZeta`** (a mathlib gap: mathlib has only the residue limit).  Proof at
  `s = 1` uses `MeromorphicAt.congr` against `ζ = (Λ₀ − 1/s − 1/(1−s))/Γ_ℝ`; no removable-singularity
  theorem.
- `HelsonEulerModification.lean` — `eulerFactor`, `meromorphicAt_finsetProd`,
  `meromorphicOn_riemannZeta_mul_eulerModification`, `finiteEulerStratum`,
  `dense_finiteEulerStratum`.
- `HelsonZetaEulerProduct.lean` — `hasProd_helsonEuler` (the factorwise split against
  `riemannZeta_eulerProduct_hasProd`), `PhaseTorus`, `continuableStratum`,
  **`dense_continuableStratum`**.

**DONE — Pong's conclusion, hypothesis discharged.**  `HelsonPhaseTailIndependence.lean`.
KEY INSIGHT: the corpus criterion `RecurringCoefficientPatternsSpan` is for FINITE-RANGE coefficient
families and is FALSE for a generic unimodular phase (no value of `χ(p)` need recur).  Fix: a single
source enters every column as one COMMON WEIGHT, and
`tailCoefficientIndependent_commonWeight_iff` makes a nowhere-vanishing weight invisible.  Apply the
criterion once to the CONSTANT family, then reinstate the phase.  Gives
`primePowerCoefficientShiftedJets_algebraicIndependent_phase`.

**OPEN**: (a) Saksman–Webb `σ(χ) = 1/2` a.s. → the NULL half of the seam (the abstract
boundary-everywhere consequences are already formal, so this is the single remaining input there);
(b) Andersson Thm 5 → divisor surjectivity; (c) the descent from the prime-power palette to the
shifted derivatives of `Z_χ` itself (the corpus's `algebraicIndependent_arithmeticColumns_of_tailIndependent`
is prime-column based; `Z_χ`'s coefficients live on all of `ℕ`, so a ℕ-indexed Jacobian criterion is
needed).

## Card 3 `irrational-power-canonical-products-…-gevrey-slope-rigidity`

**DONE this session**:
- `AsymptoticExpansionAlgebra.lean` — Poincaré expansions add, multiply, are unique; the expansion
  map is an injective algebra map into `ℂ⟦t⟧`; hence **`aeval_powerSeries_eq_zero_of_eq_zero`**,
  which is the card's `(14) ⟹ (15)`.
- `GevreyExactOrder.lean` — `IsGevreyOfOrder`, `eventually_lt_factorial`,
  **`not_isGevreyOfOrder_of_lower_bound`**, `isGevreyOfOrder_and_not_lt`,
  **`zetaTail_isGevreyOfOrder_exact`** — the card's `(12)` in its real form: Gevrey of order `s` and
  of NO SMALLER order.

**OPEN**: the Barnes expansion `(4)`–`(6)` and Sibuya–Ramis.
For Barnes, attack as a MELLIN computation: with `s > 1` (`g(s)=0`),
`H_s(x) = ∑_{n≥1} x/(n^s+x) = (1/2πi)∫_{(c)} ζ(sw)(π/sin πw)x^w dw`, `0<c<1/s`; shifting right
collects `w = 1/s`, `w = 0`, `w = -k`.  Check `PNTPlus` for usable Perron/Mellin contour machinery
before building from scratch.

## Card 5 `nonautonomous-rational-complete-tail-orbifold-classification`

Everything formal except the Lie–Cartan/Casale classification of proper transitive rational
differential groupoids on a curve into `G1/G2/G3`.  Both of its consumers are already formal.
New this session: `RationalPrefixDifferentialAdjoin.lean`, `RationalPrefixDeckDescent.lean`,
`NonautonomousCompleteTailOrbifoldLaw.lean`.
