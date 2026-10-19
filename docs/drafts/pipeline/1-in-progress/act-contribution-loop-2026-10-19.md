# ACT contribution loop (goal: 100 field-native contributions)

- **ID:** act-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md (read-only)
- **Statement:** Develop Arithmetic Criticality Theory by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field (its objects: the folded and
  two-sided generators, shifted ground states, collar masses, the energies S, P, D, X, the profile
  variance, the pole moment, the shift-averaged kernels).

## Goal
100 significant contributions: native to ACT, expanding what the field explains or solves
(README §5 frontier, or discharging a premise elsewhere in the corpus). No RH hypotheses in Lean:
consequences of positivity are stated as equivalences or as limits of unconditional identities.

## Coordination
Programme card: `act-arithmetic-criticality-theory-2026-10-19.md` (status of the first 35 modules).
THIM (`TransHorizonIncidenceMechanics/`) owns overlapping objects in `oddProfile` coordinates; check
`ls ArithmeticCriticalityTheory/` and search before naming a module.

## Conjecture queue
1. Frontier 3: every finite signed superposition `Σ c_j ω_{a_j}` that is nonnegative on the half
   line and nonzero fails the folded test at infinity; the decisive coefficient is the pole moment
   `σ = Σ c_j sinh(a_j/2) = 2∫_0^∞ M sinh(x/2)`, positive on the cone.
2. Single-shift completeness: RH ⟺ the (pole-free) variation inequality at one fixed shift `a`.
3. Origin polarity: the even form stays supercritical on even tests vanishing near `0`; the folded
   test is the even-sector test with a polar Dirichlet point (soft no-go for all folded
   supersolutions).
4. Sharp coupling: `Q − ε ρ` is negative on odd tests for every `ε > 0` (no Hardy weight
   comparable to the potential); constraint `∫ W ω_a² ≤ sinh²(a/2)` on Hardy weights.
5. Weight criterion of the monotone cone (README 3.9): decide it; positive survivor.
6. Selectivity: which statements survive for an abstract even kernel with an abstract harmonic
   identity (pole-driven vs prime-driven parts of the theory).

## Log
- 2026-10-19 — loop started; README read in full; programme card and modules surveyed; queue seeded.

## Contribution ledger (append-only)
- **C1 · Signed superpositions fail at infinity (README frontier 3)** —
  `SignedSuperpositionInfinityFailure`. For `ω = Σ_j c_j ω_{a_j}` (arbitrary real `c_j`, `a_j > 0`)
  with test coordinate `M = Σ c_j m_{a_j} ≥ 0` on the half line: `foldedDefect_spanGroundState`
  (`𝓛_N ω − Φcosh ω = 2Φ[σ sinh(x/2) − Σ c_j C_{a_j}]`, `σ = Σ c_j sinh(a_j/2)`);
  `sum_mul_max_shiftDifference_eq` (positive parts are additive on the cone, so the combined collar
  is the collar of `M`); `abs_signedPrimeShift_sub_le` (two-sided harmonic-identity evaluation
  `|Σ Λ n^{−1/2} m_a(log n − x) − 2 sinh(a/2) sinh(x/2)| ≤ K`, `0 ≤ a ≤ x`);
  `foldedDefect_spanGroundState_le` (defect `≤ −2Φ(x)[σ sinh(x/2) − K Σ|c_j|]` for `x ≥ max a_j`);
  `integral_Ioi_spanShiftDifference_mul_sinh_half` (`σ = 2∫_{x>0} M sinh(x/2)`, the pole moment);
  `spanSourceCoefficient_pos`; `exists_infinity_window_spanGroundState_foldedGenerator_lt_potential`:
  every nonzero nonnegative finite signed superposition is a strict folded subsolution on `[X, ∞)`.
  Insight: the per-shift collar bounds do not combine under mixed signs, but on the cone the collar
  is linear and the obstruction coefficient is the pole moment, positive on the cone — the same
  quantity that makes wide plateaus positive directions forbids supersolutions in the span at
  infinity. No PNT. Standard axioms.
- **C2 · Single-shift completeness (frontier problems 1 and 2 are RH at every shift)** —
  `SingleShiftCompleteness`. `shiftQuotient a F = F/m_a`: every odd `C²_c` test vanishing on
  `(−ε, ε)` is `m_a u` with `u` even `C²_c` vanishing there (`contDiff_shiftQuotient`,
  `phiDoobTest_shiftedGroundState_mul_shiftQuotient`); the corpus half-line witness gives, without
  RH, one such test with negative energy, the same for all shifts
  (`exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis`). For every fixed `a > 0`:
  RH ⟺ `Q(m_a u) ≥ 0 ∀u` (`riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg`)
  ⟺ the same on profiles vanishing near `0`
  (`riemannHypothesis_iff_forall_vanishing_profile_markovEnergy_nonneg`) ⟺ variation inequality
  (`…_forall_variationInequality`) ⟺ pole-free variation inequality `D ≤ 2S + V_a`
  (`…_forall_poleFreeVariationInequality`) ⟺ remainder dominates defect
  (`…_forall_remainder_dominates_defect`); ∃ shift ⟺ ∀ shifts
  (`riemannHypothesis_iff_exists_shift_markovEnergy_nonneg`). Insight: the shift is a gauge — the
  frontier inequalities are not weaker consequences of RH but RH itself at each shift; the origin
  (site of every folded-supersolution failure) carries no zero information; shift averaging can
  only reweight, never enlarge, the test class. Standard axioms.
