# Arithmetic Incidence Positivity (AIP): programme card

- **ID:** aip-2026-10-20
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/review-2010/hard-obstacles-summary-2010.md §2.3 (the field described there)
- **Statement:** Develop the field whose object is the sign of the critical arithmetic form as a
  property of the incidence structure of the integers (which integers are multiples of which, which
  are consecutive), read pair by pair through the gauge-free conductance kernel
  `k(x,y) = dm(|x−y|) + sinh(x/2) sinh(y/2)` of the zero form. Every contribution is an unconditional
  Lean theorem in `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/`, wired into the umbrella
  `GaloisForLFunctions.ArithmeticIncidencePositivity` (registered in `MainTheorems.lean`).

## Goal
Make the negative conductance of the zero form an explicit arithmetic object: where it sits (which
pairs of points, which pairs of integers), how large it is, and what pays it. RH is the statement
that the form is nonnegative on all even profiles in every odd gauge (ACT). The field studies the
form's conductance geometry unconditionally; the open core is the prime-side inequality between
anti-diagonal atoms `|x| + y = log n` and same-side atoms `|x − y| = log m` plus the variance.

## Gates
- [x] 0 → 1 in-progress: folder, umbrella, registration, three modules compiled with `lake env lean`
- [x] README written
- [ ] 1 → 2 fully-proven: the first analytic bridge theorem (bump profiles) proved on paper
- [ ] 2 → 3 formalized: bridge theorem in Lean, axioms `propext, Classical.choice, Quot.sound`
- [ ] 3 → 4 not pursued (user rule: no stage 4)

## Approach
Work in ACT's gauge-free coordinates (odd gauge `M`, even profile `u`, conductance
`M(x)M(y)k(x,y)`): same-side pairs positive, crossing pairs negative where `k > 0`. Separate the
archimedean density (continuous) from the prime atoms (lattice). Prove exact sign laws for the
archimedean part, exact incidence laws for the atoms, then the bridge to profiles built from bumps
at lattice points, then dyadic-window incidence, then the first-prime-window gauge problem.

## Contribution ledger (append-only)

### C1 — Prime-power incidence dominance (`PrimePowerIncidenceDominance.lean`)
- `ratioAtom a b = Λ(b/a)/√(b/a)` (same side, `a ∣ b`), `productAtom a b = Λ(ab)/√(ab)` (crossing),
  `netAtom = ratioAtom − productAtom`.
- `exists_prime_pow_of_isPrimePow_mul`: `ab` a prime power ⇒ `a = p^i`, `b = p^j`.
- `productAtom_le_ratioAtom` (`1 ≤ a < b`), `productAtom_lt_ratioAtom` (`2 ≤ a`, `ab` prime power),
  `productAtom_one_left` (`a = 1`: equality). Net conductance of every lattice pair is `≥ 0`;
  zero exactly on `{1, p^j}` or when no atom is present.
- Skeleton Laplacian: `skeletonEnergy_nonneg`, `productEnergy_le_ratioEnergy`,
  `productEnergy_eq_zero_of_tower_constant` (profiles constant on prime-power towers have no
  crossing energy).
- Insight: the negative prime atoms never win on a lattice pair; the prime obstruction lives strictly
  between lattice points. Imports: `RHTower.WeilPhiDoobPrimeAtoms`. Axioms: standard.

### C2 — Archimedean crossing sign law (`CrossingConductanceSignLaw.lean`)
- `archPairKernel x y = ω(|x−y|) + sinh(x/2)sinh(y/2)`; `crossingSymbol s = cosh(s/2) − 2ω(s)`.
- `archPairKernel_pos_of_sameSide`; `archPairKernel_pos_iff` (`x<y`): `k > 0 ⟺ S(y−x) < cosh((x+y)/2)`.
- `crossingSymbol_strictMonoOn`, `crossingSymbol_two_log_three = 119/120`,
  `crossingSymbol_four_log_two = 3311/2040`, `exists_crossingThreshold`, `crossingThreshold`
  (unique root `s₀ ∈ (2 log 3, 4 log 2)`), `crossingSymbol_lt_one_iff`.
- `archPairKernel_pos_of_lt_threshold`, `archPairKernel_pos_iff_of_eq_threshold` (only the balanced
  pair is neutral), `archPairKernel_balanced_neg_iff`.
- `archPairKernel_reflection_pos_iff`: `(−log a, log a)` negative conductance iff `a ∈ {2,3}`.
- `min_lt_of_archPairKernel_pos`: for `s ≥ 4 log 2` negative crossing pairs have
  `min(|x|,y) < 6 e^{−3s/4}` (collar).
- Imports: `RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal`,
  `ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds`. Axioms: standard.

### C3 — Negative lattice crossing pairs (`LatticeCrossingClassification.lean`)
- `archPairKernel_neg_log_log`: closed form
  `(4(ab)² − (a−1)(b−1)((ab)²−1)) / (4√(ab)((ab)²−1))` for `a, b > 0`, `ab > 1`.
- `archPairKernel_neg_log_log_pos_iff` (naturals): `k > 0 ⟺ (a−1)(b−1)((ab)²−1) < 4(ab)²`.
- `latticeCrossing_inequality_iff` and `archPairKernel_neg_log_log_pos_iff_of_two_le`: for
  `a, b ≥ 2` exactly `{2,2},{2,3},{2,4},{2,5},{3,3}` (near-misses `396 < 400`, `320 < 324`).
- `archPairKernel_zero_pos` (axis pairs), `archPairKernel_neg_log_log_neg_of_six_le`.
- Insight: on the lattice the whole negative archimedean conductance is the axis pairs plus five
  small pairs; with C1 the lattice carries no other negative conductance at all.

### C4 — Incidence inside a dyadic window (`DyadicWindowIncidence.lean`)
- `InDyadicWindow X n := X/2 < n < 2X`; `lt_four_mul_of_inDyadicWindow`.
- `eq_two_mul_or_three_mul_of_dvd`: a proper divisor relation inside a window is a doubling or a
  tripling; `ratioAtom_inDyadicWindow`: same-side atoms inside a window are `0`, `Λ(2)/√2`, `Λ(3)/√3`.
- `exponent_sub_le_one_of_inDyadicWindow`, `exponent_eq_of_inDyadicWindow_of_five_le`: consecutive
  exponents only; primes `≥ 5` have at most one power per window.
- `consecutive_powers_of_isPrimePow_mul`: window product pairs are `(p^i, p^{i+1})`, `p ∈ {2,3}`;
  `productAtom_lt_of_inDyadicWindow`: their atoms are `< 2 log 3 / X`.
- SRT bridge: `inDyadicWindow_of_mem_lagPrimeWindow` (`2w < log 2`, `n ≥ 1`),
  `eq_two_mul_or_three_mul_of_mem_lagPrimeWindow`, `productAtom_lt_of_mem_lagPrimeWindow`.
- Imports: C1 and `SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine`. Axioms: standard.
- README written (`ArithmeticIncidencePositivity/README.md`): why, objects, mechanisms 1–11, traps,
  open problems 1–6, principles.

### C5 — Polar compensation on the anti-diagonals (`AntiDiagonalPolarCompensation.lean`)
- `crossingPolarWeight s a = sinh(a/2) sinh((s−a)/2) = (cosh(s/2) − cosh(s/2 − a))/2`; symmetric, zero
  at both ends, maximum `sinh²(s/4)` at the midpoint (`crossingPolarWeight_le_midpoint`, strict
  off the midpoint); `tendsto_crossingPolarWeight_zero` (axis law).
- `archPairKernel_antiDiagonal_pos_iff`; `archPairKernel_antiDiagonal_pos_of_le_nine` (`2 ≤ n ≤ 9`:
  whole anti-diagonal negative); `antiDiagonal_collar_of_sixteen_le` (`n ≥ 16`: within `6 n^{−3/4}`
  of an axis).
- Pointwise payment: `archLevyDensity_le_polar_of_kernel_nonpos`, `archCrossing_le_variance_of_kernel_nonpos`;
  `offCollar` measurable; `lintegral_archCrossingDensity_offCollar_le` (any profile, any gauge with
  `M(x)M(y) ≤ 0` across the origin).
- `polarPaymentScale n = Λ(n)/√n / sinh²(log n/4) = 4Λ(n)/(√n−1)²` (`polarPaymentScale_eq`),
  `≤ 16 log n / n` for `n ≥ 4`.
- Imports: C2, `RHTower.WeilPhiDoobPrimeAtoms`. Axioms: standard.

### C6 — Collar measure and the ten moduli (`PrimeAtomVersusPoleClassification.lean`)
- `archPairKernel_antiDiagonal_eq`: `k_arch(−a, s−a) = ω(s) − P_s(a)`; `antiDiagonalCollar s`
  measurable; `antiDiagonalCollar_subset` (within `6e^{−3s/4}` of the ends, `s ≥ 4 log 2`);
  `volume_antiDiagonalCollar_le` (`≤ 12 e^{−3s/4}`); `lintegral_antiDiagonalCollar_le` (unpaid
  archimedean mass `≤ 12 ω(s) e^{−3s/4}`).
- Logarithm bounds: `log_add_one_sub_div_le_log` (tangent bound), `four_mul_log_le_sqrt_sub_one_sq`
  (`x ≥ 23`, via `log r ≤ sinh(log r)` on the fourth root and `r³ − r ≥ 8`),
  `four_mul_log_le_sqrt_sub_one_sq_of_sq_le` (`p ≥ 5`, `n ≥ p²`),
  `sqrt_sub_one_sq_lt_four_log_of_prime_le_nineteen` (eight explicit primes).
- `sqrt_sub_one_sq_lt_four_vonMangoldt_iff`: for `n ≥ 2`, `(√n−1)² < 4Λ(n)` iff
  `n ∈ atomDominatedModuli = {2,3,4,5,7,9,11,13,17,19}`.
- `one_lt_polarPaymentScale_iff`, `crossingPolarWeight_lt_vonMangoldtAtom` (atom exceeds polar weight
  everywhere on the anti-diagonal of a listed `n`), `antiDiagonal_total_pos_of_mem`,
  `vonMangoldtAtom_le_crossingPolarWeight_midpoint` (all other `n ≥ 2`).
- Insight: the pole pays the archimedean crossing density off a collar of length `O(e^{−3s/4})` and
  never pays an atom near the axes; among atoms it fails at the midpoint exactly for the primes up to
  `19` and for `4`, `9`. The prime-side open core is the axis region of every anti-diagonal plus
  the ten whole anti-diagonals. Imports: C5. Axioms: standard.
- README extended: polar-compensation paragraph, objects, mechanisms 12–18, three traps,
  open problems 1′ and sharpened 3.

## Conjecture queue
1. (done as C4) Dyadic-window incidence.
2. Bump-profile bridge: for even `u` built from bumps at `± log a`, the prime-atom part of ACT's
   `signedJumpEnergy` decomposes into ratio and product pairs with the common gauge factor; the
   archimedean self-energy of a bump of width `w` is `≍ w log(1/w)` and dominates as `w → 0`.
3. Sharp collar asymptotic: `min(|x|, y) ∼ 4 e^{−s}` on the boundary of the negative region.
4. Total lattice kernel (archimedean + atoms) sign law on `(−log a, log b)`; the five pairs with the
   prime atoms added (`{2,2}`: `ab = 4`, product atom `log 2 / 2`; `{2,4}`: `ab = 8`; `{3,3}`: `ab = 9`).
7. Integrated polar payment against a gauge: for odd `M`, atom mass vs polar mass along the
   anti-diagonal of `n`; which gauges pay every `n ∉ atomDominatedModuli`; the axis law makes the
   answer depend on the decay of `M` at `0`.
8. Sharp unpaid mass: replace `12 ω(s) e^{−3s/4}` by the true order `e^{−3s/2}` (collar `∼ 4e^{−s}`).
5. Parity pair: complete-period sieve forms are even in the Selberg coordinates (invariant under all
   sign characters); the first-octave response is not.
6. Open core: extend a gauge argument through the first prime window past `log 2 / 2`, paying the
   single atom `Λ(2)/√2` by the potential (summary §2.3, mechanism 1).

## Log
- 2026-10-20 — folder, umbrella and registration created; C1–C3 compiled with `lake env lean`,
  oleans produced with `lake --old env lean -j 1 -o`; README pending.
- 2026-10-20 — C4 (dyadic window incidence, SRT bridge) compiled and wired; README written; umbrella
  compiles; all audited theorems depend only on `propext, Classical.choice, Quot.sound`.
- 2026-10-20 — C5 (polar compensation) and C6 (collar measure, ten-moduli classification) compiled,
  wired, oleans built, umbrella recompiled; README extended with the continuum section. Audited
  theorems depend only on `propext, Classical.choice, Quot.sound`.
