# Zero-forcing calculus, closed transport configurations, and quartet Galois invariants

- **ID:** zero-forcing-calculus-and-transport-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-1511/obstacles-summary.md` §§2.6, 2.11, 2.21
- **Statement:** Every zero `ρ` of `ζ` with `Re ρ > ½` satisfies `½ < Re ρ ≤ 7/8` and `Im ρ ≠ 0`, forces its four-element quartet `Q(ρ) = {ρ, ρ̄, 1 − ρ, 1 − ρ̄}` of equal multiplicity, and forces no zero outside `Q(ρ)` through any Witt Euler-product monomial, Ramanujan/Rankin–Selberg convolution, Brauer permutation relation, or height-local Galois action without either an analytic continuation input across the pole boundary or a height/abscissa coincidence; the closed configurations under `k`-fold descent and dyadic doubling, the `[½, 9/16)` squarefree pole ruler, the isolated-quartet Galois discriminant and mixed-trace laws, and the expanding-lever corollaries to `RiemannHypothesis` and all width rulers hold unconditionally.

## Goal
Resolve completely the zero-forcing question of `obstacles-summary.md` §§2.6, 2.11, and 2.21:
1. Classify all locally finite functional-equation-symmetric configurations in `0 < Re s < 1` closed under the transports of `ζ(s)^m/ζ(ks)` (`k ≥ 2`) and `ζ(2s)/ζ(s)`, and decide closure of a single off-line quartet.
2. Determine exact meromorphic orders, pole-abscissa rulers, shift margins, and character cancellations across Witt monomials, Ramanujan convolutions, and Artin–Brauer permutation relations.
3. Determine the exact invariants of an isolated off-line quartet over the prime trace field `B` in both critical-parity regimes (`½ + it` absent vs. present).
4. Prove the unconditional deductions from band-expanding and depth-expanding zero-forcing laws to `RiemannHypothesis`, all EDCS width rulers, and eternal-AdS strip analyticity.

## Gates
- [x] 0 → 1  in-progress: exact classification, no-go, Galois discriminant, and ruler/RH deduction statements fixed
- [x] 1 → 2  fully-proven: complete dependency-closed paper proofs below (`[PROVED HERE]`)
- [x] 2 → 3  formalized: Lean modules in `formal/GaloisForLFunctions/ZeroForcingCalculus/`, `lake --old env lean` green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Paper proof

### 1. Quartet forcing and closed transport configurations (`[PROVED HERE]`)
- **Quartet of an off-line zero.** If `ζ(ρ) = 0` and `Re ρ > ½`, then `Re ρ ≤ 7/8` (`riemannZeta_zero_mem_quasiRH_strip`) and `Im ρ ≠ 0` (since `(x − 1)ζ(x) > 0` on `x > 0` forces `ζ(x) < 0` on `(0, 1)`). Conjugation `ξ(s̄) = conj(ξ(s))` and functional reflection `ξ(1 − s) = ξ(s)` force `Q(ρ) = {ρ, ρ̄, 1 − ρ, 1 − ρ̄}` to consist of four pairwise distinct zeros of `ζ` of identical analytic/meromorphic order (`Re ρ ≠ 1 − Re ρ` and `Im ρ ≠ −Im ρ`).
- **`k`-fold descent (`ζ(s)^m/ζ(ks)`, `k ≥ 2`, `m ≥ 1`).** Let `Z ⊆ {0 < Re s < 1}` be locally finite on compact subsets of `{0 < Re s < 1}` and symmetric under `z ↦ 1 − z̄`.
  - Under full-strip descent (`∀ z ∈ Z, z/k ∈ Z`), `Z = ∅`: iterating `z ↦ z/k` on a point of `Z` and reflecting `k/(k + 1)` leaves the unique limit point `k/(k + 1)`.
  - Under right-zero descent (`∀ z ∈ Z, Re z > ½ → z/k ∈ Z`), `ψ_k(z) = 1 − z̄/k` maps `{½ < Re z < 1}` into `(1 − 1/k, 1 − 1/(2k)) ⊂ (½, 1)` and satisfies `ψ_k^[n](z) = k/(k + 1) + (−1/k)^n (Re z − k/(k + 1)) + i (−1)^n (Im z)/k^n → k/(k + 1)`. Any `z ∈ Z` with `Re z > ½` and `z ≠ k/(k + 1)` generates an infinite orbit in a compact subset of `{0 < Re s < 1}`, contradicting local finiteness, while `k/(k + 1)` steps once to `1/(k + 1)` (`Re ≤ 1/3 < ½`) and halts. Thus `Z` is closed iff `Z ∩ {Re s > ½} ⊆ {k/(k + 1)}`, and when `∀ z ∈ Z, Im z ≠ 0`, iff `Z ⊆ {Re s = ½}`.
- **Doubling transport (`ζ(2s)/ζ(s)`).** Let `Z ⊆ {0 < Re s < 1}` be closed under `z ↦ z̄` and `z ↦ 1 − z`.
  - Under full-strip doubling, `Z = ∅`; under right-zero doubling (`Re z > ½ → 2z ∈ Z`), `Re(2z) > 1` leaves `{0 < Re s < 1}`, so closure holds iff `Z ⊆ {Re s = ½}`.
  - Under left-zero doubling (`Re z < ½ → 2z ∈ Z`), an off-line point `ρ = (½ + δ) + iγ` (`0 < δ < ½`) reflects to `1 − ρ̄ = (½ − δ) + iγ` (`Re < ½`), doubling to `(1 − 2δ) + 2iγ` at critical distance `T(δ) = |2δ − ½|` and ordinate `2γ`. By induction on `n ≥ 1`, `(∀ j < n, T^[j](δ) > 0) ∧ T^[n](δ) = 0` holds iff `δ = m / 2^{n+1}` for an odd integer `1 ≤ m < 2^n`. Every step doubles `|Im|`, so if `Z` has no real zeros (`Im z ≠ 0` on `Z`), `Z` is closed under left-zero doubling iff every `ρ ∈ Z` with `Re ρ > ½` has `Re ρ − ½ = m / 2^{n+1}` (`n ≥ 1`, `1 ≤ m < 2^n` odd) and `½ + 2^n i Im ρ ∈ Z`. An isolated quartet `Q(ρ)` (`½ < Re ρ < 1`, `Im ρ ≠ 0`) is never closed (`2|Im ρ| ≠ |Im ρ|`), and `Z_crit ∪ Q(ρ)` is closed iff `Re ρ = 3/4` and `½ + 2i Im ρ ∈ Z_crit`.

### 2. Witt monomials, squarefree pole ruler, shift margin, and Brauer cancellation (`[PROVED HERE]`)
- **Witt Euler-product monomials.** For `W_e(s) = ∏_{j : Fin K} ζ((j + 1)s)^{e_j}` (`e : Fin K → ℤ`), `ord_s(W_e) = ∑_j e_j ord_{(j+1)s}(ζ)` holds at every `s ∈ ℂ`. Whenever `Re ρ > ½`, `Re((j + 1)ρ) ≥ 2 Re ρ > 1` for `j ≥ 1`, so `ord_{(j+1)ρ}(ζ) = 0` and `ord_ρ(W_e) = e_0 ord_ρ(ζ)`.
- **Unconditional `[½, 9/16)` squarefree pole ruler.** Let `F_m(s) = ((s − 1)ζ(s))^m / ζ(2s)` (`m ∈ ℕ`). On every punctured neighborhood `𝓝[≠] s`, `F_m(w) = zetaResidueUnit(w)^m (2w − 1) / zetaResidueUnit(2w)`. For every `β ∈ [½, 9/16)`, `∀ s, β/2 < Re s → 0 ≤ meromorphicOrderAt F_m s` holds iff `zetaZeroAbscissa ≤ β`:
  - `(⇐)`: For `Re s > β/2`, either `2s = 1` (`zetaResidueUnit(1) = 1 ≠ 0`) or `2s ≠ 1` with `Re(2s) > β ≥ zetaZeroAbscissa` (`ζ(2s) ≠ 0`), so `F_m` agrees on `𝓝[≠] s` with a function analytic at `s`.
  - `(⇒)`: Any zero `ρ` with `β < Re ρ < 1` and `ζ(ρ/2) ≠ 0` gives `ord_{ρ/2}(F_m) = −ord_ρ(ζ) < 0`, contradiction; hence `ζ(ρ/2) = 0`, and `riemannZeta_ne_zero_of_halving` excludes `β < Re z < 2 − β`. Since `riemannZeta_zero_mem_quasiRH_strip` gives `Re ρ ≤ 7/8`, `1 − Re ρ / 2 ≥ 9/16 > β`, excluding all zeros with `Re ρ > β`. At `β = ½`, pole-freeness on `{Re s > ¼}` is equivalent to `RiemannHypothesis`.
- **Ramanujan / Rankin–Selberg shift margin.** For all `a, b, ρ ∈ ℂ`, `(1 + max(0, Re a, Re b, Re(a + b))) − Re((ρ + a + b)/2) ≥ 1 − Re ρ / 2`, which is `≥ 9/16` for every zero `ρ` of `ζ` with `Re ρ > 0`.
- **Brauer permutation cancellation.** For every subgroup `H` of a finite group `G`, `∑_{g ∈ G} (Ind_H^G 1_H)(g) = |G|`. Hence `∑_i c_i Ind_{H_i}^G 1_{H_i} = m · 1_G` implies `∑_i c_i = m`, and `m = 0` gives `∑_i c_i = 0`.

### 3. Isolated-quartet Galois invariants and mixed-trace dichotomy (`[PROVED HERE]`)
Let `B = primeTraceField`, `E = primeTraceExtension`, `G = Gal(E/B)`, and `ρ ∈ XiDivisorSupport` with `β = Re ρ ≠ ½` and `t = Im ρ`.
- **Universal height-trace formula.** `T_t(m) = ∑_{ρ ∈ U_t} mult(ρ) (n_m^ρ + n_m^{ρ̄})`, with `mult(1 − ρ̄) = mult(ρ)`.
- **Regime A (`U_t = {ρ, 1 − ρ̄}`).** `A_{t,p} = p (u_p(ρ) − v_p(ρ))` is real and strictly negative for every prime `p`, so `A_{t,p}² ∈ B` is strictly positive for every prime `p`; `A_{t,p}²` is a square in `B` iff `u_p(ρ) ∈ B` iff `v_p(ρ) ∈ B` iff `G` has no partial flip on `Q(ρ)`; and `T_t(m) = mult(ρ) e^{L/2} (e^{aL} + e^{−aL}) (e^{itL} + e^{−itL})` (`a = β − ½`, `L = primeRelationFrequency m`).
- **Regime B (`½ + it` present).** Sharing `|Im ρ| = |Im ρ₀|` with any critical zero `ρ₀` (`Re ρ₀ = ½`) places `u_p(ρ) = u_p(ρ₀) ∈ B` at every prime `p` and eliminates all partial flips; when `Q(ρ)` is the unique off-line quartet at ordinate `±t`, `U_t = {ρ₀, ρ, 1 − ρ̄}`, `T_t(2e_p) = p (mult(ρ₀) u_p(ρ) + mult(ρ) u_p(ρ) v_p(ρ))`, both `u_p(ρ), v_p(ρ) ∈ B`, and `G` acts on `Q(ρ)` through `{1, c, r, cr}`.

### 4. Expanding zero-forcing laws, width rulers, and `RiemannHypothesis` (`[PROVED HERE]`)
- Open and right-closed band levers `bandLever b₁ b₂` and `closedRightBandLever b₁ b₂` are monotone for `b₁ ≤ b₂` with excluded sets `(b₁, b₂)` and `(b₁, b₂]`.
- Any continuous expanding map `g(x) > x` on `(b₁, b₂)` (resp. `(b₁, b₂]`) whose zero-forcing rule produces either a `ζ`-zero of real part `≥ g(Re ρ)` or a Dirichlet `L`-zero on `Re w > 7/8` away from `(1, 1)` (discharged by `dirichlet_nonzero`) forces `zetaZeroAbscissa ∉ (b₁, b₂)` (resp. `(b₁, b₂]`), jumps every `zetaZeroWidth` ruler from `b₂ − ½` to `b₁ − ½`, and widens `modularWightmanRL` strip analyticity from `(1 − b₂)/2` to `(1 − b₁)/2` (unconditionally from `1/16` to `(1 − b₁)/2` when `b₂ = 7/8`).
- Because `½ ≤ zetaZeroAbscissa ≤ 7/8` unconditionally, continuous depth-expanding forcing on `(½, 7/8]` or a lever family covering `(½, 7/8]` collapses `wall = ½`, `zetaZeroAbscissa = ½`, `zetaZeroWidth = 0`, and proves `RiemannHypothesis`.

## Lean

Umbrella: `formal/GaloisForLFunctions/ZeroForcingCalculus.lean` (wired into `formal/GaloisForLFunctions/MainTheorems.lean`; documentation in `formal/GaloisForLFunctions/ZeroForcingCalculus/README.md`).

1. **`formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean`** (`lake --old env lean` exit 0, `#print axioms`: `[propext, Classical.choice, Quot.sound]`):
   - `offLineZero_quartet`
   - `kFoldDescent_closed_full_iff_empty`
   - `kFoldDescent_closed_right_iff_subset_fixedPoint`
   - `kFoldDescent_closed_right_noReal_iff_critical`
   - `quartet_not_closed_kFoldDescent`
   - `doubling_closed_full_iff_empty`
   - `doubling_closed_right_iff_critical`
   - `doublingDepthMap_halts_at_iff_odd_dyadic`
   - `doubling_closed_left_noReal_iff`
   - `isolated_quartet_not_closed_left_doubling`
   - `critical_union_quartet_closed_left_doubling_iff`
2. **`formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean`** (`lake --old env lean` exit 0, `#print axioms`: `[propext, Classical.choice, Quot.sound]`):
   - `meromorphicAt_riemannZeta`, `meromorphicOrderAt_riemannZeta_ne_top`, `meromorphicOrderAt_riemannZeta_one`
   - `meromorphicOrderAt_wittZetaMonomial`, `meromorphicOrderAt_wittZetaMonomial_of_half_lt_re`
   - `squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le`, `isRuler_squarefreePowerQuotient`
   - `squarefreePowerQuotient_poleFree_quarter_iff_riemannHypothesis`, `squarefreeQuotient_poleFree_iff_zetaZeroAbscissa_le`
   - `ramanujan_shift_margin_ge`, `ramanujan_shift_margin_zeta_zero_ge_nine_sixteenths`
   - `sum_inducedFunction_one`, `brauer_permutation_relation_sum_eq`, `brauer_permutation_relation_sum_eq_zero`
3. **`formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean`** (`lake --old env lean` exit 0, `#print axioms`: `[propext, Classical.choice, Quot.sound]`):
   - `xiSupportMult_mirror`, `primeDivisorTrace_eq_sum_primeUpperFibre`
   - `isolated_quartet_primeUpperFibre_eq`, `isolated_quartet_heightReflectionProduct_eq`
   - `isolated_quartet_heightReflectionProduct_neg`, `isolated_quartet_radicand_square_pos`
   - `isolated_quartet_square_iff_no_partialFlip`, `isolated_quartet_primeDivisorTrace_factorization`
   - `critical_ordinate_eliminates_partialFlip`, `shared_critical_and_isolated_quartet_klein_action`, `shared_critical_and_isolated_quartet_trace_single_two`
4. **`formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean`** (`lake --old env lean` exit 0, `#print axioms`: `[propext, Classical.choice, Quot.sound]`):
   - `isLever_bandLever_iff`, `isLever_closedRightBandLever_iff`, `not_existsDirichletZeroRightOfSevenEighths`
   - `zetaZeroAbscissa_notMem_Ioo_of_band_forcing`, `zetaZeroAbscissa_notMem_Ioc_of_band_forcing`
   - `band_forcing_width_ruler_jump`, `band_forcing_modularWightmanRL_strip_jump`
   - `unconditional_modularWightmanRL_strip_of_seven_eighths_band_forcing`
   - `riemannHypothesis_of_depth_expanding_forcing`, `riemannHypothesis_of_covering_levers`, `wall_eq_half_of_covering_monotone_levers`

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Unconditional inter-quartet zero forcing from `ξ(s) = ξ(1 − s)` and bounded-complexity Euler-product / convolution / Artin–Brauer / height-Galois identities fails:
  1. Witt monomials `∏ ζ((j+1)s)^{e_j}` satisfy `ord_s(W_e) = ∑ e_j ord_{(j+1)s}(ζ)` and have `ord_ρ(W_e) = e_0 ord_ρ(ζ)` on `Re ρ > ½`, leaving an uncancelled pole at `ρ/k` unless analyticity across `{Re s = ½}` is supplied;
  2. Ramanujan shifts have `σ_pole − Re((ρ + a + b)/2) ≥ 1 − Re ρ / 2 ≥ 9/16 > 0`;
  3. Virtual permutation relations orthogonal to `1_G` satisfy `∑ c_i = 0` by Frobenius reciprocity, cancelling `ζ(s)^{∑ c_i}`;
  4. Single-quartet off-line models exist simultaneously in `coshModel {ρ}`, `EulerSymmetric`, and `PrimeEditDivisorOn`, and an isolated quartet at height `t` with no critical zero has `Gal(E/B)`-invariant quartet and `(a ↔ it)`-symmetric height traces `T_t(m)`.
- **Strongest positive survivor:** All four theorem suites above, formalized unconditionally in `formal/GaloisForLFunctions/ZeroForcingCalculus/`.
- **New insight:** Separates pole-creation from zero-forcing into an exact equivalence (`F_m` pole-free on `{Re s > β/2}` iff `Θ ≤ β` on `[½, 9/16)` via the `7/8` seed), classifies the odd-dyadic tent-map preimages `½ + m/2^{n+1}` of Liouville left-doubling, and proves the `(a ↔ it)` symmetry of height-`t` mixed traces on a pure isolated quartet together with its symmetry breaking when `½ + it` is a critical zero.
- **Status:** Formalized in Lean 4 across 4 modules (47 `#print axioms`-verified declarations), wired into `ZeroForcingCalculus.lean` and `MainTheorems.lean`.

## Log
- 2026-11-15 — proved on paper and formalized unconditionally in `formal/GaloisForLFunctions/ZeroForcingCalculus/`.
