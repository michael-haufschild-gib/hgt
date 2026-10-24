import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity
import GaloisForLFunctions.SquareRootThreshold.PolarGroundEnergyAndPoleFreeLagAbscissaBridge
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityPrimeTwo

/-!
# Source-Determinantal Section Theory and Unconditional Arithmetic Riemann–Roch Past the First Prime

In `RiemannRochForZAndTheReflectedPrimePolarLedger`, the cone `strictCoupledArithmeticCone V` is
defined by the positivity of the intersection form (`0 < x · x ∧ 0 < x · (H + V)`): it contains
no section space `Γ(x)`, excludes `0`, `H`, and `V`, and satisfies `AmpleAxiom` vacuously because
`x · (H + V) = 0` is ruled out by definition. Moreover, past the first prime threshold
`(log 2)/2 ≈ 0.34657`, unconditional arithmetic Riemann–Roch (`RiemannRochAxiom`, `AmpleAxiom`,
`BezoutAxiom`) was previously established only on the purely odd subsurface `oddRealTestsAt r`
(`r ≤ 181/500`), while general (non-odd) tests were restricted to `a ≤ 3/10 < (log 2)/2` below the
first prime.

This module constructs a genuine **source-defined determinantal section and effectivity theory** on
polar and scaling surfaces — defined purely from the source function `f` and its two Laplace pole
evaluations without referencing `zetaZeroConfig.W`, the zeros of `ζ`, or `scalingPair x x` — and
proves **unconditional arithmetic Riemann–Roch past the first prime `2`** on the full
ample-orthogonal primitive hyperplane `primitiveSmoothRealTestsAt r` (containing both even and odd
tests, with arbitrary odd pole moment) through `r ≤ ½(log 2 + 1/50) ≈ 0.35657`, as well as
all-aperture graded arithmetic Riemann–Roch and two-prime strip allocation at `r = 23/40`:

1. **Source-Defined Section Spaces and Determinantal Cones on Polar Surfaces (§1):**
   For any polar surface `S : PolarSurface C` and source functional `Φ : C → ℝ`, the **source
   section space** `S.sourceSections Φ x` consists of pole-amplitude witnesses
   `(α, β) ∈ [0, x · H] × [0, x · V]` whose hyperbolic capacity `2αβ` pays the source energy
   `Φ(x)`. The resulting effectivity cone `S.sourceCone Φ = {x | (S.sourceSections Φ x).Nonempty}`
   is characterized by `0 ≤ x · H ∧ 0 ≤ x · V ∧ Φ(x) ≤ S.polar x x` (`mem_sourceCone_iff`) and by
   the `2 × 2` determinantal AG-mean inequality
   `∀ u v : ℝ, 2 u² v² Φ(x) ≤ (u² (x · H) + v² (x · V))²` (`mem_sourceCone_iff_agm`). Unlike
   `strictCoupledArithmeticCone`, `S.sourceCone Φ` contains `0`, `H`, `V`, and `ample = H + V`
   whenever `Φ` vanishes on the pole plane, and satisfies `S.AmpleAxiom` **non-vacuously** whenever
   `Φ` is faithful on the primitive subspace (`sourceCone_ample_of_faithful`). Whenever
   `0 ≤ Φ(x) ≤ S.defect x x`, both `S.sourceCone Φ` and its strict interior
   `S.strictSourceCone Φ` satisfy `RiemannRochAxiom`, `AmpleAxiom`, and
   `SurfaceRiemannRochAxiom 0 0`, with ampleness requiring the stated primitive faithfulness.
   Bézout requires the opposite bound `S.defect x x ≤ Φ(x)` together with Hodge index
   (`sourceCone_riemannRoch_of_le_defect`, `strictSourceCone_bezout_of_defect_le`).

2. **The Convex, Hecke-Stable `L²` Source Cone on `scalingSubsurface V` (§2):**
   On `scalingSubsurface V` (`V ≤ realTests`), the source energy
   `l2SourceEnergy c V (a, b, f) = c ∫ f(u)² du` depends only on the source integral `∫ f²` and the
   Laplace pole evaluations `deg_H(x) = a + ∫ f(u) e^{-u/2} du`,
   `deg_V(x) = b + ∫ f(u) e^{u/2} du`. We prove that for every `c ≥ 0`:
   * `l2SourceCone c V` is a **true convex cone** containing `0, H, V, H + V`, closed under
     addition (`l2SourceCone_add`, proved via `L²` Cauchy–Schwarz and hyperbolic reverse
     Cauchy–Schwarz) and nonnegative scalar multiplication (`l2SourceCone_smul`).
   * On `scalingSurface`, `l2SourceCone c ⊤` and `strictL2SourceCone c ⊤` are **unconditionally
     invariant under all Adams operations `adamsOp q` and Hecke correspondences
     `heckeCorrespondence q` (`q > 0`)** (`adamsOp_mem_l2SourceCone`,
     `heckeCorrespondence_mem_l2SourceCone`), without assuming `HodgeIndex`.
   * For every `c > 0` and every `V ≤ realTests`, `(scalingSubsurface V).AmpleAxiom (l2SourceCone c V)`
     holds **unconditionally and non-vacuously** (`l2SourceCone_ample`): if `x ∈ l2SourceCone c V`
     has `x · (H + V) = 0`, then `x · H = x · V = 0`, pinching `∫ f² = 0`, which by continuity and
     compact support of `f ∈ realTests` forces `f = 0` everywhere and `x = (0, 0, 0) = 0`.
   * **Exact Quantitative Equivalence of `RiemannRochAxiom` (`l2SourceCone_riemannRoch_iff_weilPair_ge`,
     `strictL2SourceCone_riemannRoch_iff_weilPair_ge`):** For every `c > 0`, `RiemannRochAxiom` holds
     for `l2SourceCone c V` (and for `strictL2SourceCone c V`) if and only if
     `∀ f ∈ V, c ∫ f(u)² du ≤ weilPair f f`.

3. **The All-Aperture Explicit-Formula Source Incidence Cone on `oddRealTestsAt r` (§3):**
   For every `0 < r < R`, the source-defined incidence functional `sourceIncidenceFunctional r R`
   built purely from `surplusPool`, `crossingPotentialTerm`, `evenStripGain`, `oddStripCost`,
   `gaugeRemainder`, and `poleCharge` defines `sourceIncidenceCone r R`, which coincides
   identically with `strictCoupledArithmeticCone (oddRealTestsAt r)` across all apertures
   (`sourceIncidenceCone_eq_strictCoupledArithmeticCone`) without referencing `zetaZeroConfig.W`.

4. **Unconditional Arithmetic Riemann–Roch Past the First Prime on the Full Ample-Orthogonal
   Primitive Hyperplane `primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`) (§4):**
   * **Exact Ample-Orthogonality Law (`pureTestCycle_pair_ample_eq`,
     `pureTestCycle_pair_ample_eq_zero_iff`):** On `scalingSurface`, every pure test cycle
     `(0, 0, f)` satisfies `(0, 0, f) · (H + V) = 2 evenPoleMoment f`. Thus the exact subspace of
     tests orthogonal to the ample class `H + V` is `evenPoleMoment f = ∫ f(u) cosh(u/2) du = 0`,
     containing all odd tests **together with** the entire codimension-`1` subspace of even tests
     (with completely unrestricted `oddPoleMoment f`).
   * **Unconditional Mixed-Parity Coercivity and Riemann–Roch Past the Prime `2`
     (`weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo`,
     `primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo`,
     `strictCoupledArithmeticCone_primitiveSmooth_riemannRoch_primeTwo`,
     `l2SourceCone_primitiveSmooth_riemannRoch_primeTwo`):**
     For every aperture `r ≤ ½(log 2 + 1/50) ≈ 0.35657` (strictly past the first prime threshold
     `(log 2)/2 ≈ 0.34657`, so the prime `2` actively enters both parities) and every smooth test
     `f ∈ primitiveSmoothRealTestsAt r`, orthogonal parity splitting
     `weilPair f f = fullZeroForm f_even + fullZeroForm f_odd` combines the `1/20` polar ground-energy
     certificate on the even part `f_even` (`one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo`)
     with the `1/1000` Schur-lending certificate on the unrestricted odd part `f_odd`
     (`fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`) to prove
     `weilPair f f ≥ (1/1000) ∫ f²`. Consequently, on `scalingSubsurface (primitiveSmoothRealTestsAt r)`
     (and on `polarFreeSmoothRealTestsAt r` with margin `1/20`), `HodgeIndex`, `RiemannRochAxiom`,
     `AmpleAxiom`, and `SurfaceRiemannRochAxiom 0 0` hold **unconditionally** for the source-defined
     cones `l2SourceCone` and `strictL2SourceCone`. Bézout is proved for
     `strictCoupledArithmeticCone`; the source coercive floor alone does not prove Bézout for
     the larger `L²` source cones.

5. **All-Aperture Graded Source Riemann–Roch and the Overlapping Two-Prime Window `r = 23/40` (§5):**
   Across **all** apertures `r > 0`, the Chebyshev spectral floor `-(10 + 68 e^r) ∫ f² ≤ weilPair f f`
   on `polarFreeSmoothRealTestsAt r` and the graded incidence floor `-78 e^r ∫ f² ≤ weilPair f f`
   on `oddRealTestsAt r` supply unconditional `RiemannRochAxiom` and `SurfaceRiemannRochAxiom 0 0`
   for `gradedL2SourceCone (-(10 + 68 e^r)) (polarFreeSmoothRealTestsAt r)` and
   `gradedL2SourceCone (-78 e^r) (oddRealTestsAt r)` at every scale `r > 0`. At the overlapping two-prime
   window `r = 23/40 = 0.575` (`relevantShifts (23/40) = {2, 3}`), the Castelnuovo–Severi defect on
   `scalingSubsurface (oddRealTestsAt (23/40))` absorbs both prime shifts `2` and `3` into the
   archimedean strip surplus `2 stripSurplus f (log 2 - 23/40) (23/40)` with `(1/62) ∫_{S₂} f²` to
   spare.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Source-Defined Section Spaces and Determinantal Cones on a Polar Surface -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **The Source Section Space (`sourceSections`):**
For a source energy functional `Φ : C → ℝ`, a section witness of a cycle `x : C` is a pair of
nonnegative fiber amplitudes `(α, β) ∈ [0, x · H] × [0, x · V]` whose hyperbolic pole capacity
`2αβ` pays the source energy `Φ(x)`. -/
def sourceSections (Φ : C → ℝ) (x : C) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ S.pair x S.H ∧ 0 ≤ p.2 ∧ p.2 ≤ S.pair x S.V ∧
    Φ x ≤ 2 * p.1 * p.2}

/-- **The Strict Source Section Space (`strictSourceSections`):**
Strictly positive fiber amplitudes `(α, β) ∈ (0, x · H] × (0, x · V]` whose hyperbolic pole
capacity `2αβ` strictly exceeds `Φ(x)`. -/
def strictSourceSections (Φ : C → ℝ) (x : C) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ S.pair x S.H ∧ 0 < p.2 ∧ p.2 ≤ S.pair x S.V ∧
    Φ x < 2 * p.1 * p.2}

/-- **The Closed Source Determinantal Cone (`sourceCone`):**
Cycles `x : C` admitting at least one source section (`(S.sourceSections Φ x).Nonempty`). -/
def sourceCone (Φ : C → ℝ) : Set C :=
  {x : C | (S.sourceSections Φ x).Nonempty}

/-- **The Strict Source Determinantal Cone (`strictSourceCone`):**
Cycles `x : C` admitting a strict source section (`(S.strictSourceSections Φ x).Nonempty`). -/
def strictSourceCone (Φ : C → ℝ) : Set C :=
  {x : C | (S.strictSourceSections Φ x).Nonempty}

/-- Helper: self-polar value is `2 (x · H)(x · V)`. -/
theorem polar_self (x : C) : S.polar x x = 2 * S.pair x S.H * S.pair x S.V := by
  simp only [polar]
  ring

/-- Helper: intersection of `ample = H + V` with `H` is `1`. -/
theorem pair_ample_H : S.pair S.ample S.H = 1 := by
  simp only [ample, map_add, LinearMap.add_apply, S.pair_H_H, S.pair_V_H, zero_add]

/-- Helper: intersection of `ample = H + V` with `V` is `1`. -/
theorem pair_ample_V : S.pair S.ample S.V = 1 := by
  simp only [ample, map_add, LinearMap.add_apply, S.pair_H_V, S.pair_V_V, add_zero]

/-- Helper: left additivity of `S.pair`. -/
theorem pair_add_left (x y z : C) : S.pair (x + y) z = S.pair x z + S.pair y z := by
  simp

/-- Helper: left scalar linearity of `S.pair`. -/
theorem pair_smul_left (t : ℝ) (x z : C) : S.pair (t • x) z = t * S.pair x z := by
  simp

/-- Helper: left negation of `S.pair`. -/
theorem pair_neg_left (x z : C) : S.pair (-x) z = -S.pair x z := by
  simp

/-- Helper: `S.polar (-x) (-x) = S.polar x x`. -/
theorem polar_neg_self (x : C) : S.polar (-x) (-x) = S.polar x x := by
  simp [polar]

/-- Helper: `S.defect (-x) (-x) = S.defect x x`. -/
theorem defect_neg_self (x : C) : S.defect (-x) (-x) = S.defect x x := by
  simp [defect, polar]

/-- **Determinantal characterization of `sourceCone`:**
A cycle `x` has a nonempty source section space if and only if it lies in the nef quadrant
(`0 ≤ x · H` and `0 ≤ x · V`) and its pole capacity `S.polar x x = 2(x · H)(x · V)` pays `Φ(x)`. -/
theorem mem_sourceCone_iff (Φ : C → ℝ) (x : C) :
    x ∈ S.sourceCone Φ ↔ 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x := by
  constructor
  · rintro ⟨⟨α, β⟩, hα0, hαH, hβ0, hβV, hΦ⟩
    have hH0 : 0 ≤ S.pair x S.H := hα0.trans hαH
    have hV0 : 0 ≤ S.pair x S.V := hβ0.trans hβV
    refine ⟨hH0, hV0, ?_⟩
    rw [S.polar_self]
    have hmul : α * β ≤ S.pair x S.H * S.pair x S.V := mul_le_mul hαH hβV hβ0 hH0
    linarith
  · rintro ⟨hH0, hV0, hΦ⟩
    refine ⟨(S.pair x S.H, S.pair x S.V), hH0, le_rfl, hV0, le_rfl, ?_⟩
    rwa [← S.polar_self]

/-- **Determinantal characterization of `strictSourceCone`:**
A cycle `x` has a strict source section if and only if `0 < x · H`, `0 < x · V`, and
`Φ(x) < S.polar x x`. -/
theorem mem_strictSourceCone_iff (Φ : C → ℝ) (x : C) :
    x ∈ S.strictSourceCone Φ ↔ 0 < S.pair x S.H ∧ 0 < S.pair x S.V ∧ Φ x < S.polar x x := by
  constructor
  · rintro ⟨⟨α, β⟩, hα0, hαH, hβ0, hβV, hΦ⟩
    have hH0 : 0 < S.pair x S.H := hα0.trans_le hαH
    have hV0 : 0 < S.pair x S.V := hβ0.trans_le hβV
    refine ⟨hH0, hV0, ?_⟩
    rw [S.polar_self]
    have hmul : α * β ≤ S.pair x S.H * S.pair x S.V := mul_le_mul hαH hβV hβ0.le hH0.le
    linarith
  · rintro ⟨hH0, hV0, hΦ⟩
    refine ⟨(S.pair x S.H, S.pair x S.V), hH0, le_rfl, hV0, le_rfl, ?_⟩
    rwa [← S.polar_self]

/-- **`2 × 2` AG-Mean Gram Characterization of `sourceCone`:**
A cycle `x` belongs to `S.sourceCone Φ` if and only if `0 ≤ x · H`, `0 ≤ x · V`, and for all
positive weights `u, v > 0`, `2 u v Φ(x) ≤ (u (x · H) + v (x · V))²`. -/
theorem mem_sourceCone_iff_agm (Φ : C → ℝ) (x : C) :
    x ∈ S.sourceCone Φ ↔
      0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧
        ∀ u v : ℝ, 0 < u → 0 < v →
          2 * u * v * Φ x ≤ (u * S.pair x S.H + v * S.pair x S.V) ^ 2 := by
  rw [S.mem_sourceCone_iff]
  refine and_congr_right fun hH => and_congr_right fun hV => ⟨fun hΦ u v hu hv => ?_, fun h => ?_⟩
  · rw [S.polar_self] at hΦ
    have h1 : 2 * u * v * Φ x ≤ 2 * u * v * (2 * S.pair x S.H * S.pair x S.V) :=
      mul_le_mul_of_nonneg_left hΦ (by positivity)
    have h2 : 0 ≤ (u * S.pair x S.H - v * S.pair x S.V) ^ 2 := sq_nonneg _
    nlinarith
  · rw [S.polar_self]
    by_contra hlt
    push Not at hlt
    have hΦpos : 0 < Φ x := by nlinarith
    by_cases hH0 : S.pair x S.H = 0
    · have hu := h (S.pair x S.V ^ 2 / Φ x + 1) 1 (by positivity) one_pos
      rw [hH0] at hu
      have hmul : (S.pair x S.V ^ 2 / Φ x + 1) * Φ x = S.pair x S.V ^ 2 + Φ x := by
        rw [add_mul, div_mul_cancel₀ _ hΦpos.ne', one_mul]
      nlinarith [sq_nonneg (S.pair x S.V)]
    · by_cases hV0 : S.pair x S.V = 0
      · have hv := h 1 (S.pair x S.H ^ 2 / Φ x + 1) one_pos (by positivity)
        rw [hV0] at hv
        have hmul : (S.pair x S.H ^ 2 / Φ x + 1) * Φ x = S.pair x S.H ^ 2 + Φ x := by
          rw [add_mul, div_mul_cancel₀ _ hΦpos.ne', one_mul]
        nlinarith [sq_nonneg (S.pair x S.H)]
      · have hHpos : 0 < S.pair x S.H := lt_of_le_of_ne hH (Ne.symm hH0)
        have hVpos : 0 < S.pair x S.V := lt_of_le_of_ne hV (Ne.symm hV0)
        have hVH := h (S.pair x S.V) (S.pair x S.H) hVpos hHpos
        nlinarith [mul_pos hVpos hHpos]

/-- Every strict source cycle belongs to the closed source cone. -/
theorem strictSourceCone_subset_sourceCone (Φ : C → ℝ) :
    S.strictSourceCone Φ ⊆ S.sourceCone Φ := by
  intro x hx
  rw [S.mem_strictSourceCone_iff] at hx
  rw [S.mem_sourceCone_iff]
  exact ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩

/-- The zero cycle belongs to `S.sourceCone Φ` whenever `Φ(0) ≤ 0`. -/
theorem zero_mem_sourceCone {Φ : C → ℝ} (h0 : Φ 0 ≤ 0) : 0 ∈ S.sourceCone Φ := by
  rw [S.mem_sourceCone_iff]
  simp [PolarSurface.polar, h0]

/-- The horizontal pole class `H` belongs to `S.sourceCone Φ` whenever `Φ(H) ≤ 0`. -/
theorem H_mem_sourceCone {Φ : C → ℝ} (hH : Φ S.H ≤ 0) : S.H ∈ S.sourceCone Φ := by
  rw [S.mem_sourceCone_iff]
  simp [PolarSurface.polar, S.pair_H_H, S.pair_H_V, hH]

/-- The vertical pole class `V` belongs to `S.sourceCone Φ` whenever `Φ(V) ≤ 0`. -/
theorem V_mem_sourceCone {Φ : C → ℝ} (hV : Φ S.V ≤ 0) : S.V ∈ S.sourceCone Φ := by
  rw [S.mem_sourceCone_iff]
  simp [PolarSurface.polar, S.pair_V_H, S.pair_V_V, hV]

/-- The ample class `H + V` belongs to `S.sourceCone Φ` whenever `Φ(H + V) ≤ 2`. -/
theorem ample_mem_sourceCone {Φ : C → ℝ} (hA : Φ S.ample ≤ 2) : S.ample ∈ S.sourceCone Φ := by
  rw [S.mem_sourceCone_iff, S.polar_self, S.pair_ample_H, S.pair_ample_V]
  refine ⟨ zero_le_one, zero_le_one, by linarith ⟩

/-- The ample class `H + V` belongs to `S.strictSourceCone Φ` whenever `Φ(H + V) < 2`. -/
theorem ample_mem_strictSourceCone {Φ : C → ℝ} (hA : Φ S.ample < 2) :
    S.ample ∈ S.strictSourceCone Φ := by
  rw [S.mem_strictSourceCone_iff, S.polar_self, S.pair_ample_H, S.pair_ample_V]
  refine ⟨ zero_lt_one, zero_lt_one, by linarith ⟩

/-- Every cycle in `S.sourceCone Φ` has nonnegative degree against `ample = H + V`. -/
theorem pair_ample_nonneg_of_mem_sourceCone {Φ : C → ℝ} {x : C} (hx : x ∈ S.sourceCone Φ) :
    0 ≤ S.pair x S.ample := by
  rw [S.mem_sourceCone_iff] at hx
  simp only [ample, map_add]
  linarith

/-- Every cycle in `S.strictSourceCone Φ` has strictly positive degree against `ample = H + V`. -/
theorem pair_ample_pos_of_mem_strictSourceCone {Φ : C → ℝ} {x : C}
    (hx : x ∈ S.strictSourceCone Φ) : 0 < S.pair x S.ample := by
  rw [S.mem_strictSourceCone_iff] at hx
  simp only [ample, map_add]
  linarith

/-- **Unconditional ampleness of `strictSourceCone`:**
Because every cycle in `S.strictSourceCone Φ` has strictly positive fiber degrees, `S.AmpleAxiom`
holds unconditionally for `S.strictSourceCone Φ`. -/
theorem strictSourceCone_ample (Φ : C → ℝ) : S.AmpleAxiom (S.strictSourceCone Φ) := by
  intro x hx hxA
  exact False.elim ((S.pair_ample_pos_of_mem_strictSourceCone hx).ne' hxA)

/-- **Non-vacuous ampleness of `sourceCone` from primitive faithfulness:**
If `Φ` is nonnegative and vanishes on primitive cycles (`x · H = x · V = 0`) only on the numerical
radical (`∀ y, x · y = 0`), then `S.sourceCone Φ` satisfies `S.AmpleAxiom` non-vacuously (even
though `0 ∈ S.sourceCone Φ`). -/
theorem sourceCone_ample_of_faithful {Φ : C → ℝ}
    (hnonneg : ∀ x, S.pair x S.H = 0 → S.pair x S.V = 0 → 0 ≤ Φ x)
    (hfaith : ∀ x, S.pair x S.H = 0 → S.pair x S.V = 0 → Φ x = 0 → ∀ y, S.pair x y = 0) :
    S.AmpleAxiom (S.sourceCone Φ) := by
  intro x hx hxA
  rw [S.mem_sourceCone_iff, S.polar_self] at hx
  rcases hx with ⟨hH, hV, hΦ⟩
  have hsum : S.pair x S.H + S.pair x S.V = 0 := by
    simpa [ample, map_add] using hxA
  have hH0 : S.pair x S.H = 0 := by linarith
  have hV0 : S.pair x S.V = 0 := by linarith
  have hΦle : Φ x ≤ 0 := by linarith [show 2 * S.pair x S.H * S.pair x S.V = 0 by rw [hH0]; ring]
  have hΦ0 : Φ x = 0 := le_antisymm hΦle (hnonneg x hH0 hV0)
  exact hfaith x hH0 hV0 hΦ0

/-- If `Φ` dominates the Castelnuovo–Severi defect `S.defect x x` (`S.defect x x ≤ Φ x`), then every
cycle in `S.sourceCone Φ` belongs to `S.positiveCone`. -/
theorem sourceCone_subset_positiveCone_of_defect_le {Φ : C → ℝ}
    (hge : ∀ x, S.defect x x ≤ Φ x) : S.sourceCone Φ ⊆ S.positiveCone := by
  intro x hx
  have hdeg : 0 ≤ S.pair x S.ample := S.pair_ample_nonneg_of_mem_sourceCone hx
  rw [S.mem_sourceCone_iff] at hx
  have hd : S.polar x x - S.pair x x ≤ Φ x := hge x
  refine ⟨?_, hdeg⟩
  linarith [hx.2.2, hd]

/-- If `Φ` dominates `S.defect x x` (`S.defect x x ≤ Φ x`), then every cycle in
`S.strictSourceCone Φ` belongs to `S.openPositiveCone`. -/
theorem strictSourceCone_subset_openPositiveCone_of_defect_le {Φ : C → ℝ}
    (hge : ∀ x, S.defect x x ≤ Φ x) : S.strictSourceCone Φ ⊆ S.openPositiveCone := by
  intro x hx
  have hdeg : 0 < S.pair x S.ample := S.pair_ample_pos_of_mem_strictSourceCone hx
  rw [S.mem_strictSourceCone_iff] at hx
  have hd : S.polar x x - S.pair x x ≤ Φ x := hge x
  refine ⟨?_, hdeg⟩
  linarith [hx.2.2, hd]

/-- **Riemann–Roch for `strictSourceCone` from defect domination:**
If `Φ` is even (`Φ(-x) = Φ(x)`), nonnegative, and bounded above by `S.defect x x`, then
`S.strictSourceCone Φ` satisfies `S.RiemannRochAxiom`. -/
theorem strictSourceCone_riemannRoch_of_le_defect {Φ : C → ℝ}
    (heven : ∀ x, Φ (-x) = Φ x) (hnonneg : ∀ x, 0 ≤ Φ x) (hle : ∀ x, Φ x ≤ S.defect x x) :
    S.RiemannRochAxiom (S.strictSourceCone Φ) := by
  intro x hx
  have hpol : Φ x < S.polar x x := by
    have hd : Φ x ≤ S.polar x x - S.pair x x := hle x
    linarith
  have hprod : 0 < S.pair x S.H * S.pair x S.V := by
    have h0 : 0 ≤ Φ x := hnonneg x
    rw [S.polar_self] at hpol
    linarith
  rcases mul_pos_iff.mp hprod with ⟨hH, hV⟩ | ⟨hH, hV⟩
  · exact Or.inl ((S.mem_strictSourceCone_iff Φ x).mpr ⟨hH, hV, hpol⟩)
  · right
    rw [S.mem_strictSourceCone_iff]
    refine ⟨by simpa using neg_pos.mpr hH, by simpa using neg_pos.mpr hV, ?_⟩
    rw [heven x, S.polar_self]
    simp only [map_neg, LinearMap.neg_apply]
    rw [S.polar_self] at hpol
    linarith

/-- **Riemann–Roch for `sourceCone` from defect domination:**
If `Φ` is even, nonnegative, and bounded above by `S.defect x x`, then `S.sourceCone Φ` satisfies
`S.RiemannRochAxiom`. -/
theorem sourceCone_riemannRoch_of_le_defect {Φ : C → ℝ}
    (heven : ∀ x, Φ (-x) = Φ x) (hnonneg : ∀ x, 0 ≤ Φ x) (hle : ∀ x, Φ x ≤ S.defect x x) :
    S.RiemannRochAxiom (S.sourceCone Φ) := by
  intro x hx
  rcases S.strictSourceCone_riemannRoch_of_le_defect heven hnonneg hle x hx with h | h
  · exact Or.inl (S.strictSourceCone_subset_sourceCone Φ h)
  · exact Or.inr (S.strictSourceCone_subset_sourceCone Φ h)

/-- **Canonical Surface Riemann–Roch (`K = 0, χ₀ = 0`) for `sourceCone`:**
If `Φ` is even, nonnegative, and bounded above by `S.defect x x`, then `S.sourceCone Φ` satisfies
`S.SurfaceRiemannRochAxiom 0 0`. -/
theorem sourceCone_surfaceRiemannRoch_of_le_defect {Φ : C → ℝ}
    (heven : ∀ x, Φ (-x) = Φ x) (hnonneg : ∀ x, 0 ≤ Φ x) (hle : ∀ x, Φ x ≤ S.defect x x) :
    S.SurfaceRiemannRochAxiom 0 0 (S.sourceCone Φ) := by
  intro x hx
  have hxx : 0 < S.pair x x := by
    simp only [map_zero, sub_zero, zero_add] at hx
    linarith
  rcases S.sourceCone_riemannRoch_of_le_defect heven hnonneg hle x hxx with h | h
  · exact Or.inl h
  · right
    simpa [zero_sub] using h

/-- **Bézout Positivity for `sourceCone` and `strictSourceCone` from defect upper bound:**
If `S.HodgeIndex` holds and `S.defect x x ≤ Φ x` for all `x`, then both `S.sourceCone Φ` and
`S.strictSourceCone Φ` satisfy `S.BezoutAxiom`. -/
theorem sourceCone_bezout_of_defect_le {Φ : C → ℝ}
    (hH : S.HodgeIndex) (hge : ∀ x, S.defect x x ≤ Φ x) :
    S.BezoutAxiom (S.sourceCone Φ) := by
  intro x hx y hy
  exact S.positiveCone_bezout hH x (S.sourceCone_subset_positiveCone_of_defect_le hge hx)
    y (S.sourceCone_subset_positiveCone_of_defect_le hge hy)

theorem strictSourceCone_bezout_of_defect_le {Φ : C → ℝ}
    (hH : S.HodgeIndex) (hge : ∀ x, S.defect x x ≤ Φ x) :
    S.BezoutAxiom (S.strictSourceCone Φ) := by
  intro x hx y hy
  exact S.sourceCone_bezout_of_defect_le hH hge
    x (S.strictSourceCone_subset_sourceCone Φ hx)
    y (S.strictSourceCone_subset_sourceCone Φ hy)

end PolarSurface

/-! ### 2. The Convex, Hecke-Stable `L²` Source Cone on `scalingSubsurface V` -/

/-- **Purely Source-Defined `L²` Energy Functional on `scalingSubsurface V`:**
`l2SourceEnergy c V (a, b, f) = c ∫ f(u)² du`. This functional depends only on the source test
function `f` and never references `zetaZeroConfig.W` or `weilPair`. -/
def l2SourceEnergy (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : ℝ :=
  c * ∫ u : ℝ, ((x.2.2.1 : realTests).1 u) ^ 2

/-- **The Source Section Space of `scalingSubsurface V` at Coercivity Constant `c`:**
Sections `(α, β) ∈ [0, deg_H(x)] × [0, deg_V(x)]` with `c ∫ f² ≤ 2 α β`. -/
def l2SourceSections (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) : Set (ℝ × ℝ) :=
  (scalingSubsurface V).sourceSections (l2SourceEnergy c V) x

/-- **The Closed `L²` Source Cone on `scalingSubsurface V`:**
`l2SourceCone c V = {x | 0 ≤ x · H ∧ 0 ≤ x · V ∧ c ∫ f² ≤ 2 (x · H)(x · V)}`. -/
def l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).sourceCone (l2SourceEnergy c V)

/-- **The Strict `L²` Source Cone on `scalingSubsurface V`:**
`strictL2SourceCone c V = {x | 0 < x · H ∧ 0 < x · V ∧ c ∫ f² < 2 (x · H)(x · V)}`. -/
def strictL2SourceCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  (scalingSubsurface V).strictSourceCone (l2SourceEnergy c V)

theorem scalingSubsurface_pair_H (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x (scalingSubsurface V).H = x.2.1 + poleB x.2.2.1.1 :=
  scalingSurface_pair_H (x.1, x.2.1, x.2.2.1)

theorem scalingSubsurface_pair_V (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x (scalingSubsurface V).V = x.1 + poleA x.2.2.1.1 :=
  scalingSurface_pair_V (x.1, x.2.1, x.2.2.1)

/-- **Explicit Source Characterization of `l2SourceCone c V`:**
Membership in `l2SourceCone c V` is determined purely by the source data
`b + poleB f ≥ 0`, `a + poleA f ≥ 0`, and `c ∫ f² ≤ 2 (b + poleB f)(a + poleA f)`. -/
theorem mem_l2SourceCone_iff (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    x ∈ l2SourceCone c V ↔
      0 ≤ x.2.1 + poleB x.2.2.1.1 ∧
      0 ≤ x.1 + poleA x.2.2.1.1 ∧
      c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
        2 * (x.2.1 + poleB x.2.2.1.1) * (x.1 + poleA x.2.2.1.1) := by
  rw [l2SourceCone, (scalingSubsurface V).mem_sourceCone_iff, (scalingSubsurface V).polar_self,
    scalingSubsurface_pair_H, scalingSubsurface_pair_V, l2SourceEnergy]

/-- **Explicit Source Characterization of `strictL2SourceCone c V`:**
Membership in `strictL2SourceCone c V` is determined purely by `b + poleB f > 0`,
`a + poleA f > 0`, and `c ∫ f² < 2 (b + poleB f)(a + poleA f)`. -/
theorem mem_strictL2SourceCone_iff (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    x ∈ strictL2SourceCone c V ↔
      0 < x.2.1 + poleB x.2.2.1.1 ∧
      0 < x.1 + poleA x.2.2.1.1 ∧
      c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 <
        2 * (x.2.1 + poleB x.2.2.1.1) * (x.1 + poleA x.2.2.1.1) := by
  rw [strictL2SourceCone, (scalingSubsurface V).mem_strictSourceCone_iff,
    (scalingSubsurface V).polar_self, scalingSubsurface_pair_H, scalingSubsurface_pair_V,
    l2SourceEnergy]

theorem l2SourceEnergy_zero (c : ℝ) (V : Submodule ℝ realTests) :
    l2SourceEnergy c V 0 = 0 := by
  simp [l2SourceEnergy]

theorem l2SourceEnergy_H (c : ℝ) (V : Submodule ℝ realTests) :
    l2SourceEnergy c V (scalingSubsurface V).H = 0 := by
  simp [l2SourceEnergy, scalingSubsurface, scalingSurface]

theorem l2SourceEnergy_V (c : ℝ) (V : Submodule ℝ realTests) :
    l2SourceEnergy c V (scalingSubsurface V).V = 0 := by
  simp [l2SourceEnergy, scalingSubsurface, scalingSurface]

theorem l2SourceEnergy_ample (c : ℝ) (V : Submodule ℝ realTests) :
    l2SourceEnergy c V (scalingSubsurface V).ample = 0 := by
  simp [l2SourceEnergy, PolarSurface.ample, scalingSubsurface, scalingSurface]

theorem l2SourceEnergy_neg (c : ℝ) (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    l2SourceEnergy c V (-x) = l2SourceEnergy c V x := by
  simp [l2SourceEnergy]

theorem l2SourceEnergy_nonneg {c : ℝ} (hc : 0 ≤ c) (V : Submodule ℝ realTests)
    (x : ℝ × ℝ × V) : 0 ≤ l2SourceEnergy c V x :=
  mul_nonneg hc (integral_nonneg fun _ => sq_nonneg _)

/-- `0`, `H`, `V`, and `ample = H + V` belong to `l2SourceCone c V` for every `c ∈ ℝ`, and
`ample ∈ strictL2SourceCone c V`. -/
theorem zero_mem_l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    0 ∈ l2SourceCone c V :=
  (scalingSubsurface V).zero_mem_sourceCone (by rw [l2SourceEnergy_zero])

theorem H_mem_l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).H ∈ l2SourceCone c V :=
  (scalingSubsurface V).H_mem_sourceCone (by rw [l2SourceEnergy_H])

theorem V_mem_l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).V ∈ l2SourceCone c V :=
  (scalingSubsurface V).V_mem_sourceCone (by rw [l2SourceEnergy_V])

theorem ample_mem_l2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).ample ∈ l2SourceCone c V :=
  (scalingSubsurface V).ample_mem_sourceCone (by rw [l2SourceEnergy_ample]; norm_num)

theorem ample_mem_strictL2SourceCone (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).ample ∈ strictL2SourceCone c V :=
  (scalingSubsurface V).ample_mem_strictSourceCone (by rw [l2SourceEnergy_ample]; norm_num)

/-- Every real test `f ∈ realTests` has integrable square `u ↦ f(u)²`. -/
theorem integrable_sq_of_mem_realTests {f : ℝ → ℝ} (hf : f ∈ realTests) :
    Integrable (fun u : ℝ => f u ^ 2) := by
  have hcont : Continuous (fun u : ℝ => f u ^ 2) := hf.1.continuous.pow 2
  have hsupp : HasCompactSupport (fun u : ℝ => f u ^ 2) := by
    refine hf.2.mono ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, sq_eq_zero_iff] at hu ⊢
    exact hu
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- Every pair of real tests `f, g ∈ realTests` has integrable product `u ↦ f(u) g(u)`. -/
theorem integrable_mul_of_mem_realTests {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests) :
    Integrable (fun u : ℝ => f u * g u) := by
  have hcont : Continuous (fun u : ℝ => f u * g u) := hf.1.continuous.mul hg.1.continuous
  have hsupp : HasCompactSupport (fun u : ℝ => f u * g u) := by
    refine hf.2.mono ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu ⊢
    exact hu.1
  exact hcont.integrable_of_hasCompactSupport hsupp

/-- `L²` Cauchy–Schwarz inequality for `f, g ∈ realTests`:
`(∫ f(u) g(u) du)² ≤ (∫ f(u)² du) (∫ g(u)² du)`. -/
theorem integral_mul_sq_le_of_mem_realTests {f g : ℝ → ℝ}
    (hf : f ∈ realTests) (hg : g ∈ realTests) :
    (∫ u : ℝ, f u * g u) ^ 2 ≤ (∫ u : ℝ, f u ^ 2) * (∫ u : ℝ, g u ^ 2) := by
  have hquad : ∀ t : ℝ, 0 ≤
      (∫ u : ℝ, g u ^ 2) * (t * t) + (2 * ∫ u : ℝ, f u * g u) * t + (∫ u : ℝ, f u ^ 2) := by
    intro t
    have hnonneg : 0 ≤ ∫ u : ℝ, (f u + t * g u) ^ 2 :=
      integral_nonneg fun u => sq_nonneg (f u + t * g u)
    have hexp : ∀ u : ℝ, (f u + t * g u) ^ 2 =
        (f u ^ 2 + (2 * t) * (f u * g u)) + (t * t) * g u ^ 2 := fun u => by ring
    have hint1 : Integrable (fun u : ℝ => f u ^ 2) := integrable_sq_of_mem_realTests hf
    have hint2 : Integrable (fun u : ℝ => (2 * t) * (f u * g u)) :=
      (integrable_mul_of_mem_realTests hf hg).const_mul (2 * t)
    have hint3 : Integrable (fun u : ℝ => (t * t) * g u ^ 2) :=
      (integrable_sq_of_mem_realTests hg).const_mul (t * t)
    rw [integral_congr_ae (Eventually.of_forall hexp),
      integral_add (f := fun u => f u ^ 2 + (2 * t) * (f u * g u))
        (g := fun u => (t * t) * g u ^ 2) (hint1.add hint2) hint3,
      integral_add hint1 hint2, integral_const_mul, integral_const_mul] at hnonneg
    linarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith

/-- **Additive Convexity of `l2SourceCone c V` (`c ≥ 0`):**
The source-defined cone `l2SourceCone c V` is closed under cycle addition `x + y`. -/
theorem l2SourceCone_add {c : ℝ} (hc : 0 ≤ c) (V : Submodule ℝ realTests)
    {x y : ℝ × ℝ × V} (hx : x ∈ l2SourceCone c V) (hy : y ∈ l2SourceCone c V) :
    x + y ∈ l2SourceCone c V := by
  let S := scalingSubsurface V
  rw [l2SourceCone, S.mem_sourceCone_iff, S.polar_self] at hx hy ⊢
  rcases hx with ⟨hxH, hxV, hxE⟩
  rcases hy with ⟨hyH, hyV, hyE⟩
  rw [S.pair_add_left, S.pair_add_left]
  refine ⟨by linarith, by linarith, ?_⟩
  let f : ℝ → ℝ := x.2.2.1.1
  let g : ℝ → ℝ := y.2.2.1.1
  have hf : f ∈ realTests := x.2.2.1.2
  have hg : g ∈ realTests := y.2.2.1.2
  have hfg_int : ∫ u : ℝ, ((x + y).2.2.1.1 u) ^ 2 =
      (∫ u : ℝ, f u ^ 2) + 2 * (∫ u : ℝ, f u * g u) + (∫ u : ℝ, g u ^ 2) := by
    have hexp : ∀ u : ℝ, ((x + y).2.2.1.1 u) ^ 2 =
        (f u ^ 2 + 2 * (f u * g u)) + g u ^ 2 := fun u => by
      change (f u + g u) ^ 2 = (f u ^ 2 + 2 * (f u * g u)) + g u ^ 2
      ring
    have hint1 : Integrable (fun u : ℝ => f u ^ 2) := integrable_sq_of_mem_realTests hf
    have hint2 : Integrable (fun u : ℝ => 2 * (f u * g u)) :=
      (integrable_mul_of_mem_realTests hf hg).const_mul 2
    have hint3 : Integrable (fun u : ℝ => g u ^ 2) := integrable_sq_of_mem_realTests hg
    rw [integral_congr_ae (Eventually.of_forall hexp),
      integral_add (f := fun u => f u ^ 2 + 2 * (f u * g u))
        (g := fun u => g u ^ 2) (hint1.add hint2) hint3,
      integral_add hint1 hint2, integral_const_mul]
  change c * ∫ u : ℝ, ((x + y).2.2.1.1 u) ^ 2 ≤ _
  rw [hfg_int, mul_add, mul_add, ← mul_assoc, mul_comm c 2, mul_assoc]
  have hcs := integral_mul_sq_le_of_mem_realTests hf hg
  have hcs_c : (c * ∫ u : ℝ, f u * g u) ^ 2 ≤
      (c * ∫ u : ℝ, f u ^ 2) * (c * ∫ u : ℝ, g u ^ 2) := by
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have hmul := mul_le_mul_of_nonneg_left hcs hc2
    linarith [show c ^ 2 * ((∫ u : ℝ, f u ^ 2) * (∫ u : ℝ, g u ^ 2)) =
      (c * ∫ u : ℝ, f u ^ 2) * (c * ∫ u : ℝ, g u ^ 2) by ring,
      show c ^ 2 * (∫ u : ℝ, f u * g u) ^ 2 = (c * ∫ u : ℝ, f u * g u) ^ 2 by ring]
  have hEx0 : 0 ≤ c * ∫ u : ℝ, f u ^ 2 :=
    mul_nonneg hc (integral_nonneg fun _ => sq_nonneg _)
  have hEy0 : 0 ≤ c * ∫ u : ℝ, g u ^ 2 :=
    mul_nonneg hc (integral_nonneg fun _ => sq_nonneg _)
  have hxE' : c * ∫ u : ℝ, f u ^ 2 ≤ 2 * S.pair x S.H * S.pair x S.V := hxE
  have hyE' : c * ∫ u : ℝ, g u ^ 2 ≤ 2 * S.pair y S.H * S.pair y S.V := hyE
  have hprod : (c * ∫ u : ℝ, f u * g u) ^ 2 ≤
      (2 * S.pair x S.H * S.pair x S.V) * (2 * S.pair y S.H * S.pair y S.V) :=
    hcs_c.trans (mul_le_mul hxE' hyE' hEy0 (by positivity))
  have hhyp : (2 * S.pair x S.H * S.pair x S.V) * (2 * S.pair y S.H * S.pair y S.V) ≤
      (S.pair x S.H * S.pair y S.V + S.pair y S.H * S.pair x S.V) ^ 2 := by
    have hsq : 0 ≤ (S.pair x S.H * S.pair y S.V - S.pair y S.H * S.pair x S.V) ^ 2 := sq_nonneg _
    linarith
  have hsq_le : (c * ∫ u : ℝ, f u * g u) ^ 2 ≤
      (S.pair x S.H * S.pair y S.V + S.pair y S.H * S.pair x S.V) ^ 2 :=
    hprod.trans hhyp
  have hcross_nonneg : 0 ≤ S.pair x S.H * S.pair y S.V + S.pair y S.H * S.pair x S.V := by
    positivity
  have hcross : c * ∫ u : ℝ, f u * g u ≤
      S.pair x S.H * S.pair y S.V + S.pair y S.H * S.pair x S.V := by
    by_contra hlt
    push Not at hlt
    nlinarith [lt_of_le_of_lt hcross_nonneg hlt]
  linarith [hxE', hyE', hcross,
    show 2 * (S.pair x S.H + S.pair y S.H) * (S.pair x S.V + S.pair y S.V) =
      2 * S.pair x S.H * S.pair x S.V +
      2 * (S.pair x S.H * S.pair y S.V + S.pair y S.H * S.pair x S.V) +
      2 * S.pair y S.H * S.pair y S.V by ring]

/-- **Scalar Homogeneity of `l2SourceCone c V` (`t ≥ 0`):**
`l2SourceCone c V` is closed under nonnegative scalar multiplication. -/
theorem l2SourceCone_smul {c t : ℝ} (ht : 0 ≤ t) (V : Submodule ℝ realTests)
    {x : ℝ × ℝ × V} (hx : x ∈ l2SourceCone c V) :
    t • x ∈ l2SourceCone c V := by
  let S := scalingSubsurface V
  rw [l2SourceCone, S.mem_sourceCone_iff, S.polar_self] at hx ⊢
  rcases hx with ⟨hxH, hxV, hxE⟩
  rw [S.pair_smul_left, S.pair_smul_left]
  refine ⟨mul_nonneg ht hxH, mul_nonneg ht hxV, ?_⟩
  have hint : l2SourceEnergy c V (t • x) = t ^ 2 * l2SourceEnergy c V x := by
    simp only [l2SourceEnergy]
    have hexp : (fun u : ℝ => (((t • x).2.2.1 : realTests).1 u) ^ 2) =
        fun u => t ^ 2 * ((x.2.2.1 : realTests).1 u) ^ 2 := by
      ext u
      change (t * (x.2.2.1 : realTests).1 u) ^ 2 = t ^ 2 * ((x.2.2.1 : realTests).1 u) ^ 2
      ring
    rw [hexp, integral_const_mul]
    ring
  rw [hint]
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hmul := mul_le_mul_of_nonneg_left hxE ht2
  linarith [show t ^ 2 * (2 * S.pair x S.H * S.pair x S.V) =
    2 * (t * S.pair x S.H) * (t * S.pair x S.V) by ring]

/-- `strictL2SourceCone c V` is closed under strictly positive scalar multiplication `t > 0`. -/
theorem strictL2SourceCone_smul {c t : ℝ} (ht : 0 < t) (V : Submodule ℝ realTests)
    {x : ℝ × ℝ × V} (hx : x ∈ strictL2SourceCone c V) :
    t • x ∈ strictL2SourceCone c V := by
  let S := scalingSubsurface V
  rw [strictL2SourceCone, S.mem_strictSourceCone_iff, S.polar_self] at hx ⊢
  rcases hx with ⟨hxH, hxV, hxE⟩
  rw [S.pair_smul_left, S.pair_smul_left]
  refine ⟨mul_pos ht hxH, mul_pos ht hxV, ?_⟩
  have hint : l2SourceEnergy c V (t • x) = t ^ 2 * l2SourceEnergy c V x := by
    simp only [l2SourceEnergy]
    have hexp : (fun u : ℝ => (((t • x).2.2.1 : realTests).1 u) ^ 2) =
        fun u => t ^ 2 * ((x.2.2.1 : realTests).1 u) ^ 2 := by
      ext u
      change (t * (x.2.2.1 : realTests).1 u) ^ 2 = t ^ 2 * ((x.2.2.1 : realTests).1 u) ^ 2
      ring
    rw [hexp, integral_const_mul]
    ring
  rw [hint]
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hmul := mul_lt_mul_of_pos_left hxE ht2
  linarith [show t ^ 2 * (2 * S.pair x S.H * S.pair x S.V) =
    2 * (t * S.pair x S.H) * (t * S.pair x S.V) by ring]

/-- Logarithmic scale translation `scaleShift t` preserves the `L²` norm squared `∫ f(u)² du`. -/
theorem integral_scaleShift_sq (t : ℝ) (f : ℝ → ℝ) :
    (∫ u : ℝ, (scaleShift t f u) ^ 2) = ∫ u : ℝ, f u ^ 2 :=
  MeasureTheory.integral_sub_right_eq_self (fun u : ℝ => f u ^ 2) t

/-- **Unconditional Adams Invariance of `l2SourceCone c ⊤`:**
Every Adams operation `adamsOp q` (`q > 0`) preserves `l2SourceCone c ⊤` and `strictL2SourceCone c ⊤`
(without assuming `HodgeIndex`). -/
theorem adamsOp_mem_l2SourceCone {c q : ℝ} (hq : 0 < q) {x : ℝ × ℝ × (⊤ : Submodule ℝ realTests)}
    (hx : x ∈ l2SourceCone c ⊤) :
    (let y := adamsOp q (x.1, x.2.1, x.2.2.1); (y.1, y.2.1, ⟨y.2.2, trivial⟩)) ∈
      l2SourceCone c ⊤ := by
  let x₀ : ScalingCycle := (x.1, x.2.1, x.2.2.1)
  rw [l2SourceCone, (scalingSubsurface ⊤).mem_sourceCone_iff] at hx ⊢
  rcases hx with ⟨hxH, hxV, hxE⟩
  have hH : (scalingSubsurface ⊤).pair
      (let y := adamsOp q x₀; (y.1, y.2.1, ⟨y.2.2, trivial⟩)) (scalingSubsurface ⊤).H =
      (Real.sqrt q)⁻¹ * (scalingSubsurface ⊤).pair x (scalingSubsurface ⊤).H :=
    pair_adamsOp_H hq x₀
  have hV : (scalingSubsurface ⊤).pair
      (let y := adamsOp q x₀; (y.1, y.2.1, ⟨y.2.2, trivial⟩)) (scalingSubsurface ⊤).V =
      Real.sqrt q * (scalingSubsurface ⊤).pair x (scalingSubsurface ⊤).V :=
    pair_adamsOp_V hq x₀
  have hpol : (scalingSubsurface ⊤).polar
      (let y := adamsOp q x₀; (y.1, y.2.1, ⟨y.2.2, trivial⟩))
      (let y := adamsOp q x₀; (y.1, y.2.1, ⟨y.2.2, trivial⟩)) =
      (scalingSubsurface ⊤).polar x x :=
    polar_adamsOp q x₀ x₀
  have hE : l2SourceEnergy c ⊤ (let y := adamsOp q x₀; (y.1, y.2.1, ⟨y.2.2, trivial⟩)) =
      l2SourceEnergy c ⊤ x := by
    simp only [l2SourceEnergy, adamsOp, scalingAction, LinearMap.coe_mk, AddHom.coe_mk,
      integral_scaleShift_sq]
    rfl
  rw [hH, hV, hpol, hE]
  exact ⟨mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg q)) hxH,
    mul_nonneg (Real.sqrt_nonneg q) hxV, hxE⟩

/-- **Unconditional Hecke Stability of `l2SourceCone c ⊤`:**
Every Hecke correspondence `heckeCorrespondence q` (`q > 0`) preserves `l2SourceCone c ⊤`. -/
theorem heckeCorrespondence_mem_l2SourceCone {c q : ℝ} (hq : 0 < q)
    {x : ℝ × ℝ × (⊤ : Submodule ℝ realTests)} (hx : x ∈ l2SourceCone c ⊤) :
    (let y := heckeCorrespondence q (x.1, x.2.1, x.2.2.1); (y.1, y.2.1, ⟨y.2.2, trivial⟩)) ∈
      l2SourceCone c ⊤ := by
  have hadams := adamsOp_mem_l2SourceCone hq hx
  have hsmul := l2SourceCone_smul (Real.sqrt_nonneg q) ⊤ hadams
  exact hsmul

/-- If a real test `f ∈ realTests` has `∫ u, f(u)² = 0`, then `f = 0` everywhere. -/
theorem eq_zero_of_integral_sq_eq_zero_of_mem_realTests {f : ℝ → ℝ} (hf : f ∈ realTests)
    (hint : (∫ u : ℝ, f u ^ 2) = 0) : f = 0 := by
  ext u₀
  by_contra hne
  have hsq_ne : f u₀ ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hcont : Continuous (fun u : ℝ => f u ^ 2) := hf.1.continuous.pow 2
  have hsupp : HasCompactSupport (fun u : ℝ => f u ^ 2) := by
    refine hf.2.mono ?_
    intro u hu
    simp only [Function.mem_support, ne_eq, sq_eq_zero_iff] at hu ⊢
    exact hu
  have hpos : 0 < ∫ u : ℝ, f u ^ 2 :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp (fun u => sq_nonneg (f u)) hsq_ne
  linarith

/-- **Unconditional, Non-Vacuous Ampleness of `l2SourceCone c V` (`c > 0`):**
For every `c > 0` and every test submodule `V ≤ realTests`, `l2SourceCone c V` satisfies
`(scalingSubsurface V).AmpleAxiom` **unconditionally and non-vacuously** (without assuming the sign
of `weilPair`), and in fact any cycle `x ∈ l2SourceCone c V` orthogonal to `H + V` is the zero
cycle `x = 0`. -/
theorem eq_zero_of_mem_l2SourceCone_of_pair_ample_eq_zero {c : ℝ} (hc : 0 < c)
    (V : Submodule ℝ realTests) {x : ℝ × ℝ × V} (hx : x ∈ l2SourceCone c V)
    (hxA : (scalingSubsurface V).pair x (scalingSubsurface V).ample = 0) :
    x = 0 := by
  let S := scalingSubsurface V
  rw [l2SourceCone, S.mem_sourceCone_iff, S.polar_self] at hx
  rcases hx with ⟨hH, hV, hE⟩
  have hsum : S.pair x S.H + S.pair x S.V = 0 := by
    rwa [← S.pair_ample]
  have hH0 : S.pair x S.H = 0 := by linarith
  have hV0 : S.pair x S.V = 0 := by linarith
  have hEle : l2SourceEnergy c V x ≤ 0 := by
    linarith [show 2 * S.pair x S.H * S.pair x S.V = 0 by rw [hH0]; ring]
  have hint_nonneg : 0 ≤ ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hint0 : (∫ u : ℝ, (x.2.2.1.1 u) ^ 2) = 0 := by
    change c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ 0 at hEle
    nlinarith
  have hf0 : x.2.2.1.1 = 0 :=
    eq_zero_of_integral_sq_eq_zero_of_mem_realTests x.2.2.1.2 hint0
  have hB0 : poleB x.2.2.1.1 = 0 := by rw [hf0, poleB_zero]
  have hA0 : poleA x.2.2.1.1 = 0 := by rw [hf0, poleA_zero]
  rw [scalingSubsurface_pair_H, hB0, add_zero] at hH0
  rw [scalingSubsurface_pair_V, hA0, add_zero] at hV0
  refine Prod.ext hV0 (Prod.ext hH0 ?_)
  apply Subtype.ext
  apply Subtype.ext
  exact hf0

theorem l2SourceCone_ample {c : ℝ} (hc : 0 < c) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).AmpleAxiom (l2SourceCone c V) := by
  intro x hx hxA y
  rw [eq_zero_of_mem_l2SourceCone_of_pair_ample_eq_zero hc V hx hxA]
  simp

theorem strictL2SourceCone_ample (c : ℝ) (V : Submodule ℝ realTests) :
    (scalingSubsurface V).AmpleAxiom (strictL2SourceCone c V) :=
  (scalingSubsurface V).strictSourceCone_ample (l2SourceEnergy c V)

/-- **Exact Quantitative Equivalence of `RiemannRochAxiom` for `l2SourceCone c V` (`c > 0`):**
`(scalingSubsurface V).RiemannRochAxiom (l2SourceCone c V)` holds if and only if
`∀ f ∈ V, c ∫ f(u)² du ≤ weilPair f f`. -/
theorem l2SourceCone_riemannRoch_iff_weilPair_ge {c : ℝ} (hc : 0 < c)
    (V : Submodule ℝ realTests) :
    (scalingSubsurface V).RiemannRochAxiom (l2SourceCone c V) ↔
      ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  let S := scalingSubsurface V
  constructor
  · intro hRR f
    by_contra hlt
    push Not at hlt
    let E : ℝ := c * ∫ u : ℝ, (f.1.1 u) ^ 2
    let W : ℝ := weilPair f.1.1 f.1.1
    set M : ℝ := (E + W) / 2
    have hW_lt_M : W < M := by dsimp [M]; linarith
    have hM_lt_E : M < E := by dsimp [M]; linarith
    set a₀ : ℝ := 1 / 2 - poleA f.1.1
    set b₀ : ℝ := M - poleB f.1.1
    let x : ℝ × ℝ × V := (a₀, b₀, f)
    have hxH : S.pair x S.H = M := by
      rw [scalingSubsurface_pair_H]
      simp [x, b₀]
    have hxV : S.pair x S.V = 1 / 2 := by
      rw [scalingSubsurface_pair_V]
      simp [x, a₀]
    have hpol : S.polar x x = M := by
      rw [S.polar_self, hxH, hxV]
      ring
    have hdef : S.defect x x = W := scalingSubsurface_defect_self V x
    have hpair : S.pair x x = M - W := by
      have hd : S.defect x x = S.polar x x - S.pair x x := rfl
      linarith
    have hpos : 0 < S.pair x x := by linarith
    rcases hRR x hpos with hxE | hnxE
    · rw [l2SourceCone, S.mem_sourceCone_iff, hpol] at hxE
      have hleE : E ≤ M := hxE.2.2
      linarith
    · rw [l2SourceCone, S.mem_sourceCone_iff, S.pair_neg_left x S.V, hxV] at hnxE
      linarith [hnxE.2.1]
  · intro hle
    exact S.sourceCone_riemannRoch_of_le_defect
      (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc.le V)
      (fun x => by
        rw [scalingSubsurface_defect_self]
        exact hle x.2.2)

/-- **Exact Quantitative Equivalence of `RiemannRochAxiom` for `strictL2SourceCone c V` (`c > 0`):**
`(scalingSubsurface V).RiemannRochAxiom (strictL2SourceCone c V)` holds if and only if
`∀ f ∈ V, c ∫ f(u)² du ≤ weilPair f f`. -/
theorem strictL2SourceCone_riemannRoch_iff_weilPair_ge {c : ℝ} (hc : 0 < c)
    (V : Submodule ℝ realTests) :
    (scalingSubsurface V).RiemannRochAxiom (strictL2SourceCone c V) ↔
      ∀ f : V, c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  let S := scalingSubsurface V
  constructor
  · intro hRR
    rw [← l2SourceCone_riemannRoch_iff_weilPair_ge hc V]
    intro x hx
    rcases hRR x hx with h | h
    · exact Or.inl (S.strictSourceCone_subset_sourceCone (l2SourceEnergy c V) h)
    · exact Or.inr (S.strictSourceCone_subset_sourceCone (l2SourceEnergy c V) h)
  · intro hle
    exact S.strictSourceCone_riemannRoch_of_le_defect
      (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc.le V)
      (fun x => by
        rw [scalingSubsurface_defect_self]
        exact hle x.2.2)

/-! ### 3. The All-Aperture Explicit-Formula Source Incidence Cone on `oddRealTestsAt r` -/

/-- **Purely Source-Defined Incidence Energy Functional on `oddRealTestsAt r` (`0 < r < R`):**
Built exclusively from the source integrals `surplusPool`, `crossingPotentialTerm`,
`gaugeRemainder`, and `reflectedPrimePolarCost` (with no reference to `zetaZeroConfig.W` or
`weilPair`). -/
def sourceIncidenceFunctional (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℝ :=
  let f : ℝ → ℝ := x.2.2.1
  surplusPool (aperturePlateau r R) f +
    crossingPotentialTerm (aperturePlateau r R) f +
    gaugeRemainder (aperturePlateau r R) f -
    reflectedPrimePolarCost f r

/-- **The Source Incidence Section Space on `oddRealTestsAt r`:** -/
def sourceIncidenceSections (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : Set (ℝ × ℝ) :=
  (scalingSubsurface (oddRealTestsAt r)).strictSourceSections (sourceIncidenceFunctional r R) x

/-- **The All-Aperture Source Incidence Cone on `oddRealTestsAt r`:**
`sourceIncidenceCone r R = {x | (sourceIncidenceSections r R x).Nonempty}`. -/
def sourceIncidenceCone (r R : ℝ) : Set (ℝ × ℝ × oddRealTestsAt r) :=
  (scalingSubsurface (oddRealTestsAt r)).strictSourceCone (sourceIncidenceFunctional r R)

/-- On `scalingSubsurface (oddRealTestsAt r)`, `sourceIncidenceFunctional r R x` equals the
Castelnuovo–Severi defect `(scalingSubsurface (oddRealTestsAt r)).defect x x` for all `0 < r < R`. -/
theorem sourceIncidenceFunctional_eq_defect {r R : ℝ} (hr : 0 < r) (hR : r < R)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    sourceIncidenceFunctional r R x = (scalingSubsurface (oddRealTestsAt r)).defect x x :=
  (scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hR x).symm

/-- **Zero-Free Source Characterization of `sourceIncidenceCone r R`:**
For every aperture `0 < r < R`, a cycle `x` belongs to `sourceIncidenceCone r R` if and only if
`0 < x · H ∧ 0 < x · V ∧ 0 < x · x`. In particular, every cycle in `sourceIncidenceCone r R`
belongs to `strictCoupledArithmeticCone (oddRealTestsAt r)`, and `RiemannRochAxiom` for
`sourceIncidenceCone r R` is unconditionally equivalent to `RiemannRochAxiom` for
`strictCoupledArithmeticCone (oddRealTestsAt r)` across all apertures `0 < r < R`. -/
theorem mem_sourceIncidenceCone_iff_pair_pos {r R : ℝ} (hr : 0 < r) (hR : r < R)
    (x : ℝ × ℝ × oddRealTestsAt r) :
    x ∈ sourceIncidenceCone r R ↔
      0 < (scalingSubsurface (oddRealTestsAt r)).pair x (scalingSubsurface (oddRealTestsAt r)).H ∧
      0 < (scalingSubsurface (oddRealTestsAt r)).pair x (scalingSubsurface (oddRealTestsAt r)).V ∧
      0 < (scalingSubsurface (oddRealTestsAt r)).pair x x := by
  let S := scalingSubsurface (oddRealTestsAt r)
  rw [sourceIncidenceCone, S.mem_strictSourceCone_iff, sourceIncidenceFunctional_eq_defect hr hR]
  have hd : S.defect x x = S.polar x x - S.pair x x := rfl
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => by linarith, fun h => by linarith⟩

theorem sourceIncidenceCone_subset_strictCoupledArithmeticCone {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    sourceIncidenceCone r R ⊆ strictCoupledArithmeticCone (oddRealTestsAt r) := by
  intro x hx
  have hdeg : 0 < (scalingSubsurface (oddRealTestsAt r)).pair x
      (scalingSubsurface (oddRealTestsAt r)).ample :=
    (scalingSubsurface (oddRealTestsAt r)).pair_ample_pos_of_mem_strictSourceCone hx
  rw [mem_sourceIncidenceCone_iff_pair_pos hr hR] at hx
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact ⟨hx.2.2, hdeg⟩

theorem sourceIncidenceCone_ample (r R : ℝ) :
    (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (sourceIncidenceCone r R) :=
  (scalingSubsurface (oddRealTestsAt r)).strictSourceCone_ample (sourceIncidenceFunctional r R)

/-- **All-Aperture Equivalence of `RiemannRochAxiom` for `sourceIncidenceCone r R` and
`strictCoupledArithmeticCone (oddRealTestsAt r)`:** -/
theorem sourceIncidenceCone_riemannRoch_iff_strictCoupled {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (sourceIncidenceCone r R) ↔
      (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (strictCoupledArithmeticCone (oddRealTestsAt r)) := by
  let S := scalingSubsurface (oddRealTestsAt r)
  constructor
  · intro hRR x hx
    rcases hRR x hx with h | h
    · exact Or.inl (sourceIncidenceCone_subset_strictCoupledArithmeticCone hr hR h)
    · exact Or.inr (sourceIncidenceCone_subset_strictCoupledArithmeticCone hr hR h)
  · intro hRR
    have hH : S.HodgeIndex := (strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex _).mp hRR
    have hdef : ∀ y, 0 ≤ S.defect y y := S.hodgeIndex_iff_defect_nonneg.mp hH
    refine S.strictSourceCone_riemannRoch_of_le_defect ?_ ?_ ?_
    · intro x
      rw [sourceIncidenceFunctional_eq_defect hr hR, sourceIncidenceFunctional_eq_defect hr hR,
        S.defect_neg_self]
    · intro x
      rw [sourceIncidenceFunctional_eq_defect hr hR]
      exact hdef x
    · intro x
      rw [sourceIncidenceFunctional_eq_defect hr hR]

/-- **Unconditional Source Incidence Riemann–Roch, Ampleness, and Bézout Past the First Prime
(`0 < r ≤ 181/500 < R`):**
Because `sourceIncidenceFunctional r R` equals the exact Castelnuovo–Severi defect by the
explicit-formula ledger, `sourceIncidenceCone r R` satisfies `RiemannRochAxiom`, `AmpleAxiom`, and
`BezoutAxiom` simultaneously for all `0 < r ≤ 181/500` and `r < R`. -/
theorem sourceIncidenceCone_riemannRoch_of_le_threeHundredSixtyTwoThousandths {r R : ℝ}
    (hr0 : 0 < r) (hr : r ≤ 181 / 500) (hR : r < R) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom (sourceIncidenceCone r R) ∧
      (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom (sourceIncidenceCone r R) ∧
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (sourceIncidenceCone r R) := by
  let S := scalingSubsurface (oddRealTestsAt r)
  have hH : S.HodgeIndex := scalingSubsurface_odd_hodgeIndex hr
  have hRR : S.RiemannRochAxiom (strictCoupledArithmeticCone (oddRealTestsAt r)) :=
    (strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex _).mpr hH
  refine ⟨(sourceIncidenceCone_riemannRoch_iff_strictCoupled hr0 hR).mpr hRR,
    sourceIncidenceCone_ample r R,
    S.strictSourceCone_bezout_of_defect_le hH fun x => ?_⟩
  rw [sourceIncidenceFunctional_eq_defect hr0 hR]

/-! ### 4. Unconditional Arithmetic Riemann–Roch Past the First Prime on the Full Ample-Orthogonal
Primitive Hyperplane `primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`) -/

/-- **Exact Ample-Orthogonality Law on `scalingSurface`:**
For any pure test cycle `(0, 0, f)` on `scalingSurface`, its intersection with the ample class
`H + V` is `poleB f + poleA f = 2 * evenPoleMoment f`. -/
theorem pureTestCycle_pair_ample_eq (f : realTests) :
    scalingSurface.pair (0, 0, f) scalingSurface.ample = 2 * evenPoleMoment f.1 := by
  have hH : scalingSurface.pair (0, 0, f) scalingSurface.H = poleB f.1 := by
    simpa using scalingSurface_pair_H (0, 0, f)
  have hV : scalingSurface.pair (0, 0, f) scalingSurface.V = poleA f.1 := by
    simpa using scalingSurface_pair_V (0, 0, f)
  rw [PolarSurface.ample, map_add, hH, hV,
    poleB_eq_evenPoleMoment_sub_oddPoleMoment f.2.1.continuous f.2.2,
    poleA_eq_evenPoleMoment_add_oddPoleMoment f.2.1.continuous f.2.2]
  ring

/-- **Exact Ample-Orthogonal Test Hyperplane Characterization:**
A pure test cycle `(0, 0, f)` is orthogonal to `ample = H + V` on `scalingSurface` if and only if
`evenPoleMoment f = ∫ f(u) cosh(u/2) du = 0` (with completely unrestricted `oddPoleMoment f`). -/
theorem pureTestCycle_pair_ample_eq_zero_iff (f : realTests) :
    scalingSurface.pair (0, 0, f) scalingSurface.ample = 0 ↔ evenPoleMoment f.1 = 0 := by
  rw [pureTestCycle_pair_ample_eq]
  constructor <;> intro h <;> linarith

/-- **The Polar-Free Smooth Test Subspace `polarFreeSmoothRealTestsAt r`:**
Smooth (`C^∞`) compactly supported real tests supported in `[-r, r]` with `evenPoleMoment f = 0` and
`oddPoleMoment f = 0` (the pure-test intersection with `{H, V}⊥`). -/
def polarFreeSmoothRealTestsAt (r : ℝ) : Submodule ℝ realTests where
  carrier := {f : realTests | ContDiff ℝ (⊤ : ℕ∞) f.1 ∧ tsupport f.1 ⊆ Icc (-r) r ∧
    evenPoleMoment f.1 = 0 ∧ oddPoleMoment f.1 = 0}
  add_mem' {f g} hf hg := by
    refine ⟨hf.1.add hg.1, (tsupport_add f.1 g.1).trans (union_subset hf.2.1 hg.2.1), ?_, ?_⟩
    · change evenPoleMoment (fun x => f.1 x + g.1 x) = 0
      rw [evenPoleMoment_add f.2.1.continuous f.2.2 g.2.1.continuous g.2.2, hf.2.2.1, hg.2.2.1,
        add_zero]
    · change oddPoleMoment (fun x => f.1 x + g.1 x) = 0
      rw [oddPoleMoment_add f.2.1.continuous f.2.2 g.2.1.continuous g.2.2, hf.2.2.2, hg.2.2.2,
        add_zero]
  zero_mem' := by
    refine ⟨contDiff_const, by simp [tsupport], ?_, ?_⟩
    · simp [evenPoleMoment]
    · simp [oddPoleMoment]
  smul_mem' c {f} hf := by
    refine ⟨hf.1.const_smul c, (tsupport_smul_subset_right (fun _ : ℝ => c) f.1).trans hf.2.1, ?_, ?_⟩
    · change evenPoleMoment (c • f.1) = 0
      have h : evenPoleMoment (c • f.1) = c * evenPoleMoment f.1 := by
        simp only [evenPoleMoment, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      rw [h, hf.2.2.1, mul_zero]
    · change oddPoleMoment (c • f.1) = 0
      have h : oddPoleMoment (c • f.1) = c * oddPoleMoment f.1 := by
        simp only [oddPoleMoment, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      rw [h, hf.2.2.2, mul_zero]

/-- **The Full Ample-Orthogonal Primitive Hyperplane `primitiveSmoothRealTestsAt r`:**
Smooth (`C^∞`) compactly supported real tests supported in `[-r, r]` with `evenPoleMoment f = 0` and
**arbitrary** `oddPoleMoment f` (containing both `polarFreeSmoothRealTestsAt r` and all smooth tests
in `oddRealTestsAt r`). -/
def primitiveSmoothRealTestsAt (r : ℝ) : Submodule ℝ realTests where
  carrier := {f : realTests | ContDiff ℝ (⊤ : ℕ∞) f.1 ∧ tsupport f.1 ⊆ Icc (-r) r ∧
    evenPoleMoment f.1 = 0}
  add_mem' {f g} hf hg := by
    refine ⟨hf.1.add hg.1, (tsupport_add f.1 g.1).trans (union_subset hf.2.1 hg.2.1), ?_⟩
    change evenPoleMoment (fun x => f.1 x + g.1 x) = 0
    rw [evenPoleMoment_add f.2.1.continuous f.2.2 g.2.1.continuous g.2.2, hf.2.2, hg.2.2, add_zero]
  zero_mem' := ⟨contDiff_const, by simp [tsupport], by simp [evenPoleMoment]⟩
  smul_mem' c {f} hf := by
    refine ⟨hf.1.const_smul c, (tsupport_smul_subset_right (fun _ : ℝ => c) f.1).trans hf.2.1, ?_⟩
    change evenPoleMoment (c • f.1) = 0
    have h : evenPoleMoment (c • f.1) = c * evenPoleMoment f.1 := by
      simp only [evenPoleMoment, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [h, hf.2.2, mul_zero]

/-- Every smooth odd test in `oddRealTestsAt r` belongs to `primitiveSmoothRealTestsAt r`. -/
theorem mem_primitiveSmoothRealTestsAt_of_mem_oddRealTestsAt {r : ℝ} {f : realTests}
    (hF_top : ContDiff ℝ (⊤ : ℕ∞) f.1) (hf : f ∈ oddRealTestsAt r) :
    f ∈ primitiveSmoothRealTestsAt r :=
  ⟨hF_top, hf.1, evenPoleMoment_eq_zero_of_odd hf.2⟩

/-- Every polar-free test in `polarFreeSmoothRealTestsAt r` belongs to
`primitiveSmoothRealTestsAt r`. -/
theorem polarFreeSmoothRealTestsAt_le_primitiveSmoothRealTestsAt (r : ℝ) :
    polarFreeSmoothRealTestsAt r ≤ primitiveSmoothRealTestsAt r := by
  intro f hf
  exact ⟨hf.1, hf.2.1, hf.2.2.1⟩

/-- If `f` vanishes outside `[-r, r]`, then `tsupport f ⊆ [-r, r]`. -/
theorem tsupport_subset_Icc_of_vanish_outside {f : ℝ → ℝ} {r : ℝ}
    (hsupp : ∀ u : ℝ, r < |u| → f u = 0) :
    tsupport f ⊆ Set.Icc (-r) r := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hnot
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
  apply hu
  apply hsupp
  rcases hnot with hlt | hgt
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
  · exact lt_of_lt_of_le hgt (le_abs_self u)

/-- **Unconditional `1/20` Coercivity Past the First Prime on `polarFreeSmoothRealTestsAt r`
(`r ≤ ½(log 2 + 1/50)`):**
For every smooth polar-free test `f ∈ polarFreeSmoothRealTestsAt r` with
`r ≤ (Real.log 2 + 1 / 50) / 2`,
`(1 / 20) ∫ f(u)² du ≤ weilPair f f`. -/
theorem weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) (f : polarFreeSmoothRealTestsAt r) :
    (1 / 20 : ℝ) * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  rw [weilPair_self_eq_fullZeroForm f.1.2.1 f.1.2.2]
  have htsupp : tsupport f.1.1 ⊆ Icc (-primeTwoAperture.1) primeTwoAperture.1 := by
    refine f.2.2.1.trans (Icc_subset_Icc ?_ ?_)
    · change -((Real.log 2 + 1 / 50) / 2) ≤ -r
      linarith
    · exact hr
  have hground := polarGroundEnergy_mul_le_fullZeroForm_Icc primeTwoAperture
    f.2.1 htsupp f.2.2.2.1 f.2.2.2.2
  have h120 := one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo
  exact (mul_le_mul_of_nonneg_right h120 (integral_nonneg fun _ => sq_nonneg _)).trans hground

/-- **Unconditional `1/1000` Mixed-Parity Coercivity Past the First Prime on
`primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`):**
For every smooth test `f ∈ primitiveSmoothRealTestsAt r` orthogonal to `H + V`
(`evenPoleMoment f = 0`, with completely unrestricted `oddPoleMoment f`) and every aperture
`r ≤ ½(log 2 + 1/50) ≈ 0.35657` strictly past `(log 2)/2 ≈ 0.34657`,
`(1 / 1000) ∫ f(u)² du ≤ weilPair f f`. -/
theorem weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) (f : primitiveSmoothRealTestsAt r) :
    (1 / 1000 : ℝ) * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  let F : ℝ → ℝ := f.1.1
  have hF2 : ContDiff ℝ 2 F := f.1.2.1
  have hF_top : ContDiff ℝ (⊤ : ℕ∞) F := f.2.1
  have hFc : HasCompactSupport F := f.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (f.2.2.1 hmem))
  have heven_mom : evenPoleMoment F = 0 := f.2.2.2
  rw [weilPair_self_eq_fullZeroForm hF2 hFc,
    fullZeroForm_eq_even_add_odd hF2 hFc,
    integral_sq_eq_even_add_odd hF2.continuous hFc, mul_add]
  have hFe2 : ContDiff ℝ 2 (evenPartReal F) := contDiff_evenPartReal hF2
  have hFe_top : ContDiff ℝ (⊤ : ℕ∞) (evenPartReal F) :=
    (hF_top.add (hF_top.comp contDiff_neg)).div_const 2
  have hFe_c : HasCompactSupport (evenPartReal F) := hasCompactSupport_evenPartReal hFc
  have hFo2 : ContDiff ℝ 2 (oddPartReal F) := contDiff_oddPartReal hF2
  have hFo_c : HasCompactSupport (oddPartReal F) := hasCompactSupport_oddPartReal hFc
  have hFe_tsupp : tsupport (evenPartReal F) ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    have hu1 : F u = 0 := hsupp u hu
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
    simp [evenPartReal, hu1, hu2]
  have hFe_even_mom : evenPoleMoment (evenPartReal F) = 0 := by
    have hsum : F = fun x => evenPartReal F x + oddPartReal F x :=
      funext fun x => (evenPartReal_add_oddPartReal F x).symm
    have hC : evenPoleMoment F = evenPoleMoment (evenPartReal F) := by
      conv_lhs => rw [hsum]
      rw [evenPoleMoment_add hFe2.continuous hFe_c hFo2.continuous hFo_c,
        evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F), add_zero]
    linarith
  have hFe_odd_mom : oddPoleMoment (evenPartReal F) = 0 :=
    oddPoleMoment_eq_zero_of_even (evenPartReal_neg F)
  have hFe_mem : (⟨evenPartReal F, hFe2, hFe_c⟩ : realTests) ∈ polarFreeSmoothRealTestsAt r :=
    ⟨hFe_top, hFe_tsupp, hFe_even_mom, hFe_odd_mom⟩
  have hFe_bound : (1 / 20 : ℝ) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      fullZeroForm (evenPartReal F) := by
    rw [← weilPair_self_eq_fullZeroForm hFe2 hFe_c]
    exact weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr
      ⟨⟨evenPartReal F, hFe2, hFe_c⟩, hFe_mem⟩
  have hFe_1000 : (1 / 1000 : ℝ) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      fullZeroForm (evenPartReal F) := by
    have hnonneg : 0 ≤ ∫ u : ℝ, (evenPartReal F u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith
  have hr_362 : r ≤ 181 / 500 := by
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  have hFo_supp : ∀ u : ℝ, 181 / 500 < |u| → oddPartReal F u = 0 := by
    intro u hu
    have hu' : r < |u| := lt_of_le_of_lt hr_362 hu
    have hu1 : F u = 0 := hsupp u hu'
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu')
    simp [oddPartReal, hu1, hu2]
  have hFo_1000 : (1 / 1000 : ℝ) * ∫ u : ℝ, (oddPartReal F u) ^ 2 ≤
      fullZeroForm (oddPartReal F) :=
    fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
      hFo2 hFo_c (oddPartReal_neg F) hFo_supp
  linarith

/-- **The First Prime `2` Actively Enters the Window `r = ½(log 2 + 1/50)`:**
`(log 2)/2 < (log 2 + 1/50)/2`, so `2 ∈ relevantShifts ((log 2 + 1/50)/2)`. -/
theorem half_log_two_lt_primeTwo_window :
    Real.log 2 / 2 < (Real.log 2 + 1 / 50) / 2 := by
  linarith

/-- **Unconditional Hodge Index Past the First Prime on `primitiveSmoothRealTestsAt r`
(`r ≤ ½(log 2 + 1/50)`):** -/
theorem primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).HodgeIndex := by
  rw [(scalingSubsurface (primitiveSmoothRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
  intro x
  rw [scalingSubsurface_defect_self]
  have h := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr x.2.2
  have h0 : 0 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  exact h0.trans h

/-- **Unconditional Hodge Index Past the First Prime on `polarFreeSmoothRealTestsAt r`
(`r ≤ ½(log 2 + 1/50)`):** -/
theorem polarFreeSmooth_scalingSubsurface_hodgeIndex_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).HodgeIndex := by
  rw [(scalingSubsurface (polarFreeSmoothRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
  intro x
  rw [scalingSubsurface_defect_self]
  have h := weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr x.2.2
  have h0 : 0 ≤ (1 / 20 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  exact h0.trans h

/-- **Unconditional Arithmetic Riemann–Roch, Ampleness, and Bézout Past the First Prime for
`strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)` (`r ≤ ½(log 2 + 1/50)`):** -/
theorem strictCoupledArithmeticCone_primitiveSmooth_riemannRoch_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).BezoutAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) := by
  have hH := primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo hr
  refine ⟨(strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex _).mpr hH,
    strictCoupledArithmeticCone_ample _, ?_⟩
  rw [strictCoupledArithmeticCone_eq_openPositiveCone]
  exact (scalingSubsurface (primitiveSmoothRealTestsAt r)).openPositiveCone_bezout hH

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, and
Canonical Surface Riemann–Roch Past the First Prime for `l2SourceCone c (primitiveSmoothRealTestsAt r)`
(`0 < c ≤ 1/1000`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem l2SourceCone_primitiveSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) := by
  let V := primitiveSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Strict Source-Defined Arithmetic Riemann–Roch and Ampleness Past the
First Prime for `strictL2SourceCone c (primitiveSmoothRealTestsAt r)`
(`0 < c ≤ 1/1000`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem strictL2SourceCone_primitiveSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (strictL2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (strictL2SourceCone c (primitiveSmoothRealTestsAt r)) := by
  let V := primitiveSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.strictSourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    strictL2SourceCone_ample c V⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, and
Canonical Surface Riemann–Roch Past the First Prime on `polarFreeSmoothRealTestsAt r`
(`0 < c ≤ 1/20`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem l2SourceCone_polarFreeSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 20) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) := by
  let V := polarFreeSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 20 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, and
Canonical Surface Riemann–Roch on `oddRealTestsAt r` Past the First Prime (`r ≤ 181/500`):** -/
theorem l2SourceCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths {r c : ℝ}
    (hr : r ≤ 181 / 500) (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (oddRealTestsAt r)) := by
  let V := oddRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_ge_of_mem_oddRealTestsAt hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, and
Canonical Surface Riemann–Roch on `realTestsAt a` (`a ≤ 3/10`, `0 < c ≤ 1/5000`):** -/
theorem l2SourceCone_realTestsAt_riemannRoch_of_le_three_tenths {a c : ℝ}
    (ha : a ≤ 3 / 10) (hc0 : 0 < c) (hc : c ≤ 1 / 5000) :
    (scalingSubsurface (realTestsAt a)).RiemannRochAxiom (l2SourceCone c (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).AmpleAxiom (l2SourceCone c (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (realTestsAt a)) := by
  let V := realTestsAt a
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_ge_of_mem_realTestsAt ha x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 5000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-! ### 5. All-Aperture Graded Source Riemann–Roch and Mixed-Parity Chebyshev Defect Floor -/

/-- **All-Aperture Chebyshev Defect Floor on `polarFreeSmoothRealTestsAt r` (`r > 0`):**
At every scale `r > 0`, the Castelnuovo–Severi defect on
`scalingSubsurface (polarFreeSmoothRealTestsAt r)` satisfies
`-(10 + 68 e^r) ∫ f(u)² du ≤ (scalingSubsurface (polarFreeSmoothRealTestsAt r)).defect x x`. -/
theorem polarFreeSmooth_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp {r : ℝ}
    (hr : 0 < r) (x : ℝ × ℝ × polarFreeSmoothRealTestsAt r) :
    -(10 + 68 * Real.exp r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).defect x x := by
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm x.2.2.1.2.1 x.2.2.1.2.2]
  exact neg_horizonExponent_mul_le_fullZeroForm_Icc ⟨r, hr⟩
    x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2

/-- **All-Aperture Mixed-Parity Chebyshev Defect Floor on the Full Ample-Orthogonal Hyperplane
`primitiveSmoothRealTestsAt r` (`r > 0`):**
At every scale `r > 0` and for every smooth test `f ∈ primitiveSmoothRealTestsAt r` orthogonal to
`H + V` (`evenPoleMoment f = 0`, with arbitrary `oddPoleMoment f`),
`-(10 + 78 e^r) ∫ f(u)² du ≤ (scalingSubsurface (primitiveSmoothRealTestsAt r)).defect x x`. -/
theorem primitiveSmooth_scalingSubsurface_defect_ge_neg_ten_add_seventy_eight_exp {r : ℝ}
    (hr : 0 < r) (x : ℝ × ℝ × primitiveSmoothRealTestsAt r) :
    -(10 + 78 * Real.exp r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).defect x x := by
  let F : ℝ → ℝ := x.2.2.1.1
  have hF2 : ContDiff ℝ 2 F := x.2.2.1.2.1
  have hF_top : ContDiff ℝ (⊤ : ℕ∞) F := x.2.2.2.1
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (x.2.2.2.2.1 hmem))
  have heven_mom : evenPoleMoment F = 0 := x.2.2.2.2.2
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF2 hFc,
    fullZeroForm_eq_even_add_odd hF2 hFc,
    integral_sq_eq_even_add_odd hF2.continuous hFc, mul_add]
  have hFe2 : ContDiff ℝ 2 (evenPartReal F) := contDiff_evenPartReal hF2
  have hFe_top : ContDiff ℝ (⊤ : ℕ∞) (evenPartReal F) :=
    (hF_top.add (hF_top.comp contDiff_neg)).div_const 2
  have hFe_c : HasCompactSupport (evenPartReal F) := hasCompactSupport_evenPartReal hFc
  have hFo2 : ContDiff ℝ 2 (oddPartReal F) := contDiff_oddPartReal hF2
  have hFo_c : HasCompactSupport (oddPartReal F) := hasCompactSupport_oddPartReal hFc
  have hFe_tsupp : tsupport (evenPartReal F) ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    have hu1 : F u = 0 := hsupp u hu
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
    simp [evenPartReal, hu1, hu2]
  have hFo_tsupp : tsupport (oddPartReal F) ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    have hu1 : F u = 0 := hsupp u hu
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
    simp [oddPartReal, hu1, hu2]
  have hFe_even_mom : evenPoleMoment (evenPartReal F) = 0 := by
    have hsum : F = fun u => evenPartReal F u + oddPartReal F u :=
      funext fun u => (evenPartReal_add_oddPartReal F u).symm
    have hC : evenPoleMoment F = evenPoleMoment (evenPartReal F) := by
      conv_lhs => rw [hsum]
      rw [evenPoleMoment_add hFe2.continuous hFe_c hFo2.continuous hFo_c,
        evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F), add_zero]
    linarith
  have hFe_odd_mom : oddPoleMoment (evenPartReal F) = 0 :=
    oddPoleMoment_eq_zero_of_even (evenPartReal_neg F)
  have hFe_floor : -(10 + 68 * Real.exp r) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      fullZeroForm (evenPartReal F) :=
    neg_horizonExponent_mul_le_fullZeroForm_Icc ⟨r, hr⟩ hFe_top hFe_tsupp hFe_even_mom hFe_odd_mom
  have hFo_mem : (⟨oddPartReal F, hFo2, hFo_c⟩ : realTests) ∈ oddRealTestsAt r :=
    ⟨hFo_tsupp, oddPartReal_neg F⟩
  have hFo_floor : -(78 * Real.exp r * ∫ u : ℝ, (oddPartReal F u) ^ 2) ≤
      fullZeroForm (oddPartReal F) := by
    rw [← weilPair_self_eq_fullZeroForm hFo2 hFo_c, ← scalingSubsurface_defect_self (oddRealTestsAt r)
      (0, 0, ⟨⟨oddPartReal F, hFo2, hFo_c⟩, hFo_mem⟩)]
    exact scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr
      (0, 0, ⟨⟨oddPartReal F, hFo2, hFo_c⟩, hFo_mem⟩)
  have hIe : 0 ≤ ∫ u : ℝ, (evenPartReal F u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hIo : 0 ≤ ∫ u : ℝ, (oddPartReal F u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp : 0 < Real.exp r := Real.exp_pos r
  nlinarith

/-- **The Graded Ample-Degree `L²` Source Cone (`gradedL2SourceCone`):**
Cycles `x` on `scalingSubsurface V` with `0 ≤ x · (H + V)` whose pole capacity `S.polar x x` pays
the graded source energy `c ∫ f(u)² du` (`c ∈ ℝ`). -/
def gradedL2SourceCone (c : ℝ) (V : Submodule ℝ realTests) : Set (ℝ × ℝ × V) :=
  {x | 0 ≤ (scalingSubsurface V).pair x (scalingSubsurface V).ample ∧
    l2SourceEnergy c V x ≤ (scalingSubsurface V).polar x x}

/-- When `c ≥ 0`, `l2SourceCone c V` coincides identically with `gradedL2SourceCone c V` because two
real numbers with nonnegative sum `x · H + x · V ≥ 0` and nonnegative product
`2 (x · H)(x · V) ≥ c ∫ f² ≥ 0` are both nonnegative. -/
theorem l2SourceCone_eq_gradedL2SourceCone {c : ℝ} (hc : 0 ≤ c) (V : Submodule ℝ realTests) :
    l2SourceCone c V = gradedL2SourceCone c V := by
  let S := scalingSubsurface V
  ext x
  rw [l2SourceCone, S.mem_sourceCone_iff, gradedL2SourceCone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hH, hV, hE⟩
    refine ⟨?_, hE⟩
    rw [S.pair_ample]
    linarith
  · rintro ⟨hA, hE⟩
    have hsum : 0 ≤ S.pair x S.H + S.pair x S.V := by
      rwa [S.pair_ample] at hA
    have hprod : 0 ≤ 2 * S.pair x S.H * S.pair x S.V := by
      rw [← S.polar_self]
      exact (l2SourceEnergy_nonneg hc V x).trans hE
    have hH : 0 ≤ S.pair x S.H := by
      by_contra hlt
      push Not at hlt
      have hV : 0 < S.pair x S.V := by linarith
      nlinarith
    have hV : 0 ≤ S.pair x S.V := by
      by_contra hlt
      push Not at hlt
      have hH' : 0 < S.pair x S.H := by linarith
      nlinarith
    exact ⟨hH, hV, hE⟩

/-- If `l2SourceEnergy c V x ≤ (scalingSubsurface V).defect x x` for all `x`, then
`gradedL2SourceCone c V` satisfies `RiemannRochAxiom` and `SurfaceRiemannRochAxiom 0 0`. -/
theorem gradedL2SourceCone_riemannRoch_of_le_defect (c : ℝ) (V : Submodule ℝ realTests)
    (hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ (scalingSubsurface V).defect x x) :
    (scalingSubsurface V).RiemannRochAxiom (gradedL2SourceCone c V) ∧
      (scalingSubsurface V).SurfaceRiemannRochAxiom 0 0 (gradedL2SourceCone c V) := by
  let S := scalingSubsurface V
  have hRR : S.RiemannRochAxiom (gradedL2SourceCone c V) := by
    intro x hx
    have hpol : l2SourceEnergy c V x ≤ S.polar x x := by
      have hd : S.defect x x = S.polar x x - S.pair x x := rfl
      linarith [hle x]
    rcases le_total 0 (S.pair x S.ample) with hA | hA
    · exact Or.inl ⟨hA, hpol⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [S.pair_neg_left]
        linarith
      · rw [l2SourceEnergy_neg, S.polar_neg_self]
        exact hpol
  refine ⟨hRR, fun x hx => ?_⟩
  have hxx : 0 < S.pair x x := by
    simp only [map_zero, sub_zero, zero_add] at hx
    linarith
  rcases hRR x hxx with h | h
  · exact Or.inl h
  · right
    have h0 : (0 : ℝ × ℝ × V) - x = -x := by abel
    rw [h0]
    exact h

/-- **All-Aperture Graded Source Riemann–Roch on `primitiveSmoothRealTestsAt r`,
`polarFreeSmoothRealTestsAt r`, and `oddRealTestsAt r` (`r > 0`):** -/
theorem gradedL2SourceCone_all_apertures_riemannRoch {r : ℝ} (hr : 0 < r) :
    ((scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-(10 + 78 * Real.exp r)) (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (gradedL2SourceCone (-(10 + 78 * Real.exp r)) (primitiveSmoothRealTestsAt r))) ∧
    ((scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-(10 + 68 * Real.exp r)) (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (gradedL2SourceCone (-(10 + 68 * Real.exp r)) (polarFreeSmoothRealTestsAt r))) ∧
    ((scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-78 * Real.exp r) (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (gradedL2SourceCone (-78 * Real.exp r) (oddRealTestsAt r))) :=
  ⟨gradedL2SourceCone_riemannRoch_of_le_defect _ _
      (primitiveSmooth_scalingSubsurface_defect_ge_neg_ten_add_seventy_eight_exp hr),
    gradedL2SourceCone_riemannRoch_of_le_defect _ _
      (polarFreeSmooth_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp hr),
    gradedL2SourceCone_riemannRoch_of_le_defect _ _ fun x => by
      simpa [l2SourceEnergy, neg_mul] using
        scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr x⟩

/-- **Unconditional `C²` Spectral Symbol Representation of `markovEnergy`:**
For every `a : ℝ` and every `C²` test `f : ℝ → ℂ` supported in `[-a, a]` (without any
pole-vanishing condition `paperFT f (±I/2) = 0`), the archimedean-minus-prime energy
`markovEnergy f` equals the spectral symbol integral
`Re ∫ h_{f ⋆ f̃}(τ) (μ(τ) + P_{e^{2a}}(τ)) dτ`. -/
theorem markovEnergy_eq_integral_mu_add_PX {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    _root_.RHTower.markovEnergy f =
      (∫ τ : ℝ, paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)).re := by
  have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  set k := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hks : tsupport k ⊆ Icc (-(2 * a)) (2 * a) := EF.tsupport_weilTest_subset hfs' hfs'
  have hFk := EF.integrable_fourier_of_contDiff_two hkd hkc
  have hμ := EF.integrable_paperFT_mul_mu hkd hkc gammaFacts
  have hPX := EF.integrable_paperFT_mul_PX (2 * a) hFk
  unfold _root_.RHTower.markovEnergy
  rw [weilFullFunctional_vonMangoldt]
  have hsub : EF.literatureRHS k - weilPoleTerm k =
      ∫ τ : ℝ, paperFT k τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ) := by
    have hcancel (P S G : ℂ) : P - S + G - P = -S + G := by ring
    unfold EF.literatureRHS weilPoleTerm
    rw [hcancel, EF.prime_term hkd.continuous hks hFk, EF.gamma_term,
      ← integral_add hPX hμ]
    congr 1
    ext τ
    push_cast
    ring
  rw [hsub]

/-- **Spectral Symbol Lower Bound for `markovEnergy` on Arbitrary `C²` Tests:**
If `-(E / (2π)) ≤ μ(τ) + P_{e^{2a}}(τ)` for all `τ : ℝ`, then every `C²` test `f : ℝ → ℂ`
supported in `[-a, a]` (without pole-vanishing hypotheses) satisfies
`-(E * ∫ ‖f‖²) ≤ markovEnergy f`. -/
theorem neg_mul_integral_norm_sq_le_markovEnergy_of_symbol {a E : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hE : ∀ τ : ℝ, -(E / (2 * π)) ≤ mu τ + PX (Real.exp (2 * a)) τ) :
    -(E * ∫ u : ℝ, ‖f u‖ ^ 2) ≤ _root_.RHTower.markovEnergy f := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hk := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  have hM := markovEnergy_eq_integral_mu_add_PX hf hfs
  have hi := integrable_paperFT_mul_mu_add_PX hk hkc (2 * a)
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [hM, ← hre]
  have hpt : ∀ τ : ℝ, -(E / (2 * π)) * ‖paperFT f τ‖ ^ 2 ≤
      (paperFT (EF.weilTest f f) τ * ((mu τ + PX (Real.exp (2 * a)) τ : ℝ) : ℂ)).re := by
    intro τ
    rw [paperFT_weilTest_self_ofReal hf.continuous hfc τ, ← Complex.ofReal_mul, Complex.ofReal_re,
      mul_comm (‖paperFT f τ‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hE τ) (sq_nonneg _)
  have hi2 := integrable_normSq_paperFT hf hfs
  have hmono := integral_mono (hi2.const_mul (-(E / (2 * π)))) hi.re hpt
  rw [integral_const_mul, integral_norm_sq_paperFT_eq hf hfs] at hmono
  have hπ := Real.pi_pos
  have e : -(E / (2 * π)) * (2 * π * ∫ u : ℝ, ‖f u‖ ^ 2) = -(E * ∫ u : ℝ, ‖f u‖ ^ 2) := by
    field_simp
  rwa [e] at hmono

/-- **Chebyshev Spectral Lower Bound for `markovEnergy` on Arbitrary Real `C²` Tests Supported in `[-r, r]`:**
For every `r : ℝ` and every real `C²` test `F` supported in `[-r, r]`,
`-(10 + 68 e^r) ∫ F(u)² du ≤ markovEnergy F`. -/
theorem neg_horizonExponent_mul_le_markovEnergy_Icc {r : ℝ} {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Icc (-r) r) :
    -(10 + 68 * Real.exp r) * ∫ u : ℝ, F u ^ 2 ≤
      _root_.RHTower.markovEnergy (fun u => (F u : ℂ)) := by
  have hFc : ContDiff ℝ 2 (fun u => (F u : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hFcs : tsupport (fun u => (F u : ℂ)) ⊆ Icc (-r) r := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    exact hFs (subset_tsupport F fun h0 => hx (by simp [h0]))
  have hsq : Real.sqrt (Real.exp (2 * r)) = Real.exp r := by
    rw [show 2 * r = r + r by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos r).le]
  have hbound := neg_mul_integral_norm_sq_le_markovEnergy_of_symbol hFc hFcs fun τ => by
    simpa [horizonExponent, hsq] using neg_horizonExponent_le_mu_add_PX (Real.exp_pos (2 * r)).le τ
  have hnorm : (∫ u : ℝ, ‖(F u : ℂ)‖ ^ 2) = ∫ u : ℝ, F u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm] at hbound
  linarith

/-- **The Subspace `evenRealTestsAt r` of Even `C²` Compactly Supported Real Tests in `[-r, r]`:** -/
def evenRealTestsAt (r : ℝ) : Submodule ℝ realTests where
  carrier := {f : realTests | tsupport f.1 ⊆ Icc (-r) r ∧ ∀ u : ℝ, f.1 (-u) = f.1 u}
  add_mem' {f g} hf hg :=
    ⟨(tsupport_add f.1 g.1).trans (union_subset hf.1 hg.1),
      fun u => by simp [hf.2 u, hg.2 u]⟩
  zero_mem' := ⟨by simp [tsupport], fun _ => rfl⟩
  smul_mem' c {f} hf :=
    ⟨(tsupport_smul_subset_right (fun _ : ℝ => c) f.1).trans hf.1,
      fun u => by simp [hf.2 u]⟩

/-- **All-Aperture Chebyshev Defect Floor on `evenRealTestsAt r` (No Pole-Vanishing or `C^∞` Hypothesis):**
For every `r : ℝ` and every cycle `x : ℝ × ℝ × evenRealTestsAt r`,
`-(10 + 68 e^r) ∫ f(u)² du ≤ (scalingSubsurface (evenRealTestsAt r)).defect x x`. -/
theorem even_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp (r : ℝ)
    (x : ℝ × ℝ × evenRealTestsAt r) :
    -(10 + 68 * Real.exp r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      (scalingSubsurface (evenRealTestsAt r)).defect x x := by
  let F : ℝ → ℝ := x.2.2.1.1
  have hF2 : ContDiff ℝ 2 F := x.2.2.1.2.1
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hFs : tsupport F ⊆ Icc (-r) r := x.2.2.2.1
  have hodd : oddPoleMoment F = 0 := oddPoleMoment_eq_zero_of_even x.2.2.2.2
  have hodd0 : oddPoleMoment F ^ 2 = 0 := by rw [hodd]; ring
  have heven_nn : 0 ≤ 2 * evenPoleMoment F ^ 2 := by positivity
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF2 hFc]
  have hM := neg_horizonExponent_mul_le_markovEnergy_Icc hF2 hFs
  unfold fullZeroForm
  linarith

/-- **Unconditional All-Aperture Chebyshev Defect Floor on the Entire Unrestricted `realTestsAt r` (`r > 0`):**
For every aperture `r > 0` and every cycle `x : ℝ × ℝ × realTestsAt r` (requiring only `C²`
regularity, with no parity restriction and no pole-moment vanishing hypothesis),
`-(10 + 72 e^r) ∫ f(u)² du ≤ (scalingSubsurface (realTestsAt r)).defect x x`. -/
theorem realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp {r : ℝ}
    (hr : 0 < r) (x : ℝ × ℝ × realTestsAt r) :
    -(10 + 72 * Real.exp r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      (scalingSubsurface (realTestsAt r)).defect x x := by
  let F : ℝ → ℝ := x.2.2.1.1
  have hF2 : ContDiff ℝ 2 F := x.2.2.1.2.1
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (x.2.2.2 hmem))
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF2 hFc,
    fullZeroForm_eq_even_add_odd hF2 hFc,
    integral_sq_eq_even_add_odd hF2.continuous hFc, mul_add]
  have hFe2 : ContDiff ℝ 2 (evenPartReal F) := contDiff_evenPartReal hF2
  have hFe_c : HasCompactSupport (evenPartReal F) := hasCompactSupport_evenPartReal hFc
  have hFo2 : ContDiff ℝ 2 (oddPartReal F) := contDiff_oddPartReal hF2
  have hFo_c : HasCompactSupport (oddPartReal F) := hasCompactSupport_oddPartReal hFc
  have hFe_tsupp : tsupport (evenPartReal F) ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    have hu1 : F u = 0 := hsupp u hu
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
    simp [evenPartReal, hu1, hu2]
  have hFo_tsupp : tsupport (oddPartReal F) ⊆ Icc (-r) r := by
    refine tsupport_subset_Icc_of_vanish_outside fun u hu => ?_
    have hu1 : F u = 0 := hsupp u hu
    have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
    simp [oddPartReal, hu1, hu2]
  have hFo_supp : ∀ u : ℝ, r < |u| → oddPartReal F u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (hFo_tsupp hmem))
  have hFe_odd_mom : oddPoleMoment (evenPartReal F) = 0 :=
    oddPoleMoment_eq_zero_of_even (evenPartReal_neg F)
  have hFe_odd0 : oddPoleMoment (evenPartReal F) ^ 2 = 0 := by rw [hFe_odd_mom]; ring
  have hFe_even_nn : 0 ≤ 2 * evenPoleMoment (evenPartReal F) ^ 2 := by positivity
  have hFe_M := neg_horizonExponent_mul_le_markovEnergy_Icc hFe2 hFe_tsupp
  have hFe_floor : -(10 + 68 * Real.exp r) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      fullZeroForm (evenPartReal F) := by
    unfold fullZeroForm
    linarith
  have hFo_even_mom : evenPoleMoment (oddPartReal F) = 0 :=
    evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F)
  have hFo_even0 : evenPoleMoment (oddPartReal F) ^ 2 = 0 := by rw [hFo_even_mom]; ring
  have hFo_M := neg_horizonExponent_mul_le_markovEnergy_Icc hFo2 hFo_tsupp
  have hFo_pole : 2 * oddPoleMoment (oddPartReal F) ^ 2 ≤
      4 * Real.exp r * ∫ u : ℝ, (oddPartReal F u) ^ 2 :=
    poleCharge_le_four_mul_exp_mul_sq hFo2.continuous hFo_c (oddPartReal_neg F) hr hFo_supp
  have hFo_floor : -(10 + 72 * Real.exp r) * ∫ u : ℝ, (oddPartReal F u) ^ 2 ≤
      fullZeroForm (oddPartReal F) := by
    unfold fullZeroForm
    linarith
  have hIe : 0 ≤ ∫ u : ℝ, (evenPartReal F u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hexp : 0 < Real.exp r := Real.exp_pos r
  have h1 : -(10 + 72 * Real.exp r) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      -(10 + 68 * Real.exp r) * ∫ u : ℝ, (evenPartReal F u) ^ 2 := by nlinarith
  linarith

/-- **Unconditional All-Aperture Graded Source Riemann–Roch on the Entire Unrestricted
`realTestsAt r` (`r > 0`) and `evenRealTestsAt r` (`r ∈ ℝ`):** -/
theorem gradedL2SourceCone_realTestsAt_all_apertures_riemannRoch {r : ℝ} (hr : 0 < r) :
    ((scalingSubsurface (realTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-(10 + 72 * Real.exp r)) (realTestsAt r)) ∧
      (scalingSubsurface (realTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (gradedL2SourceCone (-(10 + 72 * Real.exp r)) (realTestsAt r))) ∧
    ((scalingSubsurface (evenRealTestsAt r)).RiemannRochAxiom
        (gradedL2SourceCone (-(10 + 68 * Real.exp r)) (evenRealTestsAt r)) ∧
      (scalingSubsurface (evenRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (gradedL2SourceCone (-(10 + 68 * Real.exp r)) (evenRealTestsAt r))) :=
  ⟨gradedL2SourceCone_riemannRoch_of_le_defect _ _
      (realTestsAt_scalingSubsurface_defect_ge_neg_ten_add_seventy_two_exp hr),
    gradedL2SourceCone_riemannRoch_of_le_defect _ _
      (even_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp r)⟩

/-- **Overlapping Two-Prime (`r = 23/40`, `relevantShifts (23/40) = {2, 3}`) Strip-Surplus
Defect Allocation on `scalingSubsurface (oddRealTestsAt (23/40))`:**
For every `R > 23/40` and every cycle `x : ℝ × ℝ × oddRealTestsAt (23/40)` with `f = x.2.2.1.1`,
the Castelnuovo–Severi defect absorbs both prime shifts `2` and `3` into the archimedean strip
surplus `2 stripSurplus f (log 2 - 23/40) (23/40)` and `poleCharge f` with `(1/62) ∫_{S₂} f²` to
spare. -/
theorem scalingSubsurface_odd_defect_twentyThreeFortieths_stripSurplus_floor {R : ℝ}
    (hR : 23 / 40 < R) (x : ℝ × ℝ × oddRealTestsAt (23 / 40)) :
    let f : ℝ → ℝ := x.2.2.1.1
    surplusPool (aperturePlateau (23 / 40) R) f +
        crossingPotentialTerm (aperturePlateau (23 / 40) R) f +
        gaugeRemainder (aperturePlateau (23 / 40) R) f -
        2 * stripSurplus f (Real.log 2 - 23 / 40) (23 / 40) -
        poleCharge f +
        1 / 62 * (∫ u in (Real.log 2 - 23 / 40)..(23 / 40), f u ^ 2) ≤
      (scalingSubsurface (oddRealTestsAt (23 / 40))).defect x x := by
  intro f
  have hF1 : ContDiff ℝ 1 f := x.2.2.1.2.1.of_le one_le_two
  have hFc : HasCompactSupport f := x.2.2.1.2.2
  have hodd : ∀ u : ℝ, f (-u) = -f u := x.2.2.2.2
  have hsupp : ∀ u : ℝ, 23 / 40 < |u| → f u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (x.2.2.2.1 hmem))
  have hledger := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger
    (by norm_num : (0 : ℝ) < 23 / 40) hR x
  have halloc := reflectedPrimePolarCost_le_stripSurplus_add_poleCharge_twentyThreeFortieths
    hF1 hFc hodd hsupp
  linarith

/-- **Unconditional All-Aperture De La Vallée Poussin Sobolev Defect Floor on
`scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`):**
With universal constants `c > 0` and `K > 0`, for every `0 < r < R` and every cycle
`x : ℝ × ℝ × oddRealTestsAt r` (`f = x.2.2.1.1`), the Castelnuovo–Severi defect satisfies
`surplusPool + crossingPotentialTerm + gaugeRemainder - K e^r e^{-c√r} (∫ f² + ½ ∫ (f')²) ≤ defect x x`,
strictly beating the `e^r` barrier by the zero-free-region factor `e^{-c√r}` at all apertures. -/
theorem exists_scalingSubsurface_odd_defect_deLaValleePoussin_sobolev_floor :
    ∃ c > 0, ∃ K > 0, ∀ {r R : ℝ}, 0 < r → r < R →
      ∀ (x : ℝ × ℝ × oddRealTestsAt r),
      let f : ℝ → ℝ := x.2.2.1.1
      surplusPool (aperturePlateau r R) f +
          crossingPotentialTerm (aperturePlateau r R) f +
          gaugeRemainder (aperturePlateau r R) f -
          K * Real.exp r * Real.exp (-c * Real.sqrt r) *
            ((∫ u, f u ^ 2) + (1 / 2) * ∫ u, deriv f u ^ 2) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  obtain ⟨c, hc, K, hK, hcost⟩ := exists_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev
  refine ⟨c, hc, K, hK, fun {r R} hr hR x => ?_⟩
  intro f
  have hF1 : ContDiff ℝ 1 f := x.2.2.1.2.1.of_le one_le_two
  have hFc : HasCompactSupport f := x.2.2.1.2.2
  have hodd : ∀ u : ℝ, f (-u) = -f u := x.2.2.2.2
  have hsupp : ∀ u : ℝ, r < |u| → f u = 0 :=
    fun u hu => image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (x.2.2.2.1 hmem))
  have hledger := scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hR x
  have hbound := hcost r f hr hF1 hFc hodd hsupp
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
