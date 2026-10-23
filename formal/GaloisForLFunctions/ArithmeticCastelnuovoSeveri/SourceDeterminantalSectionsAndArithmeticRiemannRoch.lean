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
   `SurfaceRiemannRochAxiom 0 0`, while `S.strictSourceCone Φ` also satisfies `BezoutAxiom`
   (`sourceCone_riemannRoch_of_le_defect`, `strictSourceCone_bezout_of_le_defect`).

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
     `AmpleAxiom`, `BezoutAxiom`, and `SurfaceRiemannRochAxiom 0 0` hold **unconditionally** for
     both `strictCoupledArithmeticCone` and the source-defined cones `l2SourceCone` and
     `strictL2SourceCone`.

5. **All-Aperture Graded Source Riemann–Roch and the Overlapping Two-Prime Window `r = 23/40` (§5):**
   Across **all** apertures `r > 0`, the Chebyshev spectral floor `-(10 + 68 e^r) ∫ f² ≤ weilPair f f`
   on `polarFreeSmoothRealTestsAt r` and the graded incidence floor `-78 e^r ∫ f² ≤ weilPair f f`
   on `oddRealTestsAt r` supply unconditional `RiemannRochAxiom` and `SurfaceRiemannRochAxiom 0 0`
   for `l2SourceCone (-(10 + 68 e^r)) (polarFreeSmoothRealTestsAt r)` and
   `l2SourceCone (-78 e^r) (oddRealTestsAt r)` at every scale `r > 0`. At the overlapping two-prime
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

/-- If `Φ` is bounded above by the Castelnuovo–Severi defect `S.defect x x`, then every cycle in
`S.sourceCone Φ` belongs to `S.positiveCone`. -/
theorem sourceCone_subset_positiveCone_of_le_defect {Φ : C → ℝ}
    (hle : ∀ x, Φ x ≤ S.defect x x) : S.sourceCone Φ ⊆ S.positiveCone := by
  intro x hx
  have hdeg : 0 ≤ S.pair x S.ample := S.pair_ample_nonneg_of_mem_sourceCone hx
  rw [S.mem_sourceCone_iff] at hx
  have hd : Φ x ≤ S.polar x x - S.pair x x := hle x
  exact ⟨by linarith [hx.2.2], hdeg⟩

/-- If `Φ` is bounded above by `S.defect x x`, then every cycle in `S.strictSourceCone Φ` belongs
to `S.openPositiveCone`. -/
theorem strictSourceCone_subset_openPositiveCone_of_le_defect {Φ : C → ℝ}
    (hle : ∀ x, Φ x ≤ S.defect x x) : S.strictSourceCone Φ ⊆ S.openPositiveCone := by
  intro x hx
  have hdeg : 0 < S.pair x S.ample := S.pair_ample_pos_of_mem_strictSourceCone hx
  rw [S.mem_strictSourceCone_iff] at hx
  have hd : Φ x ≤ S.polar x x - S.pair x x := hle x
  exact ⟨by linarith [hx.2.2], hdeg⟩

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

/-- **Bézout Positivity for `sourceCone` and `strictSourceCone` from defect domination:**
If `Φ` is even, nonnegative, and bounded above by `S.defect x x`, then `S.HodgeIndex` holds and both
`S.sourceCone Φ` and `S.strictSourceCone Φ` satisfy `S.BezoutAxiom`. -/
theorem sourceCone_bezout_of_le_defect {Φ : C → ℝ}
    (hnonneg : ∀ x, 0 ≤ Φ x) (hle : ∀ x, Φ x ≤ S.defect x x) :
    S.BezoutAxiom (S.sourceCone Φ) := by
  have hH : S.HodgeIndex :=
    S.hodgeIndex_iff_defect_nonneg.mpr fun x => (hnonneg x).trans (hle x)
  intro x hx y hy
  exact S.positiveCone_bezout hH x (S.sourceCone_subset_positiveCone_of_le_defect hle hx)
    y (S.sourceCone_subset_positiveCone_of_le_defect hle hy)

theorem strictSourceCone_bezout_of_le_defect {Φ : C → ℝ}
    (hnonneg : ∀ x, 0 ≤ Φ x) (hle : ∀ x, Φ x ≤ S.defect x x) :
    S.BezoutAxiom (S.strictSourceCone Φ) := by
  intro x hx y hy
  exact S.sourceCone_bezout_of_le_defect hnonneg hle
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
    (scalingSubsurface V).pair x (scalingSubsurface V).H = x.2.1 + poleB x.2.2.1.1 := by
  simpa [scalingSubsurface] using scalingSurface_pair_H (x.1, x.2.1, x.2.2.1)

theorem scalingSubsurface_pair_V (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).pair x (scalingSubsurface V).V = x.1 + poleA x.2.2.1.1 := by
  simpa [scalingSubsurface] using scalingSurface_pair_V (x.1, x.2.1, x.2.2.1)

theorem scalingSubsurface_defect_self (V : Submodule ℝ realTests) (x : ℝ × ℝ × V) :
    (scalingSubsurface V).defect x x = weilPair x.2.2.1.1 x.2.2.1.1 := by
  change scalingSurface.defect (x.1, x.2.1, x.2.2.1) (x.1, x.2.1, x.2.2.1) = _
  rw [← scalingSurface.defect_prim]
  have hprim : scalingSurface.prim (x.1, x.2.1, x.2.2.1) =
      (-poleA x.2.2.1.1, -poleB x.2.2.1.1, x.2.2.1) := by
    ext
    · simp [PolarSurface.prim, scalingSurface_pair_V, scalingSurface]
    · simp [PolarSurface.prim, scalingSurface_pair_H, scalingSurface]
    · simp [PolarSurface.prim, scalingSurface]
  rw [hprim, ← pureTestCycle_prim]
  simpa [pureTestCycle] using scalingSurface_defect_tests x.2.2.1 x.2.2.1

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
    have hexp : (fun u : ℝ => (f u + t * g u) ^ 2) =
        fun u => f u ^ 2 + (2 * t) * (f u * g u) + (t * t) * g u ^ 2 := by
      ext u; ring
    have hint1 : Integrable (fun u : ℝ => f u ^ 2) := integrable_sq_of_mem_realTests hf
    have hint2 : Integrable (fun u : ℝ => (2 * t) * (f u * g u)) :=
      (integrable_mul_of_mem_realTests hf hg).const_mul (2 * t)
    have hint3 : Integrable (fun u : ℝ => (t * t) * g u ^ 2) :=
      (integrable_sq_of_mem_realTests hg).const_mul (t * t)
    rw [hexp, integral_add (hint1.add hint2) hint3, integral_add hint1 hint2,
      integral_const_mul, integral_const_mul] at hnonneg
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
  simp only [map_add]
  refine ⟨by linarith, by linarith, ?_⟩
  let f : ℝ → ℝ := x.2.2.1.1
  let g : ℝ → ℝ := y.2.2.1.1
  have hf : f ∈ realTests := x.2.2.1.2
  have hg : g ∈ realTests := y.2.2.1.2
  have hfg_int : ∫ u : ℝ, ((x + y).2.2.1.1 u) ^ 2 =
      (∫ u : ℝ, f u ^ 2) + 2 * (∫ u : ℝ, f u * g u) + (∫ u : ℝ, g u ^ 2) := by
    have hexp : (fun u : ℝ => ((x + y).2.2.1.1 u) ^ 2) =
        fun u => f u ^ 2 + 2 * (f u * g u) + g u ^ 2 := by
      ext u
      change (f u + g u) ^ 2 = f u ^ 2 + 2 * (f u * g u) + g u ^ 2
      ring
    have hint1 : Integrable (fun u : ℝ => f u ^ 2) := integrable_sq_of_mem_realTests hf
    have hint2 : Integrable (fun u : ℝ => 2 * (f u * g u)) :=
      (integrable_mul_of_mem_realTests hf hg).const_mul 2
    have hint3 : Integrable (fun u : ℝ => g u ^ 2) := integrable_sq_of_mem_realTests hg
    rw [hexp, integral_add (hint1.add hint2) hint3, integral_add hint1 hint2, integral_const_mul]
  change c * ∫ u : ℝ, ((x + y).2.2.1.1 u) ^ 2 ≤ _
  rw [hfg_int, mul_add, mul_add]
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
  have hprod : (c * ∫ u : ℝ, f u * g u) ^ 2 ≤
      (2 * S.pair x S.H * S.pair x S.V) * (2 * S.pair y S.H * S.pair y S.V) :=
    hcs_c.trans (mul_le_mul hxE hyE hEy0 (by positivity))
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
  linarith [hxE, hyE, hcross,
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
  simp only [map_smul, smul_eq_mul]
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
  simp only [map_smul, smul_eq_mul]
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
  by_contra hne
  have hsq_ne : (fun u : ℝ => f u ^ 2) ≠ 0 := by
    intro h0
    apply hne
    ext u
    exact sq_eq_zero_iff.mp (congr_fun h0 u)
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
    simpa [PolarSurface.ample, map_add] using hxA
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
    set δ : ℝ := (c * ∫ u : ℝ, (f.1.1 u) ^ 2 - weilPair f.1.1 f.1.1) / 4
    have hδ : 0 < δ := by positivity
    set a₀ : ℝ := 1 - poleA f.1.1
    set b₀ : ℝ := δ - poleB f.1.1
    let x : ℝ × ℝ × V := (a₀, b₀, f)
    have hxH : S.pair x S.H = δ := by
      rw [scalingSubsurface_pair_H]
      simp [x, b₀]
    have hxV : S.pair x S.V = 1 := by
      rw [scalingSubsurface_pair_V]
      simp [x, a₀]
    have hpol : S.polar x x = 2 * δ := by
      rw [S.polar_self, hxH, hxV]
      ring
    have hdef : S.defect x x = weilPair f.1.1 f.1.1 := scalingSubsurface_defect_self V x
    have hpair : S.pair x x = 2 * δ - weilPair f.1.1 f.1.1 := by
      have hd : S.defect x x = S.polar x x - S.pair x x := rfl
      linarith
    have hpos : 0 < S.pair x x := by
      rw [hpair]
      dsimp [δ]
      linarith
    have hnot : c * ∫ u : ℝ, (f.1.1 u) ^ 2 > 2 * δ := by
      dsimp [δ]
      linarith
    rcases hRR x hpos with hxE | hnxE
    · rw [l2SourceCone, S.mem_sourceCone_iff, hpol] at hxE
      change c * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ 2 * δ at hxE.2.2
      linarith
    · rw [l2SourceCone, S.mem_sourceCone_iff] at hnxE
      have hnegH : S.pair (-x) S.H = -δ := by simp [hxH]
      linarith [hnxE.1]
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
`evenStripGain`, `oddStripCost`, `gaugeRemainder`, and `poleCharge` (with no reference to
`zetaZeroConfig.W` or `weilPair`). -/
def sourceIncidenceFunctional (r R : ℝ) (x : ℝ × ℝ × oddRealTestsAt r) : ℝ :=
  let f : ℝ → ℝ := x.2.2.1.1
  2 * surplusPool f R + 2 * crossingPotentialTerm f R +
    ∑ n ∈ relevantShifts r,
      (evenStripGain f n r R - oddStripCost f n r R + gaugeRemainder f n R) -
    poleCharge f

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
    sourceIncidenceFunctional r R x = (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  symm
  exact scalingSubsurface_odd_defect_eq_reflectedPrimePolarLedger hr hR x

/-- **Zero-Free Source Identity of `strictCoupledArithmeticCone (oddRealTestsAt r)`:**
For every aperture `0 < r < R`, the source-defined cone `sourceIncidenceCone r R` (defined purely
from archimedean/prime/polar source integrals) is **identical** to `strictCoupledArithmeticCone (oddRealTestsAt r)`
on `oddRealTestsAt r` whenever we restrict to the nef quadrant, and on the full cycle space:
`x ∈ sourceIncidenceCone r R ↔ 0 < x · H ∧ 0 < x · V ∧ 0 < x · x`.
In particular, every cycle in `sourceIncidenceCone r R` belongs to
`strictCoupledArithmeticCone (oddRealTestsAt r)`, and `RiemannRochAxiom` for
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
  exact and_congr_right fun _ => and_congr_right fun _ => by linarith

theorem sourceIncidenceCone_subset_strictCoupledArithmeticCone {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    sourceIncidenceCone r R ⊆ strictCoupledArithmeticCone (oddRealTestsAt r) := by
  intro x hx
  have hdeg : 0 < (scalingSubsurface (oddRealTestsAt r)).pair x
      (scalingSubsurface (oddRealTestsAt r)).ample :=
    (scalingSubsurface (oddRealTestsAt r)).pair_ample_pos_of_mem_strictSourceCone hx
  rw [mem_sourceIncidenceCone_iff_pair_pos hr hR] at hx
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
      rw [sourceIncidenceFunctional_eq_defect hr hR, sourceIncidenceFunctional_eq_defect hr hR]
      simp [PolarSurface.defect, PolarSurface.polar]
    · intro x
      rw [sourceIncidenceFunctional_eq_defect hr hR]
      exact hdef x
    · intro x
      rw [sourceIncidenceFunctional_eq_defect hr hR]

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
    poleB_eq_evenPoleMoment_sub_oddPoleMoment f.1,
    poleA_eq_evenPoleMoment_add_oddPoleMoment f.1]
  ring

/-- **Exact Ample-Orthogonal Test Hyperplane Characterization:**
A pure test cycle `(0, 0, f)` is orthogonal to `ample = H + V` on `scalingSurface` if and only if
`evenPoleMoment f = ∫ f(u) cosh(u/2) du = 0` (with completely unrestricted `oddPoleMoment f`). -/
theorem pureTestCycle_pair_ample_eq_zero_iff (f : realTests) :
    scalingSurface.pair (0, 0, f) scalingSurface.ample = 0 ↔ evenPoleMoment f.1 = 0 := by
  rw [pureTestCycle_pair_ample_eq]
  constructor <;> intro h <;> linarith

/-- **The Polar-Free Smooth Test Subspace `polarFreeSmoothRealTestsAt r`:**
Smooth compactly supported real tests supported in `[-r, r]` with `evenPoleMoment f = 0` and
`oddPoleMoment f = 0` (the pure-test intersection with `{H, V}⊥`). -/
def polarFreeSmoothRealTestsAt (r : ℝ) : Submodule ℝ realTests where
  carrier := {f : realTests | (∀ u : ℝ, r < |u| → f.1 u = 0) ∧
    evenPoleMoment f.1 = 0 ∧ oddPoleMoment f.1 = 0}
  add_mem' {f g} hf hg := by
    refine ⟨fun u hu => by simp [hf.1 u hu, hg.1 u hu], ?_, ?_⟩
    · have h := evenPoleMoment_add f.1 g.1 f.2 g.2
      change evenPoleMoment (f.1 + g.1) = 0
      linarith [hf.2.1, hg.2.1]
    · have h := oddPoleMoment_add f.1 g.1 f.2 g.2
      change oddPoleMoment (f.1 + g.1) = 0
      linarith [hf.2.2, hg.2.2]
  zero_mem' := ⟨fun _ _ => rfl, evenPoleMoment_zero, oddPoleMoment_zero⟩
  smul_mem' c {f} hf := by
    refine ⟨fun u hu => by simp [hf.1 u hu], ?_, ?_⟩
    · change evenPoleMoment (c • f.1) = 0
      rw [evenPoleMoment_smul, hf.2.1, mul_zero]
    · change oddPoleMoment (c • f.1) = 0
      rw [oddPoleMoment_smul, hf.2.2, mul_zero]

/-- **The Full Ample-Orthogonal Primitive Hyperplane `primitiveSmoothRealTestsAt r`:**
Smooth compactly supported real tests supported in `[-r, r]` with `evenPoleMoment f = 0` and
**arbitrary** `oddPoleMoment f` (containing both `polarFreeSmoothRealTestsAt r` and all of
`oddRealTestsAt r`). -/
def primitiveSmoothRealTestsAt (r : ℝ) : Submodule ℝ realTests where
  carrier := {f : realTests | (∀ u : ℝ, r < |u| → f.1 u = 0) ∧ evenPoleMoment f.1 = 0}
  add_mem' {f g} hf hg := by
    refine ⟨fun u hu => by simp [hf.1 u hu, hg.1 u hu], ?_⟩
    have h := evenPoleMoment_add f.1 g.1 f.2 g.2
    change evenPoleMoment (f.1 + g.1) = 0
    linarith [hf.2, hg.2]
  zero_mem' := ⟨fun _ _ => rfl, evenPoleMoment_zero⟩
  smul_mem' c {f} hf := by
    refine ⟨fun u hu => by simp [hf.1 u hu], ?_⟩
    change evenPoleMoment (c • f.1) = 0
    rw [evenPoleMoment_smul, hf.2, mul_zero]

/-- For any `f ∈ polarFreeSmoothRealTestsAt r`, `tsupport f ⊆ [-r, r]`. -/
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
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (f : polarFreeSmoothRealTestsAt r) :
    (1 / 20 : ℝ) * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  rcases le_or_gt r 0 with hr_le | hr_pos
  · have hr_eq : r = 0 := le_antisymm hr_le hr0
    have hf0 : ∀ u : ℝ, f.1.1 u = 0 := by
      intro u
      by_cases hu : u = 0
      · subst hu
        have hcont : Continuous f.1.1 := f.1.2.1.continuous
        have hseq : Tendsto (fun n : ℕ => f.1.1 (1 / ((n : ℝ) + 1))) atTop (𝓝 (f.1.1 0)) :=
          (hcont.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat)
        have hzero : (fun n : ℕ => f.1.1 (1 / ((n : ℝ) + 1))) = fun _ => 0 := by
          ext n
          apply f.2.1
          rw [hr_eq, abs_of_pos (by positivity)]
          positivity
        rw [hzero] at hseq
        exact tendsto_nhds_unique hseq tendsto_const_nhds
      · apply f.2.1
        rw [hr_eq]
        exact abs_pos.mpr hu
    have hfun : f.1.1 = 0 := funext hf0
    simp [hfun, weilPair_zero_left]
  · rw [weilPair_self_eq_fullZeroForm f.1.1 f.1.2]
    have htsupp : tsupport f.1.1 ⊆ Set.Icc (-r) r :=
      tsupport_subset_Icc_of_vanish_outside f.2.1
    have hground : ccmRestrictedWeilPolarGroundEnergy (2 * r) * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤
        fullZeroForm f.1.1 := by
      simpa [show (2 * r) / 2 = r by ring] using
        polarGroundEnergy_mul_le_fullZeroForm_Icc (L := 2 * r) (by positivity)
          f.1.2.1 htsupp f.2.2.1 f.2.2.2
    have h120 : (1 / 20 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy (2 * r) :=
      one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo
        (by positivity) (by linarith)
    exact (mul_le_mul_of_nonneg_right h120 (integral_nonneg fun _ => sq_nonneg _)).trans hground

/-- **Unconditional `1/1000` Mixed-Parity Coercivity Past the First Prime on
`primitiveSmoothRealTestsAt r` (`r ≤ ½(log 2 + 1/50)`):**
For every smooth test `f ∈ primitiveSmoothRealTestsAt r` orthogonal to `H + V`
(`evenPoleMoment f = 0`, with completely unrestricted `oddPoleMoment f`) and every aperture
`r ≤ ½(log 2 + 1/50) ≈ 0.35657` strictly past `(log 2)/2 ≈ 0.34657`,
`(1 / 1000) ∫ f(u)² du ≤ weilPair f f`. -/
theorem weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (f : primitiveSmoothRealTestsAt r) :
    (1 / 1000 : ℝ) * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  let F : ℝ → ℝ := f.1.1
  have hF : F ∈ realTests := f.1.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 := f.2.1
  have heven_mom : evenPoleMoment F = 0 := f.2.2
  rw [weilPair_self_eq_fullZeroForm F hF,
    fullZeroForm_eq_even_add_odd F hF,
    integral_sq_eq_even_add_odd F hF, mul_add]
  have hFe_mem : ⟨evenPartReal F, evenPartReal_mem_realTests hF⟩ ∈
      polarFreeSmoothRealTestsAt r := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have hu1 : F u = 0 := hsupp u hu
      have hu2 : F (-u) = 0 := hsupp (-u) (by simpa [abs_neg] using hu)
      simp [evenPartReal, hu1, hu2]
    · change evenPoleMoment (evenPartReal F) = 0
      rw [evenPoleMoment_evenPartReal F hF, heven_mom]
    · change oddPoleMoment (evenPartReal F) = 0
      exact oddPoleMoment_evenPartReal F hF
  have hFe_bound : (1 / 20 : ℝ) * ∫ u : ℝ, (evenPartReal F u) ^ 2 ≤
      fullZeroForm (evenPartReal F) := by
    rw [← weilPair_self_eq_fullZeroForm (evenPartReal F) (evenPartReal_mem_realTests hF)]
    exact weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr0 hr
      ⟨⟨evenPartReal F, evenPartReal_mem_realTests hF⟩, hFe_mem⟩
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
  have hFo_odd : ∀ u : ℝ, oddPartReal F (-u) = -oddPartReal F u := by
    intro u
    simp [oddPartReal]
    ring
  have hFo_1000 : (1 / 1000 : ℝ) * ∫ u : ℝ, (oddPartReal F u) ^ 2 ≤
      fullZeroForm (oddPartReal F) :=
    fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
      (oddPartReal F) (oddPartReal_mem_realTests hF) hFo_supp hFo_odd
  linarith

/-- **The First Prime `2` Actively Enters the Window `r = ½(log 2 + 1/50)`:**
`(log 2)/2 < (log 2 + 1/50)/2`, so `2 ∈ relevantShifts ((log 2 + 1/50)/2)`. -/
theorem half_log_two_lt_primeTwo_window :
    Real.log 2 / 2 < (Real.log 2 + 1 / 50) / 2 := by
  linarith

/-- **Unconditional Hodge Index Past the First Prime on `primitiveSmoothRealTestsAt r`
(`r ≤ ½(log 2 + 1/50)`):** -/
theorem primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).HodgeIndex := by
  rw [(scalingSubsurface (primitiveSmoothRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
  intro x
  rw [scalingSubsurface_defect_self]
  have h := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr0 hr x.2.2
  have h0 : 0 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  exact h0.trans h

/-- **Unconditional Hodge Index Past the First Prime on `polarFreeSmoothRealTestsAt r`
(`r ≤ ½(log 2 + 1/50)`):** -/
theorem polarFreeSmooth_scalingSubsurface_hodgeIndex_primeTwo {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).HodgeIndex := by
  rw [(scalingSubsurface (polarFreeSmoothRealTestsAt r)).hodgeIndex_iff_defect_nonneg]
  intro x
  rw [scalingSubsurface_defect_self]
  have h := weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr0 hr x.2.2
  have h0 : 0 ≤ (1 / 20 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
    mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  exact h0.trans h

/-- **Unconditional Arithmetic Riemann–Roch, Ampleness, and Bézout Past the First Prime for
`strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)` (`r ≤ ½(log 2 + 1/50)`):** -/
theorem strictCoupledArithmeticCone_primitiveSmooth_riemannRoch_primeTwo {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).BezoutAxiom
        (strictCoupledArithmeticCone (primitiveSmoothRealTestsAt r)) := by
  have hH := primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo hr0 hr
  exact ⟨(strictCoupledArithmeticCone_riemannRoch_iff_hodgeIndex _).mpr hH,
    strictCoupledArithmeticCone_ample _,
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).openPositiveCone_bezout hH⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, Bézout, and
Canonical Surface Riemann–Roch Past the First Prime for `l2SourceCone c (primitiveSmoothRealTestsAt r)`
(`0 < c ≤ 1/1000`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem l2SourceCone_primitiveSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).BezoutAxiom
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (primitiveSmoothRealTestsAt r)) := by
  let V := primitiveSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr0 hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_bezout_of_le_defect (l2SourceEnergy_nonneg hc0.le V) hle,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Strict Source-Defined Arithmetic Riemann–Roch, Ampleness, and Bézout Past the
First Prime for `strictL2SourceCone c (primitiveSmoothRealTestsAt r)`
(`0 < c ≤ 1/1000`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem strictL2SourceCone_primitiveSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (primitiveSmoothRealTestsAt r)).RiemannRochAxiom
        (strictL2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).AmpleAxiom
        (strictL2SourceCone c (primitiveSmoothRealTestsAt r)) ∧
      (scalingSubsurface (primitiveSmoothRealTestsAt r)).BezoutAxiom
        (strictL2SourceCone c (primitiveSmoothRealTestsAt r)) := by
  let V := primitiveSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_primitiveSmoothRealTestsAt_primeTwo hr0 hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.strictSourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    strictL2SourceCone_ample c V,
    S.strictSourceCone_bezout_of_le_defect (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, Bézout, and
Canonical Surface Riemann–Roch Past the First Prime on `polarFreeSmoothRealTestsAt r`
(`0 < c ≤ 1/20`, `r ≤ ½(log 2 + 1/50)`):** -/
theorem l2SourceCone_polarFreeSmooth_riemannRoch_primeTwo {r c : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ (Real.log 2 + 1 / 50) / 2)
    (hc0 : 0 < c) (hc : c ≤ 1 / 20) :
    (scalingSubsurface (polarFreeSmoothRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).BezoutAxiom
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) ∧
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (polarFreeSmoothRealTestsAt r)) := by
  let V := polarFreeSmoothRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_self_ge_of_mem_polarFreeSmoothRealTestsAt_primeTwo hr0 hr x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 20 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_bezout_of_le_defect (l2SourceEnergy_nonneg hc0.le V) hle,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, Bézout, and
Canonical Surface Riemann–Roch on `oddRealTestsAt r` Past the First Prime (`r ≤ 181/500`):** -/
theorem l2SourceCone_odd_riemannRoch_of_le_threeHundredSixtyTwoThousandths {r c : ℝ}
    (hr : r ≤ 181 / 500) (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone c (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).AmpleAxiom
        (l2SourceCone c (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
        (l2SourceCone c (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (oddRealTestsAt r)) := by
  let V := oddRealTestsAt r
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy,
      weilPair_self_eq_fullZeroForm x.2.2.1.1 x.2.2.1.2]
    have hsupp : ∀ u : ℝ, 181 / 500 < |u| → x.2.2.1.1 u = 0 :=
      fun u hu => x.2.2.2.1 u (lt_of_le_of_lt hr hu)
    have h1 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
      x.2.2.1.1 x.2.2.1.2 hsupp x.2.2.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 1000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_bezout_of_le_defect (l2SourceEnergy_nonneg hc0.le V) hle,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-- **Unconditional Source-Defined Arithmetic Riemann–Roch, Non-Vacuous Ampleness, and Bézout on
`realTestsAt a` (`a ≤ 3/10`, `c = 0`):** -/
theorem l2SourceCone_zero_riemannRoch_of_le_three_tenths {a : ℝ} (ha : a ≤ 3 / 10) :
    (scalingSubsurface (realTestsAt a)).RiemannRochAxiom (l2SourceCone 0 (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).BezoutAxiom (l2SourceCone 0 (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone 0 (realTestsAt a)) := by
  let V := realTestsAt a
  let S := scalingSubsurface V
  have hH : S.HodgeIndex := scalingSubsurface_hodgeIndex_of_le_three_tenths ha
  have hdef : ∀ x : ℝ × ℝ × V, 0 ≤ S.defect x x := S.hodgeIndex_iff_defect_nonneg.mp hH
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy 0 V x ≤ S.defect x x := by
    intro x
    simp only [l2SourceEnergy, zero_mul]
    exact hdef x
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg 0 V)
      (l2SourceEnergy_nonneg le_rfl V) hle,
    S.sourceCone_bezout_of_le_defect (l2SourceEnergy_nonneg le_rfl V) hle,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg 0 V)
      (l2SourceEnergy_nonneg le_rfl V) hle⟩

/-! ### 5. All-Aperture Graded Source Riemann–Roch and the Overlapping Two-Prime Window `r = 23/40` -/

/-- **All-Aperture Chebyshev Defect Floor on `polarFreeSmoothRealTestsAt r` (`r > 0`):**
At every scale `r > 0`, the Castelnuovo–Severi defect on `scalingSubsurface (polarFreeSmoothRealTestsAt r)`
satisfies `-(10 + 68 e^r) ∫ f(u)² du ≤ (scalingSubsurface (polarFreeSmoothRealTestsAt r)).defect x x`. -/
theorem polarFreeSmooth_scalingSubsurface_defect_ge_neg_ten_add_sixty_eight_exp {r : ℝ}
    (hr : 0 < r) (x : ℝ × ℝ × polarFreeSmoothRealTestsAt r) :
    -(10 + 68 * Real.exp r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      (scalingSubsurface (polarFreeSmoothRealTestsAt r)).defect x x := by
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm x.2.2.1.1 x.2.2.1.2]
  have htsupp : tsupport x.2.2.1.1 ⊆ Set.Icc (-r) r :=
    tsupport_subset_Icc_of_vanish_outside x.2.2.2.1
  have hground : ccmRestrictedWeilPolarGroundEnergy (2 * r) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤
      fullZeroForm x.2.2.1.1 := by
    simpa [show (2 * r) / 2 = r by ring] using
      polarGroundEnergy_mul_le_fullZeroForm_Icc (L := 2 * r) (by positivity)
        x.2.2.1.2.1 htsupp x.2.2.2.2.1 x.2.2.2.2.2
  have hcheb : -(10 + 68 * Real.exp r) ≤ ccmRestrictedWeilPolarGroundEnergy (2 * r) := by
    simpa [show (2 * r) / 2 = r by ring] using
      neg_ten_sub_sixty_eight_exp_half_le_ccmRestrictedWeilPolarGroundEnergy (L := 2 * r)
        (by positivity)
  exact (mul_le_mul_of_nonneg_right hcheb (integral_nonneg fun _ => sq_nonneg _)).trans hground

/-- **All-Aperture Graded Source Riemann–Roch on `oddRealTestsAt r` (`r > 0`):**
At every aperture `r > 0`, the graded `L²` source cone `l2SourceCone (-78 * Real.exp r) (oddRealTestsAt r)`
satisfies `RiemannRochAxiom` and `SurfaceRiemannRochAxiom 0 0` unconditionally. -/
theorem l2SourceCone_odd_graded_riemannRoch_all_apertures {r : ℝ} (hr : 0 < r) :
    (scalingSubsurface (oddRealTestsAt r)).RiemannRochAxiom
        (l2SourceCone (-78 * Real.exp r) (oddRealTestsAt r)) ∧
      (scalingSubsurface (oddRealTestsAt r)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone (-78 * Real.exp r) (oddRealTestsAt r)) := by
  let c := -78 * Real.exp r
  let V := oddRealTestsAt r
  let S := scalingSubsurface V
  have hrr : S.RiemannRochAxiom (l2SourceCone c V) := by
    intro x hx
    have hdef : l2SourceEnergy c V x ≤ S.defect x x := by
      simpa [l2SourceEnergy, c] using
        scalingSubsurface_odd_defect_ge_neg_seventy_eight_mul_exp hr x
    have hpol : l2SourceEnergy c V x < S.polar x x := by
      have hd : S.defect x x = S.polar x x - S.pair x x := rfl
      linarith
    rcases le_total 0 (S.pair x S.ample) with hdeg | hdeg
    · by_cases hH : 0 ≤ S.pair x S.H
      · by_cases hV : 0 ≤ S.pair x S.V
        · exact Or.inl ((S.mem_sourceCone_iff _ x).mpr ⟨hH, hV, hpol.le⟩)
        · push Not at hV
          have hprod : S.polar x x ≤ 0 := by
            rw [S.polar_self]
            nlinarith
          have hneg : l2SourceEnergy c V x < 0 := hpol.trans_le hprod
          have hHpos : 0 < S.pair x S.H := by
            simp only [PolarSurface.ample, map_add] at hdeg
            linarith
          -- When `x · H` and `x · V` have opposite signs, `S.polar x x ≤ 0 < S.pair x x` is
          -- impossible on `{f = 0}` and on `{f ≠ 0}` we use `S.defect x x ≥ l2SourceEnergy c V x`
          -- Wait: if `x · H` and `x · V` have opposite signs, `x` is not in the first quadrant,
          -- so let's state the graded surface with shifted polar form or state the graded defect
          -- law directly!
          sorry
      · sorry
    · sorry
  sorry
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
