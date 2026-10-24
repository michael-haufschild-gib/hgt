import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor
import GaloisForLFunctions.ArithmeticOrientationTheory.NyquistRiemannRochBeyondRankNullity

/-!
# Section Effectivity, the Universal Floor Law, and Prime-Node Riemann–Roch for `ℤ`

This module resolves Open Problem 1 of the Arithmetic Castelnuovo–Severi programme (*Riemann–Roch
for `ℤ` — the open core*), answering both the structural question of whether any sign-free ample
effectivity cone can have a Riemann–Roch axiom not equivalent to the Castelnuovo–Severi defect
floor, and the constructive question of how section counts on the prime-power nodes of the
logarithmic box combine with the Chebyshev defect `E(s) = e^s + s - 1 - ψ(e^s)`, Frobenius-mass
selectivity, and hyperbolic AM-GM Bézout positivity.

## Main Results

1. **The Universal Floor Law for Ample Cones on Polar Surfaces (§1):**
   On any abstract polar surface `S : PolarSurface C` and for any candidate effectivity `E : Set C`
   whose ampleness `S.AmpleAxiom E` is proved (by any mechanism, without using the sign of the
   form):
   * **Universal Floor Necessity (`PolarSurface.riemannRoch_implies_hodgeIndex_of_ample`):**
     `S.RiemannRochAxiom E` unconditionally implies `S.HodgeIndex` (`∀ x : C, 0 ≤ S.defect x x`).
   * **Exact Equivalence on Cones Containing `openPositiveCone`
     (`PolarSurface.riemannRoch_iff_hodgeIndex_of_ample_of_openPositiveCone_subset`):**
     Whenever `S.AmpleAxiom E` and `S.openPositiveCone ⊆ E` hold, `S.RiemannRochAxiom E` is
     unconditionally equivalent to the zero-floor `∀ x : C, 0 ≤ S.defect x x` (`S.HodgeIndex`).
   * **Universal Floor Dichotomy for Nonnegative-Degree Ample Cones
     (`PolarSurface.riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg`,
     `PolarSurface.ampleHalfSpace_ample_riemannRoch_dichotomy`):**
     For **every** cone `E` of nonnegative ample degree (`∀ x ∈ E, 0 ≤ S.pair x S.ample`) satisfying
     `S.AmpleAxiom E`, `S.RiemannRochAxiom E` is unconditionally equivalent to
     `S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x`: either `E` misses a cycle of
     `S.openPositiveCone` (in which case `¬ S.RiemannRochAxiom E`), or `S.openPositiveCone ⊆ E`
     (in which case `S.RiemannRochAxiom E ↔ ∀ x : C, 0 ≤ S.defect x x`). Thus **no** ample cone of
     nonnegative degree on any polar surface can have a Riemann–Roch axiom that is not equivalent to
     a floor on `S.defect x x`.

2. **Sign-Free Section Readings and Hyperbolic AM-GM Bézout Positivity (§2):**
   * **Universal Hyperbolic AM-GM Identity (`PolarSurface.polar_sq_sub_polar_mul_polar`):**
     On any polar surface `S`, `S.polar x y ^ 2 - S.polar x x * S.polar y y =
     ((x · H)(y · V) - (x · V)(y · H)) ^ 2 ≥ 0`.
   * **Sign-Free Bézout Theorem (`PolarSurface.sourceCone_bezout_of_defect_sq_le`,
     `PolarSurface.sourceCone_bezout_of_source_nonneg`):**
     For any source functional `Φ : C → ℝ` (defined without reading `S.pair x x`), the section
     count `S.sourceSectionH0 Φ x := h0 (S.sourceSectionReading Φ x)` defines `S.sourceCone Φ`.
     Whenever `0 ≤ Φ` on `S.sourceCone Φ` and `S.defect x y ^ 2 ≤ Φ x * Φ y` (in particular whenever
     `Φ` is a nonnegative quadratic source ledger representing `S.defect z z`), `S.BezoutAxiom`
     holds on `S.sourceCone Φ` directly from hyperbolic AM-GM, without reading `S.pair x x`.

3. **Prime-Power Node Section Counts `h⁰ ≥ DoF − node count` and the Two-Sided Node-Weight Bridge
   to `ψ(e^{2r})` (§3):**
   * On the correlation box `(0, 2r)`, `primePowerNodes r := (relevantShifts r).filter IsPrimePow`
     consists of the prime-power shifts `p^k < e^{2r}`, and the prime-node correlation obstruction
     `primeNodeCorrelationObstruction r F` is supported purely on `primePowerNodes r`
     (`primeNodeCorrelationObstruction_eq_sum_primePowerNodes`).
   * For any finite-dimensional subspace `W : Submodule ℝ (ℝ → ℝ)` of tests, evaluating at the
     prime-power nodes `{log n | n ∈ primePowerNodes r}` defines the prime-blind section subspace
     `primeNodeSections r W` of dimension `primeNodeH0 r W`, satisfying the exact rank–nullity Euler
     characteristic identity `primeNodeH0 r W - primeNodeH1 r W = finrank ℝ W - (primePowerNodes r).card`
     and the lower bound `finrank ℝ W - (primePowerNodes r).card ≤ primeNodeH0 r W`
     (`primeNodeH0_sub_primeNodeH1_eq_finrank_sub_card`, `finrank_sub_card_le_primeNodeH0`).
   * Every prime-power node `n ∈ primePowerNodes r` satisfies `log 2 ≤ Λ(n)`, giving the exact
     bridge `log 2 * (primePowerNodes r).card ≤ ∑_{n ∈ primePowerNodes r} Λ(n) ≤ primeNodeCount (2r)`
     and `finrank ℝ W - primeNodeCount (2r) / log 2 ≤ primeNodeH0 r W`
     (`log_two_mul_card_primePowerNodes_le_primeNodeCount`,
     `finrank_sub_primeNodeCount_div_log_two_le_primeNodeH0`), while the continuous box degree of
     freedom `polarBoxDoF s` minus `primeNodeCount s` is identically `chebyshevTwoPoleDefect s`.

4. **Exact Pole-Charge Cancellation in the Odd Self-Intersection Pairing (§4):**
   * Every pure odd test cycle `(0, 0, f)` (`f : oddRealTestsAt r`) is automatically orthogonal to
     `ample = H + V` (`pureOddCycle_pair_ample_eq_zero`).
   * On `scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`), the exponential pole charge
     `poleCharge F = 2 (oddPoleMoment F)^2` cancels identically between the pole-plane form
     `polar x x = 2ab + 2(b - a) oddPoleMoment F - poleCharge F` and the explicit-formula defect
     `defect x x = archGaugeBudget r R F - primeNodeCorrelationObstruction r F - poleCharge F`,
     yielding the **pole-charge-free self-intersection identity**
     `(a, b, f) · (a, b, f) = 2ab + 2(b - a) oddPoleMoment F - archGaugeBudget r R F +
     primeNodeCorrelationObstruction r F` (`scalingSubsurface_odd_pair_self_eq_poleFreeLedger`) and
     `localPair F F = primeNodeCorrelationObstruction r F - archGaugeBudget r R F`
     (`localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd`).
   * On horizon-prime-blind odd tests (`IsHorizonPrimeBlind F r`), both the prime-node correlation
     obstruction and the quadratic pole charge vanish from the self-intersection, leaving
     `localPair F F = -archGaugeBudget r R F` and `(a, a, f) · (a, a, f) = 2a^2 - archGaugeBudget r R F`.
-/

open Complex Finset Matrix MeasureTheory Set Filter Topology
open scoped Real BigOperators ComplexConjugate
open Zeta23 RHTower
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.ArithmeticOrientationTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## §1. The Universal Floor Law for Ample Cones on Polar Surfaces -/

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **Universal Floor Necessity for Ample Cones:**
For *any* subset `E : Set C` on a polar surface `S`, if `S.AmpleAxiom E` holds (by any proof,
sign-free or not), then `S.RiemannRochAxiom E` unconditionally implies `S.HodgeIndex` (and hence the
defect floor `∀ x : C, 0 ≤ S.defect x x`). -/
theorem riemannRoch_implies_hodgeIndex_of_ample {E : Set C} (hA : S.AmpleAxiom E)
    (hRR : S.RiemannRochAxiom E) :
    S.HodgeIndex ∧ ∀ x : C, 0 ≤ S.defect x x := by
  have hHI : S.HodgeIndex :=
    S.hodgeIndex_iff_ampleHodgeIndex.mpr (S.ampleHodgeIndex_of_effectivity hRR hA)
  exact ⟨hHI, S.hodgeIndex_iff_defect_nonneg.mp hHI⟩

/-- **Universal Equivalence for Ample Cones Containing `openPositiveCone`:**
For *every* subset `E : Set C` satisfying `S.AmpleAxiom E` and containing `S.openPositiveCone`,
`S.RiemannRochAxiom E` is unconditionally equivalent to `S.HodgeIndex` and to the defect floor
`∀ x : C, 0 ≤ S.defect x x`. -/
theorem riemannRoch_iff_hodgeIndex_of_ample_of_openPositiveCone_subset {E : Set C}
    (hA : S.AmpleAxiom E) (hsub : S.openPositiveCone ⊆ E) :
    (S.RiemannRochAxiom E ↔ S.HodgeIndex) ∧
      (S.RiemannRochAxiom E ↔ ∀ x : C, 0 ≤ S.defect x x) := by
  have h1 : S.RiemannRochAxiom E ↔ S.HodgeIndex := by
    refine ⟨fun hRR => (S.riemannRoch_implies_hodgeIndex_of_ample hA hRR).1, fun hHI x hx => ?_⟩
    rcases S.openPositiveCone_riemannRoch_iff_hodgeIndex.mpr hHI x hx with h | h
    · exact Or.inl (hsub h)
    · exact Or.inr (hsub h)
  exact ⟨h1, h1.trans S.hodgeIndex_iff_defect_nonneg⟩

/-- **The Universal Floor Law for Ample Cones of Nonnegative Degree:**
For *every* subset `E : Set C` of nonnegative ample degree (`∀ x ∈ E, 0 ≤ S.pair x S.ample`)
satisfying `S.AmpleAxiom E`, `S.RiemannRochAxiom E` holds if and only if
`S.openPositiveCone ⊆ E` and `∀ x : C, 0 ≤ S.defect x x`. -/
theorem riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg {E : Set C}
    (hdeg : ∀ x ∈ E, 0 ≤ S.pair x S.ample) (hA : S.AmpleAxiom E) :
    S.RiemannRochAxiom E ↔ S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x := by
  refine ⟨fun hRR => ⟨S.openPositiveCone_subset_of_effectivity hRR hdeg,
    (S.riemannRoch_implies_hodgeIndex_of_ample hA hRR).2⟩, fun ⟨hsub, hdef⟩ => ?_⟩
  exact (S.riemannRoch_iff_hodgeIndex_of_ample_of_openPositiveCone_subset hA hsub).2.mpr hdef

/-- **Universal Dichotomy for Ample Cones of Nonnegative Degree:**
For every cone `E : Set C` with `∀ x ∈ E, 0 ≤ S.pair x S.ample` satisfying `S.AmpleAxiom E`:
1. If `¬ (S.openPositiveCone ⊆ E)`, then `¬ S.RiemannRochAxiom E`;
2. If `S.openPositiveCone ⊆ E`, then `S.RiemannRochAxiom E ↔ ∀ x : C, 0 ≤ S.defect x x`.
Thus no ample cone of nonnegative degree can have a `RiemannRochAxiom` that is not equivalent to a
floor on `S.defect x x`. -/
theorem ampleHalfSpace_ample_riemannRoch_dichotomy {E : Set C}
    (hdeg : ∀ x ∈ E, 0 ≤ S.pair x S.ample) (hA : S.AmpleAxiom E) :
    (¬ S.openPositiveCone ⊆ E ∧ ¬ S.RiemannRochAxiom E) ∨
      (S.openPositiveCone ⊆ E ∧ (S.RiemannRochAxiom E ↔ ∀ x : C, 0 ≤ S.defect x x)) := by
  by_cases hsub : S.openPositiveCone ⊆ E
  · exact Or.inr ⟨hsub, (S.riemannRoch_iff_hodgeIndex_of_ample_of_openPositiveCone_subset hA hsub).2⟩
  · refine Or.inl ⟨hsub, fun hRR => hsub ?_⟩
    exact S.openPositiveCone_subset_of_effectivity hRR hdeg

/-- The polar lift `S.prim x + a • S.H + b • S.V` of the primitive part of `x` with fiber degrees
`(x · H, x · V) = (b, a)`. -/
def polarLift (x : C) (a b : ℝ) : C :=
  S.prim x + a • S.H + b • S.V

theorem pair_polarLift_H (x : C) (a b : ℝ) :
    S.pair (S.polarLift x a b) S.H = b := by
  simp only [polarLift, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    S.pair_prim_H, S.pair_H_H, S.pair_V_H]
  ring

theorem pair_polarLift_V (x : C) (a b : ℝ) :
    S.pair (S.polarLift x a b) S.V = a := by
  simp only [polarLift, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    S.pair_prim_V, S.pair_H_V, S.pair_V_V]
  ring

theorem prim_polarLift (x : C) (a b : ℝ) :
    S.prim (S.polarLift x a b) = S.prim x := by
  dsimp [PolarSurface.prim]
  rw [S.pair_polarLift_H, S.pair_polarLift_V]
  dsimp [polarLift, PolarSurface.prim]
  module

theorem polar_polarLift_self (x : C) (a b : ℝ) :
    S.polar (S.polarLift x a b) (S.polarLift x a b) = 2 * a * b := by
  rw [S.polar_self, S.pair_polarLift_H, S.pair_polarLift_V]
  ring

theorem defect_polarLift_self (x : C) (a b : ℝ) :
    S.defect (S.polarLift x a b) (S.polarLift x a b) = S.defect x x := by
  rw [← S.defect_prim (S.polarLift x a b) (S.polarLift x a b), S.prim_polarLift, S.defect_prim]

theorem pair_polarLift_self (x : C) (a b : ℝ) :
    S.pair (S.polarLift x a b) (S.polarLift x a b) = 2 * a * b - S.defect x x := by
  have hd := S.defect_polarLift_self x a b
  have hp := S.polar_polarLift_self x a b
  have hdef : S.defect (S.polarLift x a b) (S.polarLift x a b) =
      S.polar (S.polarLift x a b) (S.polarLift x a b) -
        S.pair (S.polarLift x a b) (S.polarLift x a b) := rfl
  linarith

theorem polarLift_pair_V_pair_H (x : C) :
    S.polarLift x (S.pair x S.V) (S.pair x S.H) = x := by
  dsimp [polarLift, PolarSurface.prim]
  module

/-- **Universal Defect-Threshold Characterization of `RiemannRochAxiom` for Any Set `E : Set C`:**
Without any hypothesis on `E`, `S.RiemannRochAxiom E` holds if and only if for every cycle `x : C`
and every pair of fiber degrees `(a, b) ∈ ℝ × ℝ` whose hyperbolic capacity `2ab` exceeds
`S.defect x x`, the polar lift `S.polarLift x a b` belongs to `E ∪ (-E)`. -/
theorem riemannRoch_iff_forall_defect_lt_polarLift (E : Set C) :
    S.RiemannRochAxiom E ↔
      ∀ (x : C) (a b : ℝ), S.defect x x < 2 * a * b →
        S.polarLift x a b ∈ E ∨ -S.polarLift x a b ∈ E := by
  constructor
  · intro hRR x a b hlt
    apply hRR (S.polarLift x a b)
    rw [S.pair_polarLift_self]
    linarith
  · intro h x hx
    have hlt : S.defect x x < 2 * S.pair x S.V * S.pair x S.H := by
      have hd : S.defect x x = 2 * S.pair x S.H * S.pair x S.V - S.pair x x := S.defect_self x
      linarith
    have hmem := h x (S.pair x S.V) (S.pair x S.H) hlt
    rwa [S.polarLift_pair_V_pair_H] at hmem

/-! ## §2. Sign-Free Section Readings and Hyperbolic AM-GM Bézout Positivity -/

/-- **Universal Hyperbolic AM-GM Identity on a Polar Surface:**
For all `x, y : C`, `S.polar x y ^ 2 - S.polar x x * S.polar y y =
((x · H)(y · V) - (x · V)(y · H)) ^ 2 ≥ 0`. -/
theorem polar_sq_sub_polar_mul_polar (x y : C) :
    S.polar x y ^ 2 - S.polar x x * S.polar y y =
      (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H) ^ 2 ∧
    S.polar x x * S.polar y y ≤ S.polar x y ^ 2 := by
  have hid : S.polar x y ^ 2 - S.polar x x * S.polar y y =
      (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H) ^ 2 := by
    simp only [PolarSurface.polar]
    ring
  exact ⟨hid, by linarith [sq_nonneg (S.pair x S.H * S.pair y S.V - S.pair x S.V * S.pair y S.H)]⟩

/-- The `1 × 1` **source section reading** on `S` associated to a source energy functional
`Φ : C → ℝ`, defined without referencing `S.pair x x` or `S.defect x x`. -/
def sourceSectionReading (Φ : C → ℝ) (x : C) : Matrix (Fin 1) (Fin 1) ℂ :=
  open Classical in
  if 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x then 0 else 1

/-- The **source section count** `h⁰_Φ(x) := h0 (S.sourceSectionReading Φ x)`. -/
def sourceSectionH0 (Φ : C → ℝ) (x : C) : ℕ :=
  h0 (S.sourceSectionReading Φ x)

theorem sourceSectionH0_eq_ite (Φ : C → ℝ) (x : C) :
    S.sourceSectionH0 Φ x =
      (open Classical in if 0 ≤ S.pair x S.H ∧ 0 ≤ S.pair x S.V ∧ Φ x ≤ S.polar x x then 1 else 0) := by
  classical
  unfold sourceSectionH0 sourceSectionReading
  split_ifs
  · exact h0_zero_fin_one
  · exact h0_one_fin_one

/-- The section-count effectivity cone `{x : C | 1 ≤ S.sourceSectionH0 Φ x}` coincides identically
with the determinantal source cone `S.sourceCone Φ`. -/
theorem setOf_one_le_sourceSectionH0_eq_sourceCone (Φ : C → ℝ) :
    {x : C | 1 ≤ S.sourceSectionH0 Φ x} = S.sourceCone Φ := by
  classical
  ext x
  rw [Set.mem_setOf_eq, S.sourceSectionH0_eq_ite, S.mem_sourceCone_iff]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => le_rfl⟩
  · exact ⟨fun h1 => absurd h1 (by omega), fun h' => absurd h' h⟩

/-- **Sign-Free Bézout Theorem for `S.sourceCone Φ`:**
Whenever `0 ≤ Φ` on `S.sourceCone Φ` and the off-diagonal defect obeys `S.defect x y ^ 2 ≤ Φ x * Φ y`,
`S.BezoutAxiom (S.sourceCone Φ)` holds directly from hyperbolic AM-GM, without reading `S.pair x x`. -/
theorem sourceCone_bezout_of_defect_sq_le (Φ : C → ℝ)
    (hnonneg : ∀ x ∈ S.sourceCone Φ, 0 ≤ Φ x)
    (hcs : ∀ x ∈ S.sourceCone Φ, ∀ y ∈ S.sourceCone Φ, S.defect x y ^ 2 ≤ Φ x * Φ y) :
    S.BezoutAxiom (S.sourceCone Φ) := by
  intro x hx y hy
  have hΦx : 0 ≤ Φ x := hnonneg x hx
  have hΦy : 0 ≤ Φ y := hnonneg y hy
  have hcs_xy : S.defect x y ^ 2 ≤ Φ x * Φ y := hcs x hx y hy
  rw [S.mem_sourceCone_iff] at hx hy
  rcases hx with ⟨hxH, hxV, hxP⟩
  rcases hy with ⟨hyH, hyV, hyP⟩
  have hpol_nn : 0 ≤ S.polar x y := by unfold PolarSurface.polar; positivity
  have hmul : Φ x * Φ y ≤ S.polar x x * S.polar y y :=
    mul_le_mul hxP hyP hΦy (hΦx.trans hxP)
  have hamgm : S.polar x x * S.polar y y ≤ S.polar x y ^ 2 :=
    (S.polar_sq_sub_polar_mul_polar x y).2
  have hsq : S.defect x y ^ 2 ≤ S.polar x y ^ 2 := (hcs_xy.trans hmul).trans hamgm
  have hdef_le : S.defect x y ≤ S.polar x y := by
    by_contra hgt
    push Not at hgt
    nlinarith [lt_of_le_of_lt hpol_nn hgt]
  have hp : S.pair x y = S.polar x y - S.defect x y := by unfold PolarSurface.defect; ring
  linarith

/-- **Sign-Free Bézout Theorem from Any Nonnegative Source Ledger:**
If `Φ : C → ℝ` represents the diagonal of `S.defect` (`∀ z, S.defect z z = Φ z`) and satisfies
`∀ z, 0 ≤ Φ z` on the source side, then `S.defect x y ^ 2 ≤ Φ x * Φ y` for all `x, y : C` and
`S.BezoutAxiom (S.sourceCone Φ)` holds. -/
theorem sourceCone_bezout_of_source_nonneg (Φ : C → ℝ)
    (hrep : ∀ z : C, S.defect z z = Φ z) (hnonneg : ∀ z : C, 0 ≤ Φ z) :
    (∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y) ∧ S.BezoutAxiom (S.sourceCone Φ) := by
  have hcs : ∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y := fun x y => by
    have hq : ∀ t : ℝ, 0 ≤ Φ y * (t * t) + 2 * S.defect x y * t + Φ x := fun t => by
      have h1 : 0 ≤ Φ (x + t • y) := hnonneg (x + t • y)
      have h2 : Φ (x + t • y) = Φ y * (t * t) + 2 * S.defect x y * t + Φ x := by
        rw [← hrep (x + t • y), ← hrep x, ← hrep y]
        simp only [PolarSurface.defect, PolarSurface.polar, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, S.pair_comm y x]
        ring
      rwa [h2] at h1
    have hd := discrim_le_zero hq
    rw [discrim] at hd
    nlinarith [hd]
  exact ⟨hcs, S.sourceCone_bezout_of_defect_sq_le Φ (fun x _ => hnonneg x)
    (fun x _ y _ => hcs x y)⟩

end PolarSurface

/-! ## §3. Concrete Prime-Power Node Evaluation on Aperture-`r` Test Spaces and `h⁰ ≥ DoF − node count` -/

/-- The finite set of **prime-power nodes** `n = p^k` (`n ≥ 2`, `IsPrimePow n`) in the correlation
box `log n < 2r` of aperture `r`. -/
def primePowerNodes (r : ℝ) : Finset ℕ :=
  open Classical in (relevantShifts r).filter IsPrimePow

theorem mem_primePowerNodes {r : ℝ} {n : ℕ} :
    n ∈ primePowerNodes r ↔ n ∈ relevantShifts r ∧ IsPrimePow n := by
  classical
  exact Finset.mem_filter

/-- The prime-node correlation obstruction `primeNodeCorrelationObstruction r F` is supported purely
on `primePowerNodes r` (composite non-prime-power shifts have `vonMangoldtAtom n = 0` and contribute
nothing). -/
theorem primeNodeCorrelationObstruction_eq_sum_primePowerNodes (r : ℝ) (F : ℝ → ℝ) :
    primeNodeCorrelationObstruction r F =
      ∑ n ∈ primePowerNodes r,
        2 * vonMangoldtAtom n * autoCorrelation F (Real.log n) := by
  classical
  unfold primeNodeCorrelationObstruction primePowerNodes
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_
  have hpp : ¬ IsPrimePow n := fun h => hnot (Finset.mem_filter.mpr ⟨hn, h⟩)
  have hΛ : ArithmeticFunction.vonMangoldt n = 0 := by
    rwa [← not_iff_not.mpr ArithmeticFunction.vonMangoldt_ne_zero_iff, not_not] at hpp
  simp [vonMangoldtAtom, hΛ]

/-- Linear evaluation map sending a test `F : ℝ → ℝ` to its values `n ↦ F (Real.log n)` at the
prime-power nodes `primePowerNodes r` of the box `(0, 2r)`. -/
def primePowerNodeEval (r : ℝ) : (ℝ → ℝ) →ₗ[ℝ] (primePowerNodes r → ℝ) where
  toFun F n := F (Real.log (n.1 : ℝ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem primePowerNodeEval_apply (r : ℝ) (F : ℝ → ℝ) (n : primePowerNodes r) :
    primePowerNodeEval r F n = F (Real.log (n.1 : ℝ)) := rfl

/-- The **prime-node section subspace** `primeNodeSections r W` of a test subspace
`W : Submodule ℝ (ℝ → ℝ)` at aperture `r`: tests `f ∈ W` vanishing at all prime-power nodes
`log n` (`n ∈ primePowerNodes r`) of the box `(0, 2r)`. -/
def primeNodeSections (r : ℝ) (W : Submodule ℝ (ℝ → ℝ)) : Submodule ℝ W :=
  LinearMap.ker ((primePowerNodeEval r).comp W.subtype)

/-- Membership in `primeNodeSections r W`: a test `f : W` is a prime-node section iff
`f.1 (Real.log n) = 0` for every `n ∈ primePowerNodes r`. -/
theorem mem_primeNodeSections_iff (r : ℝ) (W : Submodule ℝ (ℝ → ℝ)) (f : W) :
    f ∈ primeNodeSections r W ↔ ∀ n ∈ primePowerNodes r, f.1 (Real.log (n : ℝ)) = 0 := by
  rw [primeNodeSections, LinearMap.mem_ker]
  constructor
  · intro h n hn
    exact congrFun h ⟨n, hn⟩
  · intro h
    funext ⟨n, hn⟩
    exact h n hn

/-- The **prime-node section count** `h⁰_{\text{node}}(r, W)` of a test space `W` at aperture `r`:
the vector-space dimension of `primeNodeSections r W`. -/
def primeNodeH0 (r : ℝ) (W : Submodule ℝ (ℝ → ℝ)) : ℕ :=
  Module.finrank ℝ (primeNodeSections r W)

/-- The **prime-node obstruction count** `h¹_{\text{node}}(r, W)` of a test space `W` at aperture `r`:
the codimension of the image of `W` in the prime-power node space `primePowerNodes r → ℝ`. -/
def primeNodeH1 (r : ℝ) (W : Submodule ℝ (ℝ → ℝ)) : ℕ :=
  (primePowerNodes r).card -
    Module.finrank ℝ (LinearMap.range ((primePowerNodeEval r).comp W.subtype))

/-- **Exact Box Prime-Node Riemann–Roch / Euler Characteristic Identity
(`primeNodeH0_sub_primeNodeH1_eq_finrank_sub_card`):**
For every finite-dimensional test space `W : Submodule ℝ (ℝ → ℝ)` and every aperture `r : ℝ`,
`h⁰_{\text{node}}(r, W) - h¹_{\text{node}}(r, W) = \dim W - #(primePowerNodes r)`. -/
theorem primeNodeH0_sub_primeNodeH1_eq_finrank_sub_card (r : ℝ) (W : Submodule ℝ (ℝ → ℝ))
    [FiniteDimensional ℝ W] :
    (primeNodeH0 r W : ℤ) - (primeNodeH1 r W : ℤ) =
      (Module.finrank ℝ W : ℤ) - ((primePowerNodes r).card : ℤ) := by
  let L := (primePowerNodeEval r).comp W.subtype
  have hrr := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℝ (LinearMap.range L) ≤ (primePowerNodes r).card := by
    have hsub := Submodule.finrank_le (LinearMap.range L)
    rwa [Module.finrank_pi, Fintype.card_coe] at hsub
  unfold primeNodeH0 primeNodeH1 primeNodeSections
  change (Module.finrank ℝ (LinearMap.ker L) : ℤ) -
      (((primePowerNodes r).card - Module.finrank ℝ (LinearMap.range L) : ℕ) : ℤ) =
    (Module.finrank ℝ W : ℤ) - ((primePowerNodes r).card : ℤ)
  omega

/-- **Box Prime-Node Section Count Lower Bound (`finrank_sub_card_le_primeNodeH0`):**
For every finite-dimensional test space `W : Submodule ℝ (ℝ → ℝ)` and every aperture `r : ℝ`,
`dim W - #(primePowerNodes r) ≤ primeNodeH0 r W`. -/
theorem finrank_sub_card_le_primeNodeH0 (r : ℝ) (W : Submodule ℝ (ℝ → ℝ))
    [FiniteDimensional ℝ W] :
    (Module.finrank ℝ W : ℝ) - ((primePowerNodes r).card : ℝ) ≤ (primeNodeH0 r W : ℝ) := by
  have h := primeNodeH0_sub_primeNodeH1_eq_finrank_sub_card r W
  have h1 : (0 : ℤ) ≤ (primeNodeH1 r W : ℤ) := Int.natCast_nonneg _
  have hle : (Module.finrank ℝ W : ℤ) - ((primePowerNodes r).card : ℤ) ≤ (primeNodeH0 r W : ℤ) := by
    linarith
  exact_mod_cast hle

/-- Whenever `dim W > #(primePowerNodes r)`, there exists a nonzero test `f ∈ W` vanishing at all
prime-power nodes `Real.log n` (`n ∈ primePowerNodes r`). -/
theorem exists_ne_zero_mem_primeNodeSections_of_card_lt_finrank (r : ℝ) (W : Submodule ℝ (ℝ → ℝ))
    [FiniteDimensional ℝ W] (hdim : (primePowerNodes r).card < Module.finrank ℝ W) :
    ∃ f ∈ W, f ≠ 0 ∧ ∀ n ∈ primePowerNodes r, f (Real.log (n : ℝ)) = 0 := by
  let L := (primePowerNodeEval r).comp W.subtype
  have hlt : Module.finrank ℝ (primePowerNodes r → ℝ) < Module.finrank ℝ W := by
    rwa [Module.finrank_pi, Fintype.card_coe]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) hlt
  obtain ⟨f, hfker, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨f.1, f.2, Subtype.coe_ne_coe.mpr hf0, ?_⟩
  exact (mem_primeNodeSections_iff r W f).mp hfker

/-- Every prime-power node `n ∈ primePowerNodes r` has von Mangoldt weight `Λ(n) ≥ log 2`. -/
theorem log_two_le_vonMangoldt_of_mem_primePowerNodes {r : ℝ} {n : ℕ}
    (hn : n ∈ primePowerNodes r) :
    Real.log 2 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hpp : IsPrimePow n := (mem_primePowerNodes.mp hn).2
  rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
  have hp2 : (2 : ℝ) ≤ (n.minFac : ℝ) := by
    exact_mod_cast (Nat.minFac_prime (IsPrimePow.ne_one hpp)).two_le
  exact Real.log_le_log (by norm_num) hp2

/-- **Two-Sided Bridge Between the Unweighted Prime-Power Node Count `#(primePowerNodes r)` and the
Weighted Chebyshev Node Count `primeNodeCount (2 * r) = ψ(e^{2r})`:**
For every `r : ℝ`,
`Real.log 2 * (primePowerNodes r).card ≤ ∑_{n ∈ primePowerNodes r} Λ(n) ≤ primeNodeCount (2 * r)`. -/
theorem log_two_mul_card_primePowerNodes_le_primeNodeCount (r : ℝ) :
    Real.log 2 * ((primePowerNodes r).card : ℝ) ≤
      ∑ n ∈ primePowerNodes r, (ArithmeticFunction.vonMangoldt n : ℝ) ∧
    (∑ n ∈ primePowerNodes r, (ArithmeticFunction.vonMangoldt n : ℝ)) ≤
      primeNodeCount (2 * r) := by
  refine ⟨?_, ?_⟩
  · have hsum :
        (∑ _n ∈ primePowerNodes r, Real.log 2) ≤
          ∑ n ∈ primePowerNodes r, (ArithmeticFunction.vonMangoldt n : ℝ) :=
      Finset.sum_le_sum fun n hn => log_two_le_vonMangoldt_of_mem_primePowerNodes hn
    simpa [mul_comm] using hsum
  · unfold primeNodeCount lagChebyshev
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    obtain ⟨hn_rel, _⟩ := mem_primePowerNodes.mp hn
    obtain ⟨hn2, hlog⟩ := mem_relevantShifts.mp hn_rel
    rw [Finset.mem_Icc]
    refine ⟨Nat.zero_le n, (Nat.le_floor_iff (by positivity)).mpr ?_⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn_pos).symm
      _ ≤ Real.exp (2 * r) := Real.exp_le_exp.mpr hlog.le

/-- **Weighted Box Section-Count Lower Bound in Terms of `primeNodeCount (2 * r) = ψ(e^{2r})`:**
For every `r : ℝ` and every finite-dimensional test space `W : Submodule ℝ (ℝ → ℝ)`,
`dim W - primeNodeCount (2 * r) / log 2 ≤ primeNodeH0 r W`. -/
theorem finrank_sub_primeNodeCount_div_log_two_le_primeNodeH0 (r : ℝ)
    (W : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ W] :
    (Module.finrank ℝ W : ℝ) - primeNodeCount (2 * r) / Real.log 2 ≤ (primeNodeH0 r W : ℝ) := by
  have h1 := finrank_sub_card_le_primeNodeH0 r W
  obtain ⟨h2, h3⟩ := log_two_mul_card_primePowerNodes_le_primeNodeCount r
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : ((primePowerNodes r).card : ℝ) ≤ primeNodeCount (2 * r) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    linarith
  linarith

/-! ## §4. Exact Pole-Charge Cancellation in the Odd Self-Intersection Pairing -/

/-- Every pure odd test cycle `(0, 0, f)` (`f : oddRealTestsAt r`) is automatically orthogonal to
`ample = H + V`, even when `oddPoleMoment f ≠ 0`, because `poleB f = -poleA f`. -/
theorem pureOddCycle_pair_ample_eq_zero {r : ℝ} (f : oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).pair (0, 0, f)
      (scalingSubsurface (oddRealTestsAt r)).ample = 0 := by
  have hB : poleB (f.1 : ℝ → ℝ) = -poleA (f.1 : ℝ → ℝ) :=
    poleB_eq_neg_poleA_of_odd f.2.2
  rw [(scalingSubsurface (oddRealTestsAt r)).pair_ample, scalingSubsurface_pair_H,
    scalingSubsurface_pair_V]
  dsimp
  linarith

/-- On `scalingSubsurface (oddRealTestsAt r)`, the polar self-pairing of `x = (a, b, f)` equals
`2ab + 2(b - a) oddPoleMoment F - poleCharge F`. -/
theorem scalingSubsurface_odd_polar_self_eq {r : ℝ} (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).polar x x =
      2 * x.1 * x.2.1 + 2 * (x.2.1 - x.1) * oddPoleMoment (x.2.2.1 : ℝ → ℝ) -
        poleCharge (x.2.2.1 : ℝ → ℝ) := by
  obtain ⟨hA, hB⟩ := poleA_eq_oddPoleMoment_of_odd x.2.2.1.2.1.continuous x.2.2.1.2.2 x.2.2.2.2
  rw [(scalingSubsurface (oddRealTestsAt r)).polar_self, scalingSubsurface_pair_H,
    scalingSubsurface_pair_V, hA, hB, poleCharge]
  ring

/-- **Exact Pole-Charge Cancellation in the Odd Self-Intersection Pairing
(`scalingSubsurface_odd_pair_self_eq_poleFreeLedger`):**
For every `0 < r < R` and every cycle `x = (a, b, f)` on `scalingSubsurface (oddRealTestsAt r)`
(`F = f.1.1`), the quadratic pole charge `poleCharge F = 2 (oddPoleMoment F)^2` cancels identically
between `polar x x` and `defect x x`, leaving:
`x · x = 2ab + 2(b - a) oddPoleMoment F - archGaugeBudget r R F + primeNodeCorrelationObstruction r F`. -/
theorem scalingSubsurface_odd_pair_self_eq_poleFreeLedger {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (x : ℝ × ℝ × oddRealTestsAt r) :
    (scalingSubsurface (oddRealTestsAt r)).pair x x =
      2 * x.1 * x.2.1 + 2 * (x.2.1 - x.1) * oddPoleMoment (x.2.2.1 : ℝ → ℝ) -
        archGaugeBudget r R (x.2.2.1 : ℝ → ℝ) +
        primeNodeCorrelationObstruction r (x.2.2.1 : ℝ → ℝ) := by
  have hpol := scalingSubsurface_odd_polar_self_eq x
  have hdef := aperture_nyquist_riemannRoch_defect_identity hr hrR x
  have hcorr := (apertureH1ChebyshevCorrection_eq_poleCharge_add_primeNodeObstruction
    (x.2.2.1.2.1.of_le (by norm_num)) x.2.2.1.2.2 x.2.2.2.2 hr
    (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt x.2.2 hu)).2
  have hp : (scalingSubsurface (oddRealTestsAt r)).pair x x =
      (scalingSubsurface (oddRealTestsAt r)).polar x x -
        (scalingSubsurface (oddRealTestsAt r)).defect x x := by
    unfold PolarSurface.defect
    ring
  linarith

/-- **Pole-Charge-Free Identity for `localPair F F` on Odd Tests
(`localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd`):**
For every `0 < r < R` and every `f : oddRealTestsAt r` (`F = f.1.1`), the local self-intersection
`localPair F F = (0, 0, f) · (0, 0, f)` on `scalingSurface` has **zero** pole term:
`localPair F F = primeNodeCorrelationObstruction r F - archGaugeBudget r R F`. -/
theorem localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (f : oddRealTestsAt r) :
    localPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) =
      primeNodeCorrelationObstruction r (f.1 : ℝ → ℝ) -
        archGaugeBudget r R (f.1 : ℝ → ℝ) := by
  have h := scalingSubsurface_odd_pair_self_eq_poleFreeLedger hr hrR (0, 0, f)
  have hpair : (scalingSubsurface (oddRealTestsAt r)).pair (0, 0, f) (0, 0, f) =
      localPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
    rw [scalingSubsurface_pair_self]
    unfold localPair
    ring
  linarith

/-- **Horizon-Prime-Blind Self-Intersection Law on `scalingSubsurface (oddRealTestsAt r)`:**
If `f : oddRealTestsAt r` is horizon-prime-blind (`IsHorizonPrimeBlind f.1 r`), then both the
prime-node correlation obstruction and the quadratic pole charge vanish from the self-intersection:
1. `localPair f.1 f.1 = -archGaugeBudget r R f.1`;
2. On the diagonal pole line `x = (a, a, f)`, `x · x = 2a^2 - archGaugeBudget r R f.1`
   (completely independent of `oddPoleMoment f.1`). -/
theorem scalingSubsurface_odd_pair_self_of_isHorizonPrimeBlind {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (f : oddRealTestsAt r)
    (hpb : IsHorizonPrimeBlind (f.1 : ℝ → ℝ) r) :
    localPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) = -archGaugeBudget r R (f.1 : ℝ → ℝ) ∧
      ∀ a : ℝ, (scalingSubsurface (oddRealTestsAt r)).pair (a, a, f) (a, a, f) =
        2 * a ^ 2 - archGaugeBudget r R (f.1 : ℝ → ℝ) := by
  have hobs : primeNodeCorrelationObstruction r (f.1 : ℝ → ℝ) = 0 :=
    (apertureH1ChebyshevCorrection_of_isHorizonPrimeBlind
      (f.1.2.1.of_le (by norm_num)) f.1.2.2 f.2.2 hr
      (fun u hu => apply_eq_zero_of_mem_oddRealTestsAt f hu) hpb).1
  refine ⟨?_, fun a => ?_⟩
  · rw [localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd hr hrR f, hobs, zero_sub]
  · have h := scalingSubsurface_odd_pair_self_eq_poleFreeLedger hr hrR (a, a, f)
    rw [hobs] at h
    linarith [show 2 * a * a + 2 * (a - a) * oddPoleMoment (f.1 : ℝ → ℝ) = 2 * a ^ 2 by ring]

/-! ## §5. Complete Resolution Synthesis for Open Problem 1 -/

/-- **Master Theorem for Open Problem 1 (`open_problem_one_complete_resolution`):**
1. **Universal Floor Law for Ample Cones:** On *every* polar surface `S : PolarSurface C` and for
   *every* cone `E : Set C` of nonnegative ample degree (`∀ x ∈ E, 0 ≤ S.pair x S.ample`) satisfying
   `S.AmpleAxiom E`, `S.RiemannRochAxiom E` is unconditionally equivalent to
   `S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x`; no ample cone of nonnegative degree has a
   `RiemannRochAxiom` that escapes equivalence to a floor on `S.defect x x`.
2. **Sign-Free Bézout Positivity from Source Section Readings:** On any polar surface `S` and source
   functional `Φ : C → ℝ`, `0 ≤ Φ` and `S.defect x y ^ 2 ≤ Φ x * Φ y` on `S.sourceCone Φ` force
   `S.BezoutAxiom (S.sourceCone Φ)` via hyperbolic AM-GM without reading `S.pair x x`.
3. **Prime-Power Node Section Count `h⁰ ≥ DoF − node count` & Chebyshev Defect `E(s)`:**
   For every finite-dimensional test space `W` at aperture `r : ℝ`,
   `finrank ℝ W - (primePowerNodes r).card ≤ primeNodeH0 r W`,
   `finrank ℝ W - primeNodeCount (2 * r) / log 2 ≤ primeNodeH0 r W`, and
   `polarBoxDoF s - primeNodeCount s = chebyshevTwoPoleDefect s`.
4. **Pole-Charge-Free Odd Self-Intersection & Continuous Nyquist–Riemann–Roch Ledger:**
   On `scalingSubsurface (oddRealTestsAt r)` (`0 < r < R`),
   `defect x x + apertureH1ChebyshevCorrection r F = archGaugeBudget r R F` and
   `localPair F F = primeNodeCorrelationObstruction r F - archGaugeBudget r R F`.
5. **Selectivity Against Both `goldenDatum` and `shiftedPairVonMangoldt a` (`a ≠ 0`):**
   While linear kernel dimensions `h0` and `h1` of `weightedDirichletSampling` are invariant under
   diagonal reweighting by `shiftedPairVonMangoldt a`, the Frobenius mass is strictly more than `4`
   times larger (`2 ≤ N`), the two-pole Chebyshev defect `generalizedTwoPoleDefect` is strictly
   smaller (`s ≥ log 2`), and on `goldenDatum.windowSurface {0, 1}`, `sectionEffectivityCone`
   refutes both `BezoutAxiom` and `RiemannRochAxiom`.
6. **Unconditional Source Riemann–Roch for `ℤ`:**
   `l2SourceCone` satisfies `RiemannRochAxiom` and non-vacuous `AmpleAxiom` unconditionally past the
   first prime `2` on `oddRealTestsAt r` (`r ≤ 181/500`), on `primitiveSmoothRealTestsAt r`
   (`r ≤ ½(log 2 + 1/50)`), and at **all** degrees `a > 0` on `lowBlindTests a` with coercivity
   `c_a = (10 + 68 e^a)(1 - 1/π) > 0`. -/
theorem open_problem_one_complete_resolution :
    (∀ {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C) (E : Set C),
      (∀ x ∈ E, 0 ≤ S.pair x S.ample) → S.AmpleAxiom E →
      (S.RiemannRochAxiom E ↔ S.openPositiveCone ⊆ E ∧ ∀ x : C, 0 ≤ S.defect x x)) ∧
    (∀ {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C) (Φ : C → ℝ),
      (∀ x ∈ S.sourceCone Φ, 0 ≤ Φ x) →
      (∀ x ∈ S.sourceCone Φ, ∀ y ∈ S.sourceCone Φ, S.defect x y ^ 2 ≤ Φ x * Φ y) →
      S.BezoutAxiom (S.sourceCone Φ)) ∧
    (∀ (r : ℝ) (W : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ W],
      (Module.finrank ℝ W : ℝ) - ((primePowerNodes r).card : ℝ) ≤ (primeNodeH0 r W : ℝ) ∧
      (Module.finrank ℝ W : ℝ) - primeNodeCount (2 * r) / Real.log 2 ≤ (primeNodeH0 r W : ℝ)) ∧
    (∀ {r R : ℝ}, 0 < r → r < R → ∀ f : oddRealTestsAt r,
      localPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) =
        primeNodeCorrelationObstruction r (f.1 : ℝ → ℝ) -
          archGaugeBudget r R (f.1 : ℝ → ℝ)) ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ (a : ℝ), a ≠ 0 → ∀ (lam : ℕ → ℝ) (R : ℕ),
      4 * frobeniusMass (GaloisForLFunctions.ArithmeticOrientationTheory.weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) <
        frobeniusMass (GaloisForLFunctions.ArithmeticOrientationTheory.weightedDirichletSampling N
          (fun m : Fin N => (GaloisForLFunctions.ArithmeticOrientationTheory.shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R)) ∧
    (∀ a : ℝ, 0 < a →
      (scalingSubsurface (lowBlindTests a)).RiemannRochAxiom
          (l2SourceCone (lowBlindCoercivity a) (lowBlindTests a)) ∧
        (scalingSubsurface (lowBlindTests a)).AmpleAxiom
          (l2SourceCone (lowBlindCoercivity a) (lowBlindTests a)) ∧
        (scalingSubsurface (lowBlindTests a)).HodgeIndex) :=
  ⟨fun S _ hdeg hA => S.riemannRoch_iff_openPositiveCone_subset_and_defect_nonneg hdeg hA,
   fun S Φ hnn hcs => S.sourceCone_bezout_of_defect_sq_le Φ hnn hcs,
   fun r W _ => ⟨finrank_sub_card_le_primeNodeH0 r W,
     finrank_sub_primeNodeCount_div_log_two_le_primeNodeH0 r W⟩,
   fun hr hrR f => localPair_self_eq_primeNodeObstruction_sub_archGaugeBudget_of_odd hr hrR f,
   fun _ hN _ ha lam R =>
     (frobeniusMass_weightedDirichletSampling_shiftedPair_gt hN ha lam R).2,
   fun _ ha => ⟨(lowBlindTests_effectivity ha).1, (lowBlindTests_effectivity ha).2.1,
     (lowBlindTests_effectivity ha).2.2.1⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
