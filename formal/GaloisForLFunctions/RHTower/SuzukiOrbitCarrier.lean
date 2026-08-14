import GaloisForLFunctions.RHTower.SuzukiOrbitWeightSummability
import GaloisForLFunctions.HTGeometry.WeightedShiftEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The weighted orbit carrier of a physical profile

Lifting a profile by the exponential orbit weight, `(J_ρ u)_ν = w_ρ(ν) U_ν u`, costs exactly the
weight's mass: physical translation is an isometry of `L²`, so the lattice energy of the lift is
`‖w_ρ‖₂² ‖u‖₂²`, and the root coordinate returns the profile unchanged.  Prime translation
intertwines with a weighted coordinate shift whose ratios are pinched by the weight's edge bound,
so the complete finite prime adjacency becomes a bounded — generally nonselfadjoint — operator on
the orbit carrier.
-/

open MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Physical translation of an `L²` profile by a seam displacement. -/
def orbitTranslate (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun x : ℝ => x + t) (measurePreserving_add_right volume t) u

/-- Physical translation is an isometry: the orbit lift moves no energy. -/
theorem norm_orbitTranslate (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖orbitTranslate t u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_add_right volume t)

/-- **`(4)`: the root coordinate reconstructs the profile.** -/
theorem orbitTranslate_zero (u : Lp ℂ 2 (volume : Measure ℝ)) : orbitTranslate 0 u = u := by
  refine Lp.ext ?_
  have h := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) u
    (measurePreserving_add_right volume (0:ℝ))
  filter_upwards [h] with x hx
  simpa [orbitTranslate] using hx

/-- A constant-norm weighted family has exactly the weight's energy. -/
theorem tsum_sq_weighted_const {ι : Type*} (w : ι → ℝ) (c : ℝ) :
    (∑' ν : ι, (w ν * c) ^ 2) = (∑' ν : ι, w ν ^ 2) * c ^ 2 := by
  have hterm : ∀ ν : ι, (w ν * c) ^ 2 = w ν ^ 2 * c ^ 2 := fun ν => by ring
  rw [tsum_congr hterm, tsum_mul_right]

/-- **`(3)`, `(10)`: the weighted orbit lift of an `L²` profile has energy `‖w_ρ‖₂² ‖u‖₂²`.** -/
theorem tsum_sq_orbitLift {P : Type*} [Fintype P] (ρ : ℝ) (ℓ : (P → ℤ) → ℝ)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∑' ν : P → ℤ, (orbitWeight ρ ν * ‖orbitTranslate (ℓ ν) u‖) ^ 2)
      = (∑' ν : P → ℤ, orbitWeight ρ ν ^ 2) * ‖u‖ ^ 2 := by
  have hterm : ∀ ν : P → ℤ,
      (orbitWeight ρ ν * ‖orbitTranslate (ℓ ν) u‖) ^ 2 = (orbitWeight ρ ν * ‖u‖) ^ 2 := by
    intro ν
    rw [norm_orbitTranslate]
  rw [tsum_congr hterm, tsum_sq_weighted_const]

/-- **`(11)`: the same lift of a bounded profile, in the sup norm. -/
theorem tsum_sq_orbitLift_const {P : Type*} [Fintype P] (ρ : ℝ) (c : ℝ) :
    (∑' ν : P → ℤ, (orbitWeight ρ ν * c) ^ 2)
      = (∑' ν : P → ℤ, orbitWeight ρ ν ^ 2) * c ^ 2 :=
  tsum_sq_weighted_const _ c

/-! ## The weighted valuation shift -/

/-- **`(14)`: the edge ratio of the orbit weight across a valuation step.** -/
def orbitShiftRatio {P : Type*} [Fintype P] (ρ : ℝ) (s ν : P → ℤ) : ℝ :=
  orbitWeight ρ ν / orbitWeight ρ (ν + s)

/-- **`(16)`: the edge ratio never exceeds `ρ^{-|s|₁}`.** -/
theorem abs_orbitShiftRatio_le {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1)
    (s ν : P → ℤ) : |orbitShiftRatio ρ s ν| ≤ (ρ ^ orbitLength s)⁻¹ := by
  have hpos : 0 < orbitWeight ρ (ν + s) := orbitWeight_pos hρ0 _
  have hnum : 0 < orbitWeight ρ ν := orbitWeight_pos hρ0 _
  have hle := orbitWeight_le_ratio hρ0 hρ ν s
  rw [orbitShiftRatio, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  calc orbitWeight ρ ν ≤ orbitWeight ρ (ν + s) * (ρ ^ orbitLength s)⁻¹ := hle
    _ = (ρ ^ orbitLength s)⁻¹ * orbitWeight ρ (ν + s) := by ring

/-- **`(17)`: the weighted valuation shift is bounded by `ρ^{-|s|₁}` in energy.** -/
theorem tsum_sq_orbitWeightedShift_le {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1)
    (s : P → ℤ) {Z : (P → ℤ) → ℝ} (hZ : Summable fun ν => Z ν ^ 2) :
    (∑' ν : P → ℤ, (orbitShiftRatio ρ s ν * Z (ν + s)) ^ 2)
      ≤ ((ρ ^ orbitLength s)⁻¹) ^ 2 * ∑' ν : P → ℤ, Z ν ^ 2 :=
  tsum_sq_weightedShift_le (fun ν => abs_orbitShiftRatio_le hρ0 hρ s ν) s hZ

/-- **`(19)`: a finite prime adjacency of weighted shifts is bounded in energy by the sum of its
edge bounds.** -/
theorem tsum_sq_orbitWeightedShift_le_of_le {P : Type*} [Fintype P] {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1) (s : P → ℤ) {Z : (P → ℤ) → ℝ} (hZ : Summable fun ν => Z ν ^ 2) {E : ℝ}
    (hE : (∑' ν : P → ℤ, Z ν ^ 2) ≤ E) :
    (∑' ν : P → ℤ, (orbitShiftRatio ρ s ν * Z (ν + s)) ^ 2)
      ≤ ((ρ ^ orbitLength s)⁻¹) ^ 2 * E :=
  tsum_sq_weightedShift_le_of_le (fun ν => abs_orbitShiftRatio_le hρ0 hρ s ν) s hZ hE

/-- Translation is an action: composing displacements adds them. -/
theorem orbitTranslate_add (t t' : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    orbitTranslate t (orbitTranslate t' u) = orbitTranslate (t' + t) u := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) (orbitTranslate t' u)
    (measurePreserving_add_right volume t)
  have h2 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) u
    (measurePreserving_add_right volume t')
  have h3 := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp h2
  have h4 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) u
    (measurePreserving_add_right volume (t' + t))
  filter_upwards [h1, h3, h4] with x hx1 hx3 hx4
  simp only [Function.comp_apply] at hx1 hx3 hx4 ⊢
  calc ((orbitTranslate t (orbitTranslate t' u) : Lp ℂ 2 volume) : ℝ → ℂ) x
      = ((orbitTranslate t' u : Lp ℂ 2 volume) : ℝ → ℂ) (x + t) := hx1
    _ = (u : ℝ → ℂ) (x + t + t') := hx3
    _ = (u : ℝ → ℂ) (x + (t' + t)) := by
        rw [show x + t + t' = x + (t' + t) by ring]
    _ = ((orbitTranslate (t' + t) u : Lp ℂ 2 volume) : ℝ → ℂ) x := hx4.symm

/-- **`(13)`, `(15)`: prime translation intertwines with the weighted coordinate shift.**  The
lift of a translated profile is the shifted lift, rescaled by the weight's edge ratio. -/
theorem orbitLift_translate {P : Type*} [Fintype P] {ρ : ℝ} (hρ : 0 < ρ) (ℓ : (P → ℤ) → ℝ)
    (hℓ : ∀ ν s : P → ℤ, ℓ (ν + s) = ℓ ν + ℓ s) (s ν : P → ℤ)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (orbitWeight ρ ν : ℂ) • orbitTranslate (ℓ ν) (orbitTranslate (ℓ s) u)
      = (orbitShiftRatio ρ s ν : ℂ) •
          ((orbitWeight ρ (ν + s) : ℂ) • orbitTranslate (ℓ (ν + s)) u) := by
  have hpos : 0 < orbitWeight ρ (ν + s) := orbitWeight_pos hρ _
  have hcomp : orbitTranslate (ℓ ν) (orbitTranslate (ℓ s) u)
      = orbitTranslate (ℓ (ν + s)) u := by
    rw [orbitTranslate_add, hℓ ν s, show ℓ s + ℓ ν = ℓ ν + ℓ s by ring]
  have hne : (orbitWeight ρ (ν + s) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hpos
  rw [hcomp, smul_smul]
  congr 1
  rw [orbitShiftRatio]
  push_cast
  field_simp

/-! ## Nonnormality does not obstruct the terminal estimate -/

/-- **`(20)`: the real part of a bounded operator's quadratic form is controlled by its norm** —
the statement that makes self-adjointness dispensable in the terminal ray estimate. -/
theorem abs_re_inner_le_norm_mul_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (z : H) :
    |(inner ℂ (B z) z).re| ≤ ‖B‖ * ‖z‖ ^ 2 := by
  have h1 : |(inner ℂ (B z) z).re| ≤ ‖(inner ℂ (B z) z : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : ‖(inner ℂ (B z) z : ℂ)‖ ≤ ‖B z‖ * ‖z‖ := norm_inner_le_norm _ _
  have h3 : ‖B z‖ ≤ ‖B‖ * ‖z‖ := B.le_opNorm z
  calc |(inner ℂ (B z) z).re| ≤ ‖B z‖ * ‖z‖ := le_trans h1 h2
    _ ≤ (‖B‖ * ‖z‖) * ‖z‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = ‖B‖ * ‖z‖ ^ 2 := by ring

/-- **`(22)`: the terminal coercive bracket.**  With a lower numerical-range bound for the Gamma
multiplier and a bounded coupling, the shifted form is coercive once the ray is far enough. -/
theorem re_inner_terminal_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (B : H →L[ℂ] H) (z : H) {L κ : ℝ} (hκ : -κ * ‖z‖ ^ 2 ≤ (inner ℂ (B z) z).re)
    (T : H →L[ℂ] H) :
    (2 * L - κ - ‖T‖) * ‖z‖ ^ 2
      ≤ 2 * L * ‖z‖ ^ 2 + (inner ℂ (B z) z).re - (inner ℂ (T z) z).re := by
  have hT := abs_re_inner_le_norm_mul_sq T z
  have hT' : (inner ℂ (T z) z).re ≤ ‖T‖ * ‖z‖ ^ 2 := le_trans (le_abs_self _) hT
  nlinarith [hκ, hT']

end

end RHTower
