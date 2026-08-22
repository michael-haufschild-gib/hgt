import GaloisForLFunctions.HTGeometry.AnalyticBackgroundSaturation
import GaloisForLFunctions.HTGeometry.HardyDiskCyclic
import GaloisForLFunctions.HTGeometry.ParabolicOuterOrbitLimit

/-!
# The invertible outer cage of a grafted analytic background

A bounded analytic background of sup-norm strictly below the outer floor `exp (-1)` cannot cancel
the positive-mass outer core.  The grafted source is then bounded, bounded away from zero, and
therefore invertible in `H^∞` of the upper half plane.  Pulled back to the unit disc by the Cayley
map it becomes an invertible bounded analytic function, hence a cyclic vector for the shift on
`H²(𝔻)` -- the operator form of outerness.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

noncomputable section

/-- The Cayley map from the disc to the upper half plane is holomorphic. -/
theorem differentiableAt_cayleyToUpper {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableAt ℂ cayleyToUpper w := by
  have hne : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) hne

/-- The grafted source pulled back to the unit disc by the Cayley map. -/
def graftedDisk (x ε : ℕ → ℝ) (u : MassParameter) (B : ℂ → ℂ) (w : ℂ) : ℂ :=
  massOuterBackground x ε u (cayleyToUpper w) + B (cayleyToUpper w)

theorem differentiableOn_graftedDisk {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) {B : ℂ → ℂ} (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) :
    DifferentiableOn ℂ (graftedDisk x ε u B) (ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have him : 0 < (cayleyToUpper w).im := im_cayleyToUpper_pos hw
  have hcay : DifferentiableAt ℂ cayleyToUpper w := differentiableAt_cayleyToUpper hw
  have hM : DifferentiableAt ℂ (massOuterBackground x ε u) (cayleyToUpper w) :=
    (contDiffAt_massOuterBackground hεpos hε u him).differentiableAt (by simp)
  have hBt : DifferentiableAt ℂ B (cayleyToUpper w) :=
    ((hB.analyticOnNhd isOpen_upperHalfSet) _ him).differentiableAt
  exact ((hM.comp w hcay).add (hBt.comp w hcay)).differentiableWithinAt

theorem norm_graftedDisk_le {x ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) {B : ℂ → ℂ} {b : ℝ} (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    ‖graftedDisk x ε u B w‖ ≤ Real.exp 1 + b := by
  rw [mem_ball_zero_iff] at hw
  exact norm_grafted_le hεpos hε u hb (im_cayleyToUpper_pos hw)

theorem norm_graftedDisk_ge {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    Real.exp (-1) - b ≤ ‖graftedDisk x ε u B w‖ := by
  rw [mem_ball_zero_iff] at hw
  exact norm_grafted_ge hx hεpos hε u hb (im_cayleyToUpper_pos hw)

theorem graftedDisk_ne_zero {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) (hblt : b < Real.exp (-1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    graftedDisk x ε u B w ≠ 0 := by
  rw [mem_ball_zero_iff] at hw
  exact grafted_ne_zero hx hεpos hε u hb hblt (im_cayleyToUpper_pos hw)

/-- The background bound is nonnegative. -/
theorem background_bound_nonneg {B : ℂ → ℂ} {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) : 0 ≤ b :=
  le_trans (norm_nonneg _) (hb Complex.I (by simp))

/-- The grafted source as a bounded analytic multiplier of the disc. -/
def graftedMultiplier (x : ℕ → ℝ) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε)
    (u : MassParameter) {B : ℂ → ℂ} (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) : DiskMultiplier where
  fn := graftedDisk x ε u B
  diff := differentiableOn_graftedDisk hεpos hε u hB
  bd := Real.exp 1 + b
  bd_nonneg := by
    have := background_bound_nonneg hb
    have : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    linarith [background_bound_nonneg hb]
  bd_le := fun z hz => norm_graftedDisk_le hεpos hε u hb hz

/-- The reciprocal of the grafted source, again a bounded analytic multiplier of the disc. -/
def graftedInvMultiplier {x ε : ℕ → ℝ} (hx : Function.Injective x) (hεpos : ∀ k, 0 < ε k)
    (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) (hblt : b < Real.exp (-1)) : DiskMultiplier where
  fn := fun w => (graftedDisk x ε u B w)⁻¹
  diff := by
    intro w hw
    have hd := ((differentiableOn_graftedDisk hεpos hε u hB w hw).differentiableAt
      (isOpen_ball.mem_nhds hw)).inv (graftedDisk_ne_zero hx hεpos hε u hb hblt hw)
    exact hd.differentiableWithinAt
  bd := (Real.exp (-1) - b)⁻¹
  bd_nonneg := by positivity
  bd_le := by
    intro w hw
    rw [norm_inv]
    have hpos : 0 < Real.exp (-1) - b := by linarith
    exact inv_anti₀ hpos (norm_graftedDisk_ge hx hεpos hε u hb hw)

/-- **The invertible outer cage.**  A bounded analytic background of sup-norm strictly below
`exp (-1)` leaves the grafted source invertible in `H^∞`; pulled back to the disc it is a cyclic
vector for the shift on `H²(𝔻)`, which is the operator form of outerness. -/
theorem cyclicSubspace_hardyOf_graftedMultiplier {x ε : ℕ → ℝ} (hx : Function.Injective x)
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (u : MassParameter) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B {ζ : ℂ | 0 < ζ.im}) {b : ℝ}
    (hb : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, ‖B z‖ ≤ b) (hblt : b < Real.exp (-1)) :
    cyclicSubspace (hardyOf (graftedMultiplier x hεpos hε u hB hb)) = ⊤ :=
  cyclicSubspace_hardyOf_eq_top (ψ := graftedInvMultiplier hx hεpos hε u hB hb hblt)
    (fun _ hz => mul_inv_cancel₀ (graftedDisk_ne_zero hx hεpos hε u hb hblt hz))

end

end GaloisForLFunctions.HTGeometry
