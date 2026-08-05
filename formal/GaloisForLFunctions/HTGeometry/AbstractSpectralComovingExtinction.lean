import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingMass
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Extinction along widening co-moving mass cones

The co-moving cone bound is stronger than uniform boundedness.  If the aperture tends to infinity
while continuing to contain vertical time, every individual massive term vanishes.  The universal
cone weight supplies a fixed summable dominator, so Tannery's theorem makes the complete trace
vanish.

This is an abstract theorem for every admissible spectral family.  No Xi-specific geometry or
arithmetic input enters.
-/

open Complex Filter Topology

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- Pointwise aperture-decay estimate inside the co-moving cone. -/
theorem norm_mass_term_le_comoving_aperture_decay
    {a σ u : ℝ} (ha : 1 / 2 ≤ a) (hbase : 1 / 2 ≤ F.base)
    (hu : |u| ≤ a) (hσ : 0 < σ) (i : ι) :
    ‖(F.mass ha).term ((σ : ℂ) + u * I) i‖ ≤
      Real.exp (-σ * a + (F.pt i).re / 2) := by
  have hM : a < ((F.mass ha).pt i).re := F.lt_re_mass_of_base_half ha hbase i
  have hMpos : 0 < ((F.mass ha).pt i).re := lt_trans (by linarith : 0 < a) hM
  have hRpos : 0 < (F.pt i).re := F.re_pos i
  have hprod := F.re_mul_im_mass ha i
  have hprodAbs :
      ((F.mass ha).pt i).re * |((F.mass ha).pt i).im| =
        (F.pt i).re * |(F.pt i).im| := by
    have habs := congrArg abs hprod
    simpa only [abs_mul, abs_of_pos hMpos, abs_of_pos hRpos] using habs
  have huK : u * ((F.mass ha).pt i).im ≤ (F.pt i).re / 2 := by
    calc
      u * ((F.mass ha).pt i).im ≤ |u * ((F.mass ha).pt i).im| := le_abs_self _
      _ = |u| * |((F.mass ha).pt i).im| := abs_mul _ _
      _ ≤ a * |((F.mass ha).pt i).im| :=
        mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ ≤ ((F.mass ha).pt i).re * |((F.mass ha).pt i).im| :=
        mul_le_mul_of_nonneg_right hM.le (abs_nonneg _)
      _ = (F.pt i).re * |(F.pt i).im| := hprodAbs
      _ ≤ (F.pt i).re * (1 / 2) :=
        mul_le_mul_of_nonneg_left (F.abs_im_lt i).le hRpos.le
      _ = (F.pt i).re / 2 := by ring
  rw [(F.mass ha).norm_term]
  apply Real.exp_le_exp.mpr
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one]
  nlinarith [mul_pos hσ (sub_pos.mpr hM)]

/-- **Universal co-moving extinction.** A mass aperture tending to infinity while containing
vertical time makes the complete mass trace vanish on every line `σ>1/2`. -/
theorem tendsto_mass_traceC_comoving_zero
    {mass : ℝ → ℝ} {σ : ℝ}
    (hmassHalf : ∀ u, 1 / 2 ≤ mass u)
    (hbase : 1 / 2 ≤ F.base)
    (hcone : ∀ u, |u| ≤ mass u)
    (hmass : Tendsto mass atTop atTop)
    (hσ : 1 / 2 < σ) :
    Tendsto
      (fun u : ℝ => (F.mass (hmassHalf u)).traceC ((σ : ℂ) + u * I))
      atTop (𝓝 0) := by
  have hσ0 : 0 < σ := by linarith
  have hpoint (i : ι) : Tendsto
      (fun u : ℝ => (F.mass (hmassHalf u)).term ((σ : ℂ) + u * I) i)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlinear : Tendsto (fun u : ℝ => -σ * mass u) atTop atBot :=
      hmass.const_mul_atTop_of_neg (neg_neg_of_pos hσ0)
    have hshift : Tendsto (fun u : ℝ => -σ * mass u + (F.pt i).re / 2)
        atTop atBot :=
      tendsto_atBot_add_const_right atTop ((F.pt i).re / 2) hlinear
    have hmajor : Tendsto
        (fun u : ℝ => Real.exp (-σ * mass u + (F.pt i).re / 2))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hshift
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _) ?_ hmajor
    exact Eventually.of_forall fun u =>
      F.norm_mass_term_le_comoving_aperture_decay
        (hmassHalf u) hbase (hcone u) hσ0 i
  have hbound : ∀ᶠ u : ℝ in atTop, ∀ i : ι,
      ‖(F.mass (hmassHalf u)).term ((σ : ℂ) + u * I) i‖ ≤
        F.weight (σ - 1 / 2) i :=
    Eventually.of_forall fun u i =>
      F.norm_mass_term_le_comoving_weight
        (hmassHalf u) hbase (hcone u) hσ i
  have hsum := tendsto_tsum_of_dominated_convergence
    (F.summable_weight (by linarith : 0 < σ - 1 / 2)) hpoint hbound
  simpa [traceC] using hsum

end AbstractSpectralFamily

end


end HTGeometry
