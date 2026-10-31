import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCayleyDensity
import Mathlib.Analysis.Complex.Schwarz

/-!+# Strict contraction about an interior fixed point

A holomorphic upper-half-plane self-map fixing `i`, with derivative of modulus less than one
there, strictly decreases Cayley radius away from `i`. Consequently it has no other periodic
points. The derivative gap excludes the rotations in the equality case of Schwarz's lemma.
-/

open Complex Set Metric Filter Topology
open GaloisForLFunctions.HTGeometry

namespace Bottcher.HalfPlane

noncomputable section

/-- A strict derivative gap turns Schwarz's nonexpansion into strict radial contraction. -/
theorem norm_lt_of_deriv_norm_lt_one {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0)
    (hder : ‖deriv f 0‖ < 1) {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    ‖f w‖ < ‖w‖ := by
  have hm' : MapsTo f (ball 0 1) (closedBall 0 1) :=
    fun _ h => ball_subset_closedBall (hm h)
  have hle := Complex.norm_le_norm_of_mapsTo_ball hd hm' h0 hw
  apply lt_of_le_of_ne hle
  intro heq
  have hs : ‖dslope f 0 w‖ = 1 := by
    rw [dslope_of_ne _ hw0, slope_def_field, h0, sub_zero, sub_zero, norm_div, heq]
    exact div_self (norm_ne_zero_iff.mpr hw0)
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd
    (by simpa only [h0] using hm') (mem_ball_zero_iff.mpr hw)
    (by simpa only [div_one] using hs)
  have hev : f =ᶠ[𝓝 0] fun z => z * dslope f 0 w := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    simpa only [h0, sub_zero, zero_add, smul_eq_mul] using haff hz
  have he : deriv f 0 = dslope f 0 w := by
    rw [hev.deriv_eq]
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℂ)).mul_const (dslope f 0 w)).deriv
  rw [he, hs] at hder
  exact lt_irrefl _ hder

/-- Cayley coordinates of an upper point lie in the open disk. -/
theorem norm_upperToDisk_lt_one {z : ℂ} (hz : 0 < z.im) : ‖upperToDisk z‖ < 1 := by
  have h := normSq_upperToDisk_lt_one hz
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (upperToDisk z)]

private theorem add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

/-- Derivative of the Cayley coordinate on the upper half-plane. -/
theorem hasDerivAt_upperToDisk {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt upperToDisk (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div
    ((hasDerivAt_id z).add_const I) (add_I_ne_zero hz)
  convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)

/-- Disk conjugate of an upper-half-plane map, centered at its fixed point `i`. -/
def diskConjugate (f : ℂ → ℂ) (w : ℂ) : ℂ := upperToDisk (f (diskToUpper w))

theorem diskConjugate_zero {f : ℂ → ℂ} (hi : f I = I) : diskConjugate f 0 = 0 := by
  simp [diskConjugate, diskToUpper, hi, upperToDisk]

theorem diskConjugate_mapsTo {f : ℂ → ℂ}
    (hm : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) :
    MapsTo (diskConjugate f) (ball 0 1) (ball 0 1) := by
  intro w hw
  exact mem_ball_zero_iff.mpr
    (norm_upperToDisk_lt_one (hm _ (diskToUpper_im_pos w hw)))

theorem differentiableOn_diskConjugate {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hm : ∀ z : ℂ, 0 < z.im → 0 < (f z).im) :
    DifferentiableOn ℂ (diskConjugate f) (ball 0 1) := by
  intro w hw
  have hwu := diskToUpper_im_pos w hw
  have hw1 : w ≠ 1 := by
    intro heq
    simp only [heq, mem_ball_zero_iff, norm_one, lt_self_iff_false] at hw
  exact (((hasDerivAt_upperToDisk (hm _ hwu)).differentiableAt.comp _
    (hd _ hwu)).comp _ (hasDerivAt_diskToUpper hw1).differentiableAt).differentiableWithinAt

/-- Cayley conjugacy preserves the multiplier at the anchored fixed point. -/
theorem deriv_diskConjugate_zero {f : ℂ → ℂ}
    (hd : DifferentiableAt ℂ f I) (hi : f I = I) :
    deriv (diskConjugate f) 0 = deriv f I := by
  have hzero : diskToUpper 0 = I := by simp [diskToUpper]
  have hin : HasDerivAt diskToUpper (2 * I) 0 := by
    simpa using hasDerivAt_diskToUpper (w := 0) (by simp)
  have hf : HasDerivAt f (deriv f I) (diskToUpper 0) := by
    rw [hzero]
    exact hd.hasDerivAt
  have hmid := hf.comp 0 hin
  have hout : HasDerivAt upperToDisk (2 * I / (I + I) ^ 2) (f (diskToUpper 0)) := by
    rw [hzero, hi]
    exact hasDerivAt_upperToDisk (by simp)
  have h := hout.comp 0 hmid
  change HasDerivAt (diskConjugate f) _ 0 at h
  rw [h.deriv]
  field_simp
  ring

/-- Cayley radius strictly decreases at every nonanchor upper point. -/
theorem cayleyRadius_strict_decrease {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hm : ∀ z : ℂ, 0 < z.im → 0 < (f z).im)
    (hi : f I = I) (hder : ‖deriv f I‖ < 1)
    {z : ℂ} (hz : 0 < z.im) (hzi : z ≠ I) :
    ‖upperToDisk (f z)‖ < ‖upperToDisk z‖ := by
  have hw0 : upperToDisk z ≠ 0 := by
    intro h
    apply hzi
    have := diskToUpper_upperToDisk hz
    simpa only [h, diskToUpper, add_zero, sub_zero, mul_one, div_one] using this.symm
  have h := norm_lt_of_deriv_norm_lt_one
    (differentiableOn_diskConjugate hd hm) (diskConjugate_mapsTo hm)
    (diskConjugate_zero hi)
    (by rw [deriv_diskConjugate_zero (hd I (by simp)) hi]; exact hder)
    (norm_upperToDisk_lt_one hz) hw0
  simpa only [diskConjugate, diskToUpper_upperToDisk hz] using h

/-- No positive iterate returns a nonanchor upper point. -/
theorem eq_I_of_iterate_eq_self {f : ℂ → ℂ}
    (hd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hm : ∀ z : ℂ, 0 < z.im → 0 < (f z).im)
    (hi : f I = I) (hder : ‖deriv f I‖ < 1)
    {z : ℂ} (hz : 0 < z.im) {n : ℕ} (hn : 0 < n) (hper : f^[n] z = z) : z = I := by
  by_contra hzi
  have hstep : ∀ w : ℂ, 0 < w.im → ‖upperToDisk (f w)‖ ≤ ‖upperToDisk w‖ := by
    intro w hw
    by_cases hwi : w = I
    · simp only [hwi, hi, le_refl]
    · exact (cayleyRadius_strict_decrease hd hm hi hder hw hwi).le
  have hiter : ∀ k : ℕ, 0 < (f^[k] (f z)).im ∧
      ‖upperToDisk (f^[k] (f z))‖ ≤ ‖upperToDisk (f z)‖ := by
    intro k
    induction k with
    | zero => exact ⟨hm z hz, le_rfl⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hm _ ih.1, (hstep _ ih.1).trans ih.2⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Function.iterate_succ_apply] at hper
  have hle := (hiter k).2
  rw [hper] at hle
  exact (not_lt_of_ge hle) (cayleyRadius_strict_decrease hd hm hi hder hz hzi)

end
end Bottcher.HalfPlane

#print axioms Bottcher.HalfPlane.cayleyRadius_strict_decrease
#print axioms Bottcher.HalfPlane.eq_I_of_iterate_eq_self
