import GaloisForLFunctions.RHTower.ThetaSeedTransferQuartet
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ThetaLogMoment

/-! Positive quartet deformations are dominated by the actual theta source.
They therefore isolate every selected off-line quartet with absolute moment
growth bounded by `exp((s+6) log(s+6))`. -/

open MeasureTheory Complex
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open _root_.RHTower

/-- A positive quartet deformation retains theta's logarithmic moment growth,
while its transform isolates exactly the selected quartet among Xi zeros. -/
theorem exists_positive_quartet_log_moments {a : ℂ} (ha : a ∈ xiQuadrantZeros) :
    ∃ (k : ℝ → ℝ) (C : ℝ), 0 < C ∧ Continuous k ∧
      (∀ x, 0 < k x) ∧ (∀ x, k (-x) = k x) ∧
      (∀ s : ℝ, Integrable fun x => Real.exp (s * |x|) * |k x|) ∧
      (∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (s * |x|) * k x) ≤
        C * Real.exp ((s + 6) * Real.log (s + 6))) ∧
      (∀ z ∈ xiQuartetSet a, sourceTransform (fun x => (k x : ℂ)) z ≠ 0) ∧
      (∀ z : ℂ, XiC z = 0 → z ∉ xiQuartetSet a →
        sourceTransform (fun x => (k x : ℂ)) z = 0) := by
  obtain ⟨huc, hue, ⟨Cu, huC⟩, _, _, _⟩ := quartetSource_spec ha
  obtain ⟨ε₀, hε₀, hgen⟩ := quartet_seed_transfer ha
  let ε : ℝ := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hεlt : ε < ε₀ := half_lt_self hε₀
  obtain ⟨hpos, _, _, _, _, _, _, hkeep, _, hzero⟩ := hgen ε hε hεlt
  let k : ℝ → ℝ := fun x => thetaCuspFullSource x + ε * quartetSource a x
  have hk : ∀ x, 0 < k x := hpos
  let B : ℝ := 1 + ε * |Cu|
  have hB : 0 < B := by dsimp [B]; positivity
  have hkc : Continuous k := contDiff_thetaCuspFullSource.continuous.add
    (continuous_const.mul huc.continuous)
  have hbound (x : ℝ) : |k x| ≤ B * thetaCuspFullSource x := by
    have hp := thetaCuspFullSource_pos x
    have hu : |quartetSource a x| ≤ |Cu| * thetaCuspFullSource x :=
      (huC x).trans (mul_le_mul_of_nonneg_right (le_abs_self Cu) hp.le)
    calc
      _ ≤ |thetaCuspFullSource x| + |ε * quartetSource a x| := abs_add_le _ _
      _ ≤ thetaCuspFullSource x + ε * (|Cu| * thetaCuspFullSource x) := by
        rw [abs_of_pos hp, abs_mul, abs_of_pos hε]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hu hε.le)
      _ = _ := by dsimp [B]; ring
  have hm (s : ℝ) : Integrable fun x => Real.exp (s * |x|) * |k x| := by
    have hi := (expMomentSource_ofReal_of_le hkc hbound).moment s
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hi
  obtain ⟨Cθ, hCθ, hθ⟩ := exists_theta_logarithmic_moment_bound
  refine ⟨k, B * Cθ, mul_pos hB hCθ, hkc, hpos, ?_, hm, ?_, hkeep, ?_⟩
  · intro x
    dsimp [k]
    rw [thetaCuspFullSource_neg, hue]
  · intro s hs
    have hki : Integrable fun x => Real.exp (s * |x|) * k x := by
      simpa only [abs_of_pos (hk _)] using hm s
    have hθi := (expMomentSource_ofReal_of_le contDiff_thetaCuspFullSource.continuous
      (C := 1) (fun x => by rw [abs_of_pos (thetaCuspFullSource_pos x), one_mul])).moment s
    have hθi' : Integrable fun x => Real.exp (s * |x|) * thetaCuspFullSource x := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (thetaCuspFullSource_pos _)] using hθi
    have hi := integral_mono hki (hθi'.const_mul B) (fun x => by
      have hh := mul_le_mul_of_nonneg_left
        ((le_abs_self (k x)).trans (hbound x)) (Real.exp_pos (s * |x|)).le
      simpa only [mul_left_comm B] using hh)
    rw [integral_const_mul] at hi
    exact hi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hθ s hs) hB.le)
  · intro z hz hzout
    exact (hzero z hzout).mpr (Or.inl hz)

#print axioms exists_positive_quartet_log_moments
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
