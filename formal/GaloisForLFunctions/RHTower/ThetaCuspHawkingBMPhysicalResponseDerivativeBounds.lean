import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceBounds
import GaloisForLFunctions.HTGeometry.NegativeRayBoundedDerivative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseClassical
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseBounds

/-! Actual physical derivative bounds follow from the complete forcing and original response equation. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The complete actual second derivative is bounded on the original negative ray. -/
theorem physicalCuspSecond_bounded (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, t < 0 → ‖physicalCuspSecond q r branch w a hw hd hwi hwr t‖ ≤ M := by
  obtain ⟨C,hC,hP⟩ := physicalCuspProfile_bounded q r branch w a hw hd hwi hwr
  obtain ⟨D,hD,hF⟩ := continuedAngularSourceProjection_bounded q branch (physicalAngularParameter r) a w hd hwi
  refine ⟨‖w‖^(2 : ℕ)*C+‖physicalAngularParameter r^(2 : ℕ)-1/4‖*C+D,
    add_nonneg (add_nonneg (mul_nonneg (sq_nonneg _) hC) (mul_nonneg (norm_nonneg _) hC)) hD,
    fun t ht => ?_⟩
  have hv : ‖angularWeight t^(2 : ℕ)‖ ≤ 1 := by
    rw [← horizonCoordinate_jointWeight t ht,Complex.norm_real,
      Real.norm_of_nonneg (horizonCoordinate_nonneg t)]
    exact horizonCoordinate_le_one t
  unfold physicalCuspSecond
  calc
    _ ≤ ‖w^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t-
        (physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t‖+
        ‖continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t‖ := norm_sub_le _ _
    _ ≤ (‖w^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t‖+
        ‖(physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ)*physicalCuspProfile q r branch w a hw hd hwi hwr t‖)+D :=
      add_le_add (norm_sub_le _ _) (hF t ht)
    _ ≤ _ := by
      simp only [norm_mul,norm_pow]
      have hv' : ‖angularWeight t‖^(2 : ℕ) ≤ 1 := by simpa only [norm_pow] using hv
      gcongr
      · exact hP t
      · exact mul_le_of_le_one_right (norm_nonneg _) hv'
      · exact hP t

/-- The actual first derivative is uniformly bounded up to both original endpoints; no derivative phase is assumed. -/
theorem physicalCuspProfile_deriv_bounded (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, t < 0 →
      ‖deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t‖ ≤ D := by
  obtain ⟨C,hC,hP⟩ := physicalCuspProfile_bounded q r branch w a hw hd hwi hwr
  obtain ⟨M,hM,hS⟩ := physicalCuspSecond_bounded q r branch w a hw hd hwi hwr
  refine ⟨4*C+M,add_nonneg (mul_nonneg (by norm_num) hC) hM,fun t ht => ?_⟩
  exact norm_complex_deriv_le_of_bounded_negative
    (fun x hx => (physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr x hx).1)
    (fun x hx => (physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr x hx).2)
    (physicalCuspSecond_continuousOn q r branch w a hw hd hwi hwr)
    (fun x _ => hP x) hS t ht

end
end RHTower.D4BMJointSource
