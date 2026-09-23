import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResolventEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResolventBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBoundedRadialUniqueness
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseGreenIdentification

/-! Exact resolvent identification for the original complete physical response, with angular collisions retained. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The denominator-cleared finite response is the actual original physical response times the exact gap product.
No angular noncollision, replacement response, endpoint or derivative-bound premise is supplied. -/
theorem physicalCuspProfile_mul_gapProduct (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    physicalAngularGapProduct q r*physicalCuspProfile q r branch w a hw hd hwi hwr t =
      clearedPhysicalGreen q r branch w a t := by
  let P := physicalCuspProfile q r branch w a hw hd hwi hwr
  let D := physicalAngularGapProduct q r
  let R := clearedPhysicalGreen q r branch w a
  let f : ℝ → ℂ := fun x => D*P x-R x
  let g : ℝ → ℂ := fun x => D*deriv P x-clearedPhysicalGreenFirst q r branch w a x
  have hP (x : ℝ) (hx : x < 0) := physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr x hx
  have hR (x : ℝ) (hx : x < 0) := clearedPhysicalGreen_hasDerivAt q r branch w a hwi (by linarith) x hx
  have hf (x : ℝ) (hx : x < 0) : HasDerivAt f (g x) x :=
    ((hP x hx).1.const_mul D).sub (hR x hx).1
  have hg (x : ℝ) (hx : x < 0) :
      HasDerivAt g ((w^(2 : ℕ)+(horizonCoordinate x:ℂ)*(1/4+physicalRadialFrequency r^(2 : ℕ)))*f x) x := by
    apply (((hP x hx).2.const_mul D).sub (hR x hx).2).congr_deriv
    have he := clearedPhysicalGreen_equation q r branch w a hd hwi x hx
    dsimp only [f,g,P,D,R,physicalCuspSecond]
    rw [physicalRadialFrequency_parameter,horizonCoordinate_jointWeight x hx] at he ⊢
    linear_combination he
  have hzero : Tendsto f (𝓝[<] (0:ℝ)) (𝓝 0) := by
    simpa only [f,P,R,mul_zero,sub_zero] using!
      ((physicalCuspProfile_boundary q r branch w a hw hd hwi hwr).const_mul D).sub
        (clearedPhysicalGreen_boundary q r branch w a hd hwi)
  obtain ⟨C,hC,hPb⟩ := physicalCuspProfile_bounded q r branch w a hw hd hwi hwr
  obtain ⟨B,hB,hRb⟩ := clearedPhysicalGreen_bounded q r branch w a hd hwi
  have hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x < 0, ‖f x‖ ≤ K := by
    refine ⟨‖D‖*C+B,add_nonneg (mul_nonneg (norm_nonneg _) hC) hB,fun x hx => ?_⟩
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hPb x) (norm_nonneg _)) (hRb x hx)
  have hz := bounded_radial_homogeneous_eq_zero (physicalRadialFrequency_chamber r w (by linarith))
    hf hg hbound hzero t ht
  exact sub_eq_zero.mp hz

end
end RHTower.D4BMJointSource
