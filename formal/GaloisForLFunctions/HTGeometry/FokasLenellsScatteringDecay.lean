import GaloisForLFunctions.HTGeometry.FokasLenellsOrbitDecay

/-!
# Spectral decay of genuine regularized Fokas–Lenells reflection data

Each off-diagonal scattering entry is a sum of products containing exactly
one off-diagonal endpoint entry. The proved endpoint frequency bound and
the bounded diagonal entries therefore give reciprocal decay of both
uniformized reflection numerators. The explicitly normalized potentials
have transmission norm at least three quarters, so both actual reflection
quotients inherit a global envelope `C/(1+|z|)`. This is the square-integrable
part of the regularity mechanism used in arXiv:2607.19649v1.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def uniformizedOffDiagonal (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) : ℂ :=
  uniformizedScatteringMatrix f g h z (if upper then 0 else 1) (if upper then 1 else 0)

/-- Each reflection numerator is a difference of one off-diagonal and one bounded diagonal endpoint product. -/
theorem uniformizedOffDiagonal_eq (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    uniformizedOffDiagonal f g h z upper =
      offOrbitEndpoint f g h z false upper*
        uniformizedAsymptoticMatrix f g h z true (if upper then 0 else 1) (if upper then 0 else 1)-
      uniformizedAsymptoticMatrix f g h z false (if upper then 0 else 1) (if upper then 0 else 1)*
        offOrbitEndpoint f g h z true upper := by
  cases upper <;>
    simp [uniformizedOffDiagonal, uniformizedScatteringMatrix, Matrix.inv_def,
      uniformizedAsymptoticMatrix_det, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, offOrbitEndpoint] <;> ring

def uniformizedOffDiagonalDecay (f g h : SchwartzMap ℝ ℂ) (upper : Bool) : ℝ :=
  (offOrbitDecayConstant f g h false upper+offOrbitDecayConstant f g h true upper)*
    (effectiveDisplacement f g h+1)

theorem uniformizedOffDiagonalDecay_nonneg (f g h : SchwartzMap ℝ ℂ) (upper : Bool) :
    0 ≤ uniformizedOffDiagonalDecay f g h upper := by
  unfold uniformizedOffDiagonalDecay
  exact mul_nonneg (add_nonneg (offOrbitDecayConstant_nonneg f g h false upper)
    (offOrbitDecayConstant_nonneg f g h true upper)) (by linarith [effectiveDisplacement_nonneg f g h])

/-- The actual uniformized reflection numerators lose one spectral power. -/
theorem uniformizedOffDiagonal_frequency_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    |z| * ‖uniformizedOffDiagonal f g h z upper‖ ≤ uniformizedOffDiagonalDecay f g h upper := by
  let i : Fin 2 := if upper then 0 else 1
  have hr := offOrbitEndpoint_frequency_bound f g h z false upper
  have hl := offOrbitEndpoint_frequency_bound f g h z true upper
  have hrd := uniformizedAsymptoticMatrix_entry_bound f g h z false i i
  have hld := uniformizedAsymptoticMatrix_entry_bound f g h z true i i
  have hpos : 0 ≤ effectiveDisplacement f g h+1 := by linarith [effectiveDisplacement_nonneg f g h]
  rw [uniformizedOffDiagonal_eq]
  calc
    _ ≤ |z| * (‖offOrbitEndpoint f g h z false upper‖*‖uniformizedAsymptoticMatrix f g h z true i i‖+
        ‖uniformizedAsymptoticMatrix f g h z false i i‖*‖offOrbitEndpoint f g h z true upper‖) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg z)
      simpa only [norm_mul] using norm_sub_le
        (offOrbitEndpoint f g h z false upper*uniformizedAsymptoticMatrix f g h z true i i)
        (uniformizedAsymptoticMatrix f g h z false i i*offOrbitEndpoint f g h z true upper)
    _ = (|z| * ‖offOrbitEndpoint f g h z false upper‖)*‖uniformizedAsymptoticMatrix f g h z true i i‖+
        ‖uniformizedAsymptoticMatrix f g h z false i i‖*(|z| * ‖offOrbitEndpoint f g h z true upper‖) := by ring
    _ ≤ offOrbitDecayConstant f g h false upper*(effectiveDisplacement f g h+1)+
        (effectiveDisplacement f g h+1)*offOrbitDecayConstant f g h true upper :=
      add_le_add (mul_le_mul hr hld (norm_nonneg _) (offOrbitDecayConstant_nonneg f g h false upper))
        (mul_le_mul hrd hl (by positivity) hpos)
    _ = _ := by unfold uniformizedOffDiagonalDecay; ring

/-- Both regularized reflection numerators also have a frequency-independent bound. -/
theorem uniformizedOffDiagonal_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    ‖uniformizedOffDiagonal f g h z upper‖ ≤
      4*effectiveDisplacement f g h*(1+effectiveDisplacement f g h) := by
  have hb := uniformizedScatteringMatrix_entry_displacement f g h z
    (if upper then 0 else 1) (if upper then 1 else 0)
  cases upper <;> simpa [uniformizedOffDiagonal] using hb

theorem uniformizedOffDiagonal_reciprocal_bound (f g h : SchwartzMap ℝ ℂ) (z : ℝ) (upper : Bool) :
    ‖uniformizedOffDiagonal f g h z upper‖ ≤
      (4*effectiveDisplacement f g h*(1+effectiveDisplacement f g h)+
        uniformizedOffDiagonalDecay f g h upper)/(1+|z|) := by
  apply (le_div_iff₀ (by positivity)).mpr
  have h0 := uniformizedOffDiagonal_bound f g h z upper
  have h1 := uniformizedOffDiagonal_frequency_bound f g h z upper
  nlinarith

def regularReflectionDecay (q : SchwartzMap ℝ ℂ) (upper : Bool) : ℝ :=
  (4/3 : ℝ)*uniformizedOffDiagonalDecay (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) upper

theorem regularReflectionDecay_nonneg (q : SchwartzMap ℝ ℂ) (upper : Bool) :
    0 ≤ regularReflectionDecay q upper :=
  mul_nonneg (by positivity) (uniformizedOffDiagonalDecay_nonneg _ _ _ _)

/-- The explicitly proved transmission lower bound preserves decay in both quotients. -/
theorem globalSmall_regularReflection_frequency_bound (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    |z| * ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularReflectionDecay q false ∧
    |z| * ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularReflectionDecay q true := by
  have hl := globalSmall_regularTransmission_lower q z
  have hb (upper : Bool) := uniformizedOffDiagonal_frequency_bound
    (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) z upper
  have hn (upper : Bool) := uniformizedOffDiagonalDecay_nonneg
    (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) upper
  constructor
  · rw [regularReflectionCoefficient, norm_div, ← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [hl.1])).mpr
    have hbf := hb false
    change |z| * ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 1 0‖ ≤ _ at hbf
    unfold regularReflectionDecay
    nlinarith [mul_nonneg (hn false) (by linarith : 0 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 0 0‖-3/4)]
  · rw [regularReverseReflectionCoefficient, norm_div, ← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [hl.2])).mpr
    have hbt := hb true
    change |z| * ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 0 1‖ ≤ _ at hbt
    unfold regularReflectionDecay
    nlinarith [mul_nonneg (hn true) (by linarith : 0 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 1 1‖-3/4)]

/-- A global reciprocal envelope supplies square-integrability of the actual regularized reflection data. -/
theorem globalSmall_regularReflection_reciprocal_bound (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤
      (1/3+regularReflectionDecay q false)/(1+|z|) ∧
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤
      (1/3+regularReflectionDecay q true)/(1+|z|) := by
  have h0 := globalSmall_regularReflection_bounds q z
  have h1 := globalSmall_regularReflection_frequency_bound q z
  constructor <;> apply (le_div_iff₀ (by positivity)).mpr <;> nlinarith [h0.1,h0.2,h1.1,h1.2]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
