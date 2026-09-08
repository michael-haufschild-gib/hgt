import GaloisForLFunctions.HTGeometry.FokasLenellsEndpointLipschitz
import GaloisForLFunctions.HTGeometry.FokasLenellsZeroScattering

/-!
# Global spectral Lipschitz bounds and linear zero-frequency vanishing

The endpoint comparison passes through the two-by-two scattering product.
For explicitly normalized potentials the transmission denominators are bounded
below by three quarters, so both genuine regularized reflection quotients are
globally Lipschitz. The exact zero-energy identity then forces both reflections
to vanish at least linearly at the origin. This is the missing cancellation
needed to differentiate the paper's singular time phase in L².
-/

open Complex Matrix MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem matrix_product_entry_bound (A B : Matrix (Fin 2) (Fin 2) ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (ha : ∀ i j, ‖A i j‖ ≤ C) (hb : ∀ i j, ‖B i j‖ ≤ D) (i j : Fin 2) :
    ‖(A*B) i j‖ ≤ 2*C*D := by
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  calc
    _ ≤ ‖A i 0‖*‖B 0 j‖+‖A i 1‖*‖B 1 j‖ := by simpa only [norm_mul] using norm_add_le (A i 0*B 0 j) (A i 1*B 1 j)
    _ ≤ C*D+C*D := add_le_add
      (mul_le_mul (ha i 0) (hb 0 j) (norm_nonneg _) hC)
      (mul_le_mul (ha i 1) (hb 1 j) (norm_nonneg _) hC)
    _ = _ := by ring

/-- Endpoint size and first moment give one global scattering frequency budget. -/
def scatteringFrequencyBudget (f g h : SchwartzMap ℝ ℂ) : ℝ :=
  4*(effectiveDisplacement f g h+1)*uniformizedFrequencyBudget f g h

theorem scatteringFrequencyBudget_nonneg (f g h : SchwartzMap ℝ ℂ) :
    0 ≤ scatteringFrequencyBudget f g h := by
  unfold scatteringFrequencyBudget
  exact mul_nonneg (mul_nonneg (by positivity) (by linarith [effectiveDisplacement_nonneg f g h]))
    (uniformizedFrequencyBudget_nonneg f g h)

/-- Every scattering entry is globally Lipschitz in real spectral frequency for arbitrary Schwartz profiles. -/
theorem uniformizedScatteringMatrix_entry_parameter_bound (f g h : SchwartzMap ℝ ℂ)
    (z w : ℝ) (i j : Fin 2) :
    ‖uniformizedScatteringMatrix f g h z i j-uniformizedScatteringMatrix f g h w i j‖ ≤
      scatteringFrequencyBudget f g h*|z-w| := by
  let Rz := uniformizedAsymptoticMatrix f g h z false
  let Rw := uniformizedAsymptoticMatrix f g h w false
  let Lz := (uniformizedAsymptoticMatrix f g h z true)⁻¹
  let Lw := (uniformizedAsymptoticMatrix f g h w true)⁻¹
  let K := uniformizedFrequencyBudget f g h*|z-w|
  let D := effectiveDisplacement f g h+1
  have hK : 0 ≤ K := mul_nonneg (uniformizedFrequencyBudget_nonneg f g h) (abs_nonneg (z-w))
  have hD : 0 ≤ D := by dsimp [D]; linarith [effectiveDisplacement_nonneg f g h]
  have he : uniformizedScatteringMatrix f g h z-uniformizedScatteringMatrix f g h w =
      (Rz-Rw)*Lz+Rw*(Lz-Lw) := by
    rw [sub_mul,mul_sub]
    change Rz*Lz-Rw*Lw = _
    abel
  have h0 := matrix_product_entry_bound (Rz-Rw) Lz K D hK
    (uniformizedAsymptoticMatrix_entry_parameter_bound f g h z w false)
    (uniformizedAsymptoticMatrix_inverse_entry_bound f g h z true) i j
  have h1 := matrix_product_entry_bound Rw (Lz-Lw) D K hD
    (uniformizedAsymptoticMatrix_entry_bound f g h w false)
    (uniformizedAsymptoticMatrix_inverse_entry_parameter_bound f g h z w true) i j
  change ‖(uniformizedScatteringMatrix f g h z-uniformizedScatteringMatrix f g h w) i j‖ ≤ _
  rw [he,Matrix.add_apply]
  calc
    _ ≤ 2*K*D+2*D*K := (norm_add_le _ _).trans (add_le_add h0 h1)
    _ = _ := by dsimp [K,D,scatteringFrequencyBudget]; ring

/-- The actual derivative profiles carry an explicit spectral comparison constant. -/
def regularScatteringFrequencyBudget (q : SchwartzMap ℝ ℂ) : ℝ :=
  scatteringFrequencyBudget (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))

theorem regularScatteringFrequencyBudget_nonneg (q : SchwartzMap ℝ ℂ) :
    0 ≤ regularScatteringFrequencyBudget q := scatteringFrequencyBudget_nonneg _ _ _

theorem regularScatteringMatrix_parameter_bound (q : SchwartzMap ℝ ℂ) (z w : ℝ) (i j : Fin 2) :
    ‖regularScatteringMatrix q z i j-regularScatteringMatrix q w i j‖ ≤
      regularScatteringFrequencyBudget q*|z-w| := uniformizedScatteringMatrix_entry_parameter_bound _ _ _ z w i j

/-- For every unscaled Schwartz potential the entire scattering matrix approaches the identity at least linearly. -/
theorem regularScatteringMatrix_zero_rate (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    ‖regularScatteringMatrix q z i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      regularScatteringFrequencyBudget q*|z| := by
  simpa only [regularScatteringMatrix_zero,sub_zero] using regularScatteringMatrix_parameter_bound q z 0 i j

private theorem quotient_difference_bound (a b c d : ℂ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ‖a-c‖ ≤ K) (hb : ‖b-d‖ ≤ K) (hc : ‖c‖ ≤ 1/4)
    (hbn : 3/4 ≤ ‖b‖) (hdn : 3/4 ≤ ‖d‖) :
    ‖a/b-c/d‖ ≤ (16/9 : ℝ)*K := by
  have hbpos : 0 < ‖b‖ := by linarith
  have hdpos : 0 < ‖d‖ := by linarith
  have hb0 := norm_pos_iff.mp hbpos
  have hd0 := norm_pos_iff.mp hdpos
  have he : a/b-c/d = (a-c)/b+c*((d-b)/(b*d)) := by field_simp [hb0,hd0]; ring
  have h0 : ‖(a-c)/b‖ ≤ (4/3 : ℝ)*K := by
    rw [norm_div]
    apply (div_le_iff₀ hbpos).mpr
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hbn)]
  have hnum : ‖c‖*‖d-b‖ ≤ (1/4 : ℝ)*K := by
    rw [norm_sub_rev]
    exact mul_le_mul hc hb (norm_nonneg _) (by positivity)
  have hden : (9/16 : ℝ) ≤ ‖b‖*‖d‖ := by
    have hh := mul_le_mul hbn hdn (by positivity : (0:ℝ) ≤ 3/4) (norm_nonneg b)
    nlinarith
  have h1 : ‖c*((d-b)/(b*d))‖ ≤ (4/9 : ℝ)*K := by
    rw [norm_mul,norm_div,norm_mul,← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hbpos hdpos)).mpr
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hden)]
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- The transmission gap fixes a global Lipschitz budget for the two normalized actual reflections. -/
def regularReflectionFrequencyBudget (q : SchwartzMap ℝ ℂ) : ℝ :=
  (16/9 : ℝ)*regularScatteringFrequencyBudget (globalSmallScatteringPotential q)

theorem regularReflectionFrequencyBudget_nonneg (q : SchwartzMap ℝ ℂ) :
    0 ≤ regularReflectionFrequencyBudget q :=
  mul_nonneg (by positivity) (regularScatteringFrequencyBudget_nonneg _)

/-- Both genuine normalized reflection quotients are globally Lipschitz, with no denominator hypothesis. -/
theorem globalSmall_regularReflection_parameter_bound (q : SchwartzMap ℝ ℂ) (z w : ℝ) :
    ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z-
      regularReflectionCoefficient (globalSmallScatteringPotential q) w‖ ≤ regularReflectionFrequencyBudget q*|z-w| ∧
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z-
      regularReverseReflectionCoefficient (globalSmallScatteringPotential q) w‖ ≤ regularReflectionFrequencyBudget q*|z-w| := by
  let K := regularScatteringFrequencyBudget (globalSmallScatteringPotential q)*|z-w|
  have hK : 0 ≤ K := mul_nonneg (regularScatteringFrequencyBudget_nonneg _) (abs_nonneg (z-w))
  have hn0 := globalSmall_regularScatteringMatrix_bound q w 1 0
  have hn1 := globalSmall_regularScatteringMatrix_bound q w 0 1
  simp only [Matrix.one_apply_ne (by norm_num : (1 : Fin 2) ≠ 0),
    Matrix.one_apply_ne (by norm_num : (0 : Fin 2) ≠ 1),sub_zero] at hn0 hn1
  have h0 := quotient_difference_bound _ _ _ _ K hK
    (regularScatteringMatrix_parameter_bound (globalSmallScatteringPotential q) z w 1 0)
    (regularScatteringMatrix_parameter_bound (globalSmallScatteringPotential q) z w 0 0) hn0
    (globalSmall_regularTransmission_lower q z).1 (globalSmall_regularTransmission_lower q w).1
  have h1 := quotient_difference_bound _ _ _ _ K hK
    (regularScatteringMatrix_parameter_bound (globalSmallScatteringPotential q) z w 0 1)
    (regularScatteringMatrix_parameter_bound (globalSmallScatteringPotential q) z w 1 1) hn1
    (globalSmall_regularTransmission_lower q z).2 (globalSmall_regularTransmission_lower q w).2
  constructor
  · simpa only [regularReflectionCoefficient,K,regularReflectionFrequencyBudget,mul_assoc] using h0
  · simpa only [regularReverseReflectionCoefficient,K,regularReflectionFrequencyBudget,mul_assoc] using h1

/-- Exact transparency at zero and global Lipschitz continuity force linear vanishing of both reflections. -/
theorem globalSmall_regularReflection_zero_rate (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularReflectionFrequencyBudget q*|z| ∧
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularReflectionFrequencyBudget q*|z| := by
  simpa only [(regularReflectionCoefficients_zero (globalSmallScatteringPotential q)).1,
    (regularReflectionCoefficients_zero (globalSmallScatteringPotential q)).2,sub_zero] using
    globalSmall_regularReflection_parameter_bound q z 0

end
end GaloisForLFunctions.HTGeometry.FokasLenells
