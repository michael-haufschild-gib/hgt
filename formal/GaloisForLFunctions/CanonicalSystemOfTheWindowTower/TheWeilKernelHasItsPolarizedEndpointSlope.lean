import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheEvaluationGramsHaveTheirEndpointSlope
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Polarized endpoint slopes of the precontact Weil kernel

Four finite evaluation Grams polarize to the actual complex reproducing
kernel. Their exact two-trace slopes and integral identities yield the
polarized density, absolute continuity, and the ordinary derivative
almost everywhere on compact precontact intervals.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open CanonicalSystemOfTheWindowTower
open CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact


private def kernelPolarizationCoeff (c : ℂ) : Fin 2 → ℂ := ![1,c]
private def kernelPolarizationPoints (w z : ℂ) : Fin 2 → ℂ := ![z,w]

private theorem kernelPolarization_combination (a : PrecontactAperture) (w z c : ℂ) :
    evalCombination (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) a =
      evalVector a z + c • evalVector a w := by
  simp [evalCombination, kernelPolarizationCoeff, kernelPolarizationPoints, Fin.sum_univ_two]

/-- The literal Weil kernel in the real aperture coordinate, extended by zero outside precontact. -/
def precontactKernel (w z : ℂ) (a : ℝ) : ℂ :=
  open Classical in
  if h : a ∈ precontactSet then kernel (toPrecontact h) w z else 0

/-- The polarized product of the two actual endpoint traces, extended by zero outside precontact. -/
def precontactKernelEndpointDensity (w z : ℂ) (a : ℝ) : ℂ :=
  open Classical in
  if h : a ∈ precontactSet then
    (starRingEnd ℂ) (evalLeftEndpointTrace (toPrecontact h) z)*evalLeftEndpointTrace (toPrecontact h) w+
    (starRingEnd ℂ) (evalRightEndpointTrace (toPrecontact h) z)*evalRightEndpointTrace (toPrecontact h) w
  else 0

private def kernelPolarization (G : ℂ → ℝ) : ℂ :=
  ((G 1 : ℂ)-G (-1)+((G (-I) : ℂ)-G I)*I)/4

/-- The real diagonal is the previously defined evaluation Gram. -/
theorem precontactKernel_diagonal_re (z : ℂ) (a : ℝ) :
    (precontactKernel z z a).re = diagonalEvalGram z a := by
  by_cases ha : a ∈ precontactSet
  · rw [precontactKernel, dif_pos ha]
    exact (diagonalEvalGram_eq_kernel z (toPrecontact ha)).symm
  · simp only [precontactKernel, diagonalEvalGram, evalGram, dif_neg ha, Complex.zero_re]

/-- The real diagonal density is the actual endpoint energy. -/
theorem precontactKernelEndpointDensity_diagonal_re (z : ℂ) (a : ℝ) :
    (precontactKernelEndpointDensity z z a).re = diagonalEndpointEnergy z a := by
  have hn (v : ℂ) : ((starRingEnd ℂ) v*v).re = ‖v‖^2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  by_cases ha : a ∈ precontactSet
  · simp only [precontactKernelEndpointDensity, diagonalEndpointEnergy, dif_pos ha, Complex.add_re, hn]
    rfl
  · simp only [precontactKernelEndpointDensity, diagonalEndpointEnergy, dif_neg ha, Complex.zero_re]

private theorem kernelPolarization_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) : kernelPolarization (fun c => ‖x+c • y‖^2) = inner ℂ x y := by
  have hi : (RCLike.I : ℂ) = I := rfl
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [kernelPolarization, hi, one_smul, neg_smul, sub_eq_add_neg, Complex.ofReal_pow]
  rfl

private theorem precontactKernel_polarization (w z : ℂ) (a : ℝ) :
    precontactKernel w z a = kernelPolarization (fun c => evalGram (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) a) := by
  by_cases ha : a ∈ precontactSet
  · simp only [precontactKernel, evalGram, dif_pos ha, kernelPolarization_combination]
    rw [kernelPolarization_norm, inner_evalVector]
    rfl
  · simp only [precontactKernel, evalGram, dif_neg ha, kernelPolarization, Complex.ofReal_zero,
      sub_self, zero_mul, add_zero, zero_div]

private theorem kernelPolarization_energy (a : PrecontactAperture) (w z c : ℂ) :
    evalCombinationEndpointEnergy (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) a =
      ‖evalLeftEndpointTrace a z+c*evalLeftEndpointTrace a w‖^2+
      ‖evalRightEndpointTrace a z+c*evalRightEndpointTrace a w‖^2 := by
  simp [evalCombinationEndpointEnergy, kernelPolarizationCoeff, kernelPolarizationPoints, Fin.sum_univ_two]

private theorem precontactKernelEndpointDensity_polarization (w z : ℂ) (a : ℝ) :
    precontactKernelEndpointDensity w z a =
      kernelPolarization (fun c => evalGramEndpointEnergy (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) a) := by
  by_cases ha : a ∈ precontactSet
  · simp only [precontactKernelEndpointDensity, evalGramEndpointEnergy, dif_pos ha, kernelPolarization_energy]
    have hl := kernelPolarization_norm (evalLeftEndpointTrace (toPrecontact ha) z)
      (evalLeftEndpointTrace (toPrecontact ha) w)
    have hr := kernelPolarization_norm (evalRightEndpointTrace (toPrecontact ha) z)
      (evalRightEndpointTrace (toPrecontact ha) w)
    simp only [kernelPolarization, smul_eq_mul, RCLike.inner_apply] at hl hr ⊢
    push_cast at hl hr ⊢
    linear_combination -hl-hr
  · simp only [precontactKernelEndpointDensity, evalGramEndpointEnergy, dif_neg ha, kernelPolarization,
      Complex.ofReal_zero, sub_self, zero_mul, add_zero, zero_div]

/-- At every precontact aperture the complex kernel has its polarized endpoint derivative from the right. -/
theorem hasDerivWithinAt_precontactKernel_right (w z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    HasDerivWithinAt (precontactKernel w z) (precontactKernelEndpointDensity w z a) (Ioi a) a := by
  have hd (c : ℂ) := (hasDerivWithinAt_evalGram_right (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) ha).ofReal_comp
  have h := (((hd 1).sub (hd (-1))).add (((hd (-I)).sub (hd I)).mul_const I)).div_const 4
  rw [show precontactKernel w z = fun x => kernelPolarization (fun c => evalGram (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) x)
    from funext (precontactKernel_polarization w z), precontactKernelEndpointDensity_polarization]
  exact h

private theorem ac_complexification {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => (f x : ℂ)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using hf

/-- Every polarized kernel entry is absolutely continuous on compact precontact intervals. -/
theorem absolutelyContinuousOnInterval_precontactKernel (w z : ℂ) {a b : ℝ} (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (precontactKernel w z) a b := by
  have hc (c : ℂ) := ac_complexification
    (absolutelyContinuousOnInterval_evalGram (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) hab hs)
  have h := (((hc 1).sub (hc (-1))).add
    (((hc (-I)).sub (hc I)).const_smul I)).const_smul (1/4 : ℂ)
  have he : precontactKernel w z = fun x => (1/4 : ℂ) •
      (((evalGram (kernelPolarizationCoeff 1) (kernelPolarizationPoints w z) x : ℂ)-
        (evalGram (kernelPolarizationCoeff (-1)) (kernelPolarizationPoints w z) x : ℂ))+
      I • ((evalGram (kernelPolarizationCoeff (-I)) (kernelPolarizationPoints w z) x : ℂ)-
        (evalGram (kernelPolarizationCoeff I) (kernelPolarizationPoints w z) x : ℂ))) := by
    funext x
    rw [precontactKernel_polarization]
    simp only [kernelPolarization, smul_eq_mul]
    ring
  rw [he]
  exact h

private theorem kernelPolarization_energy_integrable (w z c : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (fun x => (evalGramEndpointEnergy (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) x : ℂ))
      volume a b := by
  have hi := (integral_evalGramEndpointEnergy_eq_sub (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) hab hs).1
  simpa only [Complex.real_smul, mul_one] using
    hi.smul_continuousOn (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (uIcc a b))

/-- The actual polarized trace density is integrable on every compact precontact interval. -/
theorem intervalIntegrable_precontactKernelEndpointDensity (w z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (precontactKernelEndpointDensity w z) volume a b := by
  have hi (c : ℂ) := kernelPolarization_energy_integrable w z c hab hs
  rw [show precontactKernelEndpointDensity w z = fun x =>
      kernelPolarization (fun c => evalGramEndpointEnergy (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) x)
    from funext (precontactKernelEndpointDensity_polarization w z)]
  exact (((hi 1).sub (hi (-1))).add (((hi (-I)).sub (hi I)).mul_const I)).div_const 4

/-- Integrating the actual polarized endpoint density recovers the exact kernel increment. -/
theorem integral_precontactKernelEndpointDensity (w z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    (∫ x in a..b, precontactKernelEndpointDensity w z x) = precontactKernel w z b-precontactKernel w z a := by
  have hi (c : ℂ) := kernelPolarization_energy_integrable w z c hab hs
  have he (c : ℂ) := (integral_evalGramEndpointEnergy_eq_sub
    (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) hab hs).2
  rw [show precontactKernelEndpointDensity w z = fun x =>
      kernelPolarization (fun c => evalGramEndpointEnergy (kernelPolarizationCoeff c) (kernelPolarizationPoints w z) x)
    from funext (precontactKernelEndpointDensity_polarization w z)]
  simp only [kernelPolarization]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add ((hi 1).sub (hi (-1))) (((hi (-I)).sub (hi I)).mul_const I),
    intervalIntegral.integral_sub (hi 1) (hi (-1)), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (hi (-I)) (hi I)]
  simp only [intervalIntegral.integral_ofReal, he, Complex.ofReal_sub]
  rw [precontactKernel_polarization, precontactKernel_polarization]
  unfold kernelPolarization
  ring

/-- The ordinary aperture derivative equals the actual polarized trace density almost everywhere. -/
theorem ae_hasDerivAt_precontactKernel (w z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    ∀ᵐ x : ℝ, x ∈ Ioo a b → HasDerivAt (precontactKernel w z) (precontactKernelEndpointDensity w z x) x := by
  have hd := (intervalIntegrable_precontactKernelEndpointDensity w z hab hs).ae_hasDerivAt_integral
  filter_upwards [hd] with x hx hxI
  have hxi : x ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ⟨hxI.1.le,hxI.2.le⟩
  have hai : a ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ⟨le_rfl,hab⟩
  have h := (hx hxi a hai).const_add (precontactKernel w z a)
  apply h.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hxI.1 hxI.2] with t ht
  rw [integral_precontactKernelEndpointDensity w z ht.1 (fun y hy => hs ⟨hy.1,hy.2.trans ht.2⟩)]
  ring

#print axioms hasDerivWithinAt_precontactKernel_right
#print axioms absolutelyContinuousOnInterval_precontactKernel
#print axioms intervalIntegrable_precontactKernelEndpointDensity
#print axioms integral_precontactKernelEndpointDensity
#print axioms ae_hasDerivAt_precontactKernel
end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
