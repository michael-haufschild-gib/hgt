import GaloisForLFunctions.HTGeometry.FokasLenellsReflection

/-!
# Actual small-potential scattering and jump coercivity

This file carries the smallness mechanism of Propositions 3.2 and 3.4 of
Yan–Zhang–Zhu, arXiv:2607.19649v1, from a Schwartz potential through its
constructed Jost bases to its actual scattering quotients.

The explicit rescaling `smallScatteringPotential q K` is fixed throughout
the positive spectral band `0 < k ≤ exp K`, represented by `k = exp (K - |s|)`.
Its transmissions have modulus at least `3/4`, its two reflection quotients
have modulus at most `1/3`, and its jump energy has coercivity constant `5/9`.
Every smallness and nonvanishing condition is discharged by construction.

The estimates use the original spatial equation's coefficient mass. They
are uniform on this band, not the full-spectrum uniformized estimates in
the paper. No inverse-scattering reconstruction or nonlinear time evolution
is asserted here.
-/

open Complex Matrix MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Explicit displacement majorant, without a smallness premise. -/
def scatteringDisplacement (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℝ :=
  Real.exp (scatteringMass q κ)*scatteringMass q κ

theorem scatteringDisplacement_nonneg (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    0 ≤ scatteringDisplacement q κ :=
  mul_nonneg (Real.exp_pos _).le (scatteringMass_nonneg q κ)

theorem rightAsymptoticVector_displacement (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    ‖rightAsymptoticVector q κ v-v‖ ≤ ‖v‖*scatteringDisplacement q κ := by
  rw [rightAsymptoticVector, add_sub_cancel_left]
  have hc : 0 ≤ ‖v‖*Real.exp (scatteringMass q κ) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  calc
    ‖∫ x in Set.Ioi (0:ℝ), interactionDerivative q κ v x‖ ≤
        ∫ x in Set.Ioi (0:ℝ), (‖v‖*Real.exp (scatteringMass q κ))*scatteringDensity q κ x := by
      apply norm_integral_le_of_norm_le
        (((scatteringDensity_integrable q κ).const_mul _).integrableOn)
      filter_upwards with x
      calc
        ‖interactionDerivative q κ v x‖ ≤
            scatteringDensity q κ x*‖interactionSolution q κ v x‖ := interactionRate_bound _ _ _ _
        _ ≤ scatteringDensity q κ x*(‖v‖*Real.exp (scatteringMass q κ)) :=
          mul_le_mul_of_nonneg_left (interactionSolution_global_bound q κ v x)
            (scatteringDensity_nonneg q κ x)
        _ = _ := mul_comm _ _
    _ = (‖v‖*Real.exp (scatteringMass q κ))*∫ x in Set.Ioi (0:ℝ), scatteringDensity q κ x :=
      integral_const_mul _ _
    _ ≤ (‖v‖*Real.exp (scatteringMass q κ))*scatteringMass q κ := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact setIntegral_le_integral (scatteringDensity_integrable q κ)
        (Eventually.of_forall (scatteringDensity_nonneg q κ))
    _ = _ := by unfold scatteringDisplacement; ring

/-- Every entry of the right asymptotic basis lies within the explicit displacement of identity. -/
theorem rightAsymptoticMatrix_entry_displacement (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖rightAsymptoticMatrix q κ 0 0-1‖ ≤ scatteringDisplacement q κ ∧
    ‖rightAsymptoticMatrix q κ 1 0‖ ≤ scatteringDisplacement q κ ∧
    ‖rightAsymptoticMatrix q κ 0 1‖ ≤ scatteringDisplacement q κ ∧
    ‖rightAsymptoticMatrix q κ 1 1-1‖ ≤ scatteringDisplacement q κ := by
  have h0 := rightAsymptoticVector_displacement q κ (1,0)
  have h1 := rightAsymptoticVector_displacement q κ (0,1)
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, norm_one, norm_zero,
    max_eq_left (show (0:ℝ) ≤ 1 by positivity), max_eq_right (show (0:ℝ) ≤ 1 by positivity),
    one_mul, sub_zero] at h0 h1
  exact ⟨(max_le_iff.mp h0).1, (max_le_iff.mp h0).2,
    (max_le_iff.mp h1).1, (max_le_iff.mp h1).2⟩

/-- Reverse-space symmetry expresses all independent amplitudes quadratically in one endpoint basis. -/
theorem scattering_amplitudes_right_quadratic (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    transmission q κ = (rightAsymptoticMatrix q κ 0 0)^(2 : ℕ)-(rightAsymptoticMatrix q κ 0 1)^(2 : ℕ) ∧
    reverseTransmission q κ = (rightAsymptoticMatrix q κ 1 1)^(2 : ℕ)-(rightAsymptoticMatrix q κ 1 0)^(2 : ℕ) ∧
    reflectionAmplitude q κ = rightAsymptoticMatrix q κ 0 0*rightAsymptoticMatrix q κ 1 0-
      rightAsymptoticMatrix q κ 0 1*rightAsymptoticMatrix q κ 1 1 := by
  simp [transmission, reverseTransmission, reflectionAmplitude,
    scatteringMatrix_reflected_factorization, Matrix.inv_def, rightAsymptoticMatrix_det,
    Matrix.adjugate_fin_two, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ring
  constructor <;> ring

/-- Positive rescaling acts exactly on the coefficient mass. -/
theorem scatteringMass_smul (q : SchwartzMap ℝ ℂ) (κ : ℝ) (c : ℂ) :
    scatteringMass (c • q) κ = ‖c‖*scatteringMass q κ := by
  have hd : ∀ x, scatteringDensity (c • q) κ x = ‖c‖*scatteringDensity q κ x := by
    intro x
    simp [scatteringDensity, reflectedDerivative, RHTower.negSchwartz'_apply,
      SchwartzMap.derivCLM_apply]
    ring
  simp only [scatteringMass, hd, integral_const_mul]

/-- Simultaneous quantitative bounds on both transmissions and the reflection numerator. -/
theorem scattering_amplitudes_displacement (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖transmission q κ-1‖ ≤ scatteringDisplacement q κ*(2+2*scatteringDisplacement q κ) ∧
    ‖reverseTransmission q κ-1‖ ≤ scatteringDisplacement q κ*(2+2*scatteringDisplacement q κ) ∧
    ‖reflectionAmplitude q κ‖ ≤ scatteringDisplacement q κ*(2+2*scatteringDisplacement q κ) := by
  let δ := scatteringDisplacement q κ
  have hn : 0 ≤ δ := scatteringDisplacement_nonneg q κ
  rcases rightAsymptoticMatrix_entry_displacement q κ with ⟨h00,h10,h01,h11⟩
  rcases scattering_amplitudes_right_quadratic q κ with ⟨ha,hac,hb⟩
  have hdiag : ∀ a b : ℂ, ‖a-1‖ ≤ δ → ‖b‖ ≤ δ → ‖a^(2 : ℕ)-b^(2 : ℕ)-1‖ ≤ δ*(2+2*δ) := by
    intro a b h0 h1
    have ha1 : ‖a+1‖ ≤ δ+2 := by
      calc
        ‖a+1‖ = ‖(a-1)+(1+1)‖ := by congr 1; ring
        _ ≤ ‖a-1‖+‖(1:ℂ)+(1:ℂ)‖ := norm_add_le _ _
        _ ≤ δ+2 := by simpa only [norm_one, one_add_one_eq_two] using add_le_add h0 (norm_add_le (1:ℂ) 1)
    calc
      ‖a^(2 : ℕ)-b^(2 : ℕ)-1‖ = ‖(a-1)*(a+1)-b^(2 : ℕ)‖ := by congr 1; ring
      _ ≤ ‖a-1‖*‖a+1‖+‖b‖^(2 : ℕ) := by simpa only [pow_two, norm_mul] using norm_sub_le ((a-1)*(a+1)) (b*b)
      _ ≤ δ*(δ+2)+δ^(2 : ℕ) := by
        apply add_le_add (mul_le_mul h0 ha1 (norm_nonneg _) hn)
        nlinarith [norm_nonneg b]
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; exact hdiag _ _ h00 h01
  · rw [hac]; exact hdiag _ _ h11 h10
  · have hr00 : ‖rightAsymptoticMatrix q κ 0 0‖ ≤ δ+1 := by
      have h := norm_add_le (rightAsymptoticMatrix q κ 0 0-1) (1:ℂ)
      simp only [sub_add_cancel, norm_one] at h
      exact h.trans (add_le_add h00 le_rfl)
    have hr11 : ‖rightAsymptoticMatrix q κ 1 1‖ ≤ δ+1 := by
      have h := norm_add_le (rightAsymptoticMatrix q κ 1 1-1) (1:ℂ)
      simp only [sub_add_cancel, norm_one] at h
      exact h.trans (add_le_add h11 le_rfl)
    rw [hb]
    calc
      ‖rightAsymptoticMatrix q κ 0 0*rightAsymptoticMatrix q κ 1 0-
          rightAsymptoticMatrix q κ 0 1*rightAsymptoticMatrix q κ 1 1‖ ≤
        ‖rightAsymptoticMatrix q κ 0 0‖*‖rightAsymptoticMatrix q κ 1 0‖+
          ‖rightAsymptoticMatrix q κ 0 1‖*‖rightAsymptoticMatrix q κ 1 1‖ := by
        simpa only [norm_mul] using norm_sub_le
          (rightAsymptoticMatrix q κ 0 0*rightAsymptoticMatrix q κ 1 0)
          (rightAsymptoticMatrix q κ 0 1*rightAsymptoticMatrix q κ 1 1)
      _ ≤ (δ+1)*δ+δ*(δ+1) := add_le_add
        (mul_le_mul hr00 h10 (norm_nonneg _) (by positivity))
        (mul_le_mul h01 hr11 (norm_nonneg _) hn)
      _ = _ := by ring

/-- A fixed potential is controlled throughout the positive spectral band `k ≤ exp K`. -/
theorem scatteringMass_lower_band (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    scatteringMass q (K-|s|) ≤ scatteringMass q K := by
  apply integral_mono (scatteringDensity_integrable q (K-|s|)) (scatteringDensity_integrable q K)
  intro x
  unfold scatteringDensity
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (sub_le_self _ (abs_nonneg _)))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

def smallScatteringScale (q : SchwartzMap ℝ ℂ) (K : ℝ) : ℝ :=
  (16*(1+scatteringMass q K)*Real.exp 1)⁻¹

def smallScatteringPotential (q : SchwartzMap ℝ ℂ) (K : ℝ) : SchwartzMap ℝ ℂ :=
  (smallScatteringScale q K : ℂ) • q

theorem smallScatteringScale_pos (q : SchwartzMap ℝ ℂ) (K : ℝ) :
    0 < smallScatteringScale q K := by
  have h := scatteringMass_nonneg q K
  unfold smallScatteringScale
  positivity

/-- The same rescaled potential satisfies the mass estimate everywhere in the band. -/
theorem smallScatteringPotential_mass (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    scatteringMass (smallScatteringPotential q K) (K-|s|) ≤ 1/(16*Real.exp 1) := by
  rw [smallScatteringPotential, scatteringMass_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (smallScatteringScale_pos q K)]
  have hm := scatteringMass_nonneg q K
  calc
    smallScatteringScale q K*scatteringMass q (K-|s|) ≤
        smallScatteringScale q K*scatteringMass q K :=
      mul_le_mul_of_nonneg_left (scatteringMass_lower_band q K s) (smallScatteringScale_pos q K).le
    _ = (scatteringMass q K/(1+scatteringMass q K))/(16*Real.exp 1) := by
      unfold smallScatteringScale
      field_simp
    _ ≤ 1/(16*Real.exp 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (div_le_one (by positivity)).mpr
      linarith

theorem smallScatteringPotential_displacement (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    scatteringDisplacement (smallScatteringPotential q K) (K-|s|) ≤ 1/16 := by
  have hm := smallScatteringPotential_mass q K s
  have hn := scatteringMass_nonneg (smallScatteringPotential q K) (K-|s|)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 1/(16*Real.exp 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  unfold scatteringDisplacement
  calc
    Real.exp (scatteringMass (smallScatteringPotential q K) (K-|s|))*
        scatteringMass (smallScatteringPotential q K) (K-|s|) ≤
      Real.exp 1*(1/(16*Real.exp 1)) :=
        mul_le_mul (Real.exp_le_exp.mpr (hm.trans hb)) hm hn (Real.exp_pos _).le
    _ = 1/16 := by field_simp

/-- Closed quantitative transmission and reflection estimates, uniform on the spectral band. -/
theorem smallScatteringPotential_amplitudes (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    ‖transmission (smallScatteringPotential q K) (K-|s|)-1‖ ≤ 1/4 ∧
    ‖reverseTransmission (smallScatteringPotential q K) (K-|s|)-1‖ ≤ 1/4 ∧
    ‖reflectionAmplitude (smallScatteringPotential q K) (K-|s|)‖ ≤ 1/4 := by
  have h := scattering_amplitudes_displacement (smallScatteringPotential q K) (K-|s|)
  have hd := smallScatteringPotential_displacement q K s
  have hn := scatteringDisplacement_nonneg (smallScatteringPotential q K) (K-|s|)
  have hb : scatteringDisplacement (smallScatteringPotential q K) (K-|s|)*
      (2+2*scatteringDisplacement (smallScatteringPotential q K) (K-|s|)) ≤ 1/4 := by
    nlinarith
  exact ⟨h.1.trans hb,h.2.1.trans hb,h.2.2.trans hb⟩

/-- Both actual transmissions stay uniformly separated from zero on the band. -/
theorem smallScatteringPotential_transmission_lower (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    3/4 ≤ ‖transmission (smallScatteringPotential q K) (K-|s|)‖ ∧
    3/4 ≤ ‖reverseTransmission (smallScatteringPotential q K) (K-|s|)‖ := by
  have h := smallScatteringPotential_amplitudes q K s
  have h1 := norm_sub_norm_le (1:ℂ) (transmission (smallScatteringPotential q K) (K-|s|))
  have h2 := norm_sub_norm_le (1:ℂ) (reverseTransmission (smallScatteringPotential q K) (K-|s|))
  rw [norm_one, norm_sub_rev] at h1 h2
  constructor <;> linarith [h.1, h.2.1]

theorem smallScatteringPotential_transmission_nonzero (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    transmission (smallScatteringPotential q K) (K-|s|) ≠ 0 ∧
    reverseTransmission (smallScatteringPotential q K) (K-|s|) ≠ 0 := by
  have h := smallScatteringPotential_transmission_lower q K s
  constructor <;> apply norm_pos_iff.mp <;> linarith [h.1,h.2]

/-- The two quotients in equation (2.67), formed from the constructed scattering matrix. -/
def reflectionCoefficient (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ :=
  reflectionAmplitude q κ/transmission q κ

def reverseReflectionCoefficient (q : SchwartzMap ℝ ℂ) (κ : ℝ) : ℂ :=
  reverseReflectionAmplitude q κ/reverseTransmission q κ

/-- An unconditional spectral-band version of the mechanism in Proposition 3.2. -/
theorem smallScatteringPotential_reflection_bounds (q : SchwartzMap ℝ ℂ) (K s : ℝ) :
    ‖reflectionCoefficient (smallScatteringPotential q K) (K-|s|)‖ ≤ 1/3 ∧
    ‖reverseReflectionCoefficient (smallScatteringPotential q K) (K-|s|)‖ ≤ 1/3 := by
  have hl := smallScatteringPotential_transmission_lower q K s
  have ha := (smallScatteringPotential_amplitudes q K s).2.2
  constructor
  · rw [reflectionCoefficient, norm_div]
    apply (div_le_iff₀ (by linarith [hl.1])).mpr
    linarith [hl.1]
  · rw [reverseReflectionCoefficient, norm_div, reverseReflectionAmplitude_eq_neg, norm_neg]
    apply (div_le_iff₀ (by linarith [hl.2])).mpr
    linarith [hl.2]

/-- A norm-only lower bound for the Hermitian jump energy, useful without any reduction symmetry. -/
theorem energy_norm_lower_bound (a b u v : ℂ) :
    (1-(‖a‖+‖b‖)/2)*normSq u +
      (1-‖a‖*‖b‖-(‖a‖+‖b‖)/2)*normSq v ≤ energy a b u v := by
  let e := star u*b*v-star v*a*u-star v*a*b*v
  have he : energy a b u v = normSq u+normSq v+e.re := by
    simp [energy, e, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hr : -‖e‖ ≤ e.re := (abs_le.mp (Complex.abs_re_le_norm e)).1
  have hn : ‖e‖ ≤ ‖b‖*‖u‖*‖v‖+‖a‖*‖u‖*‖v‖+‖a‖*‖b‖*‖v‖^(2 : ℕ) := by
    calc
      ‖e‖ ≤ ‖star u*b*v-star v*a*u‖+‖star v*a*b*v‖ := norm_sub_le _ _
      _ ≤ ‖star u*b*v‖+‖star v*a*u‖+‖star v*a*b*v‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = _ := by simp only [norm_mul, norm_star]; ring
  rw [he, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))
    (sq_nonneg (‖u‖-‖v‖))]

/-- The actual non-Hermitian scattering jump has a uniform positive energy floor. -/
theorem smallScatteringPotential_jump_coercivity (q : SchwartzMap ℝ ℂ) (K s : ℝ) (u v : ℂ) :
    (5/9 : ℝ)*(normSq u+normSq v) ≤
      energy (reflectionCoefficient (smallScatteringPotential q K) (K-|s|))
        (reverseReflectionCoefficient (smallScatteringPotential q K) (K-|s|)) u v := by
  let a := reflectionCoefficient (smallScatteringPotential q K) (K-|s|)
  let b := reverseReflectionCoefficient (smallScatteringPotential q K) (K-|s|)
  have h := smallScatteringPotential_reflection_bounds q K s
  have ha : ‖a‖ ≤ 1/3 := h.1
  have hb : ‖b‖ ≤ 1/3 := h.2
  have hab : ‖a‖*‖b‖ ≤ 1/9 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1/3-‖a‖) (norm_nonneg b)]
  have h1 : 5/9 ≤ 1-(‖a‖+‖b‖)/2 := by linarith
  have h2 : 5/9 ≤ 1-‖a‖*‖b‖-(‖a‖+‖b‖)/2 := by linarith
  calc
    (5/9 : ℝ)*(normSq u+normSq v) = (5/9 : ℝ)*normSq u+(5/9 : ℝ)*normSq v := by ring
    _ ≤ (1-(‖a‖+‖b‖)/2)*normSq u+(1-‖a‖*‖b‖-(‖a‖+‖b‖)/2)*normSq v :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (normSq_nonneg u))
        (mul_le_mul_of_nonneg_right h2 (normSq_nonneg v))
    _ ≤ _ := energy_norm_lower_bound a b u v

end
end GaloisForLFunctions.HTGeometry.FokasLenells
