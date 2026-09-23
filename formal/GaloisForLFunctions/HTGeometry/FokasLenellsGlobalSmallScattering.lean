import GaloisForLFunctions.HTGeometry.FokasLenellsGaugeScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsSpaceTimeJump

/-!
# One explicit potential normalization for the entire positive spectrum

The smallness mechanism of Propositions 3.2 and 3.4 of Yan–Zhang–Zhu,
arXiv:2607.19649v1, is now applied to the actual original scattering data
without a bounded spectral band. A positive polynomial majorant controls
the linear, quadratic and cubic terms in the effective potential. One fixed
rescaling of each Schwartz potential makes the uniformized scattering error
at most `1/4`. Nonzero potentials remain nonzero.

Both transmissions have modulus at least `3/4` and both reflection quotients
have modulus at most `1/3` for every positive original spectral parameter.
The `5/9` jump-energy bound then persists at every real position and every
prescribed scattering time. All smallness and nonvanishing conditions are
proved by construction. Imaginary spectral rays, analytic continuation and
nonlinear inverse-scattering reconstruction are not asserted here.
-/

open Complex Matrix MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- A positive polynomial majorant prevents cancellation in the effective potential from hiding size. -/
def effectiveControlDensity (f g h : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ :=
  ‖mulS f g x‖+‖g x‖+‖h x‖+‖mulS (mulS f f) g x‖

theorem effectiveControlDensity_nonneg (f g h : SchwartzMap ℝ ℂ) (x : ℝ) :
    0 ≤ effectiveControlDensity f g h x := by unfold effectiveControlDensity; positivity

theorem effectiveControlDensity_integrable (f g h : SchwartzMap ℝ ℂ) :
    Integrable (effectiveControlDensity f g h) :=
  ((((mulS f g).integrable.norm.add g.integrable.norm).add h.integrable.norm).add
    (mulS (mulS f f) g).integrable.norm)

theorem effectiveDensity_le_control (f g h : SchwartzMap ℝ ℂ) (x : ℝ) :
    effectiveDensity f g h x ≤ effectiveControlDensity f g h x := by
  have hn := norm_add_le (h x) ((I/2)*(f x*f x*g x))
  simp only [norm_mul, norm_div, norm_I, Complex.norm_two] at hn
  simp [effectiveDensity, effectiveSchwartzEntries, effectiveControlDensity]
  nlinarith [norm_nonneg (f x), norm_nonneg (g x), norm_nonneg (h x),
    mul_nonneg (sq_nonneg ‖f x‖) (norm_nonneg (g x))]

def effectiveControlMass (f g h : SchwartzMap ℝ ℂ) : ℝ := ∫ x, effectiveControlDensity f g h x

theorem effectiveControlMass_nonneg (f g h : SchwartzMap ℝ ℂ) : 0 ≤ effectiveControlMass f g h :=
  integral_nonneg (effectiveControlDensity_nonneg f g h)

/-- Simultaneous rescaling has exactly linear, quadratic and cubic contributions. -/
theorem effectiveControlDensity_smul (f g h : SchwartzMap ℝ ℂ) (c : ℂ) (x : ℝ) :
    effectiveControlDensity (c • f) (c • g) (c • h) x =
      ‖c‖^(2 : ℕ)*‖mulS f g x‖+‖c‖*‖g x‖+‖c‖*‖h x‖+‖c‖^(3 : ℕ)*‖mulS (mulS f f) g x‖ := by
  simp [effectiveControlDensity]
  ring

def globalScatteringScale (q : SchwartzMap ℝ ℂ) : ℝ :=
  (64*(1+effectiveControlMass (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)))*Real.exp 1)⁻¹

def globalSmallScatteringPotential (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (globalScatteringScale q : ℂ) • q

theorem globalScatteringScale_pos (q : SchwartzMap ℝ ℂ) : 0 < globalScatteringScale q := by
  have hn := effectiveControlMass_nonneg (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  unfold globalScatteringScale
  positivity

theorem globalScatteringScale_le_one (q : SchwartzMap ℝ ℂ) : globalScatteringScale q ≤ 1 := by
  have hn := effectiveControlMass_nonneg (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by positivity)
  unfold globalScatteringScale
  apply (inv_le_one₀ (by positivity)).mpr
  nlinarith

/-- The normalization preserves every nonzero potential. -/
theorem globalSmallScatteringPotential_eq_zero_iff (q : SchwartzMap ℝ ℂ) :
    globalSmallScatteringPotential q = 0 ↔ q = 0 := by
  simp [globalSmallScatteringPotential, ne_of_gt (globalScatteringScale_pos q)]

theorem effectiveControlDensity_scaled_bound (q f g h : SchwartzMap ℝ ℂ) (x : ℝ) :
    effectiveControlDensity ((globalScatteringScale q : ℂ) • f)
      ((globalScatteringScale q : ℂ) • g) ((globalScatteringScale q : ℂ) • h) x ≤
        globalScatteringScale q*effectiveControlDensity f g h x := by
  let c := globalScatteringScale q
  have hc0 : 0 ≤ c := (globalScatteringScale_pos q).le
  have hc1 : c ≤ 1 := globalScatteringScale_le_one q
  have hc2 : c^(2 : ℕ) ≤ c := by nlinarith
  have hc3 : c^(3 : ℕ) ≤ c := by
    calc
      c^(3 : ℕ) = c*c^(2 : ℕ) := by ring
      _ ≤ c*c := mul_le_mul_of_nonneg_left hc2 hc0
      _ ≤ c := by nlinarith
  rw [effectiveControlDensity_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (globalScatteringScale_pos q)]
  calc
    _ ≤ c*‖mulS f g x‖+c*‖g x‖+c*‖h x‖+c*‖mulS (mulS f f) g x‖ := by
      apply add_le_add
      · exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc2 (norm_nonneg _)) le_rfl) le_rfl
      · exact mul_le_mul_of_nonneg_right hc3 (norm_nonneg _)
    _ = _ := by unfold effectiveControlDensity; ring

theorem effectiveMass_scaled_bound (q f g h : SchwartzMap ℝ ℂ) :
    effectiveMass ((globalScatteringScale q : ℂ) • f)
      ((globalScatteringScale q : ℂ) • g) ((globalScatteringScale q : ℂ) • h) ≤
        globalScatteringScale q*effectiveControlMass f g h := by
  rw [effectiveControlMass, ← integral_const_mul]
  apply integral_mono (effectiveDensity_integrable _ _ _)
    ((effectiveControlDensity_integrable f g h).const_mul _)
  intro x
  exact (effectiveDensity_le_control _ _ _ x).trans (effectiveControlDensity_scaled_bound q f g h x)

theorem reflectedDerivative_smul (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    reflectedDerivative (c • q) = c • reflectedDerivative q := by
  ext x
  simp [reflectedDerivative, RHTower.negSchwartz'_apply]

/-- A single rescaling controls the effective coefficient mass independently of all spectra. -/
theorem globalSmallScatteringPotential_effectiveMass (q : SchwartzMap ℝ ℂ) :
    effectiveMass (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
      (reflectedDerivative (globalSmallScatteringPotential q))
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) ≤
        1/(64*Real.exp 1) := by
  simp only [globalSmallScatteringPotential, map_smul, reflectedDerivative_smul]
  have hn := effectiveControlMass_nonneg (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  refine (effectiveMass_scaled_bound q _ _ _).trans ?_
  let M := effectiveControlMass (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
  calc
    globalScatteringScale q*M = (M/(1+M))/(64*Real.exp 1) := by
      unfold globalScatteringScale M
      field_simp
    _ ≤ 1/(64*Real.exp 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (div_le_one (by positivity)).mpr
      linarith

theorem globalSmallScatteringPotential_displacement (q : SchwartzMap ℝ ℂ) :
    effectiveDisplacement (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
      (reflectedDerivative (globalSmallScatteringPotential q))
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) ≤ 1/64 := by
  have hm := globalSmallScatteringPotential_effectiveMass q
  have hn := effectiveMass_nonneg (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q)))
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 1/(64*Real.exp 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  unfold effectiveDisplacement
  calc
    _ ≤ Real.exp 1*(1/(64*Real.exp 1)) :=
      mul_le_mul (Real.exp_le_exp.mpr (hm.trans hb)) hm hn (Real.exp_pos _).le
    _ = 1/64 := by field_simp

theorem globalSmallScatteringPotential_error (q : SchwartzMap ℝ ℂ) :
    potentialScatteringError (globalSmallScatteringPotential q) ≤ 1/4 := by
  have hd := globalSmallScatteringPotential_displacement q
  have hn := effectiveDisplacement_nonneg (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q)))
  unfold potentialScatteringError
  nlinarith

/-- Global positive-spectrum estimates for all three independent scattering amplitudes. -/
theorem globalSmallScatteringPotential_amplitudes (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖transmission (globalSmallScatteringPotential q) κ-1‖ ≤ 1/4 ∧
    ‖reverseTransmission (globalSmallScatteringPotential q) κ-1‖ ≤ 1/4 ∧
    ‖reflectionAmplitude (globalSmallScatteringPotential q) κ‖ ≤ 1/4 := by
  have hb := scattering_amplitudes_spectral_bound (globalSmallScatteringPotential q) κ
  have he := globalSmallScatteringPotential_error q
  exact ⟨hb.1.trans he,hb.2.1.trans he,hb.2.2.trans he⟩

theorem globalSmallScatteringPotential_transmission_lower (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    3/4 ≤ ‖transmission (globalSmallScatteringPotential q) κ‖ ∧
    3/4 ≤ ‖reverseTransmission (globalSmallScatteringPotential q) κ‖ := by
  have hb := globalSmallScatteringPotential_amplitudes q κ
  have h1 := norm_sub_norm_le (1:ℂ) (transmission (globalSmallScatteringPotential q) κ)
  have h2 := norm_sub_norm_le (1:ℂ) (reverseTransmission (globalSmallScatteringPotential q) κ)
  rw [norm_one, norm_sub_rev] at h1 h2
  constructor <;> linarith [hb.1,hb.2.1]

/-- No transmission zero occurs anywhere on the positive real continuous spectrum. -/
theorem globalSmallScatteringPotential_transmission_nonzero (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    transmission (globalSmallScatteringPotential q) κ ≠ 0 ∧
    reverseTransmission (globalSmallScatteringPotential q) κ ≠ 0 := by
  have hb := globalSmallScatteringPotential_transmission_lower q κ
  constructor <;> apply norm_pos_iff.mp <;> linarith [hb.1,hb.2]

/-- Proposition 3.2's small-reflection mechanism now holds without a bounded spectral band. -/
theorem globalSmallScatteringPotential_reflection_bounds (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    ‖reflectionCoefficient (globalSmallScatteringPotential q) κ‖ ≤ 1/3 ∧
    ‖reverseReflectionCoefficient (globalSmallScatteringPotential q) κ‖ ≤ 1/3 := by
  have hl := globalSmallScatteringPotential_transmission_lower q κ
  have ha := (globalSmallScatteringPotential_amplitudes q κ).2.2
  constructor
  · rw [reflectionCoefficient, norm_div]
    apply (div_le_iff₀ (by linarith [hl.1])).mpr
    linarith [hl.1]
  · rw [reverseReflectionCoefficient, norm_div, reverseReflectionAmplitude_eq_neg, norm_neg]
    apply (div_le_iff₀ (by linarith [hl.2])).mpr
    linarith [hl.2]

/-- Uniform coercivity for every positive spectral parameter, position and prescribed time. -/
theorem globalSmallScatteringPotential_spaceTime_coercivity (q : SchwartzMap ℝ ℂ)
    (κ t x : ℝ) (u v : ℂ) :
    (5/9 : ℝ)*(normSq u+normSq v) ≤
      energy (spaceTimeReflection (globalSmallScatteringPotential q) κ t x)
        (spaceTimeReverseReflection (globalSmallScatteringPotential q) κ t x) u v := by
  let a := spaceTimeReflection (globalSmallScatteringPotential q) κ t x
  let b := spaceTimeReverseReflection (globalSmallScatteringPotential q) κ t x
  have hbnd := globalSmallScatteringPotential_reflection_bounds q κ
  have ha : ‖a‖ ≤ 1/3 := by simpa only [a, spaceTimeReflection_norm] using hbnd.1
  have hb : ‖b‖ ≤ 1/3 := by simpa only [b, spaceTimeReverseReflection_norm] using hbnd.2
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
