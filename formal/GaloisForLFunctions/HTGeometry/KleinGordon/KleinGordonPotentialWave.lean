import GaloisForLFunctions.HTGeometry.WienerPotentialProduct

/-!
# The field solves the Klein–Gordon equation with a potential

Everything meets here. The second time derivative of the field is the synthesis of
`-⟨ξ⟩²û + 𝓕(Vu)`; the sum of the second spatial derivatives over an orthonormal basis is the
synthesis of `-4π²‖ξ‖²û`; and `⟨ξ⟩² = 1 + ‖ξ‖²`. So

`∂ₜ²u(t,x) = (2π)⁻²Δu(t,x) - u(t,x) + V(x)u(t,x)`

at every event, for the potential `V` given by the inverse transform of the convolving density. The
equation is classical — an identity between numbers obtained from genuine derivatives — and it holds
for every admissible density, with no smallness hypothesis and for all time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] {N : ℕ}

/-! ## The potential -/

/-- The potential attached to a convolving density: its inverse Fourier transform. -/
noncomputable def kgPotential (a : WienerDensity E N) (x : E) : ℂ := ∫ η, kgChar x η * a η

/-- The convolution operator, read on the density rather than on its representative. -/
theorem kgWeighted_kgConvBCF (a : WienerDensity E N) (G : E →ᵇ ℂ) (ξ : E) :
    kgWeighted N (kgConvBCF a G) ξ = ∫ η, a η * kgWeighted N G (ξ - η) := by
  have hconst : ∫ η, a η * kgWeighted N G (ξ - η)
      = ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * ∫ η, kgConvIntegrand N a G ξ η := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show a η * kgWeighted N G (ξ - η)
      = ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * kgConvIntegrand N a G ξ η
    rw [kgWeighted, kgConvIntegrand, Complex.ofReal_div]
    have hξ : ((kgFreq ξ ^ N : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos ξ) N).ne'
    have hη : ((kgFreq (ξ - η) ^ N : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos (ξ - η)) N).ne'
    field_simp
  rw [hconst, kgWeighted]
  rfl

/-! ## The equation -/

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

theorem integrable_kgFlowDensity (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ) :
    Integrable (kgFlowDensity a G₀ t) (volume : Measure E) := by
  have hdim : (Module.finrank ℝ E : ℝ) < N := by linarith
  exact integrable_kgWeighted (E := E) hdim (kgPotentialFlow a G₀ t)

theorem integrable_kgFreq_mul_kgFlowDensity (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ * ‖kgFlowDensity a G₀ t ξ‖) (volume : Measure E) := by
  have h : (Module.finrank ℝ E : ℝ) + (1 : ℕ) < N := by push_cast; linarith
  have := integrable_kgFreq_pow_mul_kgWeighted' (E := E) (j := 1) h (kgPotentialFlow a G₀ t)
  simpa [kgFlowDensity] using this

theorem integrable_kgFreq_sq_mul_kgFlowDensity (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ) :
    Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖kgFlowDensity a G₀ t ξ‖) (volume : Measure E) := by
  have h : (Module.finrank ℝ E : ℝ) + (2 : ℕ) < N := by push_cast; linarith
  exact integrable_kgFreq_pow_mul_kgWeighted' (E := E) (j := 2) h (kgPotentialFlow a G₀ t)

/-- The second spatial derivative along a direction, at an event. -/
theorem deriv_deriv_kgFlowField_dir (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ) (x v : E) :
    deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • v)) 0
      = ∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ
          * kgFlowDensity a G₀ t ξ := by
  have hmain := hasDerivAt_deriv_kgSynthesis_dir
    (f := kgFlowDensity a G₀ t) ((continuous_kgFlowDensity a G₀ t).aestronglyMeasurable)
    (integrable_kgFlowDensity a G₀ hN t) (integrable_kgFreq_mul_kgFlowDensity a G₀ hN t)
    (integrable_kgFreq_sq_mul_kgFlowDensity a G₀ hN t) x v 0
  have hfun : (fun s : ℝ => kgFlowField a G₀ t (x + s • v))
      = fun s : ℝ => kgSynthesis (kgFlowDensity a G₀ t) (x + s • v) := rfl
  rw [hfun]
  refine hmain.deriv.trans ?_
  simp

/-- **The Klein–Gordon equation with a potential, at every event.** -/
theorem kgFlowField_wave_equation (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    deriv (deriv fun r : ℝ => kgFlowField a G₀ r x) t
      = (((2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ)⁻¹
          * ∑ i, deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0
        - kgFlowField a G₀ t x + kgPotential (a.density t) x * kgFlowField a G₀ t x := by
  have hdim : (Module.finrank ℝ E : ℝ) < N := by linarith
  have hmeas : AEStronglyMeasurable (kgFlowDensity a G₀ t) (volume : Measure E) :=
    (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable
  have hint := integrable_kgFlowDensity a G₀ hN t
  have h2 := integrable_kgFreq_sq_mul_kgFlowDensity a G₀ hN t
  -- the time side
  have hL : deriv (deriv fun r : ℝ => kgFlowField a G₀ r x) t
      = ∫ ξ, kgChar x ξ * kgFlowDensityDeriv2 a G₀ t ξ :=
    (hasDerivAt_deriv_kgFlowField hN a G₀ x t).deriv
  -- the two pieces of the second time derivative
  have hfreqInt : Integrable
      (fun ξ : E => kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ))
      (volume : Measure E) := by
    have hcont : Continuous fun ξ : E =>
        kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ) :=
      (continuous_kgChar' x).mul
        (((Complex.continuous_ofReal.comp continuous_kgFreq).pow 2).neg.mul
          (continuous_kgFlowDensity a G₀ t))
    refine Integrable.mono' h2 hcont.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul, norm_mul, norm_neg, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (kgFreq_pos ξ)]
  have hsrcInt : Integrable
      (fun ξ : E => kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ)
      (volume : Measure E) := by
    refine (integrable_kgWeighted (E := E) hdim
      (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t))).bdd_mul (c := 1)
      ((continuous_kgChar' x).aestronglyMeasurable) ?_
    filter_upwards with ξ
    exact le_of_eq (norm_kgChar x ξ)
  have hsplit : (∫ ξ, kgChar x ξ * kgFlowDensityDeriv2 a G₀ t ξ)
      = (∫ ξ, kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ))
        + ∫ ξ, kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ := by
    rw [← integral_add hfreqInt hsrcInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show kgChar x ξ * kgFlowDensityDeriv2 a G₀ t ξ
      = kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ)
        + kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ
    rw [kgFlowDensityDeriv2_eq, kgFlowDensity, kgWeighted, kgWeighted, kgFlowSource]
    show kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
        * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ) * kgPotentialFlow a G₀ t ξ)
          + kgConv N (a.density t) (kgPotentialFlow a G₀ t) ξ))
      = kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ))
          * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * kgPotentialFlow a G₀ t ξ))
        + kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹
          * kgConvBCF (a.density t) (kgPotentialFlow a G₀ t) ξ)
    rw [kgConvBCF_apply]
    ring
  -- the potential term
  have ha_int : Integrable (fun η : E => a.density t η) (volume : Measure E) := by
    refine Integrable.mono' (a.density t).integrable_weight
      (a.density t).aestronglyMeasurable ?_
    filter_upwards with η
    have h1 : (1 : ℝ) ≤ kgFreq η ^ N := one_le_pow₀ (one_le_kgFreq η)
    nlinarith [norm_nonneg (a.density t η)]
  have hpot : (∫ ξ, kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ)
      = kgPotential (a.density t) x * kgFlowField a G₀ t x := by
    have hrw : (∫ ξ, kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ)
        = ∫ ξ, kgChar x ξ * ∫ η, a.density t η * kgFlowDensity a G₀ t (ξ - η) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show kgChar x ξ * kgWeighted N (kgConvBCF (a.density t) (kgPotentialFlow a G₀ t)) ξ
        = kgChar x ξ * ∫ η, a.density t η * kgFlowDensity a G₀ t (ξ - η)
      rw [kgWeighted_kgConvBCF]
      rfl
    rw [hrw, integral_kgChar_mul_convolution ha_int hint x]
    rfl
  -- the space side
  have hLap : ∑ i, deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0
      = ∫ ξ, ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * kgFlowDensity a G₀ t ξ := by
    rw [← sum_integral_dirSq hmeas h2 b x]
    exact Finset.sum_congr rfl fun i _ => deriv_deriv_kgFlowField_dir a G₀ hN t x (b i)
  rw [hL, hsplit, hpot, hLap]
  -- the remaining identity is between two syntheses
  have hpi : ((2 * Real.pi) ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfield : kgFlowField a G₀ t x = ∫ ξ, kgChar x ξ * kgFlowDensity a G₀ t ξ := rfl
  have hLapInt : Integrable
      (fun ξ : E => ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ
        * kgFlowDensity a G₀ t ξ) (volume : Measure E) := by
    have hcont : Continuous fun ξ : E => ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ
        * kgFlowDensity a G₀ t ξ :=
      ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_norm.pow 2))).mul
        (continuous_kgChar' x)).mul (continuous_kgFlowDensity a G₀ t)
    refine Integrable.mono' (h2.const_mul (4 * Real.pi ^ (2 : ℕ))) hcont.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_mul, norm_mul, norm_kgChar, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖, Real.pi_pos, sq_nonneg (‖ξ‖ * Real.pi)])]
    have hnorm : ‖ξ‖ ^ (2 : ℕ) ≤ kgFreq ξ ^ (2 : ℕ) := by
      rw [kgFreq_sq]
      nlinarith
    have hf : (0 : ℝ) ≤ ‖kgFlowDensity a G₀ t ξ‖ := norm_nonneg _
    have hpi2 : (0 : ℝ) < 4 * Real.pi ^ (2 : ℕ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hnorm hf]
  have hcharInt : Integrable (fun ξ : E => kgChar x ξ * kgFlowDensity a G₀ t ξ)
      (volume : Measure E) := integrable_kgChar_mul_kgFlowDensity hdim a G₀ t x
  have hcombine : (((2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ)⁻¹
        * (∫ ξ, ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * kgFlowDensity a G₀ t ξ)
      - (∫ ξ, kgChar x ξ * kgFlowDensity a G₀ t ξ)
      = ∫ ξ, kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ) := by
    rw [← integral_const_mul, ← integral_sub (hLapInt.const_mul _) hcharInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show (((2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ)⁻¹
          * (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * kgFlowDensity a G₀ t ξ)
        - kgChar x ξ * kgFlowDensity a G₀ t ξ
      = kgChar x ξ * (-(((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ)) * kgFlowDensity a G₀ t ξ)
    have hfreq : ((kgFreq ξ : ℝ) : ℂ) ^ (2 : ℕ) = ((1 + ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, kgFreq_sq]
    have hpiC : (((2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi
    rw [hfreq]
    push_cast
    field_simp
    ring
  rw [hfield, ← hcombine]

end GaloisForLFunctions.HTGeometry
