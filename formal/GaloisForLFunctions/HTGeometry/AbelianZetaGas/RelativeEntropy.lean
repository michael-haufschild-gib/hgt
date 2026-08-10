import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ClassLaw
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The relative entropy of the zeta-Gibbs law against its canonical unit tilt

The socle observable `log|soc A|` has finite mean under both the untilted gas and its canonical
unit tilt, and the two means differ by exactly the von Mangoldt Dirichlet mass.  Since the tilt is
the density `ζ(σ)|soc A|^{−σ}`, the symmetrised Kullback–Leibler divergence of the pair is `σ`
times that mass.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ArithmeticFunction

open scoped ENNReal

noncomputable section

/-! ## Finiteness of the socle expectation -/

theorem log_prime_nonneg (p : Nat.Primes) : (0 : ℝ) ≤ Real.log (((p : ℕ) : ℝ)) :=
  Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)

theorem summable_primes_log_mul_tsum_modeMean (σ : EulerSigma) :
    Summable fun p : Nat.Primes =>
      Real.log (((p : ℕ) : ℝ)) * ∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) j := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (summable_primes_log_mul_ladderBound σ)
  · exact mul_nonneg (log_prime_nonneg p)
      (tsum_nonneg fun j =>
        modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) j)
  · exact mul_le_mul_of_nonneg_left
      (tsum_modeMean_le (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le)) (log_prime_nonneg p)

/-- **The socle expectation of the untilted gas, in real form.** -/
theorem socleExpectation_temperature_eq_ofReal (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = ENNReal.ofReal (∑' p : Nat.Primes,
          Real.log (((p : ℕ) : ℝ)) * ∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) j) := by
  rw [socleExpectation_temperature σ,
    ENNReal.ofReal_tsum_of_nonneg
      (fun p => mul_nonneg (log_prime_nonneg p)
        (tsum_nonneg fun j =>
          modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) j))
      (summable_primes_log_mul_tsum_modeMean σ)]
  refine tsum_congr fun p => ?_
  rw [ENNReal.ofReal_mul (log_prime_nonneg p),
    tsum_ofReal_modeMean_eq _ (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le)]

theorem socleExpectation_temperature_ne_top (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation
      (AbelianZetaParameters.temperatureParameters σ.val σ.pos) ≠ ⊤ := by
  rw [socleExpectation_temperature_eq_ofReal σ]
  exact ENNReal.ofReal_ne_top

theorem socleExpectation_tilt_ne_top (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation (tiltParameters σ) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (socleExpectation_temperature_ne_top σ) ?_
  rw [socleExpectation_eq_tilt_add_residue σ]
  exact le_self_add

/-! ## The residue as a real Dirichlet mass -/

theorem modeMean_zero_le_ladderBound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    modeMean q 0 ≤ q / (1 - q) ^ 2 := by
  have hden : (0 : ℝ) < 1 - q := by linarith
  have hsq : (0 : ℝ) < (1 - q) ^ 2 := by positivity
  have hle : (1 - q) ^ 2 ≤ 1 - q := by nlinarith
  have : modeMean q 0 = q / (1 - q) := by
    rw [modeMean]
    norm_num
  rw [this]
  exact div_le_div_of_nonneg_left hq0 hsq hle

theorem summable_primes_log_mul_modeMean_zero (σ : EulerSigma) :
    Summable fun p : Nat.Primes =>
      Real.log (((p : ℕ) : ℝ)) * modeMean (eqgQ σ (p : ℕ)) 0 := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (summable_primes_log_mul_ladderBound σ)
  · exact mul_nonneg (log_prime_nonneg p)
      (modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) 0)
  · exact mul_le_mul_of_nonneg_left
      (modeMean_zero_le_ladderBound (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le))
      (log_prime_nonneg p)

/-- **The von Mangoldt residue of (GAS.12), in `ℝ≥0∞` form.** -/
theorem residue_eq_ofReal_vonMangoldt (σ : EulerSigma) :
    (∑' p : Nat.Primes, ENNReal.ofReal (Real.log (((p : ℕ) : ℝ)))
        * ENNReal.ofReal (modeMean (eqgQ σ (p : ℕ)) 0))
      = ENNReal.ofReal (∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val)) := by
  rw [← tsum_primes_modeMean_zero σ,
    ENNReal.ofReal_tsum_of_nonneg
      (fun p => mul_nonneg (log_prime_nonneg p)
        (modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) 0))
      (summable_primes_log_mul_modeMean_zero σ)]
  exact tsum_congr fun p => (ENNReal.ofReal_mul (log_prime_nonneg p)).symm

/-! ## The socle observable is integrable -/

theorem logSocle_nonneg (A : AbelianZetaGroupClass) :
    (0 : ℝ) ≤ Real.log (((A.socleOrder : ℕ) : ℝ)) :=
  Real.log_nonneg (by exact_mod_cast A.socleOrder_pos)

theorem measurable_logSocle :
    Measurable fun A : AbelianZetaGroupClass => Real.log (((A.socleOrder : ℕ) : ℝ)) :=
  fun _ _ => trivial

/-- **The mean socle observable is the socle expectation.** -/
theorem integral_classLaw_logSocle (θ : AbelianZetaConvergentParameters) :
    ∫ A, Real.log (((A.socleOrder : ℕ) : ℝ)) ∂(classLaw θ.toAbelianZetaParameters)
      = (AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun A => logSocle_nonneg A)
      measurable_logSocle.aestronglyMeasurable,
    lintegral_classLaw_logSocle θ]

/-- **The socle observable is integrable when its expectation is finite.** -/
theorem integrable_classLaw_logSocle (θ : AbelianZetaConvergentParameters)
    (h : AbelianZetaParameters.socleExpectation θ.toAbelianZetaParameters ≠ ⊤) :
    Integrable (fun A : AbelianZetaGroupClass => Real.log (((A.socleOrder : ℕ) : ℝ)))
      (classLaw θ.toAbelianZetaParameters) := by
  refine integrable_classLaw _ _ ?_
  have hrw : (∑' A : AbelianZetaGroupClass,
        ENNReal.ofReal ‖Real.log (((A.socleOrder : ℕ) : ℝ))‖
          * abelianZetaClassMass θ.toAbelianZetaParameters A)
      = ∫⁻ A, ENNReal.ofReal (Real.log (((A.socleOrder : ℕ) : ℝ)))
          ∂(classLaw θ.toAbelianZetaParameters) := by
    rw [lintegral_classLaw]
    exact tsum_congr fun A => by rw [Real.norm_of_nonneg (logSocle_nonneg A)]
  rw [hrw, lintegral_classLaw_logSocle θ]
  exact h

/-! ## The reverse density -/

theorem tiltConv_toParams (σ : EulerSigma) :
    (tiltConv σ).toAbelianZetaParameters = tiltParameters σ := rfl

theorem temperatureConv_toParams (σ : EulerSigma) :
    (temperatureConv σ).toAbelianZetaParameters
      = AbelianZetaParameters.temperatureParameters σ.val σ.pos := rfl

/-- **The untilted law is a density against its canonical unit tilt.** -/
theorem classLaw_temperatureConv_eq_withDensity (σ : EulerSigma) :
    classLaw (temperatureConv σ).toAbelianZetaParameters
      = (classLaw (tiltConv σ).toAbelianZetaParameters).withDensity
        (fun A => (densityConst σ)⁻¹ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val)) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [withDensity_singleton]
  have hmass : classLaw (tiltConv σ).toAbelianZetaParameters {A}
      = densityConst σ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ (-σ.val))
        * classLaw (temperatureConv σ).toAbelianZetaParameters {A} := by
    conv_lhs => rw [classLaw_tiltConv_eq_withDensity σ]
    rw [withDensity_singleton]
  have hsoc : (0 : ℝ) < ((A.socleOrder : ℝ)) := by exact_mod_cast A.socleOrder_pos
  have hpow : ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val)
      * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ (-σ.val)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hsoc.le _), ← Real.rpow_add hsoc]
    norm_num
  have hdc : (densityConst σ)⁻¹ * densityConst σ = 1 :=
    ENNReal.inv_mul_cancel (densityConst_ne_zero σ) (densityConst_ne_top σ)
  rw [hmass]
  calc classLaw (temperatureConv σ).toAbelianZetaParameters {A}
      = ((densityConst σ)⁻¹ * densityConst σ)
        * (ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val)
          * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ (-σ.val)))
        * classLaw (temperatureConv σ).toAbelianZetaParameters {A} := by
        rw [hdc, hpow, one_mul, one_mul]
    _ = (densityConst σ)⁻¹ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val)
        * (densityConst σ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ (-σ.val))
          * classLaw (temperatureConv σ).toAbelianZetaParameters {A}) := by ring

/-- **The Radon–Nikodym derivative of the untilted law against the canonical unit tilt.** -/
theorem rnDeriv_classLaw_temperatureConv (σ : EulerSigma) :
    (classLaw (temperatureConv σ).toAbelianZetaParameters).rnDeriv
        (classLaw (tiltConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (tiltConv σ).toAbelianZetaParameters]
        fun A => (densityConst σ)⁻¹ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val) := by
  have hmeas : Measurable fun A : AbelianZetaGroupClass =>
      (densityConst σ)⁻¹ * ENNReal.ofReal (((A.socleOrder : ℝ)) ^ σ.val) := fun _ _ => trivial
  rw [classLaw_temperatureConv_eq_withDensity σ]
  exact Measure.rnDeriv_withDensity _ hmeas

/-- **The reverse log-density.**  Almost everywhere,
`llr = −log C + σ·log|soc A|`. -/
theorem llr_classLaw_temperatureConv (σ : EulerSigma) :
    llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (tiltConv σ).toAbelianZetaParameters]
        fun A => -Real.log ((densityConst σ).toReal)
          + σ.val * Real.log (((A.socleOrder : ℝ))) := by
  filter_upwards [rnDeriv_classLaw_temperatureConv σ] with A hA
  show Real.log ((classLaw (temperatureConv σ).toAbelianZetaParameters).rnDeriv
      (classLaw (tiltConv σ).toAbelianZetaParameters) A).toReal = _
  have hsoc : (0 : ℝ) < ((A.socleOrder : ℝ)) := by exact_mod_cast A.socleOrder_pos
  have hc : (0 : ℝ) < (densityConst σ).toReal := densityConst_toReal_pos σ
  have hpow : (0 : ℝ) < (((A.socleOrder : ℝ)) ^ σ.val) := Real.rpow_pos_of_pos hsoc _
  rw [hA, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hsoc.le _),
    Real.log_mul (by positivity) hpow.ne', Real.log_inv, Real.log_rpow hsoc]

/-! ## The two relative entropies -/

theorem ac_tilt_temperature (σ : EulerSigma) :
    classLaw (tiltConv σ).toAbelianZetaParameters
      ≪ classLaw (temperatureConv σ).toAbelianZetaParameters :=
  classLaw_absolutelyContinuous (temperatureConv σ) (tiltConv σ)

theorem ac_temperature_tilt (σ : EulerSigma) :
    classLaw (temperatureConv σ).toAbelianZetaParameters
      ≪ classLaw (tiltConv σ).toAbelianZetaParameters :=
  classLaw_absolutelyContinuous (tiltConv σ) (temperatureConv σ)

theorem llr_tilt_ae_tilt (σ : EulerSigma) :
    llr (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (tiltConv σ).toAbelianZetaParameters]
        fun A => Real.log ((densityConst σ).toReal)
          - σ.val * Real.log (((A.socleOrder : ℝ))) :=
  (llr_classLaw_tiltConv σ).filter_mono (ac_tilt_temperature σ).ae_le

theorem integrable_llr_tilt (σ : EulerSigma) :
    Integrable (llr (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters))
      (classLaw (tiltConv σ).toAbelianZetaParameters) := by
  refine Integrable.congr ?_ (llr_tilt_ae_tilt σ).symm
  exact (integrable_const _).sub
    ((integrable_classLaw_logSocle (tiltConv σ) (socleExpectation_tilt_ne_top σ)).const_mul σ.val)

theorem integrable_llr_temperature (σ : EulerSigma) :
    Integrable (llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters))
      (classLaw (temperatureConv σ).toAbelianZetaParameters) := by
  refine Integrable.congr ?_
    ((llr_classLaw_temperatureConv σ).filter_mono (ac_temperature_tilt σ).ae_le).symm
  exact (integrable_const _).add
    ((integrable_classLaw_logSocle (temperatureConv σ)
      (socleExpectation_temperature_ne_top σ)).const_mul σ.val)

theorem integral_llr_tilt (σ : EulerSigma) :
    ∫ A, llr (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters) A
        ∂(classLaw (tiltConv σ).toAbelianZetaParameters)
      = Real.log ((densityConst σ).toReal)
        - σ.val * (AbelianZetaParameters.socleExpectation (tiltParameters σ)).toReal := by
  rw [integral_congr_ae (llr_tilt_ae_tilt σ),
    integral_sub (integrable_const _)
      ((integrable_classLaw_logSocle (tiltConv σ)
        (socleExpectation_tilt_ne_top σ)).const_mul σ.val),
    integral_const, integral_const_mul, integral_classLaw_logSocle (tiltConv σ),
    probReal_univ, smul_eq_mul, one_mul]
  rfl

theorem integral_llr_temperature (σ : EulerSigma) :
    ∫ A, llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters) A
        ∂(classLaw (temperatureConv σ).toAbelianZetaParameters)
      = -Real.log ((densityConst σ).toReal)
        + σ.val * (AbelianZetaParameters.socleExpectation
          (AbelianZetaParameters.temperatureParameters σ.val σ.pos)).toReal := by
  rw [integral_congr_ae
      ((llr_classLaw_temperatureConv σ).filter_mono (ac_temperature_tilt σ).ae_le),
    integral_add (integrable_const _)
      ((integrable_classLaw_logSocle (temperatureConv σ)
        (socleExpectation_temperature_ne_top σ)).const_mul σ.val),
    integral_const, integral_const_mul, integral_classLaw_logSocle (temperatureConv σ),
    probReal_univ, smul_eq_mul, one_mul]
  rfl

/-! ## Theorem 8.1 — the symmetrised relative entropy is the von Mangoldt mass -/

theorem klDiv_tilt (σ : EulerSigma) :
    klDiv (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      = ENNReal.ofReal (Real.log ((densityConst σ).toReal)
          - σ.val * (AbelianZetaParameters.socleExpectation (tiltParameters σ)).toReal) := by
  rw [klDiv_of_ac_of_integrable (ac_tilt_temperature σ) (integrable_llr_tilt σ),
    integral_llr_tilt σ, probReal_univ, probReal_univ]
  congr 1
  ring

theorem klDiv_temperature (σ : EulerSigma) :
    klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters)
      = ENNReal.ofReal (-Real.log ((densityConst σ).toReal)
          + σ.val * (AbelianZetaParameters.socleExpectation
            (AbelianZetaParameters.temperatureParameters σ.val σ.pos)).toReal) := by
  rw [klDiv_of_ac_of_integrable (ac_temperature_tilt σ) (integrable_llr_temperature σ),
    integral_llr_temperature σ, probReal_univ, probReal_univ]
  congr 1
  ring

theorem integral_llr_tilt_nonneg (σ : EulerSigma) :
    0 ≤ Real.log ((densityConst σ).toReal)
      - σ.val * (AbelianZetaParameters.socleExpectation (tiltParameters σ)).toReal := by
  have h := integral_llr_add_sub_measure_univ_nonneg (ac_tilt_temperature σ)
    (integrable_llr_tilt σ)
  rw [integral_llr_tilt σ, probReal_univ, probReal_univ] at h
  linarith

theorem integral_llr_temperature_nonneg (σ : EulerSigma) :
    0 ≤ -Real.log ((densityConst σ).toReal)
      + σ.val * (AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)).toReal := by
  have h := integral_llr_add_sub_measure_univ_nonneg (ac_temperature_tilt σ)
    (integrable_llr_temperature σ)
  rw [integral_llr_temperature σ, probReal_univ, probReal_univ] at h
  linarith

theorem tsum_vonMangoldt_rpow_nonneg (σ : EulerSigma) :
    0 ≤ ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val) :=
  tsum_nonneg fun n => mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The two socle means differ by the von Mangoldt Dirichlet mass.** -/
theorem socleExpectation_toReal_sub (σ : EulerSigma) :
    (AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)).toReal
      - (AbelianZetaParameters.socleExpectation (tiltParameters σ)).toReal
      = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val) := by
  have hsum := socleExpectation_eq_tilt_add_residue σ
  rw [residue_eq_ofReal_vonMangoldt σ] at hsum
  rw [hsum, ENNReal.toReal_add (socleExpectation_tilt_ne_top σ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (tsum_vonMangoldt_rpow_nonneg σ)]
  ring

/-- **Theorem 8.1, equation (GAS.12).**  The symmetrised Kullback–Leibler divergence of the
zeta-Gibbs law and its canonical unit tilt is `σ` times the von Mangoldt Dirichlet mass. -/
theorem klDiv_symmetrised_eq_vonMangoldt (σ : EulerSigma) :
    klDiv (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      + klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters)
      = ENNReal.ofReal (σ.val * ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val)) := by
  rw [klDiv_tilt σ, klDiv_temperature σ,
    ← ENNReal.ofReal_add (integral_llr_tilt_nonneg σ) (integral_llr_temperature_nonneg σ)]
  congr 1
  have h := socleExpectation_toReal_sub σ
  linear_combination σ.val * h

/-- Both relative entropies are finite. -/
theorem klDiv_tilt_ne_top (σ : EulerSigma) :
    klDiv (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters) ≠ ⊤ := by
  rw [klDiv_tilt σ]
  exact ENNReal.ofReal_ne_top

theorem klDiv_temperature_ne_top (σ : EulerSigma) :
    klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters) ≠ ⊤ := by
  rw [klDiv_temperature σ]
  exact ENNReal.ofReal_ne_top

/-- **Theorem 8.1 in real form.** -/
theorem klDiv_symmetrised_toReal (σ : EulerSigma) :
    (klDiv (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      + klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters)).toReal
      = σ.val * ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ.val) := by
  rw [klDiv_symmetrised_eq_vonMangoldt σ,
    ENNReal.toReal_ofReal (mul_nonneg σ.pos.le (tsum_vonMangoldt_rpow_nonneg σ))]

/-- **Theorem 8.1 in zeta form.**  The symmetrised relative entropy is `σ·(−ζ′/ζ)(σ)`. -/
theorem klDiv_symmetrised_eq_zeta (σ : EulerSigma) :
    (((klDiv (classLaw (tiltConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      + klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (tiltConv σ).toAbelianZetaParameters)).toReal : ℝ) : ℂ)
      = ((σ.val : ℝ) : ℂ)
        * (-deriv riemannZeta ((σ.val : ℝ) : ℂ) / riemannZeta ((σ.val : ℝ) : ℂ)) := by
  rw [klDiv_symmetrised_toReal σ, Complex.ofReal_mul, ofReal_tsum_vonMangoldt_eq σ.one_lt]

/-! ## (GAS.13) — the depth ladder of the socle mean -/

/-- The temperature at depth `j`:  `(j+1)σ`. -/
def depthSigma (σ : EulerSigma) (j : ℕ) : EulerSigma where
  val := ((j : ℝ) + 1) * σ.val
  one_lt := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hσ : 1 < σ.val := σ.one_lt
    nlinarith

theorem modeMean_eqgQ_depth (σ : EulerSigma) (p : Nat.Primes) (j : ℕ) :
    modeMean (eqgQ σ (p : ℕ)) j = modeMean (eqgQ (depthSigma σ j) (p : ℕ)) 0 := by
  have h1 : (eqgQ σ (p : ℕ)) ^ (j + 1) = eqgQ (depthSigma σ j) (p : ℕ) := by
    rw [eqgQ_pow_succ]
    rfl
  rw [modeMean, modeMean, h1, zero_add, pow_one]

/-- **(GAS.13), socle half.**  The socle mean of the untilted gas is the depth ladder
`∑_{j≥1} (−ζ′/ζ)(jσ)` of von Mangoldt masses. -/
theorem socleExpectation_temperature_depthLadder (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = ∑' j : ℕ, ENNReal.ofReal
          (∑' n : ℕ, Λ n * (n : ℝ) ^ (-(((j : ℝ) + 1) * σ.val))) := by
  rw [socleExpectation_temperature σ]
  have hstep : ∀ p : Nat.Primes,
      ENNReal.ofReal (Real.log (((p : ℕ) : ℝ)))
          * ∑' j : ℕ, ENNReal.ofReal (modeMean (eqgQ σ (p : ℕ)) j)
        = ∑' j : ℕ, ENNReal.ofReal (Real.log (((p : ℕ) : ℝ)))
            * ENNReal.ofReal (modeMean (eqgQ (depthSigma σ j) (p : ℕ)) 0) := by
    intro p
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun j => by rw [modeMean_eqgQ_depth]
  rw [tsum_congr hstep, ENNReal.tsum_comm]
  exact tsum_congr fun j => residue_eq_ofReal_vonMangoldt (depthSigma σ j)

/-! ## (GAS.13) — the depth ladder of the order mean -/

/-- The expectation of the order observable `log|A| = ∑_{(p,j)} (j+1)·A(p,j)·log p`. -/
def orderExpectation (θ : AbelianZetaParameters) : ℝ≥0∞ :=
  ∫⁻ k, (∑' m : AbelianZetaMode,
      ENNReal.ofReal ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)))
        * ((k m : ℕ) : ℝ≥0∞)) ∂θ.gasMeasure

/-- **The order expectation groups by prime.** -/
theorem orderExpectation_eq (θ : AbelianZetaParameters) :
    orderExpectation θ
      = ∑' p : Nat.Primes, ∑' j : ℕ,
        ENNReal.ofReal (((j : ℝ) + 1) * Real.log (((p : ℕ) : ℝ)))
          * ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j))) := by
  rw [orderExpectation, AbelianZetaParameters.lintegral_gasMeasure_tsum θ
    (fun m => ENNReal.ofReal ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ))))]
  have hcongr : (∑' m : AbelianZetaMode,
        ENNReal.ofReal ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)))
          * ENNReal.ofReal (θ.ratio m / (1 - θ.ratio m)))
      = ∑' m : Nat.Primes × ℕ,
        (fun (p : Nat.Primes) (j : ℕ) => ENNReal.ofReal (((j : ℝ) + 1) * Real.log (((p : ℕ) : ℝ)))
          * ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j)))) m.1 m.2 := by
    refine tsum_congr fun m => ?_
    congr 2
    rw [AbelianZetaMode.depth]
    push_cast
    ring
  rw [hcongr]
  exact ENNReal.tsum_prod (f := fun (p : Nat.Primes) (j : ℕ) =>
    ENNReal.ofReal (((j : ℝ) + 1) * Real.log (((p : ℕ) : ℝ)))
      * ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j))))

/-- **(GAS.13), order half.**  The order mean of the untilted gas is the weighted depth ladder
`∑_{j≥1} j·(−ζ′/ζ)(jσ)`. -/
theorem orderExpectation_temperature_depthLadder (σ : EulerSigma) :
    orderExpectation (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = ∑' j : ℕ, ENNReal.ofReal
          (((j : ℝ) + 1) * ∑' n : ℕ, Λ n * (n : ℝ) ^ (-(((j : ℝ) + 1) * σ.val))) := by
  rw [orderExpectation_eq, ENNReal.tsum_comm]
  refine tsum_congr fun j => ?_
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hstep : ∀ p : Nat.Primes,
      ENNReal.ofReal (((j : ℝ) + 1) * Real.log (((p : ℕ) : ℝ)))
          * ENNReal.ofReal ((AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)
            / (1 - (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)))
        = ENNReal.ofReal ((j : ℝ) + 1)
          * (ENNReal.ofReal (Real.log (((p : ℕ) : ℝ)))
            * ENNReal.ofReal (modeMean (eqgQ (depthSigma σ j) (p : ℕ)) 0)) := by
    intro p
    rw [ratio_div_one_sub_eq_modeMean σ p j, modeMean_eqgQ_depth σ p j,
      ENNReal.ofReal_mul hj, mul_assoc]
  rw [tsum_congr hstep, ENNReal.tsum_mul_left, residue_eq_ofReal_vonMangoldt (depthSigma σ j),
    ← ENNReal.ofReal_mul hj]
  rfl

/-! ## The order observable on the class space -/

/-- **`log |A|` is the mode-additive functional `∑ (depth m)·A(m)·log p`.** -/
theorem log_order (A : AbelianZetaGroupClass) :
    Real.log ((A.order : ℕ) : ℝ)
      = ∑ m ∈ A.support,
        (AbelianZetaMode.depth m : ℝ) * (A m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)) := by
  classical
  have hcast : ((A.order : ℕ) : ℝ)
      = ∏ m ∈ A.support, (((m.1 : ℕ) : ℝ)) ^ (AbelianZetaMode.depth m * A m) := by
    rw [AbelianZetaGroupClass.order, Finsupp.prod, Nat.cast_prod]
    exact Finset.prod_congr rfl fun m _ => by push_cast; ring
  rw [hcast, Real.log_prod]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  · intro m _
    have hp : (0 : ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.2.pos
    exact (pow_pos hp _).ne'

theorem log_order_classOf {k : AbelianZetaMode → ℕ} (hk : (Function.support k).Finite) :
    Real.log (((classOf k).order : ℕ) : ℝ)
      = ∑ m ∈ (classOf k).support,
        (AbelianZetaMode.depth m : ℝ) * (k m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)) := by
  rw [log_order (classOf k)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hval := classOf_of_finite hk
  rw [congrFun hval m]

/-- The mode-additive order observable as an `ℝ≥0∞` sum over all modes. -/
theorem ofReal_logOrder_eq_tsum {k : AbelianZetaMode → ℕ} (hk : (Function.support k).Finite) :
    ENNReal.ofReal (Real.log (((classOf k).order : ℕ) : ℝ))
      = ∑' m : AbelianZetaMode,
        ENNReal.ofReal ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)))
          * ((k m : ℕ) : ℝ≥0∞) := by
  classical
  have hlognn : ∀ m : AbelianZetaMode, (0 : ℝ) ≤ Real.log (((m.1 : ℕ) : ℝ)) := fun m =>
    Real.log_nonneg (by exact_mod_cast m.1.2.one_lt.le)
  have hwnn : ∀ m : AbelianZetaMode,
      (0 : ℝ) ≤ (AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)) := fun m =>
    mul_nonneg (Nat.cast_nonneg _) (hlognn m)
  rw [log_order_classOf hk,
    ENNReal.ofReal_sum_of_nonneg (fun m _ => by
      have := hwnn m
      have hk' : (0 : ℝ) ≤ (k m : ℝ) := Nat.cast_nonneg _
      nlinarith [hlognn m, Nat.cast_nonneg (α := ℝ) (AbelianZetaMode.depth m)])]
  have hzero : ∀ m ∉ (classOf k).support,
      ENNReal.ofReal ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ)))
        * ((k m : ℕ) : ℝ≥0∞) = 0 := by
    intro m hm
    have hkm : k m = 0 := by
      have hval := congrFun (classOf_of_finite hk) m
      rw [← hval]
      exact Finsupp.notMem_support_iff.mp hm
    rw [hkm]
    simp
  rw [tsum_eq_sum hzero]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hrw : (AbelianZetaMode.depth m : ℝ) * (k m : ℝ) * Real.log (((m.1 : ℕ) : ℝ))
      = ((AbelianZetaMode.depth m : ℝ) * Real.log (((m.1 : ℕ) : ℝ))) * (k m : ℝ) := by ring
  rw [hrw, ENNReal.ofReal_mul (hwnn m), ENNReal.ofReal_natCast]

/-- **The mean order observable is the order expectation.** -/
theorem lintegral_classLaw_logOrder (θ : AbelianZetaConvergentParameters) :
    ∫⁻ A, ENNReal.ofReal (Real.log ((A.order : ℕ) : ℝ))
        ∂(classLaw θ.toAbelianZetaParameters)
      = orderExpectation θ.toAbelianZetaParameters := by
  classical
  have hmeasf : Measurable fun A : AbelianZetaGroupClass =>
      ENNReal.ofReal (Real.log ((A.order : ℕ) : ℝ)) := fun _ _ => trivial
  rw [classLaw_eq_map, lintegral_map hmeasf measurable_classOf, orderExpectation]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ k ∂θ.toAbelianZetaParameters.gasMeasure, (Function.support k).Finite :=
    ae_iff.mpr (gasMeasure_infiniteSupport_null θ)
  filter_upwards [hae] with k hk
  exact ofReal_logOrder_eq_tsum hk

/-! ## Finiteness of the order expectation -/

theorem summable_depthMean {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) * modeMean q j := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hden : (0 : ℝ) < 1 - q := by linarith
  have hg : Summable fun n : ℕ => (n : ℝ) * q ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hshift : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) * q ^ (j + 1) :=
    hg.comp_injective (add_left_injective 1)
  have hmaj : Summable fun j : ℕ => ((j : ℝ) + 1) * (q ^ (j + 1) / (1 - q)) := by
    refine (hshift.div_const (1 - q)).congr fun j => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmaj
  · exact mul_nonneg (by positivity) (modeMean_nonneg hq0 hq1 j)
  · exact mul_le_mul_of_nonneg_left (modeMean_le hq0 hq1 j) (by positivity)

/-- **The depth-weighted mode-mean ladder is bounded by `q/(1−q)³`.** -/
theorem tsum_depthMean_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, ((j : ℝ) + 1) * modeMean q j) ≤ q / (1 - q) ^ 3 := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hden : (0 : ℝ) < 1 - q := by linarith
  have hg : Summable fun n : ℕ => (n : ℝ) * q ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hshift : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) * q ^ (j + 1) :=
    hg.comp_injective (add_left_injective 1)
  have hmaj : Summable fun j : ℕ => ((j : ℝ) + 1) * (q ^ (j + 1) / (1 - q)) := by
    refine (hshift.div_const (1 - q)).congr fun j => ?_
    push_cast
    ring
  have h2 : (∑' n : ℕ, (n : ℝ) * q ^ n) = q / (1 - q) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have h3 := hg.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_mul, zero_add] at h3
  have h4 : (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * q ^ (j + 1)) = q / (1 - q) ^ 2 := by
    rw [← h3, h2]
  have h1 : (∑' j : ℕ, ((j : ℝ) + 1) * (q ^ (j + 1) / (1 - q)))
      = (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * q ^ (j + 1)) / (1 - q) := by
    rw [← tsum_div_const]
    exact tsum_congr fun j => by push_cast; ring
  have hval : (∑' j : ℕ, ((j : ℝ) + 1) * (q ^ (j + 1) / (1 - q))) = q / (1 - q) ^ 3 := by
    rw [h1, h4]
    field_simp
  have hle := (summable_depthMean hq0 hq1).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (modeMean_le hq0 hq1 j) (by positivity)) hmaj
  linarith [hle, hval.le, hval.ge]

theorem div_one_sub_cube_le (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    q / (1 - q) ^ 3 ≤ 8 * q := by
  have hden : (1 : ℝ) / 2 ≤ 1 - q := by linarith
  have hq1 : (0 : ℝ) < 1 - q := by linarith
  have hcube : (1 : ℝ) / 8 ≤ (1 - q) ^ 3 := by nlinarith [sq_nonneg (1 - q - 1 / 2)]
  have hpos : (0 : ℝ) < (1 - q) ^ 3 := pow_pos hq1 3
  rw [div_le_iff₀ hpos]
  nlinarith

theorem summable_primes_log_mul_depthLadderBound (σ : EulerSigma) :
    Summable fun p : Nat.Primes =>
      Real.log (((p : ℕ) : ℝ)) * (eqgQ σ (p : ℕ) / (1 - eqgQ σ (p : ℕ)) ^ 3) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((summable_primes_vonMangoldt σ).mul_left 8)
  · have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
    have hq1 : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    have hden : (0 : ℝ) < (1 - eqgQ σ (p : ℕ)) ^ 3 := pow_pos (by linarith) 3
    exact mul_nonneg (log_prime_nonneg p) (by positivity)
  · have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
    have hq1 : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    have hb := div_one_sub_cube_le (eqgQ σ (p : ℕ)) hq0 hq1
    have hlam : Λ ((p : ℕ)) * (((p : ℕ) : ℝ)) ^ (-σ.val)
        = Real.log (((p : ℕ) : ℝ)) * eqgQ σ (p : ℕ) := by
      rw [eqgQ, ArithmeticFunction.vonMangoldt_apply_prime p.2]
    calc Real.log (((p : ℕ) : ℝ)) * (eqgQ σ (p : ℕ) / (1 - eqgQ σ (p : ℕ)) ^ 3)
        ≤ Real.log (((p : ℕ) : ℝ)) * (8 * eqgQ σ (p : ℕ)) :=
          mul_le_mul_of_nonneg_left hb (log_prime_nonneg p)
      _ = 8 * (Λ ((p : ℕ)) * (((p : ℕ) : ℝ)) ^ (-σ.val)) := by rw [hlam]; ring

theorem summable_primes_log_mul_tsum_depthMean (σ : EulerSigma) :
    Summable fun p : Nat.Primes =>
      Real.log (((p : ℕ) : ℝ)) * ∑' j : ℕ, ((j : ℝ) + 1) * modeMean (eqgQ σ (p : ℕ)) j := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (summable_primes_log_mul_depthLadderBound σ)
  · exact mul_nonneg (log_prime_nonneg p)
      (tsum_nonneg fun j => mul_nonneg (by positivity)
        (modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) j))
  · exact mul_le_mul_of_nonneg_left
      (tsum_depthMean_le (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le))
      (log_prime_nonneg p)

/-- **The order expectation of the untilted gas, in real form.** -/
theorem orderExpectation_temperature_eq_ofReal (σ : EulerSigma) :
    orderExpectation (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = ENNReal.ofReal (∑' p : Nat.Primes, Real.log (((p : ℕ) : ℝ))
          * ∑' j : ℕ, ((j : ℝ) + 1) * modeMean (eqgQ σ (p : ℕ)) j) := by
  rw [orderExpectation_eq,
    ENNReal.ofReal_tsum_of_nonneg
      (fun p => mul_nonneg (log_prime_nonneg p)
        (tsum_nonneg fun j => mul_nonneg (by positivity)
          (modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) j)))
      (summable_primes_log_mul_tsum_depthMean σ)]
  refine tsum_congr fun p => ?_
  rw [ENNReal.ofReal_mul (log_prime_nonneg p),
    ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (by positivity)
        (modeMean_nonneg (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le) j))
      (summable_depthMean (eqgQ_pos σ p.2.pos).le (eqgQ_lt_one σ p.2.two_le)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ratio_div_one_sub_eq_modeMean σ p j,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((j : ℝ) + 1) * Real.log (((p : ℕ) : ℝ))),
    ← ENNReal.ofReal_mul (log_prime_nonneg p)]
  congr 1
  ring

theorem orderExpectation_temperature_ne_top (σ : EulerSigma) :
    orderExpectation (AbelianZetaParameters.temperatureParameters σ.val σ.pos) ≠ ⊤ := by
  rw [orderExpectation_temperature_eq_ofReal σ]
  exact ENNReal.ofReal_ne_top

/-! ## (GAS.14) — the temperature deformation -/

/-- The deformed temperature `σ + u`. -/
def sigmaShift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) : EulerSigma where
  val := σ.val + u
  one_lt := by linarith [σ.one_lt]

/-- **The temperature deformation multiplies the Gibbs weight by `|A|^{−u}`.** -/
theorem twoObservableWeight_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u)
    (A : AbelianZetaGroupClass) :
    abelianZetaTwoObservableWeight
        (AbelianZetaParameters.temperatureParameters (sigmaShift σ u hu).val
          (sigmaShift σ u hu).pos) A
      = abelianZetaTwoObservableWeight
          (AbelianZetaParameters.temperatureParameters σ.val σ.pos) A
        * (((A.order : ℝ)) ^ (-u)) := by
  have horder : (0 : ℝ) < ((A.order : ℝ)) := by exact_mod_cast A.order_pos
  rw [abelianZetaTwoObservableWeight, abelianZetaTwoObservableWeight]
  show ((A.order : ℝ)) ^ (-(σ.val + u)) * ((A.socleOrder : ℝ)) ^ (-(0 : ℝ))
      = ((A.order : ℝ)) ^ (-σ.val) * ((A.socleOrder : ℝ)) ^ (-(0 : ℝ))
        * (((A.order : ℝ)) ^ (-u))
  rw [show -(σ.val + u) = -σ.val + -u by ring, Real.rpow_add horder]
  ring

/-- The shifted temperature in the convergence chamber. -/
def temperatureConvShift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    AbelianZetaConvergentParameters := temperatureConv (sigmaShift σ u hu)

/-- The constant in the Radon–Nikodym density of the temperature deformation. -/
def densityConstShift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) : ℝ≥0∞ :=
  (temperatureConvShift σ u hu).ennNormalizer / (temperatureConv σ).ennNormalizer

theorem densityConstShift_ne_zero (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    densityConstShift σ u hu ≠ 0 := by
  rw [densityConstShift]
  exact ENNReal.div_ne_zero.mpr
    ⟨AbelianZetaConvergentParameters.ennNormalizer_ne_zero _, ennNormalizer_ne_top _⟩

theorem densityConstShift_ne_top (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    densityConstShift σ u hu ≠ ⊤ := by
  rw [densityConstShift]
  exact ENNReal.div_ne_top (ennNormalizer_ne_top _)
    (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)

theorem densityConstShift_toReal_pos (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    0 < (densityConstShift σ u hu).toReal :=
  ENNReal.toReal_pos (densityConstShift_ne_zero σ u hu) (densityConstShift_ne_top σ u hu)

/-- **The deformed law is a density against the undeformed one.** -/
theorem classLaw_shift_eq_withDensity (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters
      = (classLaw (temperatureConv σ).toAbelianZetaParameters).withDensity
        (fun A => densityConstShift σ u hu * ENNReal.ofReal (((A.order : ℝ)) ^ (-u))) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [classLaw_singleton, withDensity_singleton, classLaw_singleton,
    (temperatureConvShift σ u hu).classMass_eq_ennNormalizer_mul_twoObservableWeight A,
    (temperatureConv σ).classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  have hw : (0 : ℝ) ≤ abelianZetaTwoObservableWeight
      (temperatureConv σ).toAbelianZetaParameters A :=
    AbelianZetaConvergentParameters.twoObservableWeight_nonneg _ A
  have hs : (0 : ℝ) ≤ (((A.order : ℝ)) ^ (-u)) :=
    Real.rpow_nonneg (by positivity) _
  have hweq : abelianZetaTwoObservableWeight
      (temperatureConvShift σ u hu).toAbelianZetaParameters A
      = abelianZetaTwoObservableWeight (temperatureConv σ).toAbelianZetaParameters A
        * (((A.order : ℝ)) ^ (-u)) := twoObservableWeight_shift σ u hu A
  rw [hweq, ENNReal.ofReal_mul hw]
  have hne : (temperatureConv σ).ennNormalizer ≠ 0 :=
    AbelianZetaConvergentParameters.ennNormalizer_ne_zero _
  have hc : (temperatureConvShift σ u hu).ennNormalizer / (temperatureConv σ).ennNormalizer
      * (temperatureConv σ).ennNormalizer = (temperatureConvShift σ u hu).ennNormalizer :=
    ENNReal.div_mul_cancel hne (ennNormalizer_ne_top _)
  rw [densityConstShift]
  conv_lhs => rw [← hc]
  ring

/-- **The Radon–Nikodym derivative of the temperature deformation.** -/
theorem rnDeriv_classLaw_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters).rnDeriv
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (temperatureConv σ).toAbelianZetaParameters]
        fun A => densityConstShift σ u hu * ENNReal.ofReal (((A.order : ℝ)) ^ (-u)) := by
  have hmeas : Measurable fun A : AbelianZetaGroupClass =>
      densityConstShift σ u hu * ENNReal.ofReal (((A.order : ℝ)) ^ (-u)) := fun _ _ => trivial
  rw [classLaw_shift_eq_withDensity σ u hu]
  exact Measure.rnDeriv_withDensity _ hmeas

theorem llr_classLaw_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    llr (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (temperatureConv σ).toAbelianZetaParameters]
        fun A => Real.log ((densityConstShift σ u hu).toReal)
          - u * Real.log (((A.order : ℝ))) := by
  filter_upwards [rnDeriv_classLaw_shift σ u hu] with A hA
  show Real.log ((classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters).rnDeriv
      (classLaw (temperatureConv σ).toAbelianZetaParameters) A).toReal = _
  have hord : (0 : ℝ) < ((A.order : ℝ)) := by exact_mod_cast A.order_pos
  have hc : (0 : ℝ) < (densityConstShift σ u hu).toReal := densityConstShift_toReal_pos σ u hu
  have hpow : (0 : ℝ) < (((A.order : ℝ)) ^ (-u)) := Real.rpow_pos_of_pos hord _
  rw [hA, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hord.le _),
    Real.log_mul hc.ne' hpow.ne', Real.log_rpow hord]
  ring

/-! ## The order observable is integrable -/

theorem logOrder_nonneg (A : AbelianZetaGroupClass) :
    (0 : ℝ) ≤ Real.log ((A.order : ℕ) : ℝ) :=
  Real.log_nonneg (by exact_mod_cast A.order_pos)

theorem measurable_logOrder :
    Measurable fun A : AbelianZetaGroupClass => Real.log ((A.order : ℕ) : ℝ) :=
  fun _ _ => trivial

/-- **The mean order observable is the order expectation.** -/
theorem integral_classLaw_logOrder (θ : AbelianZetaConvergentParameters) :
    ∫ A, Real.log ((A.order : ℕ) : ℝ) ∂(classLaw θ.toAbelianZetaParameters)
      = (orderExpectation θ.toAbelianZetaParameters).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun A => logOrder_nonneg A)
      measurable_logOrder.aestronglyMeasurable,
    lintegral_classLaw_logOrder θ]

theorem integrable_classLaw_logOrder (θ : AbelianZetaConvergentParameters)
    (h : orderExpectation θ.toAbelianZetaParameters ≠ ⊤) :
    Integrable (fun A : AbelianZetaGroupClass => Real.log ((A.order : ℕ) : ℝ))
      (classLaw θ.toAbelianZetaParameters) := by
  refine integrable_classLaw _ _ ?_
  have hrw : (∑' A : AbelianZetaGroupClass,
        ENNReal.ofReal ‖Real.log ((A.order : ℕ) : ℝ)‖
          * abelianZetaClassMass θ.toAbelianZetaParameters A)
      = ∫⁻ A, ENNReal.ofReal (Real.log ((A.order : ℕ) : ℝ))
          ∂(classLaw θ.toAbelianZetaParameters) := by
    rw [lintegral_classLaw]
    exact tsum_congr fun A => by rw [Real.norm_of_nonneg (logOrder_nonneg A)]
  rw [hrw, lintegral_classLaw_logOrder θ]
  exact h

theorem orderExpectation_conv_ne_top (σ : EulerSigma) :
    orderExpectation (temperatureConv σ).toAbelianZetaParameters ≠ ⊤ :=
  orderExpectation_temperature_ne_top σ

/-! ## The reverse density of the temperature deformation -/

theorem classLaw_temperatureConv_eq_withDensity_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    classLaw (temperatureConv σ).toAbelianZetaParameters
      = (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters).withDensity
        (fun A => (densityConstShift σ u hu)⁻¹ * ENNReal.ofReal (((A.order : ℝ)) ^ u)) := by
  refine Measure.ext_of_singleton fun A => ?_
  rw [withDensity_singleton]
  have hmass : classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters {A}
      = densityConstShift σ u hu * ENNReal.ofReal (((A.order : ℝ)) ^ (-u))
        * classLaw (temperatureConv σ).toAbelianZetaParameters {A} := by
    conv_lhs => rw [classLaw_shift_eq_withDensity σ u hu]
    rw [withDensity_singleton]
  have hord : (0 : ℝ) < ((A.order : ℝ)) := by exact_mod_cast A.order_pos
  have hpow : ENNReal.ofReal (((A.order : ℝ)) ^ u)
      * ENNReal.ofReal (((A.order : ℝ)) ^ (-u)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hord.le _), ← Real.rpow_add hord]
    norm_num
  have hdc : (densityConstShift σ u hu)⁻¹ * densityConstShift σ u hu = 1 :=
    ENNReal.inv_mul_cancel (densityConstShift_ne_zero σ u hu) (densityConstShift_ne_top σ u hu)
  rw [hmass]
  calc classLaw (temperatureConv σ).toAbelianZetaParameters {A}
      = ((densityConstShift σ u hu)⁻¹ * densityConstShift σ u hu)
        * (ENNReal.ofReal (((A.order : ℝ)) ^ u)
          * ENNReal.ofReal (((A.order : ℝ)) ^ (-u)))
        * classLaw (temperatureConv σ).toAbelianZetaParameters {A} := by
        rw [hdc, hpow, one_mul, one_mul]
    _ = (densityConstShift σ u hu)⁻¹ * ENNReal.ofReal (((A.order : ℝ)) ^ u)
        * (densityConstShift σ u hu * ENNReal.ofReal (((A.order : ℝ)) ^ (-u))
          * classLaw (temperatureConv σ).toAbelianZetaParameters {A}) := by ring

theorem rnDeriv_classLaw_temperatureConv_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    (classLaw (temperatureConv σ).toAbelianZetaParameters).rnDeriv
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
      =ᵐ[classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters]
        fun A => (densityConstShift σ u hu)⁻¹ * ENNReal.ofReal (((A.order : ℝ)) ^ u) := by
  have hmeas : Measurable fun A : AbelianZetaGroupClass =>
      (densityConstShift σ u hu)⁻¹ * ENNReal.ofReal (((A.order : ℝ)) ^ u) := fun _ _ => trivial
  rw [classLaw_temperatureConv_eq_withDensity_shift σ u hu]
  exact Measure.rnDeriv_withDensity _ hmeas

theorem llr_classLaw_temperatureConv_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
      =ᵐ[classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters]
        fun A => -Real.log ((densityConstShift σ u hu).toReal)
          + u * Real.log (((A.order : ℝ))) := by
  filter_upwards [rnDeriv_classLaw_temperatureConv_shift σ u hu] with A hA
  show Real.log ((classLaw (temperatureConv σ).toAbelianZetaParameters).rnDeriv
      (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters) A).toReal = _
  have hord : (0 : ℝ) < ((A.order : ℝ)) := by exact_mod_cast A.order_pos
  have hc : (0 : ℝ) < (densityConstShift σ u hu).toReal := densityConstShift_toReal_pos σ u hu
  have hpow : (0 : ℝ) < (((A.order : ℝ)) ^ u) := Real.rpow_pos_of_pos hord _
  rw [hA, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hord.le _),
    Real.log_mul (by positivity) hpow.ne', Real.log_inv, Real.log_rpow hord]

/-! ## Theorem 8.1, equation (GAS.14) -/

theorem ac_shift_temperature (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters
      ≪ classLaw (temperatureConv σ).toAbelianZetaParameters :=
  classLaw_absolutelyContinuous (temperatureConv σ) (temperatureConvShift σ u hu)

theorem ac_temperature_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    classLaw (temperatureConv σ).toAbelianZetaParameters
      ≪ classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters :=
  classLaw_absolutelyContinuous (temperatureConvShift σ u hu) (temperatureConv σ)

theorem llr_shift_ae_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    llr (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      =ᵐ[classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters]
        fun A => Real.log ((densityConstShift σ u hu).toReal)
          - u * Real.log (((A.order : ℝ))) :=
  (llr_classLaw_shift σ u hu).filter_mono (ac_shift_temperature σ u hu).ae_le

theorem integrable_llr_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (llr (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters))
      (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters) := by
  refine Integrable.congr ?_ (llr_shift_ae_shift σ u hu).symm
  exact (integrable_const _).sub
    ((integrable_classLaw_logOrder (temperatureConvShift σ u hu)
      (orderExpectation_conv_ne_top (sigmaShift σ u hu))).const_mul u)

theorem integrable_llr_temperature_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters))
      (classLaw (temperatureConv σ).toAbelianZetaParameters) := by
  refine Integrable.congr ?_
    ((llr_classLaw_temperatureConv_shift σ u hu).filter_mono
      (ac_temperature_shift σ u hu).ae_le).symm
  exact (integrable_const _).add
    ((integrable_classLaw_logOrder (temperatureConv σ)
      (orderExpectation_conv_ne_top σ)).const_mul u)

theorem integral_llr_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    ∫ A, llr (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters) A
        ∂(classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
      = Real.log ((densityConstShift σ u hu).toReal)
        - u * (orderExpectation (AbelianZetaParameters.temperatureParameters
            (sigmaShift σ u hu).val (sigmaShift σ u hu).pos)).toReal := by
  rw [integral_congr_ae (llr_shift_ae_shift σ u hu),
    integral_sub (integrable_const _)
      ((integrable_classLaw_logOrder (temperatureConvShift σ u hu)
        (orderExpectation_conv_ne_top (sigmaShift σ u hu))).const_mul u),
    integral_const, integral_const_mul,
    integral_classLaw_logOrder (temperatureConvShift σ u hu),
    probReal_univ, smul_eq_mul, one_mul]
  rfl

theorem integral_llr_temperature_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    ∫ A, llr (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters) A
        ∂(classLaw (temperatureConv σ).toAbelianZetaParameters)
      = -Real.log ((densityConstShift σ u hu).toReal)
        + u * (orderExpectation (AbelianZetaParameters.temperatureParameters
            σ.val σ.pos)).toReal := by
  rw [integral_congr_ae
      ((llr_classLaw_temperatureConv_shift σ u hu).filter_mono
        (ac_temperature_shift σ u hu).ae_le),
    integral_add (integrable_const _)
      ((integrable_classLaw_logOrder (temperatureConv σ)
        (orderExpectation_conv_ne_top σ)).const_mul u),
    integral_const, integral_const_mul, integral_classLaw_logOrder (temperatureConv σ),
    probReal_univ, smul_eq_mul, one_mul]
  rfl

theorem klDiv_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    klDiv (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      = ENNReal.ofReal (Real.log ((densityConstShift σ u hu).toReal)
          - u * (orderExpectation (AbelianZetaParameters.temperatureParameters
              (sigmaShift σ u hu).val (sigmaShift σ u hu).pos)).toReal) := by
  rw [klDiv_of_ac_of_integrable (ac_shift_temperature σ u hu) (integrable_llr_shift σ u hu),
    integral_llr_shift σ u hu, probReal_univ, probReal_univ]
  congr 1
  ring

theorem klDiv_temperature_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
      = ENNReal.ofReal (-Real.log ((densityConstShift σ u hu).toReal)
          + u * (orderExpectation (AbelianZetaParameters.temperatureParameters
              σ.val σ.pos)).toReal) := by
  rw [klDiv_of_ac_of_integrable (ac_temperature_shift σ u hu)
      (integrable_llr_temperature_shift σ u hu),
    integral_llr_temperature_shift σ u hu, probReal_univ, probReal_univ]
  congr 1
  ring

theorem integral_llr_shift_nonneg (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ Real.log ((densityConstShift σ u hu).toReal)
      - u * (orderExpectation (AbelianZetaParameters.temperatureParameters
          (sigmaShift σ u hu).val (sigmaShift σ u hu).pos)).toReal := by
  have h := integral_llr_add_sub_measure_univ_nonneg (ac_shift_temperature σ u hu)
    (integrable_llr_shift σ u hu)
  rw [integral_llr_shift σ u hu, probReal_univ, probReal_univ] at h
  linarith

theorem integral_llr_temperature_shift_nonneg (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ -Real.log ((densityConstShift σ u hu).toReal)
      + u * (orderExpectation (AbelianZetaParameters.temperatureParameters
          σ.val σ.pos)).toReal := by
  have h := integral_llr_add_sub_measure_univ_nonneg (ac_temperature_shift σ u hu)
    (integrable_llr_temperature_shift σ u hu)
  rw [integral_llr_temperature_shift σ u hu, probReal_univ, probReal_univ] at h
  linarith

/-- **The temperature deformation lowers the order mean.** -/
theorem orderExpectation_shift_le (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u * ((orderExpectation (AbelianZetaParameters.temperatureParameters σ.val σ.pos)).toReal
      - (orderExpectation (AbelianZetaParameters.temperatureParameters
          (sigmaShift σ u hu).val (sigmaShift σ u hu).pos)).toReal) := by
  have h1 := integral_llr_shift_nonneg σ u hu
  have h2 := integral_llr_temperature_shift_nonneg σ u hu
  nlinarith

/-- **Theorem 8.1, equation (GAS.14).**  The symmetrised relative entropy of the temperature
deformation is `u` times the drop of the order mean, and is nonnegative. -/
theorem klDiv_symmetrised_temperature_shift (σ : EulerSigma) (u : ℝ) (hu : 0 ≤ u) :
    klDiv (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
        (classLaw (temperatureConv σ).toAbelianZetaParameters)
      + klDiv (classLaw (temperatureConv σ).toAbelianZetaParameters)
        (classLaw (temperatureConvShift σ u hu).toAbelianZetaParameters)
      = ENNReal.ofReal (u
          * ((orderExpectation (AbelianZetaParameters.temperatureParameters
              σ.val σ.pos)).toReal
            - (orderExpectation (AbelianZetaParameters.temperatureParameters
              (sigmaShift σ u hu).val (sigmaShift σ u hu).pos)).toReal)) := by
  rw [klDiv_shift σ u hu, klDiv_temperature_shift σ u hu,
    ← ENNReal.ofReal_add (integral_llr_shift_nonneg σ u hu)
      (integral_llr_temperature_shift_nonneg σ u hu)]
  congr 1
  ring

end

end GaloisForLFunctions.HTGeometry
