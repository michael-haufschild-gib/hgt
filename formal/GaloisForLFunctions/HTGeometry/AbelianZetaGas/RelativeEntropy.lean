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

end

end GaloisForLFunctions.HTGeometry
