import GaloisForLFunctions.HTGeometry.BetaGammaFactorization
import GaloisForLFunctions.HTGeometry.IndependentCoordinateLift
import GaloisForLFunctions.HTGeometry.PrimeHodgeResidueClock
import GaloisForLFunctions.RHTower.ThetaMellinSixHodgeFormation

/-!
# Theta–prime beta–gamma projective recovery

Take independent `X ~ Gamma(3/2, π)` and `Y ~ Gamma(3, π)`, and put `V = X + Y`, `U = X/V`.

* **Projective gamma factorization.**  `U ~ Beta(3/2, 3)` and `V ~ Gamma(9/2, π)` are
  independent.
* **Theta Mellin-six identity.**  With `G_θ = Γ_ℝ`, `G_θ(2n+3)/G_θ(3) = E[Xⁿ]`,
  `G_θ(2n+9)/G_θ(9) = E[Vⁿ]`, and the normalized six-unit holonomy is
  `H_n = E[Xⁿ]/E[Vⁿ] = E[Uⁿ] = m_n = 105/((2n+3)(2n+5)(2n+7))`.
* **Signed prime recovery.**  For an independent symmetric sign `ε`, `D = ε√U` has the signed
  prime-pair Cayley law `(105/16) d²(1-d²)² 1_{(-1,1)}`; with `E = √(1-U)`, `D² + E² = 1`,
  `E[D^{2n}] = m_n` and `E[D^{2n}E²] = w_n`.
* **Projective recovery.**  The insertion `J` of the independent Gamma coordinate is an isometry,
  its adjoint `P` is integration over the Gamma coordinate, `P J = I`, and every bounded source
  multiplier commutes with `J` and `P`.
* **Relative curvature as information gain.**  The survival tilts `uⁿ Beta(3/2, 3)/m_n` are
  `Beta(n+3/2, 3)`; `r_n = E_{μ_n}[U]`, `h_n = 1 - r_n`, `w_n = m_n h_n`, and
  `κ_n = r_n - r_{n-1} = Var_{μ_{n-1}}(U)/E_{μ_{n-1}}[U] = 12/((2n+7)(2n+9))`.
* **Lift invariance and zero horizon.**  Isometric lifting `T ↦ J T J*` along the Gamma coordinate
  preserves all matrix entries, positivity, approximation numbers and traces; on the source,
  `M_{Uᴺ} → 0` strongly and `M_{1_{U=1}} = 0`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Projective gamma factorization -/

/-- **Theorem BGPR-A.**  `(X/(X+Y), X+Y) ~ Beta(3/2, 3) ⊗ Gamma(9/2, π)`. -/
theorem thetaPrime_projectiveGammaFactorization :
    Measure.map projectiveSum ((gammaMeasure (3 / 2) Real.pi).prod (gammaMeasure 3 Real.pi)) =
      (betaMeasure (3 / 2) 3).prod (gammaMeasure (9 / 2) Real.pi) := by
  rw [map_projectiveSum_gammaMeasure_prod (by norm_num) (by norm_num) Real.pi_pos]
  norm_num

/-! ### The theta Mellin-six identity -/

/-- `Γ(a+3) = (a+2)(a+1) a Γ(a)`. -/
theorem Gamma_add_three {a : ℝ} (ha : 0 < a) :
    Real.Gamma (a + 3) = (a + 2) * (a + 1) * a * Real.Gamma a := by
  rw [show a + 3 = (a + 2) + 1 by ring, Real.Gamma_add_one (by linarith),
    show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one (by linarith), Real.Gamma_add_one ha.ne']
  ring

/-- **Beta(3/2, 3) moments are the history tails**: `E[Uⁿ] = m_n`. -/
theorem integral_pow_betaMeasure_threeHalves_three (n : ℕ) :
    ∫ u, u ^ n ∂betaMeasure (3 / 2) 3 = PrimeHodgeHistory.m n := by
  rw [integral_pow_betaMeasure (by norm_num) (by norm_num) n,
    show (3 / 2 : ℝ) + 3 + n = ((3 / 2 : ℝ) + n) + 3 by ring,
    Gamma_add_three (a := 3 / 2 + n) (by positivity), Gamma_add_three (a := 3 / 2) (by norm_num),
    PrimeHodgeHistory.m]
  have hΓ := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3 / 2 + n)
  have hΓ0 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  push_cast
  field_simp
  ring

theorem integral_pow_gammaMeasure_pi {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ∫ x, x ^ n ∂gammaMeasure a Real.pi = Real.Gamma (a + n) / (Real.Gamma a * Real.pi ^ n) :=
  integral_pow_gammaMeasure ha Real.pi_pos n

/-- `Γ_ℝ(2a + 2n) / Γ_ℝ(2a) = Γ(a+n)/(Γ(a) πⁿ)`. -/
theorem gammaReal_ratio_shift {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Complex.Gammaℝ ((2 * a + 2 * n : ℝ) : ℂ) / Complex.Gammaℝ ((2 * a : ℝ) : ℂ) =
      ((Real.Gamma (a + n) / (Real.Gamma a * Real.pi ^ n) : ℝ) : ℂ) := by
  rw [_root_.RHTower.gammaReal_ofReal, _root_.RHTower.gammaReal_ofReal, ← Complex.ofReal_div]
  congr 1
  have hpi := Real.pi_pos
  have hΓ := Real.Gamma_pos_of_pos ha
  rw [show (2 * a + 2 * n) / 2 = a + n by ring, show 2 * a / 2 = a by ring,
    show -(2 * a + 2 * n) / 2 = -a + -(n : ℝ) by ring, show -(2 * a) / 2 = -a by ring,
    Real.rpow_add hpi, Real.rpow_neg hpi.le (n : ℝ), Real.rpow_natCast]
  have hpa : 0 < Real.pi ^ (-a) := Real.rpow_pos_of_pos hpi _
  field_simp

/-- **(BGPR.6), source leg.**  `G_θ(2n+3)/G_θ(3) = E[Xⁿ]` for `X ~ Gamma(3/2, π)`. -/
theorem gammaReal_ratio_three (n : ℕ) :
    Complex.Gammaℝ ((2 * n + 3 : ℕ) : ℂ) / Complex.Gammaℝ 3 =
      ((∫ x, x ^ n ∂gammaMeasure (3 / 2) Real.pi : ℝ) : ℂ) := by
  have h := gammaReal_ratio_shift (a := 3 / 2) (by norm_num) n
  rw [integral_pow_gammaMeasure_pi (by norm_num), ← h]
  congr 2 <;> push_cast <;> ring

/-- **(BGPR.6), completion leg.**  `G_θ(2n+9)/G_θ(9) = E[Vⁿ]` for `V ~ Gamma(9/2, π)`. -/
theorem gammaReal_ratio_nine (n : ℕ) :
    Complex.Gammaℝ ((2 * n + 9 : ℕ) : ℂ) / Complex.Gammaℝ 9 =
      ((∫ v, v ^ n ∂gammaMeasure (9 / 2) Real.pi : ℝ) : ℂ) := by
  have h := gammaReal_ratio_shift (a := 9 / 2) (by norm_num) n
  rw [integral_pow_gammaMeasure_pi (by norm_num), ← h]
  congr 2 <;> push_cast <;> ring

/-- **(BGPR.7).**  The normalized theta Mellin-six holonomy is the ratio of the source and
completion moments, equal to the Beta moment and to the history tail:
`H_n = E[Xⁿ]/E[Vⁿ] = E[Uⁿ] = m_n`. -/
theorem thetaCuspMellinSixHolonomy_eq_betaMoment (n : ℕ) :
    _root_.RHTower.thetaCuspMellinSixHolonomy n =
        (((∫ x, x ^ n ∂gammaMeasure (3 / 2) Real.pi) /
          ∫ v, v ^ n ∂gammaMeasure (9 / 2) Real.pi : ℝ) : ℂ) ∧
      (∫ x, x ^ n ∂gammaMeasure (3 / 2) Real.pi) / (∫ v, v ^ n ∂gammaMeasure (9 / 2) Real.pi) =
        ∫ u, u ^ n ∂betaMeasure (3 / 2) 3 ∧
      ∫ u, u ^ n ∂betaMeasure (3 / 2) 3 = PrimeHodgeHistory.m n := by
  have hV : 0 < ∫ v, v ^ n ∂gammaMeasure (9 / 2) Real.pi := by
    rw [integral_pow_gammaMeasure_pi (by norm_num)]
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 9 / 2 + n)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 9 / 2)
    have := Real.pi_pos
    positivity
  have hfac := integral_pow_gammaMeasure_eq_mul (a := 3 / 2) (b := 3) (r := Real.pi)
    (by norm_num) (by norm_num) Real.pi_pos n
  rw [show (3 / 2 : ℝ) + 3 = 9 / 2 by norm_num] at hfac
  have hratio : (∫ x, x ^ n ∂gammaMeasure (3 / 2) Real.pi) /
      (∫ v, v ^ n ∂gammaMeasure (9 / 2) Real.pi) = ∫ u, u ^ n ∂betaMeasure (3 / 2) 3 := by
    rw [hfac, mul_div_assoc, div_self hV.ne', mul_one]
  refine ⟨?_, hratio, integral_pow_betaMeasure_threeHalves_three n⟩
  rw [_root_.RHTower.thetaCuspMellinSixHolonomy_eq_primeHodgeHistory_m, hratio,
    integral_pow_betaMeasure_threeHalves_three]

/-! ### Relative curvature is posterior information gain -/

/-- **(BGPR.14).**  The survival-tilted law `uⁿ Beta(3/2, 3)/m_n` is `Beta(n + 3/2, 3)`. -/
theorem survivalTilt_betaMeasure (n : ℕ) :
    (betaMeasure (3 / 2) 3).withDensity
        (fun u => ENNReal.ofReal (u ^ n / PrimeHodgeHistory.m n)) =
      betaMeasure (n + 3 / 2) 3 := by
  have h := withDensity_pow_betaMeasure (a := 3 / 2) (b := 3) (by norm_num) (by norm_num) n
  rw [integral_pow_betaMeasure_threeHalves_three, add_comm] at h
  exact h

/-- **(BGPR.15), survival ratio**: `r_n = m_{n+1}/m_n = E_{μ_n}[U]`. -/
theorem survivalRatio_eq_tiltMean (n : ℕ) :
    PrimeHodgeHistory.survivalRatio n = ∫ u, u ∂betaMeasure (n + 3 / 2) 3 := by
  rw [integral_id_betaMeasure (by positivity) (by norm_num),
    PrimeHodgeHistory.survivalRatio_formula]
  push_cast
  field_simp
  ring

/-- **(BGPR.15), exit hazard**: `h_n = 1 - r_n = E_{μ_n}[1 - U]`. -/
theorem exitHazard_eq_tiltMean (n : ℕ) :
    PrimeHodgeHistory.exitHazard n = ∫ u, (1 - u) ∂betaMeasure (n + 3 / 2) 3 := by
  haveI := betaMeasure_isProbability (by positivity : (0 : ℝ) < n + 3 / 2)
    (by norm_num : (0 : ℝ) < 3)
  have hi : Integrable (fun u : ℝ => u) (betaMeasure (n + 3 / 2) 3) := by
    simpa using integrable_pow_betaMeasure (by positivity : (0 : ℝ) < n + 3 / 2) (by norm_num) 1
  rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul,
    ← survivalRatio_eq_tiltMean, PrimeHodgeHistory.exitHazard]

/-- **(BGPR.15), exit weight**: `w_n = m_n h_n`. -/
theorem w_eq_m_mul_tiltExit (n : ℕ) :
    PrimeHodgeHistory.w n = PrimeHodgeHistory.m n * ∫ u, (1 - u) ∂betaMeasure (n + 3 / 2) 3 := by
  rw [← exitHazard_eq_tiltMean, PrimeHodgeHistory.w_eq_m_mul_exitHazard]

/-- **(BGPR.16).**  For `n ≥ 1`, the relative-curvature weight is the normalized posterior
variance: `κ_n = r_n - r_{n-1} = Var_{μ_{n-1}}(U)/E_{μ_{n-1}}[U] = 12/((2n+7)(2n+9))`. -/
theorem relativeCurvatureWeight_eq_posteriorVariance (k : ℕ) :
    PrimeHodgeHistory.relativeCurvatureWeight (k + 1) =
        PrimeHodgeHistory.survivalRatio (k + 1) - PrimeHodgeHistory.survivalRatio k ∧
      PrimeHodgeHistory.survivalRatio (k + 1) - PrimeHodgeHistory.survivalRatio k =
        (∫ u, (u - ∫ x, x ∂betaMeasure (k + 3 / 2) 3) ^ 2 ∂betaMeasure (k + 3 / 2) 3) /
          ∫ u, u ∂betaMeasure (k + 3 / 2) 3 ∧
      PrimeHodgeHistory.relativeCurvatureWeight (k + 1) =
        12 / ((2 * ((k + 1 : ℕ) : ℝ) + 7) * (2 * ((k + 1 : ℕ) : ℝ) + 9)) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [survivalRatio_eq_tiltMean, survivalRatio_eq_tiltMean,
      ← integral_id_betaMeasure_succ_sub (by positivity) (by norm_num)]
    congr 3
    push_cast
    ring
  · rw [PrimeHodgeHistory.relativeCurvatureWeight_succ]
    push_cast
    ring_nf

/-! ### Signed prime recovery -/

/-- The symmetric sign law `(δ₋₁ + δ₁)/2`. -/
def rademacherSign : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

theorem lintegral_rademacherSign (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂rademacherSign = 2⁻¹ * (f (-1) + f 1) := by
  rw [rademacherSign, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac,
    lintegral_dirac, smul_eq_mul]

instance isProbabilityMeasure_rademacherSign : IsProbabilityMeasure rademacherSign := by
  constructor
  rw [← lintegral_one, lintegral_rademacherSign]
  rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem ae_rademacherSign : ∀ᵐ x ∂rademacherSign, x = -1 ∨ x = 1 := by
  rw [rademacherSign]
  refine Measure.ae_smul_measure ?_ _
  rw [ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq]
  exact ⟨Filter.eventually_pure.mpr (Or.inl rfl), Filter.eventually_pure.mpr (Or.inr rfl)⟩

/-- The source law `Rademacher ⊗ Beta(3/2, 3)` of `(ε, U)`. -/
def thetaPrimeSourceLaw : Measure (ℝ × ℝ) := rademacherSign.prod (betaMeasure (3 / 2) 3)

instance isProbabilityMeasure_betaThreeHalves : IsProbabilityMeasure (betaMeasure (3 / 2) 3) :=
  betaMeasure_isProbability (by norm_num) (by norm_num)

instance isProbabilityMeasure_thetaPrimeSourceLaw : IsProbabilityMeasure thetaPrimeSourceLaw := by
  unfold thetaPrimeSourceLaw
  infer_instance

/-- The signed survival coordinate `D = ε √U`. -/
def signedSurvivalCoord (p : ℝ × ℝ) : ℝ := p.1 * Real.sqrt p.2

/-- The exit coordinate `E = √(1 - U)`. -/
def exitCoord (p : ℝ × ℝ) : ℝ := Real.sqrt (1 - p.2)

theorem ae_thetaPrimeSourceLaw :
    ∀ᵐ p ∂thetaPrimeSourceLaw, (p.1 = -1 ∨ p.1 = 1) ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  have h1 := (measurePreserving_fst (μ := rademacherSign)
    (ν := betaMeasure (3 / 2) 3)).quasiMeasurePreserving.ae ae_rademacherSign
  have h2 := (measurePreserving_snd (μ := rademacherSign)
    (ν := betaMeasure (3 / 2) 3)).quasiMeasurePreserving.ae (ae_mem_Ioo_betaMeasure (3 / 2) 3)
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **(BGPR.10)**: `D² + E² = 1`. -/
theorem signedSurvival_sq_add_exit_sq :
    ∀ᵐ p ∂thetaPrimeSourceLaw, signedSurvivalCoord p ^ 2 + exitCoord p ^ 2 = 1 := by
  filter_upwards [ae_thetaPrimeSourceLaw] with p hp
  have hs1 : p.1 ^ 2 = 1 := by rcases hp.1 with h | h <;> rw [h] <;> norm_num
  rw [signedSurvivalCoord, exitCoord, mul_pow, hs1, one_mul, Real.sq_sqrt hp.2.1.le,
    Real.sq_sqrt (by linarith [hp.2.2])]
  ring

theorem signedSurvival_pow_even :
    ∀ᵐ p ∂thetaPrimeSourceLaw, ∀ n : ℕ, signedSurvivalCoord p ^ (2 * n) = p.2 ^ n := by
  filter_upwards [ae_thetaPrimeSourceLaw] with p hp n
  have hs1 : p.1 ^ 2 = 1 := by rcases hp.1 with h | h <;> rw [h] <;> norm_num
  rw [pow_mul, signedSurvivalCoord, mul_pow, hs1, one_mul, Real.sq_sqrt hp.2.1.le]

theorem integral_snd_pow_thetaPrimeSourceLaw (n : ℕ) :
    ∫ p, p.2 ^ n ∂thetaPrimeSourceLaw = PrimeHodgeHistory.m n := by
  have := integral_fun_snd (μ := rademacherSign) (ν := betaMeasure (3 / 2) 3)
    (fun u : ℝ => u ^ n)
  simp only [probReal_univ, one_smul] at this
  rw [thetaPrimeSourceLaw, this, integral_pow_betaMeasure_threeHalves_three]

/-- **(BGPR.10)**: `E[D^{2n}] = m_n`. -/
theorem integral_signedSurvival_pow (n : ℕ) :
    ∫ p, signedSurvivalCoord p ^ (2 * n) ∂thetaPrimeSourceLaw = PrimeHodgeHistory.m n := by
  rw [integral_congr_ae (signedSurvival_pow_even.mono fun p hp => hp n),
    integral_snd_pow_thetaPrimeSourceLaw]

/-- **(BGPR.10)**: `E[D^{2n} E²] = m_n - m_{n+1} = w_n`. -/
theorem integral_signedSurvival_pow_mul_exit_sq (n : ℕ) :
    ∫ p, signedSurvivalCoord p ^ (2 * n) * exitCoord p ^ 2 ∂thetaPrimeSourceLaw =
      PrimeHodgeHistory.w n := by
  have hae : ∀ᵐ p ∂thetaPrimeSourceLaw,
      signedSurvivalCoord p ^ (2 * n) * exitCoord p ^ 2 = p.2 ^ n - p.2 ^ (n + 1) := by
    filter_upwards [ae_thetaPrimeSourceLaw, signedSurvival_pow_even] with p hp hpow
    rw [hpow n, exitCoord, Real.sq_sqrt (by linarith [hp.2.2]), pow_succ]
    ring
  have hint : ∀ k : ℕ, Integrable (fun p : ℝ × ℝ => p.2 ^ k) thetaPrimeSourceLaw := fun k =>
    Integrable.of_bound (C := 1) (by fun_prop) (ae_thetaPrimeSourceLaw.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_pow, abs_of_pos hp.2.1]
      exact pow_le_one₀ hp.2.1.le hp.2.2.le)
  rw [integral_congr_ae hae, integral_sub (hint n) (hint (n + 1)),
    integral_snd_pow_thetaPrimeSourceLaw, integral_snd_pow_thetaPrimeSourceLaw,
    PrimeHodgeHistory.w]

/-- The Beta(3/2, 3) normalizer is `16/105`. -/
theorem beta_threeHalves_three : beta (3 / 2) 3 = 16 / 105 := by
  have hG3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one]
    norm_num
  have hG := Gamma_add_three (a := 3 / 2) (by norm_num)
  have hΓ := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  rw [beta, hG3, show (3 / 2 : ℝ) + 3 = 3 / 2 + 3 by ring, hG]
  field_simp
  ring

/-- Under `u = d²`, the Beta(3/2, 3) law becomes twice the Hodge density on `(0, 1)`. -/
theorem lintegral_betaThreeHalves_sqrt {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ u, G (Real.sqrt u) ∂betaMeasure (3 / 2) 3 =
      ∫⁻ d in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * hodgeSpectralDensity d) * G d := by
  have hβ := measurable_betaPDF (3 / 2) 3
  have himg : (fun d : ℝ => d ^ 2) '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext u
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨by nlinarith [hd.1], by nlinarith [hd.1, hd.2]⟩
    · intro hu
      refine ⟨Real.sqrt u, ⟨Real.sqrt_pos.mpr hu.1, ?_⟩, Real.sq_sqrt hu.1.le⟩
      rw [Real.sqrt_lt' one_pos]
      linarith [hu.2]
  have hinj : InjOn (fun d : ℝ => d ^ 2) (Ioo (0 : ℝ) 1) := fun x hx y hy hxy =>
    (sq_eq_sq₀ hx.1.le hy.1.le).mp hxy
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul₀ hβ.aemeasurable]
  · have hout : ∀ u, betaPDF (3 / 2) 3 u * G (Real.sqrt u) =
        (Ioo (0 : ℝ) 1).indicator (fun u => betaPDF (3 / 2) 3 u * G (Real.sqrt u)) u := by
      intro u
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu, betaPDF_eq]
        simp [show ¬ (0 < u ∧ u < 1) from hu]
    show ∫⁻ u, betaPDF (3 / 2) 3 u * G (Real.sqrt u) = _
    rw [lintegral_congr hout, lintegral_indicator measurableSet_Ioo, ← himg,
      lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
        (fun x _ => (hasDerivAt_pow 2 x).hasDerivWithinAt) hinj, himg]
    refine setLIntegral_congr_fun measurableSet_Ioo fun d hd => ?_
    rw [Real.sqrt_sq hd.1.le, betaPDF_of_pos_lt_one (by nlinarith [hd.1])
      (by nlinarith [hd.1, hd.2]), beta_threeHalves_three, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 2
    rw [abs_of_pos (mul_pos (by norm_num) (pow_pos hd.1 _) : (0 : ℝ) < (2 : ℕ) * d ^ (2 - 1)),
      show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, show (3 : ℝ) - 1 = (2 : ℕ) by norm_num,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.sqrt_sq hd.1.le, hodgeSpectralDensity]
    push_cast
    ring
  · exact (hG.comp Real.continuous_sqrt.measurable).aemeasurable

theorem hodgeSpectralDensity_neg (d : ℝ) : hodgeSpectralDensity (-d) = hodgeSpectralDensity d := by
  unfold hodgeSpectralDensity
  ring

/-- **Theorem BGPR-B.**  The signed survival coordinate `D = ε√U` has exactly the signed prime-pair
Cayley spectral law `(105/16) d²(1-d²)² 1_{(-1,1)}(d) dd`. -/
theorem map_signedSurvivalCoord :
    Measure.map signedSurvivalCoord thetaPrimeSourceLaw = hodgeSpectralLaw := by
  have hD : Measurable signedSurvivalCoord := by
    unfold signedSurvivalCoord
    fun_prop
  have hh : Measurable fun v => ENNReal.ofReal (hodgeSpectralDensity v) :=
    measurable_hodgeSpectralDensity.ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hD, thetaPrimeSourceLaw,
    lintegral_prod (fun p => F (signedSurvivalCoord p)) (hF.comp hD).aemeasurable,
    lintegral_rademacherSign]
  simp only [signedSurvivalCoord, neg_mul, one_mul]
  have hn := lintegral_betaThreeHalves_sqrt (hF.comp measurable_neg)
  simp only [Function.comp_apply] at hn
  rw [hn, lintegral_betaThreeHalves_sqrt hF]
  -- reflect the negative branch onto `(-1, 0)`
  have himg : (fun x : ℝ => -x) '' Ioo (0 : ℝ) 1 = Ioo (-1 : ℝ) 0 := by
    ext d
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · intro hd
      exact ⟨-d, ⟨by linarith [hd.2], by linarith [hd.1]⟩, neg_neg d⟩
  have hneg : ∫⁻ d in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * hodgeSpectralDensity d) * F (-d) =
      ∫⁻ d in Ioo (-1 : ℝ) 0, ENNReal.ofReal (2 * hodgeSpectralDensity d) * F d := by
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) neg_injective.injOn]
    refine setLIntegral_congr_fun measurableSet_Ioo fun d _ => ?_
    simp [hodgeSpectralDensity_neg]
  rw [hneg]
  -- the target side
  have hsplit : (Ioo (-1 : ℝ) 1 \ {0} : Set ℝ) = Ioo (-1) 0 ∪ Ioo 0 1 := by
    ext d
    simp only [Set.mem_sdiff, mem_Ioo, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨⟨h1, by linarith⟩, by linarith⟩
      · exact ⟨⟨by linarith, h2⟩, by linarith⟩
  have hdisj : Disjoint (Ioo (-1 : ℝ) 0) (Ioo 0 1) :=
    Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
  rw [hodgeSpectralLaw, lintegral_withDensity_eq_lintegral_mul _ hh hF]
  show _ = ∫⁻ d in Ioo (-1 : ℝ) 1, ENNReal.ofReal (hodgeSpectralDensity d) * F d
  rw [← setLIntegral_congr (sdiff_null_ae_eq_self (s := Ioo (-1 : ℝ) 1)
    (measure_singleton (0 : ℝ))), hsplit,
    lintegral_union measurableSet_Ioo hdisj]
  have htwo : ∀ d, ENNReal.ofReal (2 * hodgeSpectralDensity d) * F d =
      2 * (ENNReal.ofReal (hodgeSpectralDensity d) * F d) := fun d => by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]
  simp_rw [htwo]
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num), ← mul_add,
    ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-! ### Information-neutral projective recovery -/

instance isProbabilityMeasure_completionGamma :
    IsProbabilityMeasure (gammaMeasure (9 / 2) Real.pi) :=
  gammaMeasure_isProbability (by norm_num) Real.pi_pos

/-- **Theorem BGPR-C (projective recovery).**  For the completion
`H_complete = H_source ⊗ L²(Gamma(9/2, π))`, the insertion `J` is an isometry, its adjoint `P` is
integration over the Gamma coordinate, `P J = I`, and every bounded source multiplier `M_φ`
commutes with `J` and with `P`. -/
theorem thetaPrime_projectiveRecovery :
    (∀ f : Lp ℂ 2 thetaPrimeSourceLaw,
        ‖coordinateLift thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) f‖ = ‖f‖) ∧
      coordinateRecovery (K := ℂ) thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) ∘L
          (coordinateLift thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi)).toContinuousLinearMap
        = 1 ∧
      (∀ g : Lp ℂ 2 (thetaPrimeSourceLaw.prod (gammaMeasure (9 / 2) Real.pi)),
        (coordinateRecovery thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) g : ℝ × ℝ → ℂ)
          =ᵐ[thetaPrimeSourceLaw]
          fun x => ∫ v, (g : (ℝ × ℝ) × ℝ → ℂ) (x, v) ∂gammaMeasure (9 / 2) Real.pi) ∧
      ∀ {φ : ℝ × ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C),
        lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw.prod (gammaMeasure (9 / 2) Real.pi))
            (hφ.comp measurable_fst) hC0 (fun p => hC p.1) ∘L
            (coordinateLift (K := ℂ) thetaPrimeSourceLaw
              (gammaMeasure (9 / 2) Real.pi)).toContinuousLinearMap =
          (coordinateLift thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi)).toContinuousLinearMap
            ∘L lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw) hφ hC0 hC ∧
        coordinateRecovery (K := ℂ) thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) ∘L
            lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw.prod (gammaMeasure (9 / 2) Real.pi))
              (hφ.comp measurable_fst) hC0 (fun p => hC p.1) =
          lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw) hφ hC0 hC ∘L
            coordinateRecovery thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) :=
  ⟨fun f => (coordinateLift _ _).norm_map f, coordinateRecovery_comp_lift _ _,
    fun g => coeFn_coordinateRecovery _ _ g,
    fun hφ _ hC0 hC => ⟨coordinateLift_comp_mul _ _ hφ hC0 hC,
      mul_comp_coordinateRecovery _ _ hφ hC0 hC⟩⟩

/-- The clamped survival symbol, equal to `D` almost surely. -/
def survivalSymbol (p : ℝ × ℝ) : ℝ := unitClamp (signedSurvivalCoord p)

/-- The clamped exit symbol, equal to `E` almost surely. -/
def exitSymbol (p : ℝ × ℝ) : ℝ := Real.sqrt (1 - survivalSymbol p ^ 2)

theorem measurable_survivalSymbol : Measurable survivalSymbol := by
  unfold survivalSymbol signedSurvivalCoord
  exact measurable_unitClamp.comp (by fun_prop)

theorem measurable_exitSymbol : Measurable exitSymbol := by
  unfold exitSymbol
  exact (measurable_const.sub (measurable_survivalSymbol.pow_const 2)).sqrt

theorem survivalSymbol_ae_eq : survivalSymbol =ᵐ[thetaPrimeSourceLaw] signedSurvivalCoord := by
  filter_upwards [ae_thetaPrimeSourceLaw] with p hp
  refine unitClamp_of_mem ?_
  have hs : Real.sqrt p.2 < 1 := (Real.sqrt_lt' one_pos).mpr (by linarith [hp.2.2])
  have hs0 : 0 ≤ Real.sqrt p.2 := Real.sqrt_nonneg _
  unfold signedSurvivalCoord
  rcases hp.1 with h | h <;> rw [h] <;> constructor <;> linarith

theorem exitSymbol_ae_eq : exitSymbol =ᵐ[thetaPrimeSourceLaw] exitCoord := by
  filter_upwards [survivalSymbol_ae_eq, ae_thetaPrimeSourceLaw] with p hp hq
  have hs1 : p.1 ^ 2 = 1 := by rcases hq.1 with h | h <;> rw [h] <;> norm_num
  rw [exitSymbol, hp, exitCoord, signedSurvivalCoord, mul_pow, hs1, one_mul,
    Real.sq_sqrt hq.2.1.le]

/-- The finite record symbol `E Dⁿ` (as a complex multiplier bounded by one). -/
def recordSymbol (n : ℕ) (p : ℝ × ℝ) : ℂ := ((exitSymbol p * survivalSymbol p ^ n : ℝ) : ℂ)

theorem measurable_recordSymbol (n : ℕ) : Measurable (recordSymbol n) :=
  Complex.measurable_ofReal.comp (measurable_exitSymbol.mul (measurable_survivalSymbol.pow_const n))

theorem norm_recordSymbol_le (n : ℕ) (p : ℝ × ℝ) : ‖recordSymbol n p‖ ≤ 1 := by
  rw [recordSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow]
  have h1 : |survivalSymbol p| ≤ 1 := abs_unitClamp_le_one _
  have h2 : |exitSymbol p| ≤ 1 := abs_sqrt_one_sub_sq_le_one _
  calc |exitSymbol p| * |survivalSymbol p| ^ n ≤ 1 * 1 := by
        gcongr
        exact pow_le_one₀ (abs_nonneg _) h1
    _ = 1 := one_mul 1

/-- **Every finite record `E Dⁿ` lifts and recovers without loss.** -/
theorem record_lift_recover (n : ℕ) :
    lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw.prod (gammaMeasure (9 / 2) Real.pi))
          ((measurable_recordSymbol n).comp measurable_fst) zero_le_one
          (fun q => norm_recordSymbol_le n q.1) ∘L
          (coordinateLift (K := ℂ) thetaPrimeSourceLaw
            (gammaMeasure (9 / 2) Real.pi)).toContinuousLinearMap =
        (coordinateLift thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi)).toContinuousLinearMap ∘L
          lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw) (measurable_recordSymbol n)
            zero_le_one (norm_recordSymbol_le n) ∧
      coordinateRecovery (K := ℂ) thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) ∘L
          lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw.prod (gammaMeasure (9 / 2) Real.pi))
            ((measurable_recordSymbol n).comp measurable_fst) zero_le_one
            (fun q => norm_recordSymbol_le n q.1) =
        lpBoundedMulCLM (p := 2) (μ := thetaPrimeSourceLaw) (measurable_recordSymbol n)
            zero_le_one (norm_recordSymbol_le n) ∘L
          coordinateRecovery thetaPrimeSourceLaw (gammaMeasure (9 / 2) Real.pi) :=
  (thetaPrime_projectiveRecovery.2.2.2) (measurable_recordSymbol n) zero_le_one
    (norm_recordSymbol_le n)

/-! ### Lift invariance of the prime-mixed formation data -/

section LiftInvariance

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
  [SFinite μ] [IsProbabilityMeasure ν]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The lift `T ↦ J T J*` of a source operator to the completion. -/
def liftedOperator (A : Lp K 2 μ →L[ℂ] Lp K 2 μ) : Lp K 2 (μ.prod ν) →L[ℂ] Lp K 2 (μ.prod ν) :=
  (coordinateLift μ ν).toContinuousLinearMap ∘L A ∘L coordinateRecovery μ ν

omit [SFinite μ] in
theorem adjoint_lift_comp_lift :
    ContinuousLinearMap.adjoint (coordinateLift (K := K) μ ν).toContinuousLinearMap ∘L
      (coordinateLift μ ν).toContinuousLinearMap = ContinuousLinearMap.id ℂ _ :=
  coordinateRecovery_comp_lift μ ν

omit [SFinite μ] in
/-- **Exact recovery of every operator**: `P (J A J*) J = A`. -/
theorem recover_liftedOperator (A : Lp K 2 μ →L[ℂ] Lp K 2 μ) :
    coordinateRecovery μ ν ∘L liftedOperator μ ν A ∘L
      (coordinateLift μ ν).toContinuousLinearMap = A := by
  have h := coordinateRecovery_comp_lift (K := K) μ ν
  rw [liftedOperator]
  calc coordinateRecovery μ ν ∘L ((coordinateLift μ ν).toContinuousLinearMap ∘L A ∘L
        coordinateRecovery μ ν) ∘L (coordinateLift μ ν).toContinuousLinearMap
      = (coordinateRecovery μ ν ∘L (coordinateLift μ ν).toContinuousLinearMap) ∘L A ∘L
          (coordinateRecovery μ ν ∘L (coordinateLift μ ν).toContinuousLinearMap) := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = A := by rw [h]; rfl

omit [SFinite μ] in
/-- **Matrix entries are unchanged**: `⟨J x, (J A J*) J y⟩ = ⟨x, A y⟩`. -/
theorem inner_liftedOperator (A : Lp K 2 μ →L[ℂ] Lp K 2 μ) (x y : Lp K 2 μ) :
    ⟪coordinateLift μ ν x, liftedOperator μ ν A (coordinateLift μ ν y)⟫_ℂ = ⟪x, A y⟫_ℂ := by
  rw [liftedOperator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, coordinateRecovery_lift,
    LinearIsometry.inner_map_map]

omit [SFinite μ] in
/-- **Positivity (orientation) is unchanged.** -/
theorem liftedOperator_isPositive {A : Lp K 2 μ →L[ℂ] Lp K 2 μ} (hA : A.IsPositive) :
    (liftedOperator μ ν A).IsPositive :=
  hA.conj_adjoint _

omit [SFinite μ] in
/-- **Approximation numbers are unchanged.** -/
theorem approxNumber_liftedOperator (A : Lp K 2 μ →L[ℂ] Lp K 2 μ) (n : ℕ) :
    _root_.RHTower.approxNumber (liftedOperator μ ν A) n = _root_.RHTower.approxNumber A n :=
  approxNumber_isometric_conj (adjoint_lift_comp_lift μ ν) A n

omit [SFinite μ] in
/-- **Traces are unchanged** on Hilbert–Schmidt products `A = B C`. -/
theorem opTrace_liftedOperator {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {B : F →L[ℂ] Lp K 2 μ} {C : Lp K 2 μ →L[ℂ] F}
    (hB : B.IsHilbertSchmidt) (hC : C.IsHilbertSchmidt) :
    (liftedOperator μ ν (B ∘L C)).opTrace = (B ∘L C).opTrace := by
  have h := coordinateRecovery_comp_lift (K := K) μ ν
  have hJB : ((coordinateLift μ ν).toContinuousLinearMap ∘L B).IsHilbertSchmidt := hB.comp_left _
  have hCP : (C ∘L coordinateRecovery μ ν).IsHilbertSchmidt := hC.comp_right _
  have heq : liftedOperator μ ν (B ∘L C) =
      ((coordinateLift μ ν).toContinuousLinearMap ∘L B) ∘L (C ∘L coordinateRecovery μ ν) := by
    simp only [liftedOperator, ContinuousLinearMap.comp_assoc]
  rw [heq, ContinuousLinearMap.opTrace_comp_comm hJB hCP,
    ContinuousLinearMap.opTrace_comp_comm hB hC]
  congr 1
  calc (C ∘L coordinateRecovery μ ν) ∘L (coordinateLift μ ν).toContinuousLinearMap ∘L B
      = C ∘L (coordinateRecovery μ ν ∘L (coordinateLift μ ν).toContinuousLinearMap) ∘L B := by
        simp only [ContinuousLinearMap.comp_assoc]
    _ = C ∘L B := by rw [h]; rfl

end LiftInvariance

/-! ### Source-side zero-horizon exactness -/

/-- The survival-square multiplier `M_U` on the source. -/
def survivalSquareMul : Lp ℂ 2 thetaPrimeSourceLaw →L[ℂ] Lp ℂ 2 thetaPrimeSourceLaw :=
  contractionMul thetaPrimeSourceLaw (measurable_unitClamp.comp measurable_snd)
    (fun p => abs_unitClamp_le_one p.2)

/-- **(BGPR.17).**  `M_{Uᴺ} → 0` strongly. -/
theorem tendsto_survivalSquareMul_pow (f : Lp ℂ 2 thetaPrimeSourceLaw) :
    Tendsto (fun N => (survivalSquareMul ^ N) f) atTop (𝓝 0) :=
  tendsto_contractionMul_pow_apply _ _ _ (ae_thetaPrimeSourceLaw.mono fun p hp => by
    rw [Function.comp_apply, unitClamp_of_mem ⟨by linarith [hp.2.1], hp.2.2⟩]
    exact abs_lt.mpr ⟨by linarith [hp.2.1], hp.2.2⟩) f

/-- **(BGPR.17).**  The persistent projection `M_{1_{U=1}}` vanishes: the beta law has no atom at
`1`. -/
theorem persistentProjection_eq_zero :
    contractionMul thetaPrimeSourceLaw
        ((measurable_one.indicator ((measurableSet_singleton (1 : ℝ)).preimage measurable_snd)) :
          Measurable ((Prod.snd ⁻¹' {(1 : ℝ)}).indicator (1 : ℝ × ℝ → ℝ)))
        (fun p => by
          by_cases h : p ∈ Prod.snd ⁻¹' {(1 : ℝ)}
          · simp [indicator_of_mem h]
          · simp [indicator_of_notMem h]) = 0 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [contractionMul_coeFn thetaPrimeSourceLaw _ _ f, Lp.coeFn_zero ℂ 2
    thetaPrimeSourceLaw, ae_thetaPrimeSourceLaw] with p h1 h2 h3
  rw [h1, zero_apply, h2, indicator_of_notMem (by
    simp only [mem_preimage, mem_singleton_iff]
    exact (ne_of_lt h3.2.2))]
  simp

/-- The beta law has no atom at `1`. -/
theorem betaMeasure_threeHalves_singleton_one : betaMeasure (3 / 2) 3 {1} = 0 := by
  rw [betaMeasure, withDensity_apply _ (measurableSet_singleton 1)]
  exact setLIntegral_measure_zero _ _ (measure_singleton 1)

end GaloisForLFunctions.HTGeometry
