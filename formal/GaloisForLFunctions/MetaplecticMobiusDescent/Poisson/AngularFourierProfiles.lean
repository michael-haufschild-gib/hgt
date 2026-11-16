import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.PositiveAngularCancellation

/-! # Angular trace-Fourier profiles

Rotation covariance separates the angular character from its radial Fourier profile.
Positive scaling and Eisenstein lattice Poisson summation retain the modulus phase;
Schwartz continuity controls the profile by finitely many physical seminorms.
-/

noncomputable section
open Complex MeasureTheory
open scoped Classical SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- Radial profile of the trace Fourier transform in angular weight `k`. -/
def paperAngularFourier (k : ℕ) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  paperFourier (angularRadial k W) (Real.sqrt t : ℂ)

private theorem fourier_const_mul (c : ℂ) (f : ℂ → ℂ) (u : ℂ) :
    paperFourier (fun z => c * f z) u = c * paperFourier f u := by
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_left_comm (paperE _ ) c]
  rw [integral_const_mul]
  ring

/-- Trace Fourier transform reverses the angular character. -/
theorem paperFourier_angular (k : ℕ) (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (angularRadial k W) u =
      (conj u / (‖u‖ : ℂ)) ^ k * paperAngularFourier k W (‖u‖ ^ 2) := by
  unfold paperAngularFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · subst u
    cases k with
    | zero => simp only [pow_zero, one_mul, norm_zero, Complex.ofReal_zero]
    | succ n => simp only [angular_positive_zero_mode, norm_zero, Complex.ofReal_zero,
        mul_zero]
  have hn : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  let a : ℂ := u / (‖u‖ : ℂ)
  let b : ℂ := conj u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hn
  have hna : ‖a‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hu)]
  have hq : u / a = (‖u‖ : ℂ) := by dsimp [a]; field_simp
  have hfun : (fun z => angularRadial k W (a * z)) =
      fun z => a ^ k * angularRadial k W z := by
    funext z
    simp only [angularRadial, norm_mul, hna, one_mul, mul_div_assoc, mul_pow, mul_assoc]
  have hF := paperFourier_comp_mul (angularRadial k W) a ha u
  rw [hfun, fourier_const_mul, hna, hq] at hF
  simp only [one_pow, div_one, one_smul] at hF
  have hba : b * a = 1 := by
    dsimp [a, b]
    rw [div_mul_div_comm, Complex.conj_mul', pow_two, div_self (mul_ne_zero hn hn)]
  calc
    _ = (b * a) ^ k * paperFourier (angularRadial k W) u := by rw [hba, one_pow, one_mul]
    _ = b ^ k * paperFourier (angularRadial k W) (‖u‖ : ℂ) := by
      rw [mul_pow, mul_assoc, hF]

theorem angularRadial_real_scale (k : ℕ) (W : ℝ → ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    angularRadial k W ((r : ℂ) * z) =
      angularRadial k (fun t => W (r ^ 2 * t)) z := by
  simp only [angularRadial, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    Complex.ofReal_mul, mul_pow,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]

private theorem conj_direction_real_scale (r : ℝ) (hr : 0 < r) (z : ℂ) :
    conj ((r : ℂ) * z) / (‖(r : ℂ) * z‖ : ℂ) = conj z / (‖z‖ : ℂ) := by
  simp only [map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr.le, Complex.ofReal_mul,
    mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]

/-- Positive dilation preserves angular weight and rescales the radial dual variable. -/
theorem paperFourier_angular_scaled (k : ℕ) (W : ℝ → ℂ)
    (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (angularRadial k (fun t => W (t / K))) u =
      K • ((conj u / (‖u‖ : ℂ)) ^ k * paperAngularFourier k W (K * ‖u‖ ^ 2)) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z => angularRadial k W (a * z)) =
      angularRadial k (fun t => W (t / K)) := by
    funext z
    change angularRadial k W ((Real.sqrt K : ℂ)⁻¹ * z) = _
    rw [← Complex.ofReal_inv, angularRadial_real_scale k W _ (inv_pos.mpr (Real.sqrt_pos.mpr hK))]
    congr 1
    funext t
    rw [inv_pow, Real.sq_sqrt hK.le]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hdir : conj (u / a) / (‖u / a‖ : ℂ) = conj u / (‖u‖ : ℂ) := by
    dsimp [a]
    rw [div_inv_eq_mul, mul_comm u]
    exact conj_direction_real_scale _ (Real.sqrt_pos.mpr hK) u
  have hF := paperFourier_comp_mul (angularRadial k W) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_angular k W (u / a), hnorm, hdir] at hF
  exact hF

/-- On the defining annulus the smooth localization equals the original angular kernel. -/
theorem annularAngularCLM_eq (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    (annularAngularCLM k W : ℂ → ℂ) = angularRadial k W := by
  funext z
  rw [annularAngularCLM_apply]
  unfold angularRadial
  dsimp only
  by_cases hz : W (‖z‖ ^ 2) = 0
  · rw [hz, mul_zero]
  · rw [annularBump_one ⟨‖z‖ ^ 2, hW hz⟩, Complex.ofReal_one, one_mul]

private theorem conj_direction_div (u c : ℂ) (hc : c ≠ 0) :
    conj (u / c) / (‖u / c‖ : ℂ) =
      (c / (‖c‖ : ℂ)) * (conj u / (‖u‖ : ℂ)) := by
  have hnc : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
  have hcc : conj c ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hc
  have he : c / (‖c‖ : ℂ) = (‖c‖ : ℂ) / conj c := by
    apply (div_eq_div_iff hnc hcc).mpr
    rw [Complex.mul_conj', pow_two]
  rw [map_div₀, norm_div, Complex.ofReal_div, he, div_div_div_comm]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- A modulus rotates the dual angular profile by its own positive angular character. -/
theorem paperFourier_angular_quotient (k : ℕ) (W : ℝ → ℂ)
    (u c : ℂ) (hc : c ≠ 0) :
    paperFourier (angularRadial k W) (u / c) =
      (c / (‖c‖ : ℂ)) ^ k * (conj u / (‖u‖ : ℂ)) ^ k *
        paperAngularFourier k W (‖u‖ ^ 2 / ‖c‖ ^ 2) := by
  rw [paperFourier_angular, conj_direction_div u c hc, norm_div, div_pow, mul_pow, mul_assoc]

/-- Supported angular kernels remain Schwartz after positive dilation. -/
def scaledAnnularAngularTest (k : ℕ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) : 𝓢(ℂ, ℂ) :=
  affinePullback (annularAngularCLM k W)
    (complexMulEquiv ((Real.sqrt K : ℂ)⁻¹) (inverseSqrt_ne_zero K hK)) 0

theorem scaledAnnularAngularTest_apply (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledAnnularAngularTest k W K hK z = angularRadial k (fun t => W (t / K)) z := by
  simp only [scaledAnnularAngularTest, affinePullback_apply, complexMulEquiv_apply, add_zero]
  rw [congrFun (annularAngularCLM_eq k W hW), ← Complex.ofReal_inv,
    angularRadial_real_scale k W _ (inv_pos.mpr (Real.sqrt_pos.mpr hK))]
  congr 1
  funext t
  rw [inv_pow, Real.sq_sqrt hK.le]
  congr 1
  ring

/-- Angular Poisson reflection retains the primitive finite trace coefficient and the
modulus phase. No periodic approximation to the angular character is used. -/
theorem actual_angular_poisson_trace (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (K : ℝ) (hK : 0 < K) (c : Eisenstein.O) (hc : c ≠ 0)
    (P : Eisenstein.O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (Eisenstein.O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (Eisenstein.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : Eisenstein.O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
      angularRadial k (fun t => W (t / K)) (Eisenstein.ringComplex z)) =
    (K / ‖Eisenstein.ringComplex c‖ ^ 2 : ℝ) • ∑' h : Eisenstein.O,
      (∑ r : Eisenstein.O ⧸ Ideal.span {c}, P r *
        residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
        ((Eisenstein.ringComplex c / (‖Eisenstein.ringComplex c‖ : ℂ)) ^ k *
          (conj (Eisenstein.ringComplex h) / (‖Eisenstein.ringComplex h‖ : ℂ)) ^ k *
          paperAngularFourier k W
            (K * ‖Eisenstein.ringComplex h‖ ^ 2 / ‖Eisenstein.ringComplex c‖ ^ 2)) := by
  letI : Finite (Eisenstein.O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (Eisenstein.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hf : (scaledAnnularAngularTest k W K hK : ℂ → ℂ) =
      angularRadial k (fun t => W (t / K)) :=
    funext (scaledAnnularAngularTest_apply k W hW K hK)
  have ht := actual_eisenstein_paper_poisson (scaledAnnularAngularTest k W K hK) c hc P
  change (∑' z : Eisenstein.O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
      (scaledAnnularAngularTest k W K hK : ℂ → ℂ) (Eisenstein.ringComplex z)) = _ at ht
  rw [hf] at ht
  simp_rw [paperFourier_angular_scaled k W K hK] at ht
  simp_rw [conj_direction_div _ _ (ringComplex_ne_zero hc)] at ht
  simp only [norm_div, div_pow, mul_pow, mul_div_assoc] at ht
  have hphase (h : Eisenstein.O) (x : Eisenstein.O ⧸ Ideal.span {c}) :
      Eisenstein.ringComplex (GaussianShiftedPartition.representative c x) *
        (Eisenstein.ringComplex h / Eisenstein.ringComplex c) =
      (Eisenstein.ringComplex h / Eisenstein.ringComplex c) *
        Eisenstein.ringComplex (GaussianShiftedPartition.representative c x) := mul_comm _ _
  simp_rw [hphase] at ht
  simp only [residueTraceQuotientChar_frequency]
  rw [ht]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem paperAngularFourier_eq_plane (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (t : ℝ) :
    paperAngularFourier k W t = (2 / Real.sqrt 3 : ℝ) •
      annularFourierCLM k W (paperFrequency (Real.sqrt t : ℂ)) := by
  rw [paperAngularFourier, paperFourier_eq_standard]
  change _ = (2 / Real.sqrt 3 : ℝ) •
    (𝓕 (annularAngularCLM k W)) (paperFrequency (Real.sqrt t : ℂ))
  rw [SchwartzMap.fourier_coe, annularAngularCLM_eq k W hW]

/-- The dual radial profile has rapid decay, controlled by the Schwartz seminorms of its
angular Fourier transform. -/
theorem paperAngularFourier_weighted_bound (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (A : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ A * ‖paperAngularFourier k W t‖ ≤
      (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
        (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ)
          (annularFourierCLM k W) := by
  let ξ : ℂ := paperFrequency (Real.sqrt t : ℂ)
  have hn : ‖ξ‖ ^ 2 = (4 / 3 : ℝ) * t := paperFrequency_sqrt_norm_sq t ht
  have hscale : 0 ≤ (2 / Real.sqrt 3 : ℝ) := by positivity
  have hpow : (1 + t) ^ A ≤ (1 + ‖ξ‖) ^ (2 * A) := by
    have hbase : 1 + t ≤ (1 + ‖ξ‖) ^ 2 := by
      nlinarith only [hn, norm_nonneg ξ, ht]
    calc
      (1 + t) ^ A ≤ ((1 + ‖ξ‖) ^ 2) ^ A := pow_le_pow_left₀ (by positivity) hbase A
      _ = _ := by rw [← pow_mul]
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2 * A, 0)) (k := 2 * A) (n := 0) le_rfl le_rfl (annularFourierCLM k W) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  have hsf : (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) =
      schwartzSeminormFamily ℝ ℂ ℂ := by
    funext m
    rcases m with ⟨a, b⟩
    rfl
  rw [hsf] at hb
  rw [paperAngularFourier_eq_plane k W hW, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hscale]
  change (1 + t) ^ A * ((2 / Real.sqrt 3) * ‖annularFourierCLM k W ξ‖) ≤ _
  calc
    _ = (2 / Real.sqrt 3) * ((1 + t) ^ A * ‖annularFourierCLM k W ξ‖) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((1 + ‖ξ‖) ^ (2 * A) * ‖annularFourierCLM k W ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hscale
    _ ≤ _ := by
      simpa only [mul_assoc, add_zero] using mul_le_mul_of_nonneg_left hb hscale

/-- At each fixed angular weight, finitely many physical seminorms control every radial
decay order. The angular twist changes the constant, not the scale exponent. -/
theorem paperAngularFourier_finite_seminorm_bound (k A : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 → ∀ (t : ℝ), 0 ≤ t →
      (1 + t) ^ A * ‖paperAngularFourier k W t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S, C, hC, hb⟩ := schwartzCLM_finite_seminorm_control (annularFourierCLM k)
    (Finset.Iic (2 * A, 0))
  refine ⟨S, ((2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A)) * C, by positivity, ?_⟩
  intro W hW t ht
  calc
    _ ≤ ((2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A)) *
        ((Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ) (annularFourierCLM k W)) :=
      paperAngularFourier_weighted_bound k W hW A t ht
    _ ≤ ((2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A)) *
        (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W) (by positivity)
    _ = _ := by ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
