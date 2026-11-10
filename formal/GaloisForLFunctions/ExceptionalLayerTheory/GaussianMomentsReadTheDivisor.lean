import GaloisForLFunctions.ExceptionalLayerTheory.PolynomialDampingReadsTheDivisor

/-!
# Gaussian moments retain the exceptional-divisor reading

Multiplication by `ε n²/t` is an exact shift of the prime abscissa.
Gamma recurrence multiplies each Mellin mode by `w/(2t)`, which tends
to `-i/2` at a fixed divisor point. The moment therefore suppresses small
prime products without suppressing the normalized divisor signal.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem rotatedGaussianKernel_eq_exp {y : ℝ} (hy : 0 < y) (φ : ℝ) (w : ℂ) :
    rotatedGaussianKernel y φ w = (1 / 2 : ℂ) * Complex.Gamma (w / 2) *
      Complex.exp (-((Real.log y : ℂ) + (φ : ℂ) * I) * w / 2) := by
  rw [rotatedGaussianKernel, gaussianMBKernel,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le]
  have he : -((Real.log y : ℂ) + (φ : ℂ) * I) * w / 2 =
      -(φ : ℂ) * I * w / 2 + (Real.log y : ℂ) * -(w / 2) := by ring
  rw [he, Complex.exp_add]
  ring

/-- The first Gaussian moment acts on a Mellin mode by multiplication by `w/2`. -/
theorem complexDamping_mul_rotatedGaussianKernel_add_two {y : ℝ} (hy : 0 < y)
    (φ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    complexGaussianDamping y φ * rotatedGaussianKernel y φ (w + 2) =
      (w / 2) * rotatedGaussianKernel y φ w := by
  rw [rotatedGaussianKernel_eq_exp hy, rotatedGaussianKernel_eq_exp hy,
    show (w + 2) / 2 = w / 2 + 1 by ring,
    Complex.Gamma_add_one _ (div_ne_zero hw (by norm_num))]
  have he : Complex.exp ((Real.log y : ℂ) + (φ : ℂ) * I) *
      Complex.exp (-((Real.log y : ℂ) + (φ : ℂ) * I) * (w + 2) / 2) =
      Complex.exp (-((Real.log y : ℂ) + (φ : ℂ) * I) * w / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  dsimp only [complexGaussianDamping]
  calc
    _ = (w / 2) * ((1 / 2 : ℂ) * Complex.Gamma (w / 2)) *
        (Complex.exp ((Real.log y : ℂ) + (φ : ℂ) * I) *
          Complex.exp (-((Real.log y : ℂ) + (φ : ℂ) * I) * (w + 2) / 2)) := by ring
    _ = _ := by rw [he]; ring

/-- A literal prime Gaussian sum with its first normalized damping moment. -/
def rotatedGaussianMomentPrimeSum (s : ℂ) (y φ t : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
    (complexGaussianDamping y φ / t * (n : ℂ) ^ 2) *
      Complex.exp (-(complexGaussianDamping y φ * (n : ℂ) ^ 2))

private theorem lseries_term_mul_square (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term f s n * (n : ℂ) ^ 2 = LSeries.term f (s - 2) n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_def]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_sub _ _ hnC, Complex.cpow_ofNat]
    field_simp

/-- Multiplying each prime term by `εn²/t` shifts the abscissa by two. -/
theorem rotatedGaussianMomentPrimeSum_eq (s : ℂ) (y φ t : ℝ) :
    rotatedGaussianMomentPrimeSum s y φ t =
      (complexGaussianDamping y φ / t) * rotatedGaussianPrimeSum (s - 2) y φ := by
  rw [rotatedGaussianMomentPrimeSum, rotatedGaussianPrimeSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← lseries_term_mul_square]
  ring

/-- A damping filter applied to literal first-moment prime samples. -/
def rotatedPrimeMomentFilter (P : Polynomial ℂ) (σ β a h φ t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
      rotatedGaussianMomentPrimeSum ((σ : ℂ) + t * I)
        (geometricGaussianDamping a h t j) φ t

private theorem dampingSampleWeight_mul_damping (β a h φ t : ℝ) (s : ℂ) (j : ℕ) :
    dampingSampleWeight β h s j *
        complexGaussianDamping (geometricGaussianDamping a h t j) φ =
      complexGaussianDamping (Real.exp (-a * t)) φ *
        dampingSampleWeight β h (s - 2) j := by
  unfold dampingSampleWeight complexGaussianDamping geometricGaussianDamping
  rw [Real.log_exp, Real.log_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Each sample's own damping is retained by the shifted-abscissa filter identity. -/
theorem rotatedPrimeMomentFilter_eq (P : Polynomial ℂ) (σ β a h φ t : ℝ) :
    rotatedPrimeMomentFilter P σ β a h φ t =
      (complexGaussianDamping (Real.exp (-a * t)) φ / t) *
        rotatedPrimeDampingFilter P (σ - 2) β a h φ t := by
  unfold rotatedPrimeMomentFilter rotatedPrimeDampingFilter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [rotatedGaussianMomentPrimeSum_eq]
  have hs : ((σ : ℂ) + t * I) - 2 = (((σ - 2 : ℝ) : ℂ) + t * I) := by push_cast; ring
  have hw := dampingSampleWeight_mul_damping β a h φ t ((σ : ℂ) + t * I) j
  rw [hs] at hw ⊢
  calc
    _ = P.coeff j * (dampingSampleWeight β h ((σ : ℂ) + t * I) j *
        complexGaussianDamping (geometricGaussianDamping a h t j) φ) / t *
          rotatedGaussianPrimeSum (((σ - 2 : ℝ) : ℂ) + t * I)
            (geometricGaussianDamping a h t j) φ := by ring
    _ = _ := by rw [hw]; ring

/-- The normalized moment multiplier preserves every fixed divisor mode. -/
theorem tendsto_gaussian_moment_multiplier (ρ : ℂ) (σ : ℝ) :
    Tendsto (fun t : ℝ => (ρ - ((σ : ℂ) + t * I)) / (2 * t))
      atTop (𝓝 (-I / 2)) := by
  have hi := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
  have hh := (hi.const_mul ((ρ - σ) / 2)).sub_const (I / 2)
  simp only [Complex.ofReal_zero, mul_zero, zero_sub] at hh
  rw [show -(I / 2) = -I / 2 by ring] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp [htC]
  ring

/-- Polynomial damping reads the selected divisor at every real observation
abscissa below it; the contour remains to the right of the remainder. -/
theorem exists_polynomial_divisor_reading_below_cutline
    (F : Finset XiZeroCopy) {θ σ β : ℝ} (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ρ : ℂ) (hρhalf : 1 / 2 < ρ.re) (hgap : θ < ρ.re) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ h : ℝ → ℝ,
      Tendsto h atTop (𝓝 0) → (∀ᶠ t : ℝ in atTop, 0 < h t) →
      Tendsto (fun t : ℝ =>
        rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (h t))
          σ β (polynomialDampingSpeed A t) (h t) (boundaryDampingAngle t) t /
          ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
              (ρ - ((σ : ℂ) + t * I)))) atTop
        (𝓝 (-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q)))) := by
  classical
  obtain ⟨c, hcI, hcF⟩ := (Set.Ioo_infinite (max_lt hρhalf (max_lt hρσ hgap))).exists_notMem_finset
    (F.image fun q => (xiZero q).re)
  have hc0 : 1 / 2 < c := (le_max_left _ _).trans_lt hcI.1
  have hσc : σ < c := ((le_max_left σ θ).trans (le_max_right _ _)).trans_lt hcI.1
  have hθc : θ < c := ((le_max_right σ θ).trans (le_max_right _ _)).trans_lt hcI.1
  have havoid : ∀ q ∈ F, c ≠ (xiZero q).re := by
    intro q hq he
    exact hcF (Finset.mem_image.mpr ⟨q, hq, he.symm⟩)
  obtain ⟨B, A₀, _, hA₀, hb⟩ := exists_polynomial_normalized_prime_error_bound
    F ρ σ β hc0.le (hcI.2.trans hρ1) hσc
    hθc hrest havoid hcI.2 hρ1 hρ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA h hlim hpos
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let m : ℂ := (analyticOrderAt zetaResidueUnit ρ).toNat
  let P : ℝ → ℂ := fun t => (divisorDampingFilter F ρ β (h t)).eval
    (Complex.exp ((h t : ℂ) * (ρ - β)))
  let K : ℝ → ℂ := fun t => rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
    (ρ - ((σ : ℂ) + t * I))
  let U : ℝ → ℂ := fun t => rotatedPrimeDampingFilter
    (divisorDampingFilter F ρ β (h t)) σ β (polynomialDampingSpeed A t)
      (h t) (boundaryDampingAngle t) t
  have hE : Tendsto (fun t : ℝ => (U t + m * (P t * K t)) /
      ((h t : ℂ) ^ d * K t)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hsmall := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul B
    simp only [mul_zero] at hsmall
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsmall
    filter_upwards [hpos, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (|ρ.im| + 2)] with t hh hh1 ht htρ
    simpa only [U, m, P, K, d, rotatedDivisorFilteredMellinWeight, div_eq_mul_inv] using
      hb A t (h t) hA ht htρ hh hh1.le
  have hP := tendsto_divisorDampingFilter_scaled_value_of_tendsto F ρ β hlim
    (hpos.mono fun _ ht => ht.ne')
  have hmain := hE.sub (hP.const_mul m)
  have hmain' : Tendsto (fun t : ℝ =>
      (U t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) - m * (P t / (h t : ℂ) ^ d))
      atTop (𝓝 (-m * ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
        (ρ - xiZero q)))) := by
    simpa only [m, P, d, zero_sub, neg_mul] using hmain
  apply hmain'.congr'
  filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with t hh ht
  have hk : K t ≠ 0 := rotatedGaussianKernel_ne_zero (Real.rpow_pos_of_pos ht _) _
    (by simpa using sub_pos.mpr hρσ)
  change (U t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) -
    m * (P t / (h t : ℂ) ^ d) = U t / ((h t : ℂ) ^ d * K t)
  field_simp [hk, pow_ne_zero d (Complex.ofReal_ne_zero.mpr hh.ne')]
  ring

/-- The literal first-moment filter retains the full divisor amplitude,
multiplied by the nonzero constant `-i/2`, on every contracting grid. -/
theorem exists_polynomial_gaussian_moment_divisor_threshold
    (F : Finset XiZeroCopy) {θ σ β : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ h : ℝ → ℝ,
      Tendsto h atTop (𝓝 0) → (∀ᶠ t : ℝ in atTop, 0 < h t) →
      Tendsto (fun t : ℝ =>
        rotatedPrimeMomentFilter (divisorDampingFilter F ρ β (h t))
          σ β (polynomialDampingSpeed A t) (h t) (boundaryDampingAngle t) t /
          ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
              (ρ - ((σ : ℂ) + t * I)))) atTop
        (𝓝 ((-I / 2) * (-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))))) := by
  classical
  obtain ⟨A₀, hA₀, hb⟩ := exists_polynomial_divisor_reading_below_cutline
    (σ := σ - 2) (β := β) F hrest ρ (hσ.trans hρσ) (hgap.trans hρσ)
      (by linarith only [hρσ]) hρ1 hρ
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA h hlim hpos
  have hh := (tendsto_gaussian_moment_multiplier ρ σ).mul (hb A hA h hlim hpos)
  apply hh.congr'
  filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with t ht_h ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hhC : (h t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_h.ne'
  have hw : ρ - ((σ : ℂ) + t * I) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.zero_re] at hre
    linarith only [hρσ, hre]
  have hshift : ρ - (((σ - 2 : ℝ) : ℂ) + t * I) =
      (ρ - ((σ : ℂ) + t * I)) + 2 := by push_cast; ring
  have hk := rotatedGaussianKernel_ne_zero (Real.rpow_pos_of_pos ht (-A))
    (boundaryDampingAngle t) (w := ρ - (((σ - 2 : ℝ) : ℂ) + t * I))
    (by simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero]; linarith only [hρσ])
  have hk0 := rotatedGaussianKernel_ne_zero (Real.rpow_pos_of_pos ht (-A))
    (boundaryDampingAngle t) (w := ρ - ((σ : ℂ) + t * I))
    (by simpa using sub_pos.mpr hρσ)
  have hr := complexDamping_mul_rotatedGaussianKernel_add_two
    (Real.rpow_pos_of_pos ht (-A)) (boundaryDampingAngle t) hw
  rw [← hshift] at hr
  rw [rotatedPrimeMomentFilter_eq, exp_neg_polynomialDampingSpeed_mul A ht]
  field_simp [hk, hk0, htC, hhC]
  linear_combination -2 *
    rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (h t))
      (σ - 2) β (polynomialDampingSpeed A t) (h t) (boundaryDampingAngle t) t * hr

/-- Either the abscissa law holds, or actual top divisors have nonzero
literal first-moment readings at all sufficiently large polynomial scales. -/
theorem asymptoticAbscissaLaw_or_polynomial_moment_divisor_readings :
    AsymptoticAbscissaLaw ∨
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β →
          let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
          let C : ℂ := (-I / 2) * (-((analyticOrderAt zetaResidueUnit (xiZero q)).toNat : ℂ) *
            ((xiZero q - 1) * ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
              (xiZero q - xiZero p)))
          C ≠ 0 ∧ ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
            ∀ h : ℝ → ℝ, Tendsto h atTop (𝓝 0) → (∀ᶠ t : ℝ in atTop, 0 < h t) →
              Tendsto (fun t : ℝ =>
                rotatedPrimeMomentFilter (divisorDampingFilter F (xiZero q) β (h t))
                  σ β (polynomialDampingSpeed A t) (h t) (boundaryDampingAngle t) t /
                    ((h t : ℂ) ^ d * rotatedGaussianKernel (t ^ (-A))
                      (boundaryDampingAngle t) (xiZero q - ((σ : ℂ) + t * I)))) atTop (𝓝 C) := by
  classical
  by_cases h : AsymptoticAbscissaLaw
  · exact Or.inl h
  right
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, htop, hmax, hrest, _⟩ :=
    not_asymptoticAbscissaLaw_has_escaping_layer_profile h
  have hσ : 1 / 2 < σ := by linarith only [hθ, hgap]
  have hall : ∀ q : XiZeroCopy, (xiZero q).re ≤ β := by
    intro q
    by_cases hq : q ∈ F
    · exact hmax q hq
    · exact (hrest q hq).trans (hgap.trans hσβ).le
  refine ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, ?_⟩
  intro q _ hqβ
  dsimp only
  have hρpos : 0 < (xiZero q).re := by rw [hqβ]; linarith only [hσ, hσβ]
  have hρ1 : (xiZero q).re < 1 := by rwa [hqβ]
  have hI : (-I / 2 : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)
  exact ⟨mul_ne_zero hI (divisorDampingFilter_limit_constant_ne_zero F (xiZero q) hρpos hρ1 (xi_xiZero q)),
    exists_polynomial_gaussian_moment_divisor_threshold F hσ hgap hrest (xiZero q)
      (by rwa [hqβ]) hρ1 (xi_xiZero q)⟩

#print axioms asymptoticAbscissaLaw_or_polynomial_moment_divisor_readings

/-- Every positive-radius boundary sample eventually lies in the sector
where the real damping is no greater than the quadratic frequency. -/
theorem eventually_boundaryDamping_moment_sector :
    ∀ᶠ t : ℝ in atTop, ∀ y : ℝ, 0 < y →
      0 < (complexGaussianDamping y (boundaryDampingAngle t)).re ∧
      0 < -(complexGaussianDamping y (boundaryDampingAngle t)).im ∧
      (complexGaussianDamping y (boundaryDampingAngle t)).re ≤
        -(complexGaussianDamping y (boundaryDampingAngle t)).im := by
  have hs : Tendsto (fun t : ℝ => Real.sin (1 / t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, Real.sin_zero] using
      (Real.continuous_sin.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hc : Tendsto (fun t : ℝ => Real.cos (1 / t)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, one_div, Real.cos_zero] using
      (Real.continuous_cos.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  filter_upwards [hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hc.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)] with t hsin hcos ht
  intro y hy
  have hφ : |boundaryDampingAngle t| < Real.pi / 2 := by
    rw [abs_boundaryDampingAngle ht]
    have hi : 0 < 1 / t := by positivity
    linarith only [hi]
  have him : -(complexGaussianDamping y (boundaryDampingAngle t)).im =
      y * Real.cos (1 / t) := by
    calc
      _ = -(y * Real.sin (boundaryDampingAngle t)) := by
        simp [complexGaussianDamping_eq hy, Complex.exp_im]
      _ = _ := by
        rw [show boundaryDampingAngle t = -(Real.pi / 2 - 1 / t) by
          dsimp only [boundaryDampingAngle]; ring,
          Real.sin_neg, Real.sin_pi_div_two_sub]
        ring
  refine ⟨complexGaussianDamping_re_pos hy hφ, ?_, ?_⟩
  · rw [him]
    exact mul_pos hy (by linarith only [hcos])
  · rw [complexGaussianDamping_boundary_re hy, him]
    exact mul_le_mul_of_nonneg_left (hsin.le.trans hcos.le) hy.le

#print axioms eventually_boundaryDamping_moment_sector

#print axioms exists_polynomial_divisor_reading_below_cutline
#print axioms exists_polynomial_gaussian_moment_divisor_threshold

#print axioms complexDamping_mul_rotatedGaussianKernel_add_two
#print axioms rotatedGaussianMomentPrimeSum_eq
#print axioms rotatedPrimeMomentFilter_eq
#print axioms tendsto_gaussian_moment_multiplier

end GaloisForLFunctions.ExceptionalLayerTheory
