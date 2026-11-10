import GaloisForLFunctions.ExceptionalLayerTheory.BoundaryDampingReadsTheDivisor
import GaloisForLFunctions.ExceptionalLayerTheory.VinogradovKorobovBoundsForBoundaryDamping

/-!
# Exceptional-divisor readings at polynomial damping scales

The speed `A log(t)/t` turns exponential damping into radius `t⁻ᴬ`.
Uniform contour and reciprocal-mode estimates give a normalized error of
order `1/t` once `A` exceeds a fixed threshold. All spacing factors cancel,
so the reading survives every positive contracting grid.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Exponential speed representing polynomial damping radius. -/
def polynomialDampingSpeed (A t : ℝ) : ℝ := A * Real.log t / t

lemma polynomialDampingSpeed_mul (A : ℝ) {t : ℝ} (ht : t ≠ 0) :
    polynomialDampingSpeed A t * t = A * Real.log t := by
  dsimp only [polynomialDampingSpeed]
  field_simp [ht]

/-- The varying speed gives exactly the stated polynomial radius. -/
theorem exp_neg_polynomialDampingSpeed_mul (A : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-polynomialDampingSpeed A t * t) = t ^ (-A) := by
  rw [neg_mul, polynomialDampingSpeed_mul A ht.ne', Real.rpow_def_of_pos ht]
  congr 1
  ring

/-- Positive Mellin real part excludes every Gamma pole, independently of
whether the mode grows along the observation path. -/
theorem rotatedGaussianKernel_ne_zero {y : ℝ} (hy : 0 < y) (φ : ℝ)
    {w : ℂ} (hw : 0 < w.re) : rotatedGaussianKernel y φ w ≠ 0 := by
  have hΓ : Complex.Gamma (w / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have he := congrArg Complex.re hn
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at he
    linarith only [hw, he, Nat.cast_nonneg (α := ℝ) n]
  rw [rotatedGaussianKernel, gaussianMBKernel,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero (mul_ne_zero (by norm_num) hΓ) (Complex.exp_ne_zero _))

/-- A sufficiently large polynomial radius exponent gives a uniform `1/t`
normalized contour error, retaining the entire complementary divisor. -/
theorem exists_polynomial_normalized_prime_error_bound
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ B A₀ : ℝ, 0 < B ∧ 0 < A₀ ∧ ∀ A t h : ℝ,
      A₀ ≤ A → 1 ≤ t → |ρ.im| + 2 ≤ t → 0 < h → h ≤ 1 →
      ‖(rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h)
          σ β (polynomialDampingSpeed A t) h (boundaryDampingAngle t) t +
          ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
            rotatedDivisorFilteredMellinWeight F ρ σ β h (t ^ (-A))
              (boundaryDampingAngle t) t ρ) /
        ((h : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
            (ρ - ((σ : ℂ) + t * I)))‖ ≤ B / t := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨C, N, hC, hb⟩ := exists_boundaryPrimeDampingFilter_spacing_preserving_error_bound
    F ρ σ β hc hc1 hσc hgap hrest havoid hρc hρ1 hρ
  obtain ⟨D, M, hD, hm⟩ := exists_boundaryGaussianMode_inverse_bound ρ σ
  let A₀ := 2 * (((N + M : ℕ) : ℝ) + 1) / (ρ.re - c)
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  refine ⟨C * D + 1, A₀, by positivity, hA₀, ?_⟩
  intro A t h hA ht htρ hh hh1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hr : ((N + M : ℕ) : ℝ) + 1 ≤ A * (ρ.re - c) / 2 := by
    have hhA := (div_le_iff₀ (sub_pos.mpr hρc)).mp hA
    nlinarith only [hhA]
  let a := polynomialDampingSpeed A t
  let E := rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h)
      σ β a h (boundaryDampingAngle t) t +
    ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      rotatedDivisorFilteredMellinWeight F ρ σ β h (t ^ (-A)) (boundaryDampingAngle t) t ρ
  let K := rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
    (ρ - ((σ : ℂ) + t * I))
  have hE : ‖E‖ ≤ C * h ^ d * t ^ N * Real.exp (a * t * (c - σ) / 2) := by
    have hh' := hb a h t ht hh.le hh1
    rw [exp_neg_polynomialDampingSpeed_mul A ht0] at hh'
    exact hh'
  have hdiv : ‖E‖ / h ^ d ≤ C * t ^ N * Real.exp (a * t * (c - σ) / 2) := by
    apply (div_le_iff₀ (pow_pos hh d)).mpr
    exact hE.trans_eq (by ring)
  have hK : ‖K⁻¹‖ ≤ D * t ^ M * Real.exp (-(a * (ρ.re - σ) / 2 * t)) := by
    have hh' := hm t htρ ht a
    rw [exp_neg_polynomialDampingSpeed_mul A ht0] at hh'
    exact hh'
  have hpoly : t ^ (N + M) * Real.exp (-(A * (ρ.re - c) / 2 * Real.log t)) ≤ t⁻¹ := by
    calc
      _ = Real.exp ((((N + M : ℕ) : ℝ) - A * (ρ.re - c) / 2) * Real.log t) := by
        rw [sub_mul, Real.exp_sub, Real.exp_nat_mul, Real.exp_log ht0, Real.exp_neg]
        rfl
      _ ≤ Real.exp (-Real.log t) := Real.exp_le_exp.mpr (by
        have hh' := mul_le_mul_of_nonneg_right hr hlog
        nlinarith only [hh'])
      _ = t⁻¹ := by rw [Real.exp_neg, Real.exp_log ht0]
  change ‖E / ((h : ℂ) ^ d * K)‖ ≤ _
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh, div_mul_eq_div_div, div_eq_mul_inv, ← norm_inv]
  calc
    _ ≤ (C * t ^ N * Real.exp (a * t * (c - σ) / 2)) *
        (D * t ^ M * Real.exp (-(a * (ρ.re - σ) / 2 * t))) :=
      mul_le_mul hdiv hK (norm_nonneg _) (by positivity)
    _ = C * D * (t ^ (N + M) * Real.exp (-(A * (ρ.re - c) / 2 * Real.log t))) := by
      have he : -(A * (ρ.re - c) / 2 * Real.log t) =
          a * t * (c - σ) / 2 + -(a * (ρ.re - σ) / 2 * t) := by
        dsimp only [a, polynomialDampingSpeed]
        field_simp [ht0.ne']
        ring
      rw [he, Real.exp_add, pow_add]
      ring
    _ ≤ C * D * t⁻¹ := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hC.le hD)
    _ ≤ (C * D + 1) / t := by rw [div_eq_mul_inv]; gcongr; linarith only


/-- Every sufficiently large polynomial radius exponent recovers the
selected divisor for every positive spacing tending to zero. -/
theorem exists_polynomial_prime_filter_divisor_threshold
    (F : Finset XiZeroCopy) {θ σ β : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
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
  obtain ⟨c, hcI, hcF⟩ := (Set.Ioo_infinite hρσ).exists_notMem_finset
    (F.image fun q => (xiZero q).re)
  have havoid : ∀ q ∈ F, c ≠ (xiZero q).re := by
    intro q hq he
    exact hcF (Finset.mem_image.mpr ⟨q, hq, he.symm⟩)
  obtain ⟨B, A₀, _, hA₀, hb⟩ := exists_polynomial_normalized_prime_error_bound
    F ρ σ β (hσ.trans hcI.1).le (hcI.2.trans hρ1) hcI.1
    (hgap.trans hcI.1) hrest havoid hcI.2 hρ1 hρ
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

/-- Either the abscissa law holds, or actual top zeros are read by literal
prime filters at polynomial damping radii, on every contracting grid. -/
theorem asymptoticAbscissaLaw_or_polynomial_divisor_readings :
    AsymptoticAbscissaLaw ∨
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β →
          let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
          let C : ℂ := -((analyticOrderAt zetaResidueUnit (xiZero q)).toNat : ℂ) *
            ((xiZero q - 1) * ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
              (xiZero q - xiZero p))
          C ≠ 0 ∧ ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
            ∀ h : ℝ → ℝ, Tendsto h atTop (𝓝 0) → (∀ᶠ t : ℝ in atTop, 0 < h t) →
              Tendsto (fun t : ℝ =>
                rotatedPrimeDampingFilter (divisorDampingFilter F (xiZero q) β (h t))
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
  exact ⟨divisorDampingFilter_limit_constant_ne_zero F (xiZero q) hρpos hρ1 (xi_xiZero q),
    exists_polynomial_prime_filter_divisor_threshold F hσ hgap hrest (xiZero q)
      (by rwa [hqβ]) hρ1 (xi_xiZero q)⟩

/-- The boundary angle turns the real damping into `y sin(1/t)`. -/
theorem complexGaussianDamping_boundary_re {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (complexGaussianDamping y (boundaryDampingAngle t)).re = y * Real.sin (1 / t) := by
  calc
    _ = y * Real.cos (boundaryDampingAngle t) := by
      rw [complexGaussianDamping_eq hy]
      simp [Complex.exp_re]
    _ = _ := by
      rw [show boundaryDampingAngle t = -(Real.pi / 2 - 1 / t) by
        dsimp only [boundaryDampingAngle]; ring, Real.cos_neg, Real.cos_pi_div_two_sub]

/-- Polynomial radius has real damping of exact order `t^(-A-1)`. -/
theorem tendsto_polynomial_boundary_real_damping (A : ℝ) :
    Tendsto (fun t : ℝ => t ^ (A + 1) *
      (complexGaussianDamping (t ^ (-A)) (boundaryDampingAngle t)).re) atTop (𝓝 1) := by
  have hs : Tendsto (fun t : ℝ => Real.sinc (t⁻¹)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_sinc.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.sinc_of_ne_zero (inv_ne_zero ht.ne'),
    complexGaussianDamping_boundary_re (Real.rpow_pos_of_pos ht _), ← mul_assoc,
    ← Real.rpow_add ht, show A + 1 + -A = 1 by ring, Real.rpow_one]
  simp only [one_div, div_inv_eq_mul, mul_comm]

/-- Every geometric sample has a polynomial radius with its exact grid factor. -/
theorem geometricGaussianDamping_polynomial (A h : ℝ) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    geometricGaussianDamping (polynomialDampingSpeed A t) h t j =
      t ^ (-A) * Real.exp (-(2 * (j : ℝ) * h)) := by
  rw [geometricGaussianDamping, sub_eq_add_neg, Real.exp_add,
    exp_neg_polynomialDampingSpeed_mul A ht]

/-- Every fixed sample of a contracting grid has the same polynomial real
Gaussian scale; the grid does not reintroduce exponential prime length. -/
theorem tendsto_polynomial_geometric_real_damping (A : ℝ) (j : ℕ)
    {h : ℝ → ℝ} (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t ^ (A + 1) *
      (complexGaussianDamping
        (geometricGaussianDamping (polynomialDampingSpeed A t) (h t) t j)
        (boundaryDampingAngle t)).re) atTop (𝓝 1) := by
  have hf : Tendsto (fun t : ℝ => Real.exp (-(2 * (j : ℝ) * h t))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_exp.tendsto (-(2 * (j : ℝ) * 0))).comp
        ((hlim.const_mul (2 * (j : ℝ))).neg)
  have hm := (tendsto_polynomial_boundary_real_damping A).mul hf
  simp only [mul_one] at hm
  apply hm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [geometricGaussianDamping_polynomial A (h t) ht j,
    complexGaussianDamping_boundary_re (Real.rpow_pos_of_pos ht _),
    complexGaussianDamping_boundary_re (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _))]
  ring


/-- At polynomial radius, every real argument has a uniform Gaussian
majorant at scale `t^((A+1)/2)`, for each fixed contracting-grid sample. -/
theorem eventually_polynomial_geometric_gaussian_envelope (A : ℝ) (j : ℕ)
    {h : ℝ → ℝ} (hlim : Tendsto h atTop (𝓝 0)) :
    ∀ᶠ t : ℝ in atTop, ∀ x : ℝ,
      ‖Complex.exp (-complexGaussianDamping
        (geometricGaussianDamping (polynomialDampingSpeed A t) (h t) t j)
        (boundaryDampingAngle t) * (x : ℂ) ^ 2)‖ ≤
        Real.exp (-(x ^ 2 / (2 * t ^ (A + 1)))) := by
  have hh := (tendsto_polynomial_geometric_real_damping A j hlim).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro x
  let ε := complexGaussianDamping
    (geometricGaussianDamping (polynomialDampingSpeed A t) (h t) t j) (boundaryDampingAngle t)
  have hp : 0 < t ^ (A + 1) := Real.rpow_pos_of_pos ht0 _
  have hre : (1 / 2 : ℝ) / t ^ (A + 1) ≤ ε.re :=
    (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using ht.le)
  have hx := mul_le_mul_of_nonneg_right hre (sq_nonneg x)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : (-ε * (x : ℂ) ^ 2).re = -(ε.re * x ^ 2) := by
    simp [pow_two]
  change (-ε * (x : ℂ) ^ 2).re ≤ _
  rw [he]
  calc
    _ ≤ -(((1 / 2 : ℝ) / t ^ (A + 1)) * x ^ 2) := neg_le_neg hx
    _ = _ := by ring

/-- Polynomial contraction of any fixed degree is overcome by a sufficiently
large polynomial damping radius exponent. -/
theorem exists_polynomial_contracted_mode_growth_threshold (d : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) (ρ : ℂ) (σ : ℝ) (hρσ : σ < ρ.re) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      Tendsto (fun t : ℝ => ‖((t ^ (-κ) : ℝ) : ℂ) ^ d *
        rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
          (ρ - ((σ : ℂ) + t * I))‖) atTop atTop := by
  obtain ⟨D, M, hD, hb⟩ := exists_boundaryGaussianMode_inverse_bound ρ σ
  let A₀ := 2 * ((M : ℝ) + (d : ℝ) * κ + 1) / (ρ.re - σ)
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  refine ⟨A₀, hA₀, ?_⟩
  intro A hA
  have hr : (M : ℝ) + (d : ℝ) * κ + 1 ≤ A * (ρ.re - σ) / 2 := by
    have hh := (div_le_iff₀ (sub_pos.mpr hρσ)).mp hA
    linarith only [hh]
  let K : ℝ → ℂ := fun t => rotatedGaussianKernel (t ^ (-A)) (boundaryDampingAngle t)
    (ρ - ((σ : ℂ) + t * I))
  let g : ℝ → ℂ := fun t => ((t ^ (-κ) : ℝ) : ℂ) ^ d * K t
  have hi : Tendsto (fun t : ℝ => ‖(g t)⁻¹‖) atTop (𝓝 0) := by
    have hl := (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_log_atTop).const_mul D
    simp only [mul_zero] at hl
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hl
    filter_upwards [eventually_ge_atTop (|ρ.im| + 2), eventually_ge_atTop (1 : ℝ)]
      with t htρ ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    have hK := hb t htρ ht (polynomialDampingSpeed A t)
    rw [exp_neg_polynomialDampingSpeed_mul A ht0] at hK
    dsimp only [g]
    rw [mul_inv, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), Real.rpow_def_of_pos ht0,
      ← Real.exp_nat_mul, ← Real.exp_neg]
    calc
      _ ≤ Real.exp (-((d : ℝ) * (Real.log t * -κ))) *
          (D * t ^ M * Real.exp (-(polynomialDampingSpeed A t * (ρ.re - σ) / 2 * t))) :=
        mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
      _ = D * Real.exp (((M : ℝ) + (d : ℝ) * κ - A * (ρ.re - σ) / 2) * Real.log t) := by
        have htM : t ^ M = Real.exp ((M : ℝ) * Real.log t) := by
          rw [Real.exp_nat_mul, Real.exp_log ht0]
        rw [htM]
        rw [show D * Real.exp (((M : ℝ) + (d : ℝ) * κ - A * (ρ.re - σ) / 2) * Real.log t) =
          D * (Real.exp (-((d : ℝ) * (Real.log t * -κ))) *
            Real.exp ((M : ℝ) * Real.log t) *
            Real.exp (-(polynomialDampingSpeed A t * (ρ.re - σ) / 2 * t))) by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          dsimp only [polynomialDampingSpeed]
          field_simp [ht0.ne']
          ring]
        ring
      _ ≤ D * Real.exp (-Real.log t) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hr hlog
        nlinarith only [hh]
  have hp : ∀ᶠ t : ℝ in atTop, 0 < ‖(g t)⁻¹‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply norm_pos_iff.mpr
    apply inv_ne_zero
    exact mul_ne_zero (pow_ne_zero d (Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos ht _).ne'))
      (rotatedGaussianKernel_ne_zero (Real.rpow_pos_of_pos ht _) _
        (by simpa using sub_pos.mpr hρσ))
  have hright := tendsto_nhdsWithin_iff.mpr ⟨hi, hp⟩
  simpa only [Function.comp_def, norm_inv, inv_inv, g, K] using
    tendsto_inv_nhdsGT_zero.comp hright

/-- Literal prime filters grow with polynomially contracting spacing once
the polynomial radius exponent is sufficiently large. -/
theorem exists_polynomial_prime_growth_threshold
    (F : Finset XiZeroCopy) {θ σ β κ : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (hκ : 0 < κ) (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
        (divisorDampingFilter F ρ β (t ^ (-κ)))
          σ β (polynomialDampingSpeed A t) (t ^ (-κ)) (boundaryDampingAngle t) t‖)
        atTop atTop := by
  obtain ⟨A₁, hA₁, hread⟩ := exists_polynomial_prime_filter_divisor_threshold
    F hσ hgap hrest ρ hρσ hρ1 hρ
  obtain ⟨A₂, _, hmode⟩ := exists_polynomial_contracted_mode_growth_threshold
    (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) hκ.le ρ σ hρσ
  refine ⟨max A₁ A₂, hA₁.trans_le (le_max_left _ _), ?_⟩
  intro A hA
  have hlim : Tendsto (fun t : ℝ => t ^ (-κ)) atTop (𝓝 0) :=
    _root_.tendsto_rpow_neg_atTop hκ
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < t ^ (-κ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact Real.rpow_pos_of_pos ht _
  exact norm_tendsto_atTop_of_ratio
    (divisorDampingFilter_limit_constant_ne_zero F ρ
      (by linarith only [hσ, hρσ]) hρ1 hρ)
    (hread A ((le_max_left _ _).trans hA) _ hlim hpos)
    (hmode A ((le_max_right _ _).trans hA))

/-- Failure of the abscissa law forces growing literal prime filters with
both polynomial damping radii and polynomially contracting spacing. -/
theorem asymptoticAbscissaLaw_or_polynomial_prime_growth :
    AsymptoticAbscissaLaw ∨
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β → ∀ κ : ℝ, 0 < κ →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
            Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
              (divisorDampingFilter F (xiZero q) β (t ^ (-κ)))
                σ β (polynomialDampingSpeed A t) (t ^ (-κ)) (boundaryDampingAngle t) t‖)
              atTop atTop := by
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
  intro q _ hqβ κ hκ
  exact exists_polynomial_prime_growth_threshold F hσ hgap hrest hκ (xiZero q)
    (by rwa [hqβ]) (by rwa [hqβ]) (xi_xiZero q)

/-- The independent arithmetic estimate applies to the same varying-speed
observable, with constants independent of the polynomial radius exponent. -/
theorem exists_polynomialPrimeDampingFilter_vinogradovKorobov_bound
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β : ℝ) (hσ : σ < 1) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ A : ℝ, 0 < A →
      ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
        ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h)
          σ β (polynomialDampingSpeed A t) h (boundaryDampingAngle t) t‖ ≤
          C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
            t ^ (A * (1 - σ) / 2) *
              Real.exp (-(A * Real.log t * vkHadamardWidth (t ^ 3 + 1) / 4)) := by
  obtain ⟨C, N, hC, hb⟩ :=
    exists_boundaryPrimeDampingFilter_uniform_vinogradovKorobov_bound F ρ σ β hσ
  refine ⟨C, N, hC, ?_⟩
  intro A hA
  filter_upwards [hb, eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (4 * A)]
    with t ht ht2 htA
  have ht0 : 0 < t := by linarith only [ht2]
  have ha : 0 < polynomialDampingSpeed A t :=
    div_pos (mul_pos hA (Real.log_pos (by linarith only [ht2]))) ht0
  have hscale : 4 * polynomialDampingSpeed A t ≤ t := by
    rw [polynomialDampingSpeed, ← mul_div_assoc]
    apply (div_le_iff₀ ht0).mpr
    calc
      _ = (4 * A) * Real.log t := by ring
      _ ≤ (4 * A) * t := mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) (by positivity)
      _ ≤ t * t := mul_le_mul_of_nonneg_right htA ht0.le
  intro h hh hh1
  have hbound := ht _ ha hscale h hh hh1
  have he : Real.exp (polynomialDampingSpeed A t * (1 - σ) * t / 2 -
      polynomialDampingSpeed A t * t * vkHadamardWidth (t ^ 3 + 1) / 4) =
      t ^ (A * (1 - σ) / 2) *
        Real.exp (-(A * Real.log t * vkHadamardWidth (t ^ 3 + 1) / 4)) := by
    rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]
    congr 1
    dsimp only [polynomialDampingSpeed]
    field_simp [ht0.ne']
    ring
  rw [he] at hbound
  exact hbound.trans_eq (by ring)

#print axioms rotatedGaussianKernel_ne_zero
#print axioms exists_polynomial_normalized_prime_error_bound
#print axioms exists_polynomial_prime_filter_divisor_threshold
#print axioms asymptoticAbscissaLaw_or_polynomial_divisor_readings
#print axioms tendsto_polynomial_geometric_real_damping
#print axioms eventually_polynomial_geometric_gaussian_envelope
#print axioms exists_polynomial_contracted_mode_growth_threshold
#print axioms exists_polynomial_prime_growth_threshold
#print axioms asymptoticAbscissaLaw_or_polynomial_prime_growth
#print axioms exists_polynomialPrimeDampingFilter_vinogradovKorobov_bound

end GaloisForLFunctions.ExceptionalLayerTheory
