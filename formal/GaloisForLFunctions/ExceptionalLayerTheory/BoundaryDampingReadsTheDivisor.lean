import GaloisForLFunctions.ExceptionalLayerTheory.RotatedContoursForFiniteDivisorFilters
import GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDampingContractionReadsTheDivisor

/-!
# Exceptional-divisor recovery at every positive damping speed

Damping approaches the imaginary axis at reciprocal height. The selected
mode loses no fixed Gamma exponent, and the complete regular-line remainder
has a strictly smaller horizontal rate. Every positive contracting grid
therefore recovers the exceptional divisor at every positive damping speed.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The reciprocal boundary mode has the pure horizontal exponential rate,
uniformly over exponential damping speeds. -/
theorem exists_boundaryGaussianMode_inverse_bound (ρ : ℂ) (σ : ℝ) :
    ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ t : ℝ, |ρ.im| + 2 ≤ t → 1 ≤ t → ∀ a : ℝ,
      ‖(rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
        (ρ - ((σ : ℂ) + t * I)))⁻¹‖ ≤
          D * t ^ M * Real.exp (-(a * (ρ.re - σ) / 2 * t)) := by
  obtain ⟨C, D, N, M, _, hD, hb⟩ := exists_rotatedGaussianMode_exponential_bounds ρ σ
  refine ⟨D * Real.exp (1 / 2), M, by positivity, ?_⟩
  intro t ht ht1 a
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hφ : |boundaryDampingAngle t| ≤ Real.pi / 2 := by
    rw [abs_boundaryDampingAngle ht1]
    linarith only [one_div_pos.mpr ht0]
  have he : -((gaussianObservationRate ρ σ a - boundaryDampingAngle t / 2) * t) =
      1 / 2 - (a * (ρ.re - σ) / 2) * t := by
    dsimp only [gaussianObservationRate, boundaryDampingAngle]
    field_simp [ht0.ne']
    ring
  have hh := (hb t ht a _ hφ).2
  rw [he, Real.exp_sub] at hh
  calc
    _ ≤ D * t ^ M * (Real.exp (1 / 2) / Real.exp (a * (ρ.re - σ) / 2 * t)) := hh
    _ = _ := by rw [Real.exp_neg]; ring

private theorem normalized_boundary_prime_error_tendsto_zero
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) (ha : 0 < a)
    {h : ℝ → ℝ} (hlim : Tendsto h atTop (𝓝 0))
    (hpos : ∀ᶠ t : ℝ in atTop, 0 < h t) :
    Tendsto (fun t : ℝ =>
      (rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (h t))
          σ β a (h t) (boundaryDampingAngle t) t +
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          rotatedDivisorFilteredMellinWeight F ρ σ β (h t)
            (Real.exp (-a * t)) (boundaryDampingAngle t) t ρ) /
        ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
            (ρ - ((σ : ℂ) + t * I)))) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨C, N, hC, hb⟩ := exists_boundaryPrimeDampingFilter_spacing_preserving_error_bound
    F ρ σ β hc hc1 hσc hgap hrest havoid hρc hρ1 hρ
  obtain ⟨D, M, hD, hmode⟩ := exists_boundaryGaussianMode_inverse_bound ρ σ
  have hh1 : ∀ᶠ t : ℝ in atTop, h t ≤ 1 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ ht => ht.le
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := C * D) (N := N + M) (show 0 < a * (ρ.re - c) / 2 by positivity)
  filter_upwards [hpos, hh1, eventually_ge_atTop (|ρ.im| + 2), eventually_ge_atTop (1 : ℝ)]
    with t htpos htstep htρ ht1
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  let E := rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (h t))
      σ β a (h t) (boundaryDampingAngle t) t +
    ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      rotatedDivisorFilteredMellinWeight F ρ σ β (h t)
        (Real.exp (-a * t)) (boundaryDampingAngle t) t ρ
  let K := rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
    (ρ - ((σ : ℂ) + t * I))
  have hbound : ‖E‖ ≤ C * (h t) ^ d * t ^ N * Real.exp (a * t * (c - σ) / 2) :=
    hb a (h t) t ht1 htpos.le htstep
  have hdiv : ‖E‖ / (h t) ^ d ≤ C * t ^ N * Real.exp (a * t * (c - σ) / 2) := by
    apply (div_le_iff₀ (pow_pos htpos d)).mpr
    exact hbound.trans_eq (by ring)
  change ‖E / ((h t : ℂ) ^ d * K)‖ ≤ _
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos htpos, div_mul_eq_div_div, div_eq_mul_inv, ← norm_inv]
  calc
    _ ≤ (C * t ^ N * Real.exp (a * t * (c - σ) / 2)) *
        (D * t ^ M * Real.exp (-(a * (ρ.re - σ) / 2 * t))) :=
      mul_le_mul hdiv (hmode t htρ ht1 a) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_add, show -(a * (ρ.re - c) / 2 * t) =
        a * t * (c - σ) / 2 + -(a * (ρ.re - σ) / 2 * t) by ring, Real.exp_add]
      ring

/-- Boundary damping recovers the selected exceptional zero at every positive
speed, for every eventually positive spacing tending to zero. -/
theorem boundary_contracting_prime_filter_reads_selected_zero
    (F : Finset XiZeroCopy) {θ σ β a : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ha : 0 < a) (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    {h : ℝ → ℝ} (hlim : Tendsto h atTop (𝓝 0))
    (hpos : ∀ᶠ t : ℝ in atTop, 0 < h t) :
    Tendsto (fun t : ℝ =>
      rotatedPrimeDampingFilter (divisorDampingFilter F ρ β (h t))
        σ β a (h t) (boundaryDampingAngle t) t /
        ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
            (ρ - ((σ : ℂ) + t * I)))) atTop
      (𝓝 (-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q)))) := by
  classical
  obtain ⟨c, hcI, hcF⟩ := (Set.Ioo_infinite hρσ).exists_notMem_finset
    (F.image fun q => (xiZero q).re)
  have hσc : σ < c := hcI.1
  have hρc : c < ρ.re := hcI.2
  have hc1 : c < 1 := hρc.trans hρ1
  have hc : 1 / 2 ≤ c := (hσ.trans hσc).le
  have havoid : ∀ q ∈ F, c ≠ (xiZero q).re := by
    intro q hq he
    exact hcF (Finset.mem_image.mpr ⟨q, hq, he.symm⟩)
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let m : ℂ := (analyticOrderAt zetaResidueUnit ρ).toNat
  let P : ℝ → ℂ := fun t => (divisorDampingFilter F ρ β (h t)).eval
    (Complex.exp ((h t : ℂ) * (ρ - β)))
  let K : ℝ → ℂ := fun t => rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
    (ρ - ((σ : ℂ) + t * I))
  let A : ℝ → ℂ := fun t => rotatedPrimeDampingFilter
    (divisorDampingFilter F ρ β (h t)) σ β a (h t) (boundaryDampingAngle t) t
  have hE := normalized_boundary_prime_error_tendsto_zero F ρ σ β a hc hc1 hσc
    (hgap.trans hσc) hrest havoid hρc hρ1 hρ ha hlim hpos
  have hP := tendsto_divisorDampingFilter_scaled_value_of_tendsto F ρ β hlim
    (hpos.mono fun _ ht => ht.ne')
  have hmain := hE.sub (hP.const_mul m)
  have hKn : ∀ᶠ t : ℝ in atTop, K t ≠ 0 := by
    have hk := tendsto_norm_boundaryGaussianMode_atTop ρ σ a (mul_pos ha (sub_pos.mpr hρσ))
    exact (hk.eventually (eventually_gt_atTop (0 : ℝ))).mono fun _ ht => norm_pos_iff.mp ht
  have hmain' : Tendsto (fun t : ℝ =>
      (A t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) -
        m * (P t / (h t : ℂ) ^ d)) atTop
      (𝓝 (-m * ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
        (ρ - xiZero q)))) := by
    simpa only [A, m, P, K, d, rotatedDivisorFilteredMellinWeight, zero_sub, neg_mul] using hmain
  apply hmain'.congr'
  filter_upwards [hpos, hKn] with t ht hk
  change (A t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) -
    m * (P t / (h t : ℂ) ^ d) = A t / ((h t : ℂ) ^ d * K t)
  field_simp [hk, pow_ne_zero d (Complex.ofReal_ne_zero.mpr ht.ne')]
  ring


/-- Exponential contraction spends only horizontal amplification after
boundary rotation; there is no additional fixed Gamma loss. -/
theorem tendsto_norm_boundary_contracted_mode_atTop (d : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) (ρ : ℂ) (σ a : ℝ)
    (hr : (d : ℝ) * κ < a * (ρ.re - σ) / 2) :
    Tendsto (fun t : ℝ => ‖((Real.exp (-κ * t) : ℝ) : ℂ) ^ d *
      rotatedGaussianKernel (Real.exp (-a * t)) (boundaryDampingAngle t)
        (ρ - ((σ : ℂ) + t * I))‖) atTop atTop := by
  let K : ℝ → ℂ := fun t => rotatedGaussianKernel (Real.exp (-a * t))
    (boundaryDampingAngle t) (ρ - ((σ : ℂ) + t * I))
  let g : ℝ → ℂ := fun t => ((Real.exp (-κ * t) : ℝ) : ℂ) ^ d * K t
  obtain ⟨D, M, hD, hb⟩ := exists_boundaryGaussianMode_inverse_bound ρ σ
  have hi : Tendsto (fun t : ℝ => (g t)⁻¹) atTop (𝓝 0) := by
    apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
      (C := D) (N := M) (sub_pos.mpr hr)
    filter_upwards [eventually_ge_atTop (|ρ.im| + 2), eventually_ge_atTop (1 : ℝ)]
      with t ht ht1
    rw [g, mul_inv, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul, ← Real.exp_neg]
    rw [show -((d : ℝ) * (-κ * t)) = (d : ℝ) * κ * t by ring]
    calc
      _ ≤ Real.exp ((d : ℝ) * κ * t) *
          (D * t ^ M * Real.exp (-(a * (ρ.re - σ) / 2 * t))) :=
        mul_le_mul_of_nonneg_left (hb t ht ht1 a) (Real.exp_pos _).le
      _ = _ := by
        rw [show -((a * (ρ.re - σ) / 2 - (d : ℝ) * κ) * t) =
          (d : ℝ) * κ * t + -(a * (ρ.re - σ) / 2 * t) by ring, Real.exp_add]
        ring
  have hr0 : 0 < a * (ρ.re - σ) := by
    have hn := mul_nonneg (Nat.cast_nonneg d) hκ
    linarith only [hr, hn]
  have hK := tendsto_norm_boundaryGaussianMode_atTop ρ σ a hr0
  have hp : ∀ᶠ t : ℝ in atTop, 0 < ‖(g t)⁻¹‖ := by
    filter_upwards [hK.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    apply norm_pos_iff.mpr
    apply inv_ne_zero
    exact mul_ne_zero
      (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) (norm_pos_iff.mp ht)
  have hright := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [norm_zero] using hi.norm, hp⟩
  simpa only [Function.comp_def, norm_inv, inv_inv, g, K] using
    tendsto_inv_nhdsGT_zero.comp hright

/-- The literal prime filter diverges throughout the full horizontal
contraction range, with the complete complementary divisor retained. -/
theorem tendsto_norm_boundary_prime_filter_atTop
    (F : Finset XiZeroCopy) {θ σ β a κ : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ha : 0 < a) (hκ : 0 < κ) (ρ : ℂ)
    (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hr : ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) : ℝ) * κ <
      a * (ρ.re - σ) / 2) :
    Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
      (divisorDampingFilter F ρ β (Real.exp (-κ * t)))
        σ β a (Real.exp (-κ * t)) (boundaryDampingAngle t) t‖) atTop atTop := by
  have hlim : Tendsto (fun t : ℝ => Real.exp (-κ * t)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using HTGeometry.tendsto_pow_mul_exp_neg_scaled 0 hκ
  have hread := boundary_contracting_prime_filter_reads_selected_zero F hσ hgap hrest
    ha ρ hρσ hρ1 hρ hlim (Eventually.of_forall fun t => Real.exp_pos _)
  exact norm_tendsto_atTop_of_ratio
    (divisorDampingFilter_limit_constant_ne_zero F ρ
      (by linarith only [hσ, hρσ]) hρ1 hρ) hread
    (tendsto_norm_boundary_contracted_mode_atTop _ hκ.le ρ σ a hr)

/-- The independent boundary-rotation Euler bound still forces decay above
the absolute arithmetic contraction threshold. -/
theorem tendsto_boundary_prime_filter_zero_of_fast_contraction
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a κ : ℝ)
    (hσ : σ < 1) (ha : 0 < a) (hκ : 0 < κ)
    (hr : a * (1 - σ) / 2 <
      ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) : ℝ) * κ) :
    Tendsto (fun t : ℝ => rotatedPrimeDampingFilter
      (divisorDampingFilter F ρ β (Real.exp (-κ * t)))
        σ β a (Real.exp (-κ * t)) (boundaryDampingAngle t) t) atTop (𝓝 0) := by
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let r := (d : ℝ) * κ - a * (1 - σ) / 2
  let c := 1 + r / a
  have hr0 : 0 < r := sub_pos.mpr hr
  have hc : 1 < c := by dsimp only [c]; linarith only [div_pos hr0 ha]
  have hrate : a * (c - σ) / 2 < (d : ℝ) * κ := by
    have he : a * (c - σ) / 2 = a * (1 - σ) / 2 + r / 2 := by
      dsimp only [c]
      field_simp [ha.ne']
      ring
    rw [he]
    dsimp only [r] at hr0 ⊢
    linarith only [hr0]
  obtain ⟨C, N, hC, hb⟩ := exists_boundaryPrimeDampingFilter_arithmetic_bound
    F ρ σ β c hc (hσ.trans hc)
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := C) (N := N) (sub_pos.mpr hrate)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hh : Real.exp (-κ * t) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_mul]
    exact neg_nonpos.mpr (mul_nonneg hκ.le ht0)
  calc
    _ ≤ C * Real.exp (-κ * t) ^ d * t ^ N * Real.exp (a * t * (c - σ) / 2) :=
      hb a _ t ht (Real.exp_pos _).le hh
    _ = _ := by
      rw [← Real.exp_nat_mul, show -(((d : ℝ) * κ - a * (c - σ) / 2) * t) =
        (d : ℝ) * (-κ * t) + a * t * (c - σ) / 2 by ring, Real.exp_add]
      ring

/-- Failure of the abscissa law yields an actual nonzero divisor reading at
every positive speed and every positive contracting damping grid. -/
theorem not_asymptoticAbscissaLaw_has_boundary_contracting_prime_filters :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β →
          let d := 1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card
          let C : ℂ := -((analyticOrderAt zetaResidueUnit (xiZero q)).toNat : ℂ) *
            ((xiZero q - 1) * ∏ p ∈ F.filter (fun p => xiZero p ≠ xiZero q),
              (xiZero q - xiZero p))
          C ≠ 0 ∧ ∀ a : ℝ, 0 < a →
            ∀ h : ℝ → ℝ, Tendsto h atTop (𝓝 0) → (∀ᶠ t : ℝ in atTop, 0 < h t) →
              Tendsto (fun t : ℝ =>
                rotatedPrimeDampingFilter (divisorDampingFilter F (xiZero q) β (h t))
                  σ β a (h t) (boundaryDampingAngle t) t /
                    ((h t : ℂ) ^ d * rotatedGaussianKernel (Real.exp (-a * t))
                      (boundaryDampingAngle t) (xiZero q - ((σ : ℂ) + t * I)))) atTop (𝓝 C) := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, htop, hmax, hrest, _⟩ :=
    not_asymptoticAbscissaLaw_has_escaping_layer_profile hnot
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
  refine ⟨divisorDampingFilter_limit_constant_ne_zero F (xiZero q) hρpos hρ1 (xi_xiZero q), ?_⟩
  intro a ha h hlim hpos
  exact boundary_contracting_prime_filter_reads_selected_zero F hσ hgap hrest ha
    (xiZero q) (by rwa [hqβ]) hρ1 (xi_xiZero q) hlim hpos

/-- An actual exceptional top forces growth of literal boundary-damped
prime filters throughout the horizontal contraction range. -/
theorem not_asymptoticAbscissaLaw_has_boundary_prime_growth :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ q ∈ F, (xiZero q).re = β → ∀ a κ : ℝ, 0 < a → 0 < κ →
          ((1 + (F.filter (fun p => xiZero p ≠ xiZero q)).card : ℕ) : ℝ) * κ <
            a * (β - σ) / 2 →
          Tendsto (fun t : ℝ => ‖rotatedPrimeDampingFilter
            (divisorDampingFilter F (xiZero q) β (Real.exp (-κ * t)))
              σ β a (Real.exp (-κ * t)) (boundaryDampingAngle t) t‖) atTop atTop := by
  intro hnot
  obtain ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, hread⟩ :=
    not_asymptoticAbscissaLaw_has_boundary_contracting_prime_filters hnot
  refine ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, ?_⟩
  intro q hq hqβ a κ ha hκ hr
  obtain ⟨hC, hreadq⟩ := hread q hq hqβ
  have hlim : Tendsto (fun t : ℝ => Real.exp (-κ * t)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using HTGeometry.tendsto_pow_mul_exp_neg_scaled 0 hκ
  exact norm_tendsto_atTop_of_ratio hC
    (hreadq a ha _ hlim (Eventually.of_forall fun t => Real.exp_pos _))
    (tendsto_norm_boundary_contracted_mode_atTop _ hκ.le (xiZero q) σ a (by simpa only [hqβ] using hr))

#print axioms exists_boundaryGaussianMode_inverse_bound
#print axioms boundary_contracting_prime_filter_reads_selected_zero
#print axioms not_asymptoticAbscissaLaw_has_boundary_contracting_prime_filters
#print axioms tendsto_norm_boundary_prime_filter_atTop
#print axioms not_asymptoticAbscissaLaw_has_boundary_prime_growth
#print axioms tendsto_boundary_prime_filter_zero_of_fast_contraction

end GaloisForLFunctions.ExceptionalLayerTheory
