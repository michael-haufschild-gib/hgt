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

#print axioms exists_boundaryGaussianMode_inverse_bound
#print axioms boundary_contracting_prime_filter_reads_selected_zero
#print axioms not_asymptoticAbscissaLaw_has_boundary_contracting_prime_filters

end GaloisForLFunctions.ExceptionalLayerTheory
