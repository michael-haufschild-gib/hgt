import GaloisForLFunctions.ExceptionalLayerTheory.ContourBoundsForFiniteDivisorFilters

/-!
# Divisor recovery under arbitrary contraction

The complete filtered error contains the same spacing power as the selected
mode. After normalization, every positive spacing tending to zero recovers
the divisor, independently of its rate of contraction.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem tendsto_exp_difference_div_step {h : ℝ → ℝ}
    (hlim : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ t : ℝ in atTop, h t ≠ 0)
    (z w : ℂ) :
    Tendsto (fun t : ℝ => (Complex.exp ((h t : ℂ) * z) -
      Complex.exp ((h t : ℂ) * w)) / (h t : ℂ)) atTop (𝓝 (z - w)) := by
  have hderiv := (((hasDerivAt_id (x := (0 : ℂ))).mul_const z).cexp.sub
    (((hasDerivAt_id (x := (0 : ℂ))).mul_const w).cexp))
  have hstep : Tendsto (fun t : ℝ => (h t : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.comp hlim
    · filter_upwards [hne] with t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero] using ht
  have hs := hderiv.tendsto_slope_zero.comp hstep
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_add, zero_mul, mul_zero,
    Complex.exp_zero, one_mul, mul_one, sub_self, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hs

/-- Arbitrary nonzero spacings tending to zero expose the exact product of
differences between the selected point and all filter roots. -/
theorem tendsto_divisorDampingFilter_scaled_value_of_tendsto
    (F : Finset XiZeroCopy) (ρ : ℂ) (β : ℝ) {h : ℝ → ℝ}
    (hlim : Tendsto h atTop (𝓝 0)) (hne : ∀ᶠ t : ℝ in atTop, h t ≠ 0) :
    Tendsto (fun t : ℝ => (divisorDampingFilter F ρ β (h t)).eval
      (Complex.exp ((h t : ℂ) * (ρ - β))) /
        (h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card)) atTop
      (𝓝 ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q))) := by
  classical
  have hfactor (z : ℂ) : Tendsto (fun t : ℝ =>
      (Complex.exp ((h t : ℂ) * (ρ - β)) - Complex.exp ((h t : ℂ) * (z - β))) /
        (h t : ℂ)) atTop (𝓝 (ρ - z)) := by
    simpa only [show (ρ - (β : ℂ)) - (z - β) = ρ - z by ring] using
      tendsto_exp_difference_div_step hlim hne (ρ - β) (z - β)
  have hprod := (hfactor 1).mul
    (tendsto_finsetProd (F.filter (fun q => xiZero q ≠ ρ)) fun q _ => hfactor (xiZero q))
  apply hprod.congr
  intro t
  simp only [divisorDampingFilter, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_div_distrib, Finset.prod_const, ← mul_div_mul_comm, pow_add, pow_one]

private theorem normalized_prime_error_tendsto_zero
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hr : a * (c - σ) / 2 < gaussianObservationRate ρ σ a)
    {h : ℝ → ℝ} (hlim : Tendsto h atTop (𝓝 0))
    (hpos : ∀ᶠ t : ℝ in atTop, 0 < h t) :
    Tendsto (fun t : ℝ =>
      (primeDampingFilter (divisorDampingFilter F ρ β (h t)) σ β a (h t) t +
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          divisorFilteredMellinWeight F ρ σ β (h t) (Real.exp (-a * t)) t ρ) /
        ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))))
      atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let N := d + 1
  obtain ⟨C, hC, hb⟩ := exists_primeDampingFilter_spacing_preserving_error_bound
    F ρ σ β hc hc1 hσc hgap hrest havoid hρc hρ1 hρ
  obtain ⟨B, D, L, M, _, hD, hmode⟩ := exists_gaussianMode_exponential_bounds ρ σ
  have hh1 : ∀ᶠ t : ℝ in atTop, h t ≤ 1 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ ht => ht.le
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := C * D * 2 ^ N) (N := N + M) (sub_pos.mpr hr)
  filter_upwards [hpos, hh1, eventually_ge_atTop (|ρ.im| + 2), eventually_ge_atTop (1 : ℝ)]
    with t htpos htstep htρ ht1
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  let E := primeDampingFilter (divisorDampingFilter F ρ β (h t)) σ β a (h t) t +
    ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      divisorFilteredMellinWeight F ρ σ β (h t) (Real.exp (-a * t)) t ρ
  let K := gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))
  have hbound : ‖E‖ ≤ C * (h t) ^ d * (1 + t) ^ N *
      Real.exp (a * t * (c - σ) / 2) := by
    have hN : 2 + (F.filter (fun q => xiZero q ≠ ρ)).card = N := by dsimp [N, d]; omega
    simpa only [E, d, abs_of_nonneg ht0, hN] using hb a (h t) t htpos.le htstep
  have hdiv : ‖E‖ / (h t) ^ d ≤ C * (1 + t) ^ N *
      Real.exp (a * t * (c - σ) / 2) := by
    apply (div_le_iff₀ (pow_pos htpos d)).mpr
    exact hbound.trans_eq (by ring)
  have hp : (1 + t) ^ N ≤ (2 : ℝ) ^ N * t ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ht1]) N
  change ‖E / ((h t : ℂ) ^ d * K)‖ ≤ _
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos htpos, div_mul_eq_div_div, div_eq_mul_inv, ← norm_inv]
  calc
    _ ≤ (C * (1 + t) ^ N * Real.exp (a * t * (c - σ) / 2)) *
        (D * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t))) :=
      mul_le_mul hdiv (hmode t htρ a).2 (norm_nonneg _) (by positivity)
    _ ≤ (C * ((2 : ℝ) ^ N * t ^ N) * Real.exp (a * t * (c - σ) / 2)) *
        (D * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t))) := by gcongr
    _ = _ := by
      rw [pow_add, show -((gaussianObservationRate ρ σ a - a * (c - σ) / 2) * t) =
        a * t * (c - σ) / 2 + -(gaussianObservationRate ρ σ a * t) by ring, Real.exp_add]
      ring

/-- Every positive spacing tending to zero recovers the selected exceptional
zero. There is no restriction on the contraction rate. -/
theorem arbitrary_contracting_prime_filter_reads_selected_zero
    (F : Finset XiZeroCopy) {θ σ β a : ℝ} (hσ : 1 / 2 < σ)
    (hgap : θ < σ) (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ha : 0 < a) (ρ : ℂ) (hρσ : σ < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hr : 0 < gaussianObservationRate ρ σ a) {h : ℝ → ℝ}
    (hlim : Tendsto h atTop (𝓝 0)) (hpos : ∀ᶠ t : ℝ in atTop, 0 < h t) :
    Tendsto (fun t : ℝ =>
      primeDampingFilter (divisorDampingFilter F ρ β (h t)) σ β a (h t) t /
        ((h t : ℂ) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)))) atTop
      (𝓝 (-((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ), (ρ - xiZero q)))) := by
  classical
  let r := gaussianObservationRate ρ σ a
  have hinterval : σ < min ρ.re (σ + r / a) :=
    lt_min hρσ (lt_add_of_pos_right σ (div_pos hr ha))
  obtain ⟨c, hcI, hcF⟩ := (Set.Ioo_infinite hinterval).exists_notMem_finset
    (F.image fun q => (xiZero q).re)
  have hσc : σ < c := hcI.1
  have hρc : c < ρ.re := hcI.2.trans_le (min_le_left _ _)
  have hc1 : c < 1 := hρc.trans hρ1
  have hc : 1 / 2 ≤ c := (hσ.trans hσc).le
  have havoid : ∀ q ∈ F, c ≠ (xiZero q).re := by
    intro q hq he
    exact hcF (Finset.mem_image.mpr ⟨q, hq, he.symm⟩)
  have hrate : a * (c - σ) / 2 < gaussianObservationRate ρ σ a := by
    have hupper := hcI.2.trans_le (min_le_right _ _)
    have hca : (c - σ) * a < r := (lt_div_iff₀ ha).mp (by linarith only [hupper])
    dsimp only [r] at hca
    nlinarith only [hca, hr]
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let m : ℂ := (analyticOrderAt zetaResidueUnit ρ).toNat
  let P : ℝ → ℂ := fun t => (divisorDampingFilter F ρ β (h t)).eval
    (Complex.exp ((h t : ℂ) * (ρ - β)))
  let K : ℝ → ℂ := fun t => gaussianMBKernel (Real.exp (-a * t))
    (ρ - ((σ : ℂ) + t * I))
  let A : ℝ → ℂ := fun t =>
    primeDampingFilter (divisorDampingFilter F ρ β (h t)) σ β a (h t) t
  have hE := normalized_prime_error_tendsto_zero F ρ σ β a hc hc1 hσc
    (hgap.trans hσc) hrest havoid hρc hρ1 hρ hrate hlim hpos
  have hP := tendsto_divisorDampingFilter_scaled_value_of_tendsto F ρ β hlim
    (hpos.mono fun _ ht => ht.ne')
  have hmain := hE.sub (hP.const_mul m)
  have hKn : ∀ᶠ t : ℝ in atTop, K t ≠ 0 := by
    have hk := tendsto_norm_gaussianMode_atTop_of_positive_rate ρ σ a hr
    exact (hk.eventually (eventually_gt_atTop (0 : ℝ))).mono fun _ ht => norm_pos_iff.mp ht
  have hmain' : Tendsto (fun t : ℝ =>
      (A t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) -
        m * (P t / (h t : ℂ) ^ d)) atTop
      (𝓝 (-m * ((ρ - 1) * ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
        (ρ - xiZero q)))) := by
    simpa only [A, m, P, K, d, divisorFilteredMellinWeight, zero_sub, neg_mul] using hmain
  apply hmain'.congr'
  filter_upwards [hpos, hKn] with t ht hk
  change (A t + m * (P t * K t)) / ((h t : ℂ) ^ d * K t) -
    m * (P t / (h t : ℂ) ^ d) = A t / ((h t : ℂ) ^ d * K t)
  field_simp [hk, pow_ne_zero d (Complex.ofReal_ne_zero.mpr ht.ne')]
  ring

end GaloisForLFunctions.ExceptionalLayerTheory
