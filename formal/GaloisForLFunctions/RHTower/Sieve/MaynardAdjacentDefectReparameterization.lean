import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

/-- A normalized one-window Perron integral is independent of the admissible Heath--Brown
eligibility parametrization used to represent its physical von Mangoldt sum. -/
theorem integral_windowRelevantAggregate_mul_normalizedMellin_eq_of_reparam
    (L X k : ℕ) (hXL : X < (L + 1) ^ k)
    {T₀ t₀ T₁ t₁ N H sigma : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hscale₀ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₀ ^ t₀ ≤ N)
    (hscale₁ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₁ ^ t₁ ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hsupport : N + 2 * H ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ t₀ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I)) =
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ t₁ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((sigma : ℂ) + (y : ℝ) * I) := by
  have h₀ := smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral
    L X k hXL hT₀ hscale₀ hN hH hsupport hsigma
  have h₁ := smul_tsum_vonMangoldt_normalized_routeTSmoothWindowWeight_eq_integral
    L X k hXL hT₁ hscale₁ hN hH hsupport hsigma
  exact h₀.symm.trans h₁

/-- **Adjacent-defect reparametrization invariance.** The signed normalized target--reference
integral depends only on its physical windows, not on the admissible height and eligibility cutoff
used in the literal Heath--Brown decomposition. -/
theorem integral_windowRelevantAggregate_mul_adjacentNormalizedMellin_eq_of_reparam
    (L X k : ℕ) (hXL : X < (L + 1) ^ k)
    {T₀ t₀ T₁ t₁ N H R sigma : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hscale₀ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₀ ^ t₀ ≤ N)
    (hscale₁ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₁ ^ t₁ ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ t₀ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))) =
    ∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ t₁ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I)) := by
  have h₀ := smul_normalized_reference_sub_target_vonMangoldt_eq_integral_kernelDefect
    L X k hXL hT₀ hscale₀ hN hH hR hsupportH hsupportR hsigma
  have h₁ := smul_normalized_reference_sub_target_vonMangoldt_eq_integral_kernelDefect
    L X k hXL hT₁ hscale₁ hN hH hR hsupportH hsupportR hsigma
  exact h₀.symm.trans h₁

/-- Any lower norm bound on an adjacent defect transfers without loss to every admissible
Heath--Brown parametrization. -/
theorem norm_integral_windowRelevantAggregate_mul_adjacentNormalizedMellin_ge_of_reparam
    (L X k : ℕ) (hXL : X < (L + 1) ^ k)
    {T₀ t₀ T₁ t₁ N H R sigma B : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hscale₀ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₀ ^ t₀ ≤ N)
    (hscale₁ : ((2 ^ (2 * k) : ℕ) : ℝ) * T₁ ^ t₁ ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hsupportH : N + 2 * H ≤ X) (hsupportR : N + 2 * R ≤ X)
    (hsigma : 0 < sigma)
    (hlarge : B ≤ ‖∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ t₀ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖) :
    B ≤ ‖∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ t₁ N
          ((sigma : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((sigma : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((sigma : ℂ) + (y : ℝ) * I))‖ := by
  rw [← integral_windowRelevantAggregate_mul_adjacentNormalizedMellin_eq_of_reparam
    L X k hXL hT₀ hT₁ hscale₀ hscale₁ hN hH hR hsupportH hsupportR hsigma]
  exact hlarge

/-- Eligibility is intrinsically a lower-edge cutoff. The logarithmic base is only a coordinate. -/
theorem isHeathBrownBoxEligible_iff_threshold_le_coreLower
    {L X k : ℕ} {T t : ℝ} (hT : 1 < T)
    (box : HeathBrownBoxChoice L X k) :
    IsHeathBrownBoxEligible L X k T t box ↔
      T ^ t ≤ (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := by
  have hD :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) =
        T ^ heathBrownBoxTotalExponent L X k T box := by
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  rw [IsHeathBrownBoxEligible, hD]
  exact (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.symm

/-- Equal physical eligibility thresholds give the same literal eligible boxes. -/
theorem isHeathBrownBoxEligible_iff_of_rpow_threshold_eq
    {L X k : ℕ} {T₀ t₀ T₁ t₁ : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hthreshold : T₀ ^ t₀ = T₁ ^ t₁)
    (box : HeathBrownBoxChoice L X k) :
    IsHeathBrownBoxEligible L X k T₀ t₀ box ↔
      IsHeathBrownBoxEligible L X k T₁ t₁ box := by
  rw [isHeathBrownBoxEligible_iff_threshold_le_coreLower hT₀ box,
    isHeathBrownBoxEligible_iff_threshold_le_coreLower hT₁ box,
    hthreshold]

/-- **Pointwise aggregate reparametrization.** Equal physical eligibility thresholds make the
entire window-relevant aggregate identical at every complex point, not merely after integration. -/
theorem heathBrownWindowRelevantEligibleDyadicAggregate_eq_of_rpow_threshold_eq
    (L X k : ℕ) {T₀ t₀ T₁ t₁ N : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hthreshold : T₀ ^ t₀ = T₁ ^ t₁) (s : ℂ) :
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ t₀ N s =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ t₁ N s := by
  classical
  rw [heathBrownWindowRelevantEligibleDyadicAggregate,
    heathBrownWindowRelevantEligibleDyadicAggregate]
  apply Finset.sum_congr rfl
  intro box _hbox
  rw [isHeathBrownBoxEligible_iff_of_rpow_threshold_eq
    hT₀ hT₁ hthreshold box]

/-- Canonical exact cutoff parametrizations all have physical threshold `X^(1/120)`. -/
theorem rpow_mu_div_oneTwenty_eq_of_rpow_mu_eq_cutoff
    {X : ℕ} {T₀ mu₀ T₁ mu₁ : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hX₀ : T₀ ^ mu₀ = X) (hX₁ : T₁ ^ mu₁ = X) :
    T₀ ^ (mu₀ / 120) = T₁ ^ (mu₁ / 120) := by
  have hT₀0 : 0 ≤ T₀ := by linarith
  have hT₁0 : 0 ≤ T₁ := by linarith
  calc
    T₀ ^ (mu₀ / 120) = (T₀ ^ mu₀) ^ (1 / 120 : ℝ) := by
      have he : mu₀ / 120 = mu₀ * (1 / 120 : ℝ) := by ring
      rw [he]
      exact Real.rpow_mul hT₀0 mu₀ (1 / 120 : ℝ)
    _ = ((X : ℝ) ^ (1 / 120 : ℝ)) := by rw [hX₀]
    _ = (T₁ ^ mu₁) ^ (1 / 120 : ℝ) := by rw [hX₁]
    _ = T₁ ^ (mu₁ / 120) := by
      have he : mu₁ / 120 = mu₁ * (1 / 120 : ℝ) := by ring
      rw [he]
      exact (Real.rpow_mul hT₁0 mu₁ (1 / 120 : ℝ)).symm

/-- Canonically normalized `(T,mu)` coordinates leave the window-relevant aggregate pointwise
unchanged. This is the height-shell matching law needed after multiscale defect selection. -/
theorem heathBrownWindowRelevantEligibleDyadicAggregate_eq_of_rpow_mu_eq_cutoff
    (L X k : ℕ) {T₀ mu₀ T₁ mu₁ N : ℝ}
    (hT₀ : 1 < T₀) (hT₁ : 1 < T₁)
    (hX₀ : T₀ ^ mu₀ = X) (hX₁ : T₁ ^ mu₁ = X) (s : ℂ) :
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T₀ (mu₀ / 120) N s =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T₁ (mu₁ / 120) N s :=
  heathBrownWindowRelevantEligibleDyadicAggregate_eq_of_rpow_threshold_eq
    L X k hT₀ hT₁
      (rpow_mu_div_oneTwenty_eq_of_rpow_mu_eq_cutoff
        hT₀ hT₁ hX₀ hX₁) s

end RHTower.Sieve
