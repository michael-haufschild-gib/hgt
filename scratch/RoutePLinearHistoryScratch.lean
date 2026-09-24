import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceFixedAmplitudeOscillation
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceIntegerHistoryNoGo

open Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

private theorem routePSource_integer_credit_cofinally_linear :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ 2 ≤ N ∧
      δ * (N : ℝ) <
        (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) := by
  obtain ⟨δ, hδ, hosc⟩ := exists_routePSource_fixed_amplitude_two_sided
  let A : ℝ := Real.log 4 + 5
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hExpTop : Tendsto (fun t : ℝ => Real.exp (t / 2)) atTop atTop := by
    have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop := by
      simpa [div_eq_mul_inv, mul_comm] using
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    exact Real.tendsto_exp_atTop.comp hhalf
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (hExpTop.eventually (eventually_gt_atTop (2 * A / δ)))
  refine ⟨δ / 2, by positivity, fun M => ?_⟩
  let M₀ : ℕ := M + 2
  have hM₀ : (0 : ℝ) < M₀ := by exact_mod_cast (show 0 < M₀ by omega)
  let T : ℝ := max (Real.log (M₀ : ℝ)) T₁
  obtain ⟨t, ht, hsrc⟩ := (hosc T).1
  have htlog : Real.log (M₀ : ℝ) < t := (le_max_left _ _).trans_lt ht
  have htT₁ : T₁ ≤ t := (le_max_right _ _).trans ht.le
  have hlarge : 2 * A / δ < Real.exp (t / 2) := hT₁ t htT₁
  let X : ℝ := Real.exp t
  let N : ℕ := ⌊X⌋₊
  have hXpos : 0 < X := Real.exp_pos t
  have hXgt : (M₀ : ℝ) < X := by
    calc
      (M₀ : ℝ) = Real.exp (Real.log (M₀ : ℝ)) := (Real.exp_log hM₀).symm
      _ < Real.exp t := Real.exp_lt_exp.mpr htlog
  have hNbig : M₀ ≤ N := Nat.le_floor hXgt.le
  have hN : 2 ≤ N := by dsimp only [M₀] at hNbig; omega
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
  have ht0 : 0 ≤ t := by
    have hM₀one : (1 : ℝ) ≤ M₀ := by exact_mod_cast (show 1 ≤ M₀ by omega)
    exact (Real.log_nonneg hM₀one).trans htlog.le
  have hsourceX : δ < criticalMellinChebyshevResolventSource (Real.log X) := by
    rw [Real.log_exp]
    rw [← criticalMellinChebyshevResolventRayRepresentative_eq ht0]
    exact hsrc
  have hroot : Real.sqrt X = Real.exp (t / 2) := by
    dsimp only [X]
    exact (Real.exp_half t).symm
  have hrootpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hrootbound : 2 * A < δ * Real.sqrt X := by
    rw [hroot]
    have := (div_lt_iff₀ hδ).mp hlarge
    nlinarith
  have hrootSq : Real.sqrt X ^ (2 : ℕ) = X := Real.sq_sqrt hXpos.le
  have hcellLoss : A * Real.sqrt X < δ / 2 * X := by
    have h := mul_lt_mul_of_pos_right hrootbound hrootpos
    nlinarith [hrootSq]
  have hXcredit : δ * X <
      X * criticalMellinChebyshevResolventSource (Real.log X) :=
    by simpa only [mul_comm δ X] using
      mul_lt_mul_of_pos_left hsourceX hXpos
  have hcell := routePSource_integerCell_credit_lower hN hNX hXN
  refine ⟨N, ?_, hN, ?_⟩
  · dsimp only [M₀] at hNbig
    omega
  · dsimp only [A] at hcellLoss hcell
    have hscale : δ / 2 * (N : ℝ) ≤ δ / 2 * X :=
      mul_le_mul_of_nonneg_left hNX (by positivity)
    linarith

theorem routeP_normalized_history_cofinally_below_negative_linear :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ K : ℕ, M ≤ K ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K <
        -δ * ((K + 2 : ℕ) : ℝ) := by
  obtain ⟨δ, hδ, hsource⟩ := routePSource_integer_credit_cofinally_linear
  have hev := routeP_history_sub_credit_tendsto_atBot.eventually
    (eventually_lt_atBot (0 : ℝ))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hev
  refine ⟨2 * δ, by positivity, fun M => ?_⟩
  obtain ⟨N, hNbig, hN2, hcreditPos⟩ :=
    hsource (max M K₀ + 2)
  let K := N - 2
  have hKN : K + 2 = N := by dsimp only [K]; omega
  have hKM : M ≤ K := by dsimp only [K]; omega
  have hKK₀ : K₀ ≤ K := by dsimp only [K]; omega
  have hcredit := routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source K
  rw [hKN] at hcredit
  have hrem := hK₀ K hKK₀
  refine ⟨K, hKM, ?_⟩
  rw [hKN]
  rw [hcredit] at hrem
  nlinarith [hcreditPos]

end RHTower
