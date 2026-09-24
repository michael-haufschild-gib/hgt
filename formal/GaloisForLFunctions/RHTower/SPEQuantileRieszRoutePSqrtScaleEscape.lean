import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceIntegerHistoryNoGo

/-!
# Square-root-scale escape of the literal Route-P physical history

Quantitative unit-Riesz source oscillation survives integer-cell transfer at
arbitrarily large square-root amplitude. The full normalized physical history
inherits the negative excursions because its geometric remainder is eventually
negative. Thus a compensator of uniformly bounded square-root amplitude cannot
restore blanket source-history passivity. This is a source-side obstruction, not
the missing sign-selected payment or meromorphic graph intertwiner.
-/

open Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower

/-- Arbitrarily late integer heads retain any prescribed square-root-scale
positive source excursion after the bounded integer-cell transfer loss. -/
theorem routePSource_integer_credit_cofinally_above_sqrt
    (B : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 2 ≤ N ∧
      B * Real.sqrt (N : ℝ) <
        (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) := by
  let A : ℝ := Real.log 4 + 5
  let B₀ : ℝ := max B 0
  let C : ℝ := B₀ + A + 1
  let M₀ : ℕ := M + 2
  have hM₀ : (0 : ℝ) < M₀ := by exact_mod_cast (show 0 < M₀ by omega)
  obtain ⟨t, ht, hsource⟩ :=
    _root_.RHTower.routePSource_cofinal_above_positive_sqrt_floor
      C (Real.log (M₀ : ℝ))
  let X : ℝ := Real.exp t
  let N : ℕ := ⌊X⌋₊
  have hXpos : 0 < X := Real.exp_pos t
  have hXgt : (M₀ : ℝ) < X := by
    calc
      (M₀ : ℝ) = Real.exp (Real.log (M₀ : ℝ)) := (Real.exp_log hM₀).symm
      _ < Real.exp t := Real.exp_lt_exp.mpr ht
  have hNbig : M₀ ≤ N := Nat.le_floor hXgt.le
  have hN : 2 ≤ N := by dsimp only [M₀] at hNbig; omega
  have hNX : (N : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
  have ht0 : 0 ≤ t := by
    have hM₀one : (1 : ℝ) ≤ M₀ := by exact_mod_cast (show 1 ≤ M₀ by omega)
    exact (Real.log_nonneg hM₀one).trans ht.le
  have hlogX : Real.log X = t := Real.log_exp t
  have hrep :=
    _root_.GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative_eq ht0
  have hsourceX : C * Real.exp (-t / 2) <
      criticalMellinChebyshevResolventSource (Real.log X) := by
    rw [hlogX, ← hrep]
    exact hsource
  have hsqrt : X * Real.exp (-t / 2) = Real.sqrt X := by
    dsimp only [X]
    rw [← Real.exp_add]
    have harg : t + -t / 2 = t / 2 := by ring
    rw [harg, Real.exp_half]
  have hCcredit : C * Real.sqrt X <
      X * criticalMellinChebyshevResolventSource (Real.log X) := by
    have hmul := mul_lt_mul_of_pos_left hsourceX hXpos
    have hrewrite : X * (C * Real.exp (-t / 2)) = C * Real.sqrt X := by
      calc
        X * (C * Real.exp (-t / 2)) = C * (X * Real.exp (-t / 2)) := by ring
        _ = C * Real.sqrt X := by rw [hsqrt]
    simpa only [hrewrite] using hmul
  have hcell :=
    _root_.GaloisForLFunctions.RHTower.routePSource_integerCell_credit_lower hN hNX hXN
  have hrootNX : Real.sqrt (N : ℝ) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt hNX
  have hB₀nonneg : 0 ≤ B₀ := le_max_right B 0
  have hB₀ge : B ≤ B₀ := le_max_left B 0
  have hBroot : B * Real.sqrt (N : ℝ) ≤ B₀ * Real.sqrt X := by
    calc
      B * Real.sqrt (N : ℝ) ≤ B₀ * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_right hB₀ge (Real.sqrt_nonneg _)
      _ ≤ B₀ * Real.sqrt X := mul_le_mul_of_nonneg_left hrootNX hB₀nonneg
  have hAroot : B₀ * Real.sqrt X <
      X * criticalMellinChebyshevResolventSource (Real.log X) -
        A * Real.sqrt X := by
    have hrootpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
    dsimp only [C] at hCcredit
    linarith
  refine ⟨N, ?_, hN, ?_⟩
  · dsimp only [M₀] at hNbig
    omega
  · exact lt_of_le_of_lt hBroot (lt_of_lt_of_le hAroot hcell)

/-- The complete normalized physical history has no lower bound of fixed
square-root scale on any cofinal tail. -/
theorem routeP_normalized_history_sqrt_scale_cofinally_unbounded_below
    (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K <
        B * Real.sqrt ((K + 2 : ℕ) : ℝ) := by
  have hev := routeP_history_sub_credit_tendsto_atBot.eventually
    (eventually_lt_atBot (0 : ℝ))
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hev
  let P : ℝ := |B| + 1
  obtain ⟨N, hNbig, hN2, hsource⟩ :=
    routePSource_integer_credit_cofinally_above_sqrt P (max M K₀ + 2)
  let K := N - 2
  have hKN : K + 2 = N := by dsimp only [K]; omega
  have hKM : M ≤ K := by dsimp only [K]; omega
  have hKK₀ : K₀ ≤ K := by dsimp only [K]; omega
  have hcredit := routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source K
  rw [hKN] at hcredit
  have hrem := hK₀ K hKK₀
  have hrootpos : 0 < Real.sqrt (N : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (show 0 < N by omega)
  have hP : 0 < 2 * P + B := by
    dsimp only [P]
    by_cases hB : 0 ≤ B
    · rw [abs_of_nonneg hB]
      linarith
    · have hBneg : B < 0 := lt_of_not_ge hB
      rw [abs_of_neg hBneg]
      linarith
  refine ⟨K, hKM, ?_⟩
  rw [hKN]
  rw [hcredit] at hrem
  have hgap : 0 < (2 * P + B) * Real.sqrt (N : ℝ) :=
    mul_pos hP hrootpos
  nlinarith only [hsource, hrem, hgap]

end RHTower
