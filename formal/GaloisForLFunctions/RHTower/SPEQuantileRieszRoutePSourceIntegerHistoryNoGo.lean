import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceQuantitativeOscillation
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszLogLatticeHandoff
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePUnitRieszRenewalBridge
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePWeightedCreditEscape

/-!
# Integer-cell transfer and cofinal negative Route-P history

The literal continuous unit-Riesz source loses at most `(log 4 + 5) * sqrt X` credit
between a real endpoint `X` and its left integer neighbor. Quantitative two-sided
source oscillation therefore supplies arbitrarily late integer heads with positive
source credit. At those heads the signed Route-P credit is negative, while the
independent geometric remainder tends to `-∞`. Hence the complete normalized
prime-power history is cofinally unbounded below.

This closes blanket nonnegative-history passivity, not RH. A viable route must
select signed heads and pay both square debts, then construct the ordered-history
intertwiner on a meromorphic or singular source domain.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private def routePHalfWeightIntegrand (y : ℝ) : ℝ :=
  (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))

private theorem intervalIntegrable_routePHalfWeightIntegrand
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable routePHalfWeightIntegrand volume a b := by
  have hpsi : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub
      (continuous_id.intervalIntegrable (μ := volume) a b)
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) (Set.uIcc a b) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro y hy
    left
    rw [Set.uIcc_of_le hab] at hy
    exact ne_of_gt (zero_lt_one.trans_le (ha.trans hy.1))
  exact hpsi.mul_continuousOn hpow

private theorem abs_routePHalfWeightIntegrand_le_sqrt
    {X y : ℝ} (hy : 1 ≤ y) (hyX : y ≤ X) :
    |routePHalfWeightIntegrand y| ≤ (Real.log 4 + 5) * Real.sqrt X := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hpsi0 : 0 ≤ Chebyshev.psi y := Chebyshev.psi_nonneg y
  have hpsi := Chebyshev.psi_le_const_mul_self hy0.le
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  have herr : |Chebyshev.psi y - y| ≤ (Real.log 4 + 5) * y := by
    calc
      |Chebyshev.psi y - y| ≤ |Chebyshev.psi y| + |y| := abs_sub _ _
      _ = Chebyshev.psi y + y := by
        rw [abs_of_nonneg hpsi0, abs_of_nonneg hy0.le]
      _ ≤ (Real.log 4 + 4) * y + y := by gcongr
      _ = (Real.log 4 + 5) * y := by ring
  have hpow0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
  have hweight : y ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt y := by
    rw [Real.rpow_neg hy0.le, ← Real.sqrt_eq_rpow]
    simp [one_div]
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy0).ne'
  have hydiv : y / Real.sqrt y = Real.sqrt y := by
    apply (div_eq_iff hs).2
    simpa only [pow_two] using (Real.sq_sqrt hy0.le).symm
  unfold routePHalfWeightIntegrand
  rw [abs_mul, abs_of_nonneg hpow0]
  calc
    |Chebyshev.psi y - y| * y ^ (-(1 / 2 : ℝ)) ≤
        ((Real.log 4 + 5) * y) * y ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right herr hpow0
    _ = (Real.log 4 + 5) * Real.sqrt y := by
      rw [hweight]
      calc
        (Real.log 4 + 5) * y * (1 / Real.sqrt y) =
            (Real.log 4 + 5) * (y / Real.sqrt y) := by ring
        _ = _ := by rw [hydiv]
    _ ≤ (Real.log 4 + 5) * Real.sqrt X := by gcongr

theorem routePSource_integerCell_credit_lower
    {N : ℕ} {X : ℝ} (hN : 2 ≤ N)
    (hNX : (N : ℝ) ≤ X) (hXN : X ≤ (N : ℝ) + 1) :
    X * criticalMellinChebyshevResolventSource (Real.log X) -
        (Real.log 4 + 5) * Real.sqrt X ≤
      (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hXpos : 0 < X := hNpos.trans_le hNX
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNreal
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (hNreal.trans hNX)
  have hrayN := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogN
  have hrayX := unitRieszChebyshevRayIntegral_eq_fullResolvent hlogX
  rw [Real.exp_log hNpos] at hrayN
  rw [Real.exp_log hXpos] at hrayX
  have hprimeN := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log N)
  have hprimeX := unitRieszChebyshevRayIntegral_eq_primeIntegral (Real.log X)
  rw [Real.exp_log hNpos] at hprimeN
  rw [Real.exp_log hXpos] at hprimeX
  have hintN : IntervalIntegrable routePHalfWeightIntegrand volume 1 (N : ℝ) :=
    intervalIntegrable_routePHalfWeightIntegrand (a := 1) (b := (N : ℝ)) le_rfl hNreal
  have hintTail : IntervalIntegrable routePHalfWeightIntegrand volume (N : ℝ) X :=
    intervalIntegrable_routePHalfWeightIntegrand hNreal hNX
  have hsplit : unitRieszChebyshevRayIntegral (Real.log X) =
      unitRieszChebyshevRayIntegral (Real.log N) +
        ∫ y in (N : ℝ)..X, routePHalfWeightIntegrand y := by
    rw [hprimeX, hprimeN]
    change (∫ y in (1 : ℝ)..X, routePHalfWeightIntegrand y) = _
    exact (intervalIntegral.integral_add_adjacent_intervals hintN hintTail).symm
  let T : ℝ := ∫ y in (N : ℝ)..X, routePHalfWeightIntegrand y
  have hT : |T| ≤ (Real.log 4 + 5) * Real.sqrt X := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := routePHalfWeightIntegrand)
      (a := (N : ℝ)) (b := X) (C := (Real.log 4 + 5) * Real.sqrt X) (fun y hy => by
        have hy' : y ∈ Set.uIcc (N : ℝ) X := Set.uIoc_subset_uIcc hy
        rw [Set.uIcc_of_le hNX] at hy'
        rw [Real.norm_eq_abs]
        exact abs_routePHalfWeightIntegrand_le_sqrt
          (hNreal.trans hy'.1) hy'.2)
    rw [Real.norm_eq_abs] at hraw
    change |T| ≤ _
    calc
      |T| ≤ ((Real.log 4 + 5) * Real.sqrt X) * |X - (N : ℝ)| := hraw
      _ ≤ ((Real.log 4 + 5) * Real.sqrt X) * 1 := by
        gcongr
        rw [abs_of_nonneg (sub_nonneg.mpr hNX)]
        linarith
      _ = (Real.log 4 + 5) * Real.sqrt X := by ring
  have hEq : X * criticalMellinChebyshevResolventSource (Real.log X) =
      (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) + T := by
    change _ = _ + (∫ y in (N : ℝ)..X, routePHalfWeightIntegrand y)
    linarith [hrayN, hrayX, hsplit]
  linarith [le_abs_self T]

theorem routePSource_cofinal_positive_integer_credit (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 2 ≤ N ∧
      0 < (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) := by
  let A : ℝ := Real.log 4 + 5
  let B : ℝ := A + 1
  let M₀ : ℕ := M + 2
  have hM₀ : (0 : ℝ) < M₀ := by exact_mod_cast (show 0 < M₀ by omega)
  obtain ⟨t, ht, hsource⟩ :=
    _root_.RHTower.routePSource_cofinal_above_positive_sqrt_floor
      B (Real.log (M₀ : ℝ))
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
  have hrep := criticalMellinChebyshevResolventRayRepresentative_eq ht0
  have hsourceX : B * Real.exp (-t / 2) <
      criticalMellinChebyshevResolventSource (Real.log X) := by
    rw [hlogX, ← hrep]
    exact hsource
  have hsqrt : X * Real.exp (-t / 2) = Real.sqrt X := by
    dsimp only [X]
    rw [← Real.exp_add]
    have harg : t + -t / 2 = t / 2 := by ring
    rw [harg, Real.exp_half]
  have hBcredit : B * Real.sqrt X <
      X * criticalMellinChebyshevResolventSource (Real.log X) := by
    have hmul := mul_lt_mul_of_pos_left hsourceX hXpos
    have hrewrite : X * (B * Real.exp (-t / 2)) = B * Real.sqrt X := by
      calc
        X * (B * Real.exp (-t / 2)) = B * (X * Real.exp (-t / 2)) := by ring
        _ = B * Real.sqrt X := by rw [hsqrt]
    simpa only [hrewrite] using hmul
  have hAcredit : A * Real.sqrt X <
      X * criticalMellinChebyshevResolventSource (Real.log X) := by
    have hroot : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
    have hAB : A * Real.sqrt X < B * Real.sqrt X := by
      dsimp only [B]
      nlinarith
    exact hAB.trans hBcredit
  have hcell := routePSource_integerCell_credit_lower hN hNX hXN
  refine ⟨N, ?_, hN, ?_⟩
  · dsimp only [M₀] at hNbig
    omega
  · linarith

end GaloisForLFunctions.RHTower

namespace RHTower

theorem routeP_normalized_history_cofinally_unbounded_below
    (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K < B := by
  have hev := routeP_history_sub_credit_tendsto_atBot.eventually
    (eventually_lt_atBot B)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hev
  obtain ⟨N, hNbig, hN2, hpos⟩ :=
    GaloisForLFunctions.RHTower.routePSource_cofinal_positive_integer_credit
      (max M K₀ + 2)
  let K := N - 2
  have hKN : K + 2 = N := by dsimp only [K]; omega
  have hKM : M ≤ K := by dsimp only [K]; omega
  have hKK₀ : K₀ ≤ K := by dsimp only [K]; omega
  have hcredit := routePWeightedChebyshevNullCredit_eq_unitRiesz_resolvent_source K
  rw [hKN] at hcredit
  have hcreditNeg : routePWeightedChebyshevNullCredit K < 0 := by
    rw [hcredit]
    nlinarith [hpos]
  have hrem := hK₀ K hKK₀
  refine ⟨K, hKM, ?_⟩
  linarith

end RHTower
