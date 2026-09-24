import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePShiftedAnalyticRigidity
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePLinearHistoryEscape
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

open Filter Topology Complex Set

namespace RHTower

open GaloisForLFunctions.RHTower

private theorem routeP_source_eventual_upper_implies_RH
    {B T : ℝ} (hT : 0 ≤ T)
    (hupper : ∀ t : ℝ, T < t → routePSourceRay t ≤ B) :
    RiemannHypothesis := by
  have hpos : ∀ t : ℝ, T < t → 0 ≤ (-1 : ℝ) * routePSourceRay t + B := by
    intro t ht
    have h := hupper t ht
    nlinarith
  have hA := analyticOnNhd_routePShiftedReconstructedLogDeriv
    (epsilon := (-1 : ℝ)) (B := B) (T := T) hT hpos (by norm_num)
  have hEq := routePShiftedReconstructedLogDeriv_eq_logDeriv_rightHalf
    (epsilon := (-1 : ℝ)) (B := B) (T := T) hT hpos (by norm_num)
  apply riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
  intro s hs hlo hzero
  have hs1 : s ≠ 1 := by
    intro heq
    rw [heq] at hlo
    norm_num at hlo
  have hregZero : regularizedRiemannZeta s = 0 := by
    rw [regularizedRiemannZeta_of_ne_one hs1, hzero, mul_zero]
  have hU : ∀ᶠ w in 𝓝[≠] s, 1 / 2 < w.re :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have heq : logDeriv regularizedRiemannZeta =ᶠ[𝓝[≠] s]
      routePShiftedReconstructedLogDeriv (-1) B T := by
    filter_upwards [hU] with w hw
    exact (hEq w hw).symm
  have hcongr := meromorphicOrderAt_congr heq
  have hnonneg : (0 : WithTop ℤ) ≤
      meromorphicOrderAt (logDeriv regularizedRiemannZeta) s := by
    rw [hcongr]
    exact (hA s hs).meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hregZero] at hnonneg
  exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
    exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

private theorem routeP_source_unbounded_above_of_not_RH
    (hnot : ¬ RiemannHypothesis) (B T : ℝ) :
    ∃ t : ℝ, T < t ∧ B < routePSourceRay t := by
  by_contra h
  push Not at h
  let T₀ : ℝ := max T 0
  have hT₀ : 0 ≤ T₀ := le_max_right _ _
  have hupper : ∀ t : ℝ, T₀ < t → routePSourceRay t ≤ B := by
    intro t ht
    exact h t ((le_max_left _ _).trans_lt ht)
  exact hnot (routeP_source_eventual_upper_implies_RH hT₀ hupper)

private theorem routeP_source_integer_unbounded_above_of_not_RH
    (hnot : ¬ RiemannHypothesis) (B : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 2 ≤ N ∧
      B * (N : ℝ) <
        (N : ℝ) * criticalMellinChebyshevResolventSource (Real.log N) := by
  let A : ℝ := Real.log 4 + 5
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let M₀ : ℕ := M + 2
  have hM₀ : (0 : ℝ) < M₀ := by exact_mod_cast (show 0 < M₀ by omega)
  let T : ℝ := Real.log (M₀ : ℝ)
  obtain ⟨t, ht, hsrc⟩ :=
    routeP_source_unbounded_above_of_not_RH hnot (|B| + A + 2) T
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
  have hsourceX : |B| + A + 2 <
      criticalMellinChebyshevResolventSource (Real.log X) := by
    rw [Real.log_exp]
    rw [← criticalMellinChebyshevResolventRayRepresentative_eq ht0]
    exact hsrc
  have hrootSq : Real.sqrt X ^ (2 : ℕ) = X := Real.sq_sqrt hXpos.le
  have hrootLE : Real.sqrt X ≤ X := by
    have hXone : (1 : ℝ) ≤ X := by
      have : (1 : ℝ) ≤ M₀ := by exact_mod_cast (show 1 ≤ M₀ by omega)
      linarith
    nlinarith [Real.sqrt_nonneg X]
  have hAX : A * Real.sqrt X ≤ A * X :=
    mul_le_mul_of_nonneg_left hrootLE hA
  have hBcast : B * (N : ℝ) ≤ |B| * X := calc
    B * (N : ℝ) ≤ |B| * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self B) (Nat.cast_nonneg N)
    _ ≤ |B| * X := mul_le_mul_of_nonneg_left hNX (abs_nonneg B)
  have hXcredit : (|B| + A + 2) * X <
      X * criticalMellinChebyshevResolventSource (Real.log X) := by
    simpa only [mul_comm (|B| + A + 2) X] using
      mul_lt_mul_of_pos_left hsourceX hXpos
  have hcell := routePSource_integerCell_credit_lower hN hNX hXN
  refine ⟨N, ?_, hN, ?_⟩
  · dsimp only [M₀] at hNbig
    omega
  · dsimp only [A] at hcell hXcredit hAX
    nlinarith [hBcast]

/-- If RH fails, no fixed linear compensator bounds the physical Route-P history below. -/
theorem routeP_normalized_history_superlinear_escape_or_RH :
    RiemannHypothesis ∨
      ∀ B : ℝ, ∀ M : ℕ, ∃ K : ℕ, M ≤ K ∧
        ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect K <
          -B * ((K + 2 : ℕ) : ℝ) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    intro B M
    have hev := routeP_history_sub_credit_tendsto_atBot.eventually
      (eventually_lt_atBot (0 : ℝ))
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hev
    obtain ⟨N, hNbig, hN2, hcreditPos⟩ :=
      routeP_source_integer_unbounded_above_of_not_RH hRH (B / 2) (max M K₀ + 2)
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
