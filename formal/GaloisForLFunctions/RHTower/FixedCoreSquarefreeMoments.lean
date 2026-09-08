import GaloisForLFunctions.RHTower.FixedCoreSquarefreeDensity
import GaloisForLFunctions.HTGeometry.BeurlingCrossSystemBlindness
import GaloisForLFunctions.RHTower.ProlateActionLinear
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact weighted limits of the fixed-core squarefree source

The normalized source survival count has limit rho*(1-t^2). Finite
layer cake and dominated convergence give every half-integer moment,
including their values on moving macroscopic cutoffs. The resulting
square-root-affine square is the weight of an actual quotient energy block.
-/

noncomputable section
open Filter Topology MeasureTheory
open Finset
namespace RHTower

/-- Normalized survival function of all squarefree source magnitudes sqrt(r/N). -/
def fixedCoreSquarefreeSurvival (P : Finset ℕ) (N : ℕ) (t : ℝ) : ℝ :=
  (∑ r ∈ fixedCoreSquarefreeIndices P N,
    if t < Real.sqrt ((r : ℝ)/N) then (1 : ℝ) else 0) / N

private lemma survival_bound (P : Finset ℕ) (N : ℕ) (t : ℝ) :
    0 ≤ fixedCoreSquarefreeSurvival P N t ∧ fixedCoreSquarefreeSurvival P N t ≤ 1 := by
  have hc : (fixedCoreSquarefreeIndices P N).card ≤ N := by
    simpa [fixedCoreSquarefreeIndices] using
      (card_filter_le (s := Icc 1 N) (fun n => Squarefree n ∧ Disjoint n.primeFactors P))
  constructor
  · unfold fixedCoreSquarefreeSurvival
    positivity
  · by_cases hN : N = 0
    · simp [fixedCoreSquarefreeSurvival, hN]
    have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    apply (div_le_one hNR).mpr
    calc
      _ ≤ ∑ r ∈ fixedCoreSquarefreeIndices P N, (1 : ℝ) := by
        apply sum_le_sum
        intro r hr
        split_ifs <;> norm_num
      _ = ((fixedCoreSquarefreeIndices P N).card : ℝ) := by simp
      _ ≤ N := by exact_mod_cast hc

/-- Exact count representation of the source survival function. -/
theorem fixedCoreSquarefreeSurvival_eq_counts (P : Finset ℕ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fixedCoreSquarefreeSurvival P N t =
      (fixedCoreSquarefreeCount P N : ℝ)/N -
        (fixedCoreSquarefreeCount P ⌊(N : ℝ)*t^2⌋₊ : ℝ)/N := by
  let A := fixedCoreSquarefreeIndices P N
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht2 : t^2 ≤ 1 := by nlinarith
  have hcut : ⌊(N : ℝ)*t^2⌋₊ ≤ N := by
    have h := Nat.floor_mono (mul_le_mul_of_nonneg_left ht2 hNR.le)
    simpa using h
  have hiff (r : ℕ) : (¬ t < Real.sqrt ((r : ℝ)/N)) ↔ r ≤ ⌊(N : ℝ)*t^2⌋₊ := by
    rw [not_lt, Real.sqrt_le_iff, and_iff_right ht0,
      Nat.le_floor_iff (by positivity), div_le_iff₀ hNR]
    rw [mul_comm (t^2) (N : ℝ)]
  have he : A.filter (fun r : ℕ => ¬t < Real.sqrt ((r : ℝ)/N)) =
      fixedCoreSquarefreeIndices P ⌊(N : ℝ)*t^2⌋₊ := by
    ext r
    simp only [mem_filter, A, fixedCoreSquarefreeIndices, mem_Icc, hiff]
    constructor
    · rintro ⟨⟨hr, hs⟩, hc⟩
      exact ⟨⟨hr.1, hc⟩, hs⟩
    · rintro ⟨hr, hs⟩
      exact ⟨⟨⟨hr.1, hr.2.trans hcut⟩, hs⟩, hr.2⟩
  have hcard := card_filter_add_card_filter_not (s := A)
    (fun r => t < Real.sqrt ((r : ℝ)/N))
  rw [he] at hcard
  have hs : (∑ r ∈ A, if t < Real.sqrt ((r : ℝ)/N) then (1 : ℝ) else 0) =
      ((A.filter (fun r : ℕ => t < Real.sqrt ((r : ℝ)/N))).card : ℝ) := by
    rw [← sum_filter]
    simp
  have hcast : ((A.filter (fun r : ℕ => t < Real.sqrt ((r : ℝ)/N))).card : ℝ) +
      (fixedCoreSquarefreeCount P ⌊(N : ℝ)*t^2⌋₊ : ℝ) = fixedCoreSquarefreeCount P N := by
    exact_mod_cast hcard
  unfold fixedCoreSquarefreeSurvival
  change (∑ r ∈ A, if t < Real.sqrt ((r : ℝ)/N) then (1 : ℝ) else 0)/N = _
  rw [hs]
  rw [← sub_div]
  congr 1
  linarith

private lemma survival_limit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun N : ℕ => fixedCoreSquarefreeSurvival P N t) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*(1-t^2))) := by
  let ρ := Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1)
  have hscale : Tendsto (fun N : ℕ => (N : ℝ)*t^2) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos (sq_pos_of_pos ht0)).mpr tendsto_natCast_atTop_atTop
  have hcount := ((tendsto_fixedCoreSquarefreeRatio P hP).comp hscale).mul_const (t^2)
  have hfull := (tendsto_fixedCoreSquarefreeCount_div P hP).sub hcount
  have he : ρ - ρ*t^2 = ρ*(1-t^2) := by ring
  change Tendsto _ atTop (𝓝 (ρ-ρ*t^2)) at hfull
  rw [he] at hfull
  apply hfull.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [fixedCoreSquarefreeSurvival_eq_counts P hN ht0.le ht1]
  dsimp only [Function.comp_def, fixedCoreSquarefreeRatio]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : t ≠ 0 := ht0.ne'
  field_simp

private lemma survival_moment_integrable (P : Finset ℕ) (N k : ℕ) :
    IntervalIntegrable (fun t : ℝ => ((k : ℝ)+1)*t^k*fixedCoreSquarefreeSurvival P N t)
      volume 0 1 := by
  have h := (intervalIntegrable_finsetSum (fixedCoreSquarefreeIndices P N)
    (fun r hr => GaloisForLFunctions.HTGeometry.Beurling.intervalIntegrable_layer_atom
      k (Real.sqrt ((r : ℝ)/N)) 0 1)).div_const (N : ℝ)
  convert h using 1
  ext t
  rw [fixedCoreSquarefreeSurvival, ← mul_div_assoc, mul_sum]

/-- Exact finite layer-cake identity for every half-integer source moment. -/
theorem fixedCoreSquarefreeMoment_eq_survival_integral
    (P : Finset ℕ) (N k : ℕ) :
    (∑ r ∈ fixedCoreSquarefreeIndices P N, (Real.sqrt ((r : ℝ)/N))^(k+1))/(N : ℝ) =
      ∫ t in (0 : ℝ)..1, ((k : ℝ)+1)*t^k*fixedCoreSquarefreeSurvival P N t := by
  have hatom (r : ℕ) (hr : r ∈ fixedCoreSquarefreeIndices P N) :
      0 ≤ Real.sqrt ((r : ℝ)/N) ∧ Real.sqrt ((r : ℝ)/N) ≤ 1 := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hrN := (mem_Icc.mp (mem_filter.mp hr).1).2
    by_cases hN : N = 0
    · simp [hN]
    have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    simpa using (div_le_one hNR).mpr (by exact_mod_cast hrN)
  have he (t : ℝ) : ((k : ℝ)+1)*t^k*fixedCoreSquarefreeSurvival P N t =
      (∑ r ∈ fixedCoreSquarefreeIndices P N,
        ((k : ℝ)+1)*t^k*(if t < Real.sqrt ((r : ℝ)/N) then (1 : ℝ) else 0))/(N : ℝ) := by
    rw [fixedCoreSquarefreeSurvival, ← mul_div_assoc, mul_sum]
  simp_rw [he]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun (r : ℕ) hr =>
      GaloisForLFunctions.HTGeometry.Beurling.intervalIntegrable_layer_atom
        k (Real.sqrt ((r : ℝ)/N)) 0 1)]
  congr 1
  apply sum_congr rfl
  intro r hr
  exact (GaloisForLFunctions.HTGeometry.Beurling.integral_layer_atom k
    (hatom r hr).1 (hatom r hr).2).symm

/-- Every fixed-core half-integer moment has its exact arithmetic density limit. -/
theorem tendsto_fixedCoreSquarefree_half_moments
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ fixedCoreSquarefreeIndices P N, (Real.sqrt ((r : ℝ)/N))^(k+1))/(N : ℝ)) atTop
      (𝓝 (2*(Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))/((k : ℝ)+3))) := by
  let ρ := Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1)
  have hint := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun N : ℕ => fun t : ℝ => ((k : ℝ)+1)*t^k*fixedCoreSquarefreeSurvival P N t)
    (f := fun t : ℝ => ((k : ℝ)+1)*t^k*(ρ*(1-t^2)))
    (fun _ : ℝ => (k : ℝ)+1)
    (Eventually.of_forall (fun N => (survival_moment_integrable P N k).def'.aestronglyMeasurable))
    (Eventually.of_forall (fun N => Eventually.of_forall (fun t ht => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have ht0 := (Set.mem_Ioc.mp ht).1.le
      have ht1 := (Set.mem_Ioc.mp ht).2
      obtain ⟨hs0, hs1⟩ := survival_bound P N t
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hp := pow_le_one₀ ht0 ht1 (n := k)
      calc
        _ ≤ ((k : ℝ)+1)*1*1 := mul_le_mul
          (mul_le_mul_of_nonneg_left hp (by positivity)) hs1 hs0 (by positivity)
        _ = _ := by ring)))
    intervalIntegrable_const
    (Eventually.of_forall (fun t ht => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h := (survival_limit P hP (Set.mem_Ioc.mp ht).1 (Set.mem_Ioc.mp ht).2).const_mul
        (((k : ℝ)+1)*t^k)
      exact h))
  have hi : (∫ t in (0 : ℝ)..1, ((k : ℝ)+1)*t^k*(ρ*(1-t^2))) = 2*ρ/((k : ℝ)+3) := by
    have he (t : ℝ) : ((k : ℝ)+1)*t^k*(ρ*(1-t^2)) =
        ((k : ℝ)+1)*ρ*(t^k-t^(k+2)) := by rw [pow_add]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((continuous_pow k).intervalIntegrable 0 1) ((continuous_pow (k+2)).intervalIntegrable 0 1),
      integral_pow, integral_pow]
    simp only [one_pow, Nat.cast_add, Nat.cast_ofNat]
    rw [zero_pow (by omega : k+1 ≠ 0), zero_pow (by omega : k+2+1 ≠ 0)]
    field_simp
    ring
  rw [hi] at hint
  simpa only [fixedCoreSquarefreeMoment_eq_survival_integral] using hint

private lemma scaled_cutoff_limits {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => ⌊c*(N : ℝ)⌋₊) atTop atTop ∧
    Tendsto (fun N : ℕ => (⌊c*(N : ℝ)⌋₊ : ℝ)/(N : ℝ)) atTop (𝓝 c) := by
  have hs : Tendsto (fun N : ℕ => c*(N : ℝ)) atTop atTop := by
    simpa [mul_comm] using (tendsto_mul_const_atTop_of_pos hc).mpr
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨tendsto_nat_floor_atTop.comp hs, ?_⟩
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp hs).mul_const c
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [] with N
  dsimp only [Function.comp_def]
  field_simp

/-- Count density on every fixed positive macroscopic cutoff scale. -/
theorem tendsto_fixedCoreSquarefree_scaled_count
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => (fixedCoreSquarefreeCount P ⌊c*(N : ℝ)⌋₊ : ℝ)/(N : ℝ)) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*c)) := by
  obtain ⟨hK, hratio⟩ := scaled_cutoff_limits hc
  have h := ((tendsto_fixedCoreSquarefreeCount_div P hP).comp hK).mul hratio
  apply h.congr'
  filter_upwards [hK.eventually_gt_atTop 0] with N hN
  have hKN : (⌊c*(N : ℝ)⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [Function.comp_def]
  field_simp

/-- Every half-integer moment at a moving macroscopic cutoff, normalized
by the parent cutoff rather than its truncated child. -/
theorem tendsto_fixedCoreSquarefree_scaled_half_moments
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ fixedCoreSquarefreeIndices P ⌊c*(N : ℝ)⌋₊,
        (Real.sqrt ((r : ℝ)/N))^(k+1))/(N : ℝ)) atTop
      (𝓝 ((2*(Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))/((k : ℝ)+3))*
        c*(Real.sqrt c)^(k+1))) := by
  obtain ⟨hK, hratio⟩ := scaled_cutoff_limits hc
  have h := (((tendsto_fixedCoreSquarefree_half_moments P hP k).comp hK).mul hratio).mul
    (hratio.sqrt.pow (k+1))
  apply h.congr'
  filter_upwards [hK.eventually_gt_atTop 0] with N hN
  let K := ⌊c*(N : ℝ)⌋₊
  have hKN : (K : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he (r : ℕ) : Real.sqrt ((r : ℝ)/N) =
      Real.sqrt ((r : ℝ)/K)*Real.sqrt ((K : ℝ)/N) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (r : ℝ)/K)]
    congr 1
    field_simp
  change ((∑ r ∈ fixedCoreSquarefreeIndices P K, (Real.sqrt ((r : ℝ)/K))^(k+1))/(K : ℝ))*
    ((K : ℝ)/N)*(Real.sqrt ((K : ℝ)/N))^(k+1) = _
  have hsum : (∑ r ∈ fixedCoreSquarefreeIndices P K,
      (Real.sqrt ((r : ℝ)/N))^(k+1)) =
      (∑ r ∈ fixedCoreSquarefreeIndices P K, (Real.sqrt ((r : ℝ)/K))^(k+1))*
        (Real.sqrt ((K : ℝ)/N))^(k+1) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro r hr
    rw [he r, mul_pow]
  rw [hsum]
  field_simp

/-- Exact limit for the square-root-affine squares occurring on every
fixed quotient block of the actual divisor energy. -/
theorem tendsto_fixedCoreSquarefree_scaled_affine_sqrt_square
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ fixedCoreSquarefreeIndices P ⌊c*(N : ℝ)⌋₊,
        (a+b*Real.sqrt ((r : ℝ)/N))^2)/(N : ℝ)) atTop
      (𝓝 ((Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1))*
        (a^2*c+(4/3:ℝ)*a*b*c*Real.sqrt c+b^2*c^2/2))) := by
  let ρ := Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ)/(p+1)
  have h0 := (tendsto_fixedCoreSquarefree_scaled_count P hP hc).const_mul (a^2)
  have h1 := (tendsto_fixedCoreSquarefree_scaled_half_moments P hP 0 hc).const_mul (2*a*b)
  have h2 := (tendsto_fixedCoreSquarefree_scaled_half_moments P hP 1 hc).const_mul (b^2)
  have h := (h0.add h1).add h2
  convert h using 1
  · ext N
    have he (r : ℕ) : (a+b*Real.sqrt ((r : ℝ)/N))^2 =
        a^2+(2*a*b)*Real.sqrt ((r : ℝ)/N)+b^2*(Real.sqrt ((r : ℝ)/N))^2 := by ring
    simp_rw [he]
    simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
      fixedCoreSquarefreeCount, Nat.zero_add, Nat.one_add, pow_one, add_div, mul_div_assoc]
    ring
  · congr 1
    have hs := Real.sq_sqrt hc.le
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, pow_one]
    rw [hs]
    ring

end RHTower
