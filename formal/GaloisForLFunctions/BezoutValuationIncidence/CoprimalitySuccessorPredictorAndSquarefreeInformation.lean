import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.RHTower.CoprimeClassCount

/-!
# Coprimality predictor and exact squarefree information

The coefficient transport `Kc(d) = μ(d) Σ_{d|m≤N} c(m)/φ(m)` has the literal
signal `Σ_{m≤N, (m,k)=1} c(m)/φ(m)`. Its Selberg multiplier is `μ(q)/φ(q)`.
Consequently it retains exactly the squarefree Selberg coordinates. Its range
is exactly the zero-extended, squarefree-supported coefficient space.

The subsequent physical prediction theorem identifies this arithmetic operator
as the optimal divisor-sieve model of integer succession.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-- Explicit arithmetic coefficient transport for optimal one-step prediction. -/
def sieveSuccessorPredictor (N : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  moebiusReal d * ∑ m ∈ (Icc 1 N).filter (fun m => d ∣ m), c m / (m.totient : ℝ)

private theorem predictor_outside (N : ℕ) (c : ℕ → ℝ) (d : ℕ)
    (hd : d ∉ Icc 1 N) : sieveSuccessorPredictor N c d = 0 := by
  unfold sieveSuccessorPredictor
  suffices (∑ m ∈ (Icc 1 N).filter (fun m => d ∣ m), c m / (m.totient : ℝ)) = 0 by
    rw [this, mul_zero]
  apply sum_eq_zero
  intro m hm
  obtain ⟨hm, hdm⟩ := mem_filter.mp hm
  have hmpos := (mem_Icc.mp hm).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hmpos
  exact (hd (mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hmpos hdm).trans (mem_Icc.mp hm).2⟩)).elim

private theorem predictor_transport (N : ℕ) (c F : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, sieveSuccessorPredictor N c d * F d) =
      ∑ m ∈ Icc 1 N, c m / (m.totient : ℝ) * ∑ d ∈ m.divisors, moebiusReal d * F d := by
  classical
  calc
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        if d ∣ m then c m / (m.totient : ℝ) * (moebiusReal d * F d) else 0 := by
      simp only [sieveSuccessorPredictor, sum_filter, mul_sum, sum_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro m _
      split_ifs <;> ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      have hset : (Icc 1 N).filter (fun d => d ∣ m) = m.divisors := by
        ext d
        simp only [mem_filter, mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hd⟩
          exact ⟨hd, by have := (mem_Icc.mp hm).1; omega⟩
        · rintro ⟨hd, hm0⟩
          have hdp := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hm0)
          exact ⟨⟨hdp, (Nat.le_of_dvd (by omega) hd).trans (mem_Icc.mp hm).2⟩, hd⟩
      rw [← sum_filter, hset, mul_sum]

/-- The predicted signal is a literal weighted coprimality response at every integer. -/
theorem sieveSeq_successorPredictor (N k : ℕ) (c : ℕ → ℝ) :
    sieveSeq N (sieveSuccessorPredictor N c) k =
      ∑ m ∈ Icc 1 N, if m.Coprime k then c m / (m.totient : ℝ) else 0 := by
  have he : sieveSeq N (sieveSuccessorPredictor N c) k =
      ∑ d ∈ Icc 1 N, sieveSuccessorPredictor N c d * (if d ∣ k then 1 else 0) := by
    simp only [sieveSeq, sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp
  rw [he, predictor_transport]
  apply sum_congr rfl
  intro m hm
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (GaloisForLFunctions.RHTower.CoprimeClassCount.coprime_indicator
      (mem_Icc.mp hm).1 k)
  have hi : (∑ d ∈ m.divisors, moebiusReal d * (if d ∣ k then 1 else 0)) =
      if m.Coprime k then 1 else 0 := by
    push_cast at h
    rw [h]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp [moebiusReal]
  rw [hi]
  split_ifs <;> simp

private theorem moebius_mul_coprime (q r : ℕ) :
    moebiusReal (q * r) = if q.Coprime r then moebiusReal q * moebiusReal r else 0 := by
  by_cases h : q.Coprime r
  · simp only [if_pos h, moebiusReal, isMultiplicative_moebius.map_mul_of_coprime h, Int.cast_mul]
  · have hn : ¬Squarefree (q * r) := fun hs => h (Nat.coprime_of_squarefree_mul hs)
    simp [h, moebiusReal, moebius_eq_zero_of_not_squarefree hn]

private theorem restricted_divisor_sum (q t : ℕ) (hq : 0 < q) (ht : 0 < t) :
    (∑ d ∈ (q * t).divisors.filter (fun d => q ∣ d), moebiusReal d / (d : ℝ)) =
      moebiusReal q / (q.totient : ℝ) * ((q * t).totient : ℝ) / (q * t : ℕ) := by
  have hreindex : (∑ d ∈ (q * t).divisors.filter (fun d => q ∣ d),
      moebiusReal d / (d : ℝ)) =
      ∑ r ∈ t.divisors, moebiusReal (q * r) / ((q * r : ℕ) : ℝ) := by
    symm
    apply sum_bij (fun r _ => q * r)
    · intro r hr
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_divisors hr), (Nat.mul_pos hq ht).ne'⟩,
        dvd_mul_right q r⟩
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hq hab
    · intro d hd
      obtain ⟨hd, hqd⟩ := mem_filter.mp hd
      refine ⟨d / q, Nat.mem_divisors.mpr ⟨?_, ht.ne'⟩, Nat.mul_div_cancel' hqd⟩
      apply (Nat.mul_dvd_mul_iff_left hq).mp
      rw [Nat.mul_div_cancel' hqd]
      exact Nat.dvd_of_mem_divisors hd
    · intro r _
      rfl
  rw [hreindex]
  have hφq : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hφ : ((q * t).totient : ℝ) = (q.totient : ℝ) *
      ∑ r ∈ t.divisors, if r.Coprime q then (μ r : ℝ) * (t / r : ℕ) else 0 := by
    have h := GaloisForLFunctions.RHTower.TotientMulMoebius.totient_mul_eq q hq t
    simp only [GaloisForLFunctions.RHTower.TotientMulMoebius.H, sum_filter] at h
    have hr := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum] at hr
    rw [hr]
    congr 1
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp only [Int.cast_mul, Int.cast_natCast, Int.cast_zero]
  have hinner : (∑ r ∈ t.divisors, moebiusReal (q * r) / ((q * r : ℕ) : ℝ)) =
      moebiusReal q / ((q : ℝ) * t) *
        ∑ r ∈ t.divisors, if r.Coprime q then (μ r : ℝ) * (t / r : ℕ) else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hr).ne'
    rw [moebius_mul_coprime, Nat.cast_mul]
    by_cases hc : q.Coprime r
    · rw [if_pos hc, if_pos hc.symm, Nat.cast_div (Nat.dvd_of_mem_divisors hr) hr0]
      unfold moebiusReal
      field_simp
    · rw [if_neg hc, if_neg (fun h => hc h.symm)]
      simp
  rw [hinner, hφ]
  rw [Nat.cast_mul]
  field_simp

/-- The exact Selberg spectrum of one-step arithmetic prediction, including zero level. -/
theorem selbergMultiplesCoord_successorPredictor (N q : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (sieveSuccessorPredictor N c) q =
      moebiusReal q / (q.totient : ℝ) * selbergMultiplesCoord N c q := by
  have he : selbergMultiplesCoord N (sieveSuccessorPredictor N c) q =
      ∑ d ∈ Icc 1 N, sieveSuccessorPredictor N c d *
        (if q ∣ d then 1 / (d : ℝ) else 0) := by
    simp only [selbergMultiplesCoord, sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp [div_eq_mul_inv]
  rw [he, predictor_transport, selbergMultiplesCoord, sum_filter, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hmpos := (mem_Icc.mp hm).1
  have hinner : (∑ d ∈ m.divisors, moebiusReal d *
      (if q ∣ d then 1 / (d : ℝ) else 0)) =
      ∑ d ∈ m.divisors.filter (fun d => q ∣ d), moebiusReal d / (d : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hinner]
  by_cases hqm : q ∣ m
  · rw [if_pos hqm]
    have hq := Nat.pos_of_dvd_of_pos hqm hmpos
    have ht : 0 < m / q := Nat.div_pos (Nat.le_of_dvd hmpos hqm) hq
    have hd := restricted_divisor_sum q (m / q) hq ht
    rw [Nat.mul_div_cancel' hqm] at hd
    rw [hd]
    have hφm : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hmpos).ne'
    field_simp
  · rw [if_neg hqm, mul_zero]
    have hz : (∑ d ∈ m.divisors.filter (fun d => q ∣ d), moebiusReal d / (d : ℝ)) = 0 := by
      apply sum_eq_zero
      intro d hd
      exact (hqm ((mem_filter.mp hd).2.trans (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1))).elim
    rw [hz, mul_zero]

private theorem predictor_coefficients_eq (N : ℕ) (c b : ℕ → ℝ)
    (h : ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q = selbergMultiplesCoord N b q) :
    ∀ d ∈ Icc 1 N, c d = b d := by
  have hz := (selbergMultiplesCoord_tail_zero_iff N 0 (fun d => c d - b d)).mp
    (fun q hq => by rw [selbergMultiplesCoord_sub, h q hq, sub_self])
  intro d hd
  exact sub_eq_zero.mp (hz d hd)

/-- Two inputs predict identically exactly when all squarefree Selberg coordinates agree. -/
theorem sieveSuccessorPredictor_eq_iff (N : ℕ) (c b : ℕ → ℝ) :
    sieveSuccessorPredictor N c = sieveSuccessorPredictor N b ↔
      ∀ q ∈ Icc 1 N, Squarefree q → selbergMultiplesCoord N c q = selbergMultiplesCoord N b q := by
  constructor
  · intro h q hq hs
    have hy := congrArg (fun a => selbergMultiplesCoord N a q) h
    rw [selbergMultiplesCoord_successorPredictor, selbergMultiplesCoord_successorPredictor] at hy
    have hm : moebiusReal q ≠ 0 := by
      change (μ q : ℝ) ≠ 0
      exact_mod_cast moebius_ne_zero_iff_squarefree.mpr hs
    have hφ : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hq).1).ne'
    exact mul_left_cancel₀ (div_ne_zero hm hφ) hy
  · intro h
    have he := predictor_coefficients_eq N (sieveSuccessorPredictor N c)
      (sieveSuccessorPredictor N b) (fun q hq => by
        rw [selbergMultiplesCoord_successorPredictor, selbergMultiplesCoord_successorPredictor]
        by_cases hs : Squarefree q
        · rw [h q hq hs]
        · simp [moebiusReal, moebius_eq_zero_of_not_squarefree hs])
    funext d
    by_cases hd : d ∈ Icc 1 N
    · exact he d hd
    · rw [predictor_outside N c d hd, predictor_outside N b d hd]

/-- Exact range: finite squarefree raw support, with no remaining compatibility conditions. -/
theorem sieveSuccessorPredictor_range (N : ℕ) (b : ℕ → ℝ) :
    (∃ c, sieveSuccessorPredictor N c = b) ↔
      (∀ d, d ∉ Icc 1 N → b d = 0) ∧
      (∀ d ∈ Icc 1 N, ¬Squarefree d → b d = 0) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun d hd => predictor_outside N c d hd,
      fun d _ hd => by simp [sieveSuccessorPredictor, moebiusReal,
        moebius_eq_zero_of_not_squarefree hd]⟩
  · rintro ⟨hout, hsq⟩
    let c := pmRamanujanResidueCoeff
      (fun q => (q.totient : ℝ) / moebiusReal q * selbergMultiplesCoord N b q) N
    refine ⟨c, ?_⟩
    have he := predictor_coefficients_eq N (sieveSuccessorPredictor N c) b (fun q hq => by
      rw [selbergMultiplesCoord_successorPredictor]
      dsimp only [c]
      rw [selbergMultiplesCoord_ramanujan_inverse, if_pos hq]
      by_cases hs : Squarefree q
      · have hm : moebiusReal q ≠ 0 := by
          change (μ q : ℝ) ≠ 0
          exact_mod_cast moebius_ne_zero_iff_squarefree.mpr hs
        have hφ : (q.totient : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hq).1).ne'
        field_simp
      · have hz : selbergMultiplesCoord N b q = 0 := by
          apply sum_eq_zero
          intro d hd
          obtain ⟨hdI, hqd⟩ := mem_filter.mp hd
          rw [hsq d hdI (fun h => hs (fun p hp => h p (hp.trans hqd))), zero_div]
        rw [hz]
        ring)
    funext d
    by_cases hd : d ∈ Icc 1 N
    · exact he d hd
    · rw [predictor_outside N c d hd, hout d hd]

end
end GaloisForLFunctions.BezoutValuationIncidence
