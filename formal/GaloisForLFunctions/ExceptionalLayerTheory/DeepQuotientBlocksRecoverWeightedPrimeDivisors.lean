import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletSeriesOfDyadicBinomialPrimeCounts

/-!
# Prime divisors inside a deep quotient block

In the block ending just before `qM`, the only possible selected multiple
is `qM` itself when `q > M`. Each prime power dividing `M` contributes on
exactly its own number of cutoffs. Summing the block therefore recovers
the prime divisors with the prime-power size as a weight.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem quotient_class_iff {q X m : ℕ} (hm : 0 < m) :
    q ∣ X/m+1 ↔ ∃ k : ℕ, X < q*(k*m) ∧ q*(k*m) ≤ X+m := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_,?_⟩
    · rw [← mul_assoc,← hk]
      exact (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self _)
    · rw [← mul_assoc,← hk,add_mul,one_mul]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  · rintro ⟨k,hl,hu⟩
    rw [← mul_assoc] at hl hu
    have hlo := (Nat.div_lt_iff_lt_mul hm).mpr hl
    have hhi := (Nat.le_div_iff_mul_le hm).mpr hu
    rw [Nat.add_div_right _ hm] at hhi
    exact ⟨k,by omega⟩

private theorem deep_class_iff {q M r m : ℕ} (hM : 0 < M) (hq : M < q)
    (hr : 0 < r) (hrq : r ≤ q) (hm : 0 < m) :
    q ∣ (q*M-r)/m+1 ↔ m ∣ M ∧ r ≤ m := by
  have hq0 : 0 < q := by omega
  have htop : r ≤ q*M := hrq.trans (Nat.le_mul_of_pos_right q hM)
  rw [quotient_class_iff hm]
  constructor
  · rintro ⟨k,hl,hu⟩
    have hk : 0 < k := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h,zero_mul,mul_zero] at hl
      omega
    have hlo : M ≤ k*m := by
      by_contra! h
      have hh := Nat.mul_le_mul_left q (show k*m+1 ≤ M from h)
      rw [mul_add,mul_one] at hh
      omega
    have he : k*m=M := by
      by_contra hn
      have h₁ := Nat.mul_le_mul_left (q-1) (show M+1 ≤ k*m by omega)
      have h₂ := Nat.le_mul_of_pos_left m hk
      have hdown : (q-1)*(k*m)+k*m = q*(k*m) := by rw [← add_one_mul,show q-1+1=q by omega]
      have hup : (q-1)*M+M=q*M := by rw [← add_one_mul,show q-1+1=q by omega]
      rw [mul_add,mul_one] at h₁
      omega
    rw [he] at hu
    exact ⟨⟨k,he.symm.trans (mul_comm ..)⟩,by omega⟩
  · rintro ⟨⟨k,hk⟩,hrm⟩
    refine ⟨k,?_,?_⟩ <;> rw [mul_comm k m,← hk] <;> omega

/-- Count of the last quotient class with a prescribed arithmetic weight. -/
def quotientClassMassOf (f : ℕ → ℝ) (q X : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 X, f m*(if q ∣ X/m+1 then 1 else 0)

/-- The sufficiently large divisors of the upper base contribute exactly
once, for every choice of weights. -/
theorem quotientClassMassOf_deep_block (f : ℕ → ℝ) {q M r : ℕ} (hM : 0 < M) (hq : M < q)
    (hr : 0 < r) (hrq : r ≤ q) :
    quotientClassMassOf f q (q*M-r) = ∑ m ∈ M.divisors.filter (r ≤ ·), f m := by
  let X := q*M-r
  change (∑ m ∈ Icc 1 X, f m*(if q ∣ X/m+1 then (1:ℝ) else 0)) = _
  simp_rw [mul_ite,mul_one,mul_zero]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [mem_filter,mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hm,_⟩,hc⟩
    obtain ⟨hd,hrm⟩ := (deep_class_iff hM hq hr hrq hm).mp hc
    exact ⟨⟨hd,hM.ne'⟩,hrm⟩
  · rintro ⟨⟨hd,_⟩,hrm⟩
    have hm := Nat.pos_of_dvd_of_pos hd hM
    have hc := (deep_class_iff hM hq hr hrq hm).mpr ⟨hd,hrm⟩
    have hX : m ≤ X := by
      by_contra! h
      change q ∣ X/m+1 at hc
      rw [Nat.div_eq_of_lt h,zero_add] at hc
      have := Nat.le_of_dvd one_pos hc
      omega
    exact ⟨⟨hm,hX⟩,hc⟩

/-- The actual prime count at every interior cutoff. -/
theorem lastClassPrimeMass_deep_block {q M r : ℕ} (hM : 0 < M) (hq : M < q)
    (hr : 0 < r) (hrq : r ≤ q) :
    lastClassPrimeMass q (q*M-r) =
      ∑ m ∈ M.divisors.filter (r ≤ ·), vonMangoldt m :=
  quotientClassMassOf_deep_block vonMangoldt hM hq hr hrq

/-- Every arithmetic weight gives zero at the sampled base endpoints of sufficiently deep blocks. -/
theorem quotientClassMassOf_deep_endpoint (f : ℕ → ℝ) {q N : ℕ} (hq : N+1 < q) :
    quotientClassMassOf f q (q*N) = 0 := by
  have ht : q*(N+1)-q=q*N := by rw [mul_add,mul_one]; omega
  rw [← ht,quotientClassMassOf_deep_block f (Nat.zero_lt_succ N) hq (by omega) le_rfl]
  apply sum_eq_zero
  intro m hm
  obtain ⟨hd,hle⟩ := mem_filter.mp hm
  exact (not_le_of_gt (Nat.le_of_dvd (Nat.zero_lt_succ N) (Nat.dvd_of_mem_divisors hd) |>.trans_lt hq) hle).elim

/-- The last slot recovers the full divisor logarithm. -/
theorem lastClassPrimeMass_last_slot {q M : ℕ} (hM : 0 < M) (hq : M < q) :
    lastClassPrimeMass q (q*M-1) = Real.log M := by
  rw [lastClassPrimeMass_deep_block hM hq one_pos (by omega)]
  have he : M.divisors.filter (1 ≤ ·) = M.divisors := filter_true_of_mem
    (fun _ h => Nat.pos_of_mem_divisors h)
  rw [he,vonMangoldt_sum]

/-- All arithmetic weights are recovered at one interior slot of each deep block. -/
theorem quotientClassMassOf_recovers_weight (f : ℕ → ℝ) {q M : ℕ} (hM : 0 < M) (hq : M < q) :
    quotientClassMassOf f q (q*M-M) = f M := by
  rw [quotientClassMassOf_deep_block f hM hq hM hq.le]
  have he : M.divisors.filter (M ≤ ·) = {M} := by
    ext m
    simp only [mem_filter,Nat.mem_divisors,mem_singleton]
    constructor
    · rintro ⟨⟨hd,_⟩,hle⟩; exact le_antisymm (Nat.le_of_dvd hM hd) hle
    · rintro rfl; exact ⟨⟨dvd_refl _,hM.ne'⟩,le_rfl⟩
  rw [he,sum_singleton]

/-- One interior slot returns the actual Mangoldt weight of the base integer. -/
theorem lastClassPrimeMass_mangoldt_slot {q M : ℕ} (hM : 0 < M) (hq : M < q) :
    lastClassPrimeMass q (q*M-M) = vonMangoldt M :=
  quotientClassMassOf_recovers_weight vonMangoldt hM hq

/-- Each divisor of the base occupies exactly its own number of slots. -/
theorem sum_quotientClassMassOf_deep_block (f : ℕ → ℝ) {q M : ℕ} (hM : 0 < M) (hq : M < q) :
    ∑ r ∈ Icc 1 q, quotientClassMassOf f q (q*M-r) =
      ∑ m ∈ M.divisors, (m:ℝ)*f m := by
  calc
    _ = ∑ r ∈ Icc 1 q, ∑ m ∈ M.divisors, if r ≤ m then f m else 0 := by
      refine sum_congr rfl fun r hr => ?_
      rw [quotientClassMassOf_deep_block f hM hq (mem_Icc.mp hr).1 (mem_Icc.mp hr).2,sum_filter]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun m hm => ?_
      have hmq := (Nat.le_of_dvd hM (Nat.dvd_of_mem_divisors hm)).trans hq.le
      have he : (Icc 1 q).filter (· ≤ m) = Icc 1 m := by
        ext r; simp only [mem_filter,mem_Icc]; omega
      rw [← sum_filter,he,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]

/-- The block sum counts each prime power dividing the base once per occupied slot. -/
theorem sum_lastClassPrimeMass_deep_block {q M : ℕ} (hM : 0 < M) (hq : M < q) :
    ∑ r ∈ Icc 1 q, lastClassPrimeMass q (q*M-r) =
      ∑ m ∈ M.divisors, (m:ℝ)*vonMangoldt m :=
  sum_quotientClassMassOf_deep_block vonMangoldt hM hq

#print axioms lastClassPrimeMass_deep_block
#print axioms sum_lastClassPrimeMass_deep_block
#print axioms quotientClassMassOf_deep_endpoint
#print axioms quotientClassMassOf_recovers_weight

end GaloisForLFunctions.ExceptionalLayerTheory
