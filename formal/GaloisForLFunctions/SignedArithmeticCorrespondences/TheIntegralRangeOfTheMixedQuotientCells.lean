import GaloisForLFunctions.SignedArithmeticCorrespondences.TheFullWeilFormOnInterleavingDivisors

/-!
# Integral range of the mixed quotient cells

A tail of the glued quotient profile counts pairs incident under one fixed
multiplication. At ratio one it is twice the integral inner product. This
parity condition is the entire obstruction on mixed integral profiles.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset

/-- Summing the quotient cells above a cut replaces all endpoint jumps by
the upper divisor evaluated at the corresponding multiple. -/
theorem quotientCoefficient_tail (X N k : ℕ) (u b : ℕ → ℤ) :
    ∑ q ∈ Icc k N, quotientCoefficient X N u b q =
      ∑ i ∈ Icc 1 X, (u i : ℝ) * upperDivisor N b (k*i) := by
  unfold quotientCoefficient
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_comm, upperDivisor, Int.cast_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjN := (Nat.div_le_self j i).trans (mem_Icc.mp hj).2
  have hi₀ := (mem_Icc.mp hi).1
  rw [sum_ite_eq]
  by_cases h : k*i ≤ j
  · rw [if_pos (mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hi₀).mpr h,hjN⟩),if_pos h]
  · have hn : j/i ∉ Icc k N := fun he => h ((Nat.le_div_iff_mul_le hi₀).mp (mem_Icc.mp he).1)
    rw [if_neg hn,if_neg h,Int.cast_zero,mul_zero]

/-- The full two-sided tail at k is the sum of the two mixed correlations
between actual conductor multiplicities at i and ki. -/
theorem twoSidedCoefficient_tail (N k : ℕ) (a b : ℕ → ℤ) :
    ∑ q ∈ Icc k N, twoSidedCoefficient N a b q =
      ∑ i ∈ Icc 1 N, ((upperDivisor N a i:ℝ)*upperDivisor N b (k*i) +
        (upperDivisor N b i:ℝ)*upperDivisor N a (k*i)) := by
  simp only [twoSidedCoefficient,sum_add_distrib,quotientCoefficient_tail]

/-- The total over positive cells is an even integer with known half. On
a self-intersection that half is exactly the integral coefficient mass. -/
theorem twoSidedCoefficient_total (N : ℕ) (a b : ℕ → ℤ) :
    ∑ q ∈ Icc 1 N, twoSidedCoefficient N a b q =
      ((2 * ∑ i ∈ Icc 1 N, upperDivisor N a i*upperDivisor N b i : ℤ):ℝ) := by
  rw [twoSidedCoefficient_tail]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [one_mul]
  ring

private theorem cell_eq_tail_sub {k N : ℕ} (hk : k≤N) (f : ℕ → ℝ) :
    f k = (∑ q ∈ Icc k N, f q) - ∑ q ∈ Icc (k+1) N, f q := by
  have hs : Icc (k+1) N = (Icc k N).erase k := by
    ext j
    simp only [mem_Icc,mem_erase]
    omega
  rw [hs,← sum_erase_add (Icc k N) f (mem_Icc.mpr ⟨le_rfl,hk⟩)]
  ring

/-- A cell is the first difference of the two directed multiplicative
correlations. Values of the upper divisors beyond the cut are zero. -/
theorem twoSidedCoefficient_difference {k N : ℕ} (hk : k≤N) (a b : ℕ → ℤ) :
    let T := fun j => ∑ i ∈ Icc 1 N,
      ((upperDivisor N a i:ℝ)*upperDivisor N b (j*i) +
        (upperDivisor N b i:ℝ)*upperDivisor N a (j*i))
    twoSidedCoefficient N a b k = T k-T (k+1) := by
  simpa only [twoSidedCoefficient_tail] using
    cell_eq_tail_sub hk (twoSidedCoefficient N a b)

/-- An atom at conductor one already realizes every admissible integral
profile simultaneously. The total of the targets specifies its partner's
multiplicity at one, and all other multiplicities are prescribed tails. -/
theorem quotient_profile_of_even_total {N : ℕ} (hN : 0<N) (w : ℕ → ℤ)
    {t : ℤ} (ht : ∑ k ∈ Icc 1 N, w k = 2*t) :
    ∃ a b : ℕ → ℤ, (∀ i ∈ Icc 1 N, upperDivisor N a i = if i=1 then 1 else 0) ∧
      ∀ k ∈ Icc 1 N, twoSidedCoefficient N a b k = (w k:ℝ) := by
  let v (i : ℕ) : ℤ := if i=1 then t else ∑ j ∈ Icc i N, w j
  obtain ⟨a,ha⟩ := exists_upper_endpoints N (fun i => if i=1 then 1 else 0)
  obtain ⟨b,hb⟩ := exists_upper_endpoints N v
  have h₁ : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl,hN⟩
  have hatom (i : ℕ) (hi : 0<i) : upperDivisor N a i = if i=1 then 1 else 0 := by
    rw [ha i hi]
    by_cases he : i=1
    · subst i; simp [hN]
    · simp [he]
  have hb₁ : upperDivisor N b 1 = t := by simp [hb 1 Nat.zero_lt_one,hN,v]
  refine ⟨a,b,fun i hi => hatom i (mem_Icc.mp hi).1,?_⟩
  have tails (k : ℕ) (hk : 0<k) :
      ∑ q ∈ Icc k N, twoSidedCoefficient N a b q = ∑ q ∈ Icc k N, (w q:ℝ) := by
    by_cases hcut : k≤N
    · rw [twoSidedCoefficient_tail,sum_eq_single_of_mem 1 h₁]
      · rw [Nat.mul_one,hatom 1 Nat.zero_lt_one,hatom k hk,hb₁,hb k hk,if_pos hcut]
        by_cases he : k=1
        · subst k
          simp only [if_pos rfl,Int.cast_one,one_mul,mul_one,v]
          exact_mod_cast (by omega : t+t = ∑ j ∈ Icc 1 N, w j)
        · simp [v,he]
      · intro i hi he
        have hip := (mem_Icc.mp hi).1
        have hki := Nat.le_mul_of_pos_left i hk
        simp [hatom i hip,hatom (k*i) (Nat.mul_pos hk hip),he,show k*i≠1 by omega]
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hcut)]
  intro k hk
  calc _ = _ := cell_eq_tail_sub (mem_Icc.mp hk).2 (twoSidedCoefficient N a b)
       _ = _ := by rw [tails k (mem_Icc.mp hk).1,tails (k+1) (Nat.succ_pos _)]
       _ = (w k:ℝ) := (cell_eq_tail_sub (mem_Icc.mp hk).2 (fun q => (w q:ℝ))).symm

/-- Exact integral image on positive quotient cells. -/
theorem exists_twoSidedCoefficient_iff_even (N : ℕ) (w : ℕ → ℤ) :
    (∃ a b : ℕ → ℤ, ∀ k ∈ Icc 1 N, twoSidedCoefficient N a b k = (w k:ℝ)) ↔
      Even (∑ k ∈ Icc 1 N, w k) := by
  constructor
  · rintro ⟨a,b,he⟩
    have h := twoSidedCoefficient_total N a b
    rw [sum_congr rfl he] at h
    refine ⟨∑ i ∈ Icc 1 N, upperDivisor N a i*upperDivisor N b i,?_⟩
    rw [← two_mul]
    exact_mod_cast h
  · rintro ⟨t,ht⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0,0,by simp⟩
    obtain ⟨a,b,_,he⟩ := quotient_profile_of_even_total hN w (t := t) (by rwa [two_mul])
    exact ⟨a,b,he⟩

#print axioms quotientCoefficient_tail
#print axioms twoSidedCoefficient_tail
#print axioms twoSidedCoefficient_total
#print axioms twoSidedCoefficient_difference
#print axioms quotient_profile_of_even_total
#print axioms exists_twoSidedCoefficient_iff_even
end GaloisForLFunctions.SignedArithmeticCorrespondences
