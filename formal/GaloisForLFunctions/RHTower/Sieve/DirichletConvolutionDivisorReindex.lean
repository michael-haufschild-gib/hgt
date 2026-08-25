import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

open Finset

noncomputable section

namespace RHTower.Sieve

/-- Extend a zero-based finite coefficient vector to positive natural indices. -/
def finCoeffNat (N : ℕ) (a : Fin N → ℂ) (n : ℕ) : ℂ :=
  if h : 1 ≤ n ∧ n ≤ N then a ⟨n - 1, by omega⟩ else 0

@[simp] theorem finCoeffNat_succ (N : ℕ) (a : Fin N → ℂ) (n : Fin N) :
    finCoeffNat N a ((n : ℕ) + 1) = a n := by
  rw [finCoeffNat, dif_pos]
  · congr 1
  · exact ⟨by omega, n.isLt⟩

/-- A multiplicative convolution fibre is the standard divisor convolution
of the positive-natural coefficient extensions. -/
theorem dirConv_eq_sum_divisors_finCoeffNat
    (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ) (r : Fin (N * M)) :
    dirConv N M a b r =
      ∑ d ∈ ((r : ℕ) + 1).divisors,
        finCoeffNat N a d * finCoeffNat M b (((r : ℕ) + 1) / d) := by
  classical
  let K : ℕ := (r : ℕ) + 1
  let D : Finset ℕ := K.divisors.filter (fun d => d ≤ N ∧ K / d ≤ M)
  have hK : 0 < K := by dsimp only [K]; omega
  have hrestrict :
      (∑ d ∈ K.divisors,
          finCoeffNat N a d * finCoeffNat M b (K / d)) =
        ∑ d ∈ D, finCoeffNat N a d * finCoeffNat M b (K / d) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hddiv hdnot
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hddiv
    have hqpos : 1 ≤ K / d := by
      have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hddiv
      exact Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    simp only [Finset.mem_filter, hddiv, true_and] at hdnot
    rcases not_and_or.mp hdnot with hdN | hqM
    · have hz : finCoeffNat N a d = 0 := by
        rw [finCoeffNat, dif_neg (fun h => hdN h.2)]
      rw [hz, zero_mul]
    · have hz : finCoeffNat M b (K / d) = 0 := by
        rw [finCoeffNat, dif_neg (fun h => hqM h.2)]
      rw [hz, mul_zero]
  rw [show ((r : ℕ) + 1) = K by rfl, hrestrict]
  rw [dirConv]
  symm
  let i : (d : ℕ) → d ∈ D → Fin N × Fin M := fun d hd =>
    ⟨⟨d - 1, by
        have hv := (Finset.mem_filter.mp hd).2.1
        have hp : 1 ≤ d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
        omega⟩,
      ⟨K / d - 1, by
        have hv := (Finset.mem_filter.mp hd).2.2
        have hp : 1 ≤ K / d := by
          have hdvd : d ∣ K := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
          exact Nat.one_le_div_iff (Nat.pos_of_mem_divisors
            (Finset.mem_filter.mp hd).1) |>.2 (Nat.le_of_dvd hK hdvd)
        omega⟩⟩
  apply Finset.sum_bij i
  · intro d hd
    have hdmem := Finset.mem_filter.mp hd
    have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hdmem.1
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdmem.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [i]
    rw [Nat.sub_add_cancel hdpos]
    have hqpos : 1 ≤ K / d :=
      Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    rw [Nat.sub_add_cancel hqpos, Nat.mul_div_cancel' hdvd]
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 : 1 ≤ d₁ := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd₁).1
    have h2 : 1 ≤ d₂ := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd₂).1
    have hv := congrArg (fun q : Fin N × Fin M => q.1.val) heq
    dsimp only [i] at hv
    omega
  · intro q hq
    have hqmem := Finset.mem_filter.mp hq
    let d : ℕ := q.1.val + 1
    have hdpos : 1 ≤ d := by dsimp only [d]; omega
    have hprod : d * (q.2.val + 1) = K := by
      dsimp only [d, K]
      exact hqmem.2
    have hdvd : d ∣ K := ⟨q.2.val + 1, hprod.symm⟩
    have hquot : K / d = q.2.val + 1 := by
      calc
        K / d = (d * (q.2.val + 1)) / d := by rw [hprod]
        _ = q.2.val + 1 := Nat.mul_div_cancel_left _ (by omega)
    have hdD : d ∈ D := by
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨hdvd, by omega⟩, ?_⟩
      constructor
      · dsimp only [d]
        exact q.1.isLt
      · rw [hquot]
        exact q.2.isLt
    refine ⟨d, hdD, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      dsimp only [i, d]
      omega
    · apply Fin.ext
      dsimp only [i]
      rw [hquot]
      omega
  · intro d hd
    have hdmem := Finset.mem_filter.mp hd
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdmem.1
    have hdN := hdmem.2.1
    have hqM := hdmem.2.2
    have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hdmem.1
    have hqpos : 1 ≤ K / d :=
      Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    change finCoeffNat N a d * finCoeffNat M b (K / d) =
      a (i d hd).1 * b (i d hd).2
    rw [finCoeffNat, dif_pos ⟨hdpos, hdN⟩,
      finCoeffNat, dif_pos ⟨hqpos, hqM⟩]

end RHTower.Sieve
