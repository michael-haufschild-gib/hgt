import GaloisForLFunctions.RHTower.WeilKloostermanLFunction

/-!
# The Frobenius is a factorial stencil

Over `𝔽_q[T]` the factorial is Carlitz's `D_n = ∏_{f monic, deg f = n} f`, and `T^{q^n} − T` is the
ratio `D_n / D_{n−1}^q`. This is the factorial stencil of the two-term Dirichlet polynomial
`1 − q X`, the exact inverse of the zeta function of `𝔽_q[T]`. Its ledger can be read without using
`x^q` at all.

* **Size.** `deg D_n − q deg D_{n−1} = n q^n − q (n − 1) q^{n−1} = q^n`, the exact main term.
* **Multiplicity.** An irreducible `P` of degree `e` occurs in the ratio with order exactly `1` if
  `e ∣ n` and `0` otherwise.
* **Ledger.** `Σ_{e ∣ n} e π(e) = q^n`, with no error term: the rate of this stencil is `0`.

This is the answer in the function field to "what replaces Frobenius?". Over `𝔽_q` the inverse of the
zeta function is a polynomial, and norms are quantized, so a stencil is only ever cut at a degree
boundary and there is no sawtooth. Over `ℤ` the inverse of `ζ` is an infinite Dirichlet series, every
integer is a cut, and the rate is at least `c / (√K (1 + log K))`.
-/

open Polynomial Finset
open GaloisForLFunctions.RHTower.WeilKloosterman

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

attribute [local instance] Classical.propDecidable

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The degree of the Carlitz factorial `D_n`. -/
def carlitzSize (n : ℕ) : ℂ := ∑ f ∈ monicDeg (F := F) n, (f.natDegree : ℂ)

variable {F}

/-- The order of `P` in the Carlitz factorial, with prime powers truncated at `N`. -/
def carlitzOrder (P : F[X]) (n N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, ∑ _f ∈ (monicDeg (F := F) n).filter (fun f => P ^ k ∣ f), (1 : ℂ)

variable (F) in
theorem carlitzSize_eq (n : ℕ) : carlitzSize F n = (n : ℂ) * (Fintype.card F : ℂ) ^ n := by
  have hterm : ∀ f ∈ monicDeg (F := F) n, (f.natDegree : ℂ) = (n : ℂ) := fun f hf => by
    rw [(mem_monicDeg.mp hf).2]
  rw [carlitzSize, sum_congr rfl hterm, sum_const, card_monicDeg, nsmul_eq_mul]
  push_cast
  ring

/-- Counting multiples of `P^k` of degree `n`. -/
theorem sum_filter_pow_dvd {P : F[X]} (hP : P.Monic) (k n : ℕ) :
    ∑ _f ∈ (monicDeg (F := F) n).filter (fun f => P ^ k ∣ f), (1 : ℂ) =
      if k * P.natDegree ≤ n then (Fintype.card F : ℂ) ^ (n - k * P.natDegree) else 0 := by
  have h := sum_dvd_monicDeg (F := F) (fun _ => (1 : ℂ)) (fun _ _ _ _ => (mul_one 1).symm) hP k n
  rw [h]
  split_ifs
  · rw [degSumW, sum_const, card_monicDeg, nsmul_eq_mul, mul_one, one_mul]
    push_cast
    rfl
  · rfl

/-- **The multiplicity of the stencil `1 − qX`.** For `P` monic of degree `e ≥ 1`, the order of `P`
in `D_{n+1} / D_n^q` is `1` if `e ∣ n + 1` and `0` otherwise. -/
theorem carlitzOrder_sub {P : F[X]} (hP : P.Monic) (he : 1 ≤ P.natDegree) {n N : ℕ}
    (hN : n + 1 ≤ N) :
    carlitzOrder P (n + 1) N - (Fintype.card F : ℂ) * carlitzOrder P n N =
      if P.natDegree ∣ n + 1 then 1 else 0 := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [carlitzOrder, carlitzOrder, mul_sum, ← sum_sub_distrib]
  have hterm : ∀ k ∈ Icc 1 N,
      ∑ _f ∈ (monicDeg (F := F) (n + 1)).filter (fun f => P ^ k ∣ f), (1 : ℂ) -
        (Fintype.card F : ℂ) * ∑ _f ∈ (monicDeg (F := F) n).filter (fun f => P ^ k ∣ f), (1 : ℂ) =
      if k * P.natDegree = n + 1 then 1 else 0 := by
    intro k _
    rw [sum_filter_pow_dvd hP, sum_filter_pow_dvd hP]
    by_cases h1 : k * P.natDegree = n + 1
    · rw [if_pos (by omega), if_neg (by omega), if_pos h1, mul_zero, sub_zero, h1, Nat.sub_self,
        pow_zero]
    · rw [if_neg h1]
      by_cases h2 : k * P.natDegree ≤ n
      · rw [if_pos (by omega), if_pos h2, show n + 1 - k * P.natDegree =
          (n - k * P.natDegree) + 1 by omega, pow_succ, mul_comm, sub_self]
      · rw [if_neg (by omega), if_neg h2, mul_zero, sub_zero]
  rw [sum_congr rfl hterm]
  by_cases hd : P.natDegree ∣ n + 1
  · obtain ⟨k₀, hk₀⟩ := hd
    have hk0 : 1 ≤ k₀ := by
      rcases Nat.eq_zero_or_pos k₀ with rfl | h
      · omega
      · exact h
    have hk1 : k₀ ≤ N := by
      have : k₀ ≤ P.natDegree * k₀ := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [if_pos ⟨k₀, hk₀⟩, sum_eq_single k₀]
    · rw [if_pos (by rw [hk₀, mul_comm])]
    · intro k _ hne
      rw [if_neg]
      intro h
      apply hne
      have hmul : P.natDegree * k = P.natDegree * k₀ := by rw [mul_comm, h, hk₀]
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
    · intro h
      exact absurd (mem_Icc.mpr ⟨hk0, hk1⟩) h
  · rw [if_neg hd]
    refine sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro h
    exact hd ⟨k, by rw [← h, mul_comm]⟩

/-- **The size of the Carlitz factorial is the sum of its orders.** -/
theorem carlitzSize_eq_sum_order {n N : ℕ} (hN : n ≤ N) :
    carlitzSize F n = ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, (d : ℂ) * carlitzOrder P n N := by
  have hexp : ∀ f ∈ monicDeg (F := F) n, (f.natDegree : ℂ) =
      ∑ d ∈ Icc 1 N, ∑ P ∈ irrDeg (F := F) d, ∑ k ∈ Icc 1 N, if P ^ k ∣ f then (d : ℂ) else 0 := by
    intro f hf
    obtain ⟨hm, hd⟩ := mem_monicDeg.mp hf
    exact natDegree_eq_sum_irr hm (by omega)
  rw [carlitzSize, sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_comm, carlitzOrder, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum, sum_ite, sum_const_zero, add_zero]
  exact sum_congr rfl fun _ _ => (mul_one _).symm

/-- **The ledger of the stencil `1 − qX` is exact.** `q^{n+1} = Σ_{e ∣ n+1} e π(e)`, derived from the
sizes and multiplicities of Carlitz factorials alone. -/
theorem card_pow_eq_sum_irrDeg (n : ℕ) :
    (Fintype.card F : ℂ) ^ (n + 1) =
      ∑ e ∈ Icc 1 (n + 1), ∑ _P ∈ irrDeg (F := F) e, if e ∣ n + 1 then (e : ℂ) else 0 := by
  have h1 := carlitzSize_eq_sum_order (F := F) (n := n + 1) (N := n + 1) le_rfl
  have h2 := carlitzSize_eq_sum_order (F := F) (n := n) (N := n + 1) (Nat.le_succ n)
  have hsize : carlitzSize F (n + 1) - (Fintype.card F : ℂ) * carlitzSize F n =
      (Fintype.card F : ℂ) ^ (n + 1) := by
    rw [carlitzSize_eq, carlitzSize_eq]
    push_cast
    ring
  rw [← hsize, h1, h2, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun P hP => ?_
  obtain ⟨hm, hd, _⟩ := mem_irrDeg.mp hP
  have he1 : 1 ≤ P.natDegree := by
    rw [hd]
    exact (mem_Icc.mp he).1
  have hsub := carlitzOrder_sub hm he1 (N := n + 1) (n := n) le_rfl
  rw [hd] at hsub
  calc (e : ℂ) * carlitzOrder P (n + 1) (n + 1) -
        (Fintype.card F : ℂ) * ((e : ℂ) * carlitzOrder P n (n + 1))
      = (e : ℂ) * (carlitzOrder P (n + 1) (n + 1) -
          (Fintype.card F : ℂ) * carlitzOrder P n (n + 1)) := by ring
    _ = _ := by
        rw [hsub]
        split_ifs <;> simp

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
