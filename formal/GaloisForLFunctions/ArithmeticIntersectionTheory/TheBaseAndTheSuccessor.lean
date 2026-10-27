import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePrimeKernelIsASumOfTransverseTowers

/-!
# The base and the successor

Over `𝔽_q` every place `v` of degree `d` acts on the one Frobenius ladder `k ∈ ℕ`: its tower couples
the lags divisible by `d`, with weight `q^{−lag/2}` (`frobeniusTower`). Two places of degrees `d, d'`
share every lag divisible by `lcm(d, d')` (`frobeniusTower_lcm_ne_zero`): the local forms overlap,
and the ladder is the base on which they are summed.

Over `ℤ` the ladders of distinct primes are transverse: the kernels `L_p` and `L_ℓ` never charge the
same pair of orders (`ladderKernel_mul_ladderKernel_eq_zero`). There is no common ladder, hence no
base on which the local forms could be compared.

The only other structure on the orders is additive. The successor `n ↦ n + 1` is transverse to every
ladder: `n` and `n + 1` lie on a common `p`-ladder only for `n = 1`, `p = 2`
(`sameLadder_succ_iff`). Every successor edge but `1 → 2` joins two different ladders — the edge
`3 → 4 = 2²` of the Catalan plaquette joins the `3`-ladder through `3` with the `2`-ladder through `1`.
Additive information is invisible to each local tower and visible only across ladders.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

/-! ### Over `ℤ`: transverse ladders -/

/-- **Distinct primes never charge the same pair of orders.** -/
theorem ladderKernel_mul_ladderKernel_eq_zero {p ℓ m n : ℕ} (hpℓ : p ≠ ℓ) (hm : m ≠ 0)
    (hn : n ≠ 0) : ladderKernel p m n * ladderKernel ℓ m n = 0 := by
  by_cases h : m ≠ n ∧ ordCompl[p] m = ordCompl[p] n
  · have h' : ¬ (m ≠ n ∧ ordCompl[ℓ] m = ordCompl[ℓ] n) := fun h' =>
      h.1 (eq_of_sameLadder_of_sameLadder hpℓ hm hn h.2 h'.2)
    simp only [ladderKernel, if_neg h', mul_zero]
  · simp only [ladderKernel, if_neg h, zero_mul]

/-! ### Over `𝔽_q`: one Frobenius ladder -/

/-- The tower of a place of degree `d` on the Frobenius ladder of a curve over `𝔽_q`: the lag
`i − j` is charged when it is a nonzero multiple of `d`, with weight `q^{−|i−j|/2}`. -/
def frobeniusTower (q : ℝ) (d i j : ℕ) : ℝ :=
  if i ≠ j ∧ d ∣ (max i j - min i j) then q ^ (-((max i j - min i j : ℕ) : ℝ) / 2) else 0

/-- **Places of a curve share lags**: two places of degrees `d, d'` both charge the pair
`(0, lcm(d, d'))`. -/
theorem frobeniusTower_lcm_ne_zero {q : ℝ} (hq : 0 < q) {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d') :
    frobeniusTower q d 0 (Nat.lcm d d') ≠ 0 ∧ frobeniusTower q d' 0 (Nat.lcm d d') ≠ 0 := by
  have hl : 0 < Nat.lcm d d' := Nat.lcm_pos hd hd'
  have hne : (0 : ℕ) ≠ Nat.lcm d d' := hl.ne
  simp only [frobeniusTower, Nat.zero_max, Nat.zero_min, Nat.sub_zero]
  refine ⟨?_, ?_⟩
  · rw [if_pos ⟨hne, Nat.dvd_lcm_left d d'⟩]; exact (Real.rpow_pos_of_pos hq _).ne'
  · rw [if_pos ⟨hne, Nat.dvd_lcm_right d d'⟩]; exact (Real.rpow_pos_of_pos hq _).ne'

/-! ### The successor -/

/-- **The successor is transverse to the ladders**: `n` and `n + 1` lie on a common `p`-ladder only
for `n = 1` and `p = 2`. -/
theorem sameLadder_succ_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    ordCompl[p] n = ordCompl[p] (n + 1) ↔ n = 1 ∧ p = 2 := by
  constructor
  · intro h
    -- on a common ladder one order divides the other
    have key : ∀ c a b : ℕ, n = c * p ^ a → n + 1 = c * p ^ b → n ∣ n + 1 ∨ n + 1 ∣ n := by
      intro c a b h1 h2
      rcases le_total a b with hle | hle
      · exact Or.inl ⟨p ^ (b - a), by rw [h2, h1, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]⟩
      · exact Or.inr ⟨p ^ (a - b), by rw [h2, h1, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]⟩
    have h2 := eq_ordCompl_mul_pow p (n + 1)
    rw [← h] at h2
    have hdiv := key _ _ _ (eq_ordCompl_mul_pow p n) h2
    have hn1 : n = 1 := by
      rcases hdiv with hd | hd
      · exact (Nat.dvd_add_right (dvd_refl n)).mp hd |> Nat.dvd_one.mp
      · exact absurd (Nat.le_of_dvd hn hd) (by omega)
    subst hn1
    refine ⟨rfl, ?_⟩
    -- `ordCompl[p] 1 = ordCompl[p] 2` forces `p = 2`
    by_contra hp2
    have h2 : ordCompl[p] 2 = 2 := by
      rw [Nat.ordCompl_eq_self_iff_zero_or_not_dvd 2 hp]
      right
      intro hpd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)
    have h1 : ordCompl[p] 1 = 1 := by simp
    rw [h1, h2] at h
    omega
  · rintro ⟨rfl, rfl⟩
    rw [show (1 + 1 : ℕ) = 2 ^ 1 by norm_num, Nat.ordCompl_self_pow Nat.prime_two]
    simp

end GaloisForLFunctions.ArithmeticIntersectionTheory
