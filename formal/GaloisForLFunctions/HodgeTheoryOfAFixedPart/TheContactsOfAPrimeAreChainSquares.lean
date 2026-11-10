import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts
import GaloisForLFunctions.RHTower.CHMDPrimeChainVariance

/-!
# Prime contacts are chain squares minus the diagonal

Two distinct positive integers meet at the prime `p` exactly when their
prime-free parts agree. Grouping a finite divisor by these parts gives
one square per prime chain, with its diagonal removed.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

/-- The contact weight supported on the positive powers of one prime. -/
def primeContactWeight (p n : ℕ) : ℝ :=
  if ∃ r : ℕ, 0 < r ∧ n = p ^ r then Real.log p else 0

theorem contactW_comm (w : ℕ → ℝ) (m n : ℕ) : contactW w m n = contactW w n m := by
  unfold contactW
  exact add_comm _ _

/-- A contact at `p` is membership in the same prime chain. -/
theorem contactW_primeContactWeight {p m n : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    contactW (primeContactWeight p) m n =
      if ordCompl[p] m = ordCompl[p] n then Real.log p else 0 := by
  classical
  wlog hlt : m < n generalizing m n
  · rw [contactW_comm]
    have hrev := this hn hm hmn.symm (lt_of_le_of_ne (not_lt.mp hlt) hmn.symm)
    simpa only [eq_comm] using hrev
  have hnd : ¬ n ∣ m := fun h => (not_le.mpr hlt) (Nat.le_of_dvd hm h)
  rw [contactW, if_neg hnd, add_zero]
  by_cases he : ordCompl[p] m = ordCompl[p] n
  · obtain ⟨r, hr, hpow⟩ := _root_.RHTower.CHMDPrimeChain.exists_pow_mul_of_same_chain hp hm hlt he
    have hdiv : m ∣ n := ⟨p ^ r, hpow⟩
    have hquot : n / m = p ^ r := by
      rw [hpow, Nat.mul_comm m, Nat.mul_div_left _ hm]
    rw [if_pos hdiv, primeContactWeight, if_pos ⟨r, hr, hquot⟩, if_pos he]
  · rw [if_neg he]
    by_cases hdiv : m ∣ n
    · rw [if_pos hdiv, primeContactWeight, if_neg]
      rintro ⟨r, _, hr⟩
      apply he
      apply _root_.RHTower.CHMDPrimeChain.same_chain_of_pow_mul hp
      calc n = (n / m) * m := (Nat.div_mul_cancel hdiv).symm
        _ = m * p ^ r := by rw [hr, Nat.mul_comm]
    · rw [if_neg hdiv]

/-- Grouping a quadratic equivalence kernel produces the squares of its fibre sums. -/
theorem sum_same_fibre_eq_sum_squares (S : Finset ℕ) (κ : ℕ → ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ S, ∑ m ∈ S, if κ m = κ n then c m * c n else 0) =
      ∑ b ∈ S.image κ, (∑ n ∈ S.filter (fun n => κ n = b), c n) ^ 2 := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := κ) (t := S.image κ)
    (fun n hn => mem_image_of_mem κ hn)]
  refine sum_congr rfl fun b _ => ?_
  have hrow : ∀ n ∈ S.filter (fun n => κ n = b),
      (∑ m ∈ S, if κ m = κ n then c m * c n else 0) =
        (∑ m ∈ S.filter (fun m => κ m = b), c m) * c n := by
    intro n hn
    rw [(mem_filter.mp hn).2, ← sum_filter, sum_mul]
  rw [sum_congr rfl hrow, ← mul_sum, pow_two]

/-- The exact contact form of a prime: chain squares minus the omitted diagonal. -/
theorem prime_contact_form_eq_chain_squares (S : Finset ℕ) (c : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contactW (primeContactWeight p) m n) =
      Real.log p *
        ((∑ b ∈ S.image (fun n => ordCompl[p] n),
          (∑ n ∈ S.filter (fun n => ordCompl[p] n = b), c n) ^ 2) - ∑ n ∈ S, c n ^ 2) := by
  classical
  rw [← sum_same_fibre_eq_sum_squares, mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  rw [← sum_erase_add S (fun m => if ordCompl[p] m = ordCompl[p] n then c m * c n else 0) hn]
  simp only [if_true, mul_add]
  have hrow : ∀ m ∈ S.erase n,
      c m * c n * contactW (primeContactWeight p) m n =
        Real.log p * (if ordCompl[p] m = ordCompl[p] n then c m * c n else 0) := by
    intro m hm
    rw [contactW_primeContactWeight hp (hS m (mem_of_mem_erase hm)) (hS n hn)
      (ne_of_mem_erase hm)]
    split_ifs <;> ring
  rw [sum_congr rfl hrow, ← mul_sum]
  ring

#print axioms contactW_primeContactWeight
#print axioms prime_contact_form_eq_chain_squares

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
