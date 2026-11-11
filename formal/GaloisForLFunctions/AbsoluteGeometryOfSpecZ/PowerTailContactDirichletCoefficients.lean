import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheCombOfUnitMassesFixesTheContacts

/-!
# The arithmetic coefficients of power comb tails

For coefficients `n⁻ᵃ`, the contact form is twice the summatory function
of `n⁻²ᵃ ∑_{d∣n} Λ(d)dᵃ`. Separating these coefficients from the polar
and archimedean terms retains the literal finite comb, including its
diagonal counterterm.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart

/-- Unscaled coefficients of a power tail. -/
def powerTailWeight (a : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-a)

/-- The divisor coefficient exposed by the contacts of a power tail. -/
def powerTailContactCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  powerTailWeight (2 * a) n * ∑ d ∈ n.divisors, (d : ℝ) ^ a * Λ d

private theorem powerTailWeight_mul_of_dvd (a : ℝ) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hd : m ∣ n) :
    powerTailWeight a m * powerTailWeight a n =
      powerTailWeight (2 * a) n * ((n / m : ℕ) : ℝ) ^ a := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by omega)
  have hkR : (0 : ℝ) < (n / m : ℕ) := by exact_mod_cast hk
  have hprod : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hw : (m : ℝ) ^ (-a) = (n : ℝ) ^ (-a) * ((n / m : ℕ) : ℝ) ^ a := by
    rw [hprod, Real.mul_rpow hmR.le hkR.le, mul_assoc,
      ← Real.rpow_add hkR, neg_add_cancel, Real.rpow_zero, mul_one]
  unfold powerTailWeight
  rw [hw]
  calc
    _ = ((n : ℝ) ^ (-a) * (n : ℝ) ^ (-a)) * ((n / m : ℕ) : ℝ) ^ a := by ring
    _ = _ := by rw [← Real.rpow_add hnR]; congr 2 <;> ring

private theorem sum_dvd_Icc_two_eq_divisors {n N : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ N) (v : ℕ → ℝ) (hv : v 1 = 0) :
    (∑ d ∈ Icc 2 N, if d ∣ n then v d else 0) = ∑ d ∈ n.divisors, v d := by
  have hfilter : (Icc 2 N).filter (· ∣ n) = n.divisors.erase 1 := by
    ext d
    simp only [mem_filter, mem_erase, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hdn⟩
      exact ⟨by omega, hdn, by omega⟩
    · rintro ⟨hd1, hdn, _⟩
      have hd0 := Nat.pos_of_dvd_of_pos hdn (by omega : 0 < n)
      exact ⟨⟨by omega, (Nat.le_of_dvd (by omega) hdn).trans hN⟩, hdn⟩
  rw [← sum_filter, hfilter]
  exact Finset.sum_erase _ hv

/-- Every downward contact row is the weighted divisor coefficient. -/
theorem sum_powerTail_down_contacts (a : ℝ) {n N : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ N) :
    (∑ m ∈ (Icc 1 N).erase n, powerTailWeight a m * powerTailWeight a n *
      (if m ∣ n then (Λ (n / m) : ℝ) else 0)) = powerTailContactCoefficient a n := by
  have hrow : (∑ m ∈ (Icc 1 N).erase n,
      powerTailWeight a m * powerTailWeight a n *
        (if m ∣ n then (Λ (n / m) : ℝ) else 0)) =
      ∑ m ∈ (Icc 1 N).erase n, if m ∣ n then
        powerTailWeight (2 * a) n * (((n / m : ℕ) : ℝ) ^ a * Λ (n / m)) else 0 := by
    apply sum_congr rfl
    intro m hm
    by_cases hd : m ∣ n
    · rw [if_pos hd, if_pos hd,
        powerTailWeight_mul_of_dvd a (mem_Icc.mp (mem_of_mem_erase hm)).1 hn hd]
      ring
    · rw [if_neg hd, if_neg hd, mul_zero]
  rw [hrow, sum_ite_dvd_erase hn hN
    (fun d => powerTailWeight (2 * a) n * ((d : ℝ) ^ a * Λ d))]
  rw [sum_dvd_Icc_two_eq_divisors hn hN
    (fun d => powerTailWeight (2 * a) n * ((d : ℝ) ^ a * Λ d)) (by simp)]
  exact (Finset.mul_sum _ _ _).symm

/-- Symmetry counts each downward contact twice. -/
theorem sum_weighted_contacts_eq_two_down (S : Finset ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * contact m n) =
      2 * ∑ n ∈ S, ∑ m ∈ S.erase n,
        c m * c n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) := by
  have hswap : (∑ n ∈ S, ∑ m ∈ S.erase n,
      c m * c n * (if n ∣ m then (Λ (m / n) : ℝ) else 0)) =
      ∑ n ∈ S, ∑ m ∈ S.erase n,
        c m * c n * (if m ∣ n then (Λ (n / m) : ℝ) else 0) := by
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (by
      intro n m
      simp only [mem_erase]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩)]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    ring
  simp only [contact, mul_add, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- Exact arithmetic contact sum of the literal power-tail comb. -/
theorem sum_powerTail_contacts (a : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      powerTailWeight a m * powerTailWeight a n * contact m n) =
      2 * ∑ n ∈ Icc 1 N, powerTailContactCoefficient a n := by
  rw [sum_weighted_contacts_eq_two_down]
  congr 1
  exact sum_congr rfl fun n hn =>
    sum_powerTail_down_contacts a (mem_Icc.mp hn).1 (mem_Icc.mp hn).2

/-- Jets and diagonal counterterm of the unscaled power tail. -/
def powerTailArchimedean (a : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 * counterterm n) -
    ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      powerTailWeight a m * powerTailWeight a n * jetKernel m n

/-- The entire comb splits into pole degrees, the archimedean term,
and the explicit weighted divisor sum. -/
theorem combForm_powerTailWeight_eq (a : ℝ) (N : ℕ) :
    HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a) =
      2 * (degOne (Icc 1 N) (powerTailWeight a) * degTwo (Icc 1 N) (powerTailWeight a)) +
        powerTailArchimedean a N - 2 * ∑ n ∈ Icc 1 N, powerTailContactCoefficient a n := by
  simp only [HodgeTheoryOfAFixedPart.combForm, HodgeTheoryOfAFixedPart.combPairing,
    HodgeTheoryOfAFixedPart.pairKernel,
    mul_add, Finset.sum_add_distrib]
  rw [sum_powerTail_contacts]
  unfold powerTailArchimedean
  ring

/-- Power-tail comb form per degree point. For positive `N`, homogeneity
identifies this with coefficients `(N/n)^a` divided by `N`. -/
def powerCombTail (a : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * a - 1) * HodgeTheoryOfAFixedPart.combForm (Icc 1 N) (powerTailWeight a)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
