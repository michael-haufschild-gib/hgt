import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import GaloisForLFunctions.RHTower.MobiusHaarRamareCoprimalityBudget

/-!
# Source-faithful Haar–Ramaré factorization

This leaf reindexes the literal odd-Möbius Haar sum by a chosen prime factor.
Every nonzero squarefree source term is divided by its number of distinct prime
factors, so the full source is counted exactly once.  After `n = p*m`, the
cofactor has sign `-μ(m)` and normalization `1/(ω(m)+1)` when `p ∤ m`;
the `p ∣ m` contribution vanishes because `p*m` is squareful.  The final theorem
has no analytic cancellation premise.  Bounding its coupled signed sum at
square-root scale remains the open arithmetic producer.

The proof is kept on small mathlib imports: importing the existing analytic
Ramaré stack into a scratch check consumed excessive memory for this finite
identity.
-/

open Finset

namespace RHTower

private theorem mobius_prime_mul_real {p m : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.moebius (p * m) : ℤ) : ℝ) =
      if p ∣ m then 0 else -((ArithmeticFunction.moebius m : ℤ) : ℝ) := by
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    obtain ⟨k, rfl⟩ := hpm
    have hnsf : ¬ Squarefree (p * (p * k)) := by
      intro hsf
      have hdvd : p * p ∣ p * (p * k) := ⟨k, by ring⟩
      have hone : p = 1 := Nat.isUnit_iff.1 (hsf p hdvd)
      exact hp.one_lt.ne' hone
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
    norm_num
  · rw [if_neg hpm]
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring

private theorem prime_mul_factor_card {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (p * m).primeFactors.card = m.primeFactors.card + 1 := by
  have hm0 : m ≠ 0 := by intro h; subst m; exact hpm (dvd_zero p)
  have hnot : p ∉ m.primeFactors := by
    intro h
    exact hpm (Nat.dvd_of_mem_primeFactors h)
  have hd : Disjoint ({p} : Finset ℕ) m.primeFactors := by
    simp [hnot]
  rw [Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors,
    Finset.card_union_of_disjoint hd]
  simp [Nat.add_comm]

private theorem sum_div_image_real (p : ℕ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, p ∣ n) (g : ℕ → ℝ) :
    ∑ m ∈ T.image (fun n => n / p), g (p * m) = ∑ n ∈ T, g n := by
  classical
  have hinj : ∀ x ∈ T, ∀ y ∈ T, x / p = y / p → x = y := by
    intro x hx y hy hxy
    have h1 : p * (x / p) = x := Nat.mul_div_cancel' (hT x hx)
    have h2 : p * (y / p) = y := Nat.mul_div_cancel' (hT y hy)
    rw [← h1, ← h2, hxy]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Nat.mul_div_cancel' (hT n hn)]

theorem mobius_ramare_full_prime_cofactor (P S : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, 1 < n)
    (hcover : ∀ n ∈ S, n.primeFactors ⊆ P) :
    ∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n =
      ∑ p ∈ P, ∑ m ∈ (S.filter (fun n => p ∣ n)).image (fun n => n / p),
        if p ∣ m then 0 else
          -((ArithmeticFunction.moebius m : ℤ) : ℝ) * w (p * m) /
            ((m.primeFactors.card : ℝ) + 1) := by
  classical
  have hfac (n : ℕ) (hn : n ∈ S) :
      P.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpn⟩
      exact Nat.mem_primeFactors.mpr ⟨hP p hp, hpn, by have := hS n hn; omega⟩
    · intro hp
      exact ⟨hcover n hn hp, Nat.dvd_of_mem_primeFactors hp⟩
  have hcard (n : ℕ) (hn : n ∈ S) : (n.primeFactors.card : ℝ) ≠ 0 := by
    have : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (hS n hn)
    exact_mod_cast (Finset.card_pos.mpr this).ne'
  have hone (n : ℕ) (hn : n ∈ S) :
      (∑ p ∈ P, if p ∣ n then
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n / (n.primeFactors.card : ℝ)
        else 0) = ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n := by
    rw [← Finset.sum_filter, hfac n hn, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard n hn]
  calc
    (∑ n ∈ S, ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n)
        = ∑ n ∈ S, ∑ p ∈ P, if p ∣ n then
            ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n /
              (n.primeFactors.card : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          exact (hone n hn).symm
    _ = ∑ p ∈ P, ∑ n ∈ S, if p ∣ n then
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n /
            (n.primeFactors.card : ℝ) else 0 := Finset.sum_comm
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (fun n => p ∣ n),
          ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n /
            (n.primeFactors.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ m ∈ (S.filter (fun n => p ∣ n)).image (fun n => n / p),
          ((ArithmeticFunction.moebius (p * m) : ℤ) : ℝ) * w (p * m) /
            ((p * m).primeFactors.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          symm
          exact sum_div_image_real p (S.filter (fun n => p ∣ n))
            (fun n hn => (Finset.mem_filter.mp hn).2)
            (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ) * w n /
              (n.primeFactors.card : ℝ))
    _ = _ := by
          apply Finset.sum_congr rfl
          intro p hpP
          apply Finset.sum_congr rfl
          intro m hm
          have hp := hP p hpP
          rw [mobius_prime_mul_real hp]
          by_cases hpm : p ∣ m
          · simp [hpm]
          · simp only [if_neg hpm]
            rw [prime_mul_factor_card hp hpm]
            push_cast
            ring

/-- Odd source indices from `2` through the cutoff. -/
def oddHaarSourceSet (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Y).filter Odd

/-- Ambient prime packet through `Y`; the odd source gives prime `2` zero incidence. -/
def oddHaarPrimeSet (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Y).filter Nat.Prime

theorem oddHaarSource_factor_cover (Y : ℕ) (n : ℕ)
    (hn : n ∈ oddHaarSourceSet Y) :
    n.primeFactors ⊆ oddHaarPrimeSet Y := by
  intro p hp
  have hnY : n ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_le : p ≤ n := Nat.le_of_mem_primeFactors hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hpprime.two_le, hp_le.trans hnY⟩, hpprime⟩

/-- Unconditional finite prime–cofactor factorization of the literal odd-Möbius Haar source. -/
theorem oddHaarSource_eq_ramare_cofactor (Y : ℕ) :
    ∑ n ∈ oddHaarSourceSet Y,
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) * haarWeight Y n =
      ∑ p ∈ oddHaarPrimeSet Y,
        ∑ m ∈ ((oddHaarSourceSet Y).filter (fun n => p ∣ n)).image (fun n => n / p),
          if p ∣ m then 0 else
            -((ArithmeticFunction.moebius m : ℤ) : ℝ) * haarWeight Y (p * m) /
              ((m.primeFactors.card : ℝ) + 1) := by
  apply mobius_ramare_full_prime_cofactor
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  · intro n hn
    exact oddHaarSource_factor_cover Y n hn

end RHTower
