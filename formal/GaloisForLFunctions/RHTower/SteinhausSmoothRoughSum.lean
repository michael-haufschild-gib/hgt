import GaloisForLFunctions.RHTower.SteinhausSmoothRoughSplit
import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment

open scoped BigOperators

noncomputable section
namespace RHTower
open SteinhausModel

/-- Multiplication reindexes every finite arithmetic sum by its literal smooth and rough factors. -/
theorem sum_Icc_eq_smoothRough_sum (y N : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, F n) =
      ∑ b ∈ (Finset.Icc 1 N).filter (fun b => ∀ p ∈ Nat.primesBelow y, ¬p ∣ b),
        ∑ a ∈ Nat.smoothNumbersUpTo N y, if a * b ≤ N then F (a * b) else 0 := by
  classical
  let R := (Finset.Icc 1 N).filter (fun b => ∀ p ∈ Nat.primesBelow y, ¬p ∣ b)
  let A := Nat.smoothNumbersUpTo N y
  let T := (R.product A).filter (fun ba => ba.2 * ba.1 ≤ N)
  have hsum : (∑ ba ∈ T, F (ba.2 * ba.1)) = ∑ n ∈ Finset.Icc 1 N, F n := by
    apply Finset.sum_bij (fun ba _ => ba.2 * ba.1)
    · intro ba hba
      rcases Finset.mem_filter.mp hba with ⟨hba, hN⟩
      rcases Finset.mem_product.mp hba with ⟨hb, ha⟩
      have hb1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      have ha1 := Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp ha).2
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Nat.pos_of_ne_zero ha1) hb1, hN⟩
    · intro ba hba cd hcd heq
      rcases Finset.mem_filter.mp hba with ⟨hba, _⟩
      rcases Finset.mem_filter.mp hcd with ⟨hcd, _⟩
      rcases Finset.mem_product.mp hba with ⟨hb, ha⟩
      rcases Finset.mem_product.mp hcd with ⟨hd, hc⟩
      have hb' := Finset.mem_filter.mp hb
      have hd' := Finset.mem_filter.mp hd
      have h := smooth_rough_pair_unique (Nat.mem_smoothNumbersUpTo.mp ha).2
        (by have := (Finset.mem_Icc.mp hb'.1).1; omega) hb'.2
        (Nat.mem_smoothNumbersUpTo.mp hc).2
        (by have := (Finset.mem_Icc.mp hd'.1).1; omega) hd'.2 heq
      exact Prod.ext h.2 h.1
    · intro n hn
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnN := (Finset.mem_Icc.mp hn).2
      let a := Sieve.smoothPart (y - 1) n
      let b := Sieve.roughPart (y - 1) n
      have hprod : a * b = n := Sieve.smoothPart_mul_roughPart (by omega) (y - 1)
      have ha : a ∈ A := Nat.mem_smoothNumbersUpTo.mpr
        ⟨(Nat.le_of_dvd hn1 (Sieve.smoothPart_dvd _ _)).trans hnN,
          sieveSmoothPart_mem_smoothNumbers y n⟩
      have hb : b ∈ R := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Sieve.roughPart_pos _ _,
          (Nat.le_of_dvd hn1 (Sieve.roughPart_dvd _ _)).trans hnN⟩,
          fun p hp => not_dvd_sieveRoughPart y n hp⟩
      refine ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, ?_⟩, hprod⟩
      simpa only [hprod] using hnN
    · intro ba _
      rfl
  rw [← hsum]
  change (∑ ba ∈ (R.product A).filter (fun ba => ba.2 * ba.1 ≤ N), F (ba.2 * ba.1)) = _
  rw [Finset.sum_filter]
  exact Finset.sum_product R A (fun ba : ℕ × ℕ => if ba.2 * ba.1 ≤ N then F (ba.2 * ba.1) else 0)

/-- A smooth character only reads the retained prefix. -/
theorem X_freezeSteinhausPrefix_of_smooth {y a : ℕ} (ha : a ∈ Nat.smoothNumbers y)
    (ω η : Omega) : X a (freezeSteinhausPrefix (Nat.primesBelow y) ω η) = X a ω := by
  have hsum : (∑ p ∈ a.primeFactors, (a.factorization p : ℝ) *
      freezeSteinhausPrefix (Nat.primesBelow y) ω η p) =
      ∑ p ∈ a.primeFactors, (a.factorization p : ℝ) * ω p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [freezeSteinhausPrefix, if_pos ((Nat.mem_smoothNumbers_iff_primeFactors_subset.mp ha).2 hp)]
  simp only [X, hsum]

/-- A rough character only reads the independent exterior sample. -/
theorem X_freezeSteinhausPrefix_of_rough {y b : ℕ}
    (hr : ∀ p ∈ Nat.primesBelow y, ¬p ∣ b) (ω η : Omega) :
    X b (freezeSteinhausPrefix (Nat.primesBelow y) ω η) = X b η := by
  have hsum : (∑ p ∈ b.primeFactors, (b.factorization p : ℝ) *
      freezeSteinhausPrefix (Nat.primesBelow y) ω η p) =
      ∑ p ∈ b.primeFactors, (b.factorization p : ℝ) * η p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hnot : p ∉ Nat.primesBelow y := fun hmem => hr p hmem (Nat.dvd_of_mem_primeFactors hp)
    rw [freezeSteinhausPrefix, if_neg hnot]
  simp only [X, hsum]

/-- The literal summatory polynomial separates into rough random characters with smooth coefficients. -/
theorem steinhausSummatory_frozenPrefix_eq_smoothRough (y N : ℕ) (ω η : Omega) :
    (∑ n ∈ Finset.Icc 1 N, X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)) =
      ∑ b ∈ (Finset.Icc 1 N).filter (fun b => ∀ p ∈ Nat.primesBelow y, ¬p ∣ b),
        X b η * ∑ a ∈ Nat.smoothNumbersUpTo N y, if a * b ≤ N then X a ω else 0 := by
  classical
  rw [sum_Icc_eq_smoothRough_sum y N]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_filter.mp hb
  have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb'.1).1; omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := (Nat.mem_smoothNumbersUpTo.mp ha).2
  by_cases h : a * b ≤ N
  · simp only [h, if_true, X_mul (Nat.ne_zero_of_mem_smoothNumbers ha') hb0,
      X_freezeSteinhausPrefix_of_smooth ha', X_freezeSteinhausPrefix_of_rough hb'.2]
    exact mul_comm _ _
  · simp only [h, if_false, mul_zero]

/-- Exact frozen-prefix variance, grouped by the literal rough integer rather than an abstract index. -/
theorem integral_normSq_steinhausSummatory_frozenPrefix_eq_rough (y N : ℕ) (ω : Omega) :
    (∫ η, ‖∑ n ∈ Finset.Icc 1 N,
      X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ) ∂steinhausMeasure) =
      ∑ b ∈ (Finset.Icc 1 N).filter (fun b => ∀ p ∈ Nat.primesBelow y, ¬p ∣ b),
        ‖∑ a ∈ Nat.smoothNumbersUpTo N y, if a * b ≤ N then X a ω else 0‖ ^ (2 : ℕ) := by
  classical
  have h := integral_normSq_dpoly_complex
    (fun b => ∑ a ∈ Nat.smoothNumbersUpTo N y, if a * b ≤ N then X a ω else 0)
    ((Finset.Icc 1 N).filter (fun b => ∀ p ∈ Nat.primesBelow y, ¬p ∣ b))
    (fun b hb => by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1; omega)
  simpa only [steinhausSummatory_frozenPrefix_eq_smoothRough, mul_comm] using h

end RHTower
