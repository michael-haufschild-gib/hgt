import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

/-!
# Independence of the divided principal parts at distinct roots

For distinct points `r i` with multiplicities `m i`, the divided principal parts of
`∏ (X - r i)^(m i)` are the polynomials

`B i p = (X - r i)^(m i - p) · ∏_{l ≠ i} (X - r l)^(m l)`,  `1 ≤ p ≤ m i`,

that is, `A/(X - r i)^p` written without division.  They are linearly independent: at the root
`r i` the term of largest divided order has the lowest order of vanishing, and every other term
vanishes to one order more, so its coefficient is forced to zero.

This is the algebraic content of "the rational principal parts are independent", which converts one
null state with repeated roots into a lower bound on the dimension of a radical.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- The divided principal part of order `p` at the root `r i`, written without division. -/
def dividedPart (r : Fin k → ℝ) (m : Fin k → ℕ) (i : Fin k) (p : ℕ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (r i)) ^ (m i - p) *
    ∏ l ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (r l)) ^ (m l)

/-- Every other divided part vanishes at `r i₀` to order at least `m i₀ - p₀ + 1`. -/
theorem pow_dvd_dividedPart_of_ne (r : Fin k → ℝ) (m : Fin k → ℕ) {i₀ : Fin k} {p₀ : ℕ}
    (hp₀ : 1 ≤ p₀) {i : Fin k} {p : ℕ} (h : i ≠ i₀ ∨ (i = i₀ ∧ p < p₀)) :
    ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - p₀ + 1)) ∣ dividedPart r m i p := by
  classical
  rcases h with hne | ⟨hi, hlt⟩
  · refine Dvd.dvd.mul_left ?_ _
    have hmem : i₀ ∈ Finset.univ.erase i :=
      Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ i₀⟩
    refine dvd_trans (pow_dvd_pow _ (by omega)) (Finset.dvd_prod_of_mem _ hmem)
  · subst hi
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- The product over the other roots does not vanish at `r i₀`. -/
theorem eval_prod_erase_ne_zero {r : Fin k → ℝ} (hr : Function.Injective r) (m : Fin k → ℕ)
    (i₀ : Fin k) :
    (∏ l ∈ Finset.univ.erase i₀, (Polynomial.X - Polynomial.C (r l)) ^ (m l)).eval (r i₀)
      ≠ 0 := by
  classical
  rw [Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun l hl => ?_
  have hne : l ≠ i₀ := (Finset.mem_erase.1 hl).1
  have hval : (r i₀ - r l) ≠ 0 := sub_ne_zero.2 fun h => hne (hr h.symm)
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ hval

/-- **Independence of the divided principal parts.** -/
theorem dividedPart_eq_zero_of_sum_eq_zero {r : Fin k → ℝ} (hr : Function.Injective r)
    (m : Fin k → ℕ) (c : Fin k → ℕ → ℝ)
    (hsum : ∑ i : Fin k, ∑ p ∈ Finset.Icc 1 (m i),
      Polynomial.C (c i p) * dividedPart r m i p = 0) :
    ∀ (i : Fin k), ∀ p ∈ Finset.Icc 1 (m i), c i p = 0 := by
  classical
  by_contra hcon
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hcon
  obtain ⟨p₀, hp₀⟩ := not_forall.1 hi₀
  obtain ⟨hp₀mem, hp₀ne⟩ := not_imp.1 hp₀
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ,
      S = (Finset.Icc 1 (m i₀)).filter fun p => c i₀ p ≠ 0 := ⟨_, rfl⟩
  have hSne : S.Nonempty := ⟨p₀, by rw [hS]; exact Finset.mem_filter.2 ⟨hp₀mem, hp₀ne⟩⟩
  obtain ⟨q, hqS, hqmax⟩ : ∃ q ∈ S, ∀ p ∈ S, p ≤ q :=
    ⟨S.max' hSne, S.max'_mem hSne, fun p hp => S.le_max' p hp⟩
  have hqmem : q ∈ Finset.Icc 1 (m i₀) := by
    rw [hS] at hqS
    exact (Finset.mem_filter.1 hqS).1
  have hqne : c i₀ q ≠ 0 := by
    rw [hS] at hqS
    exact (Finset.mem_filter.1 hqS).2
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqmem).1
  obtain ⟨g, hg⟩ : ∃ g : ((_ : Fin k) × ℕ) → Polynomial ℝ,
      g = fun x => Polynomial.C (c x.1 x.2) * dividedPart r m x.1 x.2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset ((_ : Fin k) × ℕ),
      T = Finset.univ.sigma fun i => Finset.Icc 1 (m i) := ⟨_, rfl⟩
  have hsumT : ∑ x ∈ T, g x = 0 := by
    rw [hT, Finset.sum_sigma, hg]
    exact hsum
  have hx₀ : (⟨i₀, q⟩ : (_ : Fin k) × ℕ) ∈ T := by
    rw [hT]
    exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, hqmem⟩
  have hsplit : g ⟨i₀, q⟩ + ∑ x ∈ T.erase ⟨i₀, q⟩, g x = 0 := by
    rw [Finset.add_sum_erase T g hx₀]
    exact hsumT
  have hrest : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q + 1))
      ∣ ∑ x ∈ T.erase ⟨i₀, q⟩, g x := by
    refine Finset.dvd_sum fun x hx => ?_
    have hxne : x ≠ (⟨i₀, q⟩ : (_ : Fin k) × ℕ) := (Finset.mem_erase.1 hx).1
    have hxmem : x ∈ T := (Finset.mem_erase.1 hx).2
    have hxIcc : x.2 ∈ Finset.Icc 1 (m x.1) := by
      rw [hT] at hxmem
      exact (Finset.mem_sigma.1 hxmem).2
    rw [hg]
    by_cases hi : x.1 = i₀
    · by_cases hlt : x.2 < q
      · exact Dvd.dvd.mul_left (pow_dvd_dividedPart_of_ne r m hq1 (Or.inr ⟨hi, hlt⟩)) _
      · have hczero : c x.1 x.2 = 0 := by
          by_contra hc
          have hmemS : x.2 ∈ S := by
            rw [hS, ← hi]
            exact Finset.mem_filter.2 ⟨hxIcc, hc⟩
          have hle := hqmax x.2 hmemS
          have hpq : x.2 = q := by omega
          exact hxne (Sigma.ext hi (by rw [hpq]))
        rw [hczero, map_zero, zero_mul]
        exact dvd_zero _
    · exact Dvd.dvd.mul_left (pow_dvd_dividedPart_of_ne r m hq1 (Or.inl hi)) _
  have hmain : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q + 1)) ∣ g ⟨i₀, q⟩ := by
    have heq : g ⟨i₀, q⟩ = -∑ x ∈ T.erase ⟨i₀, q⟩, g x :=
      eq_neg_of_add_eq_zero_left hsplit
    rw [heq]
    exact hrest.neg_right
  rw [hg] at hmain
  obtain ⟨Π₀, hΠ₀⟩ : ∃ Π₀ : Polynomial ℝ,
      Π₀ = ∏ l ∈ Finset.univ.erase i₀, (Polynomial.X - Polynomial.C (r l)) ^ (m l) := ⟨_, rfl⟩
  have hform : Polynomial.C (c i₀ q) * dividedPart r m i₀ q
      = (Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q) * (Polynomial.C (c i₀ q) * Π₀) := by
    rw [dividedPart, hΠ₀]
    ring
  rw [hform, pow_succ] at hmain
  have hXne : ((Polynomial.X - Polynomial.C (r i₀)) ^ (m i₀ - q) : Polynomial ℝ) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (r i₀))
  have hcancel : (Polynomial.X - Polynomial.C (r i₀)) ∣ (Polynomial.C (c i₀ q) * Π₀) :=
    (mul_dvd_mul_iff_left hXne).1 hmain
  have hroot : (Polynomial.C (c i₀ q) * Π₀).eval (r i₀) = 0 :=
    Polynomial.dvd_iff_isRoot.1 hcancel
  rw [Polynomial.eval_mul, Polynomial.eval_C] at hroot
  have hΠ₀ne : Π₀.eval (r i₀) ≠ 0 := by
    rw [hΠ₀]
    exact eval_prod_erase_ne_zero hr m i₀
  exact hqne ((mul_eq_zero.1 hroot).resolve_right hΠ₀ne)

end GaloisForLFunctions.HTGeometry

end
