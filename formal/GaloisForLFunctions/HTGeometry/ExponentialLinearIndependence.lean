import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeObstruction
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Exponential-like elements are linearly independent

In a differential field, elements satisfying `E' = tau * E` behave like exponentials of the
antiderivatives of `tau`.  Artin's shortening argument shows that finitely many of them are linearly
independent over the field, provided no difference `tau i - tau j` of distinct exponents is a
logarithmic derivative in the field.

Normalizing one coefficient to one, differentiating, and subtracting the corresponding multiple of
the original relation produces a strictly shorter relation whose vanishing coefficients are exactly
the excluded logarithmic-derivative equations.  This is the shortening step of Ostrowski's theorem;
the obstruction it needs is proved separately for jet polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

variable {K : Type*} [Field K] [Differential K]

theorem deriv_mul_eq (a b : K) : (a * b)′ = a′ * b + a * b′ := by
  have h := Differential.deriv.leibniz a b
  simp only [smul_eq_mul] at h
  rw [h]
  ring

theorem deriv_one_eq_zero : (1 : K)′ = 0 :=
  Differential.deriv.map_one_eq_zero

/-- A power of an exponential-like element is exponential-like with the multiplied exponent. -/
theorem deriv_pow_expLike (x t : K) (h : x′ = t * x) (k : ℕ) :
    (x ^ k)′ = (k : K) * t * x ^ k := by
  induction k with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact deriv_one_eq_zero
  | succ k ih =>
      have hpow : x ^ (k + 1) = x * x ^ k := by ring
      rw [hpow, deriv_mul_eq, h, ih]
      push_cast
      ring

/-- A product of powers of exponential-like elements is exponential-like, with exponent the
corresponding integer combination. -/
theorem deriv_prod_pow {ι : Type*} (s : Finset ι) (E t : ι → K)
    (hEd : ∀ i ∈ s, (E i)′ = t i * E i) (n : ι → ℕ) :
    (∏ i ∈ s, E i ^ n i)′ = (∑ i ∈ s, (n i : K) * t i) * ∏ i ∈ s, E i ^ n i := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, zero_mul]
      exact deriv_one_eq_zero
  | cons a s ha ih =>
      have hmem : ∀ i ∈ s, (E i)′ = t i * E i := fun i hi =>
        hEd i (Finset.mem_cons.mpr (Or.inr hi))
      have hEa : (E a)′ = t a * E a := hEd a (Finset.mem_cons_self a s)
      rw [Finset.prod_cons, Finset.sum_cons, deriv_mul_eq, deriv_pow_expLike _ _ hEa, ih hmem]
      ring

/-- **Artin shortening for exponential-like elements.**  If the coefficients lie in a differential
subfield in which no difference of distinct exponents is a logarithmic derivative, then
exponential-like elements are linearly independent over that subfield. -/
theorem eq_zero_of_sum_expLike_eq_zero {ι : Type*} [Fintype ι] (F : Subfield K)
    (hFd : ∀ a ∈ F, a′ ∈ F) (E tau : ι → K)
    (hE : ∀ j, E j ≠ 0) (hEd : ∀ j, (E j)′ = tau j * E j) (htauF : ∀ j, tau j ∈ F)
    (htau : ∀ j₁ j₂ : ι, j₁ ≠ j₂ → ∀ c ∈ F, c ≠ 0 → c′ ≠ (tau j₁ - tau j₂) * c)
    (c : ι → K) (hcF : ∀ j, c j ∈ F) (hsum : ∑ j, c j * E j = 0) : ∀ j, c j = 0 := by
  classical
  suffices H : ∀ N : ℕ, ∀ c : ι → K, (∀ j, c j ∈ F) →
      (Finset.univ.filter fun j => c j ≠ 0).card ≤ N →
      (∑ j, c j * E j = 0) → ∀ j, c j = 0 by
    exact H _ c hcF le_rfl hsum
  intro N
  induction N with
  | zero =>
      intro c _ hcard _ j
      by_contra hj
      have hmem : j ∈ Finset.univ.filter fun j => c j ≠ 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      have hpos : 0 < (Finset.univ.filter fun j => c j ≠ 0).card :=
        Finset.card_pos.mpr ⟨j, hmem⟩
      omega
  | succ N ih =>
      intro c hcF hcard hsumc
      by_contra hnot
      push Not at hnot
      obtain ⟨j₀, hj₀⟩ := hnot
      -- normalize the `j₀` coefficient to one
      set d : ι → K := fun j => c j / c j₀ with hd
      have hdF : ∀ j, d j ∈ F := fun j => F.div_mem (hcF j) (hcF j₀)
      have hdne : ∀ j, d j ≠ 0 ↔ c j ≠ 0 := by
        intro j
        rw [hd]
        simp only [ne_eq, div_eq_zero_iff, hj₀, or_false]
      have hdj₀ : d j₀ = 1 := by
        rw [hd]
        exact div_self hj₀
      have hdsum : ∑ j, d j * E j = 0 := by
        have hrw : ∑ j, d j * E j = (∑ j, c j * E j) / c j₀ := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hd]
          ring
        rw [hrw, hsumc, zero_div]
      -- differentiate and subtract the `tau j₀` multiple
      have hderivsum : ∑ j, ((d j)′ + d j * tau j) * E j = 0 := by
        have hd0 : (∑ j, d j * E j)′ = 0 := by
          rw [hdsum]
          exact map_zero _
        rw [map_sum] at hd0
        rw [← hd0]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [deriv_mul_eq, hEd j]
        ring
      have hshort : ∑ j, ((d j)′ + d j * (tau j - tau j₀)) * E j = 0 := by
        have hsplit : ∑ j, ((d j)′ + d j * (tau j - tau j₀)) * E j
            = (∑ j, ((d j)′ + d j * tau j) * E j) - tau j₀ * ∑ j, d j * E j := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [hsplit, hderivsum, hdsum, mul_zero, sub_zero]
      -- the new coefficients have strictly smaller support
      set e : ι → K := fun j => (d j)′ + d j * (tau j - tau j₀) with he
      have heF : ∀ j, e j ∈ F := fun j =>
        F.add_mem (hFd _ (hdF j)) (F.mul_mem (hdF j) (F.sub_mem (htauF j) (htauF j₀)))
      have hej₀ : e j₀ = 0 := by
        rw [he]
        simp only [hdj₀, sub_self, mul_zero, add_zero, deriv_one_eq_zero]
      have hesub : (Finset.univ.filter fun j => e j ≠ 0)
          ⊆ (Finset.univ.filter fun j => c j ≠ 0).erase j₀ := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro hcon
          rw [hcon] at hj
          exact hj hej₀
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hdne j]
          intro hcon
          apply hj
          show (d j)′ + d j * (tau j - tau j₀) = 0
          rw [hcon, zero_mul, add_zero]
          exact map_zero _
      have hj₀mem : j₀ ∈ Finset.univ.filter fun j => c j ≠ 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj₀
      have hcarde : (Finset.univ.filter fun j => e j ≠ 0).card ≤ N := by
        have h1 := Finset.card_le_card hesub
        have h2 : ((Finset.univ.filter fun j => c j ≠ 0).erase j₀).card
            = (Finset.univ.filter fun j => c j ≠ 0).card - 1 :=
          Finset.card_erase_of_mem hj₀mem
        have h3 : 0 < (Finset.univ.filter fun j => c j ≠ 0).card :=
          Finset.card_pos.mpr ⟨j₀, hj₀mem⟩
        omega
      have hezero : ∀ j, e j = 0 := ih e heF hcarde hshort
      -- a second nonzero coefficient must exist, and it solves the excluded equation
      have hexists : ∃ j₁, j₁ ≠ j₀ ∧ d j₁ ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hsingle : ∑ j, d j * E j = d j₀ * E j₀ := by
          refine Finset.sum_eq_single j₀ (fun j _ hj => ?_) (fun hmem => absurd (Finset.mem_univ j₀) hmem)
          rw [hcon j hj, zero_mul]
        rw [hsingle, hdj₀, one_mul] at hdsum
        exact hE j₀ hdsum
      obtain ⟨j₁, hj₁ne, hj₁⟩ := hexists
      have hval : (d j₁)′ + d j₁ * (tau j₁ - tau j₀) = 0 := hezero j₁
      have hlog : (d j₁)′ = (tau j₀ - tau j₁) * d j₁ := by
        linear_combination hval
      exact htau j₀ j₁ (Ne.symm hj₁ne) (d j₁) (hdF j₁) hj₁ hlog

end

end GaloisForLFunctions.HTGeometry
