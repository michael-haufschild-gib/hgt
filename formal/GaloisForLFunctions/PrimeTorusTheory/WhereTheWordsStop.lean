import GaloisForLFunctions.PrimeTorusTheory.TarryEscottWords
import Mathlib

/-!
# Where the words stop

The saving of a word may sit on small primes, while the size of a column sits at the top. To move it up, the integers of the word must avoid the small primes. Here is what that costs.

**A full progression** (`primorial_dvd_of_free`, `sum_log_le_log_of_free`). If `K ≥ z` terms `r + q m`, `m < K`, are free of the primes up to `z`, then every prime up to `z` divides `q`. So `θ(z) ≤ log q`. The mean-distance theorem runs over full progressions, so at length `y` it deletes the primes up to `≍ log y` and no more.

**A squared word** (`squared_word_pattern`). The terms of a squared word are `x + h(a + b)`, for `a, b` in its support `S`.
* A word with moments vanishing up to `k` has `|S| ≥ k + 2` (`card_support_ge`), so its pattern has at least `2k + 3` distinct terms (`card_sumset_ge`).
* If those terms avoid a prime `p ∤ h`, then `S` occupies at most `p/2` residue classes modulo `p` (`two_mul_card_image_le`, by Cauchy–Davenport).

So a squared word living on integers with only large prime factors is an admissible pattern of `≥ 2k + 3` almost primes, in a sumset. At height `exp L` the word needs `k ≍ L`, so at polylogarithmic length this is an almost-prime tuple of size a power of its height: the sieve cannot produce it, and a random model does not contain it unless the sets correlate through `h`, which is the first case. Reaching the top of a column at polylogarithmic precision by this mechanism is at least that hard.
-/

open Finset
open scoped Pointwise Matrix

namespace GaloisForLFunctions.PrimeTorusTheory

/-- A progression of length at least `p` meets every residue class modulo `p` unless `p` divides its step. -/
theorem prime_dvd_of_free {p q r K : ℕ} (hp : p.Prime) (hK : p ≤ K)
    (hfree : ∀ m < K, ¬ p ∣ r + q * m) : p ∣ q := by
  by_contra hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set m : ZMod p := -(r : ZMod p) * (q : ZMod p)⁻¹ with hm
  refine hfree m.val ((ZMod.val_lt m).trans_le hK) ?_
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, hm]
  field_simp
  ring

/-- **The modulus of a full progression.** If `K ≥ z` terms are free of the primes up to `z`, the primorial divides the step. -/
theorem primorial_dvd_of_free {q r K z : ℕ} (hK : z ≤ K)
    (hfree : ∀ m < K, ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ r + q * m) : primorial z ∣ q := by
  unfold primorial
  refine Finset.prod_primes_dvd q (fun p hp => (Finset.mem_filter.mp hp).2.prime) fun p hp => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
  have hpz : p ≤ z := Nat.lt_succ_iff.mp (Finset.mem_range.mp h1)
  exact prime_dvd_of_free h2 (hpz.trans hK) fun m hm => hfree m hm p h2 hpz

/-- **The cost of a full progression.** `θ(z) ≤ log q`. -/
theorem sum_log_le_log_of_free {q r K z : ℕ} (hq : q ≠ 0) (hK : z ≤ K)
    (hfree : ∀ m < K, ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ r + q * m) :
    ∑ p ∈ (range (z + 1)).filter Nat.Prime, Real.log p ≤ Real.log q := by
  have hle : primorial z ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (primorial_dvd_of_free hK hfree)
  have hpos : (0 : ℝ) < (primorial z : ℕ) := by exact_mod_cast primorial_pos z
  have h1 : Real.log ((primorial z : ℕ) : ℝ) ≤ Real.log q :=
    Real.log_le_log hpos (by exact_mod_cast hle)
  refine le_trans (le_of_eq ?_) h1
  unfold primorial
  push_cast
  rw [Real.log_prod fun p hp => by
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero]

/-- **The support of a squared word in a prime.** If the pattern `x + h(S + S)` avoids `p ∤ h`, then `S` occupies at most `p/2` classes modulo `p`. -/
theorem two_mul_card_image_le {S : Finset ℕ} (hS : S.Nonempty) {p x h : ℕ} (hp : p.Prime) (hph : ¬ p ∣ h)
    (hfree : ∀ a ∈ S, ∀ b ∈ S, ¬ p ∣ x + h * (a + b)) :
    2 * (S.image fun a : ℕ => (a : ZMod p)).card ≤ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Finset (ZMod p) := S.image fun a : ℕ => (a : ZMod p) with hA
  have hAne : A.Nonempty := hS.image _
  have hh0 : (h : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set c : ZMod p := -(x : ZMod p) * (h : ZMod p)⁻¹ with hc
  have hmiss : c ∉ A + A := by
    intro hmem
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hmem
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    refine hfree a ha b hb ?_
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have e : (a : ZMod p) + b = c := huv
    rw [e, hc]
    field_simp
    ring
  have hle : (A + A).card ≤ p - 1 := by
    have hsub : A + A ⊆ Finset.univ.erase c := fun y hy =>
      Finset.mem_erase.mpr ⟨fun h => hmiss (h ▸ hy), Finset.mem_univ y⟩
    have h1 := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, ZMod.card] at h1
  have hcd := ZMod.cauchy_davenport hp hAne hAne
  have hp2 := hp.two_le
  rcases le_total p (A.card + A.card - 1) with h1 | h1
  · rw [min_eq_left h1] at hcd
    omega
  · rw [min_eq_right h1] at hcd
    have hApos : 0 < A.card := Finset.card_pos.mpr hAne
    omega

/-- The support of a word: a nonzero word with moments vanishing up to `k` has at least `k + 2` terms. -/
theorem card_support_ge {M k : ℕ} {c : ℕ → ℤ} (hm : ∀ j ≤ k, binomMoment M c j = 0)
    (hne : ∃ a ∈ range (M + 1), c a ≠ 0) :
    k + 2 ≤ ((range (M + 1)).filter fun a => c a ≠ 0).card := by
  classical
  set S := (range (M + 1)).filter fun a => c a ≠ 0 with hS
  by_contra hlt
  push Not at hlt
  set s := S.card with hs
  have hsk : ∀ j : Fin s, (j : ℕ) ≤ k := fun j => by omega
  set e : Fin s ≃ S := S.equivFin.symm with he
  set v : Fin s → ℤ := fun i => ((e i : ℕ) : ℤ) with hv
  have hinj : Function.Injective v := fun i j h => by
    have h1 : (((e i : S) : ℕ) : ℤ) = (((e j : S) : ℕ) : ℤ) := h
    exact e.injective (Subtype.ext (by exact_mod_cast h1))
  have hdet : (Matrix.of fun i j : Fin s => (descPochhammer ℤ j).eval (v i)).det ≠ 0 := by
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v (fun j => descPochhammer ℤ j)
      (fun j => descPochhammer_natDegree ℤ j) (fun j => monic_descPochhammer ℤ j)]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  -- The word lies in the kernel.
  have hker : (fun i : Fin s => c (e i : ℕ)) ᵥ* (Matrix.of fun i j : Fin s => (descPochhammer ℤ j).eval (v i)) = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    have hval : ∀ a : ℕ, (descPochhammer ℤ j).eval (a : ℤ) = ((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ) := by
      intro a
      rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      rfl
    have hsum : ∑ i : Fin s, c (e i : ℕ) * (descPochhammer ℤ j).eval (v i) =
        ∑ a ∈ S, c a * (((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ)) := by
      rw [← Finset.sum_coe_sort S fun a => c a * (((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ))]
      rw [← Equiv.sum_comp e fun a : S => c (a : ℕ) * (((j : ℕ).factorial : ℤ) * ((a : ℕ).choose (j : ℕ) : ℤ))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show v i = (((e i : S) : ℕ) : ℤ) from rfl, hval]
    rw [hsum]
    have hmom := hm (j : ℕ) (hsk j)
    have hsub : ∑ a ∈ S, c a * (((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ)) =
        ∑ a ∈ range (M + 1), c a * (((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ)) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun a ha hnot => ?_
      have : c a = 0 := by
        by_contra h0
        exact hnot (Finset.mem_filter.mpr ⟨ha, h0⟩)
      rw [this, zero_mul]
    rw [hsub]
    have e2 : ∑ a ∈ range (M + 1), c a * (((j : ℕ).factorial : ℤ) * (a.choose (j : ℕ) : ℤ)) =
        ((j : ℕ).factorial : ℤ) * binomMoment M c (j : ℕ) := by
      unfold binomMoment
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [e2, hmom, mul_zero]
  have hzero := Matrix.eq_zero_of_vecMul_eq_zero hdet hker
  obtain ⟨a, ha, hca⟩ := hne
  have hmem : a ∈ S := Finset.mem_filter.mpr ⟨ha, hca⟩
  have h0 := congrFun hzero (e.symm ⟨a, hmem⟩)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply] at h0
  exact hca h0

/-- A sumset of naturals has at least `2|S| − 1` elements. -/
theorem card_sumset_ge {S : Finset ℕ} (hS : S.Nonempty) : 2 * S.card - 1 ≤ (S + S).card := by
  have h := cauchy_davenport_add_of_linearOrder_isCancelAdd hS hS
  omega

/-- **The pattern of a squared word.** A nonzero word with moments vanishing up to `k` has a pattern of at least `2k + 3` distinct sums. If the terms `x + h(a + b)` avoid a prime `p ∤ h`, the support occupies at most `p/2`
classes modulo `p`. -/
theorem squared_word_pattern {M k : ℕ} {c : ℕ → ℤ} (hm : ∀ j ≤ k, binomMoment M c j = 0)
    (hne : ∃ a ∈ range (M + 1), c a ≠ 0) :
    2 * k + 3 ≤ (((range (M + 1)).filter fun a => c a ≠ 0) + ((range (M + 1)).filter fun a => c a ≠ 0)).card ∧
      ∀ {p x h : ℕ}, p.Prime → ¬ p ∣ h →
        (∀ a ∈ (range (M + 1)).filter (fun a => c a ≠ 0), ∀ b ∈ (range (M + 1)).filter (fun a => c a ≠ 0),
          ¬ p ∣ x + h * (a + b)) →
        2 * (((range (M + 1)).filter fun a => c a ≠ 0).image fun a : ℕ => (a : ZMod p)).card ≤ p := by
  have hcard := card_support_ge hm hne
  have hS : ((range (M + 1)).filter fun a => c a ≠ 0).Nonempty := by
    rw [← Finset.card_pos]
    omega
  refine ⟨?_, fun hp hph hfree => two_mul_card_image_le hS hp hph hfree⟩
  have := card_sumset_ge hS
  omega

end GaloisForLFunctions.PrimeTorusTheory
