import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons

/-!
# The layers of a prime: the Künneth step at the horizon

Fix a prime `p`. Every weight splits as `λ = λ_{p'} + λ_p`, where `λ_{p'}(k) = λ(k)[p ∤ k]` and
`λ_p(k) = λ(k)[p ∣ k]` (`dilationForm_split`). The edges of `λ_{p'}` do not change the `p`-adic
valuation, so they never leave a **layer** `{n : v_p(n) = a}`
(`dilationForm_coprimePart_eq_sum_layers`). The layer `a` lies in the star of `p^a`, so it is a
copy of the lower horizon `⌊N/p^a⌋` (`dilationForm_starRestrict`). Its pullback is the packet on
the integers prime to `p`, the `p`-deleted complex. Hence, for every weight (`dilationForm_layers`),

  `P^λ_N(F) = Σ_{a ≥ 0} p^{−a} P^{λ_{p'}}_{⌊N/p^a⌋}(pullback of layer a) + P^{λ_p}_N(F)`.

This is the Künneth step `S ∖ {p} → S` at the horizon. The `p`-deleted complex appears once in
every layer, at the geometrically shrinking horizons `⌊N/p^a⌋`, and the layers interact only
through the `p`-part of the weight. For `Λ` that part is the `p`-tower form. Without the horizon all
layers are the same and the step is an honest Künneth sum
(`TheEulerProductTensorizes.gap_prod_ge`). The horizon replaces it by this layered sum, whose layer
sizes are the lower horizons.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

open GaloisForLFunctions.ArithmeticCouplingTheory

/-- The part of a weight prime to `p`. -/
def coprimePart (p : ℕ) (lam : ℕ → ℝ) (k : ℕ) : ℝ := if p ∣ k then 0 else lam k

/-- The part of a weight divisible by `p`. -/
def primePart (p : ℕ) (lam : ℕ → ℝ) (k : ℕ) : ℝ := if p ∣ k then lam k else 0

/-- The dilation form is additive in the weight. -/
theorem dilationForm_add_weight (l₁ l₂ : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm (fun k => l₁ k + l₂ k) N F = dilationForm l₁ N F + dilationForm l₂ N F := by
  rw [dilationForm, dilationForm, dilationForm, ← sum_add_distrib]
  exact sum_congr rfl fun q _ => by ring

theorem dilationForm_split (p : ℕ) (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm lam N F =
      dilationForm (coprimePart p lam) N F + dilationForm (primePart p lam) N F := by
  rw [← dilationForm_add_weight]
  congr 1
  funext k
  simp only [coprimePart, primePart]
  split_ifs <;> ring

/-- The layer of valuation `a`: the packet restricted to `{n : v_p(n) = a}`. -/
def layer (p a : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ := if n.factorization p = a then F n else 0

/-- **Edges prime to `p` stay in their layer.** -/
theorem dilationForm_coprimePart_eq_sum_layers (p : ℕ) (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm (coprimePart p lam) N F =
      ∑ a ∈ range (N + 1), dilationForm (coprimePart p lam) N (layer p a F) := by
  simp only [dilationForm]
  rw [sum_comm]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨hk, hn, hkn⟩ := mem_dilationPairs.mp hq
  by_cases hpk : p ∣ q.1
  · simp [coprimePart, hpk]
  · have hv : (q.1 * q.2).factorization p = q.2.factorization p := by
      rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpk, zero_add]
    have hlt : q.2.factorization p < N + 1 := by
      have := Nat.factorization_lt p (show q.2 ≠ 0 by omega)
      have : q.2 ≤ N := (Nat.le_mul_of_pos_left _ hk).trans hkn
      omega
    rw [sum_eq_single (q.2.factorization p)]
    · simp only [layer, hv, if_true]
    · intro a _ ha
      simp only [layer, hv, if_neg (Ne.symm ha), mul_zero, zero_div]
    · intro h
      exact absurd (mem_range.mpr hlt) h

/-- A layer lies in the star of `p^a`. -/
theorem layer_eq_starRestrict (p a : ℕ) (F : ℕ → ℝ) :
    layer p a F = starRestrict (p ^ a) (layer p a F) := by
  funext n
  simp only [starRestrict]
  split_ifs with h
  · rfl
  · simp only [layer]
    split_ifs with hv
    · exfalso
      apply h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact dvd_zero _
      · rw [← hv]; exact Nat.ordProj_dvd n p
    · rfl

/-- The pullback of a layer reads the packet on the integers prime to `p`. -/
theorem starPullback_layer {p : ℕ} (hp : p.Prime) (a : ℕ) (F : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    starPullback (p ^ a) (layer p a F) m = if p ∣ m then 0 else F (p ^ a * m) := by
  have hv : (p ^ a * m).factorization p = a + m.factorization p := by
    rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same]
  simp only [starPullback, layer, hv]
  by_cases hpm : p ∣ m
  · have : m.factorization p ≠ 0 := by
      have := (Nat.Prime.dvd_iff_one_le_factorization hp hm).mp hpm
      omega
    rw [if_neg (by omega), if_pos hpm]
  · rw [Nat.factorization_eq_zero_of_not_dvd hpm, add_zero, if_pos rfl, if_neg hpm]

/-- **The layers of a prime.** For every weight, the dilation form at horizon `N` is the sum over
the layers `a` of the `p`-deleted forms at the horizons `⌊N/p^a⌋`, weighted by `p^{−a}`, plus the
form of the `p`-part of the weight. -/
theorem dilationForm_layers {p : ℕ} (hp : p.Prime) (lam : ℕ → ℝ) (N : ℕ) (F : ℕ → ℝ) :
    dilationForm lam N F =
      ∑ a ∈ range (N + 1), (1 / (p ^ a : ℕ)) *
          dilationForm (coprimePart p lam) (N / p ^ a) (starPullback (p ^ a) (layer p a F)) +
        dilationForm (primePart p lam) N F := by
  rw [dilationForm_split p, dilationForm_coprimePart_eq_sum_layers]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [layer_eq_starRestrict p a F, dilationForm_starRestrict _ (pow_pos hp.pos a),
    ← layer_eq_starRestrict p a F]

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
