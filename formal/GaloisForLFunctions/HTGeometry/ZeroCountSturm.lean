import GaloisForLFunctions.HTGeometry.FiniteZeroSet

/-!
# The zero count where the Sturm expression is positive

Assembling the pieces.  Between consecutive zeros a continuous function has constant sign, so the
gaps are arches.  Where `f'' + γ² f > 0` no zero is a local maximum, so two adjacent arches cannot
both be negative: the arches alternate at least every other step.  Every second gap is therefore
positive, and positive arches are at least `π/γ` long and pairwise disjoint, so their number — and
with it the number of gaps — is bounded by the length of the ambient interval.

`Z_{[a,b]}(f) ≤ 2 (b-a) γ / π + 2` wherever `f'' + γ² f` stays positive.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-- On a zero-free open interval a continuous function has constant sign. -/
theorem sign_constant_of_no_zero {f : ℝ → ℝ} (hf : Continuous f) {u v : ℝ}
    (hz : ∀ s ∈ Ioo u v, f s ≠ 0) :
    (∀ s ∈ Ioo u v, 0 < f s) ∨ (∀ s ∈ Ioo u v, f s < 0) := by
  by_cases hex : ∃ s ∈ Ioo u v, 0 < f s
  · left
    obtain ⟨s₀, hs₀mem, hs₀⟩ := hex
    intro s hs
    rcases lt_trichotomy (f s) 0 with hneg | hzz | hpos
    · exfalso
      rcases lt_trichotomy s s₀ with hlt | heq | hgt
      · obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Ioo (le_of_lt hlt) hf.continuousOn
          (show (0 : ℝ) ∈ Ioo (f s) (f s₀) from ⟨hneg, hs₀⟩)
        exact hz ξ ⟨lt_trans hs.1 hξ.1, lt_trans hξ.2 hs₀mem.2⟩ hξ0
      · rw [heq] at hneg; linarith
      · obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Ioo' (le_of_lt hgt) hf.continuousOn
          (show (0 : ℝ) ∈ Ioo (f s) (f s₀) from ⟨hneg, hs₀⟩)
        exact hz ξ ⟨lt_trans hs₀mem.1 hξ.1, lt_trans hξ.2 hs.2⟩ hξ0
    · exact absurd hzz (hz s hs)
    · exact hpos
  · right
    push Not at hex
    intro s hs
    rcases lt_or_eq_of_le (hex s hs) with h1 | h1
    · exact h1
    · exact absurd h1 (hz s hs)

/-- **Adjacent negative arches are impossible** where the Sturm expression is positive: the shared
zero would be a local maximum. -/
theorem not_two_negative_arches {f fd fdd h : ℝ → ℝ} {γ p m q : ℝ}
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ (2 : ℕ) * f t) (hpos : 0 < h m) (hz : f m = 0)
    (hpm : p < m) (hmq : m < q)
    (h1 : ∀ s ∈ Ioo p m, f s < 0) (h2 : ∀ s ∈ Ioo m q, f s < 0) : False := by
  refine not_isLocalMax_of_sturm_pos hf hfd hh hpos hz ?_
  refine Filter.eventually_of_mem
    (isOpen_Ioo.mem_nhds (show m ∈ Ioo p q from ⟨hpm, hmq⟩)) (fun s hs => ?_)
  rw [hz]
  rcases lt_trichotomy s m with hlt | heq | hgt
  · exact le_of_lt (h1 s ⟨hs.1, hlt⟩)
  · rw [heq, hz]
  · exact le_of_lt (h2 s ⟨hgt, hs.2⟩)

/-- **The zero count.**  Where `f'' + γ² f > 0` on `[a,b]`, consecutive zeros number at most
`2(b-a)γ/π + 2`. -/
theorem zero_count_le {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ (2 : ℕ) * f t)
    (hhpos : ∀ t ∈ Ioo a b, 0 < h t)
    {n : ℕ} (t : ℕ → ℝ)
    (hmono : ∀ i j, i < j → j ≤ n → t i < t j)
    (hmem : ∀ i, i ≤ n → t i ∈ Icc a b)
    (hzero : ∀ i, i ≤ n → f (t i) = 0)
    (hgapfree : ∀ i, i < n → ∀ s ∈ Ioo (t i) (t (i + 1)), f s ≠ 0) :
    (n : ℝ) ≤ 2 * ((b - a) * γ / π) + 1 := by
  classical
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hsign : ∀ i, i < n → (∀ s ∈ Ioo (t i) (t (i + 1)), 0 < f s)
      ∨ (∀ s ∈ Ioo (t i) (t (i + 1)), f s < 0) :=
    fun i hi => sign_constant_of_no_zero hcont (hgapfree i hi)
  -- choose, in each block of two consecutive gaps, one that is positive
  set k : ℕ := n / 2 with hk
  have hbound : ∀ j : Fin k, 2 * (j : ℕ) + 1 < n := by
    intro j
    have := j.2
    omega
  set σ : Fin k → ℕ := fun j =>
    if (∀ s ∈ Ioo (t (2 * (j : ℕ))) (t (2 * (j : ℕ) + 1)), 0 < f s) then 2 * (j : ℕ)
    else 2 * (j : ℕ) + 1 with hσ
  have hσlb : ∀ j : Fin k, 2 * (j : ℕ) ≤ σ j := by
    intro j
    simp only [hσ]
    split <;> omega
  have hσub : ∀ j : Fin k, σ j ≤ 2 * (j : ℕ) + 1 := by
    intro j
    simp only [hσ]
    split <;> omega
  have hσn : ∀ j : Fin k, σ j < n := fun j => lt_of_le_of_lt (hσub j) (by
    have := hbound j
    omega)
  have hσpos : ∀ j : Fin k, ∀ s ∈ Ioo (t (σ j)) (t (σ j + 1)), 0 < f s := by
    intro j
    simp only [hσ]
    split
    · rename_i hcase
      exact hcase
    · rename_i hcase
      have hlow : ∀ s ∈ Ioo (t (2 * (j : ℕ))) (t (2 * (j : ℕ) + 1)), f s < 0 := by
        rcases hsign (2 * (j : ℕ)) (by have := hbound j; omega) with hp | hn
        · exact absurd hp hcase
        · exact hn
      rcases hsign (2 * (j : ℕ) + 1) (hbound j) with hp | hn
      · exact hp
      · exfalso
        refine not_two_negative_arches hf hfd hh ?_ (hzero _ (by have := hbound j; omega))
          (hmono _ _ (by omega) (by have := hbound j; omega))
          (hmono _ _ (by omega) (by have := hbound j; omega)) hlow hn
        refine hhpos _ ⟨lt_of_le_of_lt (hmem (2 * (j : ℕ)) (by have := hbound j; omega)).1
            (hmono _ _ (by omega) (by have := hbound j; omega)),
          lt_of_lt_of_le (hmono (2 * (j : ℕ) + 1) (2 * (j : ℕ) + 2) (by omega)
            (by have := hbound j; omega))
            (hmem (2 * (j : ℕ) + 2) (by have := hbound j; omega)).2⟩
  -- the chosen arches are ordered and disjoint
  have hle : ∀ i j : ℕ, i ≤ j → j ≤ n → t i ≤ t j := by
    intro i j hij hjn
    rcases lt_or_eq_of_le hij with h1 | h1
    · exact le_of_lt (hmono i j h1 hjn)
    · rw [h1]
  have hcount := card_arches_le (g := f) (gd := fd) (gdd := fdd) (h := h) hγ hab hf hfd hh
    (fun t ht => (hhpos t ht).le)
    (fun j : Fin k => t (σ j)) (fun j : Fin k => t (σ j + 1))
    (fun j => (hmem _ (le_of_lt (hσn j))).1)
    (fun j => (hmem _ (hσn j)).2)
    (fun j => hmono _ _ (by omega) (hσn j))
    (fun j => hzero _ (le_of_lt (hσn j)))
    (fun j => hzero _ (hσn j))
    (fun j => hσpos j)
    (fun i j hij => by
      refine hle _ _ ?_ (le_of_lt (hσn j))
      have h1 := hσub i
      have h2 := hσlb j
      have h3 : (i : ℕ) < (j : ℕ) := hij
      omega)
  have hnk : (n : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    have : n ≤ 2 * k + 1 := by rw [hk]; omega
    exact_mod_cast this
  linarith
end GaloisForLFunctions.HTGeometry
