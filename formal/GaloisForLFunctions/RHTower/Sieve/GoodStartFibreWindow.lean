import GaloisForLFunctions.RHTower.Sieve.GoodStartVariableWindow
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare
import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation

/-!
# Step 1 at the fibre data
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Step 1 with an index-dependent start and length.** -/
theorem card_le_good_add_meanSquare_start {S Bad₂ : Finset ℕ} {st Lf : ℕ → ℕ} {D V δ : ℝ}
    (hδ : 0 < δ)
    (hδL : ∀ i ∈ S, δ ≤ (1 / 8) * D * (Lf i : ℝ))
    (hms : ∑ i ∈ S, (∑ n ∈ Finset.Ioc (st i) (st i + Lf i), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) ≤ V)
    (h2 : ∀ i ∈ S, i ∉ Bad₂ →
      (1 / 2) * D * (Lf i : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (st i) (st i + Lf i), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) :
    (S.card : ℝ)
      ≤ ((S.filter (fun i =>
          (3 / 16) * D * (Lf i : ℝ)
              ≤ (((Finset.Ioc (st i) (st i + Lf i)).filter
                  (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (Lf i : ℝ)
              ≤ (((Finset.Ioc (st i) (st i + Lf i)).filter
                  (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / δ ^ (2 : ℕ) + (Bad₂.card : ℝ) := by
  classical
  set M : ℕ → ℝ := fun i => ∑ n ∈ Finset.Ioc (st i) (st i + Lf i), ((moebius n : ℤ) : ℝ) with hM
  set Bad₁ : Finset ℕ := S.filter (fun i => δ ≤ |M i|) with hBad₁
  set G : Finset ℕ := S.filter (fun i =>
      (3 / 16) * D * (Lf i : ℝ)
          ≤ (((Finset.Ioc (st i) (st i + Lf i)).filter (fun n => moebius n = 1)).card : ℝ)
        ∧ (3 / 16) * D * (Lf i : ℝ)
          ≤ (((Finset.Ioc (st i) (st i + Lf i)).filter (fun n => moebius n = -1)).card : ℝ))
    with hG
  have h1 : ∀ i ∈ S, i ∉ Bad₁ → |M i| ≤ (1 / 8) * D * (Lf i : ℝ) := by
    intro i hi hnot
    have hlt : ¬ (δ ≤ |M i|) := by
      intro hc
      exact hnot (by rw [hBad₁, Finset.mem_filter]; exact ⟨hi, hc⟩)
    have := not_le.mp hlt
    linarith [hδL i hi]
  have hcover : S ⊆ (G ∪ Bad₁) ∪ Bad₂ := by
    intro i hi
    by_cases hb1 : i ∈ Bad₁
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb1)
    by_cases hb2 : i ∈ Bad₂
    · exact Finset.mem_union_right _ hb2
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    rw [hG, Finset.mem_filter]
    exact ⟨hi, card_moebius_sign_ge (h2 i hi hb2) (h1 i hi hb1)⟩
  have hnat : S.card ≤ (G.card + Bad₁.card) + Bad₂.card := by
    calc S.card ≤ ((G ∪ Bad₁) ∪ Bad₂).card := Finset.card_le_card hcover
      _ ≤ (G ∪ Bad₁).card + Bad₂.card := Finset.card_union_le _ _
      _ ≤ (G.card + Bad₁.card) + Bad₂.card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hmarkov : (Bad₁.card : ℝ) ≤ V / δ ^ (2 : ℕ) := by
    rw [hBad₁]
    exact RHTower.card_large_le_of_sum_sq_le hδ hms
  have hcast : (S.card : ℝ) ≤ ((G.card : ℕ) : ℝ) + (Bad₁.card : ℝ) + (Bad₂.card : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- The integer start of the fibre above `a`, as the left endpoint of a half-open window. -/
noncomputable def fibreStartIdx (x : ℝ) (a : ℕ) : ℕ := ⌈x / (a : ℝ)⌉₊ - 1

/-- The length of the fibre above `a`. -/
noncomputable def fibreLen (x h : ℝ) (a : ℕ) : ℕ :=
  ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ - fibreStartIdx x a

/-- **The fibre is a half-open window at an integer start.** -/
theorem innerFibre_eq_Ioc {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    innerFibre x h a
      = Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a) := by
  have hone : 1 ≤ ⌈x / (a : ℝ)⌉₊ := one_le_fibreStart hx ha
  rw [innerFibre_eq hx hh ha]
  simp only [fibreStartIdx, fibreLen]
  by_cases hle : ⌈x / (a : ℝ)⌉₊ - 1 ≤ ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊
  · have hsum : ⌈x / (a : ℝ)⌉₊ - 1 + (⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊
        - (⌈x / (a : ℝ)⌉₊ - 1)) = ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ := by omega
    have hsucc : ⌈x / (a : ℝ)⌉₊ - 1 + 1 = ⌈x / (a : ℝ)⌉₊ := by omega
    have hlem := Finset.Icc_add_one_left_eq_Ioc (⌈x / (a : ℝ)⌉₊ - 1)
      (⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊)
    rw [hsucc] at hlem
    rw [hsum]
    exact hlem
  · have hz : ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ - (⌈x / (a : ℝ)⌉₊ - 1) = 0 := by omega
    rw [hz, Nat.add_zero, Finset.Ioc_self]
    exact Finset.Icc_eq_empty (by omega)

/-- **Step 1 at the fibre data.**  The exceptional count is paid by the *fibre* mean square, which
is the normalisation the corpus proves unconditionally for the Möbius function. -/
theorem card_le_good_add_fibreMeanSquare {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h)
    {Bad₂ : Finset ℕ} {D V δ : ℝ} (hδ : 0 < δ)
    (hδL : ∀ a ∈ outerBlock x h, δ ≤ (1 / 8) * D * (fibreLen x h a : ℝ))
    (hms : ∑ a ∈ outerBlock x h,
        (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ (2 : ℕ) ≤ V)
    (h2 : ∀ a ∈ outerBlock x h, a ∉ Bad₂ →
      (1 / 2) * D * (fibreLen x h a : ℝ)
        ≤ ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) ^ (2 : ℕ)) :
    ((outerBlock x h).card : ℝ)
      ≤ (((outerBlock x h).filter (fun a =>
          (3 / 16) * D * (fibreLen x h a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a)).filter
                  (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (fibreLen x h a : ℝ)
              ≤ (((Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a)).filter
                  (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / δ ^ (2 : ℕ) + (Bad₂.card : ℝ) := by
  classical
  have hrw : ∀ a ∈ outerBlock x h,
      innerFibre x h a = Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a) :=
    fun a ha => innerFibre_eq_Ioc hx hh ha
  have hms' : ∑ a ∈ outerBlock x h,
      (∑ n ∈ Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a),
        ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) ≤ V := by
    refine le_trans (le_of_eq ?_) hms
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hrw a ha]
  have h2' : ∀ a ∈ outerBlock x h, a ∉ Bad₂ →
      (1 / 2) * D * (fibreLen x h a : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (fibreStartIdx x a) (fibreStartIdx x a + fibreLen x h a),
            ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) := by
    intro a ha hb
    rw [← hrw a ha]
    exact h2 a ha hb
  have hbase := card_le_good_add_meanSquare_start (S := outerBlock x h) (Bad₂ := Bad₂)
    (st := fibreStartIdx x) (Lf := fibreLen x h) (D := D) (V := V) (δ := δ)
    hδ hδL hms' h2'
  exact hbase

end RHTower.Sieve
