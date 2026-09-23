import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount
import Mathlib.Data.Finset.Sort

/-!
# Montgomery large values on an arbitrary color fibre

Maynard's box and amplitude selections color a common separated ordinate set.  A color fibre is
not generally an initial segment, so the range-indexed Montgomery estimate cannot be applied
without reindexing.  Sorting the fibre and extending its last point by an arithmetic progression
preserves the separation exactly.  This gives the literal finite-fibre mean-square and count forms.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Increasing enumeration of a nonempty finite set, continued after its last element at spacing
`delta`. -/
def finsetSeparatedExtension (S : Finset ℕ) (hS : S.Nonempty)
    (lam : ℕ → ℝ) (delta : ℝ) (i : ℕ) : ℝ :=
  if hi : i < S.card then
    lam (S.orderEmbOfFin rfl ⟨i, hi⟩)
  else
    lam (S.max' hS) + ((i + 1 - S.card : ℕ) : ℝ) * delta

theorem finsetSeparatedExtension_eq_of_lt
    (S : Finset ℕ) (hS : S.Nonempty) (lam : ℕ → ℝ) (delta : ℝ)
    {i : ℕ} (hi : i < S.card) :
    finsetSeparatedExtension S hS lam delta i =
      lam (S.orderEmbOfFin rfl ⟨i, hi⟩) := by
  simp [finsetSeparatedExtension, hi]

/-- Sorting an ambient separated sequence and continuing after the fibre preserves the same gap. -/
theorem finsetSeparatedExtension_gap
    (S : Finset ℕ) (hS : S.Nonempty) (lam : ℕ → ℝ) {delta : ℝ}
    (hdelta : 0 < delta) (hgap : ∀ i, lam i + delta ≤ lam (i + 1)) :
    ∀ i, finsetSeparatedExtension S hS lam delta i + delta ≤
      finsetSeparatedExtension S hS lam delta (i + 1) := by
  intro i
  by_cases hi1 : i + 1 < S.card
  · have hi : i < S.card := by omega
    rw [finsetSeparatedExtension_eq_of_lt S hS lam delta hi,
      finsetSeparatedExtension_eq_of_lt S hS lam delta hi1]
    let e := S.orderEmbOfFin (show S.card = S.card from rfl)
    have he : e ⟨i, hi⟩ < e ⟨i + 1, hi1⟩ :=
      e.strictMono (by simp)
    have hspread := le_of_gap hgap (e ⟨i, hi⟩) (e ⟨i + 1, hi1⟩) he.le
    have hsucc : e ⟨i, hi⟩ + 1 ≤ e ⟨i + 1, hi1⟩ := Nat.succ_le_iff.mpr he
    have hsuccR : (e ⟨i, hi⟩ : ℝ) + 1 ≤ (e ⟨i + 1, hi1⟩ : ℝ) := by
      exact_mod_cast hsucc
    nlinarith
  · by_cases hi : i < S.card
    · have hicard : i + 1 = S.card := by omega
      have hcard : 0 < S.card := hS.card_pos
      have hilast : i = S.card - 1 := by omega
      rw [finsetSeparatedExtension_eq_of_lt S hS lam delta hi]
      simp only [finsetSeparatedExtension, hi1, dite_false]
      have hlast :
          S.orderEmbOfFin rfl ⟨i, hi⟩ = S.max' hS := by
        subst i
        exact Finset.orderEmbOfFin_last rfl hcard
      rw [hlast, hicard]
      simp
    · have hi' : ¬ i + 1 < S.card := by omega
      simp only [finsetSeparatedExtension, hi, hi', dite_false]
      have hsub : i + 2 - S.card = (i + 1 - S.card) + 1 := by omega
      rw [hsub]
      push_cast
      ring_nf
      exact le_rfl

/-- Sum over a fibre equals the sum over its sorted extension's initial segment. -/
theorem sum_finset_eq_sum_extension
    (S : Finset ℕ) (hS : S.Nonempty) (lam : ℕ → ℝ) (delta : ℝ)
    (f : ℝ → ℝ) :
    ∑ r ∈ S, f (lam r) =
      ∑ i ∈ Finset.range S.card,
        f (finsetSeparatedExtension S hS lam delta i) := by
  let e := S.orderEmbOfFin (show S.card = S.card from rfl)
  calc
    ∑ r ∈ S, f (lam r) = ∑ r ∈ Finset.image e Finset.univ, f (lam r) := by
      rw [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i : Fin S.card, f (lam (e i)) := by
      rw [Finset.sum_image (Set.injOn_of_injective e.injective)]
    _ = ∑ i : Fin S.card,
        f (finsetSeparatedExtension S hS lam delta (i : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [finsetSeparatedExtension_eq_of_lt S hS lam delta i.isLt]
    _ = ∑ i ∈ Finset.range S.card,
        f (finsetSeparatedExtension S hS lam delta i) :=
      Fin.sum_univ_eq_sum_range
        (fun i => f (finsetSeparatedExtension S hS lam delta i)) S.card

/-- Montgomery's mean-square bound on an arbitrary finite subset of an ambient separated family. -/
theorem largeValues_dirPoly_finset
    (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T) :
    ∑ r ∈ S, ‖dirPoly N a (lam r)‖ ^ (2 : ℕ)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) *
          (1 / delta + 2 * Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  by_cases hS : S.Nonempty
  · let ext : ℕ → ℝ := finsetSeparatedExtension S hS lam delta
    let R : ℕ := S.card - 1
    have hcard : 0 < S.card := hS.card_pos
    have hRcard : R < S.card := by dsimp [R]; omega
    have hRsucc : R + 1 = S.card := by dsimp [R]; omega
    have hzero : (0 : ℕ) < S.card := hcard
    have hlow : delta / 2 ≤ ext 0 := by
      rw [show ext 0 = lam (S.orderEmbOfFin rfl ⟨0, hzero⟩) by
        exact finsetSeparatedExtension_eq_of_lt S hS lam delta hzero]
      exact (hband _ (Finset.orderEmbOfFin_mem S rfl _)).1
    have hhigh : ext R + delta / 2 ≤ T := by
      rw [show ext R = lam (S.orderEmbOfFin rfl ⟨R, hRcard⟩) by
        exact finsetSeparatedExtension_eq_of_lt S hS lam delta hRcard]
      exact (hband _ (Finset.orderEmbOfFin_mem S rfl _)).2
    have hbase := largeValues_dirPoly N hN a hdelta hT
      (finsetSeparatedExtension_gap S hS lam hdelta hgap) hlow R hhigh
    rw [hRsucc] at hbase
    rw [sum_finset_eq_sum_extension S hS lam delta
      (fun t => ‖dirPoly N a t‖ ^ (2 : ℕ))]
    exact hbase
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [Finset.sum_empty]
    positivity

/-- Counting form of finite-fibre Montgomery. -/
theorem card_largeValues_dirPoly_finset
    (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta T V : ℝ}
    (hdelta : 0 < delta) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hbig : ∀ r ∈ S, V ≤ ‖dirPoly N a (lam r)‖) :
    (S.card : ℝ) * V ^ (2 : ℕ)
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) *
          (1 / delta + 2 * Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have hlower : (S.card : ℝ) * V ^ (2 : ℕ) ≤
      ∑ r ∈ S, ‖dirPoly N a (lam r)‖ ^ (2 : ℕ) := by
    calc
      (S.card : ℝ) * V ^ (2 : ℕ) = ∑ _r ∈ S, V ^ (2 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
        pow_le_pow_left₀ hV.le (hbig r hr) 2
  exact hlower.trans
    (largeValues_dirPoly_finset N hN a hdelta hT hgap hband)

end RHTower.Sieve
