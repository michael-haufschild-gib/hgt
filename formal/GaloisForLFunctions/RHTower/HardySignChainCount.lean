import GaloisForLFunctions.RHTower.HardySignFlipOddOrder

/-!
# Sign chains of Hardy's `Z` feed the odd-fibre census

Each sign change of `Z` across a subinterval produces a critical zero of odd order strictly inside
it (`exists_odd_order_line_zero_of_hardyZ_sign_flip`).  Disjoint subintervals give distinct
ordinates, so a chain of `n` sign changes inside `(0, T]` gives `n` distinct members of the odd-fibre
census `O(T)`.

Combined with `three_mul_xiOddFiberCount_le` this turns **any** sign-change lower bound for `Z` — the
output of Selberg's method, and of Levinson's detector, which on the critical line is `Ξ` times a
nonvanishing factor — directly into a lower bound for the horizontal singleton count `H₁`.
-/

open Complex Set


noncomputable section

namespace RHTower

private theorem monotone_of_step {g : ℕ → ℝ} {n : ℕ} (hstep : ∀ i < n, g i < g (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → g i ≤ g j := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := by omega
      rw [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · have hij' : i ≤ j := by omega
        have hjn' : j ≤ n := by omega
        exact le_trans (ih hij' hjn') (hstep j (by omega)).le
      · have : i = j + 1 := by omega
        rw [this]

/-- **Sign changes of Hardy's `Z` are counted by the odd-fibre census.**  A strictly increasing
chain of heights in `(0, T]` across which `Z` alternates in sign produces that many distinct
critical ordinates of odd order, hence that many members of `O(T)`. -/
theorem le_xiOddFiberCount_of_sign_chain {T : ℝ} {n : ℕ} {g : ℕ → ℝ}
    (hstep : ∀ i < n, g i < g (i + 1)) (hg0 : 0 < g 0) (hgn : g n ≤ T)
    (hsign : ∀ i < n, hardyZ (g i) * hardyZ (g (i + 1)) < 0) :
    n ≤ xiOddFiberCount T := by
  classical
  have hmono := monotone_of_step hstep
  have hex : ∀ i : Fin n, ∃ τ' : ℝ, τ' ∈ Set.Ioo (g i) (g ((i : ℕ) + 1)) ∧
      xi (linePt τ') = 0 ∧ Odd ((analyticOrderAt xi (linePt τ')).toNat) := by
    intro i
    exact exists_odd_order_line_zero_of_hardyZ_sign_flip (hstep i i.isLt) (hsign i i.isLt)
  choose τ hτ using hex
  -- the chosen ordinates are strictly increasing in `i`
  have hlt : ∀ i j : Fin n, (i : ℕ) < (j : ℕ) → τ i < τ j := by
    intro i j hij
    have h1 : τ i < g ((i : ℕ) + 1) := (hτ i).1.2
    have h2 : g ((j : ℕ)) < τ j := (hτ j).1.1
    have h3 : g ((i : ℕ) + 1) ≤ g (j : ℕ) := hmono _ _ (by omega) (le_of_lt j.isLt)
    linarith
  have hinj : Function.Injective (fun i : Fin n => linePt (τ i)) := by
    intro i j hij
    have him : τ i = τ j := by
      have := congrArg Complex.im hij
      simpa [linePt_im] using this
    by_contra hne
    rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with h | h
    · exact absurd him (ne_of_lt (hlt i j h))
    · have hji : (j : ℕ) < (i : ℕ) := by
        rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with h' | h'
        · exact h'
        · exact absurd (Fin.ext (by omega)) hne
      exact absurd him.symm (ne_of_lt (hlt j i hji))
  set A : Finset ℂ :=
    (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)) with hA
  have hmem : ∀ i : Fin n, linePt (τ i) ∈ A := by
    intro i
    obtain ⟨⟨hlow, hhigh⟩, hzero, hodd⟩ := hτ i
    have hpos : 0 < τ i := lt_of_lt_of_le hg0 (le_trans (hmono 0 (i : ℕ) (Nat.zero_le _)
      (le_of_lt i.isLt)) hlow.le)
    have hle : τ i ≤ T := by
      have h1 : g ((i : ℕ) + 1) ≤ g n := hmono _ _ (by omega) le_rfl
      linarith
    rw [hA, mem_xiOddFiber_iff]
    refine ⟨?_, linePt_re _, ?_⟩
    · rw [mem_stripFinsetPos]
      exact ⟨linePt_re_pos _, linePt_re_lt_one _, by rw [linePt_im]; exact hpos,
        by rw [linePt_im]; exact hle, hzero⟩
    · exact hodd
  have hcard : (Finset.univ.image (fun i : Fin n => linePt (τ i))).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsub : Finset.univ.image (fun i : Fin n => linePt (τ i)) ⊆ A := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hmem i
  calc n = (Finset.univ.image (fun i : Fin n => linePt (τ i))).card := hcard.symm
    _ ≤ A.card := Finset.card_le_card hsub
    _ = xiOddFiberCount T := rfl

/-- **The complete combinatorial pipeline of `horizontal-singleton-zero-fibers`.**  A chain of `n`
sign changes of Hardy's `Z` inside `(0, T]` forces

```text
3n ≤ 2·H₁(T) + N(T).
```

Every step is unconditional: sign change ⟹ odd-order critical zero (seam parity), odd critical
order ⟹ odd fibre (fibre parity), odd fibre ⟹ singleton or multiplicity at least three (odd-fibre
charging).  The only remaining input for a positive singleton density is an analytic lower bound
for the sign-change count, and it must exceed `N(T)/3`. -/
theorem three_mul_le_two_mul_xiSingletonFiberCount_add_of_sign_chain
    {T : ℝ} {n : ℕ} {g : ℕ → ℝ}
    (hstep : ∀ i < n, g i < g (i + 1)) (hg0 : 0 < g 0) (hgn : g n ≤ T)
    (hsign : ∀ i < n, hardyZ (g i) * hardyZ (g (i + 1)) < 0) :
    3 * n ≤ 2 * xiSingletonFiberCount T + xiPosZeroCount T := by
  have h1 := le_xiOddFiberCount_of_sign_chain hstep hg0 hgn hsign
  have h2 := three_mul_xiOddFiberCount_le T
  omega

/-- The same over `ℝ`: `H₁(T) ≥ (3/2)·n − N(T)/2` for a chain of `n` sign changes. -/
theorem xiSingletonFiberCount_ge_of_sign_chain {T : ℝ} {n : ℕ} {g : ℕ → ℝ}
    (hstep : ∀ i < n, g i < g (i + 1)) (hg0 : 0 < g 0) (hgn : g n ≤ T)
    (hsign : ∀ i < n, hardyZ (g i) * hardyZ (g (i + 1)) < 0) :
    (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T : ℝ) / 2
      ≤ (xiSingletonFiberCount T : ℝ) := by
  have h := three_mul_le_two_mul_xiSingletonFiberCount_add_of_sign_chain hstep hg0 hgn hsign
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ) := by exact_mod_cast h
  linarith

end RHTower

end
