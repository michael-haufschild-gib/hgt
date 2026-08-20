import GaloisForLFunctions.RHTower.HardySignChainCount
import GaloisForLFunctions.HTGeometry.PhaseSignChainAvoid

/-!
# Counting odd fibres from a partial sign chain, and from a factored polar form

Two refinements of `HardySignChainCount`, both forced by Levinson's detector once its critical-line
zeros are allowed.

* `le_xiOddFiberCount_of_sign_subchain` — the steps of the chain across which `Z` changes sign need
  not be *all* of them.  Any subfamily already produces that many distinct odd-order ordinates,
  because the open steps are pairwise disjoint.

* `le_xiOddFiberCount_add_card_of_factored_advance` — the counting interface when `Z` is only known
  to be `P·ρ·cos φ` for a real amplitude `P` with finitely many zeros.  The detector
  `G = ζ + λζ'` vanishes on the critical line exactly at the multiple zeros of `ζ`, and dividing
  those out leaves precisely this shape, with `P` the real polynomial carrying them.  A node of the
  chain can be kept off the zero set of `P` (`exists_sign_chain_avoiding`), so each zero of `P`
  spoils at most one step and the loss is exactly `#S`.
-/

open Complex Set

noncomputable section

namespace RHTower

private theorem mono_of_step' {g : ℕ → ℝ} {n : ℕ} (hstep : ∀ i < n, g i < g (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → g i ≤ g j := by
  intro i j hij hjn
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact le_trans (ih (by omega) (by omega)) (hstep j (by omega)).le
      · have : i = j + 1 := by omega
        rw [this]

/-- **Only the sign flips one keeps have to be consecutive.**  A subfamily of the steps of a
strictly increasing chain across which `Z` changes sign already produces that many distinct
odd-order critical ordinates. -/
theorem le_xiOddFiberCount_of_sign_subchain {T : ℝ} {n : ℕ} {g : ℕ → ℝ} (good : Finset ℕ)
    (hgood : ∀ i ∈ good, i < n)
    (hstep : ∀ i < n, g i < g (i + 1)) (hg0 : 0 < g 0) (hgn : g n ≤ T)
    (hsign : ∀ i ∈ good, hardyZ (g i) * hardyZ (g (i + 1)) < 0) :
    good.card ≤ xiOddFiberCount T := by
  classical
  have hmono := mono_of_step' hstep
  have hex : ∀ i : ℕ, ∃ τ' : ℝ, i ∈ good →
      τ' ∈ Set.Ioo (g i) (g (i + 1)) ∧ xi (linePt τ') = 0 ∧
        Odd ((analyticOrderAt xi (linePt τ')).toNat) := by
    intro i
    by_cases hi : i ∈ good
    · obtain ⟨τ', hτ'⟩ :=
        exists_odd_order_line_zero_of_hardyZ_sign_flip (hstep i (hgood i hi)) (hsign i hi)
      exact ⟨τ', fun _ => hτ'⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose τ hτ using hex
  have hlt : ∀ i ∈ good, ∀ j ∈ good, i < j → τ i < τ j := by
    intro i hi j hj hij
    have h1 : τ i < g (i + 1) := (hτ i hi).1.2
    have h2 : g j < τ j := (hτ j hj).1.1
    have h3 : g (i + 1) ≤ g j := hmono _ _ (by omega) (le_of_lt (hgood j hj))
    linarith
  have hinj : Set.InjOn (fun i : ℕ => linePt (τ i)) good := by
    intro i hi j hj hij
    have him : τ i = τ j := by
      have := congrArg Complex.im hij
      simpa [linePt_im] using this
    by_contra hne
    rcases Nat.lt_or_ge i j with h | h
    · exact absurd him (ne_of_lt (hlt i hi j hj h))
    · have hji : j < i := by omega
      exact absurd him.symm (ne_of_lt (hlt j hj i hi hji))
  set A : Finset ℂ :=
    (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)) with hA
  have hmem : ∀ i ∈ good, linePt (τ i) ∈ A := by
    intro i hi
    obtain ⟨⟨hlow, hhigh⟩, hzero, hodd⟩ := hτ i hi
    have hpos : 0 < τ i :=
      lt_of_lt_of_le hg0 (le_trans (hmono 0 i (Nat.zero_le _) (le_of_lt (hgood i hi))) hlow.le)
    have hle : τ i ≤ T := by
      have h1 : g (i + 1) ≤ g n := hmono _ _ (hgood i hi) le_rfl
      linarith
    rw [hA, mem_xiOddFiber_iff]
    refine ⟨?_, linePt_re _, ?_⟩
    · rw [mem_stripFinsetPos]
      exact ⟨linePt_re_pos _, linePt_re_lt_one _, by rw [linePt_im]; exact hpos,
        by rw [linePt_im]; exact hle, hzero⟩
    · exact hodd
  have hcard : (good.image (fun i : ℕ => linePt (τ i))).card = good.card :=
    Finset.card_image_of_injOn hinj
  have hsub : good.image (fun i : ℕ => linePt (τ i)) ⊆ A := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact hmem i hi
  calc good.card = (good.image (fun i : ℕ => linePt (τ i))).card := hcard.symm
    _ ≤ A.card := Finset.card_le_card hsub
    _ = xiOddFiberCount T := rfl

/-- **The factored counting interface.**  If Hardy's `Z` factors on a window as a real amplitude
`P` — whose zeros lie in a finite set `S` — times `ρ·cos φ` with `ρ > 0` and `φ` continuous, then a
phase advance of `(n+1)π` still yields `n` odd-order ordinates, up to `#S` of them lost to the sign
changes of `P`. -/
theorem le_xiOddFiberCount_add_card_of_factored_advance {T₁ T₂ : ℝ} (h0 : 0 < T₁) (hT : T₁ ≤ T₂)
    {P ρ φ : ℝ → ℝ} {n : ℕ} (S : Finset ℝ)
    (hP : ContinuousOn P (Icc T₁ T₂))
    (hPz : ∀ τ ∈ Icc T₁ T₂, P τ = 0 → τ ∈ S)
    (hφ : ContinuousOn φ (Icc T₁ T₂))
    (hρ : ∀ τ ∈ Icc T₁ T₂, 0 < ρ τ)
    (hpolar : ∀ τ ∈ Icc T₁ T₂, hardyZ τ = P τ * (ρ τ * Real.cos (φ τ)))
    (hadv : φ T₁ + ((n : ℝ) + 1) * Real.pi ≤ φ T₂) :
    n ≤ xiOddFiberCount T₂ + S.card := by
  classical
  obtain ⟨g, hgmem, hgstep, hgS, hgsign⟩ :=
    exists_sign_chain_avoiding (φ := φ) (ρ := ρ) (n := n) S hT hφ hρ hadv
  set bad : Finset ℕ :=
    (Finset.range n).filter (fun i => ∃ τ ∈ S, g i < τ ∧ τ < g (i + 1)) with hbad
  have hbadex : ∀ i ∈ bad, ∃ τ ∈ S, g i < τ ∧ τ < g (i + 1) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmono := mono_of_step' hgstep
  -- choose the witness in `S` for each bad index
  have hchoice : ∀ i : ℕ, ∃ τ : ℝ, i ∈ bad → (τ ∈ S ∧ g i < τ ∧ τ < g (i + 1)) := by
    intro i
    by_cases hi : i ∈ bad
    · obtain ⟨τ, hτS, h1, h2⟩ := hbadex i hi
      exact ⟨τ, fun _ => ⟨hτS, h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hchoice
  have hbadcard : bad.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn w (fun i hi => (hw i hi).1) ?_
    intro i hi j hj hij
    by_contra hne
    have hlt : ∀ p q : ℕ, p ∈ bad → q ∈ bad → p < q → w p < w q := by
      intro p q hp hq hpq
      have h1 : w p < g (p + 1) := (hw p hp).2.2
      have h2 : g q < w q := (hw q hq).2.1
      have hqn : q < n := (Finset.mem_range.mp (Finset.mem_filter.mp hq).1)
      have h3 : g (p + 1) ≤ g q := hmono _ _ (by omega) (le_of_lt hqn)
      linarith
    rcases Nat.lt_or_ge i j with h | h
    · exact absurd hij (ne_of_lt (hlt i j hi hj h))
    · have : j < i := by omega
      exact absurd hij.symm (ne_of_lt (hlt j i hj hi this))
  set good : Finset ℕ := (Finset.range n) \ bad with hgood
  have hgoodcard : n ≤ good.card + S.card := by
    have hsub : Finset.range n ⊆ good ∪ bad := by
      intro i hi
      by_cases h : i ∈ bad
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, h⟩)
    have h1 : n ≤ good.card + bad.card := by
      calc n = (Finset.range n).card := (Finset.card_range n).symm
        _ ≤ (good ∪ bad).card := Finset.card_le_card hsub
        _ ≤ good.card + bad.card := Finset.card_union_le _ _
    omega
  have hgoodsign : ∀ i ∈ good, hardyZ (g i) * hardyZ (g (i + 1)) < 0 := by
    intro i hi
    have hin : i ∈ Finset.range n := (Finset.mem_sdiff.mp hi).1
    have hnb : i ∉ bad := (Finset.mem_sdiff.mp hi).2
    have hlt : i < n := Finset.mem_range.mp hin
    have hmi : g i ∈ Icc T₁ T₂ := hgmem i (by omega)
    have hmi1 : g (i + 1) ∈ Icc T₁ T₂ := hgmem (i + 1) (by omega)
    have hsubI : Icc (g i) (g (i + 1)) ⊆ Icc T₁ T₂ :=
      Icc_subset_Icc hmi.1 hmi1.2
    -- `P` has no zero on the step
    have hPne : ∀ τ ∈ Icc (g i) (g (i + 1)), P τ ≠ 0 := by
      intro τ hτ hzero
      have hτS : τ ∈ S := hPz τ (hsubI hτ) hzero
      have hne1 : τ ≠ g i := by
        intro h; exact hgS i (by omega) (h ▸ hτS)
      have hne2 : τ ≠ g (i + 1) := by
        intro h; exact hgS (i + 1) (by omega) (h ▸ hτS)
      refine hnb ?_
      rw [hbad, Finset.mem_filter]
      exact ⟨hin, τ, hτS, lt_of_le_of_ne hτ.1 (Ne.symm hne1), lt_of_le_of_ne hτ.2 hne2⟩
    -- hence `P` keeps its sign across the step
    have hPsign : 0 < P (g i) * P (g (i + 1)) := by
      have hPc : ContinuousOn P (Icc (g i) (g (i + 1))) := hP.mono hsubI
      have hstep' : g i ≤ g (i + 1) := (hgstep i hlt).le
      have h1 : P (g i) ≠ 0 := hPne _ ⟨le_rfl, hstep'⟩
      have h2 : P (g (i + 1)) ≠ 0 := hPne _ ⟨hstep', le_rfl⟩
      rcases lt_trichotomy (P (g i) * P (g (i + 1))) 0 with hneg | hzero | hpos
      · exfalso
        have hzin : (0 : ℝ) ∈ Icc (P (g i)) (P (g (i + 1))) ∨
            (0 : ℝ) ∈ Icc (P (g (i + 1))) (P (g i)) := by
          rcases lt_or_gt_of_ne h1 with hA | hA
          · left
            constructor
            · exact hA.le
            · nlinarith
          · right
            constructor
            · nlinarith
            · exact hA.le
        rcases hzin with hz | hz
        · obtain ⟨τ, hτ, hval⟩ := intermediate_value_Icc hstep' hPc hz
          exact hPne τ hτ hval
        · obtain ⟨τ, hτ, hval⟩ := intermediate_value_Icc' hstep' hPc hz
          exact hPne τ hτ hval
      · exact absurd hzero (mul_ne_zero h1 h2)
      · exact hpos
    have hZ1 := hpolar (g i) hmi
    have hZ2 := hpolar (g (i + 1)) hmi1
    have hW := hgsign i hlt
    rw [hZ1, hZ2]
    calc P (g i) * (ρ (g i) * Real.cos (φ (g i))) *
          (P (g (i + 1)) * (ρ (g (i + 1)) * Real.cos (φ (g (i + 1)))))
        = (P (g i) * P (g (i + 1))) *
            ((ρ (g i) * Real.cos (φ (g i))) *
              (ρ (g (i + 1)) * Real.cos (φ (g (i + 1))))) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hPsign hW
  have hcount : good.card ≤ xiOddFiberCount T₂ := by
    refine le_xiOddFiberCount_of_sign_subchain good ?_ hgstep ?_ ?_ hgoodsign
    · intro i hi
      exact Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    · exact lt_of_lt_of_le h0 (hgmem 0 (Nat.zero_le n)).1
    · exact (hgmem n le_rfl).2
  omega

end RHTower

end
