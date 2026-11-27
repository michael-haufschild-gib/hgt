import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRootPatterns
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularMonomialCosets

/-! The terminal root pattern is the Jacquet average. Moving the middle
block to the front identifies the initial pattern with the column-vanishing average. -/

noncomputable section
open WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq.JacquetPattern

variable {g n : ℕ} [Fact g.Prime]

private theorem eDat_congr (ψ : AddChar (ZMod g) ℂ) (P Q : Mt g n → Prop)
    (φ θ : Mt g n → ZMod g) (hP : ∀ A, P A ↔ Q A) (hφ : ∀ A, Q A → φ A = θ A) :
    eDat g n P φ ψ = eDat g n Q θ ψ := by
  obtain rfl : P = Q := funext fun A => propext (hP A)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.mp hu).2]

private theorem tr_pattern_reindex (ψ : AddChar (ZMod g) ℂ) (Φ E : Fin n → Fin n → Prop)
    (σ : Equiv.Perm (Fin n)) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    tr (eDat g n (InPattern fun i j => Φ (σ i) (σ j))
      (patternEntrySum fun i j => E (σ i) (σ j)) ψ) χ =
      tr (eDat g n (InPattern Φ) (patternEntrySum E) ψ) χ := by
  let w : Gn g n := monomialUnit σ.symm fun _ => 1
  let e : Gn g n ≃ Gn g n := (MulAut.conj w⁻¹).toEquiv
  have hw (u : Gn g n) : e u = w⁻¹ * u * w := by simp [e]
  have hval (u : Gn g n) (i j : Fin n) : (e u).val i j = u.val (σ.symm i) (σ.symm j) := by
    rw [hw]
    simpa only [Units.val_one, inv_one, one_mul, mul_one] using
      (monomialConj_apply σ.symm (fun _ => 1) u i j)
  have hP (u : Gn g n) :
      InPattern (fun i j => Φ (σ i) (σ j)) u.val ↔ InPattern Φ (e u).val := by
    unfold InPattern
    simp only [hval]
    constructor
    · intro h i j hij
      rw [h (σ.symm i) (σ.symm j) (by simpa only [Equiv.apply_symm_apply] using hij)]
      simp [Matrix.one_apply]
    · intro h i j hij
      have he := h (σ i) (σ j) hij
      simpa [Matrix.one_apply] using he
  have hE (u : Gn g n) :
      patternEntrySum (fun i j => E (σ i) (σ j)) u.val = patternEntrySum E (e u).val := by
    unfold patternEntrySum
    simp only [hval]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
  rw [tr_eDat, tr_eDat]
  congr 1
  · congr 2
    exact Finset.card_equiv e fun u => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP]
  · refine Finset.sum_equiv e (fun u => by simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, hP]) fun u _ => ?_
    rw [hE]
    congr 1
    rw [hw]
    simpa only [inv_inv] using (hχ u w⁻¹).symm

private theorem inPattern_column (s k : ℕ) (hsk : s + k < n) (M : Mt g n) :
    InPattern (fun a b => a < b ∧ ¬ (middle k s a ∧ (b : ℕ) = s + k)) M ↔
      IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0 := by
  constructor
  · intro h
    refine ⟨fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, fun a hs ha => ?_⟩
    · rw [h i j (fun he => hji.not_gt he.1), Matrix.one_apply_ne hji.ne']
    · subst j
      rw [h i i (fun he => lt_irrefl _ he.1), Matrix.one_apply_eq]
    · have hn : a < n := ha.trans hsk
      have hne : (⟨a, hn⟩ : Fin n) ≠ ⟨s + k, hsk⟩ := fun e =>
        ha.ne (congrArg Fin.val e)
      rw [entN, dif_pos ⟨hn, hsk⟩, h _ _ (fun he => he.2 ⟨⟨hs, ha⟩, rfl⟩),
        Matrix.one_apply_ne hne]
  · rintro ⟨hu, hz⟩ i j hij
    obtain h | rfl | h := lt_trichotomy i j
    · have hb : middle k s i ∧ (j : ℕ) = s + k := of_not_not (fun hn => hij ⟨h, hn⟩)
      have he := hz i.val hb.1.1 hb.1.2
      rw [← hb.2] at he
      rw [Matrix.one_apply_ne h.ne]
      have hijn : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨i.isLt, j.isLt⟩
      simpa only [entN, dif_pos hijn, Fin.eta] using he
    · rw [(hu i i).2 rfl, Matrix.one_apply_eq]
    · rw [(hu i j).1 h, Matrix.one_apply_ne h.ne']

private theorem allowed_last (k s : ℕ) (a b : Fin n) :
    allowed k s s a b ↔ a < b ∧ ¬ (middle k s a ∧ (b : ℕ) = s + k) := by
  simp only [allowed, middle, Fin.lt_def]
  constructor <;> intro h <;> omega

private def moveMiddleToFront (k s : ℕ) (h : k + s ≤ n) : Equiv.Perm (Fin n) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.isLt
    split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.isLt
    split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

private theorem moveMiddleToFront_val (k s : ℕ) (h : k + s ≤ n) (a : Fin n) :
    ((moveMiddleToFront k s h a : Fin n) : ℕ) =
      if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

private theorem allowed_first (k s : ℕ) (h : k + s ≤ n) (a b : Fin n) :
    allowed k s 0 (moveMiddleToFront k s h a) (moveMiddleToFront k s h b) ↔
      a < b ∧ ¬ (middle k 0 a ∧ (b : ℕ) = k) := by
  simp only [allowed, middle, Fin.lt_def, moveMiddleToFront_val, Nat.zero_add]
  split_ifs <;> omega

private theorem selected_first (k s : ℕ) (h : k + s ≤ n) (a b : Fin n) :
    selected k s (moveMiddleToFront k s h a) (moveMiddleToFront k s h b) ↔
      (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [selected, middle, moveMiddleToFront_val]
  split_ifs <;> omega

private theorem sum_graph_eq_sum_entN (M : Mt g n) (S : Finset ℕ) (f : ℕ → ℕ) :
    (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
      ∑ a ∈ S, entN M a (f a) := by
  have hs (a : Fin n) :
      (∑ b : Fin n, if (a : ℕ) ∈ S ∧ (b : ℕ) = f a then M a b else 0) =
        if (a : ℕ) ∈ S then entN M a (f a) else 0 := by
    by_cases ha : (a : ℕ) ∈ S
    · rw [if_pos ha]
      by_cases hf : f a < n
      · rw [Finset.sum_eq_single (⟨f a, hf⟩ : Fin n)]
        · have haf : (a : ℕ) < n ∧ f a < n := ⟨a.isLt, hf⟩
          simp only [ha, and_self, if_true, entN, dif_pos haf, Fin.eta]
        · intro b _ hb
          exact if_neg fun h => hb (Fin.ext h.2)
        · simp
      · rw [entN, dif_neg (fun h => hf h.2)]
        apply Finset.sum_eq_zero
        intro b _
        rw [if_neg (show ¬ ((a : ℕ) ∈ S ∧ (b : ℕ) = f a) from
          fun h => hf (h.2 ▸ b.isLt))]
    · rw [if_neg ha]
      exact Finset.sum_eq_zero fun b _ => if_neg (fun h => ha h.1)
  rw [Finset.sum_congr rfl fun a _ => hs a,
    Fin.sum_univ_eq_sum_range (fun a => if a ∈ S then entN M a (f a) else 0), ← Finset.sum_filter]
  apply Finset.sum_subset
  · exact fun a ha => (Finset.mem_filter.mp ha).2
  · intro a ha hb
    have hlt : ¬ a < n := fun h => hb (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, ha⟩)
    rw [entN, dif_neg (fun h => hlt h.1)]

private theorem sum_of_graph_iff (M : Mt g n)
    (P : ℕ → ℕ → Prop) (S : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ a b : ℕ, b < n → (P a b ↔ a ∈ S ∧ b = f a)) :
    patternEntrySum (fun i j => P i.val j.val) M = ∑ a ∈ S, entN M a (f a) := by
  unfold patternEntrySum
  rw [← sum_graph_eq_sum_entN]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    if_congr (h i j j.isLt) rfl rfl

private theorem selected_first_sum (k : ℕ) (M : Mt g n)
    (hz : ∀ a, a < k → entN M a k = 0) :
    patternEntrySum (fun a b : Fin n => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ a ∈ Finset.range (n - 1), entN M a (a + 1) := by
  let S := (Finset.range (n - 1)).filter fun a => a + 1 ≠ k
  have hsum := sum_of_graph_iff M (fun a b => b = a + 1 ∧ b ≠ k) S (fun a => a + 1)
    (fun a b hb => by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      constructor <;> intro h <;> omega)
  rw [hsum]
  unfold S
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a + 1 = k
  · rw [if_neg (not_not.mpr h), h, hz a (by omega)]
  · rw [if_pos h]

private theorem selected_last_sum (k s : ℕ) (hn : n = k + 2 * s + 1) (M : Mt g n) :
    patternEntrySum (selected k s) M = phiJ k s M := by
  let A (a b : ℕ) := b = a + 1 ∧ b < s
  let B (a b : ℕ) := a + 1 = s ∧ b = s + k
  let C (a b : ℕ) := b = a + 1 ∧ s + k ≤ a
  let D (a b : ℕ) := b = a + 1 ∧ s ≤ a ∧ b < s + k
  let sum (R : ℕ → ℕ → Prop) := patternEntrySum (fun i j => R i.val j.val) M
  have hsplit : patternEntrySum (selected k s) M = sum A + sum B + sum C + sum D := by
    unfold sum patternEntrySum
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    unfold selected middle A B C D
    split_ifs <;> first | omega | simp
  have ha := sum_of_graph_iff M A (Finset.range (s - 1)) (fun a => a + 1)
    (fun a b _ => by simp only [A, Finset.mem_range]; constructor <;> intro h <;> omega)
  have hb := sum_of_graph_iff M B ((Finset.range s).filter (fun a => a + 1 = s)) (fun _ => s + k)
    (fun a b _ => by simp only [B, Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> omega)
  have hc : sum C = ∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1) := by
    change patternEntrySum (fun i j => C i.val j.val) M = _
    rw [sum_of_graph_iff M C (Finset.Ico (s + k) (s + k + s)) (fun a => a + 1)
      (fun a b hb => by simp only [C, Finset.mem_Ico]; constructor <;> intro h <;> omega),
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hd : sum D = ∑ i ∈ Finset.range (k - 1), entN M (s + i) (s + i + 1) := by
    change patternEntrySum (fun i j => D i.val j.val) M = _
    rw [sum_of_graph_iff M D (Finset.Ico s (s + (k - 1))) (fun a => a + 1)
      (fun a b _ => by simp only [D, Finset.mem_Ico]; constructor <;> intro h <;> omega),
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  change sum A = _ at ha
  change sum B = _ at hb
  have hmiddle :
      (∑ a ∈ (Finset.range s).filter (fun a => a + 1 = s), entN M a (s + k)) +
        (∑ i ∈ Finset.range s, entN M (s + k + i) (s + k + i + 1)) =
        (if 1 ≤ s then entN M (s - 1) (s + k) + entN M (s + k) (s + k + 1) else 0) +
          ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) := by
    cases s with
    | zero => simp
    | succ t =>
      have hsingle : (Finset.range (t + 1)).filter (fun a => a + 1 = t + 1) = {t} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        omega
      rw [hsingle, Finset.sum_singleton, Finset.sum_range_succ', if_pos (Nat.succ_le_succ (Nat.zero_le t)),
        Nat.succ_sub_one]
      simp only [add_zero]
      have hsum : (∑ i ∈ Finset.range t, entN M (t + 1 + k + (i + 1)) (t + 1 + k + (i + 1) + 1)) =
          ∑ i ∈ Finset.range t, entN M (t + 1 + k + 1 + i) (t + 1 + k + 2 + i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1 <;> omega
      rw [hsum]
      abel
  rw [hsplit, ha, hb, hc, hd]
  unfold phiJ
  linear_combination hmiddle

private theorem terminal_average (ψ : AddChar (ZMod g) ℂ) (k s : ℕ) (hn : n = k + 2 * s + 1) :
    eDat g n (InPattern (allowed k s s)) (patternEntrySum (selected k s)) ψ = eJ g n k s ψ := by
  unfold eJ
  apply eDat_congr
  · intro M
    exact (show InPattern (allowed k s s) M ↔
      InPattern (fun a b => a < b ∧ ¬ (middle k s a ∧ (b : ℕ) = s + k)) M by
        simp only [InPattern, allowed_last]).trans (inPattern_column s k (by omega) M)
  · exact fun M _ => selected_last_sum k s hn M

private theorem initial_trace (ψ : AddChar (ZMod g) ℂ) (k s : ℕ) (hn : n = k + 2 * s + 1)
    (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    tr (eDat g n (InPattern (allowed k s 0)) (patternEntrySum (selected k s)) ψ) χ =
      tr (eJ' g n k ψ) χ := by
  have h : k + s ≤ n := by omega
  let σ := moveMiddleToFront k s h
  rw [← tr_pattern_reindex ψ _ _ σ χ hχ]
  congr 1
  have hA : (fun a b => allowed k s 0 (σ a) (σ b)) =
      (fun a b : Fin n => a < b ∧ ¬ (middle k 0 a ∧ (b : ℕ) = k)) :=
    funext fun a => funext fun b => propext (allowed_first k s h a b)
  have hE : (fun a b => selected k s (σ a) (σ b)) =
      (fun a b : Fin n => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) :=
    funext fun a => funext fun b => propext (selected_first k s h a b)
  rw [hA, hE, eJ']
  refine eDat_congr ψ _ _ _ _ (fun M => ?_) (fun M hM => selected_first_sum k M hM.2)
  simpa only [zero_add, Nat.zero_le, true_implies] using inPattern_column 0 k (by omega) M

/-- The Jacquet trace equals the trace of the column-vanishing average. -/
theorem tr_eJ_eq_tr_eJ' (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (k s : ℕ)
    (hn : n = k + 2 * s + 1) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    tr (eJ g n k s ψ) χ = tr (eJ' g n k ψ) χ := by
  rw [← terminal_average ψ k s hn]
  have hstep (i : ℕ) (hi : i ≤ s) :
      tr (eDat g n (InPattern (allowed k s i)) (patternEntrySum (selected k s)) ψ) χ =
        tr (eJ' g n k ψ) χ := by
    induction i with
    | zero => exact initial_trace ψ k s hn χ hχ
    | succ i ih =>
      rw [tr_step ψ hψ hn (Nat.succ_pos i) hi χ hχ, Nat.succ_sub_one]
      exact ih ((Nat.le_succ i).trans hi)
  exact hstep s le_rfl

end GlobalTheory.GLq.JacquetPattern
