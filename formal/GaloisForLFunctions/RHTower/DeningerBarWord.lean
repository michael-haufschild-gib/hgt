import GaloisForLFunctions.RHTower.DeningerWordHeight

/-!
# The entire word-height bar source

The two-term Milnor algebra `B_H = ℂ·1 ⊕ 𝒦_H⁰` is the coefficient space on single letters of the
exponent lattice, with the zero character playing the role of the unit: the alphabet
`{1} ⊔ (Γ \ {0})` is the lattice `Γ` itself, with height `H(0) = 1` and character `0`.  Bar degree
is word length, so the bar source is the coefficient space on **nonempty** words, completed with
the product of the letter heights and every exponential length weight:

`P_{k,R}(c) = ∑_w R^{|w|} h(w)^k |c_w|`.

Weighting a word only by the height of its total character would give weight one to every `(m,-m)`
and no summability on the balanced sector; controlling one fixed length would not control the
number of faces in unbounded bar degree.  The product-of-letters height with all exponential
length weights survives both, and is nuclear.

* `DeningerBarWord`, `deningerBarHeight`, `deningerBarChar` : words and their data.
* `deningerBarKotheData_isNuclear` : **the bar source is nuclear.**
* `deningerBarSeminormR` : the two-parameter seminorms `P_{k,R}`, finite for every `R ≥ 1`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Nonempty words -/

/-- A nonempty word in the exponent lattice.  The zero letter is the algebra unit. -/
abbrev DeningerBarWord : Type := Σ r : ℕ, Fin (r + 1) → DeningerLattice

/-- The length of a bar word. -/
def deningerBarLength (w : DeningerBarWord) : ℕ := w.1 + 1

/-- The product of the heights of the letters of a bar word. -/
def deningerBarHeight (w : DeningerBarWord) : ℝ := ∏ j, deningerHeight (w.2 j)

/-- The total arithmetic character of a bar word. -/
def deningerBarChar (w : DeningerBarWord) : DeningerLattice := ∑ j, w.2 j

theorem one_le_deningerBarHeight (w : DeningerBarWord) : 1 ≤ deningerBarHeight w :=
  Finset.one_le_prod fun j _ => one_le_deningerHeight (w.2 j)

theorem deningerBarHeight_pos (w : DeningerBarWord) : 0 < deningerBarHeight w :=
  lt_of_lt_of_le zero_lt_one (one_le_deningerBarHeight w)

theorem deningerBarLength_pos (w : DeningerBarWord) : 0 < deningerBarLength w :=
  Nat.succ_pos _

/-- The height of the total character never exceeds the product of the letter heights. -/
theorem deningerHeight_barChar_le (w : DeningerBarWord) :
    deningerHeight (deningerBarChar w) ≤ deningerBarHeight w := by
  classical
  obtain ⟨r, f⟩ := w
  show deningerHeight (∑ j, f j) ≤ ∏ j, deningerHeight (f j)
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      refine le_trans (deningerHeight_add_le (f 0) (∑ j : Fin (r + 1), f j.succ)) ?_
      have hstep : deningerHeight (∑ j : Fin (r + 1), f j.succ)
          ≤ ∏ j : Fin (r + 1), deningerHeight (f j.succ) := ih (fun j => f j.succ)
      exact mul_le_mul_of_nonneg_left hstep (deningerHeight_pos (f 0)).le

/-! ## The bar Köthe datum -/

/-- **The entire word-height bar datum**: the product of the letter heights raised to `k`, times
the `k`-th exponential length weight. -/
def deningerBarKotheData : DeningerKotheData DeningerBarWord where
  w k w := deningerBarHeight w ^ k * ((k : ℝ) + 1) ^ deningerBarLength w
  pos k w :=
    mul_pos (pow_pos (deningerBarHeight_pos w) k) (pow_pos (by positivity) _)
  mono k w := by
    have h1 : deningerBarHeight w ^ k ≤ deningerBarHeight w ^ (k + 1) :=
      pow_le_pow_right₀ (one_le_deningerBarHeight w) (Nat.le_succ k)
    have h2 : ((k : ℝ) + 1) ^ deningerBarLength w
        ≤ (((k : ℝ) + 1) + 1) ^ deningerBarLength w :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2nn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ deningerBarLength w :=
      pow_nonneg (by positivity) _
    have hkk : ((k : ℝ) + 1) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    calc deningerBarHeight w ^ k * ((k : ℝ) + 1) ^ deningerBarLength w
        ≤ deningerBarHeight w ^ (k + 1) * ((k : ℝ) + 1) ^ deningerBarLength w :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ deningerBarHeight w ^ (k + 1) * ((((k : ℝ) + 1) + 1) ^ deningerBarLength w) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg (deningerBarHeight_pos w).le _)
      _ = deningerBarHeight w ^ (k + 1) *
            (((k + 1 : ℕ) : ℝ) + 1) ^ deningerBarLength w := by rw [hkk]

@[simp]
theorem deningerBarKotheData_w (k : ℕ) (w : DeningerBarWord) :
    deningerBarKotheData.w k w
      = deningerBarHeight w ^ k * ((k : ℝ) + 1) ^ deningerBarLength w := rfl

/-- **The bar source is nuclear.** -/
theorem deningerBarKotheData_isNuclear : deningerBarKotheData.IsNuclear := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt (((k : ℝ) + 1) * deningerHeightInvSum 2)
  refine ⟨max (k + 2) N, le_trans (Nat.le_add_right k 2) (le_max_left _ _), ?_⟩
  set l := max (k + 2) N with hldef
  have hkl : k + 2 ≤ l := le_max_left _ _
  have hNl : N ≤ l := le_max_right _ _
  set α : ℕ := l - k with hαdef
  have hα : 2 ≤ α := by omega
  have hlk : l = k + α := by omega
  set c : ℝ := ((k : ℝ) + 1) / ((l : ℝ) + 1) with hcdef
  have hlpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  have hratio : ∀ w : DeningerBarWord,
      deningerBarKotheData.w k w / deningerBarKotheData.w l w
        = (∏ j, (deningerHeight (w.2 j))⁻¹ ^ α) * c ^ deningerBarLength w := by
    intro w
    have hHpos := deningerBarHeight_pos w
    have hsplit : (∏ j, (deningerHeight (w.2 j))⁻¹ ^ α)
        = (deningerBarHeight w)⁻¹ ^ α := by
      rw [Finset.prod_pow, Finset.prod_inv_distrib]
      rfl
    have hHne : deningerBarHeight w ≠ 0 := ne_of_gt hHpos
    have hlne : ((l : ℝ) + 1) ≠ 0 := ne_of_gt hlpos
    have hHpow : deningerBarHeight w ^ l
        = deningerBarHeight w ^ k * deningerBarHeight w ^ α := by
      rw [← pow_add, ← hlk]
    rw [deningerBarKotheData_w, deningerBarKotheData_w, hsplit, hcdef, div_pow, hHpow, inv_pow]
    field_simp
  have hfiber : ∀ r : ℕ, Summable fun f : Fin (r + 1) → DeningerLattice =>
      deningerBarKotheData.w k (⟨r, f⟩ : DeningerBarWord) /
        deningerBarKotheData.w l (⟨r, f⟩ : DeningerBarWord) := by
    intro r
    refine ((deningerWordPow_summable hα (r + 1)).mul_right (c ^ (r + 1))).congr fun f => ?_
    exact (hratio ⟨r, f⟩).symm
  have hfiberSum : ∀ r : ℕ,
      (∑' f : Fin (r + 1) → DeningerLattice,
        deningerBarKotheData.w k (⟨r, f⟩ : DeningerBarWord) /
          deningerBarKotheData.w l (⟨r, f⟩ : DeningerBarWord))
        = (c * deningerHeightInvSum α) ^ (r + 1) := by
    intro r
    have hcong : ∀ f : Fin (r + 1) → DeningerLattice,
        deningerBarKotheData.w k (⟨r, f⟩ : DeningerBarWord) /
          deningerBarKotheData.w l (⟨r, f⟩ : DeningerBarWord)
          = (∏ j, (deningerHeight (f j))⁻¹ ^ α) * c ^ (r + 1) := fun f => hratio ⟨r, f⟩
    rw [tsum_congr hcong,
      Summable.tsum_mul_right _ (deningerWordPow_summable hα (r + 1)),
      deningerWordPow_tsum hα (r + 1), ← mul_pow, mul_comm]
  have hlt : c * deningerHeightInvSum α < 1 := by
    have hS : deningerHeightInvSum α ≤ deningerHeightInvSum 2 := deningerHeightInvSum_le hα
    have hstep : c * deningerHeightInvSum α ≤ c * deningerHeightInvSum 2 :=
      mul_le_mul_of_nonneg_left hS hcnn
    have hNle : ((N : ℝ)) ≤ (l : ℝ) := by exact_mod_cast hNl
    have hkey : ((k : ℝ) + 1) * deningerHeightInvSum 2 < (l : ℝ) + 1 := by linarith
    have hfin : c * deningerHeightInvSum 2 < 1 := by
      rw [hcdef, div_mul_eq_mul_div, div_lt_one hlpos]
      exact hkey
    linarith
  have hgeomnn : 0 ≤ c * deningerHeightInvSum α :=
    mul_nonneg hcnn (le_trans zero_le_one (one_le_deningerHeightInvSum hα))
  have hnn : ∀ w : DeningerBarWord,
      0 ≤ deningerBarKotheData.w k w / deningerBarKotheData.w l w := fun w =>
    le_of_lt (div_pos (deningerBarKotheData.pos k w) (deningerBarKotheData.pos l w))
  refine (summable_sigma_of_nonneg hnn).mpr ⟨hfiber, ?_⟩
  refine ((summable_geometric_of_lt_one hgeomnn hlt).mul_left
    (c * deningerHeightInvSum α)).congr fun r => ?_
  rw [← pow_succ']
  exact (hfiberSum r).symm

/-- **The entire word-height bar source** `𝒲_H`. -/
abbrev DeningerBarKothe : Submodule ℂ (DeningerBarWord → ℂ) :=
  DeningerKotheCarrier ℂ deningerBarKotheData

/-- The `k`-th canonical seminorm of the bar source. -/
def deningerBarSeminorm (k : ℕ) : Seminorm ℂ DeningerBarKothe :=
  deningerKotheSeminorm deningerBarKotheData k

theorem deningerBarSeminorm_apply (k : ℕ) (c : DeningerBarKothe) :
    deningerBarSeminorm k c
      = ∑' w, deningerBarKotheData.w k w * ‖(c : DeningerBarWord → ℂ) w‖ := rfl

/-! ## The two-parameter seminorms -/

/-- The two-parameter word seminorm `P_{k,R}(c) = ∑_w R^{|w|} h(w)^k |c_w|`. -/
def deningerBarSeminormR (k : ℕ) (R : ℝ) (c : DeningerBarKothe) : ℝ :=
  ∑' w, R ^ deningerBarLength w * deningerBarHeight w ^ k *
    ‖(c : DeningerBarWord → ℂ) w‖

theorem deningerBarSeminormR_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (c : DeningerBarKothe) :
    0 ≤ deningerBarSeminormR k R c :=
  tsum_nonneg fun w =>
    mul_nonneg (mul_nonneg (pow_nonneg hR _)
      (pow_nonneg (deningerBarHeight_pos w).le _)) (norm_nonneg _)

/-- Every two-parameter weight is dominated by a canonical one. -/
theorem deningerBarWeight_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) {k' : ℕ} (hk : k ≤ k')
    (hRk : R ≤ (k' : ℝ) + 1) (w : DeningerBarWord) :
    R ^ deningerBarLength w * deningerBarHeight w ^ k ≤ deningerBarKotheData.w k' w := by
  rw [deningerBarKotheData_w]
  have h1 : deningerBarHeight w ^ k ≤ deningerBarHeight w ^ k' :=
    pow_le_pow_right₀ (one_le_deningerBarHeight w) hk
  have h2 : R ^ deningerBarLength w ≤ ((k' : ℝ) + 1) ^ deningerBarLength w :=
    pow_le_pow_left₀ (by linarith) hRk _
  have hR0 : (0 : ℝ) ≤ R ^ deningerBarLength w := pow_nonneg (by linarith) _
  calc R ^ deningerBarLength w * deningerBarHeight w ^ k
      ≤ R ^ deningerBarLength w * deningerBarHeight w ^ k' :=
        mul_le_mul_of_nonneg_left h1 hR0
    _ ≤ ((k' : ℝ) + 1) ^ deningerBarLength w * deningerBarHeight w ^ k' :=
        mul_le_mul_of_nonneg_right h2 (pow_nonneg (deningerBarHeight_pos w).le _)
    _ = deningerBarHeight w ^ k' * ((k' : ℝ) + 1) ^ deningerBarLength w := by ring

/-- **Every two-parameter seminorm is finite** on the bar source, and dominated by a canonical
one. -/
theorem deningerBarSeminormR_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    Summable fun w => R ^ deningerBarLength w * deningerBarHeight w ^ k *
      ‖(c : DeningerBarWord → ℂ) w‖ := by
  obtain ⟨k', hk'⟩ := exists_nat_gt R
  refine Summable.of_nonneg_of_le
    (fun w => mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (deningerBarHeight_pos w).le _)) (norm_nonneg _))
    (fun w => ?_) (c.2 (max k k'))
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine deningerBarWeight_le hR (le_max_left _ _) ?_ w
  have hkk : ((k' : ℝ)) ≤ ((max k k' : ℕ) : ℝ) := by
    exact_mod_cast le_max_right k k'
  linarith

theorem deningerBarSeminormR_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) {k' : ℕ} (hk : k ≤ k')
    (hRk : R ≤ (k' : ℝ) + 1) (c : DeningerBarKothe) :
    deningerBarSeminormR k R c ≤ deningerBarSeminorm k' c := by
  rw [deningerBarSeminormR, deningerBarSeminorm_apply]
  refine Summable.tsum_le_tsum (fun w => ?_) (deningerBarSeminormR_summable hR c) (c.2 k')
  exact mul_le_mul_of_nonneg_right (deningerBarWeight_le hR hk hRk w) (norm_nonneg _)

end

end RHTower
