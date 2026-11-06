import GaloisForLFunctions.RHTower.Deninger.DeningerWordHeight
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.WordProducts

/-!
# The suspended word-height source

Adjoining one new letter for every *pair* of old letters — the suspension of the degree-two part —
enlarges the alphabet from the exponent lattice to the lattice plus its square.  A suspended letter
carries the product of the heights of its two constituents and counts as two ancestral letters.

The letterwise counting series of the enlarged alphabet is the one-letter series plus its square,
so it is again finite, and the word series over the enlarged alphabet is again geometric.  Raising
the height index therefore makes the Grothendieck–Pietsch ratio summable exactly as for the plain
word source: the suspended source is nuclear.

* `DeningerSusp`, `deningerSuspHeight`, `deningerSuspAncestral`, `deningerSuspChar` : the enlarged
  alphabet and its data.
* `deningerSuspHeight_summable_inv_pow` : the enlarged letterwise series converges.
* `DeningerSuspWord`, `deningerSuspWordKotheData` : the suspended word source.
* `deningerSuspWordKotheData_isNuclear` : **the suspended source is nuclear.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## A general product-series lemma -/

/-- The series of products over tuples of a fixed length is the corresponding power of the
one-letter series. -/
theorem deningerPiTuple_summable_and_tsum {A : Type*} {g : A → ℝ}
    (hg : Summable g) (hnn : ∀ m, 0 ≤ g m) (r : ℕ) :
    (Summable fun f : Fin r → A => ∏ j, g (f j)) ∧
      (∑' f : Fin r → A, ∏ j, g (f j)) = (∑' m, g m) ^ r :=
  SymmetricCharacters.wordProducts_summable_and_tsum hg hnn r

/-! ## The suspended alphabet -/

/-- A suspended letter: an old letter, or a suspended pair of old letters. -/
abbrev DeningerSusp : Type := DeningerPrimeLattice ⊕ (DeningerPrimeLattice × DeningerPrimeLattice)

instance : Inhabited DeningerSusp := ⟨Sum.inl 0⟩

/-- The height of a suspended letter: a suspended pair carries the product of the two heights. -/
def deningerSuspHeight : DeningerSusp → ℝ :=
  Sum.elim deningerHeight fun p => deningerHeight p.1 * deningerHeight p.2

/-- The ancestral length of a suspended letter: a suspended pair still counts two letters. -/
def deningerSuspAncestral : DeningerSusp → ℕ := Sum.elim (fun _ => 1) fun _ => 2

/-- The arithmetic character of a suspended letter: a suspended pair carries the sum. -/
def deningerSuspChar : DeningerSusp → DeningerPrimeLattice := Sum.elim id fun p => p.1 + p.2

@[simp]
theorem deningerSuspHeight_inl (m : DeningerPrimeLattice) :
    deningerSuspHeight (Sum.inl m) = deningerHeight m := rfl

@[simp]
theorem deningerSuspHeight_inr (p : DeningerPrimeLattice × DeningerPrimeLattice) :
    deningerSuspHeight (Sum.inr p) = deningerHeight p.1 * deningerHeight p.2 := rfl

@[simp]
theorem deningerSuspChar_inl (m : DeningerPrimeLattice) :
    deningerSuspChar (Sum.inl m) = m := rfl

@[simp]
theorem deningerSuspChar_inr (p : DeningerPrimeLattice × DeningerPrimeLattice) :
    deningerSuspChar (Sum.inr p) = p.1 + p.2 := rfl

theorem one_le_deningerSuspHeight (s : DeningerSusp) : 1 ≤ deningerSuspHeight s := by
  cases s with
  | inl m => exact one_le_deningerHeight m
  | inr p =>
      rw [deningerSuspHeight_inr]
      exact one_le_mul_of_one_le_of_one_le (one_le_deningerHeight p.1)
        (one_le_deningerHeight p.2)

theorem deningerSuspHeight_pos (s : DeningerSusp) : 0 < deningerSuspHeight s :=
  lt_of_lt_of_le zero_lt_one (one_le_deningerSuspHeight s)

/-! ## The enlarged letterwise series -/

theorem deningerSuspHeight_summable_inv_pow {α : ℕ} (hα : 2 ≤ α) :
    Summable fun s : DeningerSusp => (deningerSuspHeight s)⁻¹ ^ α := by
  have hnn : ∀ m : DeningerPrimeLattice, (0 : ℝ) ≤ (deningerHeight m)⁻¹ ^ α := fun m =>
    pow_nonneg (inv_nonneg.mpr (deningerHeight_pos m).le) α
  have h1 := deningerHeight_summable_inv_pow hα
  have h2 : Summable fun p : DeningerPrimeLattice × DeningerPrimeLattice =>
      (deningerHeight p.1)⁻¹ ^ α * (deningerHeight p.2)⁻¹ ^ α :=
    Summable.mul_of_nonneg (f := fun m : DeningerPrimeLattice => (deningerHeight m)⁻¹ ^ α)
      (g := fun m : DeningerPrimeLattice => (deningerHeight m)⁻¹ ^ α) h1 h1 hnn hnn
  have h2' : Summable fun p : DeningerPrimeLattice × DeningerPrimeLattice =>
      (deningerHeight p.1 * deningerHeight p.2)⁻¹ ^ α := by
    refine h2.congr fun p => ?_
    rw [mul_inv, mul_pow]
  have hfun : (fun s : DeningerSusp => (deningerSuspHeight s)⁻¹ ^ α)
      = Sum.elim (fun m : DeningerPrimeLattice => (deningerHeight m)⁻¹ ^ α)
        (fun p : DeningerPrimeLattice × DeningerPrimeLattice =>
          (deningerHeight p.1 * deningerHeight p.2)⁻¹ ^ α) := by
    funext s
    cases s <;> rfl
  rw [hfun]
  exact Summable.sum _ h1 h2'

/-- The letterwise height series of the suspended alphabet. -/
def deningerSuspInvSum (α : ℕ) : ℝ := ∑' s : DeningerSusp, (deningerSuspHeight s)⁻¹ ^ α

theorem one_le_deningerSuspInvSum {α : ℕ} (hα : 2 ≤ α) : 1 ≤ deningerSuspInvSum α := by
  have hterm : (deningerSuspHeight (Sum.inl (0 : DeningerPrimeLattice)))⁻¹ ^ α = 1 := by
    rw [deningerSuspHeight_inl, deningerHeight_zero, inv_one, one_pow]
  have hle := (deningerSuspHeight_summable_inv_pow hα).le_tsum (Sum.inl (0 : DeningerPrimeLattice))
    (fun j _ => pow_nonneg (inv_nonneg.mpr (deningerSuspHeight_pos j).le) α)
  rw [hterm] at hle
  exact hle

theorem deningerSuspInvSum_le {α : ℕ} (hα : 2 ≤ α) :
    deningerSuspInvSum α ≤ deningerSuspInvSum 2 := by
  refine Summable.tsum_le_tsum (fun s => ?_) (deningerSuspHeight_summable_inv_pow hα)
    (deningerSuspHeight_summable_inv_pow (le_refl 2))
  have h1 : (deningerSuspHeight s)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr (one_le_deningerSuspHeight s)
  have h0 : (0 : ℝ) ≤ (deningerSuspHeight s)⁻¹ :=
    inv_nonneg.mpr (deningerSuspHeight_pos s).le
  exact pow_le_pow_of_le_one h0 h1 hα

/-! ## Suspended words -/

/-- A word in the suspended alphabet. -/
abbrev DeningerSuspWord : Type := Σ r : ℕ, Fin r → DeningerSusp

instance : Inhabited DeningerSuspWord := ⟨⟨0, fun i => i.elim0⟩⟩

/-- The number of letters of a suspended word. -/
def deningerSuspWordLength (w : DeningerSuspWord) : ℕ := w.1

/-- The ancestral length of a suspended word: suspended letters count twice. -/
def deningerSuspWordAncestral (w : DeningerSuspWord) : ℕ := ∑ j, deningerSuspAncestral (w.2 j)

/-- The product of the heights of the letters of a suspended word. -/
def deningerSuspWordHeight (w : DeningerSuspWord) : ℝ := ∏ j, deningerSuspHeight (w.2 j)

/-- The total arithmetic character of a suspended word. -/
def deningerSuspWordChar (w : DeningerSuspWord) : DeningerPrimeLattice :=
  ∑ j, deningerSuspChar (w.2 j)

theorem one_le_deningerSuspWordHeight (w : DeningerSuspWord) : 1 ≤ deningerSuspWordHeight w :=
  Finset.one_le_prod fun j _ => one_le_deningerSuspHeight (w.2 j)

theorem deningerSuspWordHeight_pos (w : DeningerSuspWord) : 0 < deningerSuspWordHeight w :=
  lt_of_lt_of_le zero_lt_one (one_le_deningerSuspWordHeight w)

theorem deningerSuspWordPow_summable {α : ℕ} (hα : 2 ≤ α) (r : ℕ) :
    Summable fun f : Fin r → DeningerSusp => ∏ j, (deningerSuspHeight (f j))⁻¹ ^ α :=
  (deningerPiTuple_summable_and_tsum (deningerSuspHeight_summable_inv_pow hα)
    (fun s => pow_nonneg (inv_nonneg.mpr (deningerSuspHeight_pos s).le) α) r).1

theorem deningerSuspWordPow_tsum {α : ℕ} (hα : 2 ≤ α) (r : ℕ) :
    (∑' f : Fin r → DeningerSusp, ∏ j, (deningerSuspHeight (f j))⁻¹ ^ α)
      = deningerSuspInvSum α ^ r :=
  (deningerPiTuple_summable_and_tsum (deningerSuspHeight_summable_inv_pow hα)
    (fun s => pow_nonneg (inv_nonneg.mpr (deningerSuspHeight_pos s).le) α) r).2

/-! ## The suspended Köthe datum -/

/-- **The suspended word-height Köthe datum.** -/
def deningerSuspWordKotheData : DeningerKotheData DeningerSuspWord where
  w k w := deningerSuspWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerSuspWordLength w
  pos k w :=
    mul_pos (pow_pos (deningerSuspWordHeight_pos w) k) (pow_pos (by positivity) _)
  mono k w := by
    have h1 : deningerSuspWordHeight w ^ k ≤ deningerSuspWordHeight w ^ (k + 1) :=
      pow_le_pow_right₀ (one_le_deningerSuspWordHeight w) (Nat.le_succ k)
    have h2 : ((k : ℝ) + 1) ^ deningerSuspWordLength w
        ≤ (((k : ℝ) + 1) + 1) ^ deningerSuspWordLength w :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2nn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ deningerSuspWordLength w :=
      pow_nonneg (by positivity) _
    have hkk : ((k : ℝ) + 1) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    calc deningerSuspWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerSuspWordLength w
        ≤ deningerSuspWordHeight w ^ (k + 1) * ((k : ℝ) + 1) ^ deningerSuspWordLength w :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ deningerSuspWordHeight w ^ (k + 1) *
            ((((k : ℝ) + 1) + 1) ^ deningerSuspWordLength w) := by
          refine mul_le_mul_of_nonneg_left h2 ?_
          exact pow_nonneg (deningerSuspWordHeight_pos w).le _
      _ = deningerSuspWordHeight w ^ (k + 1) *
            (((k + 1 : ℕ) : ℝ) + 1) ^ deningerSuspWordLength w := by rw [hkk]

@[simp]
theorem deningerSuspWordKotheData_w (k : ℕ) (w : DeningerSuspWord) :
    deningerSuspWordKotheData.w k w
      = deningerSuspWordHeight w ^ k * ((k : ℝ) + 1) ^ deningerSuspWordLength w := rfl

/-- **The suspended word-height source.** -/
abbrev DeningerSuspKothe : Submodule ℂ (DeningerSuspWord → ℂ) :=
  DeningerKotheCarrier ℂ deningerSuspWordKotheData

/-- **The suspended source is nuclear.**  The enlarged letterwise series is the one-letter series
plus its square, so the word ratio is again geometric with ratio below one once the later height
index is large enough. -/
theorem deningerSuspWordKotheData_isNuclear : deningerSuspWordKotheData.IsNuclear := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt (((k : ℝ) + 1) * deningerSuspInvSum 2)
  refine ⟨max (k + 2) N, le_trans (Nat.le_add_right k 2) (le_max_left _ _), ?_⟩
  set l := max (k + 2) N with hldef
  have hkl : k + 2 ≤ l := le_max_left _ _
  have hNl : N ≤ l := le_max_right _ _
  set α : ℕ := l - k with hαdef
  have hα : 2 ≤ α := by omega
  have hlk : l = k + α := by omega
  set c : ℝ := ((k : ℝ) + 1) / ((l : ℝ) + 1) with hcdef
  have hlpos : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hcnn : 0 ≤ c := by
    rw [hcdef]
    positivity
  have hratio : ∀ w : DeningerSuspWord,
      deningerSuspWordKotheData.w k w / deningerSuspWordKotheData.w l w
        = (∏ j, (deningerSuspHeight (w.2 j))⁻¹ ^ α) * c ^ deningerSuspWordLength w := by
    intro w
    have hHpos := deningerSuspWordHeight_pos w
    have hsplit : (∏ j, (deningerSuspHeight (w.2 j))⁻¹ ^ α)
        = (deningerSuspWordHeight w)⁻¹ ^ α := by
      rw [Finset.prod_pow, Finset.prod_inv_distrib]
      rfl
    have hHne : deningerSuspWordHeight w ≠ 0 := ne_of_gt hHpos
    have hlne : ((l : ℝ) + 1) ≠ 0 := ne_of_gt hlpos
    have hHpow : deningerSuspWordHeight w ^ l
        = deningerSuspWordHeight w ^ k * deningerSuspWordHeight w ^ α := by
      rw [← pow_add, ← hlk]
    rw [deningerSuspWordKotheData_w, deningerSuspWordKotheData_w, hsplit, hcdef, div_pow, hHpow,
      inv_pow]
    field_simp
  have hfiber : ∀ r : ℕ, Summable fun f : Fin r → DeningerSusp =>
      deningerSuspWordKotheData.w k (⟨r, f⟩ : DeningerSuspWord) /
        deningerSuspWordKotheData.w l (⟨r, f⟩ : DeningerSuspWord) := by
    intro r
    refine ((deningerSuspWordPow_summable hα r).mul_right (c ^ r)).congr fun f => ?_
    exact (hratio ⟨r, f⟩).symm
  have hfiberSum : ∀ r : ℕ,
      (∑' f : Fin r → DeningerSusp,
        deningerSuspWordKotheData.w k (⟨r, f⟩ : DeningerSuspWord) /
          deningerSuspWordKotheData.w l (⟨r, f⟩ : DeningerSuspWord))
        = (c * deningerSuspInvSum α) ^ r := by
    intro r
    have hcong : ∀ f : Fin r → DeningerSusp,
        deningerSuspWordKotheData.w k (⟨r, f⟩ : DeningerSuspWord) /
          deningerSuspWordKotheData.w l (⟨r, f⟩ : DeningerSuspWord)
          = (∏ j, (deningerSuspHeight (f j))⁻¹ ^ α) * c ^ r := fun f => hratio ⟨r, f⟩
    rw [tsum_congr hcong,
      Summable.tsum_mul_right _ (deningerSuspWordPow_summable hα r),
      deningerSuspWordPow_tsum hα r, ← mul_pow, mul_comm]
  have hlt : c * deningerSuspInvSum α < 1 := by
    have hS : deningerSuspInvSum α ≤ deningerSuspInvSum 2 := deningerSuspInvSum_le hα
    have hstep : c * deningerSuspInvSum α ≤ c * deningerSuspInvSum 2 :=
      mul_le_mul_of_nonneg_left hS hcnn
    have hNle : ((N : ℝ)) ≤ (l : ℝ) := by exact_mod_cast hNl
    have hkey : ((k : ℝ) + 1) * deningerSuspInvSum 2 < (l : ℝ) + 1 := by linarith
    have hfin : c * deningerSuspInvSum 2 < 1 := by
      rw [hcdef, div_mul_eq_mul_div, div_lt_one hlpos]
      exact hkey
    linarith
  have hnn : ∀ w : DeningerSuspWord,
      0 ≤ deningerSuspWordKotheData.w k w / deningerSuspWordKotheData.w l w := fun w =>
    le_of_lt (div_pos (deningerSuspWordKotheData.pos k w) (deningerSuspWordKotheData.pos l w))
  refine (summable_sigma_of_nonneg hnn).mpr ⟨hfiber, ?_⟩
  refine (summable_geometric_of_lt_one
    (mul_nonneg hcnn (le_trans zero_le_one (one_le_deningerSuspInvSum hα))) hlt).congr
    fun r => ?_
  exact (hfiberSum r).symm

/-- The `k`-th seminorm of the suspended source. -/
def deningerSuspSeminorm (k : ℕ) : Seminorm ℂ DeningerSuspKothe :=
  deningerKotheSeminorm deningerSuspWordKotheData k

theorem deningerSuspSeminorm_apply (k : ℕ) (a : DeningerSuspKothe) :
    deningerSuspSeminorm k a
      = ∑' w, deningerSuspWordKotheData.w k w * ‖(a : DeningerSuspWord → ℂ) w‖ := rfl

end

end RHTower
