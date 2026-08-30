import GaloisForLFunctions.HTGeometry.ConstitutiveCausalJordanFormation

/-!
# Signed drift words, their positive refinement, and endpoint blindness

Word-level layer of the causal Jordan formation card `ULF-CJFM-1`.

* `(CJF.1)`–`(CJF.8)`: a finite signed drift word, its two positive legs, the recovered
  displacement, total variation, cancellation reserve, and the exact endpoint fibre.
* `(CJF.9)`–`(CJF.16)`: strict leg additivity under concatenation, the reserve-generation law with
  its cancellation-birth term, the classification of that term, and the monoid isomorphism from the
  additive positive cone onto the twisted signed chart.
* `(CJF.17)`–`(CJF.19)`: the functional-equation reflection as an involutive automorphism.
* `(CJF.31)`–`(CJF.33)`: closed words carry strictly positive reserve.
* `(CJF.34)`–`(CJF.41)`: exponential-family observers, their word action, common Markov recovery,
  and the exact blindness of every endpoint information quantity to the reserve coordinate.

Everything here is unconditional.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-! ## 1. Signed drift words -/

namespace DriftWord

/-- `(CJF.2)` total positive leg of a signed drift word. -/
def posLeg (w : List ℝ) : ℝ := (w.map fun d => max d 0).sum

/-- `(CJF.2)` total negative leg of a signed drift word. -/
def negLeg (w : List ℝ) : ℝ := (w.map fun d => max (-d) 0).sum

/-- `(CJF.3)` recovered signed displacement. -/
def displacement (w : List ℝ) : ℝ := w.sum

/-- `(CJF.4)` total variation of a signed drift word. -/
def variation (w : List ℝ) : ℝ := (w.map fun d => |d|).sum

/-- `(CJF.5)` cancellation reserve. -/
def reserve (w : List ℝ) : ℝ := min (posLeg w) (negLeg w)

/-- `(CJF.28)` least common causal delay of a signed drift word. -/
def commonDelay (w : List ℝ) : ℝ := max (posLeg w) (negLeg w)

/-- `(CJF.17)` functional-equation reflection of a drift word. -/
def reflectWord (w : List ℝ) : List ℝ := w.map fun d => -d

@[simp] theorem posLeg_nil : posLeg [] = 0 := rfl
@[simp] theorem negLeg_nil : negLeg [] = 0 := rfl

@[simp] theorem posLeg_cons (d : ℝ) (w : List ℝ) :
    posLeg (d :: w) = max d 0 + posLeg w := rfl

@[simp] theorem negLeg_cons (d : ℝ) (w : List ℝ) :
    negLeg (d :: w) = max (-d) 0 + negLeg w := rfl

@[simp] theorem variation_cons (d : ℝ) (w : List ℝ) :
    variation (d :: w) = |d| + variation w := rfl

theorem posLeg_nonneg (w : List ℝ) : 0 ≤ posLeg w := by
  induction w with
  | nil => simp
  | cons d t ih => exact add_nonneg (le_max_right _ _) ih

theorem negLeg_nonneg (w : List ℝ) : 0 ≤ negLeg w := by
  induction w with
  | nil => simp
  | cons d t ih => exact add_nonneg (le_max_right _ _) ih

/-- `(CJF.3)` the two legs recover the signed displacement. -/
theorem posLeg_sub_negLeg (w : List ℝ) : posLeg w - negLeg w = displacement w := by
  induction w with
  | nil => simp [displacement]
  | cons d t ih =>
      have hd : max d 0 - max (-d) 0 = d := by
        rcases le_total 0 d with h | h
        · rw [max_eq_left h, max_eq_right (by linarith : -d ≤ (0:ℝ))]; ring
        · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -d)]; ring
      have ih' : posLeg t - negLeg t = t.sum := ih
      simp only [posLeg_cons, negLeg_cons, displacement, List.sum_cons]
      linarith

/-- `(CJF.4)` the two legs recover the total variation. -/
theorem posLeg_add_negLeg (w : List ℝ) : posLeg w + negLeg w = variation w := by
  induction w with
  | nil => simp [variation]
  | cons d t ih =>
      have hd : max d 0 + max (-d) 0 = |d| := by
        rcases le_total 0 d with h | h
        · rw [max_eq_left h, max_eq_right (by linarith : -d ≤ (0:ℝ)), abs_of_nonneg h]; ring
        · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -d), abs_of_nonpos h]; ring
      simp only [posLeg_cons, negLeg_cons, variation_cons]
      rw [← ih, ← hd]; ring

theorem variation_nonneg (w : List ℝ) : 0 ≤ variation w := by
  rw [← posLeg_add_negLeg]; exact add_nonneg (posLeg_nonneg w) (negLeg_nonneg w)

/-- `(CJF.9)` positive legs add strictly under concatenation. -/
@[simp] theorem posLeg_append (u v : List ℝ) : posLeg (u ++ v) = posLeg u + posLeg v := by
  simp [posLeg, List.sum_append]

/-- `(CJF.9)` negative legs add strictly under concatenation. -/
@[simp] theorem negLeg_append (u v : List ℝ) : negLeg (u ++ v) = negLeg u + negLeg v := by
  simp [negLeg, List.sum_append]

@[simp] theorem displacement_append (u v : List ℝ) :
    displacement (u ++ v) = displacement u + displacement v := by
  simp [displacement, List.sum_append]

@[simp] theorem variation_append (u v : List ℝ) :
    variation (u ++ v) = variation u + variation v := by
  simp [variation, List.sum_append]

/-- The positive formation refinement of a drift word. -/
def formation (w : List ℝ) : CausalJordanFormation :=
  ⟨posLeg w, negLeg w, posLeg_nonneg w, negLeg_nonneg w⟩

@[simp] theorem formation_positive (w : List ℝ) : (formation w).positive = posLeg w := rfl

@[simp] theorem formation_negative (w : List ℝ) : (formation w).negative = negLeg w := rfl

@[simp] theorem formation_visible (w : List ℝ) :
    CausalJordanFormation.visible (formation w) = displacement w :=
  posLeg_sub_negLeg w

@[simp] theorem formation_reserve (w : List ℝ) :
    CausalJordanFormation.reserve (formation w) = reserve w := rfl

@[simp] theorem formation_commonDelay (w : List ℝ) :
    CausalJordanFormation.commonDelay (formation w) = commonDelay w := rfl

/-- `(CJF.9)` concatenation of words is strict formation fusion. -/
theorem formation_append (u v : List ℝ) :
    formation (u ++ v) = CausalJordanFormation.fuse (formation u) (formation v) := by
  simp [formation, CausalJordanFormation.fuse]

@[simp] theorem posLeg_reflectWord (w : List ℝ) : posLeg (reflectWord w) = negLeg w := by
  simp [posLeg, negLeg, reflectWord, Function.comp_def]

@[simp] theorem negLeg_reflectWord (w : List ℝ) : negLeg (reflectWord w) = posLeg w := by
  simp [posLeg, negLeg, reflectWord, Function.comp_def]

/-- `(CJF.18)` reflection swaps the two positive legs. -/
theorem formation_reflectWord (w : List ℝ) :
    formation (reflectWord w) = CausalJordanFormation.reflect (formation w) := by
  simp [formation, CausalJordanFormation.reflect]

theorem reserve_nonneg (w : List ℝ) : 0 ≤ reserve w :=
  le_min (posLeg_nonneg w) (negLeg_nonneg w)

/-- `(CJF.5)` reserve is half the variation not paid by visible displacement. -/
theorem two_mul_reserve (w : List ℝ) :
    2 * reserve w = variation w - |displacement w| := by
  have h := CausalJordanFormation.two_mul_reserve_eq (formation w)
  rw [formation_reserve, formation_visible, formation_positive, formation_negative,
    posLeg_add_negLeg] at h
  exact h

/-- `(CJF.6)` the positive leg is the visible positive part plus the reserve. -/
theorem posLeg_eq (w : List ℝ) : posLeg w = max (displacement w) 0 + reserve w := by
  have h := two_mul_reserve w
  have hv := posLeg_add_negLeg w
  have hd := posLeg_sub_negLeg w
  rcases le_total 0 (displacement w) with hs | hs
  · rw [max_eq_left hs]; rw [abs_of_nonneg hs] at h; linarith
  · rw [max_eq_right hs]; rw [abs_of_nonpos hs] at h; linarith

/-- `(CJF.6)` the negative leg is the visible negative part plus the reserve. -/
theorem negLeg_eq (w : List ℝ) : negLeg w = max (-displacement w) 0 + reserve w := by
  have h := two_mul_reserve w
  have hv := posLeg_add_negLeg w
  have hd := posLeg_sub_negLeg w
  rcases le_total 0 (displacement w) with hs | hs
  · rw [max_eq_right (by linarith : -displacement w ≤ (0:ℝ))]
    rw [abs_of_nonneg hs] at h; linarith
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ -displacement w)]
    rw [abs_of_nonpos hs] at h; linarith

/-- `(CJF.29)` least common causal delay is visible displacement plus hidden reserve. -/
theorem commonDelay_eq (w : List ℝ) : commonDelay w = |displacement w| + reserve w := by
  have h := CausalJordanFormation.commonDelay_eq_abs_visible_add_reserve (formation w)
  rw [formation_commonDelay, formation_reserve, formation_visible] at h
  exact h

end DriftWord

/-! ## 2. The exact reserve-generation law -/

/-- `(CJF.12)` cancellation birth vanishes exactly on aligned visible laws. -/
theorem cancellationBirth_eq_zero_iff (x y : ℝ) :
    CausalJordanFormation.cancellationBirth x y = 0 ↔ 0 ≤ x * y := by
  have key : |x + y| = |x| + |y| ↔ 0 ≤ x * y := by
    rw [abs_add_eq_add_abs_iff]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact mul_nonneg hx hy
      · nlinarith
    · intro h
      rcases le_total 0 x with hx | hx
      · rcases le_total 0 y with hy | hy
        · exact Or.inl ⟨hx, hy⟩
        · rcases eq_or_lt_of_le hx with hx0 | hx0
          · exact Or.inr ⟨le_of_eq hx0.symm, hy⟩
          · have : 0 ≤ y := nonneg_of_mul_nonneg_right h hx0
            exact Or.inl ⟨hx, this⟩
      · rcases le_total 0 y with hy | hy
        · rcases eq_or_lt_of_le hy with hy0 | hy0
          · exact Or.inr ⟨hx, le_of_eq hy0.symm⟩
          · have hxy : 0 ≤ x := by nlinarith
            exact Or.inl ⟨hxy, hy⟩
        · exact Or.inr ⟨hx, hy⟩
  unfold CausalJordanFormation.cancellationBirth
  rw [← key]
  constructor <;> intro h <;> linarith

/-- `(CJF.13)` opposite visible laws create exactly the smaller magnitude as new reserve. -/
theorem cancellationBirth_of_mul_neg {x y : ℝ} (h : x * y < 0) :
    CausalJordanFormation.cancellationBirth x y = min |x| |y| := by
  unfold CausalJordanFormation.cancellationBirth
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : 0 < y := by nlinarith
    rw [abs_of_neg hx, abs_of_pos hy]
    rcases le_total 0 (x + y) with hs | hs
    · rw [abs_of_nonneg hs, min_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos hs, min_eq_right (by linarith)]; ring
  · exfalso; rw [hx] at h; simp at h
  · have hy : y < 0 := by nlinarith
    rw [abs_of_pos hx, abs_of_neg hy]
    rcases le_total 0 (x + y) with hs | hs
    · rw [abs_of_nonneg hs, min_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos hs, min_eq_left (by linarith)]; ring

namespace DriftWord

/-- **Theorem 3.1, `(CJF.11)`.**  Visible displacement is additive and reserve acquires exactly the
cancellation-birth defect. -/
theorem displacement_reserve_append (u v : List ℝ) :
    displacement (u ++ v) = displacement u + displacement v ∧
      reserve (u ++ v) =
        reserve u + reserve v +
          CausalJordanFormation.cancellationBirth (displacement u) (displacement v) := by
  refine ⟨displacement_append u v, ?_⟩
  have h := CausalJordanFormation.reserve_fuse (formation u) (formation v)
  rw [← formation_append] at h
  rw [formation_reserve, formation_reserve, formation_reserve, formation_visible,
    formation_visible] at h
  exact h

/-- Opposite drift strictly increases reserve. -/
theorem reserve_append_lt {u v : List ℝ} (h : displacement u * displacement v < 0) :
    reserve u + reserve v < reserve (u ++ v) := by
  rw [(displacement_reserve_append u v).2, cancellationBirth_of_mul_neg h]
  have hx : displacement u ≠ 0 := by rintro h0; rw [h0] at h; simp at h
  have hy : displacement v ≠ 0 := by rintro h0; rw [h0] at h; simp at h
  have : 0 < min |displacement u| |displacement v| :=
    lt_min (abs_pos.mpr hx) (abs_pos.mpr hy)
  linarith

/-- `(CJF.19)` reflection fixes reserve. -/
@[simp] theorem reserve_reflectWord (w : List ℝ) : reserve (reflectWord w) = reserve w := by
  simp [reserve, min_comm]

/-- `(CJF.18)` reflection negates visible displacement. -/
@[simp] theorem displacement_reflectWord (w : List ℝ) :
    displacement (reflectWord w) = -displacement w := by
  simp only [displacement, reflectWord]
  induction w with
  | nil => simp
  | cons d t ih => simp [ih]; ring

/-- Reflection fixes the least common causal delay. -/
@[simp] theorem commonDelay_reflectWord (w : List ℝ) :
    commonDelay (reflectWord w) = commonDelay w := by
  simp [commonDelay, max_comm]

/-- Reflection is an involution on drift words. -/
@[simp] theorem reflectWord_reflectWord (w : List ℝ) : reflectWord (reflectWord w) = w := by
  simp [reflectWord, List.map_map]

/-- **Theorem 4.1.**  Reflection is an involutive automorphism of the refined formation law. -/
theorem reflectWord_append (u v : List ℝ) :
    reflectWord (u ++ v) = reflectWord u ++ reflectWord v := by
  simp [reflectWord]

/-- `(CJF.19)` the cancellation cocycle is reflection invariant. -/
theorem cancellationBirth_neg (x y : ℝ) :
    CausalJordanFormation.cancellationBirth (-x) (-y) =
      CausalJordanFormation.cancellationBirth x y := by
  unfold CausalJordanFormation.cancellationBirth
  rw [abs_neg, abs_neg, ← neg_add, abs_neg]

end DriftWord

/-! ## 3. The twisted signed chart and its monoid isomorphism -/

/-- `(CJF.14)` composition law of the signed formation chart. -/
def formationStar (z w : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + w.1, z.2 + w.2 + CausalJordanFormation.cancellationBirth z.1 w.1)

theorem formationStar_comm (z w : ℝ × ℝ) : formationStar z w = formationStar w z := by
  unfold formationStar CausalJordanFormation.cancellationBirth
  rw [Prod.mk.injEq]
  constructor
  · ring
  · rw [add_comm z.1 w.1]; ring

theorem formationStar_assoc (z w v : ℝ × ℝ) :
    formationStar (formationStar z w) v = formationStar z (formationStar w v) := by
  have hc := CausalJordanFormation.cancellationBirth_cocycle z.1 w.1 v.1
  unfold formationStar
  rw [Prod.mk.injEq]
  refine ⟨by simp [add_assoc], ?_⟩
  simp only
  linarith

@[simp] theorem cancellationBirth_zero_left (y : ℝ) :
    CausalJordanFormation.cancellationBirth 0 y = 0 := by
  unfold CausalJordanFormation.cancellationBirth; simp

@[simp] theorem cancellationBirth_zero_right (x : ℝ) :
    CausalJordanFormation.cancellationBirth x 0 = 0 := by
  unfold CausalJordanFormation.cancellationBirth; simp

theorem formationStar_zero_left (z : ℝ × ℝ) : formationStar (0, 0) z = z := by
  unfold formationStar; simp

theorem formationStar_zero_right (z : ℝ × ℝ) : formationStar z (0, 0) = z := by
  unfold formationStar; simp

/-- The chart `(CJF.15)` sending a positive formation state to its signed/reserve coordinates. -/
def formationChart (s : CausalJordanFormation) : ℝ × ℝ :=
  (CausalJordanFormation.visible s, CausalJordanFormation.reserve s)

/-- The inverse chart, defined on all of `ℝ × ℝ` by clipping the reserve coordinate. -/
def formationUnchart (z : ℝ × ℝ) : CausalJordanFormation where
  positive := max z.1 0 + max z.2 0
  negative := max (-z.1) 0 + max z.2 0
  positive_nonneg := add_nonneg (le_max_right _ _) (le_max_right _ _)
  negative_nonneg := add_nonneg (le_max_right _ _) (le_max_right _ _)

theorem formationUnchart_formationChart (s : CausalJordanFormation) :
    formationUnchart (formationChart s) = s := by
  have hr : 0 ≤ CausalJordanFormation.reserve s := le_min s.positive_nonneg s.negative_nonneg
  have hvis : CausalJordanFormation.visible s = s.positive - s.negative := rfl
  have hres : CausalJordanFormation.reserve s = min s.positive s.negative := rfl
  have h1 : max (CausalJordanFormation.visible s) 0 + max (CausalJordanFormation.reserve s) 0
      = s.positive := by
    rw [max_eq_left hr, hvis, hres]
    rcases le_total s.positive s.negative with hpn | hpn
    · rw [min_eq_left hpn, max_eq_right (by linarith : s.positive - s.negative ≤ (0:ℝ))]; ring
    · rw [min_eq_right hpn, max_eq_left (by linarith : (0:ℝ) ≤ s.positive - s.negative)]; ring
  have h2 : max (-CausalJordanFormation.visible s) 0 + max (CausalJordanFormation.reserve s) 0
      = s.negative := by
    rw [max_eq_left hr, hvis, hres]
    rcases le_total s.positive s.negative with hpn | hpn
    · rw [min_eq_left hpn, max_eq_left (by linarith : (0:ℝ) ≤ -(s.positive - s.negative))]; ring
    · rw [min_eq_right hpn, max_eq_right (by linarith : -(s.positive - s.negative) ≤ (0:ℝ))]; ring
  cases s with
  | mk p n hp hn =>
    simp only [formationUnchart, formationChart, CausalJordanFormation.mk.injEq]
    exact ⟨h1, h2⟩

theorem formationChart_formationUnchart {z : ℝ × ℝ} (hz : 0 ≤ z.2) :
    formationChart (formationUnchart z) = z := by
  have hvis : CausalJordanFormation.visible (formationUnchart z)
      = (max z.1 0 + max z.2 0) - (max (-z.1) 0 + max z.2 0) := rfl
  have hres : CausalJordanFormation.reserve (formationUnchart z)
      = min (max z.1 0 + max z.2 0) (max (-z.1) 0 + max z.2 0) := rfl
  rw [formationChart, hvis, hres, max_eq_left hz, Prod.ext_iff]
  rcases le_total 0 z.1 with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -z.1 ≤ (0:ℝ))]
    refine ⟨by ring, ?_⟩
    rw [min_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -z.1)]
    refine ⟨by ring, ?_⟩
    rw [min_eq_left (by linarith)]
    ring

/-- **`(CJF.15)`.**  The signed chart is a monoid isomorphism from the additive positive cone onto
the twisted chart `(ℱ, ⋆)`. -/
theorem formationChart_fuse (s t : CausalJordanFormation) :
    formationChart (CausalJordanFormation.fuse s t) =
      formationStar (formationChart s) (formationChart t) := by
  have hv := CausalJordanFormation.visible_fuse s t
  have hr := CausalJordanFormation.reserve_fuse s t
  simp only [formationChart, formationStar, Prod.mk.injEq]
  exact ⟨hv, hr⟩

/-- The chart is a bijection from positive formation states onto the reserve half-space. -/
def formationChartEquiv : CausalJordanFormation ≃ {z : ℝ × ℝ // 0 ≤ z.2} where
  toFun s := ⟨formationChart s, le_min s.positive_nonneg s.negative_nonneg⟩
  invFun z := formationUnchart z.1
  left_inv s := formationUnchart_formationChart s
  right_inv z := Subtype.ext (formationChart_formationUnchart z.2)


/-! ## 4. Closed observation with strictly positive formation reserve -/

namespace DriftWord

/-- **Corollary 6.1, `(CJF.32)`–`(CJF.33)`.**  A closed word splits its total variation evenly
between the two positive legs; its reserve and its least common causal delay coincide. -/
theorem closed_word_reserve {w : List ℝ} (h : displacement w = 0) :
    posLeg w = negLeg w ∧ posLeg w = variation w / 2 ∧
      reserve w = variation w / 2 ∧ commonDelay w = reserve w := by
  have hd := posLeg_sub_negLeg w
  have hv := posLeg_add_negLeg w
  rw [h] at hd
  have heq : posLeg w = negLeg w := by linarith
  have hhalf : posLeg w = variation w / 2 := by linarith
  refine ⟨heq, hhalf, ?_, ?_⟩
  · rw [reserve, ← heq, min_self]; exact hhalf
  · rw [reserve, commonDelay, ← heq, min_self, max_self]

theorem variation_pos {w : List ℝ} (hne : w ≠ []) (hnz : ∀ d ∈ w, d ≠ 0) : 0 < variation w := by
  cases w with
  | nil => exact absurd rfl hne
  | cons d t =>
      have hd : 0 < |d| := abs_pos.mpr (hnz d (List.mem_cons_self ..))
      have ht : 0 ≤ variation t := variation_nonneg t
      rw [variation_cons]; linarith

/-- Every nonempty closed word has strictly positive hidden formation reserve. -/
theorem reserve_pos_of_closed {w : List ℝ} (hne : w ≠ []) (hnz : ∀ d ∈ w, d ≠ 0)
    (h : displacement w = 0) : 0 < reserve w := by
  have hv := variation_pos hne hnz
  rw [(closed_word_reserve h).2.2.1]
  linarith

/-- `(CJF.40)`  Every endpoint fibre contains a word of every prescribed reserve. -/
theorem exists_word_displacement_reserve (D r : ℝ) (hr : 0 ≤ r) :
    ∃ w : List ℝ, displacement w = D ∧ reserve w = r ∧ variation w = |D| + 2 * r := by
  have hmD : (0:ℝ) ≤ max D 0 := le_max_right _ _
  have hmD' : (0:ℝ) ≤ max (-D) 0 := le_max_right _ _
  have h1 : (0:ℝ) ≤ max D 0 + r := by linarith
  have h1' : -(max D 0 + r) ≤ (0:ℝ) := by linarith
  have h2 : (0:ℝ) ≤ max (-D) 0 + r := by linarith
  have h2' : -(max (-D) 0 + r) ≤ (0:ℝ) := by linarith
  refine ⟨[max D 0 + r, -(max (-D) 0 + r)], ?_, ?_, ?_⟩
  · have hD : displacement [max D 0 + r, -(max (-D) 0 + r)]
        = (max D 0 + r) + -(max (-D) 0 + r) := by simp [displacement]
    rw [hD]
    rcases le_total 0 D with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -D ≤ (0:ℝ))]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -D)]; ring
  · have hp : posLeg [max D 0 + r, -(max (-D) 0 + r)] = max D 0 + r := by
      rw [posLeg]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [max_eq_left h1, max_eq_right h2']
      ring
    have hn : negLeg [max D 0 + r, -(max (-D) 0 + r)] = max (-D) 0 + r := by
      rw [negLeg]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, neg_neg]
      rw [max_eq_right h1', max_eq_left h2]
      ring
    rw [reserve, hp, hn]
    rcases le_total 0 D with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -D ≤ (0:ℝ))]
      rw [min_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -D)]
      rw [min_eq_left (by linarith)]; ring
  · have hvar : variation [max D 0 + r, -(max (-D) 0 + r)]
        = |max D 0 + r| + |-(max (-D) 0 + r)| := by simp [variation]
    rw [hvar, abs_neg, abs_of_nonneg h1, abs_of_nonneg h2]
    rcases le_total 0 D with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -D ≤ (0:ℝ)), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -D), abs_of_nonpos h]; ring

end DriftWord

/-! ## 5. Endpoint observers, common recovery, and exact reserve blindness -/

section ExponentialObserver

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(CJF.34)`  Exponential partition response of a source law against a real statistic. -/
def partitionResponse (μ : Measure Ω) (X : Ω → ℝ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (u * X ω)) ∂μ

/-- Unnormalized exponential intervention by one signed drift. -/
def driftTilt (μ : Measure Ω) (X : Ω → ℝ) (u : ℝ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (Real.exp (u * X ω))

/-- `(CJF.35)`  Exponential-family endpoint observer. -/
def expObserver (μ : Measure Ω) (X : Ω → ℝ) (u : ℝ) : Measure Ω :=
  (partitionResponse μ X u)⁻¹ • driftTilt μ X u

theorem measurable_expDensity {X : Ω → ℝ} (hX : Measurable X) (u : ℝ) :
    Measurable fun ω => ENNReal.ofReal (Real.exp (u * X ω)) := by fun_prop

@[simp] theorem driftTilt_zero (μ : Measure Ω) (X : Ω → ℝ) : driftTilt μ X 0 = μ := by
  unfold driftTilt
  simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one]
  exact withDensity_one

/-- Sequential unnormalized interventions compose additively. -/
theorem driftTilt_driftTilt {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u v : ℝ) :
    driftTilt (driftTilt μ X u) X v = driftTilt μ X (u + v) := by
  unfold driftTilt
  rw [← withDensity_mul _ (measurable_expDensity hX u) (measurable_expDensity hX v)]
  congr 1
  funext ω
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_mul]

theorem partitionResponse_driftTilt {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u v : ℝ) :
    partitionResponse (driftTilt μ X u) X v = partitionResponse μ X (u + v) := by
  unfold partitionResponse driftTilt
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_expDensity hX u)
    (measurable_expDensity hX v)]
  refine lintegral_congr fun ω => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_mul]

theorem partitionResponse_smul (c : ℝ≥0∞) (μ : Measure Ω) (X : Ω → ℝ) (u : ℝ) :
    partitionResponse (c • μ) X u = c * partitionResponse μ X u :=
  lintegral_smul_measure _ _

theorem driftTilt_smul (c : ℝ≥0∞) (μ : Measure Ω) (X : Ω → ℝ) (u : ℝ) :
    driftTilt (c • μ) X u = c • driftTilt μ X u :=
  withDensity_smul_measure _ _

/-- The normalized observer is insensitive to the total mass of its source. -/
theorem expObserver_smul {c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (μ : Measure Ω) (X : Ω → ℝ)
    (u : ℝ) : expObserver (c • μ) X u = expObserver μ X u := by
  unfold expObserver
  rw [partitionResponse_smul, driftTilt_smul,
    ENNReal.mul_inv (Or.inl hc) (Or.inl hc'), smul_smul, mul_assoc,
    mul_comm (partitionResponse μ X u)⁻¹ c, ← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul]

/-- **`(CJF.36)`.**  Two admitted exponential interventions compose by adding their drifts. -/
theorem expObserver_expObserver {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) {u : ℝ}
    (h0 : partitionResponse μ X u ≠ 0) (htop : partitionResponse μ X u ≠ ⊤) (v : ℝ) :
    expObserver (expObserver μ X u) X v = expObserver μ X (u + v) := by
  have hstep : expObserver (expObserver μ X u) X v = expObserver (driftTilt μ X u) X v := by
    rw [expObserver]
    exact expObserver_smul (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0) _ _ _
  rw [hstep, expObserver, partitionResponse_driftTilt hX, driftTilt_driftTilt hX, expObserver]

/-- Sequential unnormalized action of a signed drift word. -/
def rawWordAction (X : Ω → ℝ) (μ : Measure Ω) (w : List ℝ) : Measure Ω :=
  w.foldl (fun ρ d => driftTilt ρ X d) μ

/-- Sequential normalized action of a signed drift word. -/
def observerWordAction (X : Ω → ℝ) (μ : Measure Ω) (w : List ℝ) : Measure Ω :=
  w.foldl (fun ρ d => expObserver ρ X d) μ

/-- **Unconditional word law.**  The whole unnormalized history acts by the recovered
displacement only. -/
theorem rawWordAction_eq {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (w : List ℝ) :
    rawWordAction X μ w = driftTilt μ X (DriftWord.displacement w) := by
  induction w generalizing μ with
  | nil => simp [rawWordAction, DriftWord.displacement]
  | cons d t ih =>
      rw [rawWordAction, List.foldl_cons]
      have : t.foldl (fun ρ e => driftTilt ρ X e) (driftTilt μ X d)
          = rawWordAction X (driftTilt μ X d) t := rfl
      rw [this, ih, driftTilt_driftTilt hX]
      simp [DriftWord.displacement]

/-- **Theorem 7.1, `(CJF.38)` first identity.**  The normalized endpoint observer after a whole
signed drift word depends on the word only through its recovered displacement. -/
theorem observerWordAction_expObserver {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u : ℝ)
    (w : List ℝ)
    (hadm : ∀ v ∈ List.scanl (· + ·) u w,
      partitionResponse μ X v ≠ 0 ∧ partitionResponse μ X v ≠ ⊤) :
    observerWordAction X (expObserver μ X u) w = expObserver μ X (u + DriftWord.displacement w) := by
  induction w generalizing u with
  | nil => simp [observerWordAction, DriftWord.displacement]
  | cons d t ih =>
      have hu := hadm u (by simp)
      rw [observerWordAction, List.foldl_cons]
      have hstep : expObserver (expObserver μ X u) X d = expObserver μ X (u + d) :=
        expObserver_expObserver hX μ hu.1 hu.2 d
      have hfold : t.foldl (fun ρ e => expObserver ρ X e) (expObserver (expObserver μ X u) X d)
          = observerWordAction X (expObserver μ X (u + d)) t := by rw [hstep]; rfl
      rw [hfold, ih (u + d) ?_]
      · simp [DriftWord.displacement, add_assoc]
      · intro v hv
        exact hadm v (by simp [List.scanl_cons, hv])

/-- The admitted normalized observer is a probability law. -/
theorem expObserver_univ (μ : Measure Ω) (X : Ω → ℝ) {u : ℝ}
    (h0 : partitionResponse μ X u ≠ 0) (htop : partitionResponse μ X u ≠ ⊤) :
    expObserver μ X u Set.univ = 1 := by
  have hd : driftTilt μ X u Set.univ = partitionResponse μ X u := by
    rw [driftTilt, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rfl
  rw [expObserver, Measure.smul_apply, hd, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

theorem isProbabilityMeasure_expObserver (μ : Measure Ω) (X : Ω → ℝ) {u : ℝ}
    (h0 : partitionResponse μ X u ≠ 0) (htop : partitionResponse μ X u ≠ ⊤) :
    IsProbabilityMeasure (expObserver μ X u) :=
  ⟨expObserver_univ μ X h0 htop⟩

variable {H : Type*} [MeasurableSpace H]

/-- **Theorem 7.1, `(CJF.38)` second identity.**  The recovered packet after a whole signed drift
word depends on the word only through its recovered displacement. -/
theorem splitFormation_observerWordAction {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u : ℝ)
    (w : List ℝ) (κ : Kernel Ω H)
    (hadm : ∀ v ∈ List.scanl (· + ·) u w,
      partitionResponse μ X v ≠ 0 ∧ partitionResponse μ X v ≠ ⊤) :
    splitFormation (observerWordAction X (expObserver μ X u) w) κ
      = splitFormation (expObserver μ X (u + DriftWord.displacement w)) κ := by
  rw [observerWordAction_expObserver hX μ u w hadm]

/-- **Theorem 7.1, `(CJF.39)`.**  A closed word returns both the endpoint observer and the whole
recovered packet exactly to their starting laws, so every directed and symmetric endpoint
information quantity vanishes. -/
theorem closedWord_information_blind {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u : ℝ)
    (w : List ℝ) (κ : Kernel Ω H) [IsMarkovKernel κ]
    (hadm : ∀ v ∈ List.scanl (· + ·) u w,
      partitionResponse μ X v ≠ 0 ∧ partitionResponse μ X v ≠ ⊤)
    (hclosed : DriftWord.displacement w = 0) :
    observerWordAction X (expObserver μ X u) w = expObserver μ X u ∧
      splitFormation (observerWordAction X (expObserver μ X u) w) κ
        = splitFormation (expObserver μ X u) κ ∧
      klDiv (splitFormation (observerWordAction X (expObserver μ X u) w) κ)
        (splitFormation (expObserver μ X u) κ) = 0 ∧
      formationJeffreys (splitFormation (observerWordAction X (expObserver μ X u) w) κ)
        (splitFormation (expObserver μ X u) κ) = 0 := by
  have hu := hadm u (by cases w <;> simp)
  haveI : IsProbabilityMeasure (expObserver μ X u) :=
    isProbabilityMeasure_expObserver μ X hu.1 hu.2
  have hobs : observerWordAction X (expObserver μ X u) w = expObserver μ X u := by
    rw [observerWordAction_expObserver hX μ u w hadm, hclosed, add_zero]
  haveI : IsProbabilityMeasure (splitFormation (expObserver μ X u) κ) := by
    unfold splitFormation
    infer_instance
  have hsplit : splitFormation (observerWordAction X (expObserver μ X u) w) κ
      = splitFormation (expObserver μ X u) κ := by rw [hobs]
  refine ⟨hobs, hsplit, ?_, ?_⟩
  · rw [hsplit]
    exact klDiv_self _
  · rw [hsplit, formationJeffreys, klDiv_self, add_zero]

/-- **Theorem 7.1, `(CJF.40)`.**  Reserve is completely unbounded inside a fixed endpoint fibre:
two words with the same recovered displacement and arbitrarily different reserves produce the same
endpoint observer and the same recovered packet. -/
theorem endpoint_blind_to_reserve {X : Ω → ℝ} (hX : Measurable X) (μ : Measure Ω) (u : ℝ)
    (κ : Kernel Ω H) (D r r' : ℝ) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    ∃ w w' : List ℝ,
      DriftWord.reserve w = r ∧ DriftWord.reserve w' = r' ∧
      DriftWord.displacement w = D ∧ DriftWord.displacement w' = D ∧
      rawWordAction X μ w = rawWordAction X μ w' ∧
      (∀ (_hadm : ∀ v ∈ List.scanl (· + ·) u w,
            partitionResponse μ X v ≠ 0 ∧ partitionResponse μ X v ≠ ⊤)
         (_hadm' : ∀ v ∈ List.scanl (· + ·) u w',
            partitionResponse μ X v ≠ 0 ∧ partitionResponse μ X v ≠ ⊤),
        observerWordAction X (expObserver μ X u) w
            = observerWordAction X (expObserver μ X u) w' ∧
          splitFormation (observerWordAction X (expObserver μ X u) w) κ
            = splitFormation (observerWordAction X (expObserver μ X u) w') κ) := by
  obtain ⟨w, hw1, hw2, -⟩ := DriftWord.exists_word_displacement_reserve D r hr
  obtain ⟨w', hw1', hw2', -⟩ := DriftWord.exists_word_displacement_reserve D r' hr'
  refine ⟨w, w', hw2, hw2', hw1, hw1', ?_, ?_⟩
  · rw [rawWordAction_eq hX, rawWordAction_eq hX, hw1, hw1']
  · intro hadm hadm'
    have h1 := observerWordAction_expObserver hX μ u w hadm
    have h2 := observerWordAction_expObserver hX μ u w' hadm'
    rw [h1, h2, hw1, hw1']
    exact ⟨rfl, rfl⟩

end ExponentialObserver

/-- **Causal Jordan word capstone.**  On finite signed drift words: the two positive legs add
strictly while the signed chart acquires exactly the cancellation-birth cocycle; that cocycle
vanishes precisely on aligned displacements and equals the smaller magnitude otherwise; reflection
is an involutive automorphism fixing reserve and common delay; every nonempty closed word carries
strictly positive reserve; and every endpoint fibre carries words of arbitrary reserve. -/
theorem causalJordanWordFormation_certificate :
    (∀ u v : List ℝ,
        DriftWord.displacement (u ++ v) = DriftWord.displacement u + DriftWord.displacement v ∧
        DriftWord.reserve (u ++ v) = DriftWord.reserve u + DriftWord.reserve v +
          CausalJordanFormation.cancellationBirth
            (DriftWord.displacement u) (DriftWord.displacement v)) ∧
      (∀ x y : ℝ, CausalJordanFormation.cancellationBirth x y = 0 ↔ 0 ≤ x * y) ∧
      (∀ x y : ℝ, x * y < 0 →
        CausalJordanFormation.cancellationBirth x y = min |x| |y|) ∧
      (∀ w : List ℝ, DriftWord.displacement (DriftWord.reflectWord w) = -DriftWord.displacement w ∧
        DriftWord.reserve (DriftWord.reflectWord w) = DriftWord.reserve w ∧
        DriftWord.commonDelay (DriftWord.reflectWord w) = DriftWord.commonDelay w) ∧
      (∀ w : List ℝ, w ≠ [] → (∀ d ∈ w, d ≠ 0) → DriftWord.displacement w = 0 →
        0 < DriftWord.reserve w) ∧
      (∀ D r : ℝ, 0 ≤ r → ∃ w : List ℝ,
        DriftWord.displacement w = D ∧ DriftWord.reserve w = r) := by
  refine ⟨fun u v => DriftWord.displacement_reserve_append u v,
    cancellationBirth_eq_zero_iff,
    fun x y h => cancellationBirth_of_mul_neg h,
    fun w => ⟨DriftWord.displacement_reflectWord w, DriftWord.reserve_reflectWord w,
      DriftWord.commonDelay_reflectWord w⟩,
    fun w hne hnz h => DriftWord.reserve_pos_of_closed hne hnz h,
    fun D r hr => ?_⟩
  obtain ⟨w, h1, h2, -⟩ := DriftWord.exists_word_displacement_reserve D r hr
  exact ⟨w, h1, h2⟩

/-! ## 6. The endpoint fibre and the countable exponential source -/

theorem positive_eq_max_add_reserve (s : CausalJordanFormation) :
    s.positive = max (CausalJordanFormation.visible s) 0 + CausalJordanFormation.reserve s := by
  have hvis : CausalJordanFormation.visible s = s.positive - s.negative := rfl
  have hres : CausalJordanFormation.reserve s = min s.positive s.negative := rfl
  rw [hvis, hres]
  rcases le_total s.positive s.negative with hpn | hpn
  · rw [min_eq_left hpn, max_eq_right (by linarith : s.positive - s.negative ≤ (0:ℝ))]; ring
  · rw [min_eq_right hpn, max_eq_left (by linarith : (0:ℝ) ≤ s.positive - s.negative)]; ring

theorem negative_eq_max_add_reserve (s : CausalJordanFormation) :
    s.negative = max (-CausalJordanFormation.visible s) 0 + CausalJordanFormation.reserve s := by
  have hvis : CausalJordanFormation.visible s = s.positive - s.negative := rfl
  have hres : CausalJordanFormation.reserve s = min s.positive s.negative := rfl
  rw [hvis, hres]
  rcases le_total s.positive s.negative with hpn | hpn
  · rw [min_eq_left hpn, max_eq_left (by linarith : (0:ℝ) ≤ -(s.positive - s.negative))]; ring
  · rw [min_eq_right hpn, max_eq_right (by linarith : -(s.positive - s.negative) ≤ (0:ℝ))]; ring

/-- **`(CJF.8)`.**  The endpoint fibre over a recovered displacement is exactly the shifted
half-line `{(D⁺ + r, D⁻ + r) : r ≥ 0}`; the coordinate `r` is the reserve erased by cancellation. -/
theorem visible_eq_iff_exists_reserve (s : CausalJordanFormation) (D : ℝ) :
    CausalJordanFormation.visible s = D ↔
      ∃ r : ℝ, 0 ≤ r ∧ s.positive = max D 0 + r ∧ s.negative = max (-D) 0 + r := by
  constructor
  · intro h
    refine ⟨CausalJordanFormation.reserve s, le_min s.positive_nonneg s.negative_nonneg, ?_, ?_⟩
    · rw [positive_eq_max_add_reserve s, h]
    · rw [negative_eq_max_add_reserve s, h]
  · rintro ⟨r, _, hp, hn⟩
    have hvis : CausalJordanFormation.visible s = s.positive - s.negative := rfl
    rw [hvis, hp, hn]
    rcases le_total 0 D with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -D ≤ (0:ℝ))]; ring
    · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -D)]; ring

section DiscreteSource

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A countable source law presented by its weights, as in `(CJF.34)`. -/
def weightMeasure (q : A → ℝ≥0∞) : Measure A := Measure.sum fun a => q a • Measure.dirac a

@[simp] theorem weightMeasure_singleton (q : A → ℝ≥0∞) (a : A) :
    weightMeasure q {a} = q a := by
  rw [weightMeasure, Measure.sum_apply _ (measurableSet_singleton a), tsum_eq_single a]
  · simp
  · intro b hb
    simp [Measure.smul_apply, Set.indicator_of_notMem, hb]

/-- `(CJF.34)`  The partition response of a countable source is its weighted exponential sum. -/
theorem partitionResponse_weightMeasure (q : A → ℝ≥0∞) (X : A → ℝ) (u : ℝ) :
    partitionResponse (weightMeasure q) X u
      = ∑' a, q a * ENNReal.ofReal (Real.exp (u * X a)) := by
  rw [partitionResponse, weightMeasure, lintegral_sum_measure]
  refine tsum_congr fun a => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem driftTilt_weightMeasure_singleton (q : A → ℝ≥0∞) {X : A → ℝ} (hX : Measurable X)
    (u : ℝ) (a : A) :
    driftTilt (weightMeasure q) X u {a} = q a * ENNReal.ofReal (Real.exp (u * X a)) := by
  rw [driftTilt, withDensity_apply _ (measurableSet_singleton a),
    ← lintegral_indicator (measurableSet_singleton a), weightMeasure, lintegral_sum_measure,
    tsum_eq_single a]
  · rw [lintegral_smul_measure, lintegral_dirac]
    simp
  · intro b hb
    rw [lintegral_smul_measure, lintegral_dirac, Set.indicator_of_notMem (by simpa using hb)]
    simp

/-- `(CJF.35)`  Atomic mass of the exponential-family observer on a countable source. -/
theorem expObserver_weightMeasure_singleton (q : A → ℝ≥0∞) {X : A → ℝ} (hX : Measurable X)
    (u : ℝ) (a : A) :
    expObserver (weightMeasure q) X u {a}
      = (partitionResponse (weightMeasure q) X u)⁻¹ *
        (q a * ENNReal.ofReal (Real.exp (u * X a))) := by
  rw [expObserver, Measure.smul_apply, driftTilt_weightMeasure_singleton q hX u a, smul_eq_mul]

end DiscreteSource

/-- **`(CJF.42)`  Euler-shell specialization.**  With source weights `n^{-σ}` and clock `log n`,
the exponential-family observer of a signed drift word is the normalized shell law `n^{u-σ}`. -/
theorem expObserver_eulerShell (S : Set ℕ) (σ u : ℝ) {n : ℕ} (hn : 0 < n) (hmem : n ∈ S) :
    expObserver (weightMeasure (Set.indicator S fun m : ℕ => ENNReal.ofReal ((m : ℝ) ^ (-σ))))
        (fun m : ℕ => Real.log m) u {n}
      = (partitionResponse
            (weightMeasure (Set.indicator S fun m : ℕ => ENNReal.ofReal ((m : ℝ) ^ (-σ))))
            (fun m : ℕ => Real.log m) u)⁻¹ * ENNReal.ofReal ((n : ℝ) ^ (u - σ)) := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hX : Measurable (fun m : ℕ => Real.log m) := measurable_from_top
  rw [expObserver_weightMeasure_singleton _ hX u n]
  congr 1
  rw [Set.indicator_of_mem hmem, ← ENNReal.ofReal_mul (Real.rpow_nonneg hnpos.le _)]
  congr 1
  have hexp : Real.exp (u * Real.log (n : ℝ)) = (n : ℝ) ^ u := by
    rw [mul_comm, ← Real.rpow_def_of_pos hnpos]
  rw [hexp, ← Real.rpow_add hnpos]
  congr 1
  ring

end

end GaloisForLFunctions.HTGeometry
