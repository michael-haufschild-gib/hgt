import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# One-sided subshifts of finite type

Sequences `x : ℕ → Fin k` over a finite alphabet, an incidence relation `A` on the alphabet, and the
admissible sequences `A (x i) (x (i+1))`.  This file provides the combinatorics used by the transfer
operator of a suspension flow:

* `cons`, `prepend`, `shiftBy`, `Agree` (agreement on an initial segment) and their interaction;
* `periodicSeq`, `periodicPoints` — the admissible sequences of period `L`, as a finite set;
* `birkhoff` sums `φⁿ(x) = Σ_{i<n} φ(σⁱx)` with the distortion bound
  `|φⁿ(x) − φⁿ(y)| ≤ C θ^j/(1 − θ)` for sequences agreeing on `n + j` symbols;
* `partitionSum_le_periodicSum` — the closing lemma: under mixing, every admissible word of length
  `n` closes up to a periodic point of period `n + M − 1`, so partition sums over preimages are
  bounded by periodic-orbit sums;
* `exists_pos_le_of_holder` — a positive Hölder function on the (compact) shift space is bounded
  below by a positive constant;
* `ShiftSpace`, `shiftMap`, `fixedPointSet` — the subshift as a type, and its periodic points.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

variable {k : ℕ}

/-! ## Sequences and words -/

/-- Prepending one symbol: `a x₀ x₁ …`. -/
def cons (a : Fin k) (x : ℕ → Fin k) : ℕ → Fin k := fun i =>
  match i with
  | 0 => a
  | j + 1 => x j

@[simp] theorem cons_zero (a : Fin k) (x : ℕ → Fin k) : cons a x 0 = a := rfl

@[simp] theorem cons_succ (a : Fin k) (x : ℕ → Fin k) (i : ℕ) : cons a x (i + 1) = x i := rfl

/-- The `n`-fold shift `(x_{i+n})_i`. -/
def shiftBy (n : ℕ) (x : ℕ → Fin k) : ℕ → Fin k := fun i => x (i + n)

@[simp] theorem shiftBy_apply (n : ℕ) (x : ℕ → Fin k) (i : ℕ) : shiftBy n x i = x (i + n) := rfl

@[simp] theorem shiftBy_zero (x : ℕ → Fin k) : shiftBy 0 x = x := rfl

theorem shiftBy_shiftBy (m n : ℕ) (x : ℕ → Fin k) : shiftBy m (shiftBy n x) = shiftBy (m + n) x := by
  funext i; simp [shiftBy, Nat.add_assoc]

theorem shiftBy_succ_cons (n : ℕ) (a : Fin k) (x : ℕ → Fin k) :
    shiftBy (n + 1) (cons a x) = shiftBy n x := by
  funext i; simp [shiftBy, ← Nat.add_assoc]

/-- Prepending a word: `v₀ … v_{n−1} x₀ x₁ …`. -/
def prepend : {n : ℕ} → (Fin n → Fin k) → (ℕ → Fin k) → ℕ → Fin k
  | 0, _, x => x
  | _ + 1, v, x => cons (v 0) (prepend (Fin.tail v) x)

@[simp] theorem prepend_zero (v : Fin 0 → Fin k) (x : ℕ → Fin k) : prepend v x = x := rfl

theorem prepend_succ {n : ℕ} (v : Fin (n + 1) → Fin k) (x : ℕ → Fin k) :
    prepend v x = cons (v 0) (prepend (Fin.tail v) x) := rfl

@[simp] theorem prepend_cons {n : ℕ} (a : Fin k) (v : Fin n → Fin k) (x : ℕ → Fin k) :
    prepend (Fin.cons a v : Fin (n + 1) → Fin k) x = cons a (prepend v x) := by
  rw [prepend_succ, Fin.cons_zero, Fin.tail_cons]

theorem prepend_apply_lt {n : ℕ} (v : Fin n → Fin k) (x : ℕ → Fin k) {i : ℕ} (hi : i < n) :
    prepend v x i = v ⟨i, hi⟩ := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [prepend_succ]
    cases i with
    | zero => rfl
    | succ i =>
      rw [cons_succ, ih (Fin.tail v) (by omega)]
      rfl

theorem prepend_apply_add {n : ℕ} (v : Fin n → Fin k) (x : ℕ → Fin k) (i : ℕ) :
    prepend v x (i + n) = x i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [prepend_succ, show i + (n + 1) = (i + n) + 1 by omega, cons_succ, ih]

@[simp] theorem shiftBy_prepend {n : ℕ} (v : Fin n → Fin k) (x : ℕ → Fin k) :
    shiftBy n (prepend v x) = x := by
  funext i; exact prepend_apply_add v x i

/-- Agreement on the first `n` symbols. -/
def Agree (n : ℕ) (x y : ℕ → Fin k) : Prop := ∀ i < n, x i = y i

theorem Agree.refl (n : ℕ) (x : ℕ → Fin k) : Agree n x x := fun _ _ => rfl

theorem Agree.symm {n : ℕ} {x y : ℕ → Fin k} (h : Agree n x y) : Agree n y x :=
  fun i hi => (h i hi).symm

theorem Agree.trans {n : ℕ} {x y z : ℕ → Fin k} (h₁ : Agree n x y) (h₂ : Agree n y z) :
    Agree n x z := fun i hi => (h₁ i hi).trans (h₂ i hi)

theorem Agree.mono {m n : ℕ} {x y : ℕ → Fin k} (h : Agree n x y) (hmn : m ≤ n) : Agree m x y :=
  fun i hi => h i (lt_of_lt_of_le hi hmn)

theorem agree_zero (x y : ℕ → Fin k) : Agree 0 x y := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem agree_cons_iff {n : ℕ} (a : Fin k) (x y : ℕ → Fin k) :
    Agree (n + 1) (cons a x) (cons a y) ↔ Agree n x y := by
  constructor
  · intro h i hi; exact h (i + 1) (by omega)
  · intro h i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by omega)

theorem agree_prepend {n j : ℕ} (v : Fin n → Fin k) {x y : ℕ → Fin k} (h : Agree j x y) :
    Agree (j + n) (prepend v x) (prepend v y) := by
  intro i hi
  by_cases hin : i < n
  · rw [prepend_apply_lt v x hin, prepend_apply_lt v y hin]
  · obtain ⟨l, rfl⟩ : ∃ l, i = l + n := ⟨i - n, by omega⟩
    rw [prepend_apply_add, prepend_apply_add]
    exact h l (by omega)

theorem agree_shiftBy {j n : ℕ} {x y : ℕ → Fin k} (h : Agree (j + n) x y) :
    Agree j (shiftBy n x) (shiftBy n y) := fun i hi => h (i + n) (by omega)

theorem agree_prepend_self {n : ℕ} (v : Fin n → Fin k) (x y : ℕ → Fin k) :
    Agree n (prepend v x) (prepend v y) := by
  have := agree_prepend (j := 0) v (agree_zero x y)
  simpa using this

/-! ## Admissibility -/

variable (A : Fin k → Fin k → Prop)

/-- A sequence is **admissible** if every transition is allowed. -/
def IsAdmissible (x : ℕ → Fin k) : Prop := ∀ i, A (x i) (x (i + 1))

/-- The first `n` transitions are allowed. -/
def IsAdmissibleUpTo (n : ℕ) (x : ℕ → Fin k) : Prop := ∀ i < n, A (x i) (x (i + 1))

variable {A}

theorem IsAdmissible.shiftBy {x : ℕ → Fin k} (hx : IsAdmissible A x) (n : ℕ) :
    IsAdmissible A (shiftBy n x) := fun i => by
  simpa [Symbolic.shiftBy, Nat.add_right_comm] using hx (i + n)

theorem isAdmissible_cons_iff (a : Fin k) (x : ℕ → Fin k) :
    IsAdmissible A (cons a x) ↔ A a (x 0) ∧ IsAdmissible A x := by
  constructor
  · intro h; exact ⟨h 0, fun i => h (i + 1)⟩
  · rintro ⟨h0, h⟩ i
    cases i with
    | zero => exact h0
    | succ i => exact h i

theorem isAdmissible_iff_upTo_and_shiftBy (n : ℕ) (x : ℕ → Fin k) :
    IsAdmissible A x ↔ IsAdmissibleUpTo A n x ∧ IsAdmissible A (shiftBy n x) := by
  constructor
  · intro h; exact ⟨fun i _ => h i, h.shiftBy n⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i < n
    · exact h1 i hi
    · obtain ⟨l, rfl⟩ : ∃ l, i = l + n := ⟨i - n, by omega⟩
      have := h2 l
      simpa [Symbolic.shiftBy, Nat.add_right_comm] using this

theorem isAdmissibleUpTo_congr {n : ℕ} {x y : ℕ → Fin k} (h : Agree (n + 1) x y) :
    IsAdmissibleUpTo A n x ↔ IsAdmissibleUpTo A n y := by
  constructor
  · intro hx i hi; rw [← h i (by omega), ← h (i + 1) (by omega)]; exact hx i hi
  · intro hy i hi; rw [h i (by omega), h (i + 1) (by omega)]; exact hy i hi

theorem isAdmissible_prepend_iff {n : ℕ} (v : Fin n → Fin k) (x : ℕ → Fin k) :
    IsAdmissible A (prepend v x) ↔ IsAdmissibleUpTo A n (prepend v x) ∧ IsAdmissible A x := by
  rw [isAdmissible_iff_upTo_and_shiftBy n, shiftBy_prepend]

/-- Admissibility of `prepend v x` depends on `x` only through `x₀`, once `x` is admissible. -/
theorem isAdmissible_prepend_congr {n : ℕ} (v : Fin n → Fin k) {x y : ℕ → Fin k}
    (hx : IsAdmissible A x) (hy : IsAdmissible A y) (h0 : x 0 = y 0) :
    IsAdmissible A (prepend v x) ↔ IsAdmissible A (prepend v y) := by
  rw [isAdmissible_prepend_iff, isAdmissible_prepend_iff,
    isAdmissibleUpTo_congr (A := A) (n := n) (x := prepend v x) (y := prepend v y)]
  · simp [hx, hy]
  · have h1 : Agree 1 x y := fun i hi => by
      obtain rfl : i = 0 := by omega
      exact h0
    have := agree_prepend v h1
    rwa [Nat.add_comm] at this

/-! ## Periodic points -/

/-- The periodic sequence `u u u …` of a word of positive length. -/
def periodicSeq {L : ℕ} [NeZero L] (u : Fin L → Fin k) : ℕ → Fin k :=
  fun i => u ⟨i % L, Nat.mod_lt _ (NeZero.pos L)⟩

theorem periodicSeq_apply_lt {L : ℕ} [NeZero L] (u : Fin L → Fin k) {i : ℕ} (hi : i < L) :
    periodicSeq u i = u ⟨i, hi⟩ := by
  simp [periodicSeq, Nat.mod_eq_of_lt hi]

theorem periodicSeq_add {L : ℕ} [NeZero L] (u : Fin L → Fin k) (i : ℕ) :
    periodicSeq u (i + L) = periodicSeq u i := by
  simp [periodicSeq, Nat.add_mod_right]

@[simp] theorem shiftBy_periodicSeq {L : ℕ} [NeZero L] (u : Fin L → Fin k) :
    shiftBy L (periodicSeq u) = periodicSeq u := by
  funext i; exact periodicSeq_add u i

theorem prepend_periodicSeq {L : ℕ} [NeZero L] (u : Fin L → Fin k) :
    prepend u (periodicSeq u) = periodicSeq u := by
  funext i
  by_cases hi : i < L
  · rw [prepend_apply_lt u _ hi, periodicSeq_apply_lt u hi]
  · obtain ⟨l, rfl⟩ : ∃ l, i = l + L := ⟨i - L, by omega⟩
    rw [prepend_apply_add, periodicSeq_add]

theorem periodicSeq_injective {L : ℕ} [NeZero L] :
    Function.Injective (periodicSeq : (Fin L → Fin k) → ℕ → Fin k) := by
  intro u v h
  funext i
  have := congrFun h i
  rwa [periodicSeq_apply_lt u i.2, periodicSeq_apply_lt v i.2] at this

theorem eq_periodicSeq_of_shiftBy_eq {L : ℕ} [NeZero L] {y : ℕ → Fin k} (hy : shiftBy L y = y) :
    periodicSeq (fun i : Fin L => y i) = y := by
  have hper : ∀ q i, y (i + q * L) = y i := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro i
      have h1 := congrFun hy (i + q * L)
      simp only [shiftBy_apply] at h1
      rw [show i + (q + 1) * L = i + q * L + L by ring, h1, ih]
  funext i
  simp only [periodicSeq]
  have := hper (i / L) (i % L)
  rw [Nat.mod_add_div' i L] at this
  exact this.symm

theorem isAdmissible_periodicSeq_iff {L : ℕ} [NeZero L] (u : Fin L → Fin k) :
    IsAdmissible A (periodicSeq u) ↔ IsAdmissibleUpTo A L (periodicSeq u) := by
  constructor
  · intro h i _; exact h i
  · intro h i
    have hL := NeZero.pos L
    have h1 := h (i % L) (Nat.mod_lt _ hL)
    have e1 : periodicSeq u (i % L) = periodicSeq u i := by
      simp [periodicSeq]
    have e2 : periodicSeq u (i % L + 1) = periodicSeq u (i + 1) := by
      simp only [periodicSeq]
      congr 2
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rwa [e1, e2] at h1

open Classical in
/-- The admissible sequences of period `L`, as a finite set. -/
noncomputable def periodicPoints (A : Fin k → Fin k → Prop) (L : ℕ) [NeZero L] :
    Finset (ℕ → Fin k) :=
  ((Finset.univ : Finset (Fin L → Fin k)).filter fun u => IsAdmissible A (periodicSeq u)).image
    periodicSeq

theorem mem_periodicPoints {L : ℕ} [NeZero L] {y : ℕ → Fin k} :
    y ∈ periodicPoints A L ↔ IsAdmissible A y ∧ shiftBy L y = y := by
  classical
  simp only [periodicPoints, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨hu, shiftBy_periodicSeq u⟩
  · rintro ⟨hy, hs⟩
    exact ⟨fun i => y i, by rwa [eq_periodicSeq_of_shiftBy_eq hs], eq_periodicSeq_of_shiftBy_eq hs⟩

/-! ## Birkhoff sums -/

/-- The Birkhoff sum `φⁿ(x) = Σ_{i<n} φ(σⁱ x)`. -/
def birkhoff (φ : (ℕ → Fin k) → ℝ) (n : ℕ) (x : ℕ → Fin k) : ℝ :=
  ∑ i ∈ Finset.range n, φ (shiftBy i x)

@[simp] theorem birkhoff_zero (φ : (ℕ → Fin k) → ℝ) (x : ℕ → Fin k) : birkhoff φ 0 x = 0 := by
  simp [birkhoff]

theorem birkhoff_succ_cons (φ : (ℕ → Fin k) → ℝ) (n : ℕ) (a : Fin k) (x : ℕ → Fin k) :
    birkhoff φ (n + 1) (cons a x) = φ (cons a x) + birkhoff φ n x := by
  rw [birkhoff, Finset.sum_range_succ', shiftBy_zero, add_comm]
  congr 1

theorem birkhoff_add (φ : (ℕ → Fin k) → ℝ) (m n : ℕ) (x : ℕ → Fin k) :
    birkhoff φ (m + n) x = birkhoff φ m x + birkhoff φ n (shiftBy m x) := by
  rw [birkhoff, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [shiftBy_shiftBy, Nat.add_comm i m]

theorem birkhoff_prepend_add {n : ℕ} (φ : (ℕ → Fin k) → ℝ) (v : Fin n → Fin k) (m : ℕ)
    (x : ℕ → Fin k) :
    birkhoff φ (n + m) (prepend v x) = birkhoff φ n (prepend v x) + birkhoff φ m x := by
  rw [birkhoff_add, shiftBy_prepend]

/-- **Birkhoff sums of a bounded function grow at most linearly.** -/
theorem abs_birkhoff_le {φ : (ℕ → Fin k) → ℝ} {R₀ : ℝ}
    (hb : ∀ y, IsAdmissible A y → |φ y| ≤ R₀) (n : ℕ) {x : ℕ → Fin k} (hx : IsAdmissible A x) :
    |birkhoff φ n x| ≤ n * R₀ := by
  rw [birkhoff]
  calc |∑ i ∈ Finset.range n, φ (shiftBy i x)| ≤ ∑ i ∈ Finset.range n, |φ (shiftBy i x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, R₀ := Finset.sum_le_sum fun i _ => hb _ (hx.shiftBy i)
    _ = n * R₀ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Bounded distortion**: for sequences agreeing on `n + j` symbols,
`|φⁿ(x) − φⁿ(y)| ≤ C θ^j/(1 − θ)`. -/
theorem abs_birkhoff_sub_le {φ : (ℕ → Fin k) → ℝ} {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    (n j : ℕ) {x y : ℕ → Fin k} (hx : IsAdmissible A x) (hy : IsAdmissible A y)
    (hxy : Agree (n + j) x y) :
    |birkhoff φ n x - birkhoff φ n y| ≤ C * θ ^ j / (1 - θ) := by
  have hC : 0 ≤ C := by
    have := hh x x 0 hx hx (Agree.refl 0 x)
    simp only [sub_self, abs_zero, pow_zero, mul_one] at this
    exact this
  rw [birkhoff, birkhoff, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range n, |φ (shiftBy i x) - φ (shiftBy i y)| ≤
      C * θ ^ j * θ ^ (n - 1 - i) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hag : Agree (j + (n - 1 - i)) (shiftBy i x) (shiftBy i y) := by
      apply agree_shiftBy
      exact hxy.mono (by omega)
    have := hh _ _ _ (hx.shiftBy i) (hy.shiftBy i) hag
    rwa [pow_add, ← mul_assoc] at this
  calc |∑ i ∈ Finset.range n, (φ (shiftBy i x) - φ (shiftBy i y))|
      ≤ ∑ i ∈ Finset.range n, |φ (shiftBy i x) - φ (shiftBy i y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, C * θ ^ j * θ ^ (n - 1 - i) := Finset.sum_le_sum hterm
    _ = C * θ ^ j * ∑ i ∈ Finset.range n, θ ^ (n - 1 - i) := by rw [Finset.mul_sum]
    _ = C * θ ^ j * ∑ i ∈ Finset.range n, θ ^ i := by
        rw [Finset.sum_range_reflect (fun i => θ ^ i) n]
    _ ≤ C * θ ^ j * (1 - θ)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hθ0 hθ1
        rw [← Finset.range_eq_Ico, pow_zero] at this
        simpa [div_eq_mul_inv] using this
    _ = C * θ ^ j / (1 - θ) := by rw [div_eq_mul_inv]

/-! ## Mixing and the closing lemma -/

variable (A) in
/-- **Mixing**: any two symbols are joined by an admissible path of length exactly `M`. -/
def IsMixing (M : ℕ) : Prop :=
  ∀ a b : Fin k, ∃ c : ℕ → Fin k, c 0 = a ∧ c M = b ∧ ∀ i < M, A (c i) (c (i + 1))

/-- The word of length `n + (M − 1)` obtained by closing `v` with the path `c` from `v_{n−1}` back
to `v₀`. -/
def closingWord {n M : ℕ} (v : Fin n → Fin k) (c : ℕ → Fin k) : Fin (n + (M - 1)) → Fin k :=
  fun i => if h : (i : ℕ) < n then v ⟨i, h⟩ else c (i - n + 1)

theorem periodicSeq_closingWord_agree {n M : ℕ} [NeZero (n + (M - 1))] (v : Fin n → Fin k)
    (c : ℕ → Fin k) (x : ℕ → Fin k) :
    Agree n (periodicSeq (closingWord (M := M) v c)) (prepend v x) := by
  intro i hi
  rw [periodicSeq_apply_lt _ (by omega), prepend_apply_lt v x hi]
  simp [closingWord, hi]

/-- **Closing**: an admissible word followed by a path back to its first symbol is the period of an
admissible periodic sequence. -/
theorem isAdmissible_periodicSeq_closingWord {n M : ℕ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    [NeZero (n + (M - 1))] (v : Fin n → Fin k) (c : ℕ → Fin k)
    (hc0 : c 0 = v ⟨n - 1, by omega⟩) (hcM : c M = v ⟨0, by omega⟩)
    (hc : ∀ i < M, A (c i) (c (i + 1))) (x : ℕ → Fin k)
    (hv : IsAdmissible A (prepend v x)) :
    IsAdmissible A (periodicSeq (closingWord (M := M) v c)) := by
  set L := n + (M - 1)
  set w := closingWord (M := M) v c
  -- the periodic sequence on `[0, L]`
  have hq : ∀ i ≤ L, periodicSeq w i = if i < n then prepend v x i else c (i + 1 - n) := by
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · rw [periodicSeq_apply_lt w hlt]
      by_cases hin : i < n
      · simp [w, closingWord, hin, prepend_apply_lt v x hin]
      · simp only [w, closingWord, hin, dif_neg, not_false_eq_true, if_false]
        congr 1; omega
    · have h0 := periodicSeq_add w 0
      rw [zero_add] at h0
      rw [h0, periodicSeq_apply_lt w (by omega : 0 < L)]
      have hnL : ¬ L < n := by omega
      simp only [hnL, if_false, w, closingWord, show (0 : ℕ) < n by omega, dif_pos]
      rw [show L + 1 - n = M by omega, hcM]
  have hq' : ∀ i ≤ L, n - 1 ≤ i → periodicSeq w i = c (i + 1 - n) := by
    intro i hi hni
    rw [hq i hi]
    split_ifs with hin
    · have : i = n - 1 := by omega
      subst this
      rw [prepend_apply_lt v x hin, show n - 1 + 1 - n = 0 by omega, hc0]
    · rfl
  rw [isAdmissible_periodicSeq_iff]
  intro i hi
  by_cases h1 : i + 1 < n
  · rw [hq i hi.le, hq (i + 1) hi, if_pos (by omega), if_pos h1]
    exact hv i
  · rw [hq' i hi.le (by omega), hq' (i + 1) hi (by omega),
      show i + 1 + 1 - n = (i + 1 - n) + 1 by omega]
    exact hc _ (by omega)

open Classical in
/-- **The closing lemma.**  Under mixing, the partition sum over admissible preimage words of
length `n` is bounded by the periodic-orbit sum of period `n + M − 1`. -/
theorem partitionSum_le_periodicSum {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ y, IsAdmissible A y → |φ y| ≤ R₀)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j)
    (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) [NeZero (n + (M - 1))] (x : ℕ → Fin k) :
    (∑ v : Fin n → Fin k, if IsAdmissible A (prepend v x) then
        Real.exp (-(σ * birkhoff φ n (prepend v x))) else 0) ≤
      Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀)) *
        ∑ p ∈ periodicPoints A (n + (M - 1)), Real.exp (-(σ * birkhoff φ (n + (M - 1)) p)) := by
  classical
  choose c hc0 hcM hc using hmix
  set close : (Fin n → Fin k) → ℕ → Fin k := fun v =>
    periodicSeq (closingWord (M := M) v (c (v ⟨n - 1, by omega⟩) (v ⟨0, by omega⟩)))
  set K := Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀))
  set S := (Finset.univ : Finset (Fin n → Fin k)).filter fun v => IsAdmissible A (prepend v x)
  have hclose_adm : ∀ v ∈ S, IsAdmissible A (close v) := by
    intro v hv
    exact isAdmissible_periodicSeq_closingWord hn hM v _ (hc0 _ _) (hcM _ _) (hc _ _) x
      (Finset.mem_filter.mp hv).2
  have hclose_mem : ∀ v ∈ S, close v ∈ periodicPoints A (n + (M - 1)) := fun v hv =>
    mem_periodicPoints.mpr ⟨hclose_adm v hv, shiftBy_periodicSeq _⟩
  have hclose_inj : Set.InjOn close S := by
    intro v _ w _ hvw
    funext i
    have h1 := periodicSeq_closingWord_agree (M := M) v
      (c (v ⟨n - 1, by omega⟩) (v ⟨0, by omega⟩)) x i i.2
    have h2 := periodicSeq_closingWord_agree (M := M) w
      (c (w ⟨n - 1, by omega⟩) (w ⟨0, by omega⟩)) x i i.2
    have h3 : close v i = close w i := by rw [hvw]
    rw [prepend_apply_lt v x i.2] at h1
    rw [prepend_apply_lt w x i.2] at h2
    simp only [close] at h3
    rw [← h1, ← h2]
    exact h3
  have hterm : ∀ v ∈ S, Real.exp (-(σ * birkhoff φ n (prepend v x))) ≤
      K * Real.exp (-(σ * birkhoff φ (n + (M - 1)) (close v))) := by
    intro v hv
    have hva : IsAdmissible A (prepend v x) := (Finset.mem_filter.mp hv).2
    have hca := hclose_adm v hv
    have hag : Agree (n + 0) (prepend v x) (close v) :=
      (periodicSeq_closingWord_agree (M := M) v _ x).symm
    have hd := abs_birkhoff_sub_le hθ0 hθ1 hh n 0 hva hca hag
    rw [pow_zero, mul_one] at hd
    have hsplit := birkhoff_add φ n (M - 1) (close v)
    have htail := abs_birkhoff_le hb (M - 1) (hca.shiftBy n)
    have hM1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM, Nat.cast_one]
    rw [hM1] at htail
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have e1 : |σ * birkhoff φ n (prepend v x) - σ * birkhoff φ n (close v)| ≤ |σ| * (C / (1 - θ)) := by
      rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left hd (abs_nonneg σ)
    have e2 : |σ * birkhoff φ (M - 1) (shiftBy n (close v))| ≤ |σ| * ((M - 1) * R₀) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left htail (abs_nonneg σ)
    rw [hsplit]
    have := abs_le.mp e1
    have := abs_le.mp e2
    nlinarith [abs_nonneg σ]
  calc (∑ v : Fin n → Fin k, if IsAdmissible A (prepend v x) then
        Real.exp (-(σ * birkhoff φ n (prepend v x))) else 0)
      = ∑ v ∈ S, Real.exp (-(σ * birkhoff φ n (prepend v x))) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ v ∈ S, K * Real.exp (-(σ * birkhoff φ (n + (M - 1)) (close v))) :=
        Finset.sum_le_sum hterm
    _ = K * ∑ p ∈ S.image close, Real.exp (-(σ * birkhoff φ (n + (M - 1)) p)) := by
        rw [← Finset.mul_sum, Finset.sum_image hclose_inj]
    _ ≤ K * ∑ p ∈ periodicPoints A (n + (M - 1)), Real.exp (-(σ * birkhoff φ (n + (M - 1)) p)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => (Real.exp_pos _).le
        intro p hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
        exact hclose_mem v hv

/-! ## Compactness -/

/-- **A positive Hölder function on the subshift is bounded below by a positive constant.**  The
subshift is compact and the function is continuous on it. -/
theorem exists_pos_le_of_holder {φ : (ℕ → Fin k) → ℝ} (hpos : ∀ x, IsAdmissible A x → 0 < φ x)
    {C θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hh : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j) :
    ∃ c > 0, ∀ x, IsAdmissible A x → c ≤ φ x := by
  set S : Set (ℕ → Fin k) := {x | IsAdmissible A x}
  have hS : IsClosed S := by
    have : S = ⋂ i, {x : ℕ → Fin k | A (x i) (x (i + 1))} := by ext x; simp [S, IsAdmissible]
    rw [this]
    refine isClosed_iInter fun i => ?_
    have hc : Continuous fun x : ℕ → Fin k => (x i, x (i + 1)) :=
      (continuous_apply i).prodMk (continuous_apply (i + 1))
    have h2 : IsClosed {p : Fin k × Fin k | A p.1 p.2} := isClosed_discrete _
    exact h2.preimage hc
  have hSc : IsCompact S := hS.isCompact
  have hcont : ContinuousOn φ S := by
    intro x hx
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    have hθj : ∃ j : ℕ, |C| * θ ^ j < ε := by
      have ht : Filter.Tendsto (fun j : ℕ => |C| * θ ^ j) Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul |C|
      exact (ht.eventually (gt_mem_nhds hε)).exists
    obtain ⟨j, hj⟩ := hθj
    have hnear : ∀ᶠ y in nhds x, Agree j y x := by
      have : ∀ i ∈ Finset.range j, ∀ᶠ y in nhds x, y i = x i := by
        intro i _
        have ht := (continuous_apply i).continuousAt (x := x)
        rw [ContinuousAt, nhds_discrete (Fin k)] at ht
        exact ht (show {a : Fin k | a = x i} ∈ pure (x i) from Filter.mem_pure.mpr rfl)
      filter_upwards [(Filter.eventually_all_finset _).mpr this] with y hy i hi
      exact hy i (Finset.mem_range.mpr hi)
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with y hy hyS
    rw [Real.dist_eq]
    calc |φ y - φ x| ≤ C * θ ^ j := hh y x j hyS hx hy
      _ ≤ |C| * θ ^ j := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hθ0 j)
      _ < ε := hj
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hne hcont
    exact ⟨φ x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩

/-! ## The subshift as a type -/

variable (A) in
/-- The one-sided **subshift of finite type** with transition relation `A`. -/
def ShiftSpace : Type := {x : ℕ → Fin k // IsAdmissible A x}

variable (A) in
/-- The shift map on the subshift. -/
def shiftMap : ShiftSpace A → ShiftSpace A := fun x => ⟨shiftBy 1 x.1, x.2.shiftBy 1⟩

theorem shiftMap_iterate_val (n : ℕ) (x : ShiftSpace A) :
    ((shiftMap A)^[n] x).1 = shiftBy n x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    show shiftBy n (shiftBy 1 x.1) = _
    rw [shiftBy_shiftBy]

variable (A) in
/-- The points fixed by `σⁿ`. -/
def fixedPointSet (n : ℕ) : Set (ShiftSpace A) := {x | (shiftMap A)^[n] x = x}

theorem mem_fixedPointSet_iff (n : ℕ) [NeZero n] (x : ShiftSpace A) :
    x ∈ fixedPointSet A n ↔ x.1 ∈ periodicPoints A n := by
  rw [mem_periodicPoints]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [shiftMap_iterate_val] at this
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [shiftMap_iterate_val, h]

/-- The Birkhoff sum `rⁿ(x) = Σ_{i<n} r(σⁱx)` on the subshift. -/
def birkhoffSum (r : ShiftSpace A → ℝ) (n : ℕ) (x : ShiftSpace A) : ℝ :=
  ∑ i ∈ Finset.range n, r ((shiftMap A)^[i] x)

/-- The **periodic-orbit sum** `Z_n(s) = Σ_{σⁿx = x} e^{−s rⁿ(x)}`. -/
noncomputable def periodicOrbitSum (r : ShiftSpace A → ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ᶠ x ∈ fixedPointSet A n, Complex.exp (-(s * birkhoffSum r n x))

open Classical in
/-- The roof function extended by zero to all sequences. -/
noncomputable def extendByZero (r : ShiftSpace A → ℝ) : (ℕ → Fin k) → ℝ :=
  fun y => if h : IsAdmissible A y then r ⟨y, h⟩ else 0

theorem extendByZero_of_adm (r : ShiftSpace A → ℝ) {y : ℕ → Fin k} (hy : IsAdmissible A y) :
    extendByZero r y = r ⟨y, hy⟩ := by
  simp [extendByZero, hy]

theorem birkhoffSum_eq (r : ShiftSpace A → ℝ) (n : ℕ) (x : ShiftSpace A) :
    birkhoffSum r n x = birkhoff (extendByZero r) n x.1 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := shiftMap_iterate_val i x
  rw [extendByZero_of_adm r (x.2.shiftBy i)]
  congr 1
  exact Subtype.ext h

/-- **The periodic-orbit sum as a sum over periodic sequences.** -/
theorem periodicOrbitSum_eq (r : ShiftSpace A → ℝ) (n : ℕ) [NeZero n] (s : ℂ) :
    periodicOrbitSum r n s =
      ∑ p ∈ periodicPoints A n, Complex.exp (-(s * birkhoff (extendByZero r) n p)) := by
  classical
  have hfin : (fixedPointSet A n).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    refine (periodicPoints A n).finite_toSet.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_fixedPointSet_iff n x).mp hx
  rw [periodicOrbitSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_bij (fun x _ => x.1) (fun x hx => ?_) (fun x _ y _ h => Subtype.ext h)
    (fun p hp => ?_) (fun x _ => ?_)
  · exact (mem_fixedPointSet_iff n x).mp ((Set.Finite.mem_toFinset hfin).mp hx)
  · have hpa : IsAdmissible A p := (mem_periodicPoints.mp hp).1
    refine ⟨⟨p, hpa⟩, (Set.Finite.mem_toFinset hfin).mpr ((mem_fixedPointSet_iff n _).mpr hp), rfl⟩
  · rw [birkhoffSum_eq]

end GaloisForLFunctions.HTGeometry.Symbolic
