import GaloisForLFunctions.SquareRootThreshold.WindowedWeilFormSliceTransfer
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Card

/-!
# Compact coordinates of tempered zero configurations

Inverse ordinates compactify escaping zeros. Ranking occurrences by their inverse-square
heights gives a uniform bound at each coordinate while retaining the total tempered mass.
Horizontal reflection restores the configuration symmetry, including collisions and multiplicity.
-/

open Set Finset Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
open Zeta23 SquareRootThreshold

section Rank
variable {ι : Type*} (w : ι → ℝ) (e : ι → ℕ)
private def Before (a b : ι) : Prop := w b < w a ∨ w a = w b ∧ e a < e b
private theorem before_irrefl (a : ι) : ¬ Before w e a a := by simp [Before]
private theorem before_trans {a b c : ι}
    (hab : Before w e a b) (hbc : Before w e b c) : Before w e a c := by
  rcases hab with hab | ⟨hab, hea⟩ <;> rcases hbc with hbc | ⟨hbc, heb⟩
  · exact Or.inl (hbc.trans hab)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hab.trans hbc, hea.trans heb⟩
private theorem before_total (he : Function.Injective e) {a b : ι} (hne : a ≠ b) :
    Before w e a b ∨ Before w e b a := by
  rcases lt_trichotomy (w a) (w b) with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases lt_or_gt_of_ne (fun h' => hne (he h')) with hab | hba
    · exact Or.inl (Or.inr ⟨h, hab⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hba⟩)
  · exact Or.inl (Or.inl h)
private theorem finite_before (hw : Summable w) (hw0 : ∀ a, 0 < w a) (a : ι) :
    {b | Before w e b a}.Finite := by
  have h := hw.tendsto_cofinite_zero.eventually_lt_const (hw0 a)
  change {b | ¬w b < w a}.Finite at h
  apply h.subset
  intro b hb
  rcases hb with hb | ⟨hb, _⟩
  · exact not_lt_of_ge hb.le
  · exact not_lt_of_ge hb.ge

private def rank (a : ι) : ℕ := {b | Before w e b a}.ncard
private theorem rank_lt (hw : Summable w) (hw0 : ∀ a, 0 < w a) {a b : ι}
    (hab : Before w e a b) : rank w e a < rank w e b := by
  apply Set.ncard_lt_ncard _ (finite_before w e hw hw0 b)
  constructor
  · exact fun _ hc => before_trans w e hc hab
  · intro h
    exact before_irrefl w e a (h hab)

private theorem rank_injective (hw : Summable w) (hw0 : ∀ a, 0 < w a)
    (he : Function.Injective e) : Function.Injective (rank w e) := by
  intro a b h
  by_contra hne
  rcases before_total w e he hne with hab | hba
  · exact (rank_lt w e hw hw0 hab).ne h
  · exact (rank_lt w e hw hw0 hba).ne h.symm

private theorem rank_mul_le (hw : Summable w) (hw0 : ∀ a, 0 < w a) (a : ι) :
    ((rank w e a : ℝ) + 1) * w a ≤ ∑' b, w b := by
  classical
  have hf := finite_before w e hw hw0 a
  have ha : a ∉ hf.toFinset := by
    intro ha
    exact before_irrefl w e a (hf.mem_toFinset.mp ha)
  have hle : ∀ b ∈ insert a hf.toFinset, w a ≤ w b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · rcases hf.mem_toFinset.mp hb with hb | ⟨hb, _⟩
      · exact hb.le
      · exact hb.ge
  have h := (Finset.card_nsmul_le_sum (insert a hf.toFinset) w (w a) hle).trans
    (hw.sum_le_tsum _ (fun b _ => (hw0 b).le))
  simpa only [Finset.card_insert_of_notMem ha, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    ← Set.ncard_eq_toFinset_card, rank] using h

end Rank


/-- A strip abscissa and inverse ordinate; zero inverse ordinate denotes an absent point. -/
abbrev Slot := Set.Icc (0 : ℝ) 1 × ℝ

/-- Inverse-ordinate bound at each labelled occurrence. -/
def CoordinateBound (C : ℝ) (p : ℕ → Slot) : Prop :=
  ∀ n : ℕ, ((n : ℝ) + 1) * (p n).2 ^ 2 ≤ C

/-- The finite point represented by a nonzero inverse ordinate. -/
def slotPoint (a : Slot) : ℂ := ⟨a.1, a.2⁻¹⟩

private def rawNode (p : ℕ → Slot) (i : ℕ × Bool) : ℂ :=
  if i.2 then reflect (slotPoint (p i.1)) else slotPoint (p i.1)

/-- Each nonempty slot supplies both members of its horizontal reflection pair. -/
abbrev Occurrence (p : ℕ → Slot) := {n : ℕ // (p n).2 ≠ 0} × Bool

def node (p : ℕ → Slot) (i : Occurrence p) : ℂ := rawNode p (i.1, i.2)

private def flip (p : ℕ → Slot) (i : Occurrence p) : Occurrence p := (i.1, !i.2)

private theorem reflect_twice (z : ℂ) : reflect (reflect z) = z := by
  apply Complex.ext <;> simp [reflect]

private theorem flip_twice (p : ℕ → Slot) (i : Occurrence p) : flip p (flip p i) = i := by
  simp [flip]

private theorem node_flip (p : ℕ → Slot) (i : Occurrence p) :
    node p (flip p i) = reflect (node p i) := by
  rcases i with ⟨n, b⟩
  cases b <;> simp [node, rawNode, flip]

theorem node_im (p : ℕ → Slot) (i : Occurrence p) : (node p i).im = (p i.1).2⁻¹ := by
  rcases i with ⟨n, b⟩
  cases b <;> simp [node, rawNode, slotPoint, reflect]

private theorem bound_nonneg {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p) : 0 ≤ C := by
  have h0 := h 0
  simp only [Nat.cast_zero, zero_add, one_mul] at h0
  exact (sq_nonneg _).trans h0

/-- Bounded inverse-square mass forces late labels to escape every bounded height interval. -/
theorem index_le_height_sq {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p)
    (i : Occurrence p) : ((i.1.val : ℝ) + 1) ≤ C * (node p i).im ^ 2 := by
  rw [node_im]
  have hu : (p i.1).2 ^ 2 * ((p i.1).2⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ i.1.property, one_pow]
  calc
    _ = (((i.1.val : ℝ) + 1) * (p i.1).2 ^ 2) * ((p i.1).2⁻¹) ^ 2 := by
      rw [mul_assoc, hu, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (h i.1) (sq_nonneg _)

private theorem finite_node_fibre {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p) (z : ℂ) :
    Finite {i : Occurrence p // node p i = z} := by
  let N := ⌊C * z.im ^ 2⌋₊
  have hi (i : {i : Occurrence p // node p i = z}) : i.val.1.val ≤ N := by
    apply Nat.le_floor
    have hb := index_le_height_sq h i.val
    rw [i.property] at hb
    linarith
  let f : {i : Occurrence p // node p i = z} → Fin (N + 1) × Bool :=
    fun i => (⟨i.val.1.val, Nat.lt_succ_of_le (hi i)⟩, i.val.2)
  apply Finite.of_injective f
  intro i j hij
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun q : Fin (N + 1) × Bool => q.1.val) hij
  · exact congrArg (fun q : Fin (N + 1) × Bool => q.2) hij

private theorem finite_node_window {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p)
    (a b : ℝ) : (Set.range (node p) ∩ {z | a < z.im ∧ z.im ≤ b}).Finite := by
  let R := max |a| |b| + 1
  let N := ⌊C * R ^ 2⌋₊ + 1
  have hC := bound_nonneg h
  refine (((Finset.range N).product (Finset.univ : Finset Bool)).finite_toSet.image
    (rawNode p)).subset ?_
  rintro z ⟨⟨i, rfl⟩, hai, hib⟩
  have hR : |(node p i).im| ≤ R := by
    apply abs_le.mpr
    constructor
    · dsimp only [R]
      linarith [neg_abs_le a, le_max_left |a| |b|]
    · dsimp only [R]
      linarith [le_abs_self b, le_max_right |a| |b|]
  have hs : (node p i).im ^ 2 ≤ R ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hR
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ R + (node p i).im by linarith)]
  have hin : i.1.val < N := by
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    have hi := index_le_height_sq h i
    have hc := mul_le_mul_of_nonneg_left hs hC
    linarith
  refine ⟨(i.1.val, i.2), ?_, rfl⟩
  change (i.1.val, i.2) ∈ (Finset.range N).product (Finset.univ : Finset Bool)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hin, Finset.mem_univ _⟩

/-- The reflected configuration represented by the slots, with collisions counted as multiplicity. -/
def config {C : ℝ} (p : ℕ → Slot) (h : CoordinateBound C p) : ZeroConfig where
  carrier := Set.range (node p)
  mult z := Nat.card {i : Occurrence p // node p i = z}
  one_le_mult z hz := by
    letI := finite_node_fibre h z
    obtain ⟨i, hi⟩ := hz
    letI : Nonempty {i : Occurrence p // node p i = z} := ⟨⟨i, hi⟩⟩
    exact Nat.card_pos
  strip := by
    rintro z ⟨⟨n, b⟩, rfl⟩
    cases b <;> dsimp [node, rawNode, slotPoint, reflect]
    · exact (p n).1.property
    · constructor <;> linarith [(p n).1.property.1, (p n).1.property.2]
  reflect_mem := by
    rintro z ⟨i, rfl⟩
    exact ⟨flip p i, node_flip p i⟩
  mult_reflect z _ := by
    apply Nat.card_congr
    refine ⟨fun i => ⟨flip p i.val, ?_⟩, fun i => ⟨flip p i.val, ?_⟩, ?_, ?_⟩
    · rw [node_flip, i.property, reflect_twice]
    · rw [node_flip, i.property]
    · intro i
      apply Subtype.ext
      exact flip_twice p i.val
    · intro i
      apply Subtype.ext
      exact flip_twice p i.val
  finite_window := finite_node_window h

theorem config_has_no_real_zeros {C : ℝ} (p : ℕ → Slot) (h : CoordinateBound C p) :
    ∀ z ∈ (config p h).carrier, z.im ≠ 0 := by
  rintro z ⟨i, rfl⟩
  rw [node_im]
  exact inv_ne_zero i.1.property

end GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
