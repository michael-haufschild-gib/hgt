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


/-- Summing labelled occurrences agrees with summing the resulting integer multiplicities. -/
theorem hasSum_node {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p) (F : ℂ → E)
    (hs : Summable (fun i : Occurrence p => F (node p i))) :
    HasSum (fun z : (config p h).carrier => (config p h).mult z • F z)
      (∑' i : Occurrence p, F (node p i)) := by
  let g : Occurrence p → (config p h).carrier := fun i => ⟨node p i, ⟨i, rfl⟩⟩
  have hh := hs.hasSum.tsum_fiberwise g
  convert hh using 1
  funext z
  have he : (g ⁻¹' {z}) = {i : Occurrence p | node p i = z.val} := by
    ext i
    exact Subtype.ext_iff
  have hc : Nat.card ↑(g ⁻¹' {z}) = (config p h).mult z := by
    exact Nat.card_congr (Equiv.setCongr he)
  symm
  calc
    _ = ∑' _ : g ⁻¹' {z}, F z := by
      apply tsum_congr
      intro i
      exact congrArg F (congrArg Subtype.val i.property)
    _ = Nat.card ↑(g ⁻¹' {z}) • F z := tsum_const _
    _ = _ := by rw [hc]

private theorem node_temperedWeight_le (p : ℕ → Slot) (i : Occurrence p) :
    1 / (1 + Complex.normSq (gammaOf (node p i))) ≤ (p i.1).2 ^ 2 := by
  have hi : (gammaOf (node p i)).re = (p i.1).2⁻¹ := by
    simpa [gammaOf] using node_im p i
  have hid : (p i.1).2 ^ 2 * ((p i.1).2⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ i.1.property, one_pow]
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _))).mpr
  rw [Complex.normSq_apply, hi]
  nlinarith only [sq_nonneg (p i.1).2,
    mul_nonneg (sq_nonneg (p i.1).2) (sq_nonneg (gammaOf (node p i)).im), hid]

/-- A finite total inverse-square mass gives temperedness, including all collisions. -/
theorem tempered_config {C : ℝ} {p : ℕ → Slot} (h : CoordinateBound C p)
    (hs : Summable (fun n => (p n).2 ^ 2)) : TemperedConfig (config p h) := by
  have hs' := hs.subtype (fun n => (p n).2 ≠ 0)
  have ho : Summable (fun i : Occurrence p => (p i.1).2 ^ 2) := by
    apply (summable_prod_of_nonneg (f := fun i : Occurrence p => (p i.1).2 ^ 2)
      (fun _ => sq_nonneg _)).mpr
    refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
    simpa only [tsum_bool, ← two_mul, Function.comp_apply] using hs'.mul_left 2
  have hw : Summable (fun i : Occurrence p =>
      1 / (1 + Complex.normSq (gammaOf (node p i)))) :=
    Summable.of_nonneg_of_le (fun _ => div_nonneg zero_le_one
      (add_nonneg zero_le_one (Complex.normSq_nonneg _))) (node_temperedWeight_le p) ho
  have hh := (hasSum_node h (fun z => 1 / (1 + Complex.normSq (gammaOf z))) hw).summable
  simpa only [TemperedConfig, nsmul_eq_mul, mul_one_div] using hh

/-- Temperedness controls inverse-square ordinates away from finitely many low zeros. -/
theorem summable_inverse_ordinate_sq (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) :
    Summable (fun z : Z.carrier => (Z.mult z : ℝ) * z.val.im⁻¹ ^ 2) := by
  have hf : {z : Z.carrier | |z.val.im| < 1}.Finite := by
    apply ((Z.finite_window (-1) 1).preimage Subtype.val_injective.injOn).subset
    intro z hz
    exact ⟨z.property, (abs_lt.mp hz).1, (abs_lt.mp hz).2.le⟩
  apply (hZ.mul_left 3).of_norm_bounded_eventually
  filter_upwards [hf.compl_mem_cofinite] with z hz
  have habs : 1 ≤ |z.val.im| := le_of_not_gt hz
  have hs : 1 ≤ z.val.im ^ 2 := by nlinarith [sq_abs z.val.im]
  have hg : Complex.normSq (gammaOf z.val) = z.val.im ^ 2 + (1 / 2 - z.val.re) ^ 2 := by
    simp [Complex.normSq_apply, gammaOf, pow_two]
  have hstrip := Z.strip z z.property
  have hdepth : (1 / 2 - z.val.re) ^ 2 ≤ 1 / 4 := by nlinarith [hstrip.1, hstrip.2]
  have hden : 1 + Complex.normSq (gammaOf z.val) ≤ 3 * z.val.im ^ 2 := by
    rw [hg]
    linarith
  have ht : z.val.im⁻¹ ^ 2 * z.val.im ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (hnoreal z z.property), one_pow]
  have hw : z.val.im⁻¹ ^ 2 ≤ 3 / (1 + Complex.normSq (gammaOf z.val)) := by
    apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (Complex.normSq_nonneg _))).mpr
    have h := mul_le_mul_of_nonneg_left hden (sq_nonneg z.val.im⁻¹)
    nlinarith only [h, ht]
  change ‖(Z.mult z : ℝ) * z.val.im⁻¹ ^ 2‖ ≤
    3 * ((Z.mult z : ℝ) / (1 + Complex.normSq (gammaOf z.val)))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (Z.mult z) : (0 : ℝ) ≤ Z.mult z)
  calc
    _ ≤ (Z.mult z : ℝ) * (3 / (1 + Complex.normSq (gammaOf z.val))) := h
    _ = _ := by ring

/-- Copies retain the natural multiplicity of each zero. -/
abbrev Copy (Z : ZeroConfig) := (z : Z.carrier) × Fin (Z.mult z)

def copyWeight (Z : ZeroConfig) (i : Copy Z) : ℝ := i.1.val.im⁻¹ ^ 2

theorem summable_copyWeight (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) : Summable (copyWeight Z) := by
  apply (summable_sigma_of_nonneg (f := copyWeight Z)
    (fun i => sq_nonneg i.1.val.im⁻¹)).mpr
  refine ⟨fun _ => summable_of_hasFiniteSupport (Set.toFinite _), ?_⟩
  simpa only [copyWeight, tsum_const, Nat.card_fin, nsmul_eq_mul] using
    summable_inverse_ordinate_sq Z hZ hnoreal


/-- The total inverse-square mass, expressed by closed finite partial-sum constraints. -/
def MassBound (C : ℝ) (p : ℕ → Slot) : Prop :=
  ∀ N : ℕ, ∑ n ∈ Finset.range N, (p n).2 ^ 2 ≤ C

/-- A bounded label carries a zero separated both from the line and from infinite height. -/
def Protected (K : ℕ) (p : ℕ → Slot) : Prop :=
  ∃ n : Fin (K + 1), 1 / ((K : ℝ) + 1) ≤ |((p n).1 : ℝ) - 1 / 2| ∧
    1 / ((K : ℝ) + 1) ≤ |(p n).2|

/-- Closed families retain an off-line occurrence under limits. -/
def family (K : ℕ) : Set (ℕ → Slot) :=
  {p | CoordinateBound K p ∧ MassBound K p ∧ Protected K p}

theorem summable_of_massBound {C : ℝ} {p : ℕ → Slot} (h : MassBound C p) :
    Summable (fun n => (p n).2 ^ 2) :=
  summable_of_sum_range_le (fun _ => sq_nonneg _) h

private theorem continuous_slot_re (n : ℕ) :
    Continuous (fun p : ℕ → Slot => ((p n).1 : ℝ)) :=
  continuous_subtype_val.comp (continuous_fst.comp (continuous_apply n))

private theorem continuous_slot_im (n : ℕ) :
    Continuous (fun p : ℕ → Slot => (p n).2) :=
  continuous_snd.comp (continuous_apply n)

private theorem isClosed_coordinateBound (C : ℝ) :
    IsClosed {p : ℕ → Slot | CoordinateBound C p} := by
  simp only [CoordinateBound, Set.setOf_forall]
  exact isClosed_iInter fun n =>
    isClosed_le ((continuous_slot_im n).pow 2 |>.const_mul _) continuous_const

private theorem isClosed_massBound (C : ℝ) :
    IsClosed {p : ℕ → Slot | MassBound C p} := by
  simp only [MassBound, Set.setOf_forall]
  apply isClosed_iInter
  intro N
  exact isClosed_le (continuous_finsetSum _ (fun n _ => (continuous_slot_im n).pow 2))
    continuous_const

private theorem isClosed_protected (K : ℕ) :
    IsClosed {p : ℕ → Slot | Protected K p} := by
  simp only [Protected, Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  intro n
  exact (isClosed_le continuous_const ((continuous_slot_re n).sub continuous_const).abs).inter
    (isClosed_le continuous_const (continuous_slot_im n).abs)

/-- Bounded inverse-square mass and a protected off-line occurrence give compact charts. -/
theorem isCompact_family (K : ℕ) : IsCompact (family K) := by
  have hc : IsClosed (family K) := (isClosed_coordinateBound K).inter
    ((isClosed_massBound K).inter (isClosed_protected K))
  have hi : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) 1)) := isCompact_univ
  have hb : IsCompact {p : ℕ → Slot | ∀ n,
      p n ∈ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ×ˢ
        Set.Icc (-((K : ℝ) + 1)) ((K : ℝ) + 1)} :=
    isCompact_pi_infinite fun _ => hi.prod isCompact_Icc
  apply hb.of_isClosed_subset hc
  intro p hp n
  refine ⟨Set.mem_univ _, ?_⟩
  have h := hp.1 n
  have hs : (p n).2 ^ 2 ≤ (K : ℝ) := by
    nlinarith only [h, mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg (p n).2)]
  constructor <;> nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K), sq_nonneg ((p n).2 + 1),
    sq_nonneg ((p n).2 - 1)]

/-- Every member of a compact family is tempered and contains a genuine off-line zero. -/
theorem family_config_impure (K : ℕ) {p : ℕ → Slot} (hp : p ∈ family K) :
    TemperedConfig (config p hp.1) ∧
      ∃ z ∈ (config p hp.1).carrier, z.re ≠ 1 / 2 := by
  refine ⟨tempered_config hp.1 (summable_of_massBound hp.2.1), ?_⟩
  obtain ⟨n, hr, ht⟩ := hp.2.2
  have ht0 : (p n).2 ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    exact (one_div_pos.mpr (by positivity : (0 : ℝ) < (K : ℝ) + 1)).not_ge ht
  let i : Occurrence p := (⟨n, ht0⟩, false)
  refine ⟨node p i, ⟨i, rfl⟩, ?_⟩
  change ((p n).1 : ℝ) ≠ 1 / 2
  intro he
  rw [he, sub_self, abs_zero] at hr
  exact (one_div_pos.mpr (by positivity : (0 : ℝ) < (K : ℝ) + 1)).not_ge hr

private instance (Z : ZeroConfig) : Countable (Copy Z) := by
  letI : Countable Z.carrier := (countable_carrier Z).to_subtype
  infer_instance

private def copyIndex (Z : ZeroConfig) : Copy Z → ℕ :=
  Classical.choose (Countable.exists_injective_nat (Copy Z))

private theorem copyIndex_injective (Z : ZeroConfig) : Function.Injective (copyIndex Z) :=
  Classical.choose_spec (Countable.exists_injective_nat (Copy Z))

/-- Label occurrences in decreasing inverse-square height. -/
def label (Z : ZeroConfig) : Copy Z → ℕ := rank (copyWeight Z) (copyIndex Z)

private theorem copyWeight_pos (Z : ZeroConfig)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) (i : Copy Z) : 0 < copyWeight Z i :=
  sq_pos_of_ne_zero (inv_ne_zero (hnoreal i.1 i.1.property))

theorem label_injective (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) : Function.Injective (label Z) :=
  rank_injective _ _ (summable_copyWeight Z hZ hnoreal) (copyWeight_pos Z hnoreal)
    (copyIndex_injective Z)

private def copySlot (Z : ZeroConfig) (i : Copy Z) : Slot :=
  (⟨i.1.val.re, Z.strip i.1 i.1.property⟩, i.1.val.im⁻¹)

private def absentSlot : Slot := (⟨0, by constructor <;> norm_num⟩, 0)

/-- Unused labels become absent points at infinite height. -/
def encoding (Z : ZeroConfig) : ℕ → Slot :=
  Function.extend (label Z) (copySlot Z) (fun _ => absentSlot)

theorem encoding_label (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) (i : Copy Z) :
    encoding Z (label Z i) = copySlot Z i :=
  (label_injective Z hZ hnoreal).extend_apply _ _ i

private theorem encoding_absent (Z : ZeroConfig) {n : ℕ} (h : n ∉ Set.range (label Z)) :
    encoding Z n = absentSlot := Function.extend_apply' _ _ n h

/-- Every nonempty encoded slot comes from one occurrence of the original configuration. -/
theorem encoding_active (Z : ZeroConfig) {n : ℕ} (h : (encoding Z n).2 ≠ 0) :
    n ∈ Set.range (label Z) := by
  by_contra hn
  exact h (congrArg Prod.snd (encoding_absent Z hn))

/-- Ranking bounds every coordinate by the same total inverse-square mass. -/
theorem coordinateBound_encoding (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) :
    CoordinateBound (∑' i, copyWeight Z i) (encoding Z) := by
  intro n
  by_cases hn : n ∈ Set.range (label Z)
  · obtain ⟨i, rfl⟩ := hn
    rw [encoding_label Z hZ hnoreal]
    exact rank_mul_le _ _ (summable_copyWeight Z hZ hnoreal) (copyWeight_pos Z hnoreal) i
  · rw [encoding_absent Z hn]
    dsimp [absentSlot]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact tsum_nonneg (fun i => (copyWeight_pos Z hnoreal i).le)

/-- Encoding preserves the full inverse-square mass. -/
theorem hasSum_encoding_sq (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) :
    HasSum (fun n => (encoding Z n).2 ^ 2) (∑' i, copyWeight Z i) := by
  have hi := label_injective Z hZ hnoreal
  have hz : ∀ n ∉ Set.range (label Z), (encoding Z n).2 ^ 2 = 0 := by
    intro n hn
    rw [encoding_absent Z hn]
    norm_num [absentSlot]
  apply (hi.hasSum_iff hz).mp
  apply (summable_copyWeight Z hZ hnoreal).hasSum.congr_fun
  intro i
  change (encoding Z (label Z i)).2 ^ 2 = copyWeight Z i
  rw [encoding_label Z hZ hnoreal]
  rfl


/-- Increasing a chart index relaxes all three bounds. -/
theorem family_mono {K L : ℕ} (hKL : K ≤ L) : family K ⊆ family L := by
  intro p hp
  have hKL' : (K : ℝ) ≤ L := by exact_mod_cast hKL
  refine ⟨fun n => (hp.1 n).trans hKL', (fun N => (hp.2.1 N).trans hKL'), ?_⟩
  obtain ⟨n, hr, ht⟩ := hp.2.2
  have hε : 1 / ((L : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact ⟨⟨n, Nat.lt_of_lt_of_le n.isLt (Nat.add_le_add_right hKL 1)⟩,
    hε.trans hr, hε.trans ht⟩

private theorem reciprocal_index_le {a : ℝ} (ha : 0 < a) {K : ℕ}
    (h : a⁻¹ ≤ (K : ℝ)) : 1 / ((K : ℝ) + 1) ≤ a := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)).mpr
  calc
    1 = a * a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
    _ ≤ a * ((K : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) ha.le

/-- Every impure tempered configuration without real zeros belongs to a compact chart after
encoding its occurrences. No attained-top hypothesis is used. -/
theorem exists_family_encoding (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0)
    (himpure : ∃ z ∈ Z.carrier, z.re ≠ 1 / 2) :
    ∃ K : ℕ, encoding Z ∈ family K := by
  obtain ⟨z, hz, hzre⟩ := himpure
  let i : Copy Z := ⟨⟨z, hz⟩, ⟨0, Z.one_le_mult z hz⟩⟩
  let ε := |z.re - 1 / 2|
  let τ := |z.im⁻¹|
  have hε : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr hzre)
  have hτ : 0 < τ := abs_pos.mpr (inv_ne_zero (hnoreal z hz))
  let M := ∑' j, copyWeight Z j
  obtain ⟨K, hK⟩ := exists_nat_gt (max M (max (label Z i : ℝ) (max ε⁻¹ τ⁻¹)))
  have hM : M ≤ (K : ℝ) := (le_max_left _ _).trans hK.le
  have hn : label Z i ≤ K := by
    exact_mod_cast (le_max_left (label Z i : ℝ) (max ε⁻¹ τ⁻¹)).trans
      ((le_max_right M _).trans hK.le)
  have hεK : ε⁻¹ ≤ (K : ℝ) := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right M _).trans hK.le))
  have hτK : τ⁻¹ ≤ (K : ℝ) := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right M _).trans hK.le))
  have hsum := hasSum_encoding_sq Z hZ hnoreal
  refine ⟨K, (fun n => (coordinateBound_encoding Z hZ hnoreal n).trans hM), ?_, ?_⟩
  · intro N
    have h := hsum.summable.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _)
    rw [hsum.tsum_eq] at h
    exact h.trans hM
  · refine ⟨⟨label Z i, Nat.lt_succ_of_le hn⟩, ?_, ?_⟩
    · simpa only [encoding_label Z hZ hnoreal, copySlot] using reciprocal_index_le hε hεK
    · simpa only [encoding_label Z hZ hnoreal, copySlot] using reciprocal_index_le hτ hτK

/-- Active labels are exactly the original zero occurrences. -/
def activeEquiv (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) :
    Copy Z ≃ {n : ℕ // (encoding Z n).2 ≠ 0} := by
  let f : Copy Z → {n : ℕ // (encoding Z n).2 ≠ 0} := fun i =>
    ⟨label Z i, by
      rw [encoding_label Z hZ hnoreal]
      exact inv_ne_zero (hnoreal i.1 i.1.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact label_injective Z hZ hnoreal (congrArg Subtype.val hij)
  · intro n
    obtain ⟨i, hi⟩ := encoding_active Z n.property
    exact ⟨i, Subtype.ext hi⟩

private theorem activeEquiv_val (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) (i : Copy Z) :
    (activeEquiv Z hZ hnoreal i).val = label Z i := rfl

private theorem node_activeEquiv (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0) (i : Copy Z) (b : Bool) :
    node (encoding Z) (activeEquiv Z hZ hnoreal i, b) =
      if b then reflect i.1.val else i.1.val := by
  have hpoint : slotPoint (encoding Z (label Z i)) = i.1.val := by
    rw [encoding_label Z hZ hnoreal]
    apply Complex.ext <;> simp [slotPoint, copySlot]
  change (if b then reflect (slotPoint (encoding Z (label Z i))) else
    slotPoint (encoding Z (label Z i))) = _
  rw [hpoint]

/-- Horizontal reflection doubles a reflection-invariant configuration, preserving its sums. -/
theorem tsum_encoding_eq_double {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ z ∈ Z.carrier, z.im ≠ 0)
    {C : ℝ} (hc : CoordinateBound C (encoding Z)) (F : ℂ → E)
    (hs : Summable (fun i : Occurrence (encoding Z) => F (node (encoding Z) i))) :
    (∑' z : (config (encoding Z) hc).carrier, (config (encoding Z) hc).mult z • F z) =
      2 • ∑' z : Z.carrier, Z.mult z • F z := by
  let e := (activeEquiv Z hZ hnoreal).prodCongr (Equiv.refl Bool)
  have hcopies : Summable (fun i : Copy Z × Bool =>
      F (if i.2 then reflect i.1.1.val else i.1.1.val)) := by
    apply (e.summable_iff.mpr hs).congr
    intro i
    exact congrArg F (node_activeEquiv Z hZ hnoreal i.1 i.2)
  have h0 : Summable (fun i : Copy Z => F i.1.val) := by
    have hh := hcopies.comp_injective
      (show Function.Injective (fun i : Copy Z => (i, false)) from fun _ _ h => congrArg Prod.fst h)
    exact hh.congr (fun i => by simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte])
  have h1 : Summable (fun i : Copy Z => F (reflect i.1.val)) := by
    have hh := hcopies.comp_injective
      (show Function.Injective (fun i : Copy Z => (i, true)) from fun _ _ h => congrArg Prod.fst h)
    exact hh.congr (fun i => by simp only [Function.comp_apply, ↓reduceIte])
  have h0sum : (∑' i : Copy Z, F i.1.val) = ∑' z : Z.carrier, Z.mult z • F z := by
    simpa only [tsum_const, Nat.card_fin] using h0.tsum_sigma
  have h1sum : (∑' i : Copy Z, F (reflect i.1.val)) =
      ∑' z : Z.carrier, Z.mult z • F (reflect z.val) := by
    simpa only [tsum_const, Nat.card_fin] using h1.tsum_sigma
  let r : Z.carrier ≃ Z.carrier :=
    ⟨fun z => ⟨reflect z.val, Z.reflect_mem z z.property⟩,
      fun z => ⟨reflect z.val, Z.reflect_mem z z.property⟩,
      fun z => Subtype.ext (reflect_twice z), fun z => Subtype.ext (reflect_twice z)⟩
  have hr : (∑' z : Z.carrier, Z.mult z • F (reflect z.val)) =
      ∑' z : Z.carrier, Z.mult z • F z := by
    have he := r.tsum_eq (fun z : Z.carrier => Z.mult z • F z)
    change (∑' z : Z.carrier, Z.mult (reflect z.val) • F (reflect z.val)) = _ at he
    simpa only [Z.mult_reflect _ (Subtype.property _)] using he
  calc
    _ = ∑' i : Occurrence (encoding Z), F (node (encoding Z) i) :=
      (hasSum_node hc F hs).tsum_eq
    _ = ∑' i : Copy Z × Bool, F (if i.2 then reflect i.1.1.val else i.1.1.val) := by
      rw [← e.tsum_eq (fun i : Occurrence (encoding Z) => F (node (encoding Z) i))]
      apply tsum_congr
      intro i
      exact congrArg F (node_activeEquiv Z hZ hnoreal i.1 i.2)
    _ = ∑' i : Copy Z, (F i.1.val + F (reflect i.1.val)) := by
      rw [hcopies.tsum_prod]
      apply tsum_congr
      intro i
      simp only [tsum_bool, Bool.false_eq_true, ↓reduceIte]
    _ = _ := by rw [h0.tsum_add h1, h0sum, h1sum, hr, two_nsmul]

#print axioms tempered_config
#print axioms isCompact_family
#print axioms exists_family_encoding
#print axioms tsum_encoding_eq_double

end GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
