import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

/-!
# Exact energy and mean under uniform prime-subset elimination

Grouping source labels by the unprocessed coordinates retains the complete signed
source. Uniform averaging gives the kernel `2^(-card(symmDiff))`; its empty-cofactor
mean weights each source by `2^(-card(label))`. The exact variance law bounds the
mean squared by averaged retained energy. Empty and complete elimination recover
the original diagonal and complete signed square, respectively.

No upper energy bound or cancellation hypothesis is introduced. The arithmetic
consumer supplies the actual divisor source and prime-factor labels.
-/

noncomputable section
open Finset
open scoped symmDiff
namespace RHTower
variable {α ι : Type*} [DecidableEq α]

/-- Uniform mean over every subset of one fixed coordinate packet. -/
def uniformSubsetMean (U : Finset α) (f : Finset α → ℝ) : ℝ :=
  (∑ P ∈ U.powerset, f P) / (2:ℝ)^U.card

/-- Exact inclusion probability for an entire prescribed coordinate set. -/
theorem uniformSubsetMean_contains (U T : Finset α) (hT : T ⊆ U) (c : ℝ) :
    uniformSubsetMean U (fun P => if T ⊆ P then c else 0) = c / (2:ℝ)^T.card := by
  rw [uniformSubsetMean, ← sum_filter, ← Icc_eq_filter_powerset]
  simp only [sum_const, nsmul_eq_mul, card_Icc_finset hT, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_sub₀ (2:ℝ) (by norm_num) (card_le_card hT)]
  field_simp

omit [DecidableEq α] in
/-- Finite source summation commutes with uniform subset averaging. -/
theorem uniformSubsetMean_sum (U : Finset α) (I : Finset ι) (f : ι → Finset α → ℝ) :
    uniformSubsetMean U (fun P => ∑ i ∈ I, f i P) =
      ∑ i ∈ I, uniformSubsetMean U (f i) := by
  simp only [uniformSubsetMean]
  rw [sum_comm, sum_div]

omit [DecidableEq α] in
/-- Exact variance gap, with the original signed mean retained. -/
theorem uniformSubsetMean_variance (U : Finset α) (f : Finset α → ℝ) :
    uniformSubsetMean U (fun P => (f P)^(2 : ℕ)) - (uniformSubsetMean U f)^(2 : ℕ) =
      uniformSubsetMean U (fun P => (f P-uniformSubsetMean U f)^(2 : ℕ)) := by
  have hpoint (P : Finset α) :
      (f P-uniformSubsetMean U f)^(2 : ℕ) = (f P)^(2 : ℕ)-2*uniformSubsetMean U f*f P+(uniformSubsetMean U f)^(2 : ℕ) := by ring
  simp_rw [hpoint]
  simp only [uniformSubsetMean, sum_add_distrib, sum_sub_distrib,
    ← mul_sum, sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring

omit [DecidableEq α] in
/-- The square of the uniform mean is bounded by the uniform square mean. -/
theorem uniformSubsetMean_sq_le (U : Finset α) (f : Finset α → ℝ) :
    (uniformSubsetMean U f)^(2 : ℕ) ≤ uniformSubsetMean U (fun P => (f P)^(2 : ℕ)) := by
  have h := uniformSubsetMean_variance U f
  have hn : 0 ≤ uniformSubsetMean U (fun P => (f P-uniformSubsetMean U f)^(2 : ℕ)) :=
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  linarith only [h,hn]

/-- Retain a source in the fibre of its unprocessed coordinate label. -/
def subsetLabelFibre (I : Finset ι) (a : ι → Finset α) (c : ι → ℝ)
    (P R : Finset α) : ℝ := ∑ i ∈ I, if a i \ P = R then c i else 0

/-- Sum the squares of every retained fibre, without normalization of the source. -/
def subsetLabelEnergy (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α) : ℝ := ∑ R ∈ U.powerset, (subsetLabelFibre I a c P R)^(2 : ℕ)

/-- Retained-square energy weighted by the number of coordinates still present
in its label.  Unlike ordinary energy, a pair that first meets only after all
of its coordinates are processed has zero weight at that meeting. -/
def subsetLabelArityEnergy (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α) : ℝ :=
  ∑ R ∈ U.powerset, (R.card : ℝ) * (subsetLabelFibre I a c P R)^(2 : ℕ)

private theorem sdiff_eq_iff_symmDiff_subset (S T P : Finset α) :
    S \ P = T \ P ↔ S ∆ T ⊆ P := by
  simp only [Finset.ext_iff, mem_sdiff, subset_iff, mem_symmDiff]
  constructor
  · intro h x hx
    by_contra hn
    have := h x
    tauto
  · intro h x
    constructor
    · rintro ⟨hx,hp⟩
      refine ⟨?_,hp⟩
      by_contra ht
      exact hp (h (Or.inl ⟨hx,ht⟩))
    · rintro ⟨hx,hp⟩
      refine ⟨?_,hp⟩
      by_contra hs
      exact hp (h (Or.inr ⟨hx,hs⟩))

/-- A pair interferes precisely when all its differing coordinates are processed. -/
theorem subsetLabelEnergy_eq_pairs (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) (P : Finset α) :
    subsetLabelEnergy U I a c P =
      ∑ i ∈ I, ∑ j ∈ I, if a i ∆ a j ⊆ P then c i*c j else 0 := by
  unfold subsetLabelEnergy subsetLabelFibre
  simp_rw [sq, sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [← sdiff_eq_iff_symmDiff_subset]
  have hm : a i \ P ∈ U.powerset := mem_powerset.mpr (sdiff_subset.trans (ha i hi))
  rw [sum_eq_single (a i \ P)]
  · by_cases h : a i \ P = a j \ P
    · simp [h]
    · simp [h,Ne.symm h]
  · intro R hR hne
    have hh : a i \ P ≠ R := Ne.symm hne
    simp [hh]
  · exact fun hn => (hn hm).elim

/-- Exact all-source pair expansion for arity-weighted retained energy.  The
pair weight is the cardinality of its common remaining label, retained without
an absolute-value or positivity relaxation. -/
theorem subsetLabelArityEnergy_eq_pairs (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) (P : Finset α) :
    subsetLabelArityEnergy U I a c P =
      ∑ i ∈ I, ∑ j ∈ I,
        if a i ∆ a j ⊆ P then ((a i \ P).card : ℝ) * c i * c j else 0 := by
  unfold subsetLabelArityEnergy subsetLabelFibre
  simp_rw [sq, sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  simp only [← sdiff_eq_iff_symmDiff_subset]
  have hm : a i \ P ∈ U.powerset := mem_powerset.mpr (sdiff_subset.trans (ha i hi))
  rw [sum_eq_single (a i \ P)]
  · by_cases h : a i \ P = a j \ P
    · simp [h]
      ring
    · simp [h, Ne.symm h]
  · intro R hR hne
    have hh : a i \ P ≠ R := Ne.symm hne
    simp [hh]
  · exact fun hn => (hn hm).elim

/-- Any additive label potential whose weight vanishes at the empty remaining
label is blind to a pair of disjoint source labels.  Before the pair can
interfere its indicator vanishes; once it can interfere, its common remaining
label is empty. -/
theorem weightedPair_zero_of_disjoint (w : ℕ → ℝ) (hw : w 0 = 0)
    (S T P : Finset α) (x y : ℝ) (hST : Disjoint S T) :
    (if S ∆ T ⊆ P then w (S \ P).card * x * y else 0) = 0 := by
  by_cases h : S ∆ T ⊆ P
  · rw [if_pos h]
    have hSP : S ⊆ P := by
      intro z hz
      apply h
      refine mem_symmDiff.mpr (Or.inl ⟨hz, ?_⟩)
      intro hzT
      exact disjoint_left.mp hST hz hzT
    rw [sdiff_eq_empty_iff_subset.mpr hSP]
    simp [hw]
  · simp [h]

/-- Arity-weighted elimination is the linear-weight instance of the universal
disjoint-pair blindness theorem. -/
theorem arityPair_zero_of_disjoint (S T P : Finset α) (x y : ℝ)
    (hST : Disjoint S T) :
    (if S ∆ T ⊆ P then ((S \ P).card : ℝ) * x * y else 0) = 0 := by
  simpa using weightedPair_zero_of_disjoint (fun n => (n : ℝ)) (by norm_num)
    S T P x y hST

/-- Exact uniform-averaged energy kernel on the original source labels. -/
theorem uniformSubsetMean_labelEnergy (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) :
    uniformSubsetMean U (subsetLabelEnergy U I a c) =
      ∑ i ∈ I, ∑ j ∈ I, c i*c j / (2:ℝ)^(a i ∆ a j).card := by
  change uniformSubsetMean U (fun P => subsetLabelEnergy U I a c P) = _
  simp_rw [subsetLabelEnergy_eq_pairs U I a c ha]
  rw [uniformSubsetMean_sum]
  apply sum_congr rfl
  intro i hi
  rw [uniformSubsetMean_sum]
  apply sum_congr rfl
  intro j hj
  apply uniformSubsetMean_contains
  intro p hp
  rcases mem_symmDiff.mp hp with h|h
  · exact ha i hi h.1
  · exact ha j hj h.1

/-- Exact retained-head mean: one reciprocal power of two per source coordinate. -/
theorem uniformSubsetMean_labelHead (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) :
    uniformSubsetMean U (fun P => subsetLabelFibre I a c P ∅) =
      ∑ i ∈ I, c i / (2:ℝ)^(a i).card := by
  simp only [subsetLabelFibre, sdiff_eq_empty_iff_subset]
  rw [uniformSubsetMean_sum]
  exact sum_congr rfl fun i hi => uniformSubsetMean_contains U (a i) (ha i hi) (c i)

/-- The actual retained-head mean squared is a lower bound for averaged energy. -/
theorem uniformSubsetMean_labelHead_sq_le_energy (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) :
    (∑ i ∈ I, c i / (2:ℝ)^(a i).card)^(2 : ℕ) ≤
      uniformSubsetMean U (subsetLabelEnergy U I a c) := by
  rw [← uniformSubsetMean_labelHead U I a c ha]
  refine (uniformSubsetMean_sq_le U _).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro P hP
  exact single_le_sum (fun R _ => sq_nonneg (subsetLabelFibre I a c P R))
    (show ∅ ∈ U.powerset by simp)


/-- Distinct source labels give exactly the original diagonal before elimination. -/
theorem subsetLabelEnergy_empty (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, a i = a j → i = j) :
    subsetLabelEnergy U I a c ∅ = ∑ i ∈ I, (c i)^(2 : ℕ) := by
  rw [subsetLabelEnergy_eq_pairs U I a c ha]
  apply sum_congr rfl
  intro i hi
  simp only [subset_empty, symmDiff_eq_empty]
  rw [sum_eq_single i]
  · simp [sq]
  · intro j hj hne
    have hne' : a i ≠ a j := fun h => hne (hinj i hi j hj h).symm
    simp [hne']
  · exact fun hn => (hn hi).elim

/-- Complete elimination gives exactly the squared complete signed source. -/
theorem subsetLabelEnergy_full (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) :
    subsetLabelEnergy U I a c U = (∑ i ∈ I, c i)^(2 : ℕ) := by
  rw [subsetLabelEnergy_eq_pairs U I a c ha,sq,sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hs : a i ∆ a j ⊆ U := by
    intro p hp
    rcases mem_symmDiff.mp hp with h|h
    · exact ha i hi h.1
    · exact ha j hj h.1
  rw [if_pos hs]



/-- Processing one coordinate is the literal signed merger of its two retained fibres. -/
theorem subsetLabelFibre_insert (I : Finset ι) (a : ι → Finset α) (c : ι → ℝ)
    (P R : Finset α) (p : α) :
    subsetLabelFibre I a c (insert p P) R =
      if p ∈ R then 0 else subsetLabelFibre I a c P R + subsetLabelFibre I a c P (insert p R) := by
  have hsplit (i : ι) : a i \ insert p P = (a i \ P).erase p := by
    ext x
    simp only [mem_sdiff,mem_insert,mem_erase]
    tauto
  by_cases hpR : p ∈ R
  · rw [if_pos hpR,subsetLabelFibre]
    apply sum_eq_zero
    intro i hi
    have hn : a i \ insert p P ≠ R := by
      intro h
      have hm : p ∉ a i \ insert p P := by simp
      exact hm (h.symm ▸ hpR)
    rw [if_neg hn]
  · rw [if_neg hpR,subsetLabelFibre,subsetLabelFibre,subsetLabelFibre,← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [hsplit]
    by_cases hpi : p ∈ a i \ P
    · have hn : a i \ P ≠ R := fun h => hpR (h ▸ hpi)
      simp only [erase_eq_iff_eq_insert hpi hpR,if_neg hn,zero_add]
    · have hn : a i \ P ≠ insert p R := by
        intro h
        exact hpi (h.symm ▸ mem_insert_self p R)
      rw [erase_eq_of_notMem hpi,if_neg hn,add_zero]

/-- Every intermediate partition preserves the complete signed source exactly. -/
theorem subsetLabelFibre_sum (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (ha : ∀ i ∈ I, a i ⊆ U) (P : Finset α) :
    (∑ R ∈ U.powerset, subsetLabelFibre I a c P R) = ∑ i ∈ I, c i := by
  unfold subsetLabelFibre
  simp_rw [← sum_filter]
  exact sum_fiberwise_of_maps_to
    (fun i hi => mem_powerset.mpr (sdiff_subset.trans (ha i hi))) c

end RHTower
