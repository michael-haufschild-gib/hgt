import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheExactCodebookSizeOfAZeroSample
import Mathlib.Data.Multiset.Sort

/-!
# Recovering the displacement multiset from minimum codebook sizes

A finite sample first needs two codewords below its largest positive
depth. Removing that single coordinate divides every codebook size by
a known positive factor. Iteration determines all positive depths,
including repetitions. Rational error tolerances above any prescribed
cutoff recover all depths strictly exceeding that cutoff.
-/

noncomputable section
open Finset Metric
open scoped NNReal ENNReal
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

private def intervals (h d : ℝ) : ℕ := max 1 ⌈d/h⌉₊
private def curve (xs : List ℝ) (h : ℝ) := (xs.map (intervals h)).prod

private theorem one_at_radius {xs : List ℝ} {h : ℝ} (hh : 0 < h) :
    curve xs h = 1 ↔ ∀ d ∈ xs, d ≤ h := by
  have hc (d : ℝ) : intervals h d = 1 ↔ d ≤ h := by
    rw [intervals,max_eq_left_iff,Nat.ceil_le,Nat.cast_one,div_le_one hh]
  induction xs with
  | nil => simp [curve]
  | cons x xs ih =>
    change intervals h x * curve xs h = 1 ↔ _
    rw [List.forall_mem_cons,←hc,←ih]
    constructor
    · intro H
      exact ⟨Nat.eq_one_of_mul_eq_one_right H,Nat.eq_one_of_mul_eq_one_left H⟩
    · rintro ⟨ha,hb⟩
      rw [ha,hb,one_mul]

private theorem head_bound {x b a : ℝ} {xs ys : List ℝ} (ha : 0 ≤ a) (hb : a ≤ b)
    (hy : ∀ d ∈ ys, d ≤ b)
    (he : ∀ q : ℚ, a < (q:ℝ) → curve (x::xs) q = curve ys q) : x ≤ b := by
  by_contra! h
  obtain ⟨q,hbq,hqx⟩ := exists_rat_btwn h
  have hq : 0 < (q:ℝ) := ha.trans_lt (hb.trans_lt hbq)
  have ho : curve ys q = 1 := (one_at_radius hq).mpr (fun d hd => (hy d hd).trans hbq.le)
  have hx := (one_at_radius hq).mp ((he q (hb.trans_lt hbq)).trans ho) x List.mem_cons_self
  exact (not_le_of_gt hqx) hx

private theorem descending_identified {a : ℝ} (ha : 0 ≤ a) (xs ys : List ℝ)
    (hx : ∀ d ∈ xs, a < d) (hy : ∀ d ∈ ys, a < d)
    (sx : xs.Pairwise (· ≥ ·)) (sy : ys.Pairwise (· ≥ ·))
    (he : ∀ q : ℚ, a < (q:ℝ) → curve xs q = curve ys q) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      exact ((not_le_of_gt (hy y List.mem_cons_self)) (head_bound ha (b:=a) le_rfl
        (ys:=[]) (by simp) (fun q hq => (he q hq).symm))).elim
  | cons x xs ih =>
    cases ys with
    | nil =>
      exact ((not_le_of_gt (hx x List.mem_cons_self)) (head_bound ha (b:=a) le_rfl
        (ys:=[]) (by simp) he)).elim
    | cons y ys =>
      obtain ⟨hmaxx,hsx⟩ := List.pairwise_cons.mp sx
      obtain ⟨hmaxy,hsy⟩ := List.pairwise_cons.mp sy
      have hxy := head_bound ha (hy y List.mem_cons_self).le (List.forall_mem_cons.mpr ⟨le_rfl,hmaxy⟩) he
      have hyx := head_bound ha (hx x List.mem_cons_self).le (List.forall_mem_cons.mpr ⟨le_rfl,hmaxx⟩)
        (fun q hq => (he q hq).symm)
      obtain rfl := le_antisymm hxy hyx
      congr 1
      apply ih ys (fun d hd => hx d (List.mem_cons_of_mem _ hd))
        (fun d hd => hy d (List.mem_cons_of_mem _ hd)) hsx hsy
      intro q hq
      exact Nat.eq_of_mul_eq_mul_left (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) (he q hq)

/-- Multiset of all sampled depths strictly above a given tolerance. -/
def sampleDepthsAbove (S : Finset ℂ) (a : ℝ) : Multiset ℝ :=
  (S.filter (fun z => a < rightDisplacement z)).val.map rightDisplacement

private def descending (S : Finset ℂ) (a : ℝ) := (sampleDepthsAbove S a).sort (· ≥ ·)

private theorem sample_curve (S : Finset ℂ) {a h : ℝ} (ha : a ≤ h) (hh : 0 < h) :
    curve (descending S a) h = zeroSampleCodeCount S h := by
  classical
  calc curve (descending S a) h = ((sampleDepthsAbove S a).map (intervals h)).prod := by
         rw [curve,← Multiset.prod_coe,← Multiset.map_coe,descending,Multiset.sort_eq]
    _ = ∏ z ∈ S.filter (fun z => a < rightDisplacement z), intervals h (rightDisplacement z) := by
         simp only [sampleDepthsAbove,Multiset.map_map,Finset.prod_map_val,Function.comp_def]
    _ = zeroSampleCodeCount S h := by
         apply Finset.prod_subset (filter_subset _ _)
         intro z hz hn
         have he : rightDisplacement z ≤ a :=
           le_of_not_gt (fun hd => hn (mem_filter.mpr ⟨hz,hd⟩))
         exact max_eq_left (Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using (div_le_one hh).mpr (he.trans ha)))

/-- Rational tolerances above a given cutoff recover exactly the multiset
of depths exceeding that cutoff, even for repeated depths. -/
theorem rational_code_curve_above_iff (S T : Finset ℂ) {a : ℝ} (ha : 0 ≤ a) :
    (∀ q : ℚ, a < (q:ℝ) → zeroSampleCodeCount S q = zeroSampleCodeCount T q) ↔
      sampleDepthsAbove S a = sampleDepthsAbove T a := by
  have hpos (U : Finset ℂ) (d : ℝ) (hd : d ∈ descending U a) : a < d := by
    have hm : d ∈ sampleDepthsAbove U a := (Multiset.mem_sort (· ≥ ·)).mp hd
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hm
    exact (Finset.mem_filter.mp hz).2
  constructor
  · intro H
    have hl := descending_identified ha _ _ (hpos S) (hpos T) (Multiset.pairwise_sort _ _)
      (Multiset.pairwise_sort _ _) (fun q hq => (sample_curve S hq.le (ha.trans_lt hq)).trans
        ((H q hq).trans (sample_curve T hq.le (ha.trans_lt hq)).symm))
    simpa only [descending,Multiset.sort_eq] using congrArg (fun l : List ℝ => (l:Multiset ℝ)) hl
  · intro H q hq
    rw [← sample_curve S hq.le (ha.trans_lt hq),← sample_curve T hq.le (ha.trans_lt hq)]
    simp only [descending,H]

/-- All positive radii recover the nonzero widths. -/
theorem code_counts_identify_positive_depths (S T : Finset ℂ) :
    (∀ q : ℚ, 0 < q → zeroSampleCodeCount S q = zeroSampleCodeCount T q) ↔
      sampleDepthsAbove S 0 = sampleDepthsAbove T 0 := by
  simpa only [Rat.cast_pos] using rational_code_curve_above_iff S T (a:=0) le_rfl

/-- The full external covering-number curve is a complete invariant of
the nonzero independent coordinate widths, counted with multiplicity. -/
theorem zero_covering_curves_iff (S T : Finset ℂ) :
    (∀ h : ℝ≥0, 0 < h → externalCoveringNumber h (zeroDisplacementBox S) =
      externalCoveringNumber h (zeroDisplacementBox T)) ↔ sampleDepthsAbove S 0 = sampleDepthsAbove T 0 := by
  constructor
  · intro H
    apply (code_counts_identify_positive_depths S T).mp
    intro q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    let r : ℝ≥0 := ⟨q,hqr.le⟩
    have hr : 0 < r := hqr
    have he := H r hr
    rw [zero_sample_codebook_size S hr,zero_sample_codebook_size T hr] at he
    exact_mod_cast he
  · intro H h hh
    rw [zero_sample_codebook_size S hh,zero_sample_codebook_size T hh]
    congr 1
    rw [← sample_curve S (a:=0) hh.le hh,← sample_curve T (a:=0) hh.le hh]
    simp only [descending,H]

#print axioms rational_code_curve_above_iff
#print axioms code_counts_identify_positive_depths
#print axioms zero_covering_curves_iff

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
