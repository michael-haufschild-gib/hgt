import GaloisForLFunctions.HTGeometry.PositiveKernels.PerronComparison
import Mathlib.Data.NNReal.Basic

/-!
# Perron response to a rank-one coupling at a diagonal spectral edge

The secular equation separates the mass on the maximal diagonal levels
from the resolvent of the lower levels. This gives the first two response
coefficients even when the highest diagonal level is repeated.
-/

open Filter Finset Matrix Set Topology
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry.EntrywisePositiveKernel

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- A nonnegative diagonal with a strictly positive rank-one coupling. -/
def diagonalRankOneKernel (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) (t : Ioi (0 : ℝ)) :
    EntrywisePositiveKernel ι :=
  ⟨fun i j => (if i = j then (d i : ℝ) else 0) + (t : ℝ) * (u i : ℝ) * (v j : ℝ),
    fun i j => add_pos_of_nonneg_of_pos
      (by split <;> positivity) (mul_pos (mul_pos t.2 (u i).2) (v j).2)⟩

/-- The highest diagonal level of the uncoupled kernel. -/
def diagonalCeiling (d : ι → ℝ≥0) : ℝ := univ.sup' univ_nonempty fun i => (d i : ℝ)

omit [DecidableEq ι] in
/-- Each diagonal level lies below the uncoupled spectral edge. -/
theorem le_diagonalCeiling (d : ι → ℝ≥0) (i : ι) : (d i : ℝ) ≤ diagonalCeiling d :=
  le_sup' (fun j => (d j : ℝ)) (mem_univ i)

/-- The total rank-one weight on the highest diagonal level. -/
def diagonalTopWeight (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) : ℝ :=
  ∑ i ∈ (univ : Finset ι).filter (fun i => (d i : ℝ) = diagonalCeiling d), (u i : ℝ) * (v i : ℝ)

/-- The rank-one resolvent with the highest diagonal level removed. -/
def diagonalLowerResolvent (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) (z : ℝ) : ℝ :=
  ∑ i ∈ (univ : Finset ι).filter (fun i => (d i : ℝ) ≠ diagonalCeiling d),
    ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))

/-- The coupled Perron root, with its diagonal limit at zero coupling. -/
def diagonalRankOneRoot (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) (t : ℝ) : ℝ :=
  if ht : 0 < t then (diagonalRankOneKernel d u v ⟨t, ht⟩).perronRoot else diagonalCeiling d

omit [Nonempty ι] in
/-- Matrix multiplication splits into the diagonal term and a single weighted sum. -/
theorem diagonalRankOneKernel_mulVec (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ))
    (t : Ioi (0 : ℝ)) (x : ι → ℝ) (i : ι) :
    ((diagonalRankOneKernel d u v t).val *ᵥ x) i =
      (d i : ℝ) * x i + ((t : ℝ) * (u i : ℝ)) * ∑ j, (v j : ℝ) * x j := by
  change (∑ j, ((if i = j then (d i : ℝ) else 0) + (t : ℝ) * (u i : ℝ) * (v j : ℝ)) * x j) = _
  simp only [add_mul, sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    mul_sum, mul_assoc]

/-- The coupled root lies above every diagonal pole and solves the secular
equation with the residue of each pole given by its rank-one weight. -/
theorem diagonalRankOneRoot_secular (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t : ℝ} (ht : 0 < t) :
    diagonalCeiling d < diagonalRankOneRoot d u v t ∧
      t * (∑ i, ((u i : ℝ) * (v i : ℝ)) / (diagonalRankOneRoot d u v t - (d i : ℝ))) = 1 := by
  let K := diagonalRankOneKernel d u v ⟨t, ht⟩
  let z := K.perronRoot
  rw [diagonalRankOneRoot, dif_pos ht]
  change diagonalCeiling d < z ∧ t * (∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))) = 1
  obtain ⟨_, x, _, hxp, hx⟩ := perronRoot_spec K
  let Q := ∑ i, (v i : ℝ) * x i
  have hQ : 0 < Q := sum_pos (fun i _ => mul_pos (v i).2 (hxp i)) univ_nonempty
  have hrow (i : ι) : (z - (d i : ℝ)) * x i = t * (u i : ℝ) * Q := by
    have he : (K.val *ᵥ x) i = z * x i := congrFun hx i
    change ((diagonalRankOneKernel d u v ⟨t, ht⟩).val *ᵥ x) i = z * x i at he
    rw [diagonalRankOneKernel_mulVec] at he
    change (d i : ℝ) * x i + t * (u i : ℝ) * Q = z * x i at he
    rw [sub_mul]
    linarith only [he]
  have hd (i : ι) : (d i : ℝ) < z := by
    have he : 0 < (z - (d i : ℝ)) * x i := by
      rw [hrow i]
      exact mul_pos (mul_pos ht (u i).2) hQ
    exact sub_pos.mp (pos_of_mul_pos_left he (hxp i).le)
  constructor
  · obtain ⟨i, _, hi⟩ := exists_mem_eq_sup' univ_nonempty (fun i => (d i : ℝ))
    change diagonalCeiling d = (d i : ℝ) at hi
    rw [hi]
    exact hd i
  · have hxi (i : ι) : x i = t * (u i : ℝ) * Q / (z - (d i : ℝ)) := by
      apply (eq_div_iff (sub_pos.mpr (hd i)).ne').mpr
      rw [mul_comm]
      exact hrow i
    have hsum : Q = Q * (t * ∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))) := by
      conv_lhs => unfold Q
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro i _
      rw [hxi i]
      ring
    apply mul_left_cancel₀ hQ.ne'
    simpa only [mul_one] using hsum.symm

/-- Above the diagonal edge the secular equation determines the root. -/
theorem diagonalRankOneRoot_eq_of_secular (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t z : ℝ}
    (ht : 0 < t) (hz : diagonalCeiling d < z)
    (he : t * (∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))) = 1) :
    diagonalRankOneRoot d u v t = z := by
  rw [diagonalRankOneRoot, dif_pos ht]
  let x : ι → ℝ := fun i => (u i : ℝ) / (z - (d i : ℝ))
  have hd (i : ι) : 0 < z - (d i : ℝ) := sub_pos.mpr ((le_diagonalCeiling d i).trans_lt hz)
  have hxp (i : ι) : 0 < x i := div_pos (u i).2 (hd i)
  refine (eq_perronRoot_of_positive_eigenvector _ x hxp z ?_).symm
  funext i
  rw [diagonalRankOneKernel_mulVec]
  change (d i : ℝ) * x i + t * (u i : ℝ) * (∑ j, (v j : ℝ) * x j) = z * x i
  have hQ : t * (∑ j, (v j : ℝ) * x j) = 1 := by
    have he' : (∑ j, (v j : ℝ) * x j) = ∑ j, ((u j : ℝ) * (v j : ℝ)) / (z - (d j : ℝ)) :=
      sum_congr rfl fun j _ => by dsimp only [x]; ring
    rwa [he']
  have hcoord : (z - (d i : ℝ)) * x i = (u i : ℝ) := by
    dsimp only [x]
    rw [mul_comm, div_mul_cancel₀ _ (hd i).ne']
  rw [show t * (u i : ℝ) * (∑ j, (v j : ℝ) * x j) = (u i : ℝ) from by
    rw [mul_comm t (u i : ℝ), mul_assoc, hQ, mul_one]]
  rw [sub_mul] at hcoord
  linarith only [hcoord]

omit [DecidableEq ι] in
private theorem diagonalSecularSum_pos (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {z : ℝ}
    (hz : diagonalCeiling d < z) : 0 < ∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ)) :=
  sum_pos (fun i _ => div_pos (mul_pos (u i).2 (v i).2)
    (sub_pos.mpr ((le_diagonalCeiling d i).trans_lt hz))) univ_nonempty

/-- Any level above the diagonal edge is reached at the reciprocal of its
secular sum. This includes the level-one coupling threshold. -/
theorem diagonalRankOneRoot_eq_iff (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) (t : Ioi (0 : ℝ)) (z : ℝ) :
    diagonalRankOneRoot d u v t = z ↔ diagonalCeiling d < z ∧
      (t : ℝ) = 1 / (∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))) := by
  constructor
  · intro h
    obtain ⟨hz, he⟩ := diagonalRankOneRoot_secular d u v t.2
    rw [h] at hz he
    exact ⟨hz, (eq_div_iff (diagonalSecularSum_pos d u v hz).ne').mpr he⟩
  · rintro ⟨hz, he⟩
    exact diagonalRankOneRoot_eq_of_secular d u v t.2 hz
      ((eq_div_iff (diagonalSecularSum_pos d u v hz).ne').mp he)

/-- Every level above the diagonal edge is attained at exactly one
positive coupling. -/
theorem existsUnique_diagonalRankOneRoot_eq (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {z : ℝ}
    (hz : diagonalCeiling d < z) : ∃! t : Ioi (0 : ℝ), diagonalRankOneRoot d u v t = z := by
  let t : Ioi (0 : ℝ) := ⟨1 / (∑ i, ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))),
    div_pos zero_lt_one (diagonalSecularSum_pos d u v hz)⟩
  refine ⟨t, (diagonalRankOneRoot_eq_iff d u v t z).mpr ⟨hz, rfl⟩, fun w hw => ?_⟩
  exact Subtype.ext ((diagonalRankOneRoot_eq_iff d u v w z).mp hw).2

/-- Increasing positive rank-one coupling strictly increases the top level,
including when the initial coupling is zero. -/
theorem strictMonoOn_diagonalRankOneRoot (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) :
    StrictMonoOn (diagonalRankOneRoot d u v) (Ici 0) := by
  intro s hs t _ hst
  have hs0 : 0 ≤ s := hs
  have ht : 0 < t := hs0.trans_lt hst
  rcases eq_or_lt_of_le hs0 with hzero | hsp
  · rw [← hzero, diagonalRankOneRoot, dif_neg (lt_irrefl 0)]
    exact (diagonalRankOneRoot_secular d u v ht).1
  · let A := diagonalRankOneKernel d u v ⟨s, hsp⟩
    let B := diagonalRankOneKernel d u v ⟨t, ht⟩
    have hentry (i j : ι) : A.val i j < B.val i j := by
      change (if i = j then (d i : ℝ) else 0) + s * (u i : ℝ) * (v j : ℝ) <
        (if i = j then (d i : ℝ) else 0) + t * (u i : ℝ) * (v j : ℝ)
      exact add_lt_add_of_le_of_lt le_rfl
        (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hst (u i).2) (v j).2)
    let i := Classical.choice (inferInstance : Nonempty ι)
    rw [diagonalRankOneRoot, dif_pos hsp, diagonalRankOneRoot, dif_pos ht]
    refine perronRoot_lt_of_weighted_le A B (fun _ => 1) (fun _ => zero_lt_one) ?_ ?_
    · simpa only [one_mul, mul_one] using fun i j => (hentry i j).le
    · simpa only [one_mul, mul_one] using (show ∃ i j, A.val i j < B.val i j from ⟨i, i, hentry i i⟩)

/-- Separating the highest-level residue gives the exact scaled response. -/
theorem diagonalRankOneRoot_sub_div_eq (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t : ℝ} (ht : 0 < t) :
    (diagonalRankOneRoot d u v t - diagonalCeiling d) / t = diagonalTopWeight d u v +
      (diagonalRankOneRoot d u v t - diagonalCeiling d) *
        diagonalLowerResolvent d u v (diagonalRankOneRoot d u v t) := by
  let z := diagonalRankOneRoot d u v t
  let b := diagonalCeiling d
  let f (i : ι) := ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))
  obtain ⟨hz, hsec⟩ := diagonalRankOneRoot_secular d u v ht
  change b < z at hz
  change t * (∑ i, f i) = 1 at hsec
  have he : (z - b) / t = (z - b) * ∑ i, f i := by
    apply (div_eq_iff ht.ne').mpr
    calc
      z - b = (z - b) * (t * ∑ i, f i) := by rw [hsec, mul_one]
      _ = _ := by ring
  rw [he, ← sum_filter_add_sum_filter_not univ (fun i => (d i : ℝ) = b) f, mul_add]
  change (z - b) * (∑ i ∈ univ.filter (fun i => (d i : ℝ) = b), f i) +
    (z - b) * diagonalLowerResolvent d u v z =
    diagonalTopWeight d u v + (z - b) * diagonalLowerResolvent d u v z
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hb := (mem_filter.mp hi).2
  dsimp only [f]
  rw [hb, mul_comm (z - b), div_mul_cancel₀ _ (sub_pos.mpr hz).ne']

/-- The shift of the top level is bounded by coupling strength times the
total rank-one weight. -/
theorem diagonalRankOneRoot_shift_le (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t : ℝ} (ht : 0 < t) :
    diagonalRankOneRoot d u v t - diagonalCeiling d ≤ t * ∑ i, (u i : ℝ) * (v i : ℝ) := by
  let z := diagonalRankOneRoot d u v t
  let b := diagonalCeiling d
  let f (i : ι) := ((u i : ℝ) * (v i : ℝ)) / (z - (d i : ℝ))
  obtain ⟨hz, hsec⟩ := diagonalRankOneRoot_secular d u v ht
  change b < z at hz
  change t * (∑ i, f i) = 1 at hsec
  have hsum : (∑ i, ((u i : ℝ) * (v i : ℝ)) * ((z - b) / (z - (d i : ℝ)))) = (z - b) * ∑ i, f i := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by dsimp only [f]; ring
  calc
    z - b = (z - b) * (t * ∑ i, f i) := by rw [hsec, mul_one]
    _ = t * ∑ i, ((u i : ℝ) * (v i : ℝ)) * ((z - b) / (z - (d i : ℝ))) := by
      rw [hsum, mul_left_comm]
    _ ≤ t * ∑ i, (u i : ℝ) * (v i : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ ht.le
      apply sum_le_sum
      intro i _
      have hi : (d i : ℝ) ≤ b := le_diagonalCeiling d i
      have hd : 0 < z - (d i : ℝ) := sub_pos.mpr (hi.trans_lt hz)
      have he : (z - b) / (z - (d i : ℝ)) ≤ 1 := (div_le_one hd).mpr (sub_le_sub_left hi z)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (mul_nonneg (u i).2.le (v i).2.le)

/-- Removing the positive coupling recovers the top diagonal level. -/
theorem tendsto_diagonalRankOneRoot (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) :
    Tendsto (diagonalRankOneRoot d u v) (𝓝[>] (0 : ℝ)) (𝓝 (diagonalCeiling d)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hU : Tendsto (fun t : ℝ => diagonalCeiling d + t * ∑ i, (u i : ℝ) * (v i : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (diagonalCeiling d)) := by
    simpa only [zero_mul, add_zero] using
      (hid.mul_const (∑ i, (u i : ℝ) * (v i : ℝ))).const_add
        (diagonalCeiling d)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (diagonalRankOneRoot_secular d u v ht).1.le
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h := diagonalRankOneRoot_shift_le d u v ht
    linarith only [h]

private theorem diagonalRankOneRoot_remainder_eq (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t : ℝ}
    (ht : 0 < t) :
    diagonalRankOneRoot d u v t - diagonalCeiling d - t * diagonalTopWeight d u v =
      t * (diagonalRankOneRoot d u v t - diagonalCeiling d) *
        diagonalLowerResolvent d u v (diagonalRankOneRoot d u v t) := by
  have hn := (div_eq_iff ht.ne').mp (diagonalRankOneRoot_sub_div_eq d u v ht)
  linear_combination hn

/-- The first-order spectral-edge approximation has a nonnegative
quadratic error, controlled by the regular part of the resolvent. -/
theorem diagonalRankOneRoot_remainder_bounds (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) {t : ℝ}
    (ht : 0 < t) :
    let e := diagonalRankOneRoot d u v t - diagonalCeiling d - t * diagonalTopWeight d u v
    0 ≤ e ∧ e ≤ t ^ 2 * (∑ i, (u i : ℝ) * (v i : ℝ)) * diagonalLowerResolvent d u v (diagonalCeiling d) := by
  let z := diagonalRankOneRoot d u v t
  let b := diagonalCeiling d
  let U := ∑ i, (u i : ℝ) * (v i : ℝ)
  have hz : b < z := (diagonalRankOneRoot_secular d u v ht).1
  have hU : 0 ≤ U := sum_nonneg fun i _ => mul_nonneg (u i).2.le (v i).2.le
  have hR0 : 0 ≤ diagonalLowerResolvent d u v z := by
    apply sum_nonneg
    intro i _
    exact div_nonneg (mul_nonneg (u i).2.le (v i).2.le) (sub_nonneg.mpr ((le_diagonalCeiling d i).trans hz.le))
  have hR : diagonalLowerResolvent d u v z ≤ diagonalLowerResolvent d u v b := by
    apply sum_le_sum
    intro i hi
    have hd : (d i : ℝ) < b := lt_of_le_of_ne (le_diagonalCeiling d i) (mem_filter.mp hi).2
    exact div_le_div_of_nonneg_left (mul_nonneg (u i).2.le (v i).2.le) (sub_pos.mpr hd)
      (sub_le_sub_right hz.le _)
  dsimp only
  rw [diagonalRankOneRoot_remainder_eq d u v ht]
  refine ⟨mul_nonneg (mul_nonneg ht.le (sub_nonneg.mpr hz.le)) hR0, ?_⟩
  change t * (z - b) * diagonalLowerResolvent d u v z ≤ t ^ 2 * U * diagonalLowerResolvent d u v b
  calc
    _ ≤ t * (t * U) * diagonalLowerResolvent d u v z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (diagonalRankOneRoot_shift_le d u v ht) ht.le) hR0
    _ ≤ t * (t * U) * diagonalLowerResolvent d u v b :=
      mul_le_mul_of_nonneg_left hR (mul_nonneg ht.le (mul_nonneg ht.le hU))
    _ = _ := by ring

private theorem tendsto_diagonalLowerResolvent_root (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) :
    Tendsto (fun t => diagonalLowerResolvent d u v (diagonalRankOneRoot d u v t))
      (𝓝[>] (0 : ℝ)) (𝓝 (diagonalLowerResolvent d u v (diagonalCeiling d))) := by
  unfold diagonalLowerResolvent
  refine tendsto_finsetSum _ fun i hi => ?_
  have hd : diagonalCeiling d - (d i : ℝ) ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (mem_filter.mp hi).2)
  exact tendsto_const_nhds.div ((tendsto_diagonalRankOneRoot d u v).sub tendsto_const_nhds) hd

/-- The first response coefficient is the total rank-one weight on the
maximal diagonal eigenspace. -/
theorem tendsto_diagonalRankOneRoot_first (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) :
    Tendsto (fun t => (diagonalRankOneRoot d u v t - diagonalCeiling d) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (diagonalTopWeight d u v)) := by
  have h := ((tendsto_diagonalRankOneRoot d u v).sub
    (tendsto_const_nhds (x := diagonalCeiling d))).mul (tendsto_diagonalLowerResolvent_root d u v)
  have h' := h.const_add (diagonalTopWeight d u v)
  rw [sub_self, zero_mul, add_zero] at h'
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact (diagonalRankOneRoot_sub_div_eq d u v ht).symm

/-- The second response coefficient is the top weight times the resolvent
of the lower levels at the uncoupled edge. -/
theorem tendsto_diagonalRankOneRoot_second (d : ι → ℝ≥0) (u v : ι → Ioi (0 : ℝ)) :
    Tendsto (fun t => (diagonalRankOneRoot d u v t - diagonalCeiling d - t * diagonalTopWeight d u v) / t ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (diagonalTopWeight d u v * diagonalLowerResolvent d u v (diagonalCeiling d))) := by
  refine ((tendsto_diagonalRankOneRoot_first d u v).mul (tendsto_diagonalLowerResolvent_root d u v)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  let y := diagonalRankOneRoot d u v t - diagonalCeiling d
  let R := diagonalLowerResolvent d u v (diagonalRankOneRoot d u v t)
  have hnum : y - t * diagonalTopWeight d u v = t * y * R := diagonalRankOneRoot_remainder_eq d u v ht
  change y / t * R = (y - t * diagonalTopWeight d u v) / t ^ 2
  rw [hnum]
  field_simp [ht.ne']

#print axioms diagonalRankOneRoot_secular
#print axioms diagonalRankOneRoot_eq_of_secular
#print axioms diagonalRankOneRoot_eq_iff
#print axioms existsUnique_diagonalRankOneRoot_eq
#print axioms strictMonoOn_diagonalRankOneRoot
#print axioms diagonalRankOneRoot_sub_div_eq
#print axioms diagonalRankOneRoot_shift_le
#print axioms diagonalRankOneRoot_remainder_bounds
#print axioms tendsto_diagonalRankOneRoot_first
#print axioms tendsto_diagonalRankOneRoot_second

end

end GaloisForLFunctions.HTGeometry.EntrywisePositiveKernel
