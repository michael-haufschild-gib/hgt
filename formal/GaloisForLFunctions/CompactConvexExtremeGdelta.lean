import Mathlib

/-!
# Extreme points of a compact convex set are a Gδ

In a real normed space, the extreme points of a compact convex set `K` form a `Gδ` set.  A point of
`K` fails to be extreme exactly when it is the midpoint of two points of `K` at positive distance,
and the midpoints of pairs at distance `≥ 1/(n+1)` form a closed set (continuous image of a compact
set).  Hence the non-extreme points are an `Fσ` inside `K`, so the extreme points are `Gδ`.

This is the elementary topological half of Choquet theory used by the moment-fiber cards
(`indeterminate-moment-fiber-maximal-translation-ht`, eq. (29)–(30)).
-/

open Set

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Midpoints of pairs of points of `K` at distance at least `1/(n+1)`. -/
def nonExtremeWitness (K : Set E) (n : ℕ) : Set E :=
  (fun p : E × E => midpoint ℝ p.1 p.2) ''
    {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ dist p.1 p.2}

theorem nonExtremeWitness_subset {K : Set E} (hK : Convex ℝ K) (n : ℕ) :
    nonExtremeWitness K n ⊆ K := by
  rintro x ⟨⟨y, z⟩, ⟨hy, hz, _⟩, rfl⟩
  exact hK.midpoint_mem hy hz

/-- Each witness set is closed: it is the continuous image of a compact set of pairs. -/
theorem isClosed_nonExtremeWitness {K : Set E} (hK : IsCompact K) (n : ℕ) :
    IsClosed (nonExtremeWitness K n) := by
  have h1 : IsClosed {p : E × E | p.1 ∈ K} := hK.isClosed.preimage continuous_fst
  have h2 : IsClosed {p : E × E | p.2 ∈ K} := hK.isClosed.preimage continuous_snd
  have h3 : IsClosed {p : E × E | (1 : ℝ) / (n + 1) ≤ dist p.1 p.2} :=
    isClosed_le continuous_const (continuous_fst.dist continuous_snd)
  have hcl : IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ dist p.1 p.2} := by
    simp only [Set.setOf_and]; exact h1.inter (h2.inter h3)
  have hcpt : IsCompact {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ dist p.1 p.2} :=
    (hK.prod hK).of_isClosed_subset hcl (fun p ⟨hp1, hp2, _⟩ => ⟨hp1, hp2⟩)
  have hcont : Continuous (fun p : E × E => midpoint ℝ p.1 p.2) := by
    simp only [midpoint_eq_smul_add]
    exact (continuous_fst.add continuous_snd).const_smul _
  exact (hcpt.image hcont).isClosed

private theorem midpoint_right_eq {x z : E} (h : midpoint ℝ x z = x) : z = x := by
  rw [midpoint_eq_smul_add, invOf_eq_inv] at h
  have h2 : x + z = (2 : ℝ) • x := by
    have := congrArg (fun w => (2 : ℝ) • w) h
    simp only [smul_smul] at this
    rwa [show (2 : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num, one_smul] at this
  have : x + z = x + x := by rw [h2, two_smul]
  exact add_left_cancel this

/-- The extreme points of `K` are exactly `K` minus the countable union of witness sets. -/
theorem extremePoints_eq_diff_iUnion {K : Set E} (hK : Convex ℝ K) :
    K.extremePoints ℝ = K \ ⋃ n, nonExtremeWitness K n := by
  ext x
  rw [mem_extremePoints_iff_forall_segment, Set.mem_diff, Set.mem_iUnion, not_exists]
  constructor
  · rintro ⟨hxK, hx⟩
    refine ⟨hxK, fun n hxn => ?_⟩
    obtain ⟨⟨y, z⟩, ⟨hy, hz, hd⟩, hmid⟩ := hxn
    simp only at hmid
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hyz : y ≠ z := by
      intro h; subst h; simp only [dist_self] at hd; linarith
    have hxseg : x ∈ segment ℝ y z := hmid ▸ midpoint_mem_segment y z
    rcases hx y hy z hz hxseg with h | h
    · subst h; exact hyz (midpoint_right_eq hmid).symm
    · subst h; rw [midpoint_comm] at hmid; exact hyz (midpoint_right_eq hmid)
  · rintro ⟨hxK, hx⟩
    refine ⟨hxK, fun y hy z hz hxseg => ?_⟩
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hyx, hzx⟩ := hcon
    obtain ⟨a, b, ha, hb, hab, hxeq⟩ := hxseg
    have hapos : 0 < a := by
      rcases ha.lt_or_eq with h | h
      · exact h
      · exfalso; apply hzx; rw [← hxeq, ← h, show b = 1 by linarith]; simp
    have hbpos : 0 < b := by
      rcases hb.lt_or_eq with h | h
      · exact h
      · exfalso; apply hyx; rw [← hxeq, ← h, show a = 1 by linarith]; simp
    have hyz : y ≠ z := by
      intro h; subst h; apply hyx
      rw [← hxeq, show a • y + b • y = (a + b) • y by module, hab, one_smul]
    set s := min a b with hs
    have hspos : 0 < s := lt_min hapos hbpos
    have hsa : s ≤ a := min_le_left _ _
    have hsb : s ≤ b := min_le_right _ _
    set y' := (a + s) • y + (b - s) • z with hy'
    set z' := (a - s) • y + (b + s) • z with hz'
    have hy'K : y' ∈ K := hK.segment_subset hy hz
      ⟨a + s, b - s, by linarith, by linarith, by linarith, rfl⟩
    have hz'K : z' ∈ K := hK.segment_subset hy hz
      ⟨a - s, b + s, by linarith, by linarith, by linarith, rfl⟩
    have hmidx : midpoint ℝ y' z' = x := by
      rw [hy', hz', midpoint_eq_smul_add, invOf_eq_inv, ← hxeq]; module
    have hdist : dist y' z' = 2 * s * dist y z := by
      rw [dist_eq_norm, dist_eq_norm, hy', hz',
        show (a + s) • y + (b - s) • z - ((a - s) • y + (b + s) • z)
            = (2 * s) • (y - z) by module, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hdpos : 0 < 2 * s * dist y z := by
      have : 0 < dist y z := dist_pos.mpr hyz
      positivity
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdpos
    exact hx n ⟨(y', z'), ⟨hy'K, hz'K, by rw [hdist]; linarith⟩, hmidx⟩

/-- **Extreme points of a compact convex set are `Gδ`.** -/
theorem isGδ_extremePoints {K : Set E} (hK : IsCompact K) (hKconv : Convex ℝ K) :
    IsGδ (K.extremePoints ℝ) := by
  rw [extremePoints_eq_diff_iUnion hKconv, Set.diff_eq, Set.compl_iUnion]
  exact hK.isClosed.isGδ.inter
    (IsGδ.iInter_of_isOpen (fun n => (isClosed_nonExtremeWitness hK n).isOpen_compl))

end HTGeometry
