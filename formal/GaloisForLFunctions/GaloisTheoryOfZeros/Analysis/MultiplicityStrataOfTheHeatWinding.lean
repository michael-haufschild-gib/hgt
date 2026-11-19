import GaloisForLFunctions.GaloisTheoryOfZeros.TheLocalDiscriminantOfAHeatCollision
import GaloisForLFunctions.GaloisTheoryOfZeros.AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.StaircasePacking

/-!
# Multiplicity strata of the heat winding

In a symmetric box at real times, a real collision has a reflected partner
and a nonreal collision has three partners. Count one representative per
orbit. Each site of order m contributes m.choose 2, so the staircase bound
for distinct orders gives a cubic lower bound for the integer winding.
-/

open Complex Set Finset
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
open RHTower GaloisForLFunctions.HTGeometry
open scoped ENNReal

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
open scoped Classical

private theorem compact_real_box (r : ℝ) : IsCompact (realTimeHeatBox r) :=
  (isCompact_Icc.image Complex.continuous_ofReal).prod (isCompact_Icc.reProdIm isCompact_Icc)

/-- Actual time-place collisions inside a closed real-time box. -/
def heatBoxSites (r : ℝ) : Finset (ℂ × ℂ) :=
  (compact_heatIntersectionMass _ (compact_real_box r)).choose

theorem mem_heatBoxSites {r : ℝ} {p : ℂ × ℂ} :
    p ∈ heatBoxSites r ↔ p ∈ realTimeHeatBox r ∧ p ∈ multipleZeros :=
  (compact_heatIntersectionMass _ (compact_real_box r)).choose_spec.1 p

/-- Integer mass whose multiple by 2πi is the winding integral on a regular box. -/
def heatBoxWinding (r : ℝ) : ℕ := ∑ p ∈ heatBoxSites r, heatIntersectionMultiplicity p

theorem heatIntersectionMass_realBox (r : ℝ) :
    heatIntersectionMass (realTimeHeatBox r) = (heatBoxWinding r : ℝ≥0∞) := by
  simpa only [heatBoxWinding, Nat.cast_sum, heatBoxSites] using
    (compact_heatIntersectionMass _ (compact_real_box r)).choose_spec.2

/-- Spatial vanishing order of the heat transform at the marked site. -/
def heatSpatialOrder (p : ℂ × ℂ) : ℕ := analyticOrderNatAt (complexHeat p.1) p.2

private theorem place_collision (p : ℂ × ℂ) : IsCollision p.1 p.2 (heatSpatialOrder p) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_complexHeat_ne_top p.1 p.2)
  simpa [heatSpatialOrder, analyticOrderNatAt, ← hm] using isCollision_iff_analyticOrderAt.mpr hm.symm

private def reflectSite (p : ℂ × ℂ) : ℂ × ℂ := (p.1, -p.2)
private def conjugateSite (p : ℂ × ℂ) : ℂ × ℂ := (starRingEnd ℂ p.1, starRingEnd ℂ p.2)

private theorem weight_reflect (p : ℂ × ℂ) :
    heatIntersectionMultiplicity (reflectSite p) = heatIntersectionMultiplicity p :=
  (place_collision p).neg.heatIntersectionMultiplicity_eq

private theorem weight_conjugate (p : ℂ × ℂ) :
    heatIntersectionMultiplicity (conjugateSite p) = heatIntersectionMultiplicity p :=
  (place_collision p).conj.heatIntersectionMultiplicity_eq

private theorem reflect_mem {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ heatBoxSites r) :
    reflectSite p ∈ heatBoxSites r := by
  obtain ⟨⟨ht, hw⟩, hm⟩ := mem_heatBoxSites.mp hp
  obtain ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ := Complex.mem_reProdIm.mp hw
  exact mem_heatBoxSites.mpr ⟨⟨ht,Complex.mem_reProdIm.mpr
    ⟨⟨by change -r ≤ -p.2.re; linarith, by change -p.2.re ≤ r; linarith⟩,
     ⟨by change -r ≤ -p.2.im; linarith, by change -p.2.im ≤ r; linarith⟩⟩⟩,
    (heatIntersectionMultiplicity_ne_zero_iff _).mp (weight_reflect p ▸
      (heatIntersectionMultiplicity_ne_zero_iff _).mpr hm)⟩

private theorem conjugate_mem {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ heatBoxSites r) :
    conjugateSite p ∈ heatBoxSites r := by
  obtain ⟨⟨⟨t,ht,he⟩, hw⟩, hm⟩ := mem_heatBoxSites.mp hp
  obtain ⟨ha,⟨hc,hd⟩⟩ := Complex.mem_reProdIm.mp hw
  exact mem_heatBoxSites.mpr ⟨⟨⟨t,ht,by simpa only [conjugateSite, ← he, Complex.conj_ofReal]⟩,
    Complex.mem_reProdIm.mpr ⟨ha,⟨by change -r ≤ -p.2.im; linarith,
      by change -p.2.im ≤ r; linarith⟩⟩⟩,
    (heatIntersectionMultiplicity_ne_zero_iff _).mp (weight_conjugate p ▸
      (heatIntersectionMultiplicity_ne_zero_iff _).mpr hm)⟩

private theorem site_re_ne_zero {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ heatBoxSites r) :
    p.2.re ≠ 0 := by
  obtain ⟨⟨⟨t,_,he⟩,_⟩,hm⟩ := mem_heatBoxSites.mp hp
  exact re_ne_zero_of_complexHeat_ofReal_eq_zero (he.symm ▸ hm.1 : complexHeat (t : ℂ) p.2 = 0)

/-- Sum over an involution: fixed-coordinate contributions occur once and
the strictly positive-coordinate half occurs twice. -/
private theorem sum_oriented {α : Type*} (S : Finset α) (v : α → ℝ) (w : α → ℕ)
    (ι : α → α) (inv : Function.Involutive ι) (hs : ∀ x ∈ S, ι x ∈ S)
    (hv : ∀ x, v (ι x) = -v x) (hw : ∀ x, w (ι x) = w x) :
    ∑ x ∈ S, w x = (∑ x ∈ S with v x = 0, w x) + 2 * ∑ x ∈ S with 0 < v x, w x := by
  let f (x : α) := if 0 < v x then w x else 0
  have hsum : ∑ x ∈ S, f (ι x) = ∑ x ∈ S, f x :=
    sum_bij' (fun x _ => ι x) (fun x _ => ι x) hs hs (fun x _ => inv x)
      (fun x _ => inv x) (fun _ _ => rfl)
  have hx (x : α) : w x = (if v x = 0 then w x else 0) + (f x + f (ι x)) := by
    rcases lt_trichotomy (v x) 0 with h|h|h
    · simp only [f, hv, hw, h.ne, h.not_gt, neg_pos, h, if_false, if_true, zero_add]
    · simp [f, hv, h]
    · simp only [f, hv, h.ne', h, neg_pos, h.not_gt, if_false, if_true, add_zero, zero_add]
  simp_rw [sum_filter]
  change _ = _ + 2 * ∑ x ∈ S, f x
  calc
    _ = ∑ x ∈ S, ((if v x = 0 then w x else 0) + (f x + f (ι x))) :=
      sum_congr rfl fun x _ => hx x
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, hsum, two_mul]

/-- Representatives of the reflected real pairs. -/
def heatRealPairs (r : ℝ) : Finset (ℂ × ℂ) :=
  ((heatBoxSites r).filter fun p => 0 < p.2.re).filter fun p => p.2.im = 0

/-- Representatives of the nonreal quartets. -/
def heatNonrealQuartets (r : ℝ) : Finset (ℂ × ℂ) :=
  ((heatBoxSites r).filter fun p => 0 < p.2.re).filter fun p => 0 < p.2.im

/-- Exact decomposition of the discriminant winding into real pairs and nonreal quartets. -/
theorem heatBoxWinding_orbits (r : ℝ) :
    heatBoxWinding r = 2 * (∑ p ∈ heatRealPairs r, heatIntersectionMultiplicity p) +
      4 * ∑ p ∈ heatNonrealQuartets r, heatIntersectionMultiplicity p := by
  let S := (heatBoxSites r).filter fun p => 0 < p.2.re
  have h := sum_oriented (heatBoxSites r) (fun p => p.2.re) heatIntersectionMultiplicity
    reflectSite (fun p => by simp [reflectSite]) (fun _ hp => reflect_mem hp)
    (fun _ => rfl) weight_reflect
  have hempty : ((heatBoxSites r).filter fun p => p.2.re = 0) = ∅ :=
    filter_eq_empty_iff.mpr fun p hp => site_re_ne_zero hp
  rw [hempty, sum_empty, zero_add] at h
  have h' := sum_oriented S (fun p => p.2.im) heatIntersectionMultiplicity conjugateSite
    (fun p => by simp [conjugateSite]) (fun p hp => mem_filter.mpr
      ⟨conjugate_mem (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩)
    (fun _ => rfl) weight_conjugate
  change heatBoxWinding r = 2 * ∑ p ∈ S, heatIntersectionMultiplicity p at h
  rw [h, h']
  dsimp only [S, heatRealPairs, heatNonrealQuartets]
  ring

/-- Distinct orders at the selected sites. Sites of order below b are omitted. -/
def heatOrderLevels (S : Finset (ℂ × ℂ)) (b : ℕ) : Finset ℕ :=
  (S.filter fun p => b ≤ heatSpatialOrder p).image heatSpatialOrder

/-- Every collision stratum pays its own triangular weight. Repeated
orders still cost at least the bottom triangular weight at every site. -/
theorem heatOrderLevels_cost (S : Finset (ℂ × ℂ)) (b : ℕ) :
    (b + (heatOrderLevels S b).card).choose 3 +
        ((S.filter fun p => b ≤ heatSpatialOrder p).card - (heatOrderLevels S b).card) * b.choose 2 ≤
      b.choose 3 + ∑ p ∈ S, heatIntersectionMultiplicity p := by
  let A := S.filter fun p => b ≤ heatSpatialOrder p
  have h := StaircasePacking.multiplicity_binomial_bound A heatSpatialOrder b 2
    (fun p hp => (mem_filter.mp hp).2)
  exact h.trans (Nat.add_le_add_left (sum_le_sum_of_subset (f := heatIntersectionMultiplicity)
    (filter_subset _ _)) _)

/-- Distinct multiplicities of real pairs and nonreal quartets have separate
cubic costs. An extra pair costs at least two units; an extra quartet costs four. -/
theorem heatBoxWinding_strata (r : ℝ) :
    let cost (S : Finset (ℂ × ℂ)) :=
      (2 + (heatOrderLevels S 2).card).choose 3 + (S.card - (heatOrderLevels S 2).card)
    2 * cost (heatRealPairs r) + 4 * cost (heatNonrealQuartets r) ≤ heatBoxWinding r := by
  let cost (S : Finset (ℂ × ℂ)) :=
    (2 + (heatOrderLevels S 2).card).choose 3 + (S.card - (heatOrderLevels S 2).card)
  have bound (S : Finset (ℂ × ℂ)) (hs : S ⊆ heatBoxSites r) :
      cost S ≤ ∑ p ∈ S, heatIntersectionMultiplicity p := by
    have ha : (S.filter fun p => 2 ≤ heatSpatialOrder p) = S := filter_eq_self.mpr fun p hp =>
      Nat.choose_ne_zero_iff.mp ((heatIntersectionMultiplicity_ne_zero_iff p).mpr
        (mem_heatBoxSites.mp (hs hp)).2)
    simpa only [cost, ha, Nat.choose_succ_self, Nat.choose_self, mul_one, zero_add] using
      heatOrderLevels_cost S 2
  rw [heatBoxWinding_orbits]
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 (bound _ ((filter_subset _ _).trans (filter_subset _ _))))
    (Nat.mul_le_mul_left 4 (bound _ ((filter_subset _ _).trans (filter_subset _ _))))

/-- Allowing winding one on an exhaustion of real-time boxes gives the same RH criterion. -/
theorem heatBoxWinding_le_one_iff_rh :
    (∀ r : ℝ, 0 < r → heatBoxWinding r ≤ 1) ↔ RiemannHypothesis := by
  obtain ⟨R,_,hb,_,_,_,_,hRH⟩ := exists_regular_heatBox_exhaustion
  constructor
  · intro h
    apply hRH.mp
    intro n
    rw [heatIntersectionMass_realBox, Nat.cast_eq_zero]
    have hsmall := h (R n) ((by positivity : (0 : ℝ) < (n : ℝ) + 1).trans (hb n).1)
    have horb := heatBoxWinding_orbits (R n)
    omega
  · intro h r hr
    have he : heatBoxSites r = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp => by
      obtain ⟨⟨⟨t, ht, he⟩, _⟩, hcol⟩ := mem_heatBoxSites.mp hp
      exact riemannHypothesis_iff_forall_pos_not_mem_branchTimes.mp h t
        ((one_div_pos.mpr hr).trans_le ht.1) ⟨p, hcol, he.symm⟩
    simp [heatBoxWinding, he]

#print axioms heatBoxWinding_orbits
#print axioms heatOrderLevels_cost
#print axioms heatBoxWinding_strata
#print axioms heatBoxWinding_le_one_iff_rh

end
end GaloisForLFunctions.GaloisTheoryOfZeros
