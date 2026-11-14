import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
# Compactness of nonoverlapping closed-ball coverings

Choose one covering centre for each point. Two chosen centres may coincide;
otherwise their distance is at least twice the radius. This disjunctive
constraint is closed, so compact products turn finite coverability into
global coverability without a countability restriction. In a proper normed
group the coverable configurations also form a closed set in the product
topology: the centre offsets lie in a fixed compact product.

This is the compactness mechanism of Kittipassorn--Phetmak--Sriamorn,
*Covering the Triangular Lattice with Non-Overlapping Unit Disks*,
Proposition 3.1, Remark 3.2, and Proposition 9.3.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

open Set Metric

variable {ι κ X : Type*} [MetricSpace X]

/-- A configuration covered by radius-`r` balls with separated distinct centres. -/
def BallCoverable (r : NNReal) (p : ι → X) : Prop :=
  ∃ c : ι → X, (∀ i, dist (p i) (c i) ≤ r) ∧
    ∀ i j, c i = c j ∨ 2 * (r : ℝ) ≤ dist (c i) (c j)

/-- Restricting or repeating points preserves a covering. -/
theorem BallCoverable.comp {r : NNReal} {p : ι → X}
    (h : BallCoverable r p) (f : κ → ι) : BallCoverable r (p ∘ f) := by
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c ∘ f, fun i => hc (f i), fun i j => hs (f i) (f j)⟩

/-- The chosen-centre description agrees with an actual set of centres. -/
theorem ballCoverable_iff_centres (r : NNReal) (p : ι → X) :
    BallCoverable r p ↔ ∃ C : Set X,
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * (r : ℝ) ≤ dist x y) ∧
      ∀ i, ∃ c ∈ C, dist (p i) c ≤ r := by
  constructor
  · rintro ⟨c, hc, hs⟩
    refine ⟨range c, ?_, fun i => ⟨c i, mem_range_self i, hc i⟩⟩
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hne
    exact (hs i j).resolve_left hne
  · rintro ⟨C, hs, hc⟩
    choose c hmem hc using hc
    refine ⟨c, hc, fun i j => ?_⟩
    by_cases h : c i = c j
    · exact Or.inl h
    · exact Or.inr (hs _ (hmem i) _ (hmem j) h)

/-- Finite satisfiability of the closed separation constraints is sufficient. -/
theorem ballCoverable_iff_finset [ProperSpace X] (r : NNReal) (p : ι → X) :
    BallCoverable r p ↔
      ∀ s : Finset ι, BallCoverable r (fun i : s => p i) := by
  classical
  constructor
  · intro h s
    exact h.comp Subtype.val
  · intro h
    let K : Set (ι → X) := pi univ (fun i => closedBall (p i) r)
    let A : ι × ι → Set (ι → X) := fun ij =>
      {c | c ij.1 = c ij.2 ∨ 2 * (r : ℝ) ≤ dist (c ij.1) (c ij.2)}
    have hK : IsCompact K := isCompact_univ_pi (fun i => isCompact_closedBall (p i) r)
    have hA (ij : ι × ι) : IsClosed (A ij) :=
      (isClosed_eq (continuous_apply ij.1) (continuous_apply ij.2)).union
        (isClosed_le continuous_const
          ((continuous_apply ij.1).dist (continuous_apply ij.2)))
    have hfin (t : Finset (ι × ι)) : (K ∩ ⋂ ij ∈ t, A ij).Nonempty := by
      let s : Finset ι := t.image Prod.fst ∪ t.image Prod.snd
      obtain ⟨c, hc, hs⟩ := h s
      let f : ι → X := fun i => if hi : i ∈ s then c ⟨i, hi⟩ else p i
      have hf (i : ι) (hi : i ∈ s) : f i = c ⟨i, hi⟩ := dif_pos hi
      refine ⟨f, ?_, ?_⟩
      · intro i _
        change dist (f i) (p i) ≤ (r : ℝ)
        by_cases hi : i ∈ s
        · rw [hf i hi, dist_comm]
          exact hc ⟨i, hi⟩
        · simp only [f, dif_neg hi, dist_self]
          exact r.coe_nonneg
      · refine mem_iInter.mpr fun ij => mem_iInter.mpr fun hij => ?_
        have hi : ij.1 ∈ s := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hij)
        have hj : ij.2 ∈ s := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hij)
        change f ij.1 = f ij.2 ∨ 2 * (r : ℝ) ≤ dist (f ij.1) (f ij.2)
        rw [hf _ hi, hf _ hj]
        exact hs ⟨ij.1, hi⟩ ⟨ij.2, hj⟩
    obtain ⟨c, hc, hs⟩ := hK.inter_iInter_nonempty A hA hfin
    refine ⟨c, fun i => ?_, fun i j => mem_iInter.mp hs (i, j)⟩
    exact (dist_comm (p i) (c i)).le.trans (hc i (mem_univ i))

/-- Failure of a covering always has a finite witness. -/
theorem not_ballCoverable_iff_finset [ProperSpace X] (r : NNReal) (p : ι → X) :
    ¬ BallCoverable r p ↔
      ∃ s : Finset ι, ¬ BallCoverable r (fun i : s => p i) := by
  rw [ballCoverable_iff_finset]
  exact not_forall

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- Coverability is closed even for arbitrarily indexed configurations. -/
theorem isClosed_ballCoverable (r : NNReal) :
    IsClosed {p : ι → E | BallCoverable r p} := by
  let K : Set (ι → E) := pi univ (fun _ => closedBall (0 : E) r)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_closedBall (0 : E) r)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K × (ι → E)) := {q | ∀ i j,
    q.2 i + q.1.val i = q.2 j + q.1.val j ∨
      2 * (r : ℝ) ≤ dist (q.2 i + q.1.val i) (q.2 j + q.1.val j)}
  have hc (i : ι) : Continuous (fun q : K × (ι → E) => q.2 i + q.1.val i) :=
    ((continuous_apply i).comp continuous_snd).add
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
  have hA : IsClosed A := by
    change IsClosed {q : K × (ι → E) | ∀ i j, _}
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      (isClosed_eq (hc i) (hc j)).union
        (isClosed_le continuous_const ((hc i).dist (hc j)))
  have heq : Prod.snd '' A = {p : ι → E | BallCoverable r p} := by
    ext p
    constructor
    · rintro ⟨⟨v, q⟩, hv, rfl⟩
      refine ⟨fun i => q i + v.val i, fun i => ?_, hv⟩
      have hi := v.property i (mem_univ i)
      change dist (v.val i) 0 ≤ (r : ℝ) at hi
      simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg, sub_zero] using hi
    · rintro ⟨c, hc, hs⟩
      have hv : (fun i => c i - p i) ∈ K := by
        intro i _
        change dist (c i - p i) 0 ≤ (r : ℝ)
        simpa only [dist_eq_norm, sub_zero, norm_sub_rev] using hc i
      refine ⟨(⟨fun i => c i - p i, hv⟩, p), ?_, rfl⟩
      change ∀ i j, p i + (c i - p i) = p j + (c j - p j) ∨ _
      have hcancel (i : ι) : p i + (c i - p i) = c i := by
        rw [add_comm, sub_add_cancel]
      simpa only [hcancel] using hs
  rw [← heq]
  exact isClosedMap_snd_of_compactSpace A hA

/-- Every continuous deformation has a closed set of coverable parameters. -/
theorem isClosed_coverable_parameters {T : Type*} [TopologicalSpace T]
    (r : NNReal) (p : T → ι → E) (hp : Continuous p) :
    IsClosed {t | BallCoverable r (p t)} :=
  (isClosed_ballCoverable r).preimage hp

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.ballCoverable_iff_finset
#print axioms GaloisForLFunctions.HilbertMetric.not_ballCoverable_iff_finset
#print axioms GaloisForLFunctions.HilbertMetric.isClosed_ballCoverable
