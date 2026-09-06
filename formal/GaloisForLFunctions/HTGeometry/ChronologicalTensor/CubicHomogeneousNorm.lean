import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHomogeneousBoundary

/-!
# The physical norm on every homogeneous observation space

The actual supremum over sparse physical probes equals the supremum of the
one-variable edge profile on [0,1] and is attained there. These capacities
define a seminorm on each homogeneous space; faithfulness of polynomial
observation proves its kernel is zero. No norm on the full algebraic
normalization quotient is asserted.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicHomogeneousValues (k : ℕ) (P : cubicHomogeneousSpace k) : Set ℝ :=
  Set.range (fun g : cubicProbeSection => |cubicPolynomialObservation P.val g|)

def cubicHomogeneousCapacity (k : ℕ) (P : cubicHomogeneousSpace k) : ℝ :=
  sSup (cubicHomogeneousValues k P)

theorem cubicHomogeneousValues_nonempty (k : ℕ) (P : cubicHomogeneousSpace k) :
    (cubicHomogeneousValues k P).Nonempty :=
  ⟨_,cubicRecoveryEdge ⟨0,⟨le_rfl,zero_le_one⟩⟩,rfl⟩

theorem cubicHomogeneousValues_bddAbove (k : ℕ) (P : cubicHomogeneousSpace k) :
    BddAbove (cubicHomogeneousValues k P) := by
  obtain ⟨c,hc⟩ := cubicHomogeneousSpace_edgeMaximum k P
  refine ⟨|cubicEdgeProfile P.val c.val|,?_⟩
  rintro y ⟨g,rfl⟩
  exact hc g

theorem cubicHomogeneousCapacity_bound (k : ℕ) (P : cubicHomogeneousSpace k) (g : cubicProbeSection) :
    |cubicPolynomialObservation P.val g| ≤ cubicHomogeneousCapacity k P :=
  le_csSup (cubicHomogeneousValues_bddAbove k P) ⟨g,rfl⟩

theorem cubicHomogeneousCapacity_nonneg (k : ℕ) (P : cubicHomogeneousSpace k) :
    0 ≤ cubicHomogeneousCapacity k P :=
  (abs_nonneg _).trans (cubicHomogeneousCapacity_bound k P
    (cubicRecoveryEdge ⟨0,⟨le_rfl,zero_le_one⟩⟩))

theorem cubicHomogeneousCapacity_attained (k : ℕ) (P : cubicHomogeneousSpace k) :
    ∃ c : Icc (0:ℝ) 1, |cubicEdgeProfile P.val c.val|=cubicHomogeneousCapacity k P := by
  obtain ⟨c,hc⟩ := cubicHomogeneousSpace_edgeMaximum k P
  refine ⟨c,le_antisymm ?_ ?_⟩
  · rw [cubicEdgeProfile_observation]
    exact cubicHomogeneousCapacity_bound k P (cubicRecoveryEdge c)
  · apply csSup_le (cubicHomogeneousValues_nonempty k P)
    rintro y ⟨g,rfl⟩
    exact hc g

theorem cubicHomogeneousCapacity_edgeSup (k : ℕ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity k P=
      sSup ((fun c : ℝ => |cubicEdgeProfile P.val c|) '' Icc 0 1) := by
  have hb : BddAbove ((fun c : ℝ => |cubicEdgeProfile P.val c|) '' Icc 0 1) := by
    refine ⟨cubicHomogeneousCapacity k P,?_⟩
    rintro y ⟨c,hc,rfl⟩
    change |cubicEdgeProfile P.val c| ≤ _
    rw [cubicEdgeProfile_observation P.val ⟨c,hc⟩]
    exact cubicHomogeneousCapacity_bound k P (cubicRecoveryEdge ⟨c,hc⟩)
  have hn : ((fun c : ℝ => |cubicEdgeProfile P.val c|) '' Icc 0 1).Nonempty :=
    ⟨_,0,⟨le_rfl,zero_le_one⟩,rfl⟩
  apply le_antisymm
  · obtain ⟨c,hc⟩ := cubicHomogeneousCapacity_attained k P
    rw [← hc]
    exact le_csSup hb ⟨c.val,c.property,rfl⟩
  · apply csSup_le hn
    rintro y ⟨c,hc,rfl⟩
    change |cubicEdgeProfile P.val c| ≤ _
    rw [cubicEdgeProfile_observation P.val ⟨c,hc⟩]
    exact cubicHomogeneousCapacity_bound k P (cubicRecoveryEdge ⟨c,hc⟩)

theorem cubicHomogeneousCapacity_zero (k : ℕ) : cubicHomogeneousCapacity k 0=0 := by
  apply le_antisymm _ (cubicHomogeneousCapacity_nonneg k 0)
  apply csSup_le (cubicHomogeneousValues_nonempty k 0)
  rintro y ⟨g,rfl⟩
  simp

theorem cubicHomogeneousCapacity_add_le (k : ℕ) (P Q : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity k (P+Q) ≤ cubicHomogeneousCapacity k P+cubicHomogeneousCapacity k Q := by
  apply csSup_le (cubicHomogeneousValues_nonempty k (P+Q))
  rintro y ⟨g,rfl⟩
  change |cubicPolynomialObservation (P.val+Q.val) g| ≤ _
  rw [map_add,Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (cubicHomogeneousCapacity_bound k P g)
    (cubicHomogeneousCapacity_bound k Q g))

theorem cubicHomogeneousCapacity_smul_le (k : ℕ) (r : ℝ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity k (r • P) ≤ ‖r‖*cubicHomogeneousCapacity k P := by
  apply csSup_le (cubicHomogeneousValues_nonempty k (r • P))
  rintro y ⟨g,rfl⟩
  change |cubicPolynomialObservation (r • P.val) g| ≤ _
  rw [map_smul,Pi.smul_apply,smul_eq_mul,abs_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (cubicHomogeneousCapacity_bound k P g) (abs_nonneg r)

def cubicHomogeneousSeminorm (k : ℕ) : Seminorm ℝ (cubicHomogeneousSpace k) :=
  Seminorm.ofSMulLE (cubicHomogeneousCapacity k) (cubicHomogeneousCapacity_zero k)
    (cubicHomogeneousCapacity_add_le k) (cubicHomogeneousCapacity_smul_le k)

theorem cubicHomogeneousCapacity_definite (k : ℕ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity k P=0 ↔ P=0 := by
  constructor
  · intro h
    have hz : cubicPolynomialObservation P.val=0 := by
      ext g
      have hb := cubicHomogeneousCapacity_bound k P g
      rw [h] at hb
      exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    apply Subtype.ext
    exact (cubicPolynomialObservation_zero_iff P.val).mp hz
  · rintro rfl
    exact cubicHomogeneousCapacity_zero k

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
