import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Reduction of integral general linear matrices is surjective.
Its kernel in the p-adic general linear group is the compact open
subgroup whose entries are congruent to the identity modulo p. -/

noncomputable section

open Matrix

namespace GlobalTheory.GLp

variable (p : ℕ) [Fact p.Prime] (n : Type*) [Fintype n] [DecidableEq n]

/-- The inclusion of integral matrices in the p-adic general linear group. -/
def integralInclusion : GL n ℤ_[p] →* GL n ℚ_[p] :=
  GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p])

/-- Reduction modulo the maximal ideal of the p-adic integers. -/
def integralReduction : GL n ℤ_[p] →* GL n (ZMod p) :=
  GeneralLinearGroup.map PadicInt.toZMod

theorem integralReduction_surjective : Function.Surjective (integralReduction p n) := by
  intro y
  choose entries he using fun i j : n => ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) (y.val i j)
  let M : Matrix n n ℤ_[p] := Matrix.of entries
  have hM : PadicInt.toZMod.mapMatrix M = y.val := Matrix.ext he
  have hm : IsUnit M.det := by
    by_contra h
    have h' : M.det ∈ IsLocalRing.maximalIdeal ℤ_[p] := h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hM] at h'
    exact (Matrix.isUnits_det_units y).ne_zero h'
  have hu := (Matrix.isUnit_iff_isUnit_det M).mpr hm
  refine ⟨hu.unit, Units.ext ?_⟩
  change PadicInt.toZMod.mapMatrix (hu.unit : Matrix n n ℤ_[p]) = y.val
  rw [IsUnit.unit_spec, hM]

/-- The first principal congruence subgroup of the p-adic general linear group. -/
def principalCongruenceOne : Subgroup (GL n ℚ_[p]) :=
  (integralReduction p n).ker.map (integralInclusion p n)

private theorem residue_eq_zero_iff_norm_lt_one (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private theorem integralReduction_eq_one_iff (x : GL n ℤ_[p]) :
    integralReduction p n x = 1 ↔ ∀ i j, ‖(x.val - 1) i j‖ < 1 := by
  have he : integralReduction p n x = 1 ↔ PadicInt.toZMod.mapMatrix (x.val - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
    exact Units.ext_iff
  rw [he]
  exact ⟨fun h i j => (residue_eq_zero_iff_norm_lt_one p _).mp (congrFun (congrFun h i) j),
    fun h => Matrix.ext fun i j => (residue_eq_zero_iff_norm_lt_one p _).mpr (h i j)⟩

private theorem coe_one_matrix (i j : n) :
    (((1 : Matrix n n ℤ_[p]) i j : ℤ_[p]) : ℚ_[p]) = (1 : Matrix n n ℚ_[p]) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_principalCongruenceOne_iff (x : GL n ℚ_[p]) :
    x ∈ principalCongruenceOne p n ↔ ∀ i j, ‖(x.val - 1) i j‖ < 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ i j
    have hy' := (integralReduction_eq_one_iff p n y).mp hy i j
    rw [PadicInt.norm_def, Matrix.sub_apply, PadicInt.coe_sub, coe_one_matrix] at hy'
    rw [Matrix.sub_apply]
    exact hy'
  · intro hx
    have hInt (i j : n) : ‖x.val i j‖ ≤ 1 := by
      rw [← sub_add_cancel (x.val i j) ((1 : Matrix n n ℚ_[p]) i j)]
      refine (Padic.nonarchimedean _ _).trans (max_le (hx i j).le ?_)
      rw [Matrix.one_apply]
      split_ifs <;> simp
    let M : Matrix n n ℤ_[p] := fun i j => ⟨x.val i j, hInt i j⟩
    have hMsub : PadicInt.toZMod.mapMatrix (M - 1) = 0 := by
      ext i j
      apply (residue_eq_zero_iff_norm_lt_one p _).mpr
      rw [PadicInt.norm_def, Matrix.sub_apply, PadicInt.coe_sub, coe_one_matrix]
      exact hx i j
    have hM : PadicInt.toZMod.mapMatrix M = 1 := by
      rwa [map_sub, map_one, sub_eq_zero] at hMsub
    have hm : IsUnit M.det := by
      by_contra h
      have h' : M.det ∈ IsLocalRing.maximalIdeal ℤ_[p] := h
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hM, Matrix.det_one] at h'
      exact one_ne_zero h'
    have hu := (Matrix.isUnit_iff_isUnit_det M).mpr hm
    refine ⟨hu.unit, ?_, Units.ext ?_⟩
    · apply Units.ext
      change PadicInt.toZMod.mapMatrix (hu.unit : Matrix n n ℤ_[p]) = 1
      rw [IsUnit.unit_spec, hM]
    · change (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (hu.unit : Matrix n n ℤ_[p]) = x.val
      rw [IsUnit.unit_spec]
      exact Matrix.ext fun _ _ => rfl

theorem isOpen_principalCongruenceOne : IsOpen (principalCongruenceOne p n : Set (GL n ℚ_[p])) := by
  have he : (principalCongruenceOne p n : Set (GL n ℚ_[p])) =
      {x | ∀ i j, ‖(x.val - 1) i j‖ < 1} :=
    Set.ext (mem_principalCongruenceOne_iff p n)
  rw [he]
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
  exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm

theorem isCompact_principalCongruenceOne : IsCompact (principalCongruenceOne p n : Set (GL n ℚ_[p])) := by
  haveI : CompactSpace (Matrix n n ℤ_[p]) := inferInstanceAs (CompactSpace (n → n → ℤ_[p]))
  have hc : Continuous (integralInclusion p n) :=
    Units.continuous_map (continuous_id.matrix_map continuous_subtype_val)
  have ho : IsOpen ((integralReduction p n).ker : Set (GL n ℤ_[p])) := by
    have he : ((integralReduction p n).ker : Set (GL n ℤ_[p])) =
        {x | ∀ i j, ‖(x.val - 1) i j‖ < 1} := Set.ext (integralReduction_eq_one_iff p n)
    rw [he]
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm
  exact ((integralReduction p n).ker.isClosed_of_isOpen ho).isCompact.image hc

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.integralReduction_surjective
#print axioms GlobalTheory.GLp.isCompact_principalCongruenceOne
#print axioms GlobalTheory.GLp.isOpen_principalCongruenceOne
