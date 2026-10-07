import GaloisForLFunctions.HTGeometry.ClosedLogarithmicLoops
import GaloisForLFunctions.RHTower.XiMarkedIslandSeparation
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The actual source space for finite marked Xi monodromy

All real exponential marks have the common value one-half at zero.
Deleting their minus-one divisors together with the Xi divisor leaves a
path-connected plane domain, since the deleted set is countable.
-/

open Set Topology unitInterval

namespace RHTower.XiMarkedMonodromy

noncomputable section

abbrev Target := {z : ℂ // z ≠ 0 ∧ z ≠ -1}

def targetHalf : Target := ⟨1 / 2, by norm_num⟩

def targetToPunctured : C(Target, Pi1CMinusZero.Cs) :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def value (a : ℝ) (s : ℂ) : ℂ := xi s * Complex.exp (-(a : ℂ) * s)

theorem value_differentiable (a : ℝ) : Differentiable ℂ (value a) :=
  xi_differentiable.mul (by fun_prop)

@[simp] theorem value_zero (a : ℝ) : value a 0 = 1 / 2 := by
  simp [value, xi_zero]

def sourceSet (A : Finset ℝ) : Set ℂ :=
  {s | xi s ≠ 0 ∧ ∀ a ∈ A, value a s ≠ -1}

abbrev Source (A : Finset ℝ) := sourceSet A

def sourceZero (A : Finset ℝ) : Source A :=
  ⟨0, by norm_num [sourceSet, xi_zero]⟩

/-- The common marked-source domain is path connected, with no zero-location premise. -/
theorem sourceSet_pathConnected (A : Finset ℝ) : IsPathConnected (sourceSet A) := by
  have hxi : {s : ℂ | xi s = 0}.Countable :=
    countable_setOf_eq_zero_of_differentiable xi_differentiable
      (x := 0) (by rw [xi_zero]; norm_num)
  have hv (a : ℝ) : {s : ℂ | value a s = -1}.Countable := by
    have hc := countable_setOf_eq_zero_of_differentiable
      ((value_differentiable a).add_const 1)
      (x := 0) (by rw [value_zero]; norm_num)
    simpa only [add_eq_zero_iff_eq_neg] using hc
  have hc : ({s : ℂ | xi s = 0} ∪ ⋃ a ∈ A, {s : ℂ | value a s = -1}).Countable :=
    hxi.union (A.countable_toSet.biUnion fun a _ => hv a)
  have hp := hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  convert hp using 1
  ext s
  simp [sourceSet]

instance source_pathConnectedSpace (A : Finset ℝ) : PathConnectedSpace (Source A) :=
  isPathConnected_iff_pathConnectedSpace.mp (sourceSet_pathConnected A)

/-- Each marked coordinate is an actual continuous map to the twice-punctured plane. -/
def coordinate (A : Finset ℝ) (a : A) : C(Source A, Target) :=
  ⟨fun s => ⟨value a s, mul_ne_zero s.2.1 (Complex.exp_ne_zero _), s.2.2 a a.2⟩,
    ((value_differentiable a).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem coordinate_sourceZero (A : Finset ℝ) (a : A) :
    coordinate A a (sourceZero A) = targetHalf := by
  apply Subtype.ext
  exact value_zero a

end

end RHTower.XiMarkedMonodromy
