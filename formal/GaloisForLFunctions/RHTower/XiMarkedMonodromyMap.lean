import GaloisForLFunctions.HTGeometry.NormalizedWindingHom
import GaloisForLFunctions.RHTower.XiMarkedLoopPackets
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The actual finite marked Xi monodromy map

The source basepoint is zero and every coordinate target basepoint is one-half.
Normalized zero winding is identical in every coordinate, because exponential
factors have zero winding on every source loop.
-/

open Topology Pi1CMinusZero
open GaloisForLFunctions.HTGeometry

namespace RHTower.XiMarkedMonodromy

noncomputable section

abbrev TargetGroup := FundamentalGroup Target targetHalf
abbrev JointGroup (A : Finset ℝ) := A → TargetGroup

def jointMap (A : Finset ℝ) :
    FundamentalGroup (Source A) (sourceZero A) →* JointGroup A :=
  MonoidHom.pi fun a => FundamentalGroup.mapOfEq (coordinate A a) (coordinate_sourceZero A a)

def zeroWinding : TargetGroup →* Multiplicative ℤ :=
  normalizedWindingHom targetToPunctured targetHalf

def xiPunctured (A : Finset ℝ) : C(Source A, Cs) :=
  ⟨fun s => ⟨xi s, s.2.1⟩,
    (xi_differentiable.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Every coordinate has the winding of the same actual Xi source loop. -/
theorem zeroWinding_jointMap (A : Finset ℝ)
    (q : FundamentalGroup (Source A) (sourceZero A)) (a : A) :
    zeroWinding (jointMap A q a) = normalizedWindingHom (xiPunctured A) (sourceZero A) q := by
  change ((normalizedWindingHom targetToPunctured targetHalf).comp
    (FundamentalGroup.mapOfEq (coordinate A a) (coordinate_sourceZero A a))) q = _
  rw [normalizedWindingHom_comp_mapOfEq]
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [normalizedWindingHom_mk, normalizedWindingHom_mk]
    apply congrArg Multiplicative.ofAdd
    have hxc : Continuous (fun s : Source A => xi (s : ℂ)) :=
      xi_differentiable.continuous.comp continuous_subtype_val
    have hxn : ∀ s : Source A, xi (s : ℂ) ≠ 0 := fun s => s.2.1
    have hmc : Continuous (fun s : Source A => -(a : ℂ) * (s : ℂ)) := by fun_prop
    have hec := Complex.continuous_exp.comp hmc
    have hen : ∀ s : Source A, Complex.exp (-(a : ℂ) * (s : ℂ)) ≠ 0 :=
      fun s => Complex.exp_ne_zero _
    change Bottcher.wind (fun s : Source A => xi (s : ℂ) *
      Complex.exp (-(a : ℂ) * (s : ℂ))) (hxc.mul hec)
        (fun s => mul_ne_zero (hxn s) (hen s)) p = Bottcher.wind _ hxc hxn p
    rw [Bottcher.wind_mul, Bottcher.wind_exp, add_zero] <;> assumption

/-- The full marked winding vector is diagonal, including the empty mark family. -/
theorem jointMap_zero_winding_diagonal (A : Finset ℝ)
    (q : FundamentalGroup (Source A) (sourceZero A)) :
    ∃ k : Multiplicative ℤ, ∀ a : A, zeroWinding (jointMap A q a) = k :=
  ⟨normalizedWindingHom (xiPunctured A) (sourceZero A) q,
    fun a => zeroWinding_jointMap A q a⟩

end

end RHTower.XiMarkedMonodromy
