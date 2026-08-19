import GaloisForLFunctions.HTGeometry.QuotientDerivation
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# The logarithmic derivative transfers the additive classification to the multiplicative group

Cassidy's classification of differential algebraic subgroups of `G_a` says a proper one is cut out
by a nonzero linear differential operator; the coordinate-ideal form of that statement is already in
the tree (`DifferentialHopfPrimitive.nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation`).
The multiplicative case is obtained from it by the logarithmic derivative, which is a group
homomorphism from the units of a differential field to its additive group.

This file supplies that transfer: the subgroup of units on which a constant-coefficient linear
differential operator kills the logarithmic derivative is exactly the preimage, under the
logarithmic-derivative homomorphism, of the additive subgroup the same operator cuts out.  Both
sides are groups, and the identification is definitional once the homomorphism is in place.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {F : Type*} [Field F] [Differential F]

theorem differentialJet_neg (n : ℕ) (x : F) :
    differentialJet n (-x) = -differentialJet n x := by
  induction n with
  | zero => simp
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, ih, map_neg]

theorem differentialJet_zero_arg (n : ℕ) : differentialJet n (0 : F) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [differentialJet_succ, ih, map_zero]

/-- A constant-coefficient linear differential operator applied to an element. -/
def jetOperator {m : ℕ} (c : Fin m → F) (x : F) : F :=
  ∑ i, c i * differentialJet (i : ℕ) x

theorem jetOperator_add {m : ℕ} (c : Fin m → F) (x y : F) :
    jetOperator c (x + y) = jetOperator c x + jetOperator c y := by
  unfold jetOperator
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [differentialJet_add_apply, mul_add]

theorem jetOperator_zero {m : ℕ} (c : Fin m → F) : jetOperator c (0 : F) = 0 := by
  unfold jetOperator
  exact Finset.sum_eq_zero fun i _ => by rw [differentialJet_zero_arg, mul_zero]

theorem jetOperator_neg {m : ℕ} (c : Fin m → F) (x : F) :
    jetOperator c (-x) = -jetOperator c x := by
  unfold jetOperator
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [differentialJet_neg, mul_neg]

/-- **The additive relation subgroup.**  A constant-coefficient linear differential operator cuts
out an additive subgroup: this is the shape of every proper differential algebraic subgroup of the
additive group. -/
def jetRelationAddSubgroup {m : ℕ} (c : Fin m → F) : AddSubgroup F where
  carrier := {x | jetOperator c x = 0}
  zero_mem' := jetOperator_zero c
  add_mem' := by
    intro x y hx hy
    show jetOperator c (x + y) = 0
    rw [jetOperator_add, show jetOperator c x = 0 from hx, show jetOperator c y = 0 from hy,
      add_zero]
  neg_mem' := by
    intro x hx
    show jetOperator c (-x) = 0
    rw [jetOperator_neg, show jetOperator c x = 0 from hx, neg_zero]

@[simp] theorem mem_jetRelationAddSubgroup {m : ℕ} {c : Fin m → F} {x : F} :
    x ∈ jetRelationAddSubgroup c ↔ jetOperator c x = 0 := Iff.rfl

variable (F) in
/-- **The logarithmic derivative is a group homomorphism from the units to the additive group.** -/
def logDerivHom : Fˣ →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (Differential.logDeriv (x : F))
  map_one' := by
    show Multiplicative.ofAdd (Differential.logDeriv ((1 : Fˣ) : F)) = 1
    rw [Units.val_one, Differential.logDeriv_one]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (Differential.logDeriv ((x * y : Fˣ) : F))
      = Multiplicative.ofAdd (Differential.logDeriv (x : F))
        * Multiplicative.ofAdd (Differential.logDeriv (y : F))
    have hx : ((x : F)) ≠ 0 := Units.ne_zero x
    have hy : ((y : F)) ≠ 0 := Units.ne_zero y
    have hmul : Differential.logDeriv ((x : F) * (y : F))
        = Differential.logDeriv (x : F) + Differential.logDeriv (y : F) :=
      Differential.logDeriv_mul (x : F) (y : F) hx hy
    rw [Units.val_mul, hmul]
    rfl

@[simp] theorem logDerivHom_apply (x : Fˣ) :
    logDerivHom F x = Multiplicative.ofAdd (Differential.logDeriv (x : F)) := rfl

/-- **The multiplicative relation subgroup.**  The units on which a constant-coefficient linear
differential operator kills the logarithmic derivative. -/
def logDerivRelationSubgroup {m : ℕ} (c : Fin m → F) : Subgroup Fˣ :=
  Subgroup.comap (logDerivHom F) (AddSubgroup.toSubgroup (jetRelationAddSubgroup c))

@[simp] theorem mem_logDerivRelationSubgroup {m : ℕ} {c : Fin m → F} {x : Fˣ} :
    x ∈ logDerivRelationSubgroup c ↔ jetOperator c (Differential.logDeriv (x : F)) = 0 :=
  Iff.rfl

/-- **The transfer.**  The multiplicative relation subgroup is exactly the preimage of the additive
one under the logarithmic derivative. -/
theorem logDerivRelationSubgroup_eq_comap {m : ℕ} (c : Fin m → F) :
    logDerivRelationSubgroup c
      = Subgroup.comap (logDerivHom F) (AddSubgroup.toSubgroup (jetRelationAddSubgroup c)) := rfl

/-- Every constant unit lies in every relation subgroup: the constants are the kernel of the
logarithmic derivative. -/
theorem constant_mem_logDerivRelationSubgroup {m : ℕ} (c : Fin m → F) {x : Fˣ}
    (hx : Differential.deriv (x : F) = 0) : x ∈ logDerivRelationSubgroup c := by
  show jetOperator c (Differential.logDeriv (x : F)) = 0
  have hlog : Differential.logDeriv (x : F) = 0 :=
    (Differential.logDeriv_eq_zero (a := (x : F))).mpr hx
  rw [hlog, jetOperator_zero]

end

end GaloisForLFunctions.HTGeometry
