import GaloisForLFunctions.HTGeometry.DifferentialClosureStep

/-!
# The tower of one-step extensions and its union

Iterating the one-step extension gives a chain of differential fields; its union carries a field
structure as the directed union of fields, and a derivation obtained from the universal property:
the maps `x ↦ (x, x′)` into the dual numbers of the union are compatible along the tower, so they
lift to a ring map whose first component is the identity, and whose second component is therefore a
derivation extending the derivation of every stage.

Every consistent system over a stage acquires a solution one stage later, so the union is the field
over which the differential Nullstellensatz will be available.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable (F : Type u) [Field F] [Algebra ℚ F] [Differential F]

/-- A differential field extension solving every consistent differential system over `F`. -/
def closureStep : DiffFieldExt F := (exists_ext_solving_all F).choose

theorem exists_solution_closureStep (n : ℕ)
    (I : Ideal (DifferentialPolynomial (ULift.{u} (Fin n)) F))
    (hδ : ∀ x ∈ I, differentialPolynomialOverDerivation (ULift.{u} (Fin n)) F x ∈ I)
    (hne : I ≠ ⊤) :
    ∃ y : ULift.{u} (Fin n) → (closureStep F).carrier,
      ∀ p ∈ I, differentialPolynomialEvalOver (K := F) y p = 0 :=
  (exists_ext_solving_all F).choose_spec n I hδ hne

/-- The tower of iterated one-step extensions. -/
def diffTowerExt : ℕ → DiffFieldExt F
  | 0 => DiffFieldExt.refl
  | (n + 1) => (diffTowerExt n).trans (closureStep (diffTowerExt n).carrier)

/-- The `n`-th stage of the tower. -/
abbrev diffTowerCarrier (n : ℕ) : Type u := (diffTowerExt F n).carrier

theorem diffTowerCarrier_succ (n : ℕ) :
    diffTowerCarrier F (n + 1) = (closureStep (diffTowerCarrier F n)).carrier := rfl

/-- The map from one stage of the tower to the next. -/
def diffTowerStepHom (n : ℕ) : diffTowerCarrier F n →+* diffTowerCarrier F (n + 1) :=
  algebraMap (diffTowerCarrier F n) (closureStep (diffTowerCarrier F n)).carrier

theorem diffTowerStepHom_deriv (n : ℕ) (x : diffTowerCarrier F n) :
    diffTowerStepHom F n (Differential.deriv x) = Differential.deriv (diffTowerStepHom F n x) :=
  ((closureStep (diffTowerCarrier F n)).compat x).symm

/-- The map between two stages of the tower. -/
def diffTowerHom {i j : ℕ} (h : i ≤ j) : diffTowerCarrier F i →+* diffTowerCarrier F j :=
  Nat.leRec (motive := fun j _ => diffTowerCarrier F i →+* diffTowerCarrier F j) (RingHom.id _)
    (fun {m} _ φ => (diffTowerStepHom F m).comp φ) h

theorem diffTowerHom_self (i : ℕ) (h : i ≤ i) : diffTowerHom F h = RingHom.id _ :=
  Nat.leRec_self _ _

theorem diffTowerHom_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    diffTowerHom F h' = (diffTowerStepHom F j).comp (diffTowerHom F h) :=
  Nat.leRec_succ _ _ h

theorem diffTowerHom_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k)
    (x : diffTowerCarrier F i) : diffTowerHom F hjk (diffTowerHom F hij x) = diffTowerHom F hik x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [diffTowerHom_self]; rfl
  | succ k hjk ih =>
      rw [diffTowerHom_succ F hjk (le_trans hjk (Nat.le_succ k)),
        diffTowerHom_succ F (le_trans hij hjk) hik, RingHom.comp_apply, RingHom.comp_apply,
        ih (le_trans hij hjk)]

instance diffTowerDirectedSystem :
    DirectedSystem (diffTowerCarrier F) (fun _ _ h => ⇑(diffTowerHom F h)) where
  map_self := by
    intro i x
    rw [diffTowerHom_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    exact diffTowerHom_trans F hij hjk (le_trans hij hjk) x

theorem diffTowerHom_deriv {i j : ℕ} (h : i ≤ j) (x : diffTowerCarrier F i) :
    diffTowerHom F h (Differential.deriv x) = Differential.deriv (diffTowerHom F h x) := by
  induction j, h using Nat.le_induction with
  | base => rw [diffTowerHom_self]; rfl
  | succ j h ih =>
      rw [diffTowerHom_succ F h (le_trans h (Nat.le_succ j)), RingHom.comp_apply, RingHom.comp_apply,
        ih, diffTowerStepHom_deriv]

/-- The union of the tower: a differential field in which every consistent system over any stage has
a solution. -/
def diffClosure : Type u := Ring.DirectLimit (diffTowerCarrier F) (fun _ _ h => ⇑(diffTowerHom F h))

instance diffClosureCommRing : CommRing (diffClosure F) :=
  inferInstanceAs (CommRing (Ring.DirectLimit (diffTowerCarrier F) (fun _ _ h => ⇑(diffTowerHom F h))))

noncomputable instance diffClosureFieldInstance : Field (diffClosure F) :=
  { diffClosureCommRing F,
    Field.DirectLimit.field (diffTowerCarrier F) (fun _ _ h => diffTowerHom F h) with }


/-- The canonical map from a stage of the tower into the union. -/
def diffTowerLimitHom (n : ℕ) : diffTowerCarrier F n →+* diffClosure F :=
  Ring.DirectLimit.of (diffTowerCarrier F) (fun _ _ h => ⇑(diffTowerHom F h)) n

theorem diffTowerLimitHom_diffTowerHom {i j : ℕ} (h : i ≤ j) (x : diffTowerCarrier F i) :
    diffTowerLimitHom F j (diffTowerHom F h x) = diffTowerLimitHom F i x :=
  Ring.DirectLimit.of_f h x

/-- Each stage maps to the dual numbers of the union, recording the derivative. -/
def diffTowerDualHom (n : ℕ) : diffTowerCarrier F n →+* DualNumber (diffClosure F) where
  toFun x := TrivSqZeroExt.inl (diffTowerLimitHom F n x)
    + TrivSqZeroExt.inr (diffTowerLimitHom F n (Differential.deriv x))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [Derivation.map_one_eq_zero]
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.fst_mul]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, zero_add, add_zero, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_mul]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [map_add]

theorem diffTowerDualHom_diffTowerHom {i j : ℕ} (h : i ≤ j) (x : diffTowerCarrier F i) :
    diffTowerDualHom F j (diffTowerHom F h x) = diffTowerDualHom F i x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [diffTowerDualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      diffTowerLimitHom_diffTowerHom]
  · simp only [diffTowerDualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rw [← diffTowerHom_deriv, diffTowerLimitHom_diffTowerHom]

/-- The lift of the dual-number maps to the union. -/
def diffClosureDualLift : diffClosure F →+* DualNumber (diffClosure F) := by
  exact Ring.DirectLimit.lift (diffTowerCarrier F) (fun _ _ h => ⇑(diffTowerHom F h))
    (DualNumber (diffClosure F)) (diffTowerDualHom F)
    (fun _ _ hij x => diffTowerDualHom_diffTowerHom F hij x)

theorem diffClosureDualLift_diffTowerLimitHom (n : ℕ) (x : diffTowerCarrier F n) :
    diffClosureDualLift F (diffTowerLimitHom F n x) = diffTowerDualHom F n x := by
  exact Ring.DirectLimit.lift_of _ _ _ n x

theorem diffClosureDualLift_fst (z : diffClosure F) : (diffClosureDualLift F z).fst = z := by
  refine Ring.DirectLimit.induction_on (G := diffTowerCarrier F) z fun n x => ?_
  show (diffClosureDualLift F (diffTowerLimitHom F n x)).fst = diffTowerLimitHom F n x
  rw [diffClosureDualLift_diffTowerLimitHom]
  simp [diffTowerDualHom]

/-- The derivation of the union, read off from the dual-number lift. -/
def diffClosureDerivation : Derivation ℤ (diffClosure F) (diffClosure F) where
  toFun z := (diffClosureDualLift F z).snd
  map_add' x y := by
    show (diffClosureDualLift F (x + y)).snd = _
    rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' c z := by
    show (diffClosureDualLift F (c • z)).snd = c • (diffClosureDualLift F z).snd
    rw [map_zsmul]
    simp
  map_one_eq_zero' := by
    show (diffClosureDualLift F 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  leibniz' x y := by
    show (diffClosureDualLift F (x * y)).snd
      = x • (diffClosureDualLift F y).snd + y • (diffClosureDualLift F x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, diffClosureDualLift_fst, diffClosureDualLift_fst,
      smul_eq_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

instance : Differential (diffClosure F) := ⟨diffClosureDerivation F⟩

theorem deriv_diffTowerLimitHom (n : ℕ) (x : diffTowerCarrier F n) :
    Differential.deriv (diffTowerLimitHom F n x) = diffTowerLimitHom F n (Differential.deriv x) := by
  show (diffClosureDualLift F (diffTowerLimitHom F n x)).snd = _
  rw [diffClosureDualLift_diffTowerLimitHom]
  simp [diffTowerDualHom]

instance diffTowerAlgebra (n : ℕ) : Algebra (diffTowerCarrier F n) (diffClosure F) :=
  (diffTowerLimitHom F n).toAlgebra

theorem algebraMap_diffTower (n : ℕ) (x : diffTowerCarrier F n) :
    algebraMap (diffTowerCarrier F n) (diffClosure F) x = diffTowerLimitHom F n x := rfl

theorem algebraMap_diffTower_step (n : ℕ) (x : diffTowerCarrier F n) :
    algebraMap (diffTowerCarrier F n) (diffClosure F) x
      = diffTowerLimitHom F (n + 1) (diffTowerStepHom F n x) := by
  rw [algebraMap_diffTower]
  rw [← diffTowerLimitHom_diffTowerHom F (Nat.le_succ n) x]
  congr 1
  rw [diffTowerHom_succ F (le_refl n) (Nat.le_succ n), RingHom.comp_apply, diffTowerHom_self]
  rfl

theorem deriv_algebraMap_diffTower (n : ℕ) (x : diffTowerCarrier F n) :
    Differential.deriv (algebraMap (diffTowerCarrier F n) (diffClosure F) x)
      = algebraMap (diffTowerCarrier F n) (diffClosure F) (Differential.deriv x) := by
  rw [algebraMap_diffTower, algebraMap_diffTower, deriv_diffTowerLimitHom]

instance : Algebra F (diffClosure F) := (diffTowerLimitHom F 0).toAlgebra

instance : Algebra ℚ (diffClosure F) := ((diffTowerLimitHom F 0).comp (algebraMap ℚ F)).toAlgebra

theorem algebraMap_diffClosure (a : F) :
    algebraMap F (diffClosure F) a = diffTowerLimitHom F 0 a := rfl

/-- The union of the tower, as a differential field extension of the base. -/
def diffClosureExt : DiffFieldExt F where
  carrier := diffClosure F
  compat := fun a => by
    rw [algebraMap_diffClosure, algebraMap_diffClosure, deriv_diffTowerLimitHom]
    rfl

end

end GaloisForLFunctions.HTGeometry
