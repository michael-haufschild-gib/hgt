import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupHopf
import GaloisForLFunctions.HTGeometry.HopfAntipodeCoLie

/-!
# Hopf algebra of a represented differential matrix group

The differential coordinate algebra of a determinant-one matrix group carries the usual
commutative Hopf-algebra structure.  The laws are proved by injective evaluation on triples of
group points, so they do not depend on a chosen polynomial presentation.
-/

open scoped Differential TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u

variable {C G : Type u} [Field C] [Differential C] [Group G]

namespace DifferentialMatrixGroupRepresentation

variable (r : DifferentialMatrixGroupRepresentation (C := C) (G := G))

local instance hopfAlgebraAmbientFunctionDifferential : Differential (G → C) :=
  pointwiseFunctionDifferential G

local instance hopfAlgebraCoordinateDifferential : Differential r.coordinateAlgebra :=
  r.coordinateAlgebraDifferential

/-- Inclusion of the coordinate algebra into all scalar-valued functions. -/
def coordinateFunctionLinear : r.coordinateAlgebra →ₗ[C] (G → C) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of a right-associated triple tensor on three group points. -/
def coordinateTripleEval :
    r.coordinateAlgebra ⊗[C] (r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) →ₗ[C]
      (G × (G × G) → C) :=
  (GaloisForLFunctions.RHTower.functionTensorProductHom C G (G × G)).comp
    (TensorProduct.map r.coordinateFunctionLinear r.coordinateTensorEval.toLinearMap)

theorem coordinateTripleEval_tmul
    (f : r.coordinateAlgebra)
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (x y z : G) :
    r.coordinateTripleEval (f ⊗ₜ[C] t) (x, (y, z)) =
      f.1 x * r.coordinateTensorEval t (y, z) := by
  rw [coordinateTripleEval, LinearMap.comp_apply, TensorProduct.map_tmul,
    GaloisForLFunctions.RHTower.functionTensorProductHom_tmul]
  rfl

@[simp] theorem coordinateTripleEval_tmul_tmul
    (f g h : r.coordinateAlgebra) (x y z : G) :
    r.coordinateTripleEval (f ⊗ₜ[C] (g ⊗ₜ[C] h)) (x, (y, z)) =
      f.1 x * (g.1 y * h.1 z) := by
  rw [r.coordinateTripleEval_tmul, r.coordinateTensorEval_tmul]

theorem coordinateTripleEval_assoc_tmul
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra)
    (h : r.coordinateAlgebra) (x y z : G) :
    r.coordinateTripleEval
        ((Algebra.TensorProduct.assoc C C C _ _ _) (t ⊗ₜ[C] h)) (x, (y, z)) =
      r.coordinateTensorEval t (x, y) * h.1 z := by
  induction t using TensorProduct.induction_on with
  | zero =>
      have ht : (0 : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) ⊗ₜ[C] h = 0 :=
        TensorProduct.zero_tmul (r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) h
      have hassoc : (Algebra.TensorProduct.assoc C C C _ _ _)
          (0 : (r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) ⊗[C]
            r.coordinateAlgebra) = 0 := by
        exact (Algebra.TensorProduct.assoc C C C _ _ _).toLinearMap.map_zero
      have htriple : r.coordinateTripleEval 0 = 0 := r.coordinateTripleEval.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      rw [ht, hassoc, htriple, heval]
      change (0 : C) = 0 * h.1 z
      exact (zero_mul _).symm
  | add a b ha hb =>
      have ht : (a + b) ⊗ₜ[C] h = a ⊗ₜ[C] h + b ⊗ₜ[C] h :=
        TensorProduct.add_tmul _ _ _
      have hassoc : (Algebra.TensorProduct.assoc C C C _ _ _)
          (a ⊗ₜ[C] h + b ⊗ₜ[C] h) =
          (Algebra.TensorProduct.assoc C C C _ _ _) (a ⊗ₜ[C] h) +
          (Algebra.TensorProduct.assoc C C C _ _ _) (b ⊗ₜ[C] h) := by
        exact (Algebra.TensorProduct.assoc C C C _ _ _).toLinearMap.map_add _ _
      have htriple := r.coordinateTripleEval.map_add
          ((Algebra.TensorProduct.assoc C C C _ _ _) (a ⊗ₜ[C] h))
          ((Algebra.TensorProduct.assoc C C C _ _ _) (b ⊗ₜ[C] h))
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      rw [ht, hassoc, htriple, Pi.add_apply, ha, hb, heval, Pi.add_apply, add_mul]
  | tmul f g =>
      rw [Algebra.TensorProduct.assoc_tmul,
        r.coordinateTripleEval_tmul_tmul,
        r.coordinateTensorEval_tmul]
      exact (mul_assoc _ _ _).symm

/-- Separated evaluation on three factors is injective. -/
theorem coordinateTripleEval_injective : Function.Injective r.coordinateTripleEval := by
  apply Function.Injective.comp
    (GaloisForLFunctions.RHTower.functionTensorProductHom_injective C G (G × G))
  apply TensorProduct.map_injective_of_flat_flat
  · intro f g h
    exact Subtype.ext h
  · exact r.coordinateTensorEval_injective

theorem coordinateTripleEval_map_comul_id
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (x y z : G) :
    r.coordinateTripleEval
        ((Algebra.TensorProduct.assoc C C C _ _ _)
          (Algebra.TensorProduct.map r.coordinateComul (AlgHom.id C r.coordinateAlgebra) t))
        (x, (y, z)) =
      r.coordinateTensorEval t (x * y, z) := by
  let F := Algebra.TensorProduct.map r.coordinateComul
    (AlgHom.id C r.coordinateAlgebra)
  let α := Algebra.TensorProduct.assoc C C C r.coordinateAlgebra
    r.coordinateAlgebra r.coordinateAlgebra
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have hα : α 0 = 0 := α.map_zero
      have htriple : r.coordinateTripleEval 0 = 0 := r.coordinateTripleEval.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change r.coordinateTripleEval (α (F 0)) (x, (y, z)) =
        r.coordinateTensorEval 0 (x * y, z)
      rw [hF, hα, htriple, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have hα : α (F a + F b) = α (F a) + α (F b) := α.map_add _ _
      have htriple := r.coordinateTripleEval.map_add (α (F a)) (α (F b))
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change r.coordinateTripleEval (α (F (a + b))) (x, (y, z)) =
        r.coordinateTensorEval (a + b) (x * y, z)
      rw [hF, hα, htriple, Pi.add_apply, heval, Pi.add_apply, ha, hb]
  | tmul f g =>
      rw [Algebra.TensorProduct.map_tmul,
        r.coordinateTripleEval_assoc_tmul,
        r.coordinateTensorEval_tmul]
      rw [r.coordinateTensorEval_coordinateComul]
      rfl

theorem coordinateTripleEval_map_id_comul
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (x y z : G) :
    r.coordinateTripleEval
        (Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra) r.coordinateComul t)
        (x, (y, z)) =
      r.coordinateTensorEval t (x, y * z) := by
  let F := Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra)
    r.coordinateComul
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have htriple : r.coordinateTripleEval 0 = 0 := r.coordinateTripleEval.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change r.coordinateTripleEval (F 0) (x, (y, z)) =
        r.coordinateTensorEval 0 (x, y * z)
      rw [hF, htriple, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have htriple := r.coordinateTripleEval.map_add (F a) (F b)
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change r.coordinateTripleEval (F (a + b)) (x, (y, z)) =
        r.coordinateTensorEval (a + b) (x, y * z)
      rw [hF, htriple, Pi.add_apply, heval, Pi.add_apply, ha, hb]
  | tmul f g =>
      rw [Algebra.TensorProduct.map_tmul,
        r.coordinateTripleEval_tmul,
        r.coordinateTensorEval_tmul]
      rw [r.coordinateTensorEval_coordinateComul]
      rfl

theorem coordinateLid_map_counit_id_apply
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (g : G) :
    ((Algebra.TensorProduct.lid C r.coordinateAlgebra)
        (Algebra.TensorProduct.map r.coordinateCounit
          (AlgHom.id C r.coordinateAlgebra) t)).1 g =
      r.coordinateTensorEval t (1, g) := by
  let F := Algebra.TensorProduct.map r.coordinateCounit
    (AlgHom.id C r.coordinateAlgebra)
  let lidMap := Algebra.TensorProduct.lid C r.coordinateAlgebra
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have hlid : lidMap 0 = 0 := lidMap.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change (lidMap (F 0)).1 g = r.coordinateTensorEval 0 (1, g)
      rw [hF, hlid, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have hlid : lidMap (F a + F b) = lidMap (F a) + lidMap (F b) :=
        lidMap.map_add _ _
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change (lidMap (F (a + b))).1 g = r.coordinateTensorEval (a + b) (1, g)
      rw [hF, hlid, heval]
      change (lidMap (F a)).1 g + (lidMap (F b)).1 g =
        r.coordinateTensorEval a (1, g) + r.coordinateTensorEval b (1, g)
      rw [ha, hb]
  | tmul f h =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        r.coordinateTensorEval_tmul]
      change f.1 1 * h.1 g = f.1 1 * h.1 g
      rfl

theorem coordinateRid_map_id_counit_apply
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (g : G) :
    ((Algebra.TensorProduct.rid C C r.coordinateAlgebra)
        (Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra)
          r.coordinateCounit t)).1 g =
      r.coordinateTensorEval t (g, 1) := by
  let F := Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra)
    r.coordinateCounit
  let ρ := Algebra.TensorProduct.rid C C r.coordinateAlgebra
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have hρ : ρ 0 = 0 := ρ.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change (ρ (F 0)).1 g = r.coordinateTensorEval 0 (g, 1)
      rw [hF, hρ, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have hρ : ρ (F a + F b) = ρ (F a) + ρ (F b) := ρ.map_add _ _
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change (ρ (F (a + b))).1 g = r.coordinateTensorEval (a + b) (g, 1)
      rw [hF, hρ, heval]
      change (ρ (F a)).1 g + (ρ (F b)).1 g =
        r.coordinateTensorEval a (g, 1) + r.coordinateTensorEval b (g, 1)
      rw [ha, hb]
  | tmul f h =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
        r.coordinateTensorEval_tmul]
      change h.1 1 * f.1 g = f.1 g * h.1 1
      exact mul_comm _ _

/-- The coordinate operations satisfy the bialgebra laws. -/
noncomputable instance coordinateBialgebra : Bialgebra C r.coordinateAlgebra :=
  Bialgebra.ofAlgHom r.coordinateComul r.coordinateCounit
    (by
      ext f
      apply r.coordinateTripleEval_injective
      ext z
      rcases z with ⟨x, y, z⟩
      change r.coordinateTripleEval
          ((Algebra.TensorProduct.assoc C C C _ _ _)
            (Algebra.TensorProduct.map r.coordinateComul
              (AlgHom.id C r.coordinateAlgebra) (r.coordinateComul f)))
          (x, (y, z)) =
        r.coordinateTripleEval
          (Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra)
            r.coordinateComul (r.coordinateComul f)) (x, (y, z))
      rw [r.coordinateTripleEval_map_comul_id,
        r.coordinateTripleEval_map_id_comul,
        r.coordinateTensorEval_coordinateComul,
        r.coordinateTensorEval_coordinateComul]
      rw [mul_assoc])
    (by
      ext f
      apply (Algebra.TensorProduct.lid C r.coordinateAlgebra).injective
      change
        (Algebra.TensorProduct.lid C r.coordinateAlgebra)
            (Algebra.TensorProduct.map r.coordinateCounit
              (AlgHom.id C r.coordinateAlgebra) (r.coordinateComul f)) =
          (Algebra.TensorProduct.lid C r.coordinateAlgebra)
            ((Algebra.TensorProduct.lid C r.coordinateAlgebra).symm f)
      rw [(Algebra.TensorProduct.lid C r.coordinateAlgebra).apply_symm_apply]
      apply Subtype.ext
      funext g
      rw [r.coordinateLid_map_counit_id_apply,
        r.coordinateTensorEval_coordinateComul]
      simp)
    (by
      ext f
      apply (Algebra.TensorProduct.rid C C r.coordinateAlgebra).injective
      change
        (Algebra.TensorProduct.rid C C r.coordinateAlgebra)
            (Algebra.TensorProduct.map (AlgHom.id C r.coordinateAlgebra)
              r.coordinateCounit (r.coordinateComul f)) =
          (Algebra.TensorProduct.rid C C r.coordinateAlgebra)
            ((Algebra.TensorProduct.rid C C r.coordinateAlgebra).symm f)
      rw [(Algebra.TensorProduct.rid C C r.coordinateAlgebra).apply_symm_apply]
      apply Subtype.ext
      funext g
      rw [r.coordinateRid_map_id_counit_apply,
        r.coordinateTensorEval_coordinateComul]
      simp)

@[simp] theorem coordinateComulAlgHom_eq :
    Bialgebra.comulAlgHom C r.coordinateAlgebra = r.coordinateComul :=
  rfl

@[simp] theorem coordinateCounitAlgHom_eq :
    Bialgebra.counitAlgHom C r.coordinateAlgebra = r.coordinateCounit :=
  rfl

theorem coordinateLift_antipode_id_apply
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (g : G) :
    (Algebra.TensorProduct.lift r.coordinateAntipode
        (AlgHom.id C r.coordinateAlgebra) (fun _ _ => Commute.all _ _) t).1 g =
      r.coordinateTensorEval t (g⁻¹, g) := by
  let F := Algebra.TensorProduct.lift r.coordinateAntipode
    (AlgHom.id C r.coordinateAlgebra) (fun _ _ => Commute.all _ _)
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change (F 0).1 g = r.coordinateTensorEval 0 (g⁻¹, g)
      rw [hF, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change (F (a + b)).1 g = r.coordinateTensorEval (a + b) (g⁻¹, g)
      rw [hF, heval]
      change (F a).1 g + (F b).1 g =
        r.coordinateTensorEval a (g⁻¹, g) + r.coordinateTensorEval b (g⁻¹, g)
      rw [ha, hb]
  | tmul f h =>
      rw [Algebra.TensorProduct.lift_tmul, r.coordinateTensorEval_tmul]
      change f.1 g⁻¹ * h.1 g = f.1 g⁻¹ * h.1 g
      rfl

theorem coordinateLift_id_antipode_apply
    (t : r.coordinateAlgebra ⊗[C] r.coordinateAlgebra) (g : G) :
    (Algebra.TensorProduct.lift (AlgHom.id C r.coordinateAlgebra)
        r.coordinateAntipode (fun _ _ => Commute.all _ _) t).1 g =
      r.coordinateTensorEval t (g, g⁻¹) := by
  let F := Algebra.TensorProduct.lift (AlgHom.id C r.coordinateAlgebra)
    r.coordinateAntipode (fun _ _ => Commute.all _ _)
  induction t using TensorProduct.induction_on with
  | zero =>
      have hF : F 0 = 0 := F.map_zero
      have heval : r.coordinateTensorEval 0 = 0 := r.coordinateTensorEval.map_zero
      change (F 0).1 g = r.coordinateTensorEval 0 (g, g⁻¹)
      rw [hF, heval]
      rfl
  | add a b ha hb =>
      have hF : F (a + b) = F a + F b := F.map_add a b
      have heval : r.coordinateTensorEval (a + b) =
          r.coordinateTensorEval a + r.coordinateTensorEval b := by
        exact map_add _ _ _
      change (F (a + b)).1 g = r.coordinateTensorEval (a + b) (g, g⁻¹)
      rw [hF, heval]
      change (F a).1 g + (F b).1 g =
        r.coordinateTensorEval a (g, g⁻¹) + r.coordinateTensorEval b (g, g⁻¹)
      rw [ha, hb]
  | tmul f h =>
      rw [Algebra.TensorProduct.lift_tmul, r.coordinateTensorEval_tmul]
      change f.1 g * h.1 g⁻¹ = f.1 g * h.1 g⁻¹
      rfl

/-- The coordinate antipode supplies the Hopf-algebra inverse laws. -/
noncomputable instance coordinateHopfAlgebra : HopfAlgebra C r.coordinateAlgebra :=
  HopfAlgebra.ofAlgHom r.coordinateAntipode
    (by
      rw [r.coordinateComulAlgHom_eq, r.coordinateCounitAlgHom_eq]
      ext f g
      change
        (Algebra.TensorProduct.lift r.coordinateAntipode
          (AlgHom.id C r.coordinateAlgebra) (fun _ _ => Commute.all _ _)
          (r.coordinateComul f)).1 g = f.1 1
      rw [r.coordinateLift_antipode_id_apply,
        r.coordinateTensorEval_coordinateComul]
      simp)
    (by
      rw [r.coordinateComulAlgHom_eq, r.coordinateCounitAlgHom_eq]
      ext f g
      change
        (Algebra.TensorProduct.lift (AlgHom.id C r.coordinateAlgebra)
          r.coordinateAntipode (fun _ _ => Commute.all _ _)
          (r.coordinateComul f)).1 g = f.1 1
      rw [r.coordinateLift_id_antipode_apply,
        r.coordinateTensorEval_coordinateComul]
      simp)

end DifferentialMatrixGroupRepresentation

end

end GaloisForLFunctions.HTGeometry
