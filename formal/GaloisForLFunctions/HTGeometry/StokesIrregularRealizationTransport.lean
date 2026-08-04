import GaloisForLFunctions.HTGeometry.StokesCellularCategory

open CategoryTheory

namespace GaloisForLFunctions.IrregularStokes.CellularStokesCategory

noncomputable section

open CellularMicrolocal

/-- Linear equivalence underlying an isomorphism of module objects. -/
def moduleLinearEquivOfIso {R : Type*} [Ring R] {X Y : ModuleCat R} (e : X ≅ Y) :
    X ≃ₗ[R] Y :=
  { e.hom.hom with
    invFun := e.inv.hom
    left_inv := e.hom_inv_id_apply
    right_inv := e.inv_hom_id_apply }

variable {C : Type*} [Category C]

/-- The transported arc-to-nearby-to-vanishing sequence is exact for every realization functor;
no exactness hypothesis is needed beyond the quotient construction in the target. -/
theorem realizationTransport_exact (Phi : C ⥤ GermCategory) (A : C)
    (s : ConormalSide) :
    Function.Exact (sideMap (Phi.obj A) s).hom
        (nearbyToVanishing (Phi.obj A) s) ∧
      Function.Surjective (nearbyToVanishing (Phi.obj A) s) :=
  ⟨arc_wall_vanishing_exact (Phi.obj A) s,
    nearbyToVanishing_surjective (Phi.obj A) s⟩

/-- If a realized object is an exponential germ, exactly one transported conormal carries its
full coefficient rank. -/
theorem realizationTransport_exponential (Phi : C ⥤ GermCategory) (A : C)
    {d : ℕ} (hd : 0 < d) (active : Bool)
    (hA : Phi.obj A = exponentialGerm d active) :
    (Module.finrank ℚ (microstalkSpace (Phi.obj A) .left) = d ∧
        Module.finrank ℚ (microstalkSpace (Phi.obj A) .right) = 0) ∨
      (Module.finrank ℚ (microstalkSpace (Phi.obj A) .left) = 0 ∧
        Module.finrank ℚ (microstalkSpace (Phi.obj A) .right) = d) := by
  rw [hA]
  exact exponentialGerm_exactly_one_vanishing hd active

/-- Naturally isomorphic realization functors induce canonically isomorphic quotient
microstalks. -/
def realizationTransportMicrostalkIso {Phi Psi : C ⥤ GermCategory}
    (eta : Phi ≅ Psi) (A : C) (s : ConormalSide) :
    (microstalkFunctor s).obj (Phi.obj A) ≅
      (microstalkFunctor s).obj (Psi.obj A) :=
  (microstalkFunctor s).mapIso (eta.app A)

/-- In particular, every characteristic-cycle coefficient defined as microstalk dimension is
independent of a naturally isomorphic realization. -/
theorem realizationTransport_finrank_invariant {Phi Psi : C ⥤ GermCategory}
    (eta : Phi ≅ Psi) (A : C) (s : ConormalSide) :
    Module.finrank ℚ (microstalkSpace (Phi.obj A) s) =
      Module.finrank ℚ (microstalkSpace (Psi.obj A) s) := by
  let e := realizationTransportMicrostalkIso eta A s
  exact (moduleLinearEquivOfIso e).finrank_eq

end

end GaloisForLFunctions.IrregularStokes.CellularStokesCategory
