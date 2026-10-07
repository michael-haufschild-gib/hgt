import GaloisForLFunctions.Bottcher.WindDynamics

/-!
# Normalized winding as an actual fundamental-group homomorphism

This packages the existing exponential-cover degree and transported-loop
winding, keeping the same integer invariant and basepoint normalization.
-/

open Topology Pi1CMinusZero

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def puncturedPlaneDegreeHom : FundamentalGroup Cs one_cs →* Multiplicative ℤ where
  toFun q := Multiplicative.ofAdd (degZ q)
  map_one' := by
    change degZ (Path.Homotopic.Quotient.refl one_cs) = 0
    exact degZ_refl
  map_mul' p q := by
    change degZ (q.trans p) = degZ p + degZ q
    rw [degZ_trans, add_comm]

def normalizedWindingHom {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) (x : X) : FundamentalGroup X x →* Multiplicative ℤ :=
  puncturedPlaneDegreeHom.comp
    (FundamentalGroup.mapOfEq (Bottcher.normalizeToOne g x) (Bottcher.normalizeToOne_base g x))

theorem normalizedWindingHom_mk {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {x : X} (p : Path x x) :
    normalizedWindingHom g x (FundamentalGroup.fromPath ⟦p⟧) =
      Multiplicative.ofAdd (Bottcher.wind (fun z => (g z : ℂ))
        (continuous_subtype_val.comp g.continuous) (fun z => (g z).2) p) := by
  change Multiplicative.ofAdd (degZ
    (FundamentalGroup.mapOfEq (Bottcher.normalizeToOne g x)
      (Bottcher.normalizeToOne_base g x) (FundamentalGroup.fromPath ⟦p⟧))) = _
  rw [FundamentalGroup.mapOfEq_apply]
  change Multiplicative.ofAdd (degZ
    (((Path.Homotopic.Quotient.mk p).map (Bottcher.normalizeToOne g x)).cast _ _)) = _
  rw [← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, Bottcher.normalizeToOne_path_eq_transLoop]
  rfl

/-- Winding commutes with an actual pointed continuous map. -/
theorem normalizedWindingHom_comp_mapOfEq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(Y, Cs)) (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) :
    (normalizedWindingHom g y).comp (FundamentalGroup.mapOfEq f h) =
      normalizedWindingHom (g.comp f) x := by
  subst y
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    change normalizedWindingHom g (f x)
      (FundamentalGroup.mapOfEq f rfl (FundamentalGroup.fromPath ⟦p⟧)) = _
    rw [FundamentalGroup.mapOfEq_apply]
    change normalizedWindingHom g (f x)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.map f.continuous))) = _
    exact (normalizedWindingHom_mk g (p.map f.continuous)).trans
      (normalizedWindingHom_mk (g.comp f) p).symm

end

end GaloisForLFunctions.HTGeometry
