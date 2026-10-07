import GaloisForLFunctions.HTGeometry.NormalizedWindingHom
import GaloisForLFunctions.HTGeometry.PointedPacketTransport

open Topology Pi1CMinusZero

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A homeomorphism induces a bijection on the actual pointed loop groups. -/
theorem fundamentalGroup_mapOfEq_bijective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) {y : Y}
    (hy : e x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ (x := x) hy) := by
  subst y
  let f := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ (x := x) rfl
  let h : e.symm (e x) = x := e.symm_apply_apply x
  let g := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ h
  have hleft : Function.LeftInverse g f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      change FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ h
        (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ rfl (FundamentalGroup.fromPath ⟦p⟧)) = _
      simp only [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.mk
        (((p.map e.continuous).map e.symm.continuous).cast h.symm h.symm) =
          Path.Homotopic.Quotient.mk p
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact e.symm_apply_apply (p t)
  have hright : Function.RightInverse g f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p =>
      change FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ rfl
        (FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ h (FundamentalGroup.fromPath ⟦p⟧)) = _
      simp only [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.mk
        (((p.map e.symm.continuous).cast h.symm h.symm).map e.continuous) =
          Path.Homotopic.Quotient.mk p
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      exact e.apply_symm_apply (p t)
  exact ⟨hleft.injective, hright.surjective⟩

def puncturedNormalization (b : Cs) : Cs ≃ₜ Cs where
  toFun z := ⟨(z : ℂ) / b, div_ne_zero z.2 b.2⟩
  invFun z := ⟨(b : ℂ) * z, mul_ne_zero b.2 z.2⟩
  left_inv z := by apply Subtype.ext; exact mul_div_cancel₀ _ b.2
  right_inv z := by apply Subtype.ext; simp [b.2]
  continuous_toFun := (continuous_subtype_val.div_const _).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- Normalization preserves every loop class; zero winding is a complete invariant in C*. -/
theorem punctured_normalizedWinding_bijective (b : Cs) :
    Function.Bijective (normalizedWindingHom (ContinuousMap.id Cs) b) := by
  have hn : puncturedNormalization b b = one_cs := by
    apply Subtype.ext
    exact div_self b.2
  have hf := fundamentalGroup_mapOfEq_bijective (puncturedNormalization b) b hn
  have hmap : Function.Bijective
      (FundamentalGroup.mapOfEq (Bottcher.normalizeToOne (ContinuousMap.id Cs) b)
        (Bottcher.normalizeToOne_base (ContinuousMap.id Cs) b)) := by
    convert hf using 1
    congr 2
  exact ⟨fun p q hpq => hmap.1 (degZ_injective (congrArg Multiplicative.toAdd hpq)),
    fun k => by
      obtain ⟨q, hq⟩ := degZ_surjective k.toAdd
      obtain ⟨p, hp⟩ := hmap.2 q
      refine ⟨p, ?_⟩
      change Multiplicative.ofAdd (degZ
        (FundamentalGroup.mapOfEq (Bottcher.normalizeToOne (ContinuousMap.id Cs) b)
          (Bottcher.normalizeToOne_base (ContinuousMap.id Cs) b) p)) = k
      rw [hp, hq]
      rfl⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- Factor normalized winding through the actual map to the punctured plane. -/
theorem normalizedWindingHom_map {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) (x : X) (q : FundamentalGroup X x) :
    normalizedWindingHom (ContinuousMap.id Cs) (g x) (FundamentalGroup.map g x q) =
      normalizedWindingHom g x q := by
  have h := congrArg (fun f : FundamentalGroup X x →* Multiplicative ℤ => f q)
    (normalizedWindingHom_comp_mapOfEq (ContinuousMap.id Cs) g rfl)
  change normalizedWindingHom (ContinuousMap.id Cs) (g x)
    (Path.Homotopic.Quotient.map q g) = normalizedWindingHom g x q
  simpa only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, ContinuousMap.id_comp] using h

/-- Surjectivity of winding is exactly surjectivity of the actual punctured-plane map. -/
theorem normalizedWindingHom_surjective_iff {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) (x : X) :
    Function.Surjective (normalizedWindingHom g x) ↔
      Function.Surjective (FundamentalGroup.map g x) := by
  constructor
  · intro h q
    obtain ⟨p, hp⟩ := h (normalizedWindingHom (ContinuousMap.id Cs) (g x) q)
    refine ⟨p, (punctured_normalizedWinding_bijective (g x)).1 ?_⟩
    rw [normalizedWindingHom_map, hp]
  · intro h k
    obtain ⟨q, hq⟩ := (punctured_normalizedWinding_bijective (g x)).2 k
    obtain ⟨p, hp⟩ := h q
    exact ⟨p, by rw [← normalizedWindingHom_map, hp, hq]⟩

/-- A winding-one loop at any basepoint supplies winding one at every joined basepoint. -/
theorem normalizedWindingHom_surjective_of_one {X : Type*} [TopologicalSpace X]
    (g : C(X, Cs)) {s x : X} (α : Path s x)
    (p : FundamentalGroup X s)
    (hp : normalizedWindingHom g s p = Multiplicative.ofAdd 1) :
    Function.Surjective (normalizedWindingHom g x) := by
  have hs : Function.Surjective (normalizedWindingHom g s) := by
    intro k
    refine ⟨p ^ k.toAdd, ?_⟩
    rw [map_zpow, hp]
    change k.toAdd • (1 : ℤ) = k.toAdd
    simp
  have hs' := (normalizedWindingHom_surjective_iff g s).mp hs
  apply (normalizedWindingHom_surjective_iff g x).mpr
  intro q
  let β := α.map g.continuous
  obtain ⟨r, hr⟩ := hs' ((FundamentalGroup.fundamentalGroupMulEquivOfPath β).symm q)
  refine ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath α r, ?_⟩
  rw [fundamentalGroup_map_transport, hr]
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPath β).apply_symm_apply q

end GaloisForLFunctions.HTGeometry
