import GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol
import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Algebraic independence detected by ambient Kähler differentials

Over a characteristic-zero base field, a family in an arbitrary ambient field extension is
algebraically independent exactly when its universal Kähler differentials are linearly
independent over the ambient field.  The forward direction extends the family to a transcendence
basis, base-changes its canonical differential basis, and uses formal étaleness of the remaining
algebraic extension.  The reverse direction uses the nonzero gradient circuit of a minimal
polynomial relation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set IntermediateField

/-- Algebraic independence over a characteristic-zero field is equivalent to linear independence
of the corresponding universal differentials in the full ambient extension. -/
theorem algebraicIndependent_iff_kaehlerD_linearIndependent
    {I K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (x : I → L) :
    AlgebraicIndependent K x ↔
      LinearIndependent L (fun i : I ↦ KaehlerDifferential.D K L (x i)) := by
  constructor
  · intro hx
    classical
    have hI : (AlgebraicIndependent.matroid K L).Indep (Set.range x) :=
      AlgebraicIndependent.matroid_indep_iff.mpr hx.to_subtype_range
    obtain ⟨B, hBbase, hxB⟩ := hI.exists_isBase_superset
    have hB : IsTranscendenceBasis K ((↑) : B → L) :=
      AlgebraicIndependent.matroid_isBase_iff.mp hBbase
    let F := IntermediateField.adjoin K (Set.range ((↑) : B → L))
    letI : Algebra.IsAlgebraic F L := hB.isAlgebraic_field
    letI : Algebra.IsIntegral F L := Algebra.IsAlgebraic.isIntegral
    letI : Algebra.IsSeparable F L := by infer_instance
    letI : Algebra.FormallyEtale F L :=
      Algebra.FormallyEtale.of_isSeparable F L
    let bF : Basis B F Ω[F⁄K] :=
      kaehlerD_adjoin_coordinates_basis hB.1
    let bT : Basis B L (TensorProduct F L (KaehlerDifferential K F)) :=
      bF.baseChange L
    let bL : Basis B L Ω[L⁄K] :=
      bT.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F L)
    have hbL (b : B) : bL b = KaehlerDifferential.D K L b.1 := by
      simp only [bL, Basis.map_apply, bT, Basis.baseChange_apply, bF]
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul, one_smul,
        kaehlerD_adjoin_coordinates_basis_apply,
        KaehlerDifferential.map_D]
      rfl
    let e : I → B := fun i ↦ ⟨x i, hxB ⟨i, rfl⟩⟩
    have he : Function.Injective e := by
      intro i j hij
      apply hx.injective
      exact congrArg Subtype.val hij
    have hsub := bL.linearIndependent.comp e he
    change LinearIndependent L (fun i : I ↦ bL (e i)) at hsub
    simpa [e, hbL] using hsub
  · intro hdx
    by_contra hdep
    obtain ⟨c, hc, hrel⟩ :=
      GaloisForLFunctions.exists_nonzero_kaehler_relation_of_not_algebraicIndependent x hdep
    rw [linearIndependent_iff] at hdx
    exact hc (hdx c hrel)

end

end GaloisForLFunctions.HTGeometry
