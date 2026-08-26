import GaloisForLFunctions.HTGeometry.KaehlerAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.TorsorDecomposition

/-!
# Kähler injectivity along characteristic-zero field towers

For a characteristic-zero field tower `K → F → L`, the canonical map from
`Ω[F/K]` to `Ω[L/K]` is injective.  The proof reuses the corpus theorem detecting
algebraic independence by ambient Kähler differentials: a transcendence basis of
`F/K` gives a basis of `Ω[F/K]`, and its image remains linearly independent in
the full ambient extension `L/K`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set IntermediateField TensorProduct

/-- In characteristic zero, relative Kähler differentials of an intermediate
field inject into the absolute relative differentials of every overfield. -/
theorem kaehlerMap_injective_of_fieldTower
    {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] [CharZero K] :
    Function.Injective (KaehlerDifferential.map K K F L) := by
  classical
  obtain ⟨B, hBbase⟩ := (AlgebraicIndependent.matroid K F).exists_isBase
  have hB : IsTranscendenceBasis K ((↑) : B → F) :=
    AlgebraicIndependent.matroid_isBase_iff.mp hBbase
  let P := IntermediateField.adjoin K (Set.range ((↑) : B → F))
  letI : Algebra.IsAlgebraic P F := hB.isAlgebraic_field
  letI : Algebra.IsIntegral P F := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable P F := by infer_instance
  letI : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isSeparable P F
  let bP : Basis B P Ω[P⁄K] :=
    kaehlerD_adjoin_coordinates_basis hB.1
  let bT : Basis B F (TensorProduct P F (KaehlerDifferential K P)) :=
    bP.baseChange F
  let bF : Basis B F Ω[F⁄K] :=
    bT.map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K P F)
  have hbF (b : B) : bF b = KaehlerDifferential.D K F b.1 := by
    simp only [bF, Basis.map_apply, bT, Basis.baseChange_apply, bP]
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul,
      kaehlerD_adjoin_coordinates_basis_apply,
      KaehlerDifferential.map_D]
    rfl
  apply injective_of_basis_map_linearIndependent bF
    (KaehlerDifferential.map K K F L)
  let ι : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
  have hAlgL : AlgebraicIndependent K (ι ∘ ((↑) : B → F)) :=
    hB.1.map' ι.injective
  have hlinL : LinearIndependent L
      (fun b : B ↦ KaehlerDifferential.D K L (ι b.1)) :=
    (algebraicIndependent_iff_kaehlerD_linearIndependent _).mp hAlgL
  have hscalar : Function.Injective (fun r : F ↦ r • (1 : L)) := by
    simpa only [Algebra.smul_def, mul_one] using (algebraMap F L).injective
  have hlinF : LinearIndependent F
      (fun b : B ↦ KaehlerDifferential.D K L (ι b.1)) :=
    hlinL.restrict_scalars hscalar
  simpa only [hbF, KaehlerDifferential.map_D, ι,
    IsScalarTower.toAlgHom_apply] using hlinF

end

end GaloisForLFunctions.HTGeometry
