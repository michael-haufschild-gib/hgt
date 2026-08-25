import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldGalois
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicGaloisH2InvariantOverBase

/-!
# Root-lift model of residue-exhausting maximal subfields

Every residue-exhausting maximal subfield of a local central division algebra is identified with
a concrete finite unramified Hensel root lift of the same degree. This exposes the equivalence
constructed internally in the cyclicity proof so finite `ZMod n` invariants can be transported to
the cyclic slices that exhaust the local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued WithZero WithZeroMulInt

variable {F A : Type} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

set_option maxHeartbeats 800000 in
/-- A residue-exhausting maximal subfield is an unramified root-lift field of the same degree. -/
theorem divisionAlgebraResidueExhaustingMaximalSubfield_exists_unramifiedRootLiftAlgEquiv
    (T : Subalgebra F A) (hT : IsField T)
    (hdegree : Module.finrank F T = divisionAlgebraDegree (F := F) (A := A))
    (hres :
      letI : NormedDivisionRing A :=
        divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
      letI : NontriviallyNormedField T :=
        divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
          (F := F) (A := A) T hT
      letI : NormedSpace F T :=
        divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
      letI : IsUltrametricDist T :=
        divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
      NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
        DivisionAlgebraDeterminantResidue (F := F) (A := A)) :
    letI : NormedDivisionRing A :=
      divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
    letI : NontriviallyNormedField T :=
      divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
        (F := F) (A := A) T hT
    letI : NormedSpace F T :=
      divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
    letI : CompleteSpace T :=
      divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := A) T hT
    letI : IsUltrametricDist T :=
      divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
    letI : ProperSpace T :=
      divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
      change (NormedField.valuation (K := F)).IsNontrivial
      exact Valuation.RankOne.toIsNontrivial
    letI : IsNonarchimedeanLocalField F :=
      isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
    ∃ D : NonarchimedeanFiniteUnramifiedRootLift F,
      D.polynomial.natDegree = Module.finrank F T ∧
      let B := AdjoinRoot D.polynomial
      let U := FractionRing B
      letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain F
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
      letI : Algebra F U := by
        let g₀ : (ValuativeRel.valuation F).integer →+* U :=
          (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
        have hg₀ : Function.Injective g₀ :=
          (IsFractionRing.injective B U).comp
            (AdjoinRoot.of.injective_of_degree_ne_zero
              (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F
                D.polynomial D.monic D.residuePolynomial D.reduction_eq
                  D.residueIrreducible))
        exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
      Nonempty (U ≃ₐ[F] T) ∧
        Nonempty (cyclicGaloisH2 F T ≃+ ZMod D.polynomial.natDegree) := by
  letI : NormedDivisionRing A :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := A)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := A) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := A) T hT
  letI : CompleteSpace T :=
    divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := A) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist (F := F) (A := A) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  letI : ValuativeRel T := .ofValuation (NormedField.valuation (K := T))
  letI : IsNonarchimedeanLocalField T :=
    divisionAlgebraRestrictedRootDeterminant_isNonarchimedeanLocalField
      (F := F) (A := A) T hT
  letI : IsGalois F T :=
    divisionAlgebraResidueExhaustingMaximalSubfield_isGalois
      (F := F) (A := A) T hT hdegree hres
  let n := divisionAlgebraDegree (F := F) (A := A)
  letI : NeZero n := ⟨(divisionAlgebraDegree_pos (F := F) (A := A)).ne'⟩
  obtain ⟨g, hgmonic, hg, hgdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_irreducible_residuePolynomial_of_natDegree F n
  obtain ⟨f, hf, hfg, hfdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_residuePolynomial_lift F g hgmonic
  let D : NonarchimedeanFiniteUnramifiedRootLift F := {
    polynomial := f
    residuePolynomial := g
    monic := hf
    residueMonic := hgmonic
    reduction_eq := hfg
    residueIrreducible := hg }
  let kF := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer
  let kT := IsLocalRing.ResidueField (ValuativeRel.valuation T).integer
  have hkTdegree : Module.finrank kF kT = n :=
    divisionAlgebraRestrictedIntrinsicResidue_finrank_eq_degree
      (F := F) (A := A) T hT hres
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite kF (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Fact (ringChar kF).Prime :=
    ⟨CharP.char_is_prime kF (ringChar kF)⟩
  have hrootDegree : Module.finrank kF (AdjoinRoot g) = n := by
    rw [(AdjoinRoot.isAdjoinRootMonic g hgmonic).finrank, hgdegree]
  let eRoot := FiniteField.algEquivExtension kF (ringChar kF) n
    (AdjoinRoot g) hrootDegree
  let eT := FiniteField.algEquivExtension kF (ringChar kF) n kT hkTdegree
  let e : AdjoinRoot g ≃ₐ[kF] kT := eRoot.trans eT.symm
  let a₀ : kT := e (AdjoinRoot.root g)
  have hrootg : Polynomial.aeval a₀ g = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero g e.toAlgHom
  letI : Algebra kT kT := Algebra.id kT
  let p : Polynomial (ValuativeRel.valuation T).integer :=
    f.map (algebraMap (ValuativeRel.valuation F).integer
      (ValuativeRel.valuation T).integer)
  have hp : p.Monic := hf.map _
  have hcoeff : (IsLocalRing.residue (ValuativeRel.valuation T).integer).comp
      (algebraMap (ValuativeRel.valuation F).integer
        (ValuativeRel.valuation T).integer) =
      (algebraMap kF kT).comp
        (IsLocalRing.residue (ValuativeRel.valuation F).integer) := by
    ext c
    exact (IsLocalRing.ResidueField.algebraMap_residue c).symm
  have hreduce : p.map (IsLocalRing.residue (ValuativeRel.valuation T).integer) =
      g.map (algebraMap kF kT) := by
    calc
      p.map (IsLocalRing.residue (ValuativeRel.valuation T).integer) =
          f.map ((IsLocalRing.residue (ValuativeRel.valuation T).integer).comp
            (algebraMap (ValuativeRel.valuation F).integer
              (ValuativeRel.valuation T).integer)) := by
        simp only [p, Polynomial.map_map]
      _ = f.map ((algebraMap kF kT).comp
          (IsLocalRing.residue (ValuativeRel.valuation F).integer)) := by rw [hcoeff]
      _ = (f.map (IsLocalRing.residue (ValuativeRel.valuation F).integer)).map
          (algebraMap kF kT) := by rw [Polynomial.map_map]
      _ = g.map (algebraMap kF kT) := by
        change (f.map (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer))).map _ = _
        exact congrArg (fun q ↦ q.map (algebraMap kF kT)) hfg
  have hrootpMapped :
      (p.map (IsLocalRing.residue (ValuativeRel.valuation T).integer)).eval a₀ = 0 := by
    rw [hreduce]
    change (g.map (algebraMap kF kT)).eval a₀ = 0
    rw [Polynomial.eval_map]
    exact hrootg
  have hrootp : Polynomial.aeval a₀ p = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      IsLocalRing.ResidueField.algebraMap_eq]
    exact hrootpMapped
  letI : PerfectField kF := inferInstance
  have hgsep : g.Separable := PerfectField.separable_of_irreducible hg
  have hsepp : (p.map
      (IsLocalRing.residue (ValuativeRel.valuation T).integer)).Separable := by
    rw [hreduce]
    exact (Polynomial.separable_map _).mpr hgsep
  have hsimplep : Polynomial.aeval a₀ p.derivative ≠ 0 := by
    have hs : (p.map (IsLocalRing.residue
        (ValuativeRel.valuation T).integer)).derivative.eval a₀ ≠ 0 := by
      apply hsepp.eval₂_derivative_ne_zero (RingHom.id kT)
      simpa only [Polynomial.eval₂_id] using hrootpMapped
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      IsLocalRing.ResidueField.algebraMap_eq]
    simpa only [Polynomial.derivative_map] using hs
  obtain ⟨a, ha, _⟩ :=
    nonarchimedeanLocalField_hensel_lift_residue_root T p hp a₀ hrootp hsimplep
  let q : Polynomial F :=
    f.map (algebraMap (ValuativeRel.valuation F).integer F)
  let α : T := (a : T)
  have hcomm : (algebraMap F T).comp
      (algebraMap (ValuativeRel.valuation F).integer F) =
      (algebraMap (ValuativeRel.valuation T).integer T).comp
        (algebraMap (ValuativeRel.valuation F).integer
          (ValuativeRel.valuation T).integer) := by
    ext c
    rfl
  have hpolyMap : q.map (algebraMap F T) =
      p.map (algebraMap (ValuativeRel.valuation T).integer T) := by
    calc
      q.map (algebraMap F T) = f.map ((algebraMap F T).comp
          (algebraMap (ValuativeRel.valuation F).integer F)) := by
        simp only [q, Polynomial.map_map]
      _ = f.map ((algebraMap (ValuativeRel.valuation T).integer T).comp
          (algebraMap (ValuativeRel.valuation F).integer
            (ValuativeRel.valuation T).integer)) := by rw [hcomm]
      _ = p.map (algebraMap (ValuativeRel.valuation T).integer T) := by
        simp only [p, Polynomial.map_map]
  have hrootq : Polynomial.aeval α q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hpolyMap]
    have hamap := ha.map (f := algebraMap (ValuativeRel.valuation T).integer T)
    change (p.map (algebraMap (ValuativeRel.valuation T).integer T)).eval
      (algebraMap (ValuativeRel.valuation T).integer T a) = 0 at hamap
    have hcoe : algebraMap (ValuativeRel.valuation T).integer T a = (a : T) := rfl
    rw [hcoe] at hamap
    exact hamap
  have hqmonic : q.Monic := hf.map _
  have hqdegree : q.natDegree = f.natDegree := hf.natDegree_map _
  have hqirr : Irreducible q :=
    nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible
      F f hf g hfg hg
  have hmin : minpoly F α = q :=
    (minpoly.eq_of_irreducible_of_monic hqirr hrootq hqmonic).symm
  letI : Algebra.IsIntegral F T := Algebra.IsIntegral.of_finite F T
  let ST : IntermediateField F T := IntermediateField.adjoin F {α}
  have hSTfinrank : Module.finrank F ST = q.natDegree := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin]
  have hgenT : ST = ⊤ := by
    rw [eq_top_iff]
    intro z _
    change z ∈ ST.toSubmodule
    have htop : ST.toSubmodule = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      change Module.finrank F ST = Module.finrank F T
      rw [hSTfinrank, hdegree]
      exact hqdegree.trans (hfdegree.trans (hgdegree.trans rfl))
    rw [htop]
    exact Submodule.mem_top
  have hsplitT : (q.map (algebraMap F T)).Splits := by
    rw [← hmin]
    exact Normal.splits' α
  letI : Polynomial.IsSplittingField F T q := by
    apply isSplittingField_iff_intermediateField.mpr
    refine ⟨hsplitT, ?_⟩
    apply top_unique
    rw [← hgenT]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    apply IntermediateField.subset_adjoin
    apply Polynomial.mem_rootSet'.mpr
    exact ⟨(hqmonic.map _).ne_zero, hrootq⟩
  let B := AdjoinRoot f
  let U := FractionRing B
  letI : IsDomain B :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain F f hf g hfg hg
  letI : IsLocalRing B :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing F f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation F).integer B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom F f hf g hfg hg
  letI : FaithfulSMul (ValuativeRel.valuation F).integer B := by
    refine (faithfulSMul_iff_algebraMap_injective
      (ValuativeRel.valuation F).integer B).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F f hf g hfg hg)
  letI : FaithfulSMul (ValuativeRel.valuation F).integer U := by
    refine (faithfulSMul_iff_algebraMap_injective
      (ValuativeRel.valuation F).integer U).mpr ?_
    change Function.Injective <|
      (algebraMap B U).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F f hf g hfg hg))
  letI : Algebra (FractionRing (ValuativeRel.valuation F).integer) U :=
    FractionRing.liftAlgebra (ValuativeRel.valuation F).integer U
  let g₀ : (ValuativeRel.valuation F).integer →+* U :=
    (algebraMap B U).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F f hf g hfg hg))
  letI : Algebra F U := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  let β : U := algebraMap B U (AdjoinRoot.root f)
  have hcommU : (algebraMap F U).comp
      (algebraMap (ValuativeRel.valuation F).integer F) =
      (algebraMap B U).comp
        (algebraMap (ValuativeRel.valuation F).integer B) := by
    ext r
    change IsFractionRing.lift hg₀
      (algebraMap (ValuativeRel.valuation F).integer F r) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hmapU : q.map (algebraMap F U) =
      (f.map (algebraMap (ValuativeRel.valuation F).integer B)).map
        (algebraMap B U) := by
    calc
      q.map (algebraMap F U) =
          f.map ((algebraMap F U).comp
            (algebraMap (ValuativeRel.valuation F).integer F)) := by
        simp only [q, Polynomial.map_map]
      _ = f.map ((algebraMap B U).comp
          (algebraMap (ValuativeRel.valuation F).integer B)) := by rw [hcommU]
      _ = (f.map (algebraMap (ValuativeRel.valuation F).integer B)).map
          (algebraMap B U) := by
        simp only [Polynomial.map_map]
  have hpolyEvalU (r : Polynomial (ValuativeRel.valuation F).integer) :
      algebraMap B U (AdjoinRoot.mk f r) =
        Polynomial.aeval β
          (r.map (algebraMap (ValuativeRel.valuation F).integer F)) := by
    rw [← AdjoinRoot.aeval_eq r]
    exact Polynomial.map_aeval_eq_aeval_map hcommU r (AdjoinRoot.root f)
  have hrootU : Polynomial.aeval β q = 0 := by
    rw [← hpolyEvalU f]
    simp
  have hminU : minpoly F β = q :=
    (minpoly.eq_of_irreducible_of_monic hqirr hrootU hqmonic).symm
  letI : FiniteDimensional F U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase
      F f hf g hfg hg
  letI : Algebra.IsIntegral F U := Algebra.IsIntegral.of_finite F U
  let SU : IntermediateField F U := IntermediateField.adjoin F {β}
  have hSUfinrank : Module.finrank F SU = q.natDegree := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β), hminU]
  have hUfinrank : Module.finrank F U = f.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase F f hf g hfg hg
  have hgenU : SU = ⊤ := by
    rw [eq_top_iff]
    intro z _
    change z ∈ SU.toSubmodule
    have htop : SU.toSubmodule = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      change Module.finrank F SU = Module.finrank F U
      rw [hSUfinrank, hqdegree, hUfinrank]
    rw [htop]
    exact Submodule.mem_top
  letI : Normal F U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_normal
      F f hf g hgmonic hfg hg
  have hsplitU : (q.map (algebraMap F U)).Splits := by
    rw [← hminU]
    exact Normal.splits' β
  letI : Polynomial.IsSplittingField F U q := by
    apply isSplittingField_iff_intermediateField.mpr
    refine ⟨hsplitU, ?_⟩
    apply top_unique
    rw [← hgenU]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    apply IntermediateField.subset_adjoin
    apply Polynomial.mem_rootSet'.mpr
    exact ⟨(hqmonic.map _).ne_zero, hrootU⟩
  let eUT : U ≃ₐ[F] T :=
    (Polynomial.IsSplittingField.algEquiv U q).trans
      (Polynomial.IsSplittingField.algEquiv T q).symm
  letI : IsGalois F U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois
      F f hf g hgmonic hfg hg
  letI : IsCyclic Gal(U / F) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base
      F f hf g hgmonic hfg hg
  letI : IsCyclic Gal(T / F) :=
    divisionAlgebraResidueExhaustingMaximalSubfield_isCyclic
      (F := F) (A := A) T hT hdegree hres
  let hInv : cyclicGaloisH2 F T ≃+ ZMod f.natDegree :=
    (cyclicGaloisH2AddEquivOfAlgEquiv F U T eUT).symm.trans
      (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase
        F f hf g hgmonic hfg hg)
  refine ⟨D, ?_, ⟨⟨eUT⟩, ?_⟩⟩
  · dsimp only [D]
    exact hfdegree.trans (hgdegree.trans hdegree.symm)
  · dsimp only [D]
    exact ⟨hInv⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
