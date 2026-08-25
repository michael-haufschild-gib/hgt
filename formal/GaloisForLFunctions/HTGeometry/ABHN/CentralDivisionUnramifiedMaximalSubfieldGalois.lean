import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldLocalField
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalUnramifiedSplitting
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open Polynomial
open scoped NormedField ValuativeRel Valued

universe u

/-- The canonical unramified Hensel lift has cyclic Galois group over the original local field,
not only over the fraction field of its integer ring.  The two automorphism groups are identified
by the canonical fraction-ring equivalence of the bases. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsCyclic Gal(FractionRing (AdjoinRoot f) / K) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) :=
    RingHom.toAlgebra (IsFractionRing.lift hg₀)
  let e := FractionRing.algEquiv 𝒪[K] K
  have hforward :
      (algebraMap K (FractionRing (AdjoinRoot f))).comp e.toRingEquiv.toRingHom =
        (RingEquiv.refl (FractionRing (AdjoinRoot f))).toRingHom.comp
          (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    simp only [RingHom.comp_apply]
    change (algebraMap K (FractionRing (AdjoinRoot f)))
      (e (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [e.commutes]
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap]
    rw [IsFractionRing.lift_algebraMap]
  let baseEquiv :
      Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) ≃*
        Gal(FractionRing (AdjoinRoot f) / K) :=
    { toFun := fun σ ↦
        { σ.toRingEquiv with
          commutes' := fun x ↦ by
            have hx := DFunLike.congr_fun hforward (e.symm x)
            calc
              σ (algebraMap K (FractionRing (AdjoinRoot f)) x) =
                  σ (algebraMap (FractionRing 𝒪[K])
                    (FractionRing (AdjoinRoot f)) (e.symm x)) := by
                    simpa using congrArg σ hx
              _ = algebraMap (FractionRing 𝒪[K])
                    (FractionRing (AdjoinRoot f)) (e.symm x) := σ.commutes _
              _ = algebraMap K (FractionRing (AdjoinRoot f)) x := by
                    simpa using hx.symm }
      invFun := fun τ ↦
        { τ.toRingEquiv with
          commutes' := fun y ↦ by
            have hy := DFunLike.congr_fun hforward y
            calc
              τ (algebraMap (FractionRing 𝒪[K])
                    (FractionRing (AdjoinRoot f)) y) =
                  τ (algebraMap K (FractionRing (AdjoinRoot f)) (e y)) := by
                    simpa using congrArg τ hy.symm
              _ = algebraMap K (FractionRing (AdjoinRoot f)) (e y) := τ.commutes _
              _ = algebraMap (FractionRing 𝒪[K])
                    (FractionRing (AdjoinRoot f)) y := by simpa using hy }
      left_inv := fun σ ↦ by ext; rfl
      right_inv := fun τ ↦ by ext; rfl
      map_mul' := fun σ τ ↦ by ext; rfl }
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
      K f hf g hgmonic hfg hg
  exact isCyclic_of_surjective baseEquiv.toMonoidHom baseEquiv.surjective

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

set_option maxHeartbeats 800000 in
/-- A maximal subfield of a central division algebra that exhausts its determinant residue
field is Galois over the center.  The proof lifts a residue generator by Hensel, proves that
its lifted minimal polynomial splits, and uses the exact residue degree to show that the lift
generates the whole maximal subfield. -/
theorem divisionAlgebraResidueExhaustingMaximalSubfield_isGalois
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
    IsGalois F T := by
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
  let n := divisionAlgebraDegree (F := F) (A := A)
  letI : NeZero n := ⟨(divisionAlgebraDegree_pos (F := F) (A := A)).ne'⟩
  obtain ⟨g, hgmonic, hg, hgdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_irreducible_residuePolynomial_of_natDegree F n
  obtain ⟨f, hf, hfg, hfdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_residuePolynomial_lift F g hgmonic
  let kF := IsLocalRing.ResidueField (ValuativeRel.valuation F).integer
  let kT := IsLocalRing.ResidueField (ValuativeRel.valuation T).integer
  have hkTdegree : Module.finrank kF kT = n := by
    exact divisionAlgebraRestrictedIntrinsicResidue_finrank_eq_degree
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
  have hrootg : Polynomial.aeval a₀ g = 0 := by
    exact AdjoinRoot.aeval_algHom_eq_zero g e.toAlgHom
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
        exact congrArg (fun q => q.map (algebraMap kF kT)) hfg
  have hrootpMapped :
      (p.map (IsLocalRing.residue (ValuativeRel.valuation T).integer)).eval a₀ = 0 := by
    rw [hreduce]
    change (g.map (algebraMap kF kT)).eval a₀ = 0
    rw [Polynomial.eval_map]
    exact hrootg
  have hrootp : Polynomial.aeval a₀ p = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    rw [IsLocalRing.ResidueField.algebraMap_eq]
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
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    simpa only [Polynomial.derivative_map] using hs
  obtain ⟨a, ha, _ha₀⟩ :=
    nonarchimedeanLocalField_hensel_lift_residue_root T p hp a₀ hrootp hsimplep
  have hminres : minpoly kF a₀ = g :=
    (minpoly.eq_of_irreducible_of_monic hg hrootg hgmonic).symm
  letI : IsGalois kF kT := inferInstance
  letI : Normal kF kT := IsGalois.to_normal
  have hsplitg : (g.map (algebraMap kF kT)).Splits := by
    rw [← hminres]
    exact Normal.splits' a₀
  have hsplitp : p.Splits := by
    apply polynomial_splits_of_split_reduction_and_root_lifts
      (IsLocalRing.residue (ValuativeRel.valuation T).integer) p hp hsepp
    · rw [hreduce]
      exact hsplitg
    · intro x hx
      change (p.map (IsLocalRing.residue
        (ValuativeRel.valuation T).integer)).eval x = 0 at hx
      have hxroot : Polynomial.aeval x p = 0 := by
        rw [Polynomial.aeval_def, ← Polynomial.eval_map,
          IsLocalRing.ResidueField.algebraMap_eq]
        exact hx
      have hxsimple : Polynomial.aeval x p.derivative ≠ 0 := by
        have hs : (p.map (IsLocalRing.residue
            (ValuativeRel.valuation T).integer)).derivative.eval x ≠ 0 := by
          apply hsepp.eval₂_derivative_ne_zero (RingHom.id kT)
          simpa only [Polynomial.eval₂_id] using hx
        rw [Polynomial.aeval_def, ← Polynomial.eval_map,
          IsLocalRing.ResidueField.algebraMap_eq]
        simpa only [Polynomial.derivative_map] using hs
      exact nonarchimedeanLocalField_hensel_lift_residue_root
        T p hp x hxroot hxsimple
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
  have hsplitq : (q.map (algebraMap F T)).Splits := by
    rw [hpolyMap]
    exact hsplitp.map _
  have hqmonic : q.Monic := hf.map _
  have hqdegree : q.natDegree = f.natDegree := hf.natDegree_map _
  have hqirr : Irreducible q :=
    nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible
      F f hf g hfg hg
  have hqsep : q.Separable :=
    nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_separable
      F f hf g hfg hg
  have hmin : minpoly F α = q :=
    (minpoly.eq_of_irreducible_of_monic hqirr hrootq hqmonic).symm
  letI : Algebra.IsIntegral F T := Algebra.IsIntegral.of_finite F T
  let S : IntermediateField F T := IntermediateField.adjoin F {α}
  have hSfinrank : Module.finrank F S = q.natDegree := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α), hmin]
  have hgen : S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    change z ∈ S.toSubmodule
    have hStop : S.toSubmodule = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      change Module.finrank F S = Module.finrank F T
      rw [hSfinrank, hdegree]
      exact hqdegree.trans (hfdegree.trans (hgdegree.trans rfl))
    rw [hStop]
    exact Submodule.mem_top
  letI : Normal F T :=
    normal_of_splits_and_adjoin_root_eq_top q α
      (hqmonic.map (algebraMap F T)).ne_zero hrootq hsplitq hgen
  have hαsep : IsSeparable F α := by
    change (minpoly F α).Separable
    exact hqsep.of_dvd (minpoly.dvd F α hrootq)
  letI : Algebra.IsSeparable F S :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F T).mpr hαsep
  let eS : S ≃ₐ[F] T :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  letI : Algebra.IsSeparable F T := AlgEquiv.Algebra.isSeparable eS
  exact IsGalois.mk

set_option maxHeartbeats 800000 in
/-- A residue-exhausting maximal subfield of a local central division algebra is cyclic
Galois over the center.  It is identified with the canonical unramified Hensel lift as a
splitting field, so arithmetic Frobenius generates its full Galois group. -/
theorem divisionAlgebraResidueExhaustingMaximalSubfield_isCyclic
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
    IsCyclic Gal(T / F) := by
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
  letI : IsCyclic Gal(U / F) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base
      F f hf g hgmonic hfg hg
  exact isCyclic_of_surjective (AlgEquiv.autCongr eUT).toMonoidHom
    (AlgEquiv.autCongr eUT).surjective


/-- Every finite-dimensional central division algebra over a nonarchimedean local field is split
by a degree-exact Galois maximal subfield whose residue field exhausts the determinant residue
field.  This is the unramified Galois splitting-field half of local cyclic exhaustion. -/
theorem exists_residueExhausting_galoisMaximalSubfield_scalarExtension_eq_split :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
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
          divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
            (F := F) (A := A) T hT
        letI : ProperSpace T :=
          divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          Nonempty (NormValuationResidue (F := T) ≃ₐ[NormValuationResidue (F := F)]
            DivisionAlgebraDeterminantResidue (F := F) (A := A)) ∧
          IsGalois F T ∧
          IsCyclic Gal(T / F) ∧
          scalarExtensionBrauerMap F T (brauerClass (centralDivisionCSA F A)) =
            brauerSplitClass T := by
  obtain ⟨x, hT, hdegree, ⟨hres⟩⟩ :=
    exists_maximalSubfield_normValuationResidue_algEquiv (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
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
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
      (F := F) (A := A) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := A) T hT
  have hGalois : IsGalois F T :=
    divisionAlgebraResidueExhaustingMaximalSubfield_isGalois
      (F := F) (A := A) T hT hdegree hres
  have hCyclic : IsCyclic Gal(T / F) :=
    divisionAlgebraResidueExhaustingMaximalSubfield_isCyclic
      (F := F) (A := A) T hT hdegree hres
  have hcommT : IsMulCommutative T := inferInstance
  obtain ⟨S, hTS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hSsq : Module.finrank F S * Module.finrank F S = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  have hSdegree : Module.finrank F S = divisionAlgebraDegree (F := F) (A := A) :=
    Nat.mul_self_inj.mp
      (hSsq.trans (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm)
  have hTeqS : T = S :=
    Subalgebra.eq_of_le_of_finrank_eq hTS (hdegree.trans hSdegree.symm)
  have hmaxT : ∀ U : Subalgebra F A, T ≤ U → IsMulCommutative U → U = T := by
    intro U hTU hcommU
    exact (hmaxS U (by simpa only [hTeqS] using hTU) hcommU).trans hTeqS.symm
  refine ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, ?_⟩
  exact scalarExtensionBrauerMap_centralDivisionCSA_eq_split_of_maximalSubfield
    F A T hcommT hT hmaxT

/-- Every Brauer class over a nonarchimedean local field is split by a finite cyclic Galois
extension.  The extension is the residue-exhausting maximal subfield of a central division
representative of the class. -/
theorem brauerGroup_exists_cyclicGaloisSplittingField (c : BrauerGroup F) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : IsGalois F L) (_ : IsCyclic Gal(L / F)),
      scalarExtensionBrauerMap F L c = brauerSplitClass L := by
  obtain ⟨D, hD, aD, finD, hcentralD, hc⟩ :=
    brauerGroup_exists_centralDivisionRepresentative F c
  letI : DivisionRing D := hD
  letI : Algebra F D := aD
  letI : Module.Finite F D := finD
  letI : Algebra.IsCentral F D := hcentralD
  obtain ⟨x, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, hsplit⟩ :=
    exists_residueExhausting_galoisMaximalSubfield_scalarExtension_eq_split
      (F := F) (A := D)
  let T := Algebra.adjoin F ({(x : D)} : Set D)
  letI : NormedDivisionRing D :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := D)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := D) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := D) T hT
  letI : CompleteSpace T :=
    divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := D) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
      (F := F) (A := D) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := D) T hT
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [hc]
  exact hsplit

end

end GaloisForLFunctions.HTGeometry.ABHN
