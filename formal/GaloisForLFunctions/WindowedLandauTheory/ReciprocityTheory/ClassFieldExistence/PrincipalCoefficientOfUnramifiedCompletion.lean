import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionResidueFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IrreducibleNormalizedInteger
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrincipalUnitIndices
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionUnitsReduction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDeepRoots

/-! First principal-unit coefficients at an unramified completion form an
additive residue quotient. A base uniformizer makes coefficient reduction
equivariant for Frobenius. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Multiplicative
open GaloisForLFunctions GaloisForLFunctions.HTGeometry.ABHN WindowedLandauTheory.ConjugateSelfDual
open scoped Pointwise WithZero ValuativeRel GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem exists_frobeniusEquivariant_principalCoefficient
    (he : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hσ : IsArithFrobAt (𝓞 K) σ.val w.asIdeal) :
    ∃ f : unitsLevel (K := L) w 0 →* Multiplicative (𝓞 L ⧸ w.asIdeal),
      Function.Surjective f ∧ IsOpen (f.ker : Set (unitsLevel (K := L) w 0)) ∧
      ∀ x y : unitsLevel (K := L) w 0,
        y.val = Units.map (decompositionMulEquiv v w σ).toMonoidHom x.val →
        f y = ofAdd (toAdd (f x) ^ normV v) := by
  obtain ⟨w₀, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := L)).surjective w
  let w := w₀.maximalIdeal
  letI : w.asIdeal.LiesOver v.asIdeal :=
    ‹(FinitePlace.equivHeightOneSpectrum w₀).asIdeal.LiesOver v.asIdeal›
  have he' : w.asIdeal.ramificationIdx (𝓞 K) = 1 := he
  let F := w.adicCompletion L
  let V : Valuation F ℤᵐ⁰ := Valued.v
  letI : ValuativeRel F := numberFieldAdicCompletionValuativeRel L w₀
  letI : V.Compatible := numberFieldAdicCompletionValuationCompatible L w₀
  letI : IsNonarchimedeanLocalField F := numberFieldAdicCompletionIsNonarchimedeanLocalField L w₀
  let e : 𝒪[F] ≃+* CompletedIntegers w :=
    (RingEquiv.subringCongr (valuationSubring_eq_integer V)).symm
  let ek : 𝓀[F] ≃+* (𝓞 L ⧸ w.asIdeal) :=
    (IsLocalRing.ResidueField.mapEquiv e).trans (completedResidueEquiv w).symm
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Finite 𝓀[F] := Finite.of_injective ek ek.injective
  obtain ⟨p, hp⟩ := valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  let z := AdicLiesOver.completionMap v w p
  have hz : V z = WithZero.exp (-1 : ℤ) := by
    change Valued.v (AdicLiesOver.completionMap v w p) = _
    rw [AdicLiesOver.valued_completionMap v w, hp,
      Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he', pow_one]
  let p' : CompletedIntegers w := ⟨z, by
    change V z ≤ 1
    rw [hz, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega⟩
  let π := e.symm p'
  have hπ : Irreducible π :=
    (irreducible_integer_of_valuation_eq_exp_neg_one V p' hz).map e.symm.toMulEquiv
  have hπV : V (π : F) = WithZero.exp (-1 : ℤ) := hz
  let j : unitsLevel (K := L) w 0 ≃* 𝒪[F]ˣ :=
    (unitsLevelZeroEquivIntegerUnits w).trans (Units.mapEquiv e.symm.toMulEquiv)
  let k : Multiplicative 𝓀[F] →* Multiplicative (𝓞 L ⧸ w.asIdeal) :=
    AddMonoidHom.toMultiplicative ek.toAddMonoidHom
  let f := k.comp ((firstPrincipalUnitCoefficient hπ).comp j.toMonoidHom)
  have hfs : Function.Surjective f := ek.surjective.comp
    ((firstPrincipalUnitCoefficient_surjective hπ).comp j.surjective)
  have hop : IsOpen (f.ker : Set (unitsLevel (K := L) w 0)) := by
    let U := (Subtype.val : unitsLevel (K := L) w 0 → (w.adicCompletion L)ˣ) ⁻¹'
      (unitsLevel (K := L) w 2 : Set (w.adicCompletion L)ˣ)
    have hU : IsOpen U := (isOpen_unitsLevel (K := L) w 2).preimage continuous_subtype_val
    have h1 : (1 : unitsLevel (K := L) w 0) ∈ U := (unitsLevel (K := L) w 2).one_mem
    apply f.ker.isOpen_of_mem_nhds (g := 1)
    refine Filter.mem_of_superset (hU.mem_nhds h1) fun x hx => ?_
    have hLvl : x.val ∈ unitsLevel (K := L) w 2 := hx
    have h₂ : V (((j x).val : F) - 1) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
      (mem_unitsLevel.mp hLvl).2
    have hJ := mem_principalUnits_of_valued_bound V hπ hπV 2 (j x) h₂
    change k (firstPrincipalUnitCoefficient hπ (j x)) = 1
    rw [firstPrincipalUnitCoefficient_eq_one_of_mem_level_two hπ _ hJ, map_one]
  refine ⟨f, hfs, hop, fun x y hxy => ?_⟩
  let d := decompositionOnCompletedIntegersEquiv v w σ
  let c := (e.trans d).trans e.symm
  have hcπ : c π = π := by
    apply e.injective
    rw [show e (c π) = d (e π) from e.apply_symm_apply _, show e π = p' from e.apply_symm_apply p']
    apply Subtype.ext
    change (decompositionMulEquiv v w σ) (algebraMap (v.adicCompletion K) F p) = _
    exact (decompositionMulEquiv v w σ).commutes p
  have hj : j y = Units.map c.toMonoidHom (j x) := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : (w.adicCompletion L)ˣ => (z : w.adicCompletion L)) hxy
  have hres (r : 𝓀[F]) : ek (IsLocalRing.ResidueField.mapEquiv c r) = (ek r) ^ normV v := by
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
    change completionReduction w (e (c s)) = (completionReduction w (e s)) ^ normV v
    rw [show e (c s) = d (e s) from e.apply_symm_apply _]
    exact completionReduction_decomposition_frobenius v w σ hσ (e s)
  change k (firstPrincipalUnitCoefficient hπ (j y)) = _
  rw [hj, firstPrincipalUnitCoefficient_map hπ c hcπ]
  exact congrArg ofAdd (hres (toAdd (firstPrincipalUnitCoefficient hπ (j x))))

end GlobalTheory.Reciprocity
