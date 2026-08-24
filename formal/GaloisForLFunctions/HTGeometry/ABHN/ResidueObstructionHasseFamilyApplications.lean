import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSumHasseClassification
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocityQuotient
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionCompletedTameRatModIntHasseSequence
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanValuationHasse
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldNormHasse
import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90Hasse
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousReciprocityHasseClassification

/-!
# Residue and obstruction Hasse-family applications

Placewise and one-obstruction-coordinate forms of exact local--global sequences already proved in
the corpus.  This includes actual completed finite-adic tame quotients for `F(t)`, the raw
finite-support `RatModInt` reciprocity target, valuation and norm quotients, Hilbert 90, and cyclic
degree-two cohomology.  No comparison with a local Brauer group is asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

noncomputable section

/-- Zero-sum number-field invariant packets are separated place by place. -/
def numberFieldZeroSumInvariantHasseFamily
    (K : Type u) [Field K] [NumberField K] :
    HasseFamily
      (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker
      (NumberFieldPlace K) where
  Local := fun _ => RatModInt
  profile := fun x v => x.1 v
  profile_injective := by
    intro x y hxy
    apply Subtype.ext
    ext v
    exact congrFun hxy v

/-- Zero-sum rational-function invariant packets are separated place by place. -/
def rationalFunctionZeroSumInvariantHasseFamily
    (F : Type u) [Field F] [Finite F] :
    HasseFamily
      (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker
      (RationalFunctionPlace F) where
  Local := fun _ => RatModInt
  profile := fun x v => x.1 v
  profile_injective := by
    intro x y hxy
    apply Subtype.ext
    ext v
    exact congrFun hxy v

/-- The number-field reciprocity cokernel has the invariant sum as one complete coordinate. -/
def numberFieldInvariantSumQuotientHasseFamily
    (K : Type u) [Field K] [NumberField K] :
    HasseFamily
      ((NumberFieldPlace K →₀ RatModInt) ⧸
        (finsuppRatModIntSumAddHom (NumberFieldPlace K)).ker)
      Unit :=
  HasseFamily.ofEquivSingle (numberFieldFinsuppRatModIntSumQuotientEquiv K).toEquiv

/-- The rational-function reciprocity cokernel has the invariant sum as one complete coordinate. -/
def rationalFunctionInvariantSumQuotientHasseFamily
    (F : Type u) [Field F] [Finite F] :
    HasseFamily
      ((RationalFunctionPlace F →₀ RatModInt) ⧸
        (finsuppRatModIntSumAddHom (RationalFunctionPlace F)).ker)
      Unit :=
  HasseFamily.ofEquivSingle (rationalFunctionFinsuppRatModIntSumQuotientEquiv F).toEquiv

/-- Over any field, finite polynomial residues and infinity jointly determine a Milnor class
modulo constants. -/
def milnorPolynomialGlobalResidueQuotientHasseFamily
    (F : Type u) [Field F] (n : ℕ) :
    HasseFamily
      (MilnorKDeg (RatFunc F) n.succ ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ))
      (Sum (MonicIrred F) Unit) where
  Local := fun p => match p with
    | .inl q => MilnorKDeg (polyResidueField q.2.1) n
    | .inr _ => MilnorKDeg F n
  profile := fun x p => match p with
    | .inl q => (milnorPolynomialGlobalResidueQuotientEquiv (F := F) n x).1.1 q
    | .inr _ => (milnorPolynomialGlobalResidueQuotientEquiv (F := F) n x).1.2
  profile_injective := by
    intro x y hxy
    apply (milnorPolynomialGlobalResidueQuotientEquiv (F := F) n).injective
    apply Subtype.ext
    apply Prod.ext
    · apply DFinsupp.ext
      intro q
      exact congrFun hxy (.inl q)
    · exact congrFun hxy (.inr ())

/-- Actual completed finite-adic tame quotients and infinity jointly determine `K₂ᴹ(F(t))`
modulo constants. -/
def rationalFunctionCompletedTameGlobalResidueHasseFamily
    (F : Type u) [Field F] [Finite F] :
    HasseFamily
      (MilnorKDeg (RatFunc F) 2 ⧸
        AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) 2))
      (Sum (MonicIrred F) Unit) where
  Local := fun p => match p with
    | .inl q => RationalFunctionFiniteAdicTameQuotient F q
    | .inr _ => MilnorKDeg F 1
  profile := fun x p => match p with
    | .inl q => (rationalFunctionCompletedTameGlobalResidueQuotientEquiv F x).1.1 q
    | .inr _ => (rationalFunctionCompletedTameGlobalResidueQuotientEquiv F x).1.2
  profile_injective := by
    intro x y hxy
    apply (rationalFunctionCompletedTameGlobalResidueQuotientEquiv F).injective
    apply Subtype.ext
    apply Prod.ext
    · apply DFinsupp.ext
      intro q
      exact congrFun hxy (.inl q)
    · exact congrFun hxy (.inr ())

/-- The finite-layer Milnor local-profile cokernel is completely measured by its realized
`RatModInt` obstruction. -/
def milnorPolynomialKOneLocalObstructionHasseFamily
    (F : Type u) [Field F] [Finite F] :
    HasseFamily
      ((MilnorPolynomialTotalResidueTarget (F := F) 1 × MilnorKDeg F 1) ⧸
        (milnorPolynomialAllResidue (F := F) 1).range)
      Unit :=
  HasseFamily.ofEquivSingle
    (milnorPolynomialKOneLocalProfileQuotientEquivRatModIntRange (F := F)).toEquiv

/-- The completed-tame local-profile cokernel is completely measured by its realized
`RatModInt` obstruction. -/
def rationalFunctionCompletedTameLocalObstructionHasseFamily
    (F : Type u) [Field F] [Finite F] :
    HasseFamily
      (RationalFunctionCompletedTameAllLocalData F ⧸
        (rationalFunctionCompletedTameAllResidue F).range)
      Unit :=
  HasseFamily.ofEquivSingle
    (rationalFunctionCompletedTameLocalProfileQuotientEquivRatModIntRange F).toEquiv

/-- The normalized valuation is a complete one-place invariant modulo valuation-zero units. -/
def nonarchimedeanValuationQuotientHasseFamily
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    HasseFamily
      (Kˣ ⧸ (nonarchimedeanLocalFieldResidueData K).val.ker)
      Unit :=
  HasseFamily.ofEquivSingle (nonarchimedeanLocalFieldQuotientKerValuationEquiv K).toEquiv

/-- Finite-field norm is a complete one-place invariant modulo Frobenius coboundaries. -/
def finiteFieldFrobeniusNormQuotientHasseFamily
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    HasseFamily
      (Additive Lˣ ⧸
        (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L)).range)
      Unit :=
  HasseFamily.ofEquivSingle (finiteFieldArithmeticFrobeniusNormHasseQuotientEquiv K L).toEquiv

/-- Cyclic Hilbert 90 gives a complete one-place norm-one invariant. -/
def cyclicHilbert90QuotientHasseFamily
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : ∀ sigma, sigma ∈ Subgroup.zpowers g) :
    HasseFamily
      (Additive Lˣ ⧸ (cyclicGaloisAdditiveCoboundary g).ker)
      Unit :=
  HasseFamily.ofEquivSingle (cyclicHilbert90HasseQuotientEquiv hg).toEquiv

/-- Cyclic degree-two cohomology is the complete invariant of base units modulo norms. -/
def cyclicGaloisH2NormQuotientHasseFamily
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    HasseFamily
      (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L)
      Unit :=
  HasseFamily.ofEquivSingle (cyclicGaloisH2BaseNormQuotientEquiv K L).toEquiv

/-- For place-dependent local groups and invariant maps, the realized invariant sum is a complete
coordinate modulo the heterogeneous reciprocity kernel. -/
noncomputable def heterogeneousInvariantSumQuotientHasseFamily
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) :=
  HasseFamily.ofEquivSingle
    (heterogeneousRatModIntProfileInvariantSumQuotientEquivRange A inv).toEquiv

end
end GaloisForLFunctions.HTGeometry.ABHN
