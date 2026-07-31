import GaloisForLFunctions.HTGeometry.FiniteDimensionalLinearHolographicLocalityTradeoffUniversalityLaw
import GaloisForLFunctions.HTGeometry.PrincipalSymbolDetectorCompressionLocalityUniversalityLaw
import GaloisForLFunctions.HTGeometry.SmoothWaringThreeScaleCompressionLocalityUniversalityLaw

/-!
# Finite-dimensional linear--quadratic holographic compression and locality

The quadratic principal-symbol completion can be transported through a linear coordinate
equivalence just like the linear-width completion.  On an arbitrary finite-dimensional law
space, both coordinate-free completions then have one dependence horizon and maximal exterior
symbol.  Linear detector compression leaves the coordinate membrane pair-covering cost unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {V : Type w} [AddCommGroup V] [Module K V]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- Transport the quadratic-width completion to an arbitrary linearly equivalent law space. -/
def coordinateFreeQuadraticWidthPrincipalSymbolCompletion
    (q : K) (hq : q ^ d = 1)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) :
    V →ₗ[K] Module.End K (QuadraticPrincipalCompletionState M n d) :=
  (quadraticWidthPrincipalSymbolCompletion q hq
    (A₀.comp e.symm.toLinearMap)).comp e.toLinearMap

/-- Coordinate transport preserves the represented scalar law for the quadratic completion. -/
theorem coordinateFreeQuadraticWidthPrincipalSymbolCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id) (v : V) :
    (coordinateFreeQuadraticWidthPrincipalSymbolCompletion
      q hq.pow_eq_one e A₀ v) ^ d =
      F v • LinearMap.id := by
  have hcoord : ∀ c : Fin n → K,
      ((A₀.comp e.symm.toLinearMap) c) ^ d =
        F (e.symm c) • LinearMap.id := by
    intro c
    exact hA₀ (e.symm c)
  simpa [coordinateFreeQuadraticWidthPrincipalSymbolCompletion] using
    (quadraticWidthPrincipalSymbolCompletion_pow
      q hq (A₀.comp e.symm.toLinearMap) (fun c ↦ F (e.symm c)) hcoord (e v))

omit [CharZero K] in
/-- Coordinate transport preserves maximal quadratic exterior principal-symbol rank. -/
theorem
    coordinateFreeQuadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (coordinateFreeQuadraticWidthPrincipalSymbolCompletion
          q hq.pow_eq_one e A₀)) := by
  rw [coordinateFreeQuadraticWidthPrincipalSymbolCompletion,
    endomorphismCommutatorMap_comp]
  exact
    (quadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
      q hq (A₀.comp e.symm.toLinearMap) m hm).comp
      (exteriorPower.map_injective_field (n := 2) e.injective)

/-- Coordinate-free quadratic dependence-horizon and maximal-symbol theorem. -/
theorem
    coordinateFreeQuadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d)
    (e : V ≃ₗ[K] (Fin n → K))
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (coordinateFreeQuadraticWidthPrincipalSymbolCompletion
            q hq.pow_eq_one e A₀ v)
          (quadraticPrincipalCompletionRoot (n := n) (d := d) m))} =
      {v : V | F v = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (coordinateFreeQuadraticWidthPrincipalSymbolCompletion
            q hq.pow_eq_one e A₀))) := by
  constructor
  · apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
      (coordinateFreeQuadraticWidthPrincipalSymbolCompletion
        q hq.pow_eq_one e A₀) F d
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
      (quadraticPrincipalCompletionRoot (n := n) (d := d) m)
      (quadraticPrincipalCompletionRoot_ne_zero m hm)
    exact
      coordinateFreeQuadraticWidthPrincipalSymbolCompletion_pow
        q hq e A₀ F hA₀
  · rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact
      coordinateFreeQuadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
        q hq e A₀ m hm

variable [FiniteDimensional K V]

/-- Canonical basis-free quadratic completion of a finite-dimensional law space. -/
def finiteDimensionalQuadraticHolographicCompletion
    (q : K) (hq : q ^ d = 1)
    (A₀ : V →ₗ[K] Module.End K M) :
    V →ₗ[K] Module.End K
      (QuadraticPrincipalCompletionState M (Module.finrank K V) d) :=
  coordinateFreeQuadraticWidthPrincipalSymbolCompletion
    q hq finiteDimensionalLawCoordinates A₀

/-- Canonical finite-coordinate quadratic symbol before transport back to the law space. -/
def finiteDimensionalQuadraticHolographicCoordinateSymbol
    (q : K) (hq : q ^ d = 1)
    (A₀ : V →ₗ[K] Module.End K M) :
    (Fin (Module.finrank K V) → K) →ₗ[K]
      Module.End K
        (QuadraticPrincipalCompletionState M (Module.finrank K V) d) :=
  quadraticWidthPrincipalSymbolCompletion q hq
    (A₀.comp finiteDimensionalLawCoordinates.symm.toLinearMap)

variable {Hlin Hquad : Type*} [Fintype Hlin] [Fintype Hquad]

/-- **Finite-dimensional linear--quadratic holographic compression--locality universality
law.** The coordinate-free linear and quadratic completions have one exact dependence horizon
and maximal exterior symbols. From four law directions onward the linear detector is strictly
smaller, but bounded-valence coordinate membranes for both completions obey the same pair-covering
lower bound. -/
theorem
    finiteDimensionalLinearQuadraticHolographicCompletion_compressionLocalityUniversality
    (hrank : 4 ≤ Module.finrank K V)
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (A₀ : V →ₗ[K] Module.End K M) (F : V → K)
    (hA₀ : ∀ v, (A₀ v) ^ d = F v • LinearMap.id)
    (m : M) (hm : m ≠ 0)
    (supportLinear : Hlin → Finset (Fin (Module.finrank K V)))
    (supportQuadratic : Hquad → Finset (Fin (Module.finrank K V)))
    (Δlin Δquad : ℕ)
    (hmembraneLinear : MembraneLocalPrincipalBrackets
      (finiteDimensionalLinearHolographicCoordinateSymbol q hq.pow_eq_one A₀)
      supportLinear)
    (hmembraneQuadratic : MembraneLocalPrincipalBrackets
      (finiteDimensionalQuadraticHolographicCoordinateSymbol q hq.pow_eq_one A₀)
      supportQuadratic)
    (hlocalLinear : MembraneValenceAtMost supportLinear Δlin)
    (hlocalQuadratic : MembraneValenceAtMost supportQuadratic Δquad) :
    ({v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀ v)
          (linearPrincipalCompletionRoot
            (n := Module.finrank K V) (d := d) m))} =
      {v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalQuadraticHolographicCompletion
            q hq.pow_eq_one A₀ v)
          (quadraticPrincipalCompletionRoot
            (n := Module.finrank K V) (d := d) m))}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalLinearHolographicCompletion q hq.pow_eq_one A₀))) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalQuadraticHolographicCompletion
            q hq.pow_eq_one A₀))) ∧
    Fintype.card
        (LinearWidthDetectorIndex (Module.finrank K V) × ZMod d) <
      Fintype.card
        (QuadraticQuantumDetectorIndex (Module.finrank K V) × ZMod d) ∧
    MembranePairComplete supportLinear ∧
    MembranePairComplete supportQuadratic ∧
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card Hlin * Nat.choose Δlin 2 ∧
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card Hquad * Nat.choose Δquad 2 := by
  have hlinear :=
    finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq hd A₀ F hA₀ m hm
  have hquadratic :=
    coordinateFreeQuadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq finiteDimensionalLawCoordinates A₀ F hA₀ m hm
  have hcoordPow : ∀ c : Fin (Module.finrank K V) → K,
      ((A₀.comp finiteDimensionalLawCoordinates.symm.toLinearMap) c) ^ d =
        F (finiteDimensionalLawCoordinates.symm c) • LinearMap.id :=
    fun c => hA₀ (finiteDimensionalLawCoordinates.symm c)
  have hcomparison :=
    principalSymbolDetectorCompression_localityUniversality
      hrank q hq hd
      (A₀.comp finiteDimensionalLawCoordinates.symm.toLinearMap)
      (fun c => F (finiteDimensionalLawCoordinates.symm c))
      hcoordPow m hm
      supportLinear supportQuadratic Δlin Δquad
      hmembraneLinear hmembraneQuadratic hlocalLinear hlocalQuadratic
  exact
    ⟨hlinear.1.trans hquadratic.1.symm,
      hlinear.2,
      hquadratic.2,
      hcomparison.2.2.2.1,
      hcomparison.2.2.2.2.1,
      hcomparison.2.2.2.2.2.1,
      hcomparison.2.2.2.2.2.2.1,
      hcomparison.2.2.2.2.2.2.2⟩

/-! ## Coordinate-free smooth-Waring three-scale completion -/

variable {s : ℕ}

/-- Physical finite-quantum Waring symbol transported to an arbitrary
finite-dimensional law space. -/
def finiteDimensionalSmoothWaringSymbol
    (q : K) (hq : q ^ d = 1)
    (a : Matrix (Fin s) (Fin (Module.finrank K V)) K) :
    V →ₗ[K] Module.End K (FiniteQuantumState (Fin s) d → K) :=
  (finiteQuantumWaringSymbol (d := d) q hq a.mulVecLin).comp
    finiteDimensionalLawCoordinates.toLinearMap

/-- Scalar Waring law in canonical finite-dimensional coordinates. -/
def finiteDimensionalSmoothWaringLaw
    (a : Matrix (Fin s) (Fin (Module.finrank K V)) K) (v : V) : K :=
  MvPolynomial.eval (finiteDimensionalLawCoordinates v)
    (mvWaringPolynomial d a)

variable {Hbase : Type*} [Fintype Hbase]

/-- Coordinate-free three-scale certificate for one smooth Waring law. -/
structure FiniteDimensionalSmoothWaringThreeScaleCertificate
    (q : K) (hq : q ^ d = 1)
    (a : Matrix (Fin s) (Fin (Module.finrank K V)) K)
    (supportBase : Hbase → Finset (Fin (Module.finrank K V)))
    (supportLinear : Hlin → Finset (Fin (Module.finrank K V)))
    (supportQuadratic : Hquad → Finset (Fin (Module.finrank K V)))
    (Δbase Δlin Δquad : ℕ) : Prop where
  physicalHorizon :
    {v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalSmoothWaringSymbol q hq a v)
          (finiteQuantumRoot (K := K) (ι := Fin s) (d := d)))} =
      {v : V | finiteDimensionalSmoothWaringLaw (d := d) a v = 0}
  linearHorizon :
    {v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalLinearHolographicCompletion q hq
            (finiteDimensionalSmoothWaringSymbol q hq a) v)
          (linearPrincipalCompletionRoot
            (n := Module.finrank K V) (d := d)
            (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))))} =
      {v : V | finiteDimensionalSmoothWaringLaw (d := d) a v = 0}
  quadraticHorizon :
    {v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteDimensionalQuadraticHolographicCompletion q hq
            (finiteDimensionalSmoothWaringSymbol q hq a) v)
          (quadraticPrincipalCompletionRoot
            (n := Module.finrank K V) (d := d)
            (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))))} =
      {v : V | finiteDimensionalSmoothWaringLaw (d := d) a v = 0}
  physicalMaximalSymbol :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalSmoothWaringSymbol q hq a)))
  linearMaximalSymbol :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalLinearHolographicCompletion q hq
            (finiteDimensionalSmoothWaringSymbol q hq a))))
  quadraticMaximalSymbol :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteDimensionalQuadraticHolographicCompletion q hq
            (finiteDimensionalSmoothWaringSymbol q hq a))))
  detectorCompression :
    Fintype.card
        (LinearWidthDetectorIndex (Module.finrank K V) × ZMod d) <
      Fintype.card
        (QuadraticQuantumDetectorIndex (Module.finrank K V) × ZMod d)
  monomialIndependent :
    LinearIndependent K
      (finiteQuantumMonomial (K := K) (ι := Fin s) (d := d) q hq)
  monomialProduct :
    ∀ x y : Fin s → ZMod d,
      finiteQuantumMonomial q hq x * finiteQuantumMonomial q hq y =
        (∏ i, finiteQuantumCharacter d q hq
            (-(y i * finiteQuantumTailCharge i x))) •
          finiteQuantumMonomial q hq (x + y)
  basePairComplete : MembranePairComplete supportBase
  linearPairComplete : MembranePairComplete supportLinear
  quadraticPairComplete : MembranePairComplete supportQuadratic
  baseLocalityBound :
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card Hbase * Nat.choose Δbase 2
  linearLocalityBound :
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card Hlin * Nat.choose Δlin 2
  quadraticLocalityBound :
    Nat.choose (Module.finrank K V) 2 ≤
      Fintype.card Hquad * Nat.choose Δquad 2

/-- **Finite-dimensional smooth-Waring three-scale holographic law.** The
physical packet and both meta-completions have one coordinate-free horizon
and maximal symbols, while strict detector compression preserves the
three membrane pair-covering lower bounds. -/
theorem finiteDimensionalSmoothWaring_threeScaleHolographicUniversality
    (hrank : 4 ≤ Module.finrank K V)
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (a : Matrix (Fin s) (Fin (Module.finrank K V)) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a))
    (supportBase : Hbase → Finset (Fin (Module.finrank K V)))
    (supportLinear : Hlin → Finset (Fin (Module.finrank K V)))
    (supportQuadratic : Hquad → Finset (Fin (Module.finrank K V)))
    (Δbase Δlin Δquad : ℕ)
    (hmembraneBase :
      MembraneLocalPrincipalBrackets
        (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
        supportBase)
    (hmembraneLinear :
      MembraneLocalPrincipalBrackets
        (finiteDimensionalLinearHolographicCoordinateSymbol q hq.pow_eq_one
          (finiteDimensionalSmoothWaringSymbol q hq.pow_eq_one a))
        supportLinear)
    (hmembraneQuadratic :
      MembraneLocalPrincipalBrackets
        (finiteDimensionalQuadraticHolographicCoordinateSymbol q hq.pow_eq_one
          (finiteDimensionalSmoothWaringSymbol q hq.pow_eq_one a))
        supportQuadratic)
    (hlocalBase : MembraneValenceAtMost supportBase Δbase)
    (hlocalLinear : MembraneValenceAtMost supportLinear Δlin)
    (hlocalQuadratic : MembraneValenceAtMost supportQuadratic Δquad) :
    FiniteDimensionalSmoothWaringThreeScaleCertificate
      q hq.pow_eq_one a supportBase supportLinear supportQuadratic
        Δbase Δlin Δquad := by
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    finiteDimensionalLawCoordinates
  let A₀ := finiteDimensionalSmoothWaringSymbol q hq.pow_eq_one a
  let F := finiteDimensionalSmoothWaringLaw (d := d) a
  let Acoord :=
    finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin
  have hbase :=
    smoothMvWaring_normalForm_holographicLocalityUniversality
      q hq a hsmooth supportBase Δbase hmembraneBase hlocalBase
  have hpower : ∀ v, (A₀ v) ^ d = F v • LinearMap.id := by
    intro v
    change (Acoord (e v)) ^ d =
      MvPolynomial.eval (e v) (mvWaringPolynomial d a) • LinearMap.id
    rw [eval_mvWaringPolynomial]
    exact finiteQuantumTorusSymbol_pow q hq (a.mulVecLin (e v))
  let root := finiteQuantumRoot (K := K) (ι := Fin s) (d := d)
  have hlinear :=
    finiteDimensionalLinearHolographicCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq hd A₀ F hpower root finiteQuantumRoot_ne_zero
  have hquadratic :=
    coordinateFreeQuadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq e A₀ F hpower root finiteQuantumRoot_ne_zero
  have hmeta :=
    finiteDimensionalLinearQuadraticHolographicCompletion_compressionLocalityUniversality
      hrank q hq hd A₀ F hpower root finiteQuantumRoot_ne_zero
        supportLinear supportQuadratic Δlin Δquad
        hmembraneLinear hmembraneQuadratic hlocalLinear hlocalQuadratic
  have hphysicalHorizon :
      {v : V | ¬ AlgebraicIndependent K
          (generalizedCliffordShiftFieldJet (A₀ v) root)} =
        {v : V | F v = 0} := by
    ext v
    have hv := Set.ext_iff.mp hbase.1.1 (e v)
    simpa [A₀, F, e, root, finiteDimensionalSmoothWaringSymbol,
      finiteDimensionalSmoothWaringLaw, Acoord] using hv
  have hcoordEndomorphism :
      Function.Injective (endomorphismCommutatorMap Acoord) := by
    rw [← generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact hbase.1.2.1
  have hphysicalSymbol :
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw A₀)) := by
    rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    change Function.Injective
      (endomorphismCommutatorMap
        (Acoord.comp e.toLinearMap))
    rw [endomorphismCommutatorMap_comp]
    exact hcoordEndomorphism.comp
      (exteriorPower.map_injective_field (n := 2) e.injective)
  exact {
    physicalHorizon := hphysicalHorizon
    linearHorizon := hlinear.1
    quadraticHorizon := hquadratic.1
    physicalMaximalSymbol := hphysicalSymbol
    linearMaximalSymbol := hlinear.2
    quadraticMaximalSymbol := hquadratic.2
    detectorCompression := hmeta.2.2.2.1
    monomialIndependent := hbase.1.2.2.1
    monomialProduct := hbase.1.2.2.2
    basePairComplete := hbase.2.1
    linearPairComplete := hmeta.2.2.2.2.1
    quadraticPairComplete := hmeta.2.2.2.2.2.1
    baseLocalityBound := hbase.2.2
    linearLocalityBound := hmeta.2.2.2.2.2.2.1
    quadraticLocalityBound := hmeta.2.2.2.2.2.2.2 }

end

end GaloisForLFunctions.HTGeometry
