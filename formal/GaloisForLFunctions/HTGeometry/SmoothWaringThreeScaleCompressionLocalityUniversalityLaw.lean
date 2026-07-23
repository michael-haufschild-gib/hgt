import GaloisForLFunctions.HTGeometry.PrincipalSymbolDetectorCompressionLocalityUniversalityLaw
import GaloisForLFunctions.HTGeometry.SmoothWaringHolographicLocalityUniversalityLaw

/-!
# Smooth Waring three-scale compression–locality universality

The exact primitive-order power identity of a smooth finite Waring packet instantiates the
representation-free linear/quadratic detector-completion theorem.  Consequently the original
finite quantum realization and both detector completions have one common Waring hypersurface
horizon and maximal exterior principal symbols, while all three obey the same pair-covering
locality obstruction.  The linear completion is nevertheless strictly narrower than the
quadratic completion from four law directions onward.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {d r s : ℕ} [NeZero d] [Fact (1 < d)]
  {Hbase Hlin Hquad : Type*}
  [Fintype Hbase] [Fintype Hlin] [Fintype Hquad]

/-- **Smooth Waring three-scale compression–locality universality law.**  For an actual smooth
Waring pencil, the original finite quantum packet and its linear- and quadratic-width
meta-completions have one complete dependence horizon.  Every realization has an injective
exterior derivation symbol and the same membrane pair-covering obstruction; the original packet
also retains its twisted-monomial normal form, while the linear meta-completion is strictly
narrower than the quadratic one. -/
theorem smoothMvWaring_threeScaleCompressionLocalityUniversality
    (hr : 4 ≤ r)
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (a : Matrix (Fin s) (Fin r) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a))
    (supportBase : Hbase → Finset (Fin r))
    (supportLinear : Hlin → Finset (Fin r))
    (supportQuadratic : Hquad → Finset (Fin r))
    (Δbase Δlin Δquad : ℕ)
    (hmembraneBase :
      MembraneLocalPrincipalBrackets
        (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
        supportBase)
    (hmembraneLinear :
      MembraneLocalPrincipalBrackets
        (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin))
        supportLinear)
    (hmembraneQuadratic :
      MembraneLocalPrincipalBrackets
        (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin))
        supportQuadratic)
    (hlocalBase : MembraneValenceAtMost supportBase Δbase)
    (hlocalLinear : MembraneValenceAtMost supportLinear Δlin)
    (hlocalQuadratic : MembraneValenceAtMost supportQuadratic Δquad) :
    ({c : Fin r → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin c)
          (finiteQuantumRoot (K := K) (ι := Fin s) (d := d)))} =
      {c : Fin r → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin) c)
          (linearPrincipalCompletionRoot (n := r) (d := d)
            (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))))}) ∧
    ({c : Fin r → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin) c)
          (linearPrincipalCompletionRoot (n := r) (d := d)
            (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))))} =
      {c : Fin r → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin) c)
          (quadraticPrincipalCompletionRoot (n := r) (d := d)
            (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))))}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin))) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (linearWidthPrincipalSymbolCompletion q hq.pow_eq_one
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)))) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)))) ∧
    Fintype.card (LinearWidthDetectorIndex r × ZMod d) <
      Fintype.card (QuadraticQuantumDetectorIndex r × ZMod d) ∧
    LinearIndependent K
      (finiteQuantumMonomial (K := K) (ι := Fin s) (d := d) q hq.pow_eq_one) ∧
    (∀ x y : Fin s → ZMod d,
      finiteQuantumMonomial q hq.pow_eq_one x *
          finiteQuantumMonomial q hq.pow_eq_one y =
        (∏ i, finiteQuantumCharacter d q hq.pow_eq_one
            (-(y i * finiteQuantumTailCharge i x))) •
          finiteQuantumMonomial q hq.pow_eq_one (x + y)) ∧
    MembranePairComplete supportBase ∧
    MembranePairComplete supportLinear ∧
    MembranePairComplete supportQuadratic ∧
    Nat.choose r 2 ≤ Fintype.card Hbase * Nat.choose Δbase 2 ∧
    Nat.choose r 2 ≤ Fintype.card Hlin * Nat.choose Δlin 2 ∧
    Nat.choose r 2 ≤ Fintype.card Hquad * Nat.choose Δquad 2 := by
  have hpower :
      ∀ c,
        (finiteQuantumWaringSymbol
          (d := d) q hq.pow_eq_one a.mulVecLin c) ^ d =
          MvPolynomial.eval c (mvWaringPolynomial d a) •
            (LinearMap.id :
              Module.End K (FiniteQuantumState (Fin s) d → K)) := by
    intro c
    rw [eval_mvWaringPolynomial]
    exact finiteQuantumTorusSymbol_pow q hq (a.mulVecLin c)
  have hbase :=
    smoothMvWaring_normalForm_holographicLocalityUniversality
      q hq a hsmooth supportBase Δbase hmembraneBase hlocalBase
  have hlinear :=
    linearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
      q hq hd
      (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
      (fun c => MvPolynomial.eval c (mvWaringPolynomial d a))
      hpower
      (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))
      finiteQuantumRoot_ne_zero
  have hdetectors :=
    principalSymbolDetectorCompression_localityUniversality
      hr q hq hd
      (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin)
      (fun c => MvPolynomial.eval c (mvWaringPolynomial d a))
      hpower
      (finiteQuantumRoot (K := K) (ι := Fin s) (d := d))
      finiteQuantumRoot_ne_zero
      supportLinear supportQuadratic Δlin Δquad
      hmembraneLinear hmembraneQuadratic hlocalLinear hlocalQuadratic
  exact
    ⟨hbase.1.1.trans hlinear.1.symm,
      hdetectors.1,
      hbase.1.2.1,
      hdetectors.2.1,
      hdetectors.2.2.1,
      hdetectors.2.2.2.1,
      hbase.1.2.2.1,
      hbase.1.2.2.2,
      hbase.2.1,
      hdetectors.2.2.2.2.1,
      hdetectors.2.2.2.2.2.1,
      hbase.2.2,
      hdetectors.2.2.2.2.2.2.1,
      hdetectors.2.2.2.2.2.2.2⟩

end

end GaloisForLFunctions.HTGeometry
