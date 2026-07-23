import GaloisForLFunctions.HTGeometry.FiniteQuantumNormalForm
import GaloisForLFunctions.HTGeometry.MvPolynomialWaringSmoothHorizon

/-!
# Smooth Waring quantum normal-form universality

Projective smoothness makes a Waring coefficient map concise, hence its finite quantum packet has
the exact hypersurface horizon and maximal exterior commutator symbol.  That packet is built from
the same finite quantum torus whose ordered monomials carry a complete independent twisted normal
form.  The combined law extends the normal-form horizon package from diagonal Fermat forms to every
projectively smooth Waring presentation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {d m n : ℕ} [NeZero d] [Fact (1 < d)]

/-- **Smooth Waring quantum normal-form universality law.**  A projectively smooth Waring form has
its exact finite quantum dependence horizon, an injective exterior derivation symbol, and a full
linearly independent twisted-monomial normal form in the same ambient packet. -/
theorem smoothMvWaring_normalForm_maximalHorizon
    (q : K) (hq : IsPrimitiveRoot q d)
    (a : Matrix (Fin n) (Fin m) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a)) :
    ({v : Fin m → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one a.mulVecLin v)
          (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)))} =
        {v : Fin m → K |
          MvPolynomial.eval v (mvWaringPolynomial d a) = 0}) ∧
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw
            (finiteQuantumWaringSymbol
              (d := d) q hq.pow_eq_one a.mulVecLin))) ∧
      LinearIndependent K
        (finiteQuantumMonomial (K := K) (ι := Fin n) (d := d) q hq.pow_eq_one) ∧
      ∀ x y : Fin n → ZMod d,
        finiteQuantumMonomial q hq.pow_eq_one x *
            finiteQuantumMonomial q hq.pow_eq_one y =
          (∏ i, finiteQuantumCharacter d q hq.pow_eq_one
              (-(y i * finiteQuantumTailCharge i x))) •
            finiteQuantumMonomial q hq.pow_eq_one (x + y) := by
  have hhorizon := smoothMvWaring_horizon_and_maximalPrincipalSymbol
    q hq a hsmooth
  exact ⟨hhorizon.1, hhorizon.2,
    finiteQuantumMonomial_linearIndependent q hq.pow_eq_one,
    fun x y => finiteQuantumMonomial_mul q hq.pow_eq_one x y⟩

end

end GaloisForLFunctions.HTGeometry
