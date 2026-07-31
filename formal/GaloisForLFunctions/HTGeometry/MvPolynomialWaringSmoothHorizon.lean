import GaloisForLFunctions.HTGeometry.FiniteQuantumWaringHorizon
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Smooth Waring forms have maximal quantum horizons

For a Waring polynomial `P = ∑ᵢ ℓᵢ^d`, every vector annihilated by all `ℓᵢ` is a
nonzero singular point of the projective hypersurface unless that vector is zero.  Consequently
projective smoothness removes the only remaining hypothesis in the finite quantum principal-symbol
theorem: the Waring coefficient map is automatically injective.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {d m n : ℕ} [NeZero d] [Fact (1 < d)]

/-- The linear polynomial given by one row of a Waring coefficient matrix. -/
def mvWaringLinearPolynomial
    (a : Matrix (Fin n) (Fin m) K) (i : Fin n) :
    MvPolynomial (Fin m) K :=
  ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j

/-- The degree-`d` sum-of-powers polynomial associated to a coefficient matrix. -/
def mvWaringPolynomial
    (d : ℕ) (a : Matrix (Fin n) (Fin m) K) :
    MvPolynomial (Fin m) K :=
  ∑ i, mvWaringLinearPolynomial a i ^ d

/-- Algebraic projective smoothness: every nonzero affine point on the cone has a nonzero
partial derivative. -/
def MvPolynomialProjectivelySmooth
    (P : MvPolynomial (Fin m) K) : Prop :=
  ∀ v : Fin m → K, v ≠ 0 → MvPolynomial.eval v P = 0 →
    ∃ j, MvPolynomial.eval v (MvPolynomial.pderiv j P) ≠ 0

omit [CharZero K] in
@[simp]
theorem eval_mvWaringLinearPolynomial
    (a : Matrix (Fin n) (Fin m) K) (i : Fin n) (v : Fin m → K) :
    MvPolynomial.eval v (mvWaringLinearPolynomial a i) =
      a.mulVecLin v i := by
  classical
  simp [mvWaringLinearPolynomial,
    Matrix.mulVec, dotProduct]

omit [NeZero d] [Fact (1 < d)] in
omit [CharZero K] in
/-- Evaluation of the Waring polynomial is exactly the scalar potential used by the finite
quantum packet. -/
theorem eval_mvWaringPolynomial
    (a : Matrix (Fin n) (Fin m) K) (v : Fin m → K) :
    MvPolynomial.eval v (mvWaringPolynomial d a) =
      finiteQuantumWaringPotential d a.mulVecLin v := by
  classical
  simp [mvWaringPolynomial, finiteQuantumWaringPotential,
    finiteQuantumDiagonalPotential, eval_mvWaringLinearPolynomial]

omit [NeZero d] in
omit [CharZero K] in
/-- Any vector killed by every Waring linear form kills every partial derivative of the Waring
polynomial. -/
theorem eval_pderiv_mvWaringPolynomial_eq_zero_of_mem_ker
    (a : Matrix (Fin n) (Fin m) K) (v : Fin m → K)
    (hv : v ∈ LinearMap.ker a.mulVecLin) (j : Fin m) :
    MvPolynomial.eval v (MvPolynomial.pderiv j (mvWaringPolynomial d a)) = 0 := by
  classical
  have hrow : ∀ i, MvPolynomial.eval v (mvWaringLinearPolynomial a i) = 0 := by
    intro i
    rw [eval_mvWaringLinearPolynomial]
    exact congrFun (LinearMap.mem_ker.mp hv) i
  rw [mvWaringPolynomial, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.pderiv_pow, MvPolynomial.eval_mul,
    MvPolynomial.eval_mul, MvPolynomial.eval_pow, hrow i]
  have hdgt : 1 < d := Fact.out
  have hdsub : d - 1 ≠ 0 := by omega
  simp [hdsub]

omit [CharZero K] in
/-- **Smoothness forces Waring concision.**  If the Waring hypersurface is projectively smooth,
its linear forms separate every vector. -/
theorem mvWaring_mulVecLin_injective_of_projectivelySmooth
    (a : Matrix (Fin n) (Fin m) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a)) :
    Function.Injective a.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have hP0 : MvPolynomial.eval v (mvWaringPolynomial d a) = 0 := by
    rw [eval_mvWaringPolynomial]
    simp [finiteQuantumWaringPotential, finiteQuantumDiagonalPotential,
      LinearMap.mem_ker.mp hv, NeZero.ne d]
  obtain ⟨j, hj⟩ := hsmooth v hv0 hP0
  exact hj (eval_pderiv_mvWaringPolynomial_eq_zero_of_mem_ker a v hv j)

/-- **Smooth all-degree pre-temporal horizon theorem.**  A projectively smooth Waring form has
an exact rational differential-field horizon and a maximal exterior derivation commutator in the
same explicit finite quantum packet. -/
theorem smoothMvWaring_horizon_and_maximalPrincipalSymbol
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
              (d := d) q hq.pow_eq_one a.mulVecLin))) := by
  have hmain := finiteQuantumWaring_horizon_and_maximalPrincipalSymbol
    q hq a.mulVecLin
      (mvWaring_mulVecLin_injective_of_projectivelySmooth a hsmooth)
  refine ⟨?_, hmain.2⟩
  rw [hmain.1]
  ext v
  change finiteQuantumWaringPotential d a.mulVecLin v = 0 ↔
    MvPolynomial.eval v (mvWaringPolynomial d a) = 0
  rw [eval_mvWaringPolynomial]

end

end GaloisForLFunctions.HTGeometry
