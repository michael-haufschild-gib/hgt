import GaloisForLFunctions.HTGeometry.FiniteQuantumTorusRepresentation
import GaloisForLFunctions.HTGeometry.QuantumBinomialRootOfUnity

/-!
# Finite quantum Waring horizons

A primitive root of unity and an explicit finite phase-space packet realize every finite sum of
degree-`d` powers as an exact scalar generalized-Clifford relation.  At the same time, every
two-plane in an injectively parametrized law space survives as a nonzero derivation commutator.

Thus the scalar dependence horizon and the exterior incompatibility symbol coexist in one finite
pre-temporal packet: the first records the hypersurface, while the second retains all oriented
two-coordinate information that the scalar equation forgets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- The diagonal degree-`d` scalar constraint carried by the finite quantum packet. -/
def finiteQuantumDiagonalPotential (d : ℕ) (c : Fin n → K) : K :=
  ∑ i, c i ^ d

/-- The explicit finite quantum-torus linear pencil. -/
def finiteQuantumTorusSymbol
    (q : K) (hqpow : q ^ d = 1) :
    (Fin n → K) →ₗ[K]
      Module.End K (FiniteQuantumState (Fin n) d → K) :=
  quantumGeneratorSymbol
    (fun i : Fin n ↦ finiteQuantumGenerator d q hqpow i)

/-- The primitive-order power of the finite quantum pencil is exactly its scalar diagonal
potential.  No mixed word survives. -/
theorem finiteQuantumTorusSymbol_pow
    (q : K) (hq : IsPrimitiveRoot q d) (c : Fin n → K) :
    (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one c) ^ d =
      finiteQuantumDiagonalPotential d c •
        (LinearMap.id : Module.End K (FiniteQuantumState (Fin n) d → K)) := by
  rw [finiteQuantumTorusSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply,
    quantumMultinomial_fin_smul_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (fun i : Fin n ↦ finiteQuantumGenerator d q hq.pow_eq_one i) c
      (fun i j hij ↦ finiteQuantumGenerator_mul_of_lt q hq.pow_eq_one hij)]
  simp_rw [finiteQuantumGenerator_pow_degree]
  rw [← Finset.sum_smul]
  rfl

/-- The phase-space delta at the origin is nonzero. -/
theorem finiteQuantumRoot_ne_zero :
    (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : FiniteQuantumState (Fin n) d)
  simpa [finiteQuantumRoot] using h0

/-- **Exact all-degree finite quantum horizon.**  Complete differential dependence in the
rational observable field occurs exactly on the diagonal degree-`d` hypersurface. -/
theorem finiteQuantumTorusField_dependenceHorizon_eq
    (q : K) (hq : IsPrimitiveRoot q d) :
    {c : Fin n → K | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftFieldJet
        (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one c)
        (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)))} =
      {c : Fin n → K | finiteQuantumDiagonalPotential d c = 0} := by
  apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
    (finiteQuantumTorusSymbol (d := d) q hq.pow_eq_one)
    (finiteQuantumDiagonalPotential d)
    d (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
    (finiteQuantumRoot (K := K) (ι := Fin n) (d := d))
    finiteQuantumRoot_ne_zero
  exact finiteQuantumTorusSymbol_pow q hq

variable {V : Type v} [AddCommGroup V] [Module K V]

/-- A finite Waring power sum, viewed as a scalar law on an arbitrary linear parameter space. -/
def finiteQuantumWaringPotential
    (d : ℕ) (L : V →ₗ[K] (Fin n → K)) (v : V) : K :=
  finiteQuantumDiagonalPotential d (L v)

/-- Pull the canonical finite quantum packet back along a family of linear forms. -/
def finiteQuantumWaringSymbol
    (q : K) (hqpow : q ^ d = 1) (L : V →ₗ[K] (Fin n → K)) :
    V →ₗ[K] Module.End K (FiniteQuantumState (Fin n) d → K) :=
  (finiteQuantumTorusSymbol (d := d) q hqpow).comp L

/-- Every finite Waring presentation has an exact differential-field dependence horizon, with
no representation-existence assumption. -/
theorem finiteQuantumWaringField_dependenceHorizon_eq
    (q : K) (hq : IsPrimitiveRoot q d) (L : V →ₗ[K] (Fin n → K)) :
    {v : V | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftFieldJet
        (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one L v)
        (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)))} =
      {v : V | finiteQuantumWaringPotential d L v = 0} := by
  apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
    (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one L)
    (finiteQuantumWaringPotential d L)
    d (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
    (finiteQuantumRoot (K := K) (ι := Fin n) (d := d))
    finiteQuantumRoot_ne_zero
  intro v
  exact finiteQuantumTorusSymbol_pow q hq (L v)

/-- An injective family of Waring linear forms retains every bivector of the law space after
shift suspension: no two-plane incompatibility is lost by scalarization. -/
theorem finiteQuantumWaring_derivationCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (L : V →ₗ[K] (Fin n → K)) (hL : Function.Injective L) :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one L))) := by
  exact finiteQuantumTorus_derivationCommutatorMap_injective
    q hq.pow_eq_one (hq.ne_one Fact.out) L hL

/-- **Pre-temporal scalar/exterior separation theorem.**  One explicit finite packet realizes
the Waring scalar horizon exactly and, whenever the linear forms separate law directions,
simultaneously carries a faithful exterior commutator symbol. -/
theorem finiteQuantumWaring_horizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d)
    (L : V →ₗ[K] (Fin n → K)) (hL : Function.Injective L) :
    ({v : V | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one L v)
          (finiteQuantumRoot (K := K) (ι := Fin n) (d := d)))} =
        {v : V | finiteQuantumWaringPotential d L v = 0}) ∧
      Function.Injective
        (derivationCommutatorMap
          (generalizedCliffordShiftFieldDerivationLaw
            (finiteQuantumWaringSymbol (d := d) q hq.pow_eq_one L))) := by
  exact ⟨finiteQuantumWaringField_dependenceHorizon_eq q hq L,
    finiteQuantumWaring_derivationCommutatorMap_injective q hq L hL⟩

end

end GaloisForLFunctions.HTGeometry
