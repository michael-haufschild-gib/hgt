import GaloisForLFunctions.HTGeometry.ConservativeDissipativeTensorKraus
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs

/-!
# Composite thermal quantum dynamical semigroup

The conservative–dissipative mechanism of arXiv:2609.04530 is applied to two
thermal spins with independent raw rate and bath coordinates. Sixteen explicit
Kraus outcomes construct the channel. The matrix-unit tensor expansion proves
the identity and semigroup laws on every composite matrix, not only products.
The product bath is proved positive, normalized, and fixed, and is identified
with the tensor product of the existing Gibbs carriers.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Sixteen constructed Kraus outcomes for two independently damped thermal spins. -/
def spinThermalTensorKraus (a u b v : ℝ) (t : NNReal) :
    FiniteRectangularKrausChannel 4 4 ((Fin 2 ⊕ Fin 2) × (Fin 2 ⊕ Fin 2)) :=
  rectangularSpinKrausTensor (spinThermalKraus a u t) (spinThermalKraus b v t)

/-- Completely positive trace-preserving two-spin evolution in the existing channel type. -/
def spinThermalTensorChannel (a u b v : ℝ) (t : NNReal) : QuantumChannel (Fin 4) :=
  quantumChannelFromRectangularKraus (spinThermalTensorKraus a u b v t)

/-- Exact local action on every product matrix, including nonpositive raw factors. -/
theorem spinThermalTensorChannel_product (a u b v : ℝ) (t : NNReal)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinThermalTensorChannel a u b v t).map (finiteSpinTensorMatrix A B) =
      finiteSpinTensorMatrix ((spinThermalChannel a u t).map A) ((spinThermalChannel b v t).map B) := by
  exact finiteSpinTensorMatrix_kraus_sum (spinThermalKraus a u t).operator (spinThermalKraus b v t).operator A B

/-- The same constructed channel as a linear map, for finite matrix expansions. -/
def spinThermalTensorLinear (a u b v : ℝ) (t : NNReal) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := (spinThermalTensorChannel a u b v t).map
  map_add' := (spinThermalTensorChannel a u b v t).map_add
  map_smul' := (spinThermalTensorChannel a u b v t).map_smul

/-- Zero time is the identity on every composite matrix, not only on product states. -/
theorem spinThermalTensorChannel_zero (a u b v : ℝ) : spinThermalTensorChannel a u b v 0 = 1 := by
  apply QuantumChannel.ext
  funext ρ
  change spinThermalTensorLinear a u b v 0 ρ = ρ
  rw [finiteSpinTensorMatrix_expansion (m := 2) (n := 2) ρ]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single i.1 j.1 (ρ (finProdFinEquiv i) (finProdFinEquiv j))
  let B : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single i.2 j.2 1
  change (spinThermalTensorChannel a u b v 0).map (finiteSpinTensorMatrix A B) = finiteSpinTensorMatrix A B
  rw [spinThermalTensorChannel_product, spinThermalChannel_zero, spinThermalChannel_zero]
  rfl

/-- Full semigroup law on arbitrary composite inputs, including entangled matrices. -/
theorem spinThermalTensorChannel_add (a u b v : ℝ) (s t : NNReal) :
    spinThermalTensorChannel a u b v (s + t) = spinThermalTensorChannel a u b v s * spinThermalTensorChannel a u b v t := by
  apply QuantumChannel.ext
  funext ρ
  change spinThermalTensorLinear a u b v (s + t) ρ =
    spinThermalTensorLinear a u b v s (spinThermalTensorLinear a u b v t ρ)
  rw [finiteSpinTensorMatrix_expansion (m := 2) (n := 2) ρ]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single i.1 j.1 (ρ (finProdFinEquiv i) (finProdFinEquiv j))
  let B : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single i.2 j.2 1
  change (spinThermalTensorChannel a u b v (s + t)).map (finiteSpinTensorMatrix A B) =
    (spinThermalTensorChannel a u b v s).map ((spinThermalTensorChannel a u b v t).map (finiteSpinTensorMatrix A B))
  rw [spinThermalTensorChannel_product, spinThermalTensorChannel_product, spinThermalTensorChannel_product,
    spinThermalChannel_add, spinThermalChannel_add]
  rfl

/-- The two-spin construction is an actual quantum dynamical semigroup. -/
def spinThermalTensorSemigroup (a u b v : ℝ) : DynamicalSemigroup (Fin 4) where
  ch := spinThermalTensorChannel a u b v
  ch_zero := spinThermalTensorChannel_zero a u b v
  ch_add := spinThermalTensorChannel_add a u b v

/-- Product of the constructed stationary bath densities. -/
def spinThermalTensorBath (u v : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  finiteSpinTensorMatrix (spinBathDensity u) (spinBathDensity v)

/-- The product bath is positive by the existing Kronecker positivity theorem. -/
theorem spinThermalTensorBath_posSemidef (u v : ℝ) : (spinThermalTensorBath u v).PosSemidef := by
  change ((spinBathDensity u ⊗ₖ spinBathDensity v).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).PosSemidef
  exact ((spinBathDensity_posSemidef u).kronecker (spinBathDensity_posSemidef v)).submatrix _

/-- Product-bath normalization is derived from the local trace laws. -/
theorem spinThermalTensorBath_trace (u v : ℝ) : Matrix.trace (spinThermalTensorBath u v) = 1 := by
  rw [spinThermalTensorBath, finiteSpinTensorMatrix_trace, spinBathDensity_trace, spinBathDensity_trace, mul_one]

/-- The exact stationary composite bath is fixed at every physical time. -/
theorem spinThermalTensorChannel_bath_fixed (a u b v : ℝ) (t : NNReal) :
    (spinThermalTensorChannel a u b v t).map (spinThermalTensorBath u v) = spinThermalTensorBath u v := by
  rw [spinThermalTensorBath, spinThermalTensorChannel_product, spinThermalChannel_bath_fixed, spinThermalChannel_bath_fixed]

/-- Raw pairs of chart coordinates construct normalized positive two-spin input states. -/
theorem spinThermalTensor_pure_state (z w : ℂ) :
    (finiteSpinTensorMatrix (spinChartDensity z) (spinChartDensity w)).PosSemidef ∧
      Matrix.trace (finiteSpinTensorMatrix (spinChartDensity z) (spinChartDensity w)) = 1 := by
  constructor
  · change ((spinChartDensity z ⊗ₖ spinChartDensity w).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).PosSemidef
    exact ((spinChartDensity_posSemidef z).kronecker (spinChartDensity_posSemidef w)).submatrix _
  · rw [finiteSpinTensorMatrix_trace, spinChartDensity_trace, spinChartDensity_trace, mul_one]

/-- Local Gibbs biases give a literal tensor product of the existing Gibbs carriers. -/
theorem spinThermalTensorBath_gibbs (u v : ℝ) :
    spinThermalTensorBath (Real.exp (-u)) (Real.exp (-v)) =
      finiteSpinTensorMatrix (qubitDensity 0 u) (qubitDensity 0 v) := by
  rw [spinThermalTensorBath, spinBathDensity_gibbs, spinBathDensity_gibbs]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
