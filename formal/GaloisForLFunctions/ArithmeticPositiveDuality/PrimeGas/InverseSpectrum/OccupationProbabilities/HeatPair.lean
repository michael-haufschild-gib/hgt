import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Partition
import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison

/-! # The rank-one heat defect and its native and surviving eigenbases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace _root_.RHTower
open scoped InnerProductSpace

abbrev survivingHeat (v : MissingWave) : GasOp := projected (omitLine v.val)^2

/-- The normalized heat image whose outer product is the entire observable defect. -/
def defectVector (v : MissingWave) : Gas := ((‖v.val‖⁻¹:ℝ):ℂ) • criticalOperator v.val

theorem survivingHeat_eq (v : MissingWave) :
    survivingHeat v = squareHeat.val-rankOne ℂ (defectVector v) (defectVector v) := by
  rw [survivingHeat,line_square]
  congr 1
  apply ContinuousLinearMap.ext
  intro y
  change ((‖v.val‖^2:ℝ):ℂ)⁻¹ • (inner ℂ (criticalOperator v.val) y • criticalOperator v.val) =
    inner ℂ (defectVector v) y • defectVector v
  rw [defectVector,inner_smul_left,Complex.conj_ofReal,smul_smul,smul_smul]
  congr 1
  simp only [Complex.ofReal_pow,Complex.ofReal_inv]
  ring

theorem defectVector_norm_sq (v : MissingWave) : ‖defectVector v‖^2 = firstMoment v.val := by
  rw [defectVector,norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),mul_pow,inv_pow,firstMoment,div_eq_mul_inv,mul_comm]

/-- Native eigenvectors numbered in descending energy weight. -/
def occupationMode (n : ℕ) : Gas := HilbertSchmidt.lpBasis ℕ+ (number n)

theorem occupationMode_orthonormal : Orthonormal ℂ occupationMode :=
  (HilbertSchmidt.lpBasis ℕ+).orthonormal.comp number number_injective

theorem nativeHeat_eigen (n : ℕ) : squareHeat.val (occupationMode n) = (occupationWeight n:ℂ) • occupationMode n := by
  rw [occupationMode,HilbertSchmidt.lpBasis_apply]
  change criticalOperator (criticalOperator (modeWave (number n))) = _ • modeWave (number n)
  rw [heat_modeWave,map_smul,heat_modeWave,smul_smul,← sq,← Complex.ofReal_pow]
  rfl

theorem nativeHeat_positive : squareHeat.val.IsPositive := by
  have h := isPositive_adjoint_comp_self criticalOperator
  change (adjoint criticalOperator * criticalOperator).IsPositive at h
  rw [show adjoint criticalOperator = criticalOperator from critical_isPositive.isSelfAdjoint.star_eq] at h
  exact h

theorem nativeHeat_singVal (n : ℕ) : singVal squareHeat.val n = occupationWeight n :=
  (approxNumber_eq_singVal squareHeat.property.2.isCompactOperator n).symm.trans (squareHeat_approxNumber n)

theorem survivingHeat_hs (v : MissingWave) : (survivingHeat v).IsHilbertSchmidt :=
  conserving_square_hs (linePropagator v)

theorem survivingHeat_singVal (v : MissingWave) (n : ℕ) : singVal (survivingHeat v) n = (missingSpectrum v n).val :=
  (approxNumber_eq_singVal (survivingHeat_hs v).isCompactOperator n).symm

theorem survivingHeat_basis (v : MissingWave) : ∃ e : HilbertBasis ℕ ℂ Gas,
    ∀ n, survivingHeat v (e n) = ((missingSpectrum v n).val:ℂ) • e n :=
  exists_physical_heat_basis _ ((missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩)
    (((nonzero_line_conserves_iff _).mpr v.property).2)

#print axioms survivingHeat_eq
#print axioms defectVector_norm_sq
#print axioms occupationMode_orthonormal
#print axioms nativeHeat_eigen
#print axioms nativeHeat_positive
#print axioms nativeHeat_singVal
#print axioms survivingHeat_hs
#print axioms survivingHeat_singVal
#print axioms survivingHeat_basis

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
