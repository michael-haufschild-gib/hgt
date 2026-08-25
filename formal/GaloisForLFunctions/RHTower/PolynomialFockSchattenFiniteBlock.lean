import GaloisForLFunctions.RHTower.PolynomialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.Sieve.LargeSieveDuality
import GaloisForLFunctions.HTGeometry.SchattenFiniteRankEnergy

/-!
# Finite critical-prime Fock blocks

Finite weighted kernel Gram blocks are the local pieces of the critical-prime incidence operator.
This module gives their exact rank-one expansion, projective mass, and operator/Schatten energy
bounds from a local prime tangent-ball overlap estimate.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A rank-one continuous operator has rank at most one. -/
theorem hasRankLE_rankOne (x y : H) :
    HasRankLE (InnerProductSpace.rankOne ℂ x y) 1 := by
  classical
  let s : Finset H := {x}
  refine ⟨Submodule.span ℂ ((s : Finset H) : Set H),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet s), ?_, ?_⟩
  · exact (finrank_span_finset_le_card s).trans (by simp [s])
  · intro z
    rw [InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.mpr (by simp [s])))

/-- Gram operator of a finite vector family. -/
def finiteGramBlock {ι : Type*} (s : Finset ι) (φ : ι → H) : H →L[ℂ] H :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (φ i) (φ i)

@[simp] theorem finiteGramBlock_apply
    {ι : Type*} (s : Finset ι) (φ : ι → H) (x : H) :
    finiteGramBlock s φ x = ∑ i ∈ s, inner ℂ (φ i) x • φ i := by
  simp [finiteGramBlock, InnerProductSpace.rankOne_apply]

/-- A finite Bessel estimate controls the operator norm of its Gram block with the same constant. -/
theorem norm_finiteGramBlock_le_of_bessel
    {ι : Type*} (s : Finset ι) (φ : ι → H) {B : ℝ} (hB : 0 ≤ B)
    (hbessel : ∀ x : H, ∑ i ∈ s, ‖inner ℂ (φ i) x‖ ^ 2 ≤ B * ‖x‖ ^ 2) :
    ‖finiteGramBlock s φ‖ ≤ B := by
  apply opNorm_le_bound _ hB
  intro x
  have hsyn := Sieve.norm_sum_smul_sq_le_of_bessel s φ hB hbessel
    (fun i => inner ℂ (φ i) x)
  rw [← finiteGramBlock_apply] at hsyn
  have henergy := hbessel x
  have hsq : ‖finiteGramBlock s φ x‖ ^ 2 ≤ (B * ‖x‖) ^ 2 := by
    calc
      ‖finiteGramBlock s φ x‖ ^ 2 ≤
          B * ∑ i ∈ s, ‖inner ℂ (φ i) x‖ ^ 2 := hsyn
      _ ≤ B * (B * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left henergy hB
      _ = (B * ‖x‖) ^ 2 := by ring
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg hB (norm_nonneg _))] at hsqrt
  exact hsqrt

/-- Prime-weighted normalized polynomial-Fock kernel vector. -/
def polynomialCriticalPrimeWeightedKernel
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) : MomentFock :=
  (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) •
    criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith)) p

@[simp] theorem inner_polynomialCriticalPrimeWeightedKernel
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) (f : MomentFock) :
    inner ℂ (polynomialCriticalPrimeWeightedKernel m hm p) f =
      criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel (polynomialMomentFockData m (by linarith))) p f := by
  rw [polynomialCriticalPrimeWeightedKernel, inner_smul_left,
    criticalPrimeKernelRestriction_apply]
  simp

@[simp] theorem normSq_polynomialCriticalPrimeWeightedKernel
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) :
    ‖polynomialCriticalPrimeWeightedKernel m hm p‖ ^ 2 =
      criticalPrimeSamplingWeight p := by
  rw [polynomialCriticalPrimeWeightedKernel, norm_smul,
    norm_criticalPrimeMomentFockKernel, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact (criticalPrimeSamplingWeight_pos p).le

/-- One positive weighted prime-kernel atom. -/
def polynomialCriticalPrimeKernelAtom
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) : MomentFock →L[ℂ] MomentFock :=
  InnerProductSpace.rankOne ℂ
    (polynomialCriticalPrimeWeightedKernel m hm p)
    (polynomialCriticalPrimeWeightedKernel m hm p)

theorem polynomialCriticalPrimeKernelAtom_hasRankLE_one
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) :
    HasRankLE (polynomialCriticalPrimeKernelAtom m hm p) 1 := by
  exact hasRankLE_rankOne _ _

@[simp] theorem norm_polynomialCriticalPrimeKernelAtom
    (m : ℝ) (hm : 4 ≤ m) (p : Nat.Primes) :
    ‖polynomialCriticalPrimeKernelAtom m hm p‖ = criticalPrimeSamplingWeight p := by
  rw [polynomialCriticalPrimeKernelAtom, InnerProductSpace.norm_rankOne,
    ← pow_two, normSq_polynomialCriticalPrimeWeightedKernel]

/-- Literal finite weighted prime-kernel Gram block. -/
def polynomialCriticalPrimeKernelBlock
    (m : ℝ) (hm : 4 ≤ m) (P : Finset Nat.Primes) : MomentFock →L[ℂ] MomentFock :=
  ∑ p ∈ P, polynomialCriticalPrimeKernelAtom m hm p

@[simp] theorem polynomialCriticalPrimeKernelBlock_eq_finiteGramBlock
    (m : ℝ) (hm : 4 ≤ m) (P : Finset Nat.Primes) :
    polynomialCriticalPrimeKernelBlock m hm P =
      finiteGramBlock P (polynomialCriticalPrimeWeightedKernel m hm) := rfl

/-- Local tangent-ball overlap controls the finite prime block in operator norm. -/
theorem norm_polynomialCriticalPrimeKernelBlock_le
    {m B : ℝ} (hm : 4 ≤ m) (P : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ P, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B) :
    ‖polynomialCriticalPrimeKernelBlock m hm P‖ ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B := by
  rw [polynomialCriticalPrimeKernelBlock_eq_finiteGramBlock]
  apply norm_finiteGramBlock_le_of_bessel
  · exact mul_nonneg (Real.exp_nonneg _) (by
      have h := hoverlap 0
      exact le_trans (Finset.sum_nonneg fun p _ => by
        split_ifs
        · exact (criticalPrimeSamplingWeight_pos p).le
        · exact le_rfl) h)
  · intro f
    simpa using sum_normSq_criticalPrimeKernelRestriction_polynomial_le hm f P hoverlap

/-- Schatten energy of a finite prime block is bounded by local overlap to power `q-1` times its
exact prime projective mass. -/
theorem schattenEnergy_polynomialCriticalPrimeKernelBlock_le
    {m B q : ℝ} (hm : 4 ≤ m) (hq : 1 ≤ q) (P : Finset Nat.Primes)
    (hoverlap : ∀ z : ℂ,
      (∑ p ∈ P, if dist z ((Real.log (p : ℝ) : ℝ) : ℂ) <
          polynomialFockTangentRadius m (Real.log (p : ℝ))
        then criticalPrimeSamplingWeight p else 0) ≤ B) :
    schattenNorm q (polynomialCriticalPrimeKernelBlock m hm P) ^ q ≤
      (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B) ^ (q - 1) *
        ∑ p ∈ P, criticalPrimeSamplingWeight p := by
  have hbase :=
    schattenEnergy_finsetSum_le_norm_rpow_sub_one_mul_sum_norm_of_rankOne
      hq (fun p => polynomialCriticalPrimeKernelAtom m hm p)
      (fun p => polynomialCriticalPrimeKernelAtom_hasRankLE_one m hm p) P
  have hnorm := norm_polynomialCriticalPrimeKernelBlock_le hm P hoverlap
  calc
    schattenNorm q (polynomialCriticalPrimeKernelBlock m hm P) ^ q ≤
        ‖polynomialCriticalPrimeKernelBlock m hm P‖ ^ (q - 1) *
          ∑ p ∈ P, criticalPrimeSamplingWeight p := by
      simpa [polynomialCriticalPrimeKernelBlock,
        norm_polynomialCriticalPrimeKernelAtom] using hbase
    _ ≤ (Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) * B) ^ (q - 1) *
          ∑ p ∈ P, criticalPrimeSamplingWeight p := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) hnorm (sub_nonneg.mpr hq))
        (Finset.sum_nonneg fun p _ => (criticalPrimeSamplingWeight_pos p).le)

end

end RHTower
