import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction.Readout
import GaloisForLFunctions.RHTower.ZetaEulerLogPrimeSum

/-! # Complex thermal partition reconstructed from unlabelled coincidence events -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction

open MeasureTheory

/-- At u = 1/p this test cancels the atomic mass 1/p²
and reads the Euler logarithm of the underlying mode. -/
def eulerResponse (s : ℂ) (u : ℝ) := -Complex.log (1-((u⁻¹:ℝ):ℂ)^(-s))/(u:ℂ)^2

private def primeLog (s : ℂ) (n : ℕ) := -Complex.log (1-(n:ℂ)^(-s))
private def selectedLog (s : ℂ) (n : ℕ) := if n.Prime then primeLog s n else 0

private theorem weighted_response (s : ℂ) (n : ℕ) :
    (weight n:ℂ)*eulerResponse s (node n)=selectedLog s n := by
  by_cases hp : n.Prime
  · have nz : (node n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero))
    rw [weight,if_pos hp,eulerResponse,selectedLog,if_pos hp,Complex.ofReal_pow]
    have val : (node n)⁻¹=(n:ℝ) := inv_inv _
    rw [val,Complex.ofReal_natCast,primeLog]
    exact mul_div_cancel₀ _ (pow_ne_zero 2 nz)
  · simp only [selectedLog,weight,if_neg hp,Complex.ofReal_zero,zero_mul]

private theorem log_support (s : ℂ) :
    Function.support (selectedLog s) ⊆ {n : ℕ | n.Prime} := by
  intro n hn
  by_contra h
  apply hn
  rw [selectedLog,if_neg (show ¬n.Prime from h)]

private theorem log_summable (s : {z : ℂ // 1<z.re}) : Summable (selectedLog s.val) := by
  have hp := _root_.RHTower.summable_primeEulerLog (τ:=s.val.im) s.property
  have eta : _root_.RHTower.zetaLinePoint s.val.re s.val.im=s.val := Complex.re_add_im _
  rw [eta] at hp
  let S : Set ℕ := {n | n.Prime}
  have g : Summable (primeLog s.val ∘ ((↑) : S → ℕ)) := hp
  refine (summable_subtype_iff_indicator.mp g).congr fun n => ?_
  by_cases hn : n.Prime
  · rw [Set.indicator_of_mem (show n∈S from hn),selectedLog,if_pos hn]
  · rw [Set.indicator_of_notMem (show n∉S from hn),selectedLog,if_neg hn]

/-- Absolute summability on the measured spectrum justifies the test even at
temperatures where the response is unbounded near the origin. -/
theorem integrable_response (s : {z : ℂ // 1<z.re}) : Integrable (eulerResponse s.val) reconstructed := by
  rw [reconstructed_eq]
  apply _root_.HTGeometry.integrable_complex_countableWeightedDirac weight_nonneg
  refine (log_summable s).norm.congr fun n => ?_
  have h := congrArg norm (weighted_response s.val n)
  simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_nonneg n)] using h.symm

/-- Exponentiating the integrated Euler response of the measured spectrum
gives the full gas heat trace for complex inverse temperatures. -/
theorem thermal_partition (s : {z : ℂ // 1<z.re}) :
    Complex.exp (∫ u,eulerResponse s.val u ∂reconstructed)=(gibbsOperator s).opTrace := by
  have hi := integrable_response s
  rw [reconstructed_eq,intensity] at hi ⊢
  rw [_root_.HTGeometry.integral_complex_countableWeightedDirac weight_nonneg hi,
    tsum_congr (weighted_response s.val),←tsum_subtype_eq_of_support_subset (log_support s.val),
    partition_eq_zeta]
  change Complex.exp (∑' p : Nat.Primes, selectedLog s.val p.val)=riemannZeta s.val
  have reduced (p : Nat.Primes) : selectedLog s.val p.val= -Complex.log (1-(p:ℂ)^(-s.val)) := if_pos p.property
  rw [tsum_congr reduced]
  exact riemannZeta_eulerProduct_exp_log s.property

#print axioms integrable_response
#print axioms thermal_partition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction
