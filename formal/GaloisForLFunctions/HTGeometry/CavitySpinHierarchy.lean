import GaloisForLFunctions.HTGeometry.CavityInteractionCoefficients
import GaloisForLFunctions.HTGeometry.DiscreteTimeCrystalSpinChain
/-!
# Nonlinear cavity hierarchy in finite-spin observables

The higher-order generator of arXiv:2608.14343 is instantiated on the collective
observables used for arXiv:2609.04037. Exact commutation, global-kick conjugation,
and the full Fisher covariance sum hold at every truncation order. The shear
identity is algebraic; no short-time or Gaussian approximation is asserted.
-/

open scoped BigOperators Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- A finite nonlinear hierarchy in a single observable, with real coupling coefficients. -/
def finitePolynomialGenerator {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {m : ℕ} (c : Fin m → ℝ) : Matrix n n ℂ :=
  ∑ k, (c k : ℂ) • A ^ (k.val + 1)
/-- Every nonlinear hierarchy commutes with its underlying observable. -/
theorem finitePolynomialGenerator_commute {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {m : ℕ} (c : Fin m → ℝ) :
    Commute (finitePolynomialGenerator A c) A := by
  classical
  change (∑ k, (c k : ℂ) • A ^ (k.val + 1)) * A =
    A * (∑ k, (c k : ℂ) • A ^ (k.val + 1))
  rw [Finset.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.smul_mul, Matrix.mul_smul, ← pow_succ, ← pow_succ']
/-- Nonlinear Fisher information includes every covariance between different interaction orders. -/
theorem pureGeneratorQuantumFisher_finitePolynomialGenerator
    {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : n → ℂ) (A : Matrix n n ℂ) {m : ℕ} (c : Fin m → ℝ) :
    pureGeneratorQuantumFisher ψ (finitePolynomialGenerator A c) =
      4 * ∑ k, ∑ l, c k * c l * QuantumAlg.qCov ψ (A ^ (k.val + 1)) (A ^ (l.val + 1)) := by
  classical
  unfold pureGeneratorQuantumFisher finitePolynomialGenerator
  rw [QuantumAlg.qCov_sum_ofReal_smul_left]
  simp_rw [QuantumAlg.qCov_sum_ofReal_smul_right, Finset.mul_sum, mul_assoc]
/-- Exact covariance decomposition for a shear; cross terms remain visible at every finite size. -/
theorem qCov_exact_shear {n : Type*} [Fintype n]
    (ψ : n → ℂ) (Y F : Matrix n n ℂ) (t : ℝ) :
    QuantumAlg.qCov ψ (Y + ((-t : ℝ) : ℂ) • F) (Y + ((-t : ℝ) : ℂ) • F) =
      QuantumAlg.qCov ψ Y Y - t * (QuantumAlg.qCov ψ Y F + QuantumAlg.qCov ψ F Y) +
        t ^ 2 * QuantumAlg.qCov ψ F F := by
  rw [QuantumAlg.qCov_add_left]
  simp_rw [QuantumAlg.qCov_add_right, QuantumAlg.qCov_ofReal_smul_left,
    QuantumAlg.qCov_ofReal_smul_right]
  ring
/-- Cavity coefficients supply an actual nonlinear collective-spin generator in the existing corpus. -/
def finiteCavitySpinGenerator
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (weights : σ → ℂ) (η q d D : ℝ) (m : ℕ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePolynomialGenerator (weightedLongitudinalObservable weights)
    (fun k : Fin m => cavityInteractionCoeff η q d D k.val)
/-- The cavity hierarchy preserves its collective longitudinal observable at every truncation order. -/
theorem finiteCavitySpinGenerator_commute
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (weights : σ → ℂ) (η q d D : ℝ) (m : ℕ) :
    Commute (finiteCavitySpinGenerator weights η q d D m)
      (weightedLongitudinalObservable weights) :=
  finitePolynomialGenerator_commute _ _
/-- Exact Fisher/correlation law for the cavity hierarchy in the finite spin-chain corpus. -/
theorem finiteCavitySpinGenerator_quantumFisher
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (weights : σ → ℂ)
    (η q d D : ℝ) (m : ℕ) :
    pureGeneratorQuantumFisher ψ (finiteCavitySpinGenerator weights η q d D m) =
      4 * ∑ k : Fin m, ∑ l : Fin m,
        cavityInteractionCoeff η q d D k.val * cavityInteractionCoeff η q d D l.val *
          QuantumAlg.qCov ψ (weightedLongitudinalObservable weights ^ (k.val + 1))
            (weightedLongitudinalObservable weights ^ (l.val + 1)) :=
  pureGeneratorQuantumFisher_finitePolynomialGenerator _ _ _
/-- Perfect-X conjugation transports all powers, not only the linear and quadratic spin sectors. -/
theorem globalXPauliKick_conj_pow
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) (n : ℕ) :
    globalXPauliKick σ * A ^ n * globalXPauliKick σ =
      (globalXPauliKick σ * A * globalXPauliKick σ) ^ n := by
  induction n with
  | zero => simp [globalXPauliKick_mul_self]
  | succ n ih => rw [pow_succ, globalXPauliKick_conj_mul, ih, ← pow_succ]
/-- A global half-turn exactly reverses the longitudinal argument of every polynomial hierarchy. -/
theorem globalXPauliKick_conj_finitePolynomialGenerator
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (weights : σ → ℂ) {m : ℕ} (c : Fin m → ℝ) :
    globalXPauliKick σ * finitePolynomialGenerator (weightedLongitudinalObservable weights) c *
        globalXPauliKick σ = finitePolynomialGenerator (-weightedLongitudinalObservable weights) c := by
  classical
  unfold finitePolynomialGenerator
  rw [Matrix.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_smul, Matrix.smul_mul, globalXPauliKick_conj_pow,
    globalXPauliKick_conj_weightedLongitudinal]
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra
/-- Exact exponential dynamics preserve longitudinal magnetization for the full finite hierarchy. -/
theorem finiteCavitySpinEvolution_commute
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (weights : σ → ℂ) (η q d D t : ℝ) (m : ℕ) :
    Commute (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      finiteCavitySpinGenerator weights η q d D m)) (weightedLongitudinalObservable weights) := by
  exact ((finiteCavitySpinGenerator_commute weights η q d D m).smul_left
    (-Complex.I * (t : ℂ))).exp_left
end
end GaloisForLFunctions.HTGeometry
