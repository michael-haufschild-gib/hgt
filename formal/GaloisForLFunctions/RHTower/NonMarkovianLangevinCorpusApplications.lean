import GaloisForLFunctions.HTGeometry.NonMarkovianLangevinKernel
import GaloisForLFunctions.HTGeometry.GammaDigammaJetFreeness
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness
import GaloisForLFunctions.RHTower.XiJetFreeness
import GaloisForLFunctions.RHTower.XiLogDerivFiniteSpectralDressing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildNonMarkovEdge
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite
import Mathlib.Tactic

set_option maxHeartbeats 800000

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Infinite Schwarzschild/FZZ Bose memory -/

/-- The reciprocal-energy Bose clock at the canonical positive scale, read as a memory kernel. -/
def schwarzschildBoseMemoryKernel : ℝ → ℂ :=
  atomicFourierSeries (_root_.HTGeometry.gammaBoseWeight 1)
    (_root_.HTGeometry.gammaBoseNode 1)

theorem summable_abs_schwarzschildBoseMemoryWeight :
    Summable (fun j : ℕ => |_root_.HTGeometry.gammaBoseWeight 1 j|) := by
  have h := _root_.HTGeometry.summable_gammaBoseWeight_mul_node_abs_pow
    (a := (1 : ℝ)) (by norm_num) 0
  simp only [pow_zero, mul_one] at h
  refine h.congr fun j => ?_
  rw [abs_of_pos (_root_.HTGeometry.gammaBoseWeight_pos (a := (1 : ℝ)) (by norm_num) j)]

theorem norm_schwarzschildBoseMemoryKernel_le_zero (t : ℝ) :
    ‖schwarzschildBoseMemoryKernel t‖ ≤
      ∑' j : ℕ, _root_.HTGeometry.gammaBoseWeight 1 j := by
  unfold schwarzschildBoseMemoryKernel atomicFourierSeries
  have hs : Summable (fun j : ℕ =>
      ((_root_.HTGeometry.gammaBoseWeight 1 j : ℝ) : ℂ) *
        realFourierCharacter (_root_.HTGeometry.gammaBoseNode 1 j) t) := by
    rw [← summable_norm_iff]
    simpa [norm_mul, Real.norm_eq_abs] using summable_abs_schwarzschildBoseMemoryWeight
  calc
    ‖∑' j : ℕ, ((_root_.HTGeometry.gammaBoseWeight 1 j : ℝ) : ℂ) *
        realFourierCharacter (_root_.HTGeometry.gammaBoseNode 1 j) t‖
        ≤ ∑' j : ℕ, ‖((_root_.HTGeometry.gammaBoseWeight 1 j : ℝ) : ℂ) *
          realFourierCharacter (_root_.HTGeometry.gammaBoseNode 1 j) t‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ = ∑' j : ℕ, _root_.HTGeometry.gammaBoseWeight 1 j := by
      apply tsum_congr
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (_root_.HTGeometry.gammaBoseWeight_pos (a := (1 : ℝ)) (by norm_num) j)]
      simp

/-- Existing Schwarzschild/FZZ Bose spectrum is an unconditional positive-definite
non-Markovian memory kernel. -/
theorem positiveDefiniteOnReal_schwarzschildBoseMemoryKernel :
    PositiveDefiniteOnReal schwarzschildBoseMemoryKernel := by
  exact positiveDefinite_atomicFourierSeries_of_nonnegative
    summable_abs_schwarzschildBoseMemoryWeight
    (fun j => (_root_.HTGeometry.gammaBoseWeight_pos (a := (1 : ℝ)) (by norm_num) j).le)

/-! ## Finite bath response as spectral dressing -/

theorem gamma_add_unitFiniteBathMemory_constantCoefficientDifferentiallyTranscendental
    {n : ℕ} (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    _root_.HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (Complex.Gamma +
        finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1)) := by
  rw [finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition]
  exact GaloisForLFunctions.gamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental _

theorem digamma_add_unitFiniteBathMemory_constantCoefficientDifferentiallyTranscendental
    {n : ℕ} (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    _root_.HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (Complex.digamma +
        finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1)) := by
  rw [finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition]
  exact GaloisForLFunctions.digamma_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental _

theorem riemannZeta_add_unitFiniteBathMemory_constantCoefficientDifferentiallyTranscendental
    {n : ℕ} (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    _root_.HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (riemannZeta +
        finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1)) := by
  rw [finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition]
  exact GaloisForLFunctions.riemannZeta_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental _

theorem xi_add_unitFiniteBathMemory_constantCoefficientDifferentiallyTranscendental
    {n : ℕ} (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    _root_.HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (RHTower.xi +
        finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1)) := by
  rw [finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition]
  exact RHTower.xi_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental _

theorem xiLogDeriv_add_unitFiniteBathMemory_constantCoefficientDifferentiallyTranscendental
    {n : ℕ} (systemFrequency : ℝ) (environmentFrequency : Fin n → ℝ) :
    _root_.HTGeometry.ConstantCoefficientDifferentiallyTranscendental
      (logDeriv RHTower.xi +
        finiteBathMemoryAnalytic systemFrequency environmentFrequency (fun _ => 1)) := by
  rw [finiteBathMemoryAnalytic_unit_eq_finiteComplexGibbsPartition]
  exact RHTower.xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental _

end

end GaloisForLFunctions.HTGeometry

