import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Response

/-! # Finite energy windows of the critical composition response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open scoped BigOperators

/-- Composition parameter on the isometry line at real clock time t. -/
def criticalTime (t : ℝ) : ℂ := ((1/2:ℝ):ℂ)+(t:ℂ)*Complex.I

theorem criticalTime_re (t : ℝ) : (criticalTime t).re = 1/2 := by simp [criticalTime]

/-- Phase acquired by the occupation n under the isometric split. -/
def splitPhase (t : ℝ) (n : ℕ+) := heat (2*criticalTime t-1) n

theorem splitPhase_eq_exp (t : ℝ) (n : ℕ+) :
    splitPhase t n = Complex.exp (((-2*t*energy n:ℝ):ℂ)*Complex.I) := by
  unfold splitPhase heat criticalTime
  congr 1
  push_cast
  ring

theorem splitPhase_norm (t : ℝ) (n : ℕ+) : ‖splitPhase t n‖ = 1 := by
  rw [splitPhase,composition_heat_norm,shellMass,criticalTime_re]
  norm_num

theorem splitPhase_zero (n : ℕ+) : splitPhase 0 n = 1 := by simp [splitPhase_eq_exp]

theorem splitPhase_continuous (n : ℕ+) : Continuous (fun t => splitPhase t n) := by
  simp only [splitPhase_eq_exp]
  fun_prop

theorem occupationLaw_hasSum (v : MissingWave) : HasSum (occupationProbability v) 1 :=
  Equiv.pnatEquivNat.symm.hasSum_iff.mp (occupationProbability_sum v)

theorem occupationLaw_nonneg (v : MissingWave) (n : ℕ+) : 0 ≤ occupationProbability v n :=
  (exteriorLaw v).property.1 n

/-- At a critical time the complex Born terms sum absolutely to the actual response. -/
theorem criticalTerms_hasSum (v : MissingWave) (t : ℝ) :
    HasSum (fun n => (occupationProbability v n:ℂ)*splitPhase t n) (compositionResponse v (criticalTime t)) :=
  ((response_absolute_iff v _).mpr ((forall_finiteSplit_iff _).mpr (criticalTime_re t).ge v)).of_norm.hasSum

def windowMass (v : MissingWave) (F : Finset ℕ+) := ∑ n ∈ F, occupationProbability v n

def windowAmplitude (v : MissingWave) (t : ℝ) (F : Finset ℕ+) :=
  ∑ n ∈ F, (occupationProbability v n:ℂ)*splitPhase t n

theorem windowMass_nonneg (v : MissingWave) (F : Finset ℕ+) : 0 ≤ windowMass v F :=
  Finset.sum_nonneg fun n _ => occupationLaw_nonneg v n

theorem windowMass_le_one (v : MissingWave) (F : Finset ℕ+) : windowMass v F ≤ 1 := by
  rw [← (occupationLaw_hasSum v).tsum_eq]
  exact (occupationLaw_hasSum v).summable.sum_le_tsum F (fun n _ => occupationLaw_nonneg v n)

theorem occupationLaw_le_one (v : MissingWave) (n : ℕ+) : occupationProbability v n ≤ 1 := by
  simpa only [windowMass,Finset.sum_singleton] using windowMass_le_one v {n}

/-- The missing probability is a rigorous complex error radius for a finite energy readout. -/
theorem window_response_disk (v : MissingWave) (t : ℝ) (F : Finset ℕ+) :
    ‖compositionResponse v (criticalTime t)-windowAmplitude v t F‖ ≤ 1-windowMass v F := by
  let μ := occupationProbability v
  let f := fun n => (μ n:ℂ)*splitPhase t n
  have hμ : HasSum μ 1 := occupationLaw_hasSum v
  have hf : HasSum f (compositionResponse v (criticalTime t)) := criticalTerms_hasSum v t
  have hn (n : ℕ+) : ‖f n‖ = μ n := by
    rw [show f n = (μ n:ℂ)*splitPhase t n from rfl,norm_mul,splitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_of_nonneg (occupationLaw_nonneg v n)]
  have tailF : ∑' n : (Fᶜ : Set ℕ+), f n = compositionResponse v (criticalTime t)-windowAmplitude v t F :=
    eq_sub_iff_add_eq'.mpr ((hf.summable.sum_add_tsum_compl (s := F)).trans hf.tsum_eq)
  have tailμ : ∑' n : (Fᶜ : Set ℕ+), μ n = 1-windowMass v F :=
    eq_sub_iff_add_eq'.mpr ((hμ.summable.sum_add_tsum_compl (s := F)).trans hμ.tsum_eq)
  rw [← tailF,← tailμ]
  have habs : Summable (fun n : (Fᶜ : Set ℕ+) => ‖f n‖) := by
    simp only [hn]
    exact hμ.summable.subtype (fun n => n ∈ (Fᶜ : Set ℕ+))
  exact (norm_tsum_le_tsum_norm habs).trans_eq (tsum_congr (fun n => hn n))

#print axioms criticalTime_re
#print axioms splitPhase_eq_exp
#print axioms splitPhase_norm
#print axioms splitPhase_zero
#print axioms splitPhase_continuous
#print axioms occupationLaw_hasSum
#print axioms occupationLaw_nonneg
#print axioms criticalTerms_hasSum
#print axioms windowMass_nonneg
#print axioms windowMass_le_one
#print axioms occupationLaw_le_one
#print axioms window_response_disk

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
