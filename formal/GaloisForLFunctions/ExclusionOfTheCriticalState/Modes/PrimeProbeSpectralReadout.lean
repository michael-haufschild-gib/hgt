import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.CoupledCubicProbeRecovery
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDisplacementSpectrum
import GaloisForLFunctions.RHTower.ParityConditionedForecastingInstability
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Scalar observation of a symmetric exponential probe bank

On any distinct integer schedule, including prime times, the exponential
Hankel bank has simple positive spectrum. Every eigenmode has a nonzero
sum of coordinates. Summing the output after each of the first n iterates
therefore recovers an arbitrary n-component signal. In the eigenbasis,
the diagonal sampling rates themselves have a Cauchy matrix.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.ProbeSpectrum
open Matrix Finset WithLp MeasureTheory ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.HilbertMetric.CauchyJordan
open GaloisForLFunctions.HilbertMetric.CauchySpectrum
variable {n : ℕ}

/-- Positive diagonal rate associated with an integer probe time. -/
def sampleRate (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) : ℝ := Real.exp s+5+2*(t i:ℝ)
private def logs (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) := Real.log (sampleRate s t i)

private theorem node_pos (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) : 0 < sampleRate s t i := by
  unfold sampleRate
  positivity

private theorem rate_logs (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) : rate (logs s t) i = sampleRate s t i :=
  Real.exp_log (node_pos s t i)

/-- The diagonal bank is the inverse Jordan image of the constant source. -/
theorem bank_response (s : ℝ) (t : Fin n ↪ ℕ) :
    bank s t t = GaloisForLFunctions.HilbertMetric.CauchySpectrum.response (logs s t) 1 := by
  ext i j
  change (∫ u, probe (Real.exp s) u * Real.exp ((5+((t i+t j:ℕ):ℝ))*u)) = _
  have hpos : 0 < Real.exp s+(5+((t i+t j:ℕ):ℝ)) := by positivity
  rw [integral_probe_mul_exp hpos]
  simp only [HilbertMetric.CauchySpectrum.response,rate_logs,sampleRate,Pi.one_apply,mul_one,Nat.cast_add]
  have hp := node_pos s t i
  have hq := node_pos s t j
  unfold sampleRate at hp hq
  field_simp <;> ring

theorem bank_hermitian (s : ℝ) (t : Fin n ↪ ℕ) : (bank s t t).IsHermitian := by
  rw [bank_response]
  ext i j
  simp [Matrix.conjTranspose_apply,HilbertMetric.CauchySpectrum.response,add_comm]

private abbrev basis (s : ℝ) (t : Fin n ↪ ℕ) := (bank_hermitian s t).eigenvectorBasis
/-- Real coordinate eigenvector for a spectral level of the bank. -/
abbrev eigenmode (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) := ((basis s t) i).ofLp

/-- Eigenvalues of the real symmetric bank, with multiplicities. -/
def levels (s : ℝ) (t : Fin n ↪ ℕ) := (bank_hermitian s t).eigenvalues

private theorem eigen (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) :
    (bank s t t).mulVec (eigenmode s t i) = levels s t i • eigenmode s t i :=
  (bank_hermitian s t).mulVec_eigenvectorBasis i

private theorem vec_ne (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) : eigenmode s t i ≠ 0 :=
  (ofLp_eq_zero 2).ne.2 ((basis s t).orthonormal.ne_zero i)

/-- Every mode is strictly positive and visible in the sum of the outputs. -/
theorem positive_visible_modes (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) :
    0 < levels s t i ∧ (∑ k, eigenmode s t i k) ≠ 0 := by
  have he := eigen s t i
  rw [bank_response] at he
  obtain ⟨hn,hiff⟩ := eigenvalue_detection (logs s t) 1 ⟨_,vec_ne s t i⟩ _ he
  have hne : levels s t i ≠ 0 := by
    intro hz
    have hk := eigen s t i
    rw [hz,zero_smul,← Matrix.mulVec_zero (bank s t t)] at hk
    exact vec_ne s t i ((bank_bijective s t t).1 hk)
  exact ⟨lt_of_le_of_ne hn hne.symm,by simpa [reading] using hne ∘ hiff.mp⟩

/-- The spectral resolution has no repeated level at any distinct schedule. -/
theorem levels_injective (s : ℝ) (t : Fin n ↪ ℕ) : Function.Injective (levels s t) := by
  intro i j heq
  by_contra hij
  have hi := eigen s t i
  have hj := eigen s t j
  rw [bank_response,heq] at hi
  rw [bank_response] at hj
  have h := (simple_eigenvectors (logs s t) 1 _ _ _ hi hj).resolve_left
    (positive_visible_modes s t j).1.ne'
  have hb : reading 1 (eigenmode s t j) • basis s t i = reading 1 (eigenmode s t i) • basis s t j := by
    simpa only [WithLp.toLp_smul,WithLp.toLp_ofLp] using congrArg (WithLp.toLp 2) h
  have hh := congrArg (fun v => inner ℝ (basis s t i) v) hb
  have orth := orthonormal_iff_ite.mp (basis s t).orthonormal
  simp [real_inner_smul_right,orth,hij] at hh
  exact (positive_visible_modes s t j).2 (by simpa [reading] using hh)

/-- In the eigenbasis the sampling-rate operator has a Cauchy matrix whose
weights are the same scalar observations used for reconstruction. -/
theorem dual_rate_matrix (s : ℝ) (t : Fin n ↪ ℕ) (i j : Fin n) :
    (∑ k, sampleRate s t k*eigenmode s t i k*eigenmode s t j k) =
      2*(∑ k, eigenmode s t i k)*(∑ k, eigenmode s t j k)/(levels s t i+levels s t j) := by
  have sd := polarized_reading (logs s t) 1 (eigenmode s t i) (eigenmode s t j)
  rw [← bank_response,eigen,eigen] at sd
  simp only [reading,Pi.one_apply,one_mul,rate_logs,Pi.smul_apply,smul_eq_mul] at sd
  apply (eq_div_iff (add_pos (positive_visible_modes s t i).1 (positive_visible_modes s t j).1).ne').2
  rw [mul_add,Finset.sum_mul,Finset.sum_mul,sd,add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

/-- Total output after k iterations, including the initial reading at k=0. -/
def echo (s : ℝ) (t : Fin n ↪ ℕ) (v : Fin n → ℝ) (k : ℕ) := ∑ i, (((bank s t t)^k).mulVec v) i

private theorem power_mode (s : ℝ) (t : Fin n ↪ ℕ) (i : Fin n) (k : ℕ) :
    ((bank s t t)^k).mulVec (eigenmode s t i) = (levels s t i)^k • eigenmode s t i := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,eigen,smul_smul,← pow_succ]

private def coefficient (s : ℝ) (t : Fin n ↪ ℕ) (v : Fin n → ℝ) (i : Fin n) :=
  inner ℝ (basis s t i) (WithLp.toLp 2 v)

private theorem synthesis (s : ℝ) (t : Fin n ↪ ℕ) (v : Fin n → ℝ) :
    ∑ i, coefficient s t v i • eigenmode s t i = v := by
  have h := congrArg WithLp.ofLp ((basis s t).sum_repr' (WithLp.toLp 2 v))
  simpa [coefficient,eigenmode] using h

private theorem echo_moment (s : ℝ) (t : Fin n ↪ ℕ) (v : Fin n → ℝ) (k : ℕ) :
    echo s t v k = ∑ i, (coefficient s t v i*(∑ j, eigenmode s t i j))*levels s t i^k := by
  unfold echo
  conv_lhs => rw [← synthesis s t v]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,power_mode,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The first n scalar echoes determine every input on an n-point schedule. -/
theorem scalar_echo_injective (s : ℝ) (t : Fin n ↪ ℕ) :
    Function.Injective (fun v : Fin n → ℝ => fun k : Fin n => echo s t v k) := by
  intro u v h
  have hm := _root_.RHTower.ParityForecast.weights_eq_of_first_moments_on_distinct_nodes
    (levels_injective s t) (fun k => (echo_moment s t u k).symm.trans
      ((congrFun h k).trans (echo_moment s t v k)))
  have hc (i : Fin n) : coefficient s t u i = coefficient s t v i :=
    mul_right_cancel₀ (positive_visible_modes s t i).2 (congrFun hm i)
  calc u = ∑ i, coefficient s t u i • eigenmode s t i := (synthesis s t u).symm
       _ = ∑ i, coefficient s t v i • eigenmode s t i := Finset.sum_congr rfl fun i _ => by rw [hc]
       _ = v := synthesis s t v

end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.ProbeSpectrum
