import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.ClockReadout

/-! # Consecutive harmonics of the quantum composition clock -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- The Born response of the split at the k-th multiple of its clock time. -/
def harmonicReading (v : MissingWave) (t : ℝ) (k : ℕ) :=
  compositionResponse v (criticalTime ((k:ℝ)*t))

def harmonicTest (r : ℕ+) (δ : ℝ) (v : MissingWave) (t : ℝ) : Prop :=
  ∀ h : ℕ, 0 < h → h < r.val → ‖harmonicReading v t h‖ ≤ δ

theorem splitPhase_nat_mul (k : ℕ) (t : ℝ) (n : ℕ+) :
    splitPhase ((k:ℝ)*t) n = splitPhase t n ^ k := by
  rw [splitPhase_eq_exp,splitPhase_eq_exp,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem harmonicTerms_hasSum (v : MissingWave) (t : ℝ) (k : ℕ) :
    HasSum (fun n => (occupationProbability v n:ℂ)*splitPhase t n ^ k) (harmonicReading v t k) := by
  simpa only [harmonicReading,splitPhase_nat_mul] using criticalTerms_hasSum v ((k:ℝ)*t)

theorem harmonicReading_zero (v : MissingWave) (t : ℝ) : harmonicReading v t 0 = 1 := by
  apply (harmonicTerms_hasSum v t 0).unique
  simpa only [pow_zero,mul_one,Complex.ofReal_one] using (Complex.hasSum_ofReal.mpr (occupationLaw_hasSum v))

theorem norm_harmonicReading_le_one (v : MissingWave) (t : ℝ) (k : ℕ) :
    ‖harmonicReading v t k‖ ≤ 1 := by
  simpa [harmonicReading,windowAmplitude,windowMass] using window_response_disk v ((k:ℝ)*t) ∅

/-- The clock polynomial of d equally spaced observations. -/
def clockPolynomial (d : ℕ) (u : ℂ) := ∑ h ∈ Finset.range d, u^h

theorem clockPolynomial_one (d : ℕ) : clockPolynomial d 1 = d := by simp [clockPolynomial]

theorem clockPolynomial_succ (d : ℕ) (u : ℂ) :
    clockPolynomial (d+1) u = 1+u*clockPolynomial d u := by
  simp only [clockPolynomial,Finset.sum_range_succ',pow_zero,pow_succ',Finset.mul_sum,add_comm]

theorem clockPolynomial_step_sq (d : ℕ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖clockPolynomial (d+1) u‖^2 = ‖clockPolynomial d u‖^2+1+2*(u*clockPolynomial d u).re := by
  have h (z : ℂ) : ‖1+z‖^2 = ‖z‖^2+1+2*z.re := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im]
    ring
  rw [clockPolynomial_succ,h,norm_mul,hu,one_mul]

theorem clockPhase_limit {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (n : ℕ+) :
    Tendsto (fun j => splitPhase (t j) n) atTop (𝓝 1) := by
  simpa only [Function.comp_def,splitPhase_zero] using
    ((splitPhase_continuous n).continuousAt (x := 0)).tendsto.comp ht

theorem clockPolynomial_limit {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (n : ℕ+) (d : ℕ) :
    Tendsto (fun j => clockPolynomial d (splitPhase (t j) n)) atTop (𝓝 (d:ℂ)) := by
  simpa only [clockPolynomial,one_pow,Finset.sum_const,Finset.card_range,nsmul_one] using
    (tendsto_finsetSum (Finset.range d) (fun k _ => (clockPhase_limit ht n).pow k))

/-- A running sum of d observed responses, starting at harmonic k. -/
def blockReading (v : MissingWave) (t : ℝ) (k d : ℕ) :=
  ∑ h ∈ Finset.range d, harmonicReading v t (k+h)

theorem blockReading_hasSum (v : MissingWave) (t : ℝ) (k d : ℕ) :
    HasSum (fun n => (occupationProbability v n:ℂ)*(splitPhase t n^k*clockPolynomial d (splitPhase t n)))
      (blockReading v t k d) := by
  induction d with
  | zero => simp [clockPolynomial,blockReading]
  | succ d ih =>
    rw [blockReading,Finset.sum_range_succ]
    apply (ih.add (harmonicTerms_hasSum v t (k+d))).congr_fun
    intro n
    simp only [clockPolynomial,Finset.sum_range_succ,pow_add,mul_add]

#print axioms splitPhase_nat_mul
#print axioms harmonicTerms_hasSum
#print axioms harmonicReading_zero
#print axioms norm_harmonicReading_le_one
#print axioms clockPolynomial_one
#print axioms clockPolynomial_succ
#print axioms clockPolynomial_step_sq
#print axioms clockPhase_limit
#print axioms clockPolynomial_limit
#print axioms blockReading_hasSum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
