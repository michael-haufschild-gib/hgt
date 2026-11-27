import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Character
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Thermometry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdjacentShellTrace

/-! # Height-uniform isometry test from a prime and its composite square -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature

open Real
open PrimeCalibration (log_pos_prime)

/-- The elementary occupation and the exponent of its centered heat multiplier. -/
def atom (p : Nat.Primes) := label (Finsupp.single p 1)

def coordinate (p : Nat.Primes) (s : ℂ) := (s-((1/2 : ℝ) : ℂ))*(log p.val : ℂ)

/-- Real reciprocal readings on the actual prime and prime-square energy shells. -/
def squareReading (p : Nat.Primes) (s : ℂ) :=
  max |amplitude (heat (((1/2 : ℝ) : ℂ)-s) (atom p))|
    (|amplitude (heat (((1/2 : ℝ) : ℂ)-s) (atom p*atom p))|/2)

private theorem prime_heat (p : Nat.Primes) (s : ℂ) :
    heat (((1/2 : ℝ) : ℂ)-s) (atom p)=Complex.exp (coordinate p s) := by
  simp only [heat,energy,atom,label_one_quantum,neg_sub,coordinate]

theorem square_character (p : Nat.Primes) (s : ℂ) :
    squareReading p s=joint (Complex.exp (coordinate p s)) := by
  rw [squareReading,heat_mul,prime_heat,joint,sq]

private theorem re_coord (p : Nat.Primes) (s : ℂ) :
    (coordinate p s).re=(s.re-1/2)*log p.val := by
  simp only [coordinate,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

private theorem im_coord (p : Nat.Primes) (s : ℂ) :
    (coordinate p s).im=s.im*log p.val := by
  simp only [coordinate,Complex.mul_im,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_add,sub_zero]

/-- A single prime together with its square detects isometry at every
complex temperature using only real quadratures. -/
theorem square_isometry (p : Nat.Primes) (s : ℂ) :
    squareReading p s=0 ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [square_character,joint_zero,re_coord,mul_eq_zero,or_iff_left (log_pos_prime p).ne',
    sub_eq_zero,split_isometric_iff]

/-- At every real part the sharp lower envelope is attained at an actual
height, which can be chosen in the first quarter period. -/
theorem minimum_over_heights (p : Nat.Primes) (σ : ℝ) :
    let x := (σ-1/2)*log p.val
    let floor := 2*|sinh x| * radius (cosh x)
    (∀ t : ℝ, floor ≤ squareReading p ⟨σ,t⟩) ∧
      squareReading p ⟨σ,arccos (radius (cosh x))/log p.val⟩=floor := by
  let x := (σ-1/2)*log p.val
  have form (t : ℝ) : squareReading p ⟨σ,t⟩=
      2*|sinh x| * phaseGain (cosh x) (t*log p.val) := by
    rw [square_character,joint_factor,re_coord,im_coord]
  constructor
  · intro t; rw [form]
    exact mul_le_mul_of_nonneg_left (sharp_phase (one_le_cosh x) _).1 (by positivity)
  · rw [form,div_mul_cancel₀ _ (log_pos_prime p).ne',attaining_phase (one_le_cosh x)]

/-- The phase that hides a single prime at any prescribed real part still
leaves the composite reading visible off the critical line. -/
theorem hidden_prime (p : Nat.Primes) (σ : ℝ) :
    let s : ℂ := ⟨σ,(π/2)/log p.val⟩
    amplitude (heat (((1/2 : ℝ) : ℂ)-s) (atom p))=0 ∧
      (squareReading p s=0 ↔ σ=1/2) := by
  let s : ℂ := ⟨σ,(π/2)/log p.val⟩
  change amplitude (heat _ (atom p))=0 ∧ (squareReading p s=0 ↔ σ=1/2)
  constructor
  · rw [prime_heat,first,im_coord]
    change _ * cos ((π/2)/log p.val*log p.val)=0
    rw [div_mul_cancel₀ _ (log_pos_prime p).ne',cos_pi_div_two,mul_zero]
  · exact (square_isometry p s).trans (split_isometric_iff s)

/-- The elementary and composite quadratures bound every odd-order
probability reading, uniformly in the imaginary part. -/
theorem gibbs_bound (p : Nat.Primes) (s : ℂ) (n : ℕ) :
    |thermometer n p (2*s.re-1)|≤(2*squareReading p s)^(2*n+3) := by
  have radial := joint_lower (coordinate p s)
  rw [←square_character,re_coord] at radial
  rw [exact_reading,abs_neg,abs_pow,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2),
    show (2*s.re-1)*log p.val/2=(s.re-1/2)*log p.val by ring]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left radial (by norm_num)) _

/-- The remaining implication at partition zeros, expressed in the two
real quadratures of the prime and its square. -/
theorem rh_iff_zero_quadratures (p : Nat.Primes) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 → squareReading p s.val=0 := by
  rw [rh_iff_trace_zero_forces_isometry]
  exact ⟨fun h s hz => (square_isometry p s.val).mpr (h s ((adjacentTrace_zero_iff s).mpr hz)),
    fun h s hz => (square_isometry p s.val).mp (h s ((adjacentTrace_zero_iff s).mp hz))⟩

#print axioms square_character
#print axioms square_isometry
#print axioms minimum_over_heights
#print axioms hidden_prime
#print axioms gibbs_bound
#print axioms rh_iff_zero_quadratures

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature
