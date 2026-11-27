import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Projection

/-! # Critical Born weights and the law of the observed elementary channel -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real MeasureTheory
open GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature (atom projection projected_heat)
open scoped Topology

/-- The real part is fixed by isometric divisor splitting. -/
def critical (t : ℝ) : ℂ := ⟨1/2,t⟩

theorem critical_weight (p : Nat.Primes) (t : ℝ) :
    ‖heat (critical t) (atom p)‖^2 = weight p.val := by
  rw [norm_heat,atom,energy,label_one_quantum,←exp_nat_mul]
  change exp ((2 : ℕ)*( -(1/2 : ℝ)*log p.val))=(p.val : ℝ)⁻¹
  rw [show ((2 : ℕ) : ℝ)*(-(1/2 : ℝ)*log p.val)= -log p.val by ring,exp_neg,
    exp_log (Nat.cast_pos.mpr p.property.pos)]

/-- On the isometry line the normalized divisor-channel overlap is
exactly the elementary phase; no radial normalization is needed. -/
theorem critical_projection (p : Nat.Primes) (t : ℝ) :
    projection (critical t) (atom p)=(phase t p.val : ℂ) := by
  have hp := (Nat.cast_pos.mpr p.property.pos : (0 : ℝ)<p.val)
  have root : sqrt (p.val : ℝ)=exp (log p.val/2) := by rw [exp_half,exp_log hp]
  rw [projected_heat,heat,energy,atom,label_one_quantum,root,Complex.ofReal_exp,
    ←Complex.exp_add,phase,Circle.coe_exp]
  congr 1
  have temp : critical t=((1/2 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [critical]
  rw [temp]
  push_cast
  ring

def reading (z : Circle) := |(z : ℂ).re|

private theorem read_cont : Continuous reading :=
  (Complex.continuous_re.comp continuous_subtype_val).abs

/-- Probability law of the absolute real channel measurement. -/
def readingLaw (t : ℝ) (N : ℕ) :=
  (phaseLaw t N).map read_cont.measurable.aemeasurable

def uniformReading := uniform.map read_cont.measurable.aemeasurable

theorem reading_limit (t : ℝ) (ht : t≠0) :
    Tendsto (readingLaw t) atTop (𝓝 uniformReading) :=
  (ProbabilityMeasure.continuous_map read_cont).continuousAt.tendsto.comp (phase_limit t ht)

theorem absolute_reading (p : Nat.Primes) (t : ℝ) :
    |(projection (critical t) (atom p)).re|=reading (phase t p.val) :=
  congrArg (fun z : ℂ => |z.re|) (critical_projection p t)

private theorem double_reading (z : Circle) :
    2*(reading z)^2=1+((z : ℂ)^2).re := by
  have unit := Complex.sq_norm (z : ℂ)
  simp only [Circle.norm_coe,one_pow,Complex.normSq_apply] at unit
  rw [reading,sq_abs,pow_two (z : ℂ),Complex.mul_re]
  nlinarith only [unit]

/-- Exact finite mean square. The entire discrepancy from 1/2 is one
nonconstant Fourier coefficient of the sampled elementary phases. -/
theorem mean_square (t : ℝ) (N : ℕ) :
    (∑ p ∈ primes N, weight p*(reading (phase t p))^2) / mass N =
      (1+(coefficient t (-2) N).re)/2 := by
  have denom := (mass_pos N).ne'
  have eq : (∑ p ∈ primes N, weight p*(reading (phase t p))^2)*2 =
      mass N + ∑ p ∈ primes N, weight p*((phase t p : ℂ)^2).re := by
    rw [sum_mul,mass,←sum_add_distrib]
    apply sum_congr rfl
    intro p _
    linear_combination weight p * double_reading (phase t p)
  have realCoef : (coefficient t (-2) N).re =
      (∑ p ∈ primes N, weight p*((phase t p : ℂ)^2).re) / mass N := by
    simp only [coefficient,neg_neg,zpow_ofNat,Complex.div_ofReal_re,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [realCoef]
  field_simp [denom]
  linarith only [eq]

theorem mean_square_limit (t : ℝ) (ht : t≠0) :
    Tendsto (fun N => (∑ p ∈ primes N, weight p*(reading (phase t p))^2)/mass N) atTop (𝓝 (1/2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (nonzero_mode t ht (-2) (by norm_num))
  have law := ((tendsto_const_nhds (x := (1 : ℝ))).add h).div_const (2 : ℝ)
  simpa only [mean_square,Function.comp_def,Complex.zero_re,add_zero] using law

theorem mean_square_zero (N : ℕ) :
    (∑ p ∈ primes N, weight p*(reading (phase 0 p))^2)/mass N = 1 := by
  rw [mean_square,zero_height_coefficient]
  norm_num

#print axioms mean_square_zero
#print axioms critical_weight
#print axioms critical_projection
#print axioms reading_limit
#print axioms absolute_reading
#print axioms mean_square
#print axioms mean_square_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
