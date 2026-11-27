import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.PrimeSquare

/-! # Reading the critical line directly from the divisor channels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature

open Finset Real
open scoped ComplexConjugate

/-- Complex amplitude of the propagated order-class vector along the
unit vector in the direction of the unpropagated shell at s=0. -/
def projection (s : ℂ) (n : ℕ+) : ℂ :=
  (∑ a ∈ (n : ℕ).divisors, conj (channel 0 n a)*channel s n a) /
    (sqrt (∑ a ∈ (n : ℕ).divisors, ‖channel 0 n a‖^2) : ℂ)

private theorem reference_norm (n : ℕ+) :
    ∑ a ∈ (n : ℕ).divisors, ‖channel 0 n a‖^2=((n : ℕ) : ℝ) := by
  simp only [channel_norm_sq,heat,neg_zero,zero_mul,Complex.exp_zero,norm_one,one_pow,mul_one,
    ←Nat.cast_sum,Nat.sum_totient]

/-- The factor sqrt(n) follows from the order multiplicities in the
reference vector. It fixes the critical exponent of the propagated amplitude. -/
theorem projected_heat (s : ℂ) (n : ℕ+) :
    projection s n=(sqrt ((n : ℕ) : ℝ) : ℂ)*heat s n := by
  rw [projection,shell_pairing,reference_norm,map_zero,zero_add]
  have pos : 0<((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have nz := Complex.ofReal_ne_zero.mpr (sqrt_pos.mpr pos).ne'
  have sqr : (sqrt ((n : ℕ) : ℝ) : ℂ)^2=(n : ℕ) := by exact_mod_cast sq_sqrt pos.le
  apply (div_eq_iff nz).mpr
  rw [←sqr]
  ring

/-- Independent energy composition multiplies these normalized shell
amplitudes, including when the two integer labels share a prime. -/
theorem projection_mul (s : ℂ) (a b : ℕ+) :
    projection s (a*b)=projection s a*projection s b := by
  rw [projected_heat,projected_heat,projected_heat,heat_mul,PNat.mul_coe,Nat.cast_mul,
    sqrt_mul (Nat.cast_nonneg _),Complex.ofReal_mul]
  ring

theorem projection_mass (s : ℂ) (n : ℕ+) : ‖projection s n‖^2=shellMass s n := by
  simp only [projected_heat,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sqrt_nonneg _),sq_sqrt (Nat.cast_nonneg _),shellMass_eq]

private theorem inverse_projection (s : ℂ) (n : ℕ+) :
    (projection s n)⁻¹=heat (((1/2 : ℝ) : ℂ)-s) n := by
  have pos : 0<((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have root : sqrt ((n : ℕ) : ℝ)=exp (energy n/2) := by
    rw [energy,exp_half,exp_log pos]
  rw [projected_heat,root,Complex.ofReal_exp,heat,←Complex.exp_add,←Complex.exp_neg,heat]
  congr 1
  rw [Complex.ofReal_div,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

/-- Two real reciprocal comparisons from normalized channel overlaps.
Their definition uses only the split at s and its reference at zero. -/
def channelReading (p : Nat.Primes) (s : ℂ) :=
  max |amplitude (projection s (atom p))| (|amplitude (projection s (atom p*atom p))|/2)

theorem from_channels (p : Nat.Primes) (s : ℂ) : channelReading p s=squareReading p s := by
  have reciprocal (w : ℂ) : |amplitude w⁻¹|=|amplitude w| := by
    simp only [amplitude,inv_inv,Complex.sub_re]
    exact abs_sub_comm _ _
  rw [channelReading,squareReading,←inverse_projection,←inverse_projection,reciprocal,reciprocal]

/-- A prime and its square force norm preservation from the original
divisor channels, without specifying the critical exponent in the observation. -/
theorem intrinsic_isometry (p : Nat.Primes) (s : ℂ) :
    channelReading p s=0 ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [from_channels,square_isometry]

/-- RH is equivalent to the vanishing of the prime and prime-square
real comparisons at every strip zero, measured in the original channels. -/
theorem rh_iff_channel_reading (p : Nat.Primes) :
    RiemannHypothesis ↔ ∀ s : OpenStrip, riemannZeta s.val=0 → channelReading p s.val=0 := by
  simpa only [from_channels] using rh_iff_zero_quadratures p

#print axioms rh_iff_channel_reading
#print axioms projected_heat
#print axioms projection_mul
#print axioms projection_mass
#print axioms from_channels
#print axioms intrinsic_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature
