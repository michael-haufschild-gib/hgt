import GaloisForLFunctions.RHTower.Sieve.KloostermanSharedHybridCollapse

/-!
# Symplectic Fourier symmetry of the discrete ambiguity function

For an arbitrary complex profile on a cyclic group, the squared
ambiguity amplitude is its own symplectic Fourier transform. The
four-point coefficient prior to transformation is symmetric in its
two increments. Fourier inversion gives the finite identity in the
proof of Di Fratta and Slastikov, Lemma 8.9, equation (8.83).
-/
noncomputable section
open Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {q : ℕ} [NeZero q]
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod q) ℂ)

/-- Fourier amplitude of the correlation at a prescribed shift. -/
def cyclicAmbiguityAmplitude (c : ZMod q → ℂ) (a b : ZMod q) : ℂ :=
  ∑ x, c (x+b)*conj (c x)*χ (-(a*x))

def cyclicAmbiguityWeight (c : ZMod q → ℂ) (a b : ZMod q) : ℝ :=
  ‖cyclicAmbiguityAmplitude c a b‖^2

/-- Four coefficients at the corners of an additive parallelogram. -/
def cyclicRectangle (c : ZMod q → ℂ) (b h : ZMod q) : ℂ :=
  ∑ x, c (x+b)*c (x+h)*conj (c x)*conj (c (x+b+h))

theorem cyclic_rectangle_symmetric (c : ZMod q → ℂ) (b h : ZMod q) :
    cyclicRectangle c b h=cyclicRectangle c h b := by
  unfold cyclicRectangle
  refine sum_congr rfl fun x _ => ?_
  rw [show x+b+h=x+h+b by ring]; ring

private theorem square_fourier_row (f : ZMod q → ℂ) (a : ZMod q) :
    ((‖∑ x, f x*χ (-(a*x))‖^2 : ℝ):ℂ) =
      ∑ h, (∑ x, f x*conj (f (x+h)))*χ (a*h) := by
  rw [Complex.ofReal_pow,←Complex.mul_conj',map_sum,sum_mul_sum]
  symm
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun h => ?_
  change f x*conj (f (x+h))*χ (a*h) =
    (f x*χ (-(a*x)))*conj (f (x+h)*χ (-(a*(x+h))))
  rw [map_mul (starRingEnd ℂ) (f (x+h)) (χ (-(a*(x+h)))),
    ←AddChar.map_neg_eq_conj χ (-(a*(x+h))),neg_neg]
  have hp : χ (-(a*x))*χ (a*(x+h))=χ (a*h) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1; ring
  rw [←hp]; ring

/-- A single Fourier transform in the lag variable recovers every
squared ambiguity amplitude from the four-point correlations. -/
theorem cyclic_ambiguity_weight_fourier (c : ZMod q → ℂ) (a b : ZMod q) :
    (cyclicAmbiguityWeight c a b:ℂ) = ∑ h, cyclicRectangle c b h*χ (a*h) := by
  rw [cyclicAmbiguityWeight,cyclicAmbiguityAmplitude,
    square_fourier_row (fun x => c (x+b)*conj (c x)) a]
  refine sum_congr rfl fun h _ => congrArg (fun z : ℂ => z*χ (a*h)) ?_
  unfold cyclicRectangle
  refine sum_congr rfl fun x _ => ?_
  rw [map_mul,Complex.conj_conj,show x+h+b=x+b+h by ring]
  ring

/-- Fourier inversion of the whole frequency row, at any lag. -/
theorem cyclic_ambiguity_weight_inversion (c : ZMod q → ℂ) (b s : ZMod q) :
    (∑ r, (cyclicAmbiguityWeight c r s:ℂ)*χ (r*(-b))) = (q:ℂ)*cyclicRectangle c s b := by
  simp_rw [cyclic_ambiguity_weight_fourier]
  simpa only [neg_neg] using
    _root_.RHTower.Sieve.sum_additiveFourier_mul_stdAddChar q (cyclicRectangle c s) (-b)

/-- Sussman's finite symplectic Fourier identity. There is no
primality, parity, or normalization restriction on the signal. -/
theorem cyclic_ambiguity_self_fourier (c : ZMod q → ℂ) (a b : ZMod q) :
    (∑ r,∑ s, (cyclicAmbiguityWeight c r s:ℂ)*χ (a*s-b*r)) =
      (q:ℂ)*(cyclicAmbiguityWeight c a b:ℂ) := by
  calc _ = ∑ s, (∑ r, (cyclicAmbiguityWeight c r s:ℂ)*χ (r*(-b)))*χ (a*s) := by
         rw [sum_comm]
         refine sum_congr rfl fun s _ => ?_
         rw [sum_mul]
         refine sum_congr rfl fun r _ => ?_
         rw [show a*s-b*r=r*(-b)+a*s by ring,AddChar.map_add_eq_mul,mul_assoc]
       _ = ∑ s,(q:ℂ)*(cyclicRectangle c b s*χ (a*s)) := by
         refine sum_congr rfl fun s _ => ?_
         rw [cyclic_ambiguity_weight_inversion,cyclic_rectangle_symmetric c s b,mul_assoc]
       _ = _ := by rw [←mul_sum,←cyclic_ambiguity_weight_fourier]

/-- The real cosine kernel transfers the nonnegative weights to a
linear test on the same grid. -/
theorem cyclic_ambiguity_real_fourier (c : ZMod q → ℂ) (a b : ZMod q) :
    (∑ r,∑ s, cyclicAmbiguityWeight c r s*(χ (a*s-b*r)).re) =
      (q:ℝ)*cyclicAmbiguityWeight c a b := by
  have h := congrArg Complex.re (cyclic_ambiguity_self_fourier c a b)
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using h

/-- The zero lag of the four-point row is ordinary intensity autocorrelation. -/
theorem cyclic_ambiguity_frequency_mass (c : ZMod q → ℂ) (s : ZMod q) :
    ∑ r, cyclicAmbiguityWeight c r s =
      (q:ℝ)*∑ x, ‖c x‖^2*‖c (x+s)‖^2 := by
  have h := cyclic_ambiguity_weight_inversion c 0 s
  have hrect : cyclicRectangle c s 0 = ((∑ x, ‖c x‖^2*‖c (x+s)‖^2 : ℝ):ℂ) := by
    rw [cyclicRectangle,Complex.ofReal_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [add_zero,Complex.ofReal_mul,Complex.ofReal_pow,←Complex.mul_conj']
    ring
  rw [hrect] at h
  simpa only [neg_zero,mul_zero,AddChar.map_zero_eq_one,mul_one,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    using congrArg Complex.re h

theorem cyclic_ambiguity_origin (c : ZMod q → ℂ) :
    cyclicAmbiguityWeight c 0 0 = (∑ x, ‖c x‖^2)^2 := by
  have ha : cyclicAmbiguityAmplitude c 0 0 = ((∑ x, ‖c x‖^2 : ℝ):ℂ) := by
    simp only [cyclicAmbiguityAmplitude,add_zero,zero_mul,neg_zero,AddChar.map_zero_eq_one,
      mul_one,Complex.mul_conj',Complex.ofReal_sum,Complex.ofReal_pow]
  rw [cyclicAmbiguityWeight,ha,Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Finite Moyal identity with counting measure in both coordinates. -/
theorem cyclic_ambiguity_total_mass (c : ZMod q → ℂ) :
    (∑ r,∑ s, cyclicAmbiguityWeight c r s)=(q:ℝ)*(∑ x, ‖c x‖^2)^2 := by
  simpa only [zero_mul,sub_zero,AddChar.map_zero_eq_one,Complex.one_re,mul_one,
    cyclic_ambiguity_origin] using cyclic_ambiguity_real_fourier c 0 0

#print axioms cyclic_ambiguity_weight_fourier
#print axioms cyclic_ambiguity_self_fourier
#print axioms cyclic_ambiguity_frequency_mass
#print axioms cyclic_ambiguity_total_mass
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
