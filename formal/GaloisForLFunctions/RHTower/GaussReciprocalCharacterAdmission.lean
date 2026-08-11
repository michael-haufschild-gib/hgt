import GaloisForLFunctions.HTGeometry.ReciprocalCharacterRealFormMechanics
import GaloisForLFunctions.RHTower.FisherDeconvolvedSameCarrierOrientationLaw
import GaloisForLFunctions.RHTower.GaussHodgeMassCurrent

/-!
# Gauss reciprocal-character admission

The literal Gauss residue/Fisher packet realizes reciprocal-character virial mechanics.  Its
Hodge mass is exactly the Euler-generated virial current and inherits its quadratic lower bound.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Source weight placing the Gauss Hodge shape in reciprocal-character normalization. -/
def gaussReciprocalCharacterWeight (m : ℕ) (p : Nat.Primes) : ℝ :=
  Real.log 2 / 2 * gaussChannelResidueCurrent m p *
    primeActivationOccupancyFisherDensity p / Real.log (p : ℝ)

theorem gaussReciprocalCharacterWeight_pos {m : ℕ} (hm : 1 ≤ m)
    (p : Nat.Primes) : 0 < gaussReciprocalCharacterWeight m p := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hc := gaussChannelResidueCurrent_pos hm p
  have hf := primeActivationOccupancyFisherDensity_pos' p
  rw [gaussReciprocalCharacterWeight]
  positivity

/-- Fourth-organ generator identity: Gauss Hodge mass is the reciprocal virial current. -/
theorem gaussHodgeMassCurrent_eq_reciprocalCharacterVirial
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p =
      reciprocalCharacterVirialCurrent (gaussReciprocalCharacterWeight m p)
        (Real.log (p : ℝ)) (primeDepthBVWoldXiCenteredRate q.1) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [gaussHodgeMassCurrent_eq_boost_square, hodgeMassShape,
    reciprocalCharacterVirialCurrent, gaussReciprocalCharacterWeight,
    rpow_sub_rpow_neg_eq_two_sinh hp]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  field_simp

/-- Literal Gauss Hodge current inherits the universal virial quadratic lower bound. -/
theorem gaussHodgeMassCurrent_virial_lower {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    Real.log 2 * gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) *
          primeDepthBVWoldXiCenteredRate q.1 ^ 2 ≤
      gaussHodgeMassCurrent m q p := by
  rw [gaussHodgeMassCurrent_eq_reciprocalCharacterVirial]
  have h := reciprocalCharacterVirial_quadratic_lower
    (a := gaussReciprocalCharacterWeight m p)
    (lambda := Real.log (p : ℝ))
    (t := primeDepthBVWoldXiCenteredRate q.1)
    (gaussReciprocalCharacterWeight_pos hm p).le
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  refine le_trans (le_of_eq ?_) h
  rw [gaussReciprocalCharacterWeight]
  field_simp

/-! ## Cofinal admission -/

/-- The exact Gauss residue/Fisher coefficient uniformly dominates a nonzero multiple of the
prime harmonic density. -/
theorem gaussResidueFisherLog_harmonic_lower {m : ℕ} (hm : 1 ≤ m)
    (p : Nat.Primes) :
    ((1 / 2 : ℝ) ^ (2 * m) / (2 * (m : ℝ) ^ 2)) * (1 / (p : ℝ)) ≤
      gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by
  let P : ℝ := p
  let M : ℝ := m
  have hp2 : (2 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast p.prop.two_le
  have hp0 : 0 < P := lt_of_lt_of_le (by norm_num) hp2
  have hm0 : 0 < M := by
    dsimp [M]
    exact_mod_cast (show 0 < m by omega)
  have hratio : (1 / 2 : ℝ) ≤ (P - 1) / P := by
    rw [le_div_iff₀ hp0]
    linarith
  have hlocal : (1 / 2 : ℝ) ^ (2 * m) ≤ gaussLocalFactorWeight m p := by
    rw [gaussLocalFactorWeight]
    exact pow_le_pow_left₀ (by norm_num) hratio (2 * m)
  have hpow2Nat : 2 ≤ (p : ℕ) ^ m :=
    p.prop.two_le.trans (Nat.le_pow (by omega : 0 < m))
  have hpow2 : (2 : ℝ) ≤ P ^ m := by
    dsimp [P]
    exact_mod_cast hpow2Nat
  have hgap : 1 ≤ (P ^ m - 1) ^ 2 := by
    nlinarith [sq_nonneg (P ^ m - 1)]
  have hcoef : 0 ≤ 2 / M ^ 2 := by positivity
  have hlocal0 : 0 ≤ gaussLocalFactorWeight m p :=
    le_trans (by positivity) hlocal
  have hcurrent :
      2 / M ^ 2 * (1 / 2 : ℝ) ^ (2 * m) ≤
        gaussChannelResidueCurrent m p * Real.log (p : ℝ) := by
    calc
      2 / M ^ 2 * (1 / 2 : ℝ) ^ (2 * m) =
          2 / M ^ 2 * (1 / 2 : ℝ) ^ (2 * m) * 1 := by ring
      _ ≤ 2 / M ^ 2 * gaussLocalFactorWeight m p * 1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlocal hcoef) zero_le_one
      _ ≤ 2 / M ^ 2 * gaussLocalFactorWeight m p * (P ^ m - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hgap (mul_nonneg hcoef hlocal0)
      _ = gaussChannelResidueCurrent m p * Real.log (p : ℝ) := by
        rw [gaussChannelResidueCurrent_mul_log hm p]
  have hfisher := (primeActivationOccupancyFisherDensity_bounds p).1
  have hproduct := mul_le_mul hcurrent hfisher (by positivity)
    (mul_nonneg (gaussChannelResidueCurrent_pos hm p).le
      (Real.log_pos (by exact_mod_cast p.prop.one_lt)).le)
  calc
    ((1 / 2 : ℝ) ^ (2 * m) / (2 * (m : ℝ) ^ 2)) * (1 / (p : ℝ)) =
        (2 / M ^ 2 * (1 / 2 : ℝ) ^ (2 * m)) * (1 / (4 * P)) := by
      dsimp [M, P]
      ring
    _ ≤ (gaussChannelResidueCurrent m p * Real.log (p : ℝ)) *
        primeActivationOccupancyFisherDensity p := hproduct
    _ = gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p * Real.log (p : ℝ) := by ring

/-- Positive coefficient multiplying the divergent harmonic prime family off the neutral form. -/
def gaussVirialAdmissionConstant (m : ℕ) (q : XiZeroCopy) : ℝ :=
  Real.log 2 * primeDepthBVWoldXiCenteredRate q.1 ^ 2 *
    ((1 / 2 : ℝ) ^ (2 * m) / (2 * (m : ℝ) ^ 2))

theorem gaussVirialAdmissionConstant_pos {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    0 < gaussVirialAdmissionConstant m q := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [gaussVirialAdmissionConstant]
  positivity

/-- Every off-neutral Gauss virial term dominates one fixed positive multiple of `1/p`. -/
theorem gaussVirialAdmissionConstant_mul_harmonic_le {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussVirialAdmissionConstant m q * (1 / (p : ℝ)) ≤
      gaussHodgeMassCurrent m q p := by
  have hbase := gaussResidueFisherLog_harmonic_lower hm p
  have hscale : 0 ≤ Real.log 2 * primeDepthBVWoldXiCenteredRate q.1 ^ 2 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  have hvirial := gaussHodgeMassCurrent_virial_lower hm q p
  rw [gaussVirialAdmissionConstant]
  exact le_trans (le_of_eq (by ring)) (le_trans hscaled (le_trans (le_of_eq (by ring)) hvirial))

/-- Off the neutral real form the all-prime Gauss virial current is not summable. -/
theorem not_summable_gaussHodgeMassCurrent_of_rate_ne_zero {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    ¬ Summable (gaussHodgeMassCurrent m q) := by
  intro hsum
  have hC := gaussVirialAdmissionConstant_pos hm q hq
  have hscaled : Summable (fun p : Nat.Primes =>
      gaussVirialAdmissionConstant m q * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (gaussVirialAdmissionConstant_mul_harmonic_le hm q) hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff hC.ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Cofinal admission classification: prime summability is exactly radial neutrality. -/
theorem summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) :
    Summable (gaussHodgeMassCurrent m q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hsum
    by_contra hq
    exact not_summable_gaussHodgeMassCurrent_of_rate_ne_zero hm q hq hsum
  · intro hq
    have hre : (q.1 : ℂ).re = 1 / 2 := by
      rw [primeDepthBVWoldXiCenteredRate] at hq
      linarith
    have hzero : gaussHodgeMassCurrent m q = 0 := by
      funext p
      exact (gaussHodgeMassCurrent_eq_zero_iff hm q p).2 hre
    rw [hzero]
    exact summable_zero

/-- The resulting trace-ideal admission condition is exactly the RH selection gate. -/
theorem forall_summable_gaussHodgeMassCurrent_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) :
    (∀ q : XiZeroCopy, Summable (gaussHodgeMassCurrent m q)) ↔ RiemannHypothesis := by
  rw [← gaussHodgeMass_vanishing_iff_riemannHypothesis hm]
  constructor
  · intro h q p
    have hrate := (summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero hm q).1 (h q)
    apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
    rw [primeDepthBVWoldXiCenteredRate] at hrate
    linarith
  · intro h q
    apply (summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero hm q).2
    have hre := (gaussHodgeMassCurrent_eq_zero_iff hm q ⟨2, Nat.prime_two⟩).1
      (h q ⟨2, Nat.prime_two⟩)
    rw [primeDepthBVWoldXiCenteredRate]
    linarith

end


end RHTower
