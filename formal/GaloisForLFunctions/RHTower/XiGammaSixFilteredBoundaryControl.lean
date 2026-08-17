import GaloisForLFunctions.RHTower.XiGammaSixCurvaturePrimeTraceWeld
import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail

/-!
# Sharp boundary control for the filtered Gamma-six primitive

The coefficient-faithful curvature/trace weld identifies raw Gamma-six curvature with a central
two-orientation difference of the canonical second Mellin primitive. This file locates the true
real abscissa of that filtered primitive and computes its nonnegative second boundary jet.

For centered grade `t` and Gauss depth `m`, the abscissa is `2m + |t|`. After the two boundary
derivatives cancel the primitive's two logarithmic denominators, the coefficient factors as

`(log 2 / m²) L_m(p) (1-p⁻ᵐ)² F(p) (1-p⁻|t|)²`.

Every factor is nonnegative. Off neutral grade it uniformly dominates a positive multiple of
`1/p`, so Euler's prime harmonic divergence forbids summability. At neutral grade it vanishes
coefficientwise. Consequently finite source-natural second-boundary mass is exactly horizontal
neutrality, forces summability of the original curvature coefficients, and universally is
equivalent to RH. Bare meromorphic continuation supplies none of this positive boundary control.
-/

open Complex Set Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- True real abscissa of the Gamma-six filtered second primitive at one retained Xi copy. -/
def gammaSixFilteredBoundaryAbscissa (m : ℕ) (q : XiZeroCopy) : ℝ :=
  2 * (m : ℝ) + |primeDepthBVWoldXiCenteredRate q.1|

/-- Positive coefficient of the literal second boundary jet at the true real abscissa. -/
def gammaSixFilteredBoundarySecondJet
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) ^ 2 *
    (p : ℝ) ^ (-gammaSixFilteredBoundaryAbscissa m q) *
      gammaSixSuspensionDeterminantPrimeCurrent m q p

/-- Literal source translation of the filtered canonical second Mellin primitive. At translation
parameter zero this is the coefficient-faithful Gamma-six central difference. -/
def gammaSixFilteredPrimeTraceTranslatedSecondPrimitive
    (m : ℕ) (p : Nat.Primes) (t : ℝ) (z : ℂ) : ℂ :=
  (gammaSixPrimeTraceHadamardWeight m p : ℂ) *
    (xiValuationOneSecondMellinPrimitiveAtom p (z - t) +
      xiValuationOneSecondMellinPrimitiveAtom p (z + t) -
      2 * xiValuationOneSecondMellinPrimitiveAtom p z)

private theorem xiValuationOneSecondMellinPrimitiveAtom_translate
    (p : Nat.Primes) (z s : ℂ) :
    xiValuationOneSecondMellinPrimitiveAtom p (z + s) =
      Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) *
        xiValuationOneSecondMellinPrimitiveAtom p s := by
  rw [xiValuationOneSecondMellinPrimitiveAtom,
    xiValuationOneSecondMellinPrimitiveAtom]
  have hexp :
      Complex.exp (-((Real.log (p : ℝ) : ℂ) * (z + s))) =
        Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) *
          Complex.exp (-((Real.log (p : ℝ) : ℂ) * s)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Source translation factors through the exact coefficient-faithful Gamma-six central
difference. This prevents the boundary jet below from being an independently fitted current. -/
theorem gammaSixFilteredPrimeTraceTranslatedSecondPrimitive_eq_exp_mul
    (m : ℕ) (p : Nat.Primes) (t : ℝ) (z : ℂ) :
    gammaSixFilteredPrimeTraceTranslatedSecondPrimitive m p t z =
      Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) *
        gammaSixFilteredPrimeTraceSecondDifference m p t := by
  rw [gammaSixFilteredPrimeTraceTranslatedSecondPrimitive,
    gammaSixFilteredPrimeTraceSecondDifference]
  rw [show z - (t : ℂ) = z + (-(t : ℂ)) by ring]
  have hzero := xiValuationOneSecondMellinPrimitiveAtom_translate p z 0
  simp only [add_zero] at hzero
  rw [xiValuationOneSecondMellinPrimitiveAtom_translate,
    xiValuationOneSecondMellinPrimitiveAtom_translate, hzero]
  ring

/-- The literal second complex derivative of the source-translated primitive is the prime-log
Hessian of the same Gamma-six central-difference coefficient. -/
theorem secondDeriv_gammaSixFilteredPrimeTraceTranslatedSecondPrimitive
    (m : ℕ) (p : Nat.Primes) (t : ℝ) (z : ℂ) :
    deriv (fun w : ℂ => deriv
      (gammaSixFilteredPrimeTraceTranslatedSecondPrimitive m p t) w) z =
      (Real.log (p : ℝ) : ℂ) ^ 2 *
        Complex.exp (-((Real.log (p : ℝ) : ℂ) * z)) *
          gammaSixFilteredPrimeTraceSecondDifference m p t := by
  let a : ℂ := -(Real.log (p : ℝ) : ℂ)
  let C : ℂ := gammaSixFilteredPrimeTraceSecondDifference m p t
  have hfun : gammaSixFilteredPrimeTraceTranslatedSecondPrimitive m p t =
      fun w : ℂ => Complex.exp (a * w) * C := by
    funext w
    rw [gammaSixFilteredPrimeTraceTranslatedSecondPrimitive_eq_exp_mul]
    dsimp only [a, C]
    congr 2
    ring
  rw [hfun]
  have hfirst :
      (fun w : ℂ => deriv (fun v : ℂ => Complex.exp (a * v) * C) w) =
        fun w : ℂ => Complex.exp (a * w) * a * C := by
    funext w
    have hlin : HasDerivAt (fun v : ℂ => a * v) a w := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul a
    exact (hlin.cexp.mul_const C).deriv
  rw [hfirst]
  have hlin : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul a
  have hsecond := ((hlin.cexp.mul_const a).mul_const C).deriv
  change deriv (fun w : ℂ => Complex.exp (a * w) * a * C) z = _
  rw [hsecond]
  dsimp only [a, C]
  ring

/-- **Literal boundary weld.** The nonnegative real second jet is exactly the second complex
derivative of the coefficient-faithful source-translated primitive at its Xi-selected abscissa. -/
theorem secondDeriv_gammaSixFilteredPrimeTraceTranslatedSecondPrimitive_at_boundary
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    deriv (fun w : ℂ => deriv
      (gammaSixFilteredPrimeTraceTranslatedSecondPrimitive m p
        (primeDepthBVWoldXiCenteredRate q.1)) w)
        (gammaSixFilteredBoundaryAbscissa m q : ℂ) =
      (gammaSixFilteredBoundarySecondJet m q p : ℂ) := by
  have hP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hexp :
      Complex.exp (-((Real.log (p : ℝ) : ℂ) *
        (gammaSixFilteredBoundaryAbscissa m q : ℂ))) =
      (((p : ℝ) ^ (-gammaSixFilteredBoundaryAbscissa m q) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hP, Complex.ofReal_exp]
    push_cast
    congr 1
    ring
  rw [secondDeriv_gammaSixFilteredPrimeTraceTranslatedSecondPrimitive, hexp,
    ← gammaSixSuspensionDeterminantPrimeCurrent_eq_filteredPrimeTrace]
  rw [gammaSixFilteredBoundarySecondJet]
  push_cast
  ring

private theorem gammaSixSuspensionDeterminantPrimeCurrent_eq_rpow_formula
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixSuspensionDeterminantPrimeCurrent m q p =
      (Real.log 2 / (m : ℝ) ^ 2) *
        gaussLocalFactorWeight m p * ((p : ℝ) ^ m - 1) ^ 2 *
        primeActivationOccupancyFisherDensity p /
          Real.log (p : ℝ) ^ 2 *
        ((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 +
          (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) - 2) := by
  let P : ℝ := p
  let L : ℝ := Real.log P
  let t : ℝ := primeDepthBVWoldXiCenteredRate q.1
  have hP : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 < P := by dsimp [P]; exact_mod_cast p.2.one_lt
  have hL : L ≠ 0 := by
    dsimp [L]
    exact (Real.log_pos hP1).ne'
  have hres := gaussChannelResidueCurrent_mul_log hm p
  have hres' : gaussChannelResidueCurrent m p * L =
      2 / (m : ℝ) ^ 2 * gaussLocalFactorWeight m p * (P ^ m - 1) ^ 2 := by
    simpa only [P, L] using hres
  have hdef : P ^ t + P ^ (-t) - 2 =
      2 * Real.cosh (L * t) - 2 := by
    simpa only [L, mul_comm] using
      (HTGeometry.rpow_add_rpow_neg_sub_two_eq hP t)
  rw [gammaSixSuspensionDeterminantPrimeCurrent,
    gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
    gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy,
    reciprocalCharacterSplitEnergy,
    gaussReciprocalCharacterWeight]
  change 2 * (Real.log 2 / 2 * gaussChannelResidueCurrent m p *
      primeActivationOccupancyFisherDensity p / L) *
        (Real.cosh (L * t) - 1) =
      (Real.log 2 / (m : ℝ) ^ 2) *
        gaussLocalFactorWeight m p * (P ^ m - 1) ^ 2 *
        primeActivationOccupancyFisherDensity p / L ^ 2 *
        (P ^ t + P ^ (-t) - 2)
  have hcosh : Real.cosh (L * t) - 1 =
      (P ^ t + P ^ (-t) - 2) / 2 := by
    linarith [hdef]
  have hfirst :
      2 * (Real.log 2 / 2 * gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p / L) *
          ((P ^ t + P ^ (-t) - 2) / 2) =
        (Real.log 2 / 2 *
          (gaussChannelResidueCurrent m p * L) *
          primeActivationOccupancyFisherDensity p / L ^ 2) *
          (P ^ t + P ^ (-t) - 2) := by
    field_simp [hL]
  rw [hcosh, hfirst, hres']
  ring_nf

private theorem rpow_symmetric_gap
    (P u : ℝ) (hP : 0 < P) :
    (P ^ u + P ^ (-u) - 2) * P ^ (-u) =
      (1 - P ^ (-u)) ^ 2 := by
  have hprod : P ^ u * P ^ (-u) = 1 := by
    rw [← Real.rpow_add hP]
    norm_num
  ring_nf
  rw [hprod]

private theorem rpow_nat_gap
    (P : ℝ) (m : ℕ) (hP : 0 < P) :
    (P ^ m - 1) ^ 2 * P ^ (-(2 * (m : ℝ))) =
      (1 - P ^ (-(m : ℝ))) ^ 2 := by
  have hprod : P ^ (m : ℝ) * P ^ (-(m : ℝ)) = 1 := by
    rw [← Real.rpow_add hP]
    norm_num
  have htwo : P ^ (-(2 * (m : ℝ))) =
      P ^ (-(m : ℝ)) * P ^ (-(m : ℝ)) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  have hprodNat : P ^ m * P ^ (-(m : ℝ)) = 1 := by
    rw [← Real.rpow_natCast]
    exact hprod
  rw [htwo]
  calc
    (P ^ m - 1) ^ 2 * (P ^ (-(m : ℝ)) * P ^ (-(m : ℝ))) =
        ((P ^ m - 1) * P ^ (-(m : ℝ))) ^ 2 := by ring
    _ = (1 - P ^ (-(m : ℝ))) ^ 2 := by
      congr 1
      calc
        (P ^ m - 1) * P ^ (-(m : ℝ)) =
            P ^ m * P ^ (-(m : ℝ)) - P ^ (-(m : ℝ)) := by ring
        _ = 1 - P ^ (-(m : ℝ)) := by rw [hprodNat]

/-- Exact positive factorization of the second boundary jet. -/
theorem gammaSixFilteredBoundarySecondJet_eq_factorized
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p =
      Real.log 2 / (m : ℝ) ^ 2 *
        gaussLocalFactorWeight m p *
        (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 *
        primeActivationOccupancyFisherDensity p *
        (1 - (p : ℝ) ^
          (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 := by
  let P : ℝ := p
  let L : ℝ := Real.log P
  let t : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let u : ℝ := |t|
  have hP : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 < P := by dsimp [P]; exact_mod_cast p.2.one_lt
  have hL : L ≠ 0 := by
    dsimp [L]
    exact (Real.log_pos hP1).ne'
  have habs : P ^ t + P ^ (-t) = P ^ u + P ^ (-u) := by
    dsimp only [u]
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos (le_of_not_ge ht)]
      ring
  have hshape : (P ^ t + P ^ (-t) - 2) * P ^ (-u) =
      (1 - P ^ (-u)) ^ 2 := by
    rw [habs]
    exact rpow_symmetric_gap P u hP
  have hgap := rpow_nat_gap P m hP
  have hsigma : P ^ (-gammaSixFilteredBoundaryAbscissa m q) =
      P ^ (-(2 * (m : ℝ))) * P ^ (-u) := by
    rw [gammaSixFilteredBoundaryAbscissa]
    dsimp only [u, t]
    rw [← Real.rpow_add hP]
    congr 1
    ring
  rw [gammaSixFilteredBoundarySecondJet,
    gammaSixSuspensionDeterminantPrimeCurrent_eq_rpow_formula hm q p]
  change L ^ 2 * P ^ (-gammaSixFilteredBoundaryAbscissa m q) *
      ((Real.log 2 / (m : ℝ) ^ 2) * gaussLocalFactorWeight m p *
        (P ^ m - 1) ^ 2 * primeActivationOccupancyFisherDensity p / L ^ 2 *
          (P ^ t + P ^ (-t) - 2)) =
      Real.log 2 / (m : ℝ) ^ 2 * gaussLocalFactorWeight m p *
        (1 - P ^ (-(m : ℝ))) ^ 2 * primeActivationOccupancyFisherDensity p *
          (1 - P ^ (-u)) ^ 2
  rw [hsigma]
  calc
    L ^ 2 * (P ^ (-(2 * (m : ℝ))) * P ^ (-u)) *
        ((Real.log 2 / (m : ℝ) ^ 2) * gaussLocalFactorWeight m p *
          (P ^ m - 1) ^ 2 * primeActivationOccupancyFisherDensity p / L ^ 2 *
            (P ^ t + P ^ (-t) - 2)) =
        (Real.log 2 / (m : ℝ) ^ 2) * gaussLocalFactorWeight m p *
          ((P ^ m - 1) ^ 2 * P ^ (-(2 * (m : ℝ)))) *
          primeActivationOccupancyFisherDensity p *
          ((P ^ t + P ^ (-t) - 2) * P ^ (-u)) := by
      field_simp [hL]
    _ = _ := by rw [hgap, hshape]

private theorem half_pow_le_gaussLocalFactorWeight
    (m : ℕ) (p : Nat.Primes) :
    (1 / 2 : ℝ) ^ (2 * m) ≤ gaussLocalFactorWeight m p := by
  let P : ℝ := p
  have hP2 : (2 : ℝ) ≤ P := by
    dsimp [P]
    exact_mod_cast p.2.two_le
  have hP : 0 < P := by linarith
  have hratio : (1 / 2 : ℝ) ≤ (P - 1) / P := by
    rw [le_div_iff₀ hP]
    linarith
  rw [gaussLocalFactorWeight]
  exact pow_le_pow_left₀ (by norm_num) hratio (2 * m)

private theorem one_fourth_le_rpow_nat_gap
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    (1 / 4 : ℝ) ≤ (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 := by
  let P : ℝ := p
  let x : ℝ := P ^ (-(m : ℝ))
  have hP : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hpowNat : (2 : ℝ) ≤ P ^ m := by
    have hnat : (2 : ℕ) ≤ (p : ℕ) ^ m :=
      p.2.two_le.trans (Nat.le_pow (by omega : 0 < m))
    dsimp [P]
    exact_mod_cast hnat
  have hx0 : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos hP _
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    rw [Real.rpow_neg hP.le, Real.rpow_natCast]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpowNat)
  change (1 / 4 : ℝ) ≤ (1 - x) ^ 2
  nlinarith [sq_nonneg (x - 1 / 2)]

private theorem prime_rpow_neg_le_two_rpow_neg
    {u : ℝ} (hu : 0 ≤ u) (p : Nat.Primes) :
    (p : ℝ) ^ (-u) ≤ (2 : ℝ) ^ (-u) := by
  have hP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [Real.rpow_neg hP.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (2 : ℝ) ^ u ≤ (p : ℝ) ^ u :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast p.2.two_le) hu
  simpa only [one_div] using
    (one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) u) hpow)

private theorem two_gap_sq_le_prime_gap_sq
    {u : ℝ} (hu : 0 < u) (p : Nat.Primes) :
    (1 - (2 : ℝ) ^ (-u)) ^ 2 ≤
      (1 - (p : ℝ) ^ (-u)) ^ 2 := by
  have htwo0 : 0 < (2 : ℝ) ^ (-u) := Real.rpow_pos_of_pos (by norm_num) _
  have htwo1 : (2 : ℝ) ^ (-u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hu)
  have hp0 : 0 ≤ (p : ℝ) ^ (-u) := Real.rpow_nonneg (by positivity) _
  have hle := prime_rpow_neg_le_two_rpow_neg hu.le p
  have hprod : 0 ≤
      ((1 - (p : ℝ) ^ (-u)) - (1 - (2 : ℝ) ^ (-u))) *
      ((1 - (p : ℝ) ^ (-u)) + (1 - (2 : ℝ) ^ (-u))) := by
    apply mul_nonneg
    · linarith
    · linarith
  nlinarith

/-- Explicit positive coefficient of the harmonic-prime lower bound. -/
def gammaSixFilteredBoundaryHarmonicConstant
    (m : ℕ) (q : XiZeroCopy) : ℝ :=
  Real.log 2 / (m : ℝ) ^ 2 *
    (1 / 2 : ℝ) ^ (2 * m) * (1 / 4 : ℝ) * (1 / 4 : ℝ) *
      (1 - (2 : ℝ) ^
        (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2

theorem gammaSixFilteredBoundaryHarmonicConstant_pos
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    0 < gammaSixFilteredBoundaryHarmonicConstant m q := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hu : 0 < |primeDepthBVWoldXiCenteredRate q.1| := abs_pos.mpr hq
  have hpow : (2 : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hu)
  rw [gammaSixFilteredBoundaryHarmonicConstant]
  positivity

/-- Every off-neutral boundary Hessian coefficient dominates one fixed positive multiple of
`1/p`; at neutral grade both sides vanish. -/
theorem gammaSixFilteredBoundaryHarmonicConstant_mul_one_div_le
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryHarmonicConstant m q * (1 / (p : ℝ)) ≤
      gammaSixFilteredBoundarySecondJet m q p := by
  by_cases hq : primeDepthBVWoldXiCenteredRate q.1 = 0
  · rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p]
    simp [gammaSixFilteredBoundaryHarmonicConstant, hq]
  let P : ℝ := p
  let u : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hP : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hc : 0 ≤ Real.log 2 / (m : ℝ) ^ 2 := by positivity
  have hlocal := half_pow_le_gaussLocalFactorWeight m p
  have hlocal0 : 0 ≤ gaussLocalFactorWeight m p :=
    (gaussLocalFactorWeight_pos m p).le
  have hgap := one_fourth_le_rpow_nat_gap hm p
  have hgap0 : 0 ≤ (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 := sq_nonneg _
  have hF := (primeActivationOccupancyFisherDensity_bounds p).1
  have hF0 : 0 ≤ primeActivationOccupancyFisherDensity p :=
    (primeActivationOccupancyFisherDensity_pos' p).le
  have hshape := two_gap_sq_le_prime_gap_sq
    (show 0 < u from abs_pos.mpr hq) p
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p]
  change gammaSixFilteredBoundaryHarmonicConstant m q * (1 / P) ≤ _
  have hrewrite :
      gammaSixFilteredBoundaryHarmonicConstant m q * (1 / P) =
        (Real.log 2 / (m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (2 * m) *
          (1 / 4 : ℝ) * (1 / (4 * P)) *
            (1 - (2 : ℝ) ^ (-u)) ^ 2 := by
    rw [gammaSixFilteredBoundaryHarmonicConstant]
    dsimp only [u]
    field_simp [hP.ne']
  rw [hrewrite]
  gcongr

theorem gammaSixFilteredBoundarySecondJet_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundarySecondJet m q p := by
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p]
  have hlocal := (gaussLocalFactorWeight_pos m p).le
  have hF := (primeActivationOccupancyFisherDensity_pos' p).le
  positivity

/-- **Finite-level source boundary control.** Every finite Euler-subset Hessian is bounded by one
constant. This formulation only mentions finite source packets; it does not assume an infinite
sum or hide the desired Tauberian conclusion in the definition. -/
def XiGammaSixFilteredBoundaryControlled (m : ℕ) (q : XiZeroCopy) : Prop :=
  ∃ C : ℝ, ∀ F : Finset Nat.Primes,
    ∑ p ∈ F, gammaSixFilteredBoundarySecondJet m q p ≤ C

/-- For the nonnegative literal Hessian, uniform control of every finite source packet is exactly
absolute summability. This is the compactness/Tauberian passage missing from continuation alone. -/
theorem sourceNaturalBoundaryControl_iff_summable
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    XiGammaSixFilteredBoundaryControlled m q ↔
      Summable (gammaSixFilteredBoundarySecondJet m q) := by
  constructor
  · rintro ⟨C, hC⟩
    exact summable_of_sum_le (c := C)
      (gammaSixFilteredBoundarySecondJet_nonneg hm q) hC
  · intro hsum
    refine ⟨∑' p, gammaSixFilteredBoundarySecondJet m q p, ?_⟩
    intro F
    exact hsum.sum_le_tsum F
      (fun p _ => gammaSixFilteredBoundarySecondJet_nonneg hm q p)

/-- Sharp Tauberian wall: the nonnegative second boundary jet is summable exactly at neutral
horizontal grade. -/
theorem summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixFilteredBoundarySecondJet m q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · intro hsum
    by_contra hq
    have hC := gammaSixFilteredBoundaryHarmonicConstant_pos hm q hq
    have hscaled : Summable (fun p : Nat.Primes =>
        gammaSixFilteredBoundaryHarmonicConstant m q * (1 / (p : ℝ))) :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (gammaSixFilteredBoundaryHarmonicConstant_mul_one_div_le hm q) hsum
    have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
      (summable_mul_left_iff hC.ne').mp hscaled
    exact Nat.Primes.not_summable_one_div hharmonic
  · intro hrate
    have hzero : gammaSixFilteredBoundarySecondJet m q = 0 := by
      funext p
      rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p, hrate]
      simp
    rw [hzero]
    exact summable_zero

/-- Finite source boundary Hessian forces summability of the original nonnegative Gamma-six
curvature coefficients. This is the positive Tauberian implication absent from meromorphic
continuation alone. -/
theorem sourceNaturalBoundaryControl_forces_gammaSixCurvatureSummability
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hcontrol : XiGammaSixFilteredBoundaryControlled m q) :
    Summable (gammaSixSuspensionDeterminantPrimeCurrent m q) := by
  apply (summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero
    hm q).2
  exact (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero
    hm q).1 ((sourceNaturalBoundaryControl_iff_summable hm q).1 hcontrol)

/-- Every proposed finite-packet Hessian bound is violated off neutral grade. This is the
quantitative obstruction that any source-natural C² producer must overcome. -/
theorem exists_finset_gammaSixFilteredBoundarySecondJet_sum_gt
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) (C : ℝ) :
    ∃ F : Finset Nat.Primes,
      C < ∑ p ∈ F, gammaSixFilteredBoundarySecondJet m q p := by
  by_contra hbound
  push Not at hbound
  have hcontrol : XiGammaSixFilteredBoundaryControlled m q := ⟨C, hbound⟩
  exact hq ((summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero
    hm q).1 ((sourceNaturalBoundaryControl_iff_summable hm q).1 hcontrol))

/-- **Summable-majorant classification.** A coefficientwise summable source observable can control
the exact boundary Hessian precisely on the neutral fibre. Thus importing a summable Wold,
Stokes, or Route-P tail is useful only after a coefficient-faithful domination theorem; such a
domination is itself already a genuine line-forcing producer. -/
theorem exists_summable_majorant_gammaSixFilteredBoundarySecondJet_iff
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    (∃ M : Nat.Primes → ℝ,
      Summable M ∧
        ∀ p, gammaSixFilteredBoundarySecondJet m q p ≤ M p) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  constructor
  · rintro ⟨M, hM, hmajor⟩
    have hsum : Summable (gammaSixFilteredBoundarySecondJet m q) :=
      Summable.of_nonneg_of_le
        (gammaSixFilteredBoundarySecondJet_nonneg hm q) hmajor hM
    exact (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero
      hm q).1 hsum
  · intro hrate
    let J : Nat.Primes → ℝ := gammaSixFilteredBoundarySecondJet m q
    refine ⟨J, ?_, fun _ => le_rfl⟩
    exact (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero
      hm q).2 hrate

/-- Universal source boundary control is exactly RH. -/
theorem forall_sourceNaturalBoundaryControl_iff_riemannHypothesis
    {m : ℕ} (hm : 1 ≤ m) :
    (∀ q : XiZeroCopy, XiGammaSixFilteredBoundaryControlled m q) ↔
      RiemannHypothesis := by
  rw [← forall_summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_riemannHypothesis hm]
  constructor
  · intro h q
    exact sourceNaturalBoundaryControl_forces_gammaSixCurvatureSummability hm q (h q)
  · intro h q
    apply (sourceNaturalBoundaryControl_iff_summable hm q).2
    apply (summable_gammaSixFilteredBoundarySecondJet_iff_centeredRate_eq_zero hm q).2
    exact (summable_gammaSixSuspensionDeterminantPrimeCurrent_iff_centeredRate_eq_zero hm q).1
      (h q)

/-! ## Sharp lower-order boundary regularity -/

/-- Coefficientwise boundary value of the filtered second primitive. -/
def gammaSixFilteredBoundaryValue
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-gammaSixFilteredBoundaryAbscissa m q) *
    gammaSixSuspensionDeterminantPrimeCurrent m q p

/-- Coefficientwise first boundary jet of the filtered second primitive. -/
def gammaSixFilteredBoundaryFirstJet
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) *
    (p : ℝ) ^ (-gammaSixFilteredBoundaryAbscissa m q) *
      gammaSixSuspensionDeterminantPrimeCurrent m q p

private theorem gaussLocalFactorWeight_le_one
    (m : ℕ) (p : Nat.Primes) :
    gaussLocalFactorWeight m p ≤ 1 := by
  have hP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hP1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hratio0 : 0 ≤ ((p : ℝ) - 1) / (p : ℝ) :=
    div_nonneg (sub_nonneg.mpr hP1.le) hP.le
  have hratio1 : ((p : ℝ) - 1) / (p : ℝ) ≤ 1 := by
    rw [div_le_one hP]
    linarith
  rw [gaussLocalFactorWeight]
  exact pow_le_one₀ hratio0 hratio1

private theorem rpow_nat_gap_le_one (m : ℕ) (p : Nat.Primes) :
    (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 ≤ 1 := by
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hx0 : 0 ≤ (p : ℝ) ^ (-(m : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hx1 : (p : ℝ) ^ (-(m : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1
      (neg_nonpos.mpr (Nat.cast_nonneg m))
  nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 2 - (p : ℝ) ^ (-(m : ℝ)))]

private theorem rpow_abs_gap_le_one
    (u : ℝ) (hu : 0 ≤ u) (p : Nat.Primes) :
    (1 - (p : ℝ) ^ (-u)) ^ 2 ≤ 1 := by
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hx0 : 0 ≤ (p : ℝ) ^ (-u) := Real.rpow_nonneg (by positivity) _
  have hx1 : (p : ℝ) ^ (-u) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1 (neg_nonpos.mpr hu)
  nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 2 - (p : ℝ) ^ (-u))]

/-- Uniform harmonic upper bound for the second boundary jet. -/
theorem gammaSixFilteredBoundarySecondJet_le_harmonic
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p ≤
      (Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)) := by
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p]
  have hc : 0 ≤ Real.log 2 / (m : ℝ) ^ 2 := by positivity
  have hl := gaussLocalFactorWeight_le_one m p
  have hl0 := (gaussLocalFactorWeight_pos m p).le
  have hg := rpow_nat_gap_le_one m p
  have hg0 : 0 ≤ (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 := sq_nonneg _
  have hF := (primeActivationOccupancyFisherDensity_bounds p).2
  have hF0 := (primeActivationOccupancyFisherDensity_pos' p).le
  have hs :
      (1 - (p : ℝ) ^
        (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 ≤ 1 :=
    rpow_abs_gap_le_one |primeDepthBVWoldXiCenteredRate q.1|
      (abs_nonneg _) p
  have hs0 : 0 ≤ (1 - (p : ℝ) ^
      (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 := sq_nonneg _
  calc
    Real.log 2 / (m : ℝ) ^ 2 * gaussLocalFactorWeight m p *
        (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 *
        primeActivationOccupancyFisherDensity p *
        (1 - (p : ℝ) ^
          (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 ≤
      (Real.log 2 / (m : ℝ) ^ 2) * 1 * 1 *
        (1 / (p : ℝ)) * 1 := by gcongr
    _ = (Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)) := by ring

theorem gammaSixFilteredBoundaryFirstJet_eq_secondJet_div_log
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryFirstJet m q p =
      gammaSixFilteredBoundarySecondJet m q p / Real.log (p : ℝ) := by
  have hL : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  rw [gammaSixFilteredBoundaryFirstJet, gammaSixFilteredBoundarySecondJet]
  field_simp [hL]

theorem gammaSixFilteredBoundaryValue_eq_secondJet_div_log_sq
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryValue m q p =
      gammaSixFilteredBoundarySecondJet m q p / Real.log (p : ℝ) ^ 2 := by
  have hL : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  rw [gammaSixFilteredBoundaryValue, gammaSixFilteredBoundarySecondJet]
  field_simp [hL]

theorem gammaSixFilteredBoundaryFirstJet_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryFirstJet m q p := by
  rw [gammaSixFilteredBoundaryFirstJet_eq_secondJet_div_log]
  exact div_nonneg (gammaSixFilteredBoundarySecondJet_nonneg hm q p)
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).le

theorem gammaSixFilteredBoundaryValue_nonneg
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryValue m q p := by
  rw [gammaSixFilteredBoundaryValue_eq_secondJet_div_log_sq]
  exact div_nonneg (gammaSixFilteredBoundarySecondJet_nonneg hm q p)
    (sq_nonneg _)

theorem gammaSixFilteredBoundaryFirstJet_le_logMajorant
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryFirstJet m q p ≤
      (Real.log 2 / (m : ℝ) ^ 2) *
        (1 / ((p : ℝ) * Real.log (p : ℝ) ^ (1 : ℝ))) := by
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [gammaSixFilteredBoundaryFirstJet_eq_secondJet_div_log]
  calc
    gammaSixFilteredBoundarySecondJet m q p / Real.log (p : ℝ) ≤
        ((Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ))) /
          Real.log (p : ℝ) :=
      div_le_div_of_nonneg_right
        (gammaSixFilteredBoundarySecondJet_le_harmonic hm q p) hL.le
    _ = _ := by
      rw [Real.rpow_one]
      field_simp [hL.ne', (show (p : ℝ) ≠ 0 by exact_mod_cast p.2.ne_zero)]

theorem gammaSixFilteredBoundaryValue_le_logSqMajorant
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryValue m q p ≤
      (Real.log 2 / (m : ℝ) ^ 2) *
        (1 / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℝ))) := by
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [gammaSixFilteredBoundaryValue_eq_secondJet_div_log_sq]
  calc
    gammaSixFilteredBoundarySecondJet m q p / Real.log (p : ℝ) ^ 2 ≤
        ((Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ))) /
          Real.log (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (gammaSixFilteredBoundarySecondJet_le_harmonic hm q p) (sq_nonneg _)
    _ = _ := by
      rw [← Real.rpow_natCast]
      norm_num
      field_simp [hL.ne', (show (p : ℝ) ≠ 0 by exact_mod_cast p.2.ne_zero)]

/-- Boundary value is unconditionally absolutely summable on every Xi fibre. -/
theorem summable_gammaSixFilteredBoundaryValue
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixFilteredBoundaryValue m q) := by
  apply Summable.of_nonneg_of_le
    (gammaSixFilteredBoundaryValue_nonneg hm q)
    (gammaSixFilteredBoundaryValue_le_logSqMajorant hm q)
  exact (Sieve.summable_primes_one_div_mul_log_rpow
    (show (0 : ℝ) < 2 by norm_num)).mul_left _

/-- First boundary jet is unconditionally absolutely summable on every Xi fibre. -/
theorem summable_gammaSixFilteredBoundaryFirstJet
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixFilteredBoundaryFirstJet m q) := by
  apply Summable.of_nonneg_of_le
    (gammaSixFilteredBoundaryFirstJet_nonneg hm q)
    (gammaSixFilteredBoundaryFirstJet_le_logMajorant hm q)
  exact (Sieve.summable_primes_one_div_mul_log_rpow
    (show (0 : ℝ) < 1 by norm_num)).mul_left _

end

end RHTower
