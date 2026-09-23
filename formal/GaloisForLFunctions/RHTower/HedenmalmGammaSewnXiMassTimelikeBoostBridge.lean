import GaloisForLFunctions.RHTower.HedenmalmGammaSewnBurnolHolonomyMassShell
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherAffineResidueBridge
import GaloisForLFunctions.RHTower.XiMassAnalyticTest

/-!
# Route N reciprocal charge and Route T mass propagation are one timelike boost

The Route T mass kernel has real oscillatory phase

`Theta(x) = u * sqrt(x^(2 : ℕ) + a^(2 : ℕ)) + h * x`.

For `0 <= h < u`, it has one stationary point. Writing `q = sqrt(u^(2 : ℕ)-h^(2 : ℕ))`, the
stationary point is `-a*h/q`, its mass root is `a*u/q`, and its phase is the proper-time
value `a*q`. For `u <= h`, the derivative is strictly positive, so no stationary point exists.

The reciprocal Route N Sonin amplification `A` has canonical timelike coordinates

`u = (A + A^-1)/2`,  `h = (A - A^-1)/2`,  `q = 1`.

Under this embedding, Route N Burnol holonomy is the oriented boost `A-A^-1=2h`, Route N
Hermitian nonmetricity is the energy excess `A+A^-1-2=2u-2`, and their C25 identity is exactly
the Route T mass shell. The C27 affine Xi residue is multiplicity times the logarithmic rapidity
`log A/(2 log p)`, with the forced negative orientation on the strict-right divisor.

Thus the Fisher residue, Sonin escape, Burnol holonomy, Route N nonmetricity, and Route T
stationary mass ray are different coordinates of one conserved boost charge. This is an
unconditional structural bridge; it does not assume or prove RH.
-/

open Complex Real

namespace RHTower

noncomputable section

def xiMassTimelikeProperTime (u h : ℝ) : ℝ := Real.sqrt (u ^ 2 - h ^ 2)

def xiMassTimelikeAmplification (u h : ℝ) : ℝ :=
  (u + h) / xiMassTimelikeProperTime u h

def xiMassTimelikeOrientedBoost (u h : ℝ) : ℝ :=
  xiMassTimelikeAmplification u h - (xiMassTimelikeAmplification u h)⁻¹

def xiMassTimelikeNonmetricity (u h : ℝ) : ℝ :=
  xiMassTimelikeAmplification u h + (xiMassTimelikeAmplification u h)⁻¹ - 2

def xiMassTimelikePhase (a u h x : ℝ) : ℝ :=
  u * Real.sqrt (x ^ 2 + a ^ 2) + h * x

def xiMassTimelikeStationaryPoint (a u h : ℝ) : ℝ :=
  -a * h / xiMassTimelikeProperTime u h

def reciprocalMassTime (A : ℝ) : ℝ := (A + A⁻¹) / 2

def reciprocalMassFrequency (A : ℝ) : ℝ := (A - A⁻¹) / 2

theorem xiMassTimelikeProperTime_pos {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    0 < xiMassTimelikeProperTime u h := by
  rw [xiMassTimelikeProperTime]
  apply Real.sqrt_pos.mpr
  nlinarith

theorem sq_xiMassTimelikeProperTime {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikeProperTime u h ^ 2 = u ^ 2 - h ^ 2 := by
  rw [xiMassTimelikeProperTime, Real.sq_sqrt]
  nlinarith

theorem xiMassTimelikeAmplification_pos {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    0 < xiMassTimelikeAmplification u h := by
  rw [xiMassTimelikeAmplification]
  exact div_pos (by linarith) (xiMassTimelikeProperTime_pos hh0 hhu)

theorem xiMassTimelikeAmplification_inv {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    (xiMassTimelikeAmplification u h)⁻¹ =
      (u - h) / xiMassTimelikeProperTime u h := by
  let q := xiMassTimelikeProperTime u h
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  have hq2 : q ^ 2 = u ^ 2 - h ^ 2 := sq_xiMassTimelikeProperTime hh0 hhu
  have huh : u + h ≠ 0 := by linarith
  rw [xiMassTimelikeAmplification]
  change ((u + h) / q)⁻¹ = (u - h) / q
  rw [inv_div]
  field_simp [hq.ne', huh]
  nlinarith

theorem xiMassTimelikeOrientedBoost_eq {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikeOrientedBoost u h =
      2 * h / xiMassTimelikeProperTime u h := by
  rw [xiMassTimelikeOrientedBoost,
    xiMassTimelikeAmplification_inv hh0 hhu, xiMassTimelikeAmplification]
  ring

theorem xiMassTimelikeNonmetricity_eq {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikeNonmetricity u h =
      2 * u / xiMassTimelikeProperTime u h - 2 := by
  rw [xiMassTimelikeNonmetricity,
    xiMassTimelikeAmplification_inv hh0 hhu, xiMassTimelikeAmplification]
  ring

theorem sq_xiMassTimelikeOrientedBoost_eq_nonmetricity_massShell
    {u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikeOrientedBoost u h ^ 2 =
      xiMassTimelikeNonmetricity u h * (xiMassTimelikeNonmetricity u h + 4) := by
  let q := xiMassTimelikeProperTime u h
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  have hq2 : q ^ 2 = u ^ 2 - h ^ 2 := sq_xiMassTimelikeProperTime hh0 hhu
  rw [xiMassTimelikeOrientedBoost_eq hh0 hhu,
    xiMassTimelikeNonmetricity_eq hh0 hhu]
  change (2 * h / q) ^ 2 = (2 * u / q - 2) * (2 * u / q - 2 + 4)
  field_simp [hq.ne']
  nlinarith

theorem xiMassTimelikeStationaryPoint_massRoot
    {a u h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hhu : h < u) :
    Real.sqrt (xiMassTimelikeStationaryPoint a u h ^ 2 + a ^ 2) =
      a * u / xiMassTimelikeProperTime u h := by
  let q := xiMassTimelikeProperTime u h
  have hu : 0 < u := lt_of_le_of_lt hh0 hhu
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  have hq2 : q ^ 2 = u ^ 2 - h ^ 2 := sq_xiMassTimelikeProperTime hh0 hhu
  have hrhs0 : 0 ≤ a * u / q := by positivity
  have hinside :
      xiMassTimelikeStationaryPoint a u h ^ 2 + a ^ 2 = (a * u / q) ^ 2 := by
    rw [xiMassTimelikeStationaryPoint]
    change (-a * h / q) ^ 2 + a ^ 2 = (a * u / q) ^ 2
    field_simp [hq.ne']
    nlinarith
  have hinside0 : 0 ≤ xiMassTimelikeStationaryPoint a u h ^ 2 + a ^ 2 := by positivity
  have hsqrtSq := Real.sq_sqrt hinside0
  have hsqrt0 := Real.sqrt_nonneg
    (xiMassTimelikeStationaryPoint a u h ^ 2 + a ^ 2)
  nlinarith

theorem hasDerivAt_xiMassTimelikePhase
    {a u h x : ℝ} (ha : 0 < a) :
    HasDerivAt (xiMassTimelikePhase a u h)
      (u * x / Real.sqrt (x ^ 2 + a ^ 2) + h) x := by
  change HasDerivAt (fun y : ℝ => u * Real.sqrt (y ^ 2 + a ^ 2) + h * y)
    (u * x / Real.sqrt (x ^ 2 + a ^ 2) + h) x
  have hpos : 0 < x ^ 2 + a ^ 2 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (a ^ 2)
  have hsqrt := (Real.hasDerivAt_sqrt hpos.ne').comp x hinner
  have hscaled := hsqrt.const_mul u
  have hlinear : HasDerivAt (fun y : ℝ => h * y) h x := by
    simpa using (hasDerivAt_id x).const_mul h
  have hsum := hscaled.add hlinear
  have hden : Real.sqrt (x ^ 2 + a ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  refine hsum.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · field_simp [hden]
  · exact Filter.Eventually.of_forall fun _ => rfl

theorem xiMassTimelikePhase_deriv_stationary_eq_zero
    {a u h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hhu : h < u) :
    deriv (xiMassTimelikePhase a u h) (xiMassTimelikeStationaryPoint a u h) = 0 := by
  rw [(hasDerivAt_xiMassTimelikePhase (x := xiMassTimelikeStationaryPoint a u h) ha).deriv,
    xiMassTimelikeStationaryPoint_massRoot ha hh0 hhu]
  let q := xiMassTimelikeProperTime u h
  have hu : 0 < u := lt_of_le_of_lt hh0 hhu
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  rw [xiMassTimelikeStationaryPoint]
  change u * (-a * h / q) / (a * u / q) + h = 0
  field_simp [ha.ne', hu.ne', hq.ne']
  ring

theorem eq_xiMassTimelikeStationaryPoint_of_phase_deriv_eq_zero
    {a u h x : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hhu : h < u)
    (hzero : deriv (xiMassTimelikePhase a u h) x = 0) :
    x = xiMassTimelikeStationaryPoint a u h := by
  let q := xiMassTimelikeProperTime u h
  let s := Real.sqrt (x ^ 2 + a ^ 2)
  have hu : 0 < u := lt_of_le_of_lt hh0 hhu
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  have hq2 : q ^ 2 = u ^ 2 - h ^ 2 := sq_xiMassTimelikeProperTime hh0 hhu
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = x ^ 2 + a ^ 2 := by
    dsimp only [s]
    rw [Real.sq_sqrt]
    positivity
  rw [(hasDerivAt_xiMassTimelikePhase ha).deriv] at hzero
  have hlin : u * x + h * s = 0 := by
    change u * x / s + h = 0 at hzero
    field_simp [hs.ne'] at hzero
    simpa [mul_comm] using hzero
  have hxnonpos : x ≤ 0 := by
    have : u * x ≤ 0 := by nlinarith [mul_nonneg hh0 hs.le]
    exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using this) hu
  have hsquare : q ^ 2 * x ^ 2 = a ^ 2 * h ^ 2 := by
    have hprod : u * x = -(h * s) := by linarith
    have hprodSq := congrArg (fun y : ℝ => y ^ 2) hprod
    ring_nf at hprodSq
    nlinarith
  have htargetSquare : x ^ 2 = (-a * h / q) ^ 2 := by
    field_simp [hq.ne']
    nlinarith
  have htargetNonpos : -a * h / q ≤ 0 := by
    have hnum : -a * h ≤ 0 := by nlinarith [mul_nonneg ha.le hh0]
    exact div_nonpos_of_nonpos_of_nonneg hnum hq.le
  rw [xiMassTimelikeStationaryPoint]
  nlinarith

theorem xiMassTimelikePhase_deriv_pos_of_spacelike
    {a u h x : ℝ} (ha : 0 < a) (hu : 0 < u) (huh : u ≤ h) :
    0 < deriv (xiMassTimelikePhase a u h) x := by
  let s := Real.sqrt (x ^ 2 + a ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hxlt : |x| < s := by
    have hsq : x ^ 2 < x ^ 2 + a ^ 2 := by nlinarith [sq_pos_of_pos ha]
    have hroot := Real.sqrt_lt_sqrt (sq_nonneg x) hsq
    simpa only [Real.sqrt_sq_eq_abs] using hroot
  have hratio : -1 < x / s := by
    have hxlow : -s < x := by
      have hneg : -s < -|x| := neg_lt_neg hxlt
      exact hneg.trans_le (neg_abs_le x)
    exact (lt_div_iff₀ hs).2 (by simpa using hxlow)
  have hscaled : -u < u * (x / s) := by
    nlinarith [mul_lt_mul_of_pos_left hratio hu]
  rw [(hasDerivAt_xiMassTimelikePhase ha).deriv]
  have heq : u * x / Real.sqrt (x ^ 2 + a ^ 2) = u * (x / s) := by
    dsimp only [s]
    ring
  rw [heq]
  linarith

theorem reciprocalMassFrequency_nonneg {A : ℝ} (hA : 1 < A) :
    0 ≤ reciprocalMassFrequency A := by
  have hInv : A⁻¹ < 1 := inv_lt_one_of_one_lt₀ hA
  rw [reciprocalMassFrequency]
  linarith

theorem reciprocalMassFrequency_lt_time {A : ℝ} (hA : 1 < A) :
    reciprocalMassFrequency A < reciprocalMassTime A := by
  have hInv0 : 0 < A⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hA)
  rw [reciprocalMassFrequency, reciprocalMassTime]
  linarith

theorem reciprocalMass_time_sq_sub_frequency_sq {A : ℝ} (hA : 1 < A) :
    reciprocalMassTime A ^ 2 - reciprocalMassFrequency A ^ 2 = 1 := by
  have hA0 : A ≠ 0 := ne_of_gt (lt_trans zero_lt_one hA)
  rw [reciprocalMassTime, reciprocalMassFrequency]
  field_simp [hA0]
  ring

theorem xiMassTimelikeProperTime_reciprocalMass {A : ℝ} (hA : 1 < A) :
    xiMassTimelikeProperTime (reciprocalMassTime A) (reciprocalMassFrequency A) = 1 := by
  rw [xiMassTimelikeProperTime, reciprocalMass_time_sq_sub_frequency_sq hA,
    Real.sqrt_one]

theorem xiMassTimelikeAmplification_reciprocalMass {A : ℝ} (hA : 1 < A) :
    xiMassTimelikeAmplification (reciprocalMassTime A) (reciprocalMassFrequency A) = A := by
  rw [xiMassTimelikeAmplification, xiMassTimelikeProperTime_reciprocalMass hA,
    div_one, reciprocalMassTime, reciprocalMassFrequency]
  ring

theorem xiMassTimelikeOrientedBoost_reciprocalMass {A : ℝ} (hA : 1 < A) :
    xiMassTimelikeOrientedBoost (reciprocalMassTime A) (reciprocalMassFrequency A) =
      A - A⁻¹ := by
  rw [xiMassTimelikeOrientedBoost,
    xiMassTimelikeAmplification_reciprocalMass hA]

theorem xiMassTimelikeNonmetricity_reciprocalMass {A : ℝ} (hA : 1 < A) :
    xiMassTimelikeNonmetricity (reciprocalMassTime A) (reciprocalMassFrequency A) =
      A + A⁻¹ - 2 := by
  rw [xiMassTimelikeNonmetricity,
    xiMassTimelikeAmplification_reciprocalMass hA]

theorem routeNGammaSewnSoninEscapeAmplification_gt_one
    {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    1 < routeNGammaSewnSoninEscapeAmplification t p := by
  rw [routeNGammaSewnSoninEscapeAmplification_eq_rpow, abs_of_pos ht]
  exact Real.one_lt_rpow (by exact_mod_cast p.2.one_lt) (by linarith)

theorem routeNNonmetricity_eq_xiMassTimelikeNonmetricity
    {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    routeNGammaSewnSoninHermitianNonmetricity t p =
      xiMassTimelikeNonmetricity
        (reciprocalMassTime (routeNGammaSewnSoninEscapeAmplification t p))
        (reciprocalMassFrequency (routeNGammaSewnSoninEscapeAmplification t p)) := by
  let A := routeNGammaSewnSoninEscapeAmplification t p
  have hA : 1 < A := routeNGammaSewnSoninEscapeAmplification_gt_one ht p
  rw [routeNGammaSewnSoninHermitianNonmetricity_eq_escape_add_inv_sub_two]
  change A + A⁻¹ - 2 = _
  rw [xiMassTimelikeNonmetricity_reciprocalMass hA]

theorem re_xiAffineResidue_eq_neg_multiplicity_mul_routeNRapidity
    {rho : ℂ} {k : ℕ} (hhalf : 1 / 2 < rho.re) (p : Nat.Primes) :
    (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))).re =
      -((k + 1 : ℕ) : ℝ) *
        (Real.log
          (routeNGammaSewnSoninEscapeAmplification (rho.re - 1 / 2) p) /
            (2 * Real.log (p : ℝ))) := by
  have ht : 0 < rho.re - 1 / 2 := by linarith
  rw [log_routeNGammaSewnSoninEscapeAmplification_div,
    abs_of_pos ht]
  norm_num [mul_re]
  ring

theorem burnolHolonomy_eq_xiMassTimelikeOrientedBoost
    {w : ℂ} {a : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) (hz : riemannZeta w = 0) :
    burnolCoPoissonNormalizedHolonomy (r := (p : ℝ)) hlo hhi ha
        (by exact_mod_cast p.2.one_lt) =
      xiMassTimelikeOrientedBoost
        (reciprocalMassTime
          (routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p))
        (reciprocalMassFrequency
          (routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p)) := by
  have ht : 0 < w.re - 1 / 2 := by linarith
  let A := routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p
  have hA : 1 < A := routeNGammaSewnSoninEscapeAmplification_gt_one ht p
  rw [burnolCoPoissonNormalizedHolonomy_eq_routeNSoninEscape_sub_inv
      hlo hhi ha ha1 p hz]
  change A - A⁻¹ = _
  rw [xiMassTimelikeOrientedBoost_reciprocalMass hA]

theorem xiMassStationaryPoint_eq_neg_half_burnolHolonomy
    {w : ℂ} {a aperture : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (haperture : 0 < aperture) (haperture1 : aperture < 1)
    (p : Nat.Primes) (hz : riemannZeta w = 0) :
    xiMassTimelikeStationaryPoint a
        (reciprocalMassTime
          (routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p))
        (reciprocalMassFrequency
          (routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p)) =
      -(a / 2) *
        burnolCoPoissonNormalizedHolonomy (r := (p : ℝ)) hlo hhi haperture
          (by exact_mod_cast p.2.one_lt) := by
  have ht : 0 < w.re - 1 / 2 := by linarith
  let A := routeNGammaSewnSoninEscapeAmplification (w.re - 1 / 2) p
  have hA : 1 < A := routeNGammaSewnSoninEscapeAmplification_gt_one ht p
  rw [xiMassTimelikeStationaryPoint,
    xiMassTimelikeProperTime_reciprocalMass hA, div_one,
    reciprocalMassFrequency,
    burnolCoPoissonNormalizedHolonomy_eq_routeNSoninEscape_sub_inv
      hlo hhi haperture haperture1 p hz]
  change -a * ((A - A⁻¹) / 2) = -(a / 2) * (A - A⁻¹)
  ring

theorem xiMassTimelikePhase_stationary_eq_properTime
    {a u h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikePhase a u h (xiMassTimelikeStationaryPoint a u h) =
      a * xiMassTimelikeProperTime u h := by
  rw [xiMassTimelikePhase, xiMassTimelikeStationaryPoint_massRoot ha hh0 hhu,
    xiMassTimelikeStationaryPoint]
  let q := xiMassTimelikeProperTime u h
  have hq : 0 < q := xiMassTimelikeProperTime_pos hh0 hhu
  have hq2 : q ^ 2 = u ^ 2 - h ^ 2 := sq_xiMassTimelikeProperTime hh0 hhu
  change u * (a * u / q) + h * (-a * h / q) = a * q
  field_simp [hq.ne']
  nlinarith

theorem xiMassTimelikeStationaryPoint_eq_orientedBoost
    {a u h : ℝ} (hh0 : 0 ≤ h) (hhu : h < u) :
    xiMassTimelikeStationaryPoint a u h =
      -(a / 2) * xiMassTimelikeOrientedBoost u h := by
  rw [xiMassTimelikeStationaryPoint, xiMassTimelikeOrientedBoost_eq hh0 hhu]
  ring

theorem xiMassTimelikeStationaryMassRoot_eq_nonmetricity
    {a u h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hhu : h < u) :
    Real.sqrt (xiMassTimelikeStationaryPoint a u h ^ 2 + a ^ 2) =
      (a / 2) * (xiMassTimelikeNonmetricity u h + 2) := by
  rw [xiMassTimelikeStationaryPoint_massRoot ha hh0 hhu,
    xiMassTimelikeNonmetricity_eq hh0 hhu]
  ring

theorem xiMassTimelikePhase_stationary_reciprocalMass_eq
    {A a : ℝ} (hA : 1 < A) (ha : 0 < a) :
    xiMassTimelikePhase a (reciprocalMassTime A) (reciprocalMassFrequency A)
        (xiMassTimelikeStationaryPoint a
          (reciprocalMassTime A) (reciprocalMassFrequency A)) = a := by
  rw [xiMassTimelikePhase_stationary_eq_properTime ha
      (reciprocalMassFrequency_nonneg hA)
      (reciprocalMassFrequency_lt_time hA),
    xiMassTimelikeProperTime_reciprocalMass hA, mul_one]

structure RouteNMassXiTimelikeBoostCertificate : Prop where
  massShell :
    ∀ {u h : ℝ}, 0 ≤ h → h < u →
      xiMassTimelikeOrientedBoost u h ^ 2 =
        xiMassTimelikeNonmetricity u h * (xiMassTimelikeNonmetricity u h + 4)
  timelikeStationary :
    ∀ {a u h : ℝ}, 0 < a → 0 ≤ h → h < u →
      deriv (xiMassTimelikePhase a u h) (xiMassTimelikeStationaryPoint a u h) = 0
  timelikeStationaryUnique :
    ∀ {a u h x : ℝ}, 0 < a → 0 ≤ h → h < u →
      deriv (xiMassTimelikePhase a u h) x = 0 →
        x = xiMassTimelikeStationaryPoint a u h
  spacelikeNoStationary :
    ∀ {a u h x : ℝ}, 0 < a → 0 < u → u ≤ h →
      0 < deriv (xiMassTimelikePhase a u h) x
  reciprocalPhase :
    ∀ {A a : ℝ}, 1 < A → 0 < a →
      xiMassTimelikePhase a (reciprocalMassTime A) (reciprocalMassFrequency A)
          (xiMassTimelikeStationaryPoint a
            (reciprocalMassTime A) (reciprocalMassFrequency A)) = a
  affineResidueRapidity :
    ∀ {rho : ℂ} {k : ℕ}, 1 / 2 < rho.re → ∀ p : Nat.Primes,
      (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))).re =
        -((k + 1 : ℕ) : ℝ) *
          (Real.log
            (routeNGammaSewnSoninEscapeAmplification (rho.re - 1 / 2) p) /
              (2 * Real.log (p : ℝ)))
  routeNNonmetricity :
    ∀ {t : ℝ}, 0 < t → ∀ p : Nat.Primes,
      routeNGammaSewnSoninHermitianNonmetricity t p =
        xiMassTimelikeNonmetricity
          (reciprocalMassTime (routeNGammaSewnSoninEscapeAmplification t p))
          (reciprocalMassFrequency (routeNGammaSewnSoninEscapeAmplification t p))

theorem routeNMassXiTimelikeBoost_law : RouteNMassXiTimelikeBoostCertificate where
  massShell := sq_xiMassTimelikeOrientedBoost_eq_nonmetricity_massShell
  timelikeStationary := xiMassTimelikePhase_deriv_stationary_eq_zero
  timelikeStationaryUnique := eq_xiMassTimelikeStationaryPoint_of_phase_deriv_eq_zero
  spacelikeNoStationary := xiMassTimelikePhase_deriv_pos_of_spacelike
  reciprocalPhase := xiMassTimelikePhase_stationary_reciprocalMass_eq
  affineResidueRapidity := re_xiAffineResidue_eq_neg_multiplicity_mul_routeNRapidity
  routeNNonmetricity := routeNNonmetricity_eq_xiMassTimelikeNonmetricity

end

end RHTower
