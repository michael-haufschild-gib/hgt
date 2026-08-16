import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentFiniteBoundaryReadout
import GaloisForLFunctions.RHTower.CCMUnitRieszHankelBoundaryPulse


/-!
# Literal outgoing coherent charge as an exact HG boundary trace

Prime coherent tail charge is the outgoing base-state coefficient of finite von-Mangoldt source.
Polar coefficient is retained as its actual continuum integral, not inserted after evaluation.
Their difference defines a literal completed outgoing profile.

This module proves the profile collapses to
`(R_1(log N)/2) exp(-u/2)`, is HG-admissible, and has exact all-aperture boundary trace

`boundaryRelativeTrace = (R_1(log N)^2/4)(1-exp(-u))`.

Consequently domination by canonical incoming pole packet `4(1-exp(-u))` at every positive
aperture is equivalent to `R_1(log N)^2 <= 16`.  This supplies canonical source-defined HG carrier
and an exact arithmetic four-unit target; missing science is proof of domination (and its
source-to-divisor endpoint), not profile construction.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitRieszCoherentPrimeOutgoingCharge (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 N,
    (ArithmeticFunction.vonMangoldt k / Real.sqrt N) *
      (1 - Real.exp (-(Real.log N - Real.log k) / 2))

def unitRieszCoherentPolarOutgoingCharge (N : ℕ) : ℝ :=
  Real.sqrt N * ∫ p in Ioi (0 : ℝ),
    Real.exp (-p) * (1 - Real.exp (-p / 2))

def unitRieszCoherentCompletedOutgoingCharge (N : ℕ) : ℝ :=
  unitRieszCoherentPrimeOutgoingCharge N - unitRieszCoherentPolarOutgoingCharge N

theorem unitRieszCoherentPrimeOutgoingCharge_eq_energy_half
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentPrimeOutgoingCharge N =
      unitRieszCoherentPrimeEnergy N N / 2 := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  simpa only [unitRieszCoherentPrimeOutgoingCharge] using
    unitRieszCoherentPrimeKernelTailCharge_eq (X := (N : ℝ)) (K := N) hNpos le_rfl

theorem unitRieszCoherentPolarOutgoingCharge_eq (N : ℕ) :
    unitRieszCoherentPolarOutgoingCharge N = Real.sqrt N / 3 := by
  have h1 : IntegrableOn (fun p : ℝ => Real.exp (-(1 * p))) (Ioi 0) :=
    by simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi 0 (b := (1 : ℝ)) one_pos)
  have h32 : IntegrableOn (fun p : ℝ => Real.exp (-((3 / 2) * p))) (Ioi 0) :=
    by simpa only [neg_mul] using
      (exp_neg_integrableOn_Ioi 0 (b := (3 / 2 : ℝ)) (by norm_num))
  rw [unitRieszCoherentPolarOutgoingCharge]
  rw [show (fun p : ℝ => Real.exp (-p) * (1 - Real.exp (-p / 2))) =
      fun p => Real.exp (-(1 * p)) - Real.exp (-((3 / 2) * p)) by
    funext p
    simp only [one_mul]
    rw [mul_sub, mul_one]
    rw [show Real.exp (-p) * Real.exp (-p / 2) = Real.exp (-((3 / 2) * p)) by
      rw [← Real.exp_add]
      congr 1
      ring]]
  rw [integral_sub h1 h32,
    integral_Ioi_rexp_neg_mul_shift one_pos 0,
    integral_Ioi_rexp_neg_mul_shift (by norm_num : (0 : ℝ) < 3 / 2) 0]
  norm_num
  ring_nf

theorem unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentCompletedOutgoingCharge N =
      criticalMellinChebyshevResolventSource (Real.log N) / 2 := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hp := unitRieszCoherentPrimeOutgoingCharge_eq_energy_half hN
  have hpolar := unitRieszCoherentPolarEnergy_eq hNpos
  have hres := criticalMellinChebyshevResolventSource_log_nat_eq_coherentPrime_sub_polar hN1
  rw [unitRieszCoherentCompletedOutgoingCharge, hp,
    unitRieszCoherentPolarOutgoingCharge_eq]
  rw [hres, hpolar]
  ring_nf

def unitRieszCoherentCompletedOutgoingProfile (N : ℕ) (u : ℝ) : ℂ :=
  ((unitRieszCoherentCompletedOutgoingCharge N * Real.exp (-u / 2) : ℝ) : ℂ)

theorem unitRieszCoherentCompletedOutgoingProfile_eq_resolvent
    {N : ℕ} (hN : 2 ≤ N) (u : ℝ) :
    unitRieszCoherentCompletedOutgoingProfile N u =
      ((criticalMellinChebyshevResolventSource (Real.log N) / 2 *
        Real.exp (-u / 2) : ℝ) : ℂ) := by
  rw [unitRieszCoherentCompletedOutgoingProfile,
    unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN]

theorem continuous_unitRieszCoherentCompletedOutgoingProfile (N : ℕ) :
    Continuous (unitRieszCoherentCompletedOutgoingProfile N) := by
  unfold unitRieszCoherentCompletedOutgoingProfile
  fun_prop

theorem leakDensity_unitRieszCoherentCompletedOutgoingProfile (N : ℕ) (u : ℝ) :
    leakDensity (unitRieszCoherentCompletedOutgoingProfile N) u =
      unitRieszCoherentCompletedOutgoingCharge N ^ 2 * Real.exp (-u) := by
  rw [leakDensity, unitRieszCoherentCompletedOutgoingProfile, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, mul_pow]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring_nf

theorem leakProfile_unitRieszCoherentCompletedOutgoingProfile (N : ℕ) :
    LeakProfile (unitRieszCoherentCompletedOutgoingProfile N) := by
  constructor
  · exact (continuous_unitRieszCoherentCompletedOutgoingProfile N).measurable.aestronglyMeasurable
  · have hbase : IntegrableOn (fun u : ℝ => (1 + u) * Real.exp (-1 * u)) (Ioi 0) :=
      integrableOn_one_add_mul_exp_neg (b := 1) one_pos
    have hmul := hbase.const_mul (unitRieszCoherentCompletedOutgoingCharge N ^ 2)
    refine hmul.congr ?_
    filter_upwards with u
    rw [leakDensity_unitRieszCoherentCompletedOutgoingProfile]
    rw [show -1 * u = -u by ring]
    ring_nf

theorem integral_leakDensity_unitRieszCoherentCompletedOutgoingProfile (N : ℕ) :
    (∫ u in Ioi (0 : ℝ),
        leakDensity (unitRieszCoherentCompletedOutgoingProfile N) u) =
      unitRieszCoherentCompletedOutgoingCharge N ^ 2 := by
  rw [show (fun u : ℝ => leakDensity (unitRieszCoherentCompletedOutgoingProfile N) u) =
      fun u => unitRieszCoherentCompletedOutgoingCharge N ^ 2 * Real.exp (-(1 * u)) by
    funext u
    rw [leakDensity_unitRieszCoherentCompletedOutgoingProfile]
    congr 2
    ring_nf]
  rw [integral_const_mul, integral_Ioi_rexp_neg_mul_shift one_pos 0]
  norm_num

theorem hankelGapProfile_unitRieszCoherentCompletedOutgoingProfile
    (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    hankelGapProfile (unitRieszCoherentCompletedOutgoingProfile N) u =
      unitRieszCoherentCompletedOutgoingCharge N ^ 2 * Real.exp (-u) := by
  rw [hankelGapProfile_of_leakDensity_exp
    (c := unitRieszCoherentCompletedOutgoingCharge N ^ 2) (a := 1)
    (fun t => by
      rw [leakDensity_unitRieszCoherentCompletedOutgoingProfile]
      congr 2
      ring_nf) one_pos hu]
  ring_nf

theorem boundaryRelativeTrace_unitRieszCoherentCompletedOutgoingProfile
    (N : ℕ) {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u =
      unitRieszCoherentCompletedOutgoingCharge N ^ 2 * (1 - Real.exp (-u)) := by
  rw [boundaryRelativeTrace_eq_gap_sub
    (leakProfile_unitRieszCoherentCompletedOutgoingProfile N) hu,
    hankelGapProfile_unitRieszCoherentCompletedOutgoingProfile N (le_refl 0),
    hankelGapProfile_unitRieszCoherentCompletedOutgoingProfile N hu.le,
    neg_zero, Real.exp_zero]
  ring_nf

/-- Direct CCM-HG source weld: initial boundary relative-trace slope of literal outgoing coherent
source is exactly square of half completed unit-Riesz resolvent. -/
theorem tendsto_boundaryRelativeTrace_div_unitRieszCoherentCompletedOutgoingProfile
    {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun u : ℝ =>
        boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u / u)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((criticalMellinChebyshevResolventSource (Real.log N) / 2) ^ 2)) := by
  have hlim := tendsto_boundaryRelativeTrace_div
    (leakProfile_unitRieszCoherentCompletedOutgoingProfile N)
  rw [integral_leakDensity_unitRieszCoherentCompletedOutgoingProfile,
    unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN] at hlim
  exact hlim

theorem unitRieszCoherentCompletedOutgoingProfile_density_le_four_iff
    {N : ℕ} (hN : 2 ≤ N) :
    (∀ L : ℝ,
        Tendsto (fun u : ℝ =>
            boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u / u)
          (𝓝[>] (0 : ℝ)) (𝓝 L) → L ≤ 4) ↔
      criticalMellinChebyshevResolventSource (Real.log N) ^ 2 ≤ 16 := by
  have hlim :=
    tendsto_boundaryRelativeTrace_div_unitRieszCoherentCompletedOutgoingProfile hN
  constructor
  · intro hall
    have hle := hall _ hlim
    nlinarith
  · intro hres L hL
    have hEq : L = (criticalMellinChebyshevResolventSource (Real.log N) / 2) ^ 2 :=
      tendsto_nhds_unique hL hlim
    rw [hEq]
    nlinarith

/-- All-aperture HG pole domination for literal outgoing source is exactly uniform four-unit bound
on completed aperture resolvent; no infinitesimal limiting argument is needed. -/
theorem unitRieszCoherentCompletedOutgoingProfile_le_pole_iff
    {N : ℕ} (hN : 2 ≤ N) :
    (∀ u : ℝ, 0 < u →
      boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u ≤
        boundaryRelativeTrace polePacketProfile u) ↔
      criticalMellinChebyshevResolventSource (Real.log N) ^ 2 ≤ 16 := by
  constructor
  · intro hall
    have h := hall 1 one_pos
    rw [boundaryRelativeTrace_unitRieszCoherentCompletedOutgoingProfile N one_pos,
      unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN,
      boundaryRelativeTrace_polePacket one_pos] at h
    have hfactor : 0 < 1 - Real.exp (-(1 : ℝ)) := by
      have : Real.exp (-(1 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      linarith
    have hsquare : (criticalMellinChebyshevResolventSource (Real.log N) / 2) ^ 2 ≤ 4 :=
      le_of_mul_le_mul_right h hfactor
    nlinarith
  · intro hres u hu
    rw [boundaryRelativeTrace_unitRieszCoherentCompletedOutgoingProfile N hu,
      unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN,
      boundaryRelativeTrace_polePacket hu]
    have hsquare : (criticalMellinChebyshevResolventSource (Real.log N) / 2) ^ 2 ≤ 4 := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hsquare (by
      have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith)

end GaloisForLFunctions.RHTower

