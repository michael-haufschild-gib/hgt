import GaloisForLFunctions.CountingHolography.Sections.SignedSplineSmallSections
import GaloisForLFunctions.CountingHolography.TheIntegerProbesAreNotIntegerValued
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtThePrimeDegrees

/-!
# An integer divisibility test at the prime pairs

For a sum of two positive spline atoms every local condition is an integral
divisibility condition. The lower bound for spline correlations at the prime
degrees lets one use one fixed quadratic allowance for the logarithmic radius,
with cofinal multiplicities separately at each prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography AbsoluteGeometryOfSpecZ
open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry RenormalizedIntersectionTheory
open BiScaleUncertainty.ChebyshevGauge

/-- Integral modulus of the nonnegative contact rows. -/
def contactModulus {N : ℕ} (a : Fin N → ℤ) : ℕ :=
  ∏ k ∈ Icc 2 (3*windowEnd N), contactBase k ^
    ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋₊

theorem generator_eq_contactModulus {N : ℕ} (a : Fin N → ℤ) (ha : ∀ i, 0 ≤ a i) :
    generator a = (contactModulus a : ℚ) := by
  have hf (u : ℝ) : 0 ≤ packet a u := by
    unfold packet splineSource
    exact sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast ha i) (cubicSpline_nonneg _)
  unfold generator contactGenerator contactModulus
  push_cast
  apply prod_congr rfl
  intro k _
  have he : 0 ≤ contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k := by
    unfold contactMultiplicity
    exact mul_nonneg (by positivity) (sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (hf _) (hf _)) (Nat.cast_nonneg _))
  rw [← Int.natCast_floor_eq_floor he, zpow_natCast]

/-- The two effective graphs have degrees one and p. -/
def primePair (p : ℕ) : Fin (p+1) → ℤ :=
  Pi.single (⟨p-1, by omega⟩ : Fin (p+1)) 1 + Pi.single 0 1

private theorem smul_primePair_nonneg (p m : ℕ) (i : Fin (p+1)) : 0 ≤ (m • primePair p) i := by
  simp only [primePair, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.single_apply]
  split_ifs <;> positivity

theorem integerProbe_primePair {p : ℕ} (hp : 0 < p) :
    integerProbe (p+1) (primePair p) =
      2 * (splineSeries 0).re + 2 * (splineSeries (Real.log p)).re := by
  have he : ((p-1 : ℕ) : ℝ) + 1 = p := by
    rw [Nat.cast_sub hp]; push_cast; ring
  rw [primePair, integerProbe_pair]
  simp only [atomGram_eq_splineSeries, Fin.val_zero, Nat.cast_zero, zero_add,
    Real.log_one, sub_self, sub_zero, he]
  ring

/-- RH is equivalent to one uniform archimedean allowance on the prime pairs.
The finite-place side is the positive integer generating the contact ideal. -/
theorem riemannHypothesis_iff_prime_modulus_bound :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ p : ℕ, p.Prime →
      ∃ᶠ m : ℕ in atTop, Real.log (contactModulus (m • primePair p)) ≤
        radius (m • primePair p) + C * (m : ℝ)^2 := by
  have he (p m : ℕ) : (generator (m • primePair p) : ℝ) = contactModulus (m • primePair p) := by
    exact_mod_cast generator_eq_contactModulus _ (smul_primePair_nonneg p m)
  constructor
  · intro h
    refine ⟨1, fun p _ => ?_⟩
    have hs := riemannHypothesis_iff_smallSections_with_slack.mp h (p+1) (primePair p) 1 one_pos
    apply (hs.mono fun m hm => ?_).frequently
    rw [← he]
    have hpos : 0 < (generator (m • primePair p) : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
    exact (exists_nonzero_smallSection hpos).mp hm
  · rintro ⟨C, h⟩
    apply SurfaceOfSpecZ.riemannHypothesis_iff_bddBelow_primeDegrees'.mpr
    refine ⟨C / 2 + (splineSeries 0).re, fun p hp => ?_⟩
    have hb : -C ≤ integerProbe (p+1) (primePair p) := by
      by_contra! hlt
      have hs := (tendsto_splineDegree (primePair p)).eventually_lt_const hlt
      obtain ⟨m, hm, hs', hm1⟩ := ((h p hp).and_eventually (hs.and (eventually_ge_atTop 1))).exists
      have hm2 : 0 < (m : ℝ)^2 := by positivity
      have hh := (div_lt_iff₀ hm2).mp hs'
      rw [he] at hh
      linarith only [hm, hh]
    rw [integerProbe_primePair hp.pos] at hb
    rw [orbitCorr_splineCycle_eq]
    linarith only [hb]

#print axioms riemannHypothesis_iff_prime_modulus_bound

end GaloisForLFunctions.CountingHolography.Sections
