import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnFisherHalfDensityBridge
import GaloisForLFunctions.RHTower.RouteRCriticalWallOrientedHarmonicQuantization

/-!
# Route N / Route R critical-wall identification

At nonzero centered grade, the Gamma-sewn Hedenmalm marked doublet at its sharp damping horizon
and the signed Route R Gamma--Bockstein at its first-trace wall carry the same prime-harmonic
essential atom.  The marked doublet is the positive representative; the Bockstein supplies its
orientation.  Precisely, modulo summable prime sequences,

`RouteN_horizon(t) = -sign(t) * RouteR_wall(t)`.

This is a source-to-source identification, not an RH implication.  It shows that the Route N
Hilbert-admission horizon and Route R trace-ideal wall are two polarizations of one boundary
class, so they cannot be counted as independent zero selectors.
-/

open Complex

namespace RHTower

noncomputable section

/-- Positive Route N marked energy at the sharp damping horizon `u = |t|`. -/
def routeNGammaSewnCriticalHorizonEnergy (t : ℝ) (p : Nat.Primes) : ℝ :=
  hedenmalmMarkedPrimeEnergy
    (gammaSewnHedenmalmDampedMarkedCharacter |t| p ((t : ℂ) * I))

/-- At the horizon, one marked orientation is the prime-harmonic atom and the opposite
orientation is a summable radial tail. -/
theorem routeNGammaSewnCriticalHorizonEnergy_eq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnCriticalHorizonEnergy t p =
      (p.1 : ℝ)⁻¹ + (p.1 : ℝ) ^ (-1 - 2 * |t|) := by
  rw [routeNGammaSewnCriticalHorizonEnergy,
    gammaSewnHedenmalmDampedMarkedCharacter_energy_eq_rpow,
    ← Real.rpow_neg_one]
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul, add_zero]
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    congr 1 <;> ring_nf
  · rw [abs_of_nonpos ht, add_comm]
    congr 1 <;> ring_nf

/-- Away from neutral grade, the radial remainder beyond the common prime-harmonic atom is
summable. -/
theorem summable_routeNGammaSewnCriticalHorizonEnergy_sub_primeHarmonic
    {t : ℝ} (ht : t ≠ 0) :
    Summable (fun p : Nat.Primes =>
      routeNGammaSewnCriticalHorizonEnergy t p - (p.1 : ℝ)⁻¹) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have htail : Summable (fun p : Nat.Primes =>
      (p.1 : ℝ) ^ (-1 - 2 * |t|)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine htail.congr fun p => ?_
  rw [routeNGammaSewnCriticalHorizonEnergy_eq]
  ring

/-- Enumerated complex representative of the positive Route N critical-horizon energy. -/
def routeNGammaSewnCriticalHorizonTraceSequence (t : ℝ) : RouteRTraceSequence :=
  fun n =>
    (routeNGammaSewnCriticalHorizonEnergy t (nthPrimeEquiv n) : ℂ)

@[simp]
theorem routeNGammaSewnCriticalHorizonTraceSequence_apply
    (t : ℝ) (n : ℕ) :
    routeNGammaSewnCriticalHorizonTraceSequence t n =
      (routeNGammaSewnCriticalHorizonEnergy t (nthPrimeEquiv n) : ℂ) :=
  rfl

/-- The Route N horizon sequence represents the positive prime-harmonic class. -/
theorem summable_routeNGammaSewnCriticalHorizonTraceSequence_sub_harmonic
    {t : ℝ} (ht : t ≠ 0) :
    Summable
      (routeNGammaSewnCriticalHorizonTraceSequence t -
        routeRPrimeHarmonicTraceSequence) := by
  have hreal := nthPrimeEquiv.summable_iff.mpr
    (summable_routeNGammaSewnCriticalHorizonEnergy_sub_primeHarmonic ht)
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  refine hcomplex.congr fun n => ?_
  rw [Pi.sub_apply, routeNGammaSewnCriticalHorizonTraceSequence_apply,
    routeRPrimeHarmonicTraceSequence]
  change
    ((routeNGammaSewnCriticalHorizonEnergy t (nthPrimeEquiv n) -
      (((nthPrimeEquiv n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = _
  push_cast
  ring

/-- Positive grade: Route N energy is the negative of the oriented Route R wall modulo `ell¹`. -/
theorem summable_routeNGammaSewnCriticalHorizonTraceSequence_add_routeR_of_pos
    {t : ℝ} (ht : 0 < t) :
    Summable
      (routeNGammaSewnCriticalHorizonTraceSequence t +
        routeRPrimeGammaCriticalWallSequence t) := by
  have hsum :=
    (summable_routeNGammaSewnCriticalHorizonTraceSequence_sub_harmonic ht.ne').add
      (summable_routeRPrimeGammaCriticalWallSequence_add_harmonic_of_pos ht)
  refine hsum.congr fun n => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Negative grade: Route N energy equals the oriented Route R wall modulo `ell¹`. -/
theorem summable_routeNGammaSewnCriticalHorizonTraceSequence_sub_routeR_of_neg
    {t : ℝ} (ht : t < 0) :
    Summable
      (routeNGammaSewnCriticalHorizonTraceSequence t -
        routeRPrimeGammaCriticalWallSequence t) := by
  have hsum :=
    (summable_routeNGammaSewnCriticalHorizonTraceSequence_sub_harmonic ht.ne).sub
      (summable_routeRPrimeGammaCriticalWallSequence_sub_harmonic_of_neg ht)
  refine hsum.congr fun n => ?_
  simp only [Pi.sub_apply]
  ring

end

end RHTower
