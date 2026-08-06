import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos

/-!
# Oriented harmonic quantization at the Route R first trace wall

The signed reflected Gamma Bockstein is critically damped at its moving first
trace wall `epsilon = |t|`.  At that wall every positive grade represents the
negative prime-harmonic class, every negative grade represents the positive
prime-harmonic class, and neutral grade represents zero.  Thus the continuum
of off-centre grades collapses to one nonzero rank port with an orientation.
-/

namespace RHTower

noncomputable section

/-- Signed prime coefficient of the Gamma Bockstein at its moving first trace wall. -/
def primeGammaCofinalBocksteinCriticalWallCoefficient
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-|t|) *
    (primeActivationOccupancyFisherTwist (-t) p -
      primeActivationOccupancyFisherTwist t p)

/-- The critically damped magnitude is the Fisher density times one reflected character
defect. -/
theorem primeGammaCofinalBocksteinCriticalWallMagnitude_eq
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinDampedMass |t| t p =
      primeActivationOccupancyFisherDensity p *
        (1 - (p : ℝ) ^ (-2 * |t|)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [primeGammaCofinalBocksteinDampedMass,
    primeGammaCofinalBocksteinMagnitude_factor,
    primeActivationOccupancyFisherTwist]
  calc
    (p : ℝ) ^ (-|t|) *
        ((p : ℝ) ^ |t| * primeActivationOccupancyFisherDensity p *
          (1 - (p : ℝ) ^ (-2 * |t|))) =
      ((p : ℝ) ^ (-|t|) * (p : ℝ) ^ |t|) *
        primeActivationOccupancyFisherDensity p *
          (1 - (p : ℝ) ^ (-2 * |t|)) := by ring
    _ = primeActivationOccupancyFisherDensity p *
          (1 - (p : ℝ) ^ (-2 * |t|)) := by
      rw [← Real.rpow_add hp0]
      simp

/-- Positive grade gives the negative orientation of the critically damped magnitude. -/
theorem primeGammaCofinalBocksteinCriticalWallCoefficient_eq_neg_magnitude_of_pos
    {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCriticalWallCoefficient t p =
      -primeGammaCofinalBocksteinDampedMass |t| t p := by
  rw [primeGammaCofinalBocksteinCriticalWallCoefficient,
    primeGammaCofinalBocksteinDampedMass,
    primeGammaCofinalBocksteinMagnitude_eq, abs_of_pos ht]
  ring

/-- Negative grade gives the positive orientation of the critically damped magnitude. -/
theorem primeGammaCofinalBocksteinCriticalWallCoefficient_eq_magnitude_of_neg
    {t : ℝ} (ht : t < 0) (p : Nat.Primes) :
    primeGammaCofinalBocksteinCriticalWallCoefficient t p =
      primeGammaCofinalBocksteinDampedMass |t| t p := by
  rw [primeGammaCofinalBocksteinCriticalWallCoefficient,
    primeGammaCofinalBocksteinDampedMass,
    primeGammaCofinalBocksteinMagnitude_eq, abs_of_neg ht]
  simp only [neg_neg]

/-- Fisher density differs summably from the prime-harmonic density. -/
theorem summable_primeHarmonic_sub_activationFisherDensity :
    Summable (fun p : Nat.Primes =>
      (p : ℝ)⁻¹ - primeActivationOccupancyFisherDensity p) := by
  have hsquare : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  refine Summable.of_nonneg_of_le
    (fun p => by simpa [one_div] using
      (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).1)
    (fun p => ?_) (hsquare.mul_left 3)
  calc
    (p : ℝ)⁻¹ - primeActivationOccupancyFisherDensity p ≤
        3 / (p : ℝ) ^ 2 :=
      by simpa [one_div] using
        (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).2
    _ = 3 * ((p : ℝ)⁻¹) ^ 2 := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      field_simp

/-- Away from neutral grade, the reflected correction at the first trace wall is summable. -/
theorem summable_activationFisherDensity_mul_criticalWallCorrection
    {t : ℝ} (ht : t ≠ 0) :
    Summable (fun p : Nat.Primes =>
      primeActivationOccupancyFisherDensity p *
        (p : ℝ) ^ (-2 * |t|)) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have hmodel : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-1 - 2 * |t|)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (by
      rw [primeActivationOccupancyFisherDensity_eq]
      positivity) (Real.rpow_nonneg (by positivity) _))
    (fun p => ?_) hmodel
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hFle : primeActivationOccupancyFisherDensity p ≤ (p : ℝ)⁻¹ := by
    apply sub_nonneg.mp
    simpa [one_div] using
      (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).1
  calc
    primeActivationOccupancyFisherDensity p * (p : ℝ) ^ (-2 * |t|) ≤
        (p : ℝ)⁻¹ * (p : ℝ) ^ (-2 * |t|) :=
      mul_le_mul_of_nonneg_right hFle (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-1 - 2 * |t|) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]
      congr 1
      ring

/-- The positive critically damped magnitude is the prime-harmonic density modulo `ell¹`. -/
theorem summable_primeHarmonic_sub_criticalWallMagnitude
    {t : ℝ} (ht : t ≠ 0) :
    Summable (fun p : Nat.Primes =>
      (p : ℝ)⁻¹ - primeGammaCofinalBocksteinDampedMass |t| t p) := by
  have hsum := summable_primeHarmonic_sub_activationFisherDensity.add
    (summable_activationFisherDensity_mul_criticalWallCorrection ht)
  refine hsum.congr fun p => ?_
  rw [primeGammaCofinalBocksteinCriticalWallMagnitude_eq]
  ring

/-- Positive grades equal the negative prime-harmonic orientation modulo `ell¹`. -/
theorem summable_criticalWallCoefficient_add_primeHarmonic_of_pos
    {t : ℝ} (ht : 0 < t) :
    Summable (fun p : Nat.Primes =>
      primeGammaCofinalBocksteinCriticalWallCoefficient t p + (p : ℝ)⁻¹) := by
  refine (summable_primeHarmonic_sub_criticalWallMagnitude ht.ne').congr fun p => ?_
  rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_neg_magnitude_of_pos ht]
  ring

/-- Negative grades equal the positive prime-harmonic orientation modulo `ell¹`. -/
theorem summable_criticalWallCoefficient_sub_primeHarmonic_of_neg
    {t : ℝ} (ht : t < 0) :
    Summable (fun p : Nat.Primes =>
      primeGammaCofinalBocksteinCriticalWallCoefficient t p - (p : ℝ)⁻¹) := by
  refine (summable_primeHarmonic_sub_criticalWallMagnitude ht.ne).neg.congr fun p => ?_
  rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_magnitude_of_neg ht]
  ring

/-- Enumerated complex prime-harmonic representative of the universal first-wall class. -/
def routeRPrimeHarmonicTraceSequence : RouteRTraceSequence :=
  fun n => (((nthPrimeEquiv n : ℕ) : ℝ)⁻¹ : ℂ)

/-- Signed enumerated Gamma Bockstein at its moving first trace wall. -/
def routeRPrimeGammaCriticalWallSequence (t : ℝ) : RouteRTraceSequence :=
  routeRPrimeGammaDampedBocksteinSequence |t| t

theorem routeRPrimeGammaCriticalWallSequence_apply
    (t : ℝ) (n : ℕ) :
    routeRPrimeGammaCriticalWallSequence t n =
      (primeGammaCofinalBocksteinCriticalWallCoefficient t (nthPrimeEquiv n) : ℂ) := by
  rw [routeRPrimeGammaCriticalWallSequence,
    routeRPrimeGammaDampedBocksteinSequence,
    primeGammaCofinalBocksteinCriticalWallCoefficient]
  simp only [primeActivationOccupancyFisherComplexTwist]
  push_cast
  ring

/-- Positive orientation differs from the negative harmonic sequence by a summable sequence. -/
theorem summable_routeRPrimeGammaCriticalWallSequence_add_harmonic_of_pos
    {t : ℝ} (ht : 0 < t) :
    Summable (routeRPrimeGammaCriticalWallSequence t + routeRPrimeHarmonicTraceSequence) := by
  have hreal := nthPrimeEquiv.summable_iff.mpr
    (summable_criticalWallCoefficient_add_primeHarmonic_of_pos ht)
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  refine hcomplex.congr fun n => ?_
  rw [Pi.add_apply, routeRPrimeGammaCriticalWallSequence_apply,
    routeRPrimeHarmonicTraceSequence]
  change ((primeGammaCofinalBocksteinCriticalWallCoefficient t (nthPrimeEquiv n) +
      (((nthPrimeEquiv n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = _
  push_cast
  ring

/-- Negative orientation differs from the positive harmonic sequence by a summable sequence. -/
theorem summable_routeRPrimeGammaCriticalWallSequence_sub_harmonic_of_neg
    {t : ℝ} (ht : t < 0) :
    Summable (routeRPrimeGammaCriticalWallSequence t - routeRPrimeHarmonicTraceSequence) := by
  have hreal := nthPrimeEquiv.summable_iff.mpr
    (summable_criticalWallCoefficient_sub_primeHarmonic_of_neg ht)
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  refine hcomplex.congr fun n => ?_
  rw [Pi.sub_apply, routeRPrimeGammaCriticalWallSequence_apply,
    routeRPrimeHarmonicTraceSequence]
  change ((primeGammaCofinalBocksteinCriticalWallCoefficient t (nthPrimeEquiv n) -
      (((nthPrimeEquiv n : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) = _
  push_cast
  ring

/-- The universal prime-harmonic wall representative is not summable. -/
theorem not_summable_routeRPrimeHarmonicTraceSequence :
    ¬ Summable routeRPrimeHarmonicTraceSequence := by
  intro hsum
  have hnorm : Summable (fun n =>
      (((nthPrimeEquiv n : ℕ) : ℝ)⁻¹)) := by
    simpa [routeRPrimeHarmonicTraceSequence] using
      (summable_norm_iff.mpr hsum)
  have hprime : Summable (fun p : Nat.Primes => (p : ℝ)⁻¹) :=
    nthPrimeEquiv.summable_iff.mp hnorm
  have hrpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-1 : ℝ)) :=
    hprime.congr fun p => (Real.rpow_neg_one _).symm
  have hexp := Nat.Primes.summable_rpow.mp hrpow
  linarith

/-- Critical-wall Gamma sequence is summable only at neutral grade. -/
theorem summable_routeRPrimeGammaCriticalWallSequence_iff (t : ℝ) :
    Summable (routeRPrimeGammaCriticalWallSequence t) ↔ t = 0 := by
  rw [routeRPrimeGammaCriticalWallSequence,
    summable_routeRPrimeGammaDampedBocksteinSequence_iff]
  simp

/-- Diagonal tail--Roos class respects subtraction of global coefficient sequences. -/
theorem routeRDiagonalTailRoosClass_sub
    (a b : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass (a - b) =
      routeRDiagonalTailRoosClass a - routeRDiagonalTailRoosClass b := by
  have hm : routeRDiagonalMismatchInIdeal (a - b) =
      routeRDiagonalMismatchInIdeal a - routeRDiagonalMismatchInIdeal b := by
    funext n
    apply Subtype.ext
    funext k
    cases k <;> (simp [routeRDiagonalMismatchInIdeal, routeRDiagonalMismatch, routeRTail,
      Nat.add_comm, Nat.add_left_comm] <;> ring)
  simp only [routeRDiagonalTailRoosClass, hm, Submodule.Quotient.mk_sub]

/-- Diagonal tail--Roos class respects negation. -/
theorem routeRDiagonalTailRoosClass_neg (a : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass (-a) = -routeRDiagonalTailRoosClass a := by
  have h := routeRDiagonalTailRoosClass_sub (0 : RouteRTraceSequence) a
  have hza : (0 : RouteRTraceSequence) - a = -a := by
    funext n
    simp
  rw [hza] at h
  have hzero : routeRDiagonalTailRoosClass (0 : RouteRTraceSequence) = 0 :=
    (routeRDiagonalTailRoosClass_eq_zero_iff_summable _).mpr summable_zero
  calc
    routeRDiagonalTailRoosClass (-a) =
        routeRDiagonalTailRoosClass (0 : RouteRTraceSequence) -
          routeRDiagonalTailRoosClass a := h
    _ = -routeRDiagonalTailRoosClass a := by rw [hzero, zero_sub]

/-- Two diagonal tail classes agree exactly when their coefficient difference is summable. -/
theorem routeRDiagonalTailRoosClass_eq_iff_summable_sub
    (a b : RouteRTraceSequence) :
    routeRDiagonalTailRoosClass a = routeRDiagonalTailRoosClass b ↔
      Summable (a - b) := by
  constructor
  · intro hab
    apply (routeRDiagonalTailRoosClass_eq_zero_iff_summable (a - b)).mp
    rw [routeRDiagonalTailRoosClass_sub, hab, sub_self]
  · intro hsum
    have hzero :=
      (routeRDiagonalTailRoosClass_eq_zero_iff_summable (a - b)).mpr hsum
    rw [routeRDiagonalTailRoosClass_sub] at hzero
    exact sub_eq_zero.mp hzero

/-- Positive grades carry exactly the negative universal harmonic tail class. -/
theorem routeRPrimeGammaCriticalWallTailRoosClass_eq_neg_harmonic_of_pos
    {t : ℝ} (ht : 0 < t) :
    routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) =
      -routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence := by
  calc
    routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) =
        routeRDiagonalTailRoosClass (-routeRPrimeHarmonicTraceSequence) := by
      apply (routeRDiagonalTailRoosClass_eq_iff_summable_sub
        (routeRPrimeGammaCriticalWallSequence t)
        (-routeRPrimeHarmonicTraceSequence)).mpr
      simpa [sub_neg_eq_add] using
        summable_routeRPrimeGammaCriticalWallSequence_add_harmonic_of_pos ht
    _ = -routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence :=
      routeRDiagonalTailRoosClass_neg routeRPrimeHarmonicTraceSequence

/-- Negative grades carry exactly the positive universal harmonic tail class. -/
theorem routeRPrimeGammaCriticalWallTailRoosClass_eq_harmonic_of_neg
    {t : ℝ} (ht : t < 0) :
    routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) =
      routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence := by
  apply (routeRDiagonalTailRoosClass_eq_iff_summable_sub
    (routeRPrimeGammaCriticalWallSequence t)
    routeRPrimeHarmonicTraceSequence).mpr
  exact summable_routeRPrimeGammaCriticalWallSequence_sub_harmonic_of_neg ht

/-- Neutral grade carries the zero tail class. -/
theorem routeRPrimeGammaCriticalWallTailRoosClass_eq_zero :
    routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence 0) = 0 := by
  apply (routeRDiagonalTailRoosClass_eq_zero_iff_summable _).mpr
  exact (summable_routeRPrimeGammaCriticalWallSequence_iff 0).mpr rfl

/-- The universal harmonic rank port is genuinely nonzero. -/
theorem routeRPrimeHarmonicTailRoosClass_ne_zero :
    routeRDiagonalTailRoosClass routeRPrimeHarmonicTraceSequence ≠ 0 := by
  intro hzero
  exact not_summable_routeRPrimeHarmonicTraceSequence
    ((routeRDiagonalTailRoosClass_eq_zero_iff_summable _).mp hzero)

end

end RHTower
