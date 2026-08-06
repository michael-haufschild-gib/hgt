import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# The first trace wall as a scale detector

At one stage of a bounded unit profile the oriented first-wall average is not
merely convergent: its modulus is pinned from below by

`(1 - q ^ (-2|t|)) * (1 - 3 / q)`,

where `q` is any lower bound for the primes carrying the stage.  The first
factor is the reflected character defect evaluated at the shallowest available
prime and the second is the Fisher deficit of the harmonic weight.

Consequently a single stage carried by deep primes converts a strict modulus
bound into an explicit numerical bound on the grade, `|t| = O(1 / log q)`, and a
family of arbitrarily deep stages with one common threshold below the harmonic
quantum forces neutral grade.  No asymptotics in the stage index are needed.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The damped first-wall mass -/

/-- Damped mass at the moving first trace wall: the activation Fisher density
times the reflected character defect. -/
def routeRFirstWallMass (t : ℝ) (p : Nat.Primes) : ℝ :=
  primeActivationOccupancyFisherDensity p * (1 - ((p : ℕ) : ℝ) ^ (-2 * |t|))

theorem one_le_prime_real (p : Nat.Primes) : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.one_lt.le

theorem primeCharacterDefect_nonneg (t : ℝ) (p : Nat.Primes) :
    0 ≤ 1 - ((p : ℕ) : ℝ) ^ (-2 * |t|) := by
  have h := Real.rpow_le_one_of_one_le_of_nonpos (one_le_prime_real p)
    (by simp [abs_nonneg t] : -2 * |t| ≤ 0)
  linarith

theorem activationFisherDensity_nonneg (p : Nat.Primes) :
    0 ≤ primeActivationOccupancyFisherDensity p := by
  rw [primeActivationOccupancyFisherDensity_eq]
  positivity

theorem routeRFirstWallMass_nonneg (t : ℝ) (p : Nat.Primes) :
    0 ≤ routeRFirstWallMass t p :=
  mul_nonneg (activationFisherDensity_nonneg p) (primeCharacterDefect_nonneg t p)

theorem activationFisherDensity_le_harmonic (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p ≤ primeHarmonicWeight p := by
  have h := (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).1
  rw [primeHarmonicWeight]
  simpa [one_div] using sub_nonneg.mp h

theorem routeRFirstWallMass_le_harmonic (t : ℝ) (p : Nat.Primes) :
    routeRFirstWallMass t p ≤ primeHarmonicWeight p := by
  have hdefect : 1 - ((p : ℕ) : ℝ) ^ (-2 * |t|) ≤ 1 := by
    have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-2 * |t|) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  calc routeRFirstWallMass t p ≤ primeActivationOccupancyFisherDensity p * 1 :=
        mul_le_mul_of_nonneg_left hdefect (activationFisherDensity_nonneg p)
    _ = primeActivationOccupancyFisherDensity p := mul_one _
    _ ≤ primeHarmonicWeight p := activationFisherDensity_le_harmonic p

@[simp] theorem routeRFirstWallMass_zero (p : Nat.Primes) :
    routeRFirstWallMass 0 p = 0 := by
  simp [routeRFirstWallMass]

@[simp] theorem criticalWallCoefficient_zero (p : Nat.Primes) :
    primeGammaCofinalBocksteinCriticalWallCoefficient 0 p = 0 := by
  simp [primeGammaCofinalBocksteinCriticalWallCoefficient]

/-- The first-wall coefficient has modulus exactly the damped mass. -/
theorem abs_criticalWallCoefficient_eq (t : ℝ) (p : Nat.Primes) :
    |primeGammaCofinalBocksteinCriticalWallCoefficient t p| =
      routeRFirstWallMass t p := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_magnitude_of_neg ht,
      primeGammaCofinalBocksteinCriticalWallMagnitude_eq,
      abs_of_nonneg (by
        simpa [routeRFirstWallMass] using routeRFirstWallMass_nonneg t p)]
    rfl
  · subst ht
    simp
  · rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_neg_magnitude_of_pos ht,
      primeGammaCofinalBocksteinCriticalWallMagnitude_eq, abs_neg,
      abs_of_nonneg (by
        simpa [routeRFirstWallMass] using routeRFirstWallMass_nonneg t p)]
    rfl

/-! ## One stage of a unit profile -/

section Stage

variable {w : Nat.Primes → ℝ}

theorem summable_stageFirstWallMass
    (hstage : IsUnitStage primeHarmonicWeight w) (t : ℝ) :
    Summable fun p => w p * routeRFirstWallMass t p :=
  Summable.of_nonneg_of_le
    (fun p => mul_nonneg (hstage.nonneg p) (routeRFirstWallMass_nonneg t p))
    (fun p => mul_le_mul_of_nonneg_left (routeRFirstWallMass_le_harmonic t p)
      (hstage.nonneg p))
    hstage.hasSum_mass.summable

theorem summable_stageCriticalWallCoefficient
    (hstage : IsUnitStage primeHarmonicWeight w) (t : ℝ) :
    Summable fun p =>
      w p * primeGammaCofinalBocksteinCriticalWallCoefficient t p := by
  refine Summable.of_abs
    ((summable_stageFirstWallMass hstage t).congr fun p => ?_)
  rw [abs_mul, abs_of_nonneg (hstage.nonneg p), abs_criticalWallCoefficient_eq]

theorem tsum_stageFirstWallMass_nonneg
    (hstage : IsUnitStage primeHarmonicWeight w) (t : ℝ) :
    0 ≤ ∑' p, w p * routeRFirstWallMass t p :=
  tsum_nonneg fun p =>
    mul_nonneg (hstage.nonneg p) (routeRFirstWallMass_nonneg t p)

theorem abs_tsum_stageCriticalWallCoefficient
    (hstage : IsUnitStage primeHarmonicWeight w) (t : ℝ) :
    |∑' p, w p * primeGammaCofinalBocksteinCriticalWallCoefficient t p| =
      ∑' p, w p * routeRFirstWallMass t p := by
  have hnn := tsum_stageFirstWallMass_nonneg hstage t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have heq : ∀ p, w p *
        primeGammaCofinalBocksteinCriticalWallCoefficient t p =
          w p * routeRFirstWallMass t p := by
      intro p
      rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_magnitude_of_neg ht,
        primeGammaCofinalBocksteinCriticalWallMagnitude_eq]
      rfl
    rw [tsum_congr heq, abs_of_nonneg hnn]
  · subst ht
    simp
  · have heq : ∀ p, w p *
        primeGammaCofinalBocksteinCriticalWallCoefficient t p =
          -(w p * routeRFirstWallMass t p) := by
      intro p
      rw [primeGammaCofinalBocksteinCriticalWallCoefficient_eq_neg_magnitude_of_pos ht,
        primeGammaCofinalBocksteinCriticalWallMagnitude_eq]
      show w p * -(primeActivationOccupancyFisherDensity p *
        (1 - ((p : ℕ) : ℝ) ^ (-2 * |t|))) = _
      rw [routeRFirstWallMass]
      ring
    rw [tsum_congr heq, tsum_neg, abs_neg, abs_of_nonneg hnn]

/-- The modulus of a stage average of the first-wall field is the stage average
of the damped mass. -/
theorem norm_stageAverage_criticalWall_eq
    (hstage : IsUnitStage primeHarmonicWeight w) (t : ℝ) :
    ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ =
      ∑' p, w p * routeRFirstWallMass t p := by
  rw [show routeRPrimeGammaCriticalWallField t =
      fun p => ((primeGammaCofinalBocksteinCriticalWallCoefficient t p : ℝ) : ℂ)
      from rfl,
    norm_stageAverage_ofReal (summable_stageCriticalWallCoefficient hstage t),
    abs_tsum_stageCriticalWallCoefficient hstage t]

/-! ## The scale bound -/

/-- **Stage depth pins the oriented modulus from below.**  For a stage carried
by primes at least `q`, the modulus of the first-wall average is at least the
character defect at `q` times the Fisher deficit at `q`. -/
theorem le_norm_stageAverage_criticalWall
    (hstage : IsUnitStage primeHarmonicWeight w) {q : ℝ} (hq : 3 ≤ q)
    (hsupp : ∀ p : Nat.Primes, w p ≠ 0 → q ≤ ((p : ℕ) : ℝ)) (t : ℝ) :
    (1 - q ^ (-2 * |t|)) * (1 - 3 / q) ≤
      ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hdefectQ : 0 ≤ 1 - q ^ (-2 * |t|) := by
    have := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1 : ℝ) ≤ q)
      (by simp [abs_nonneg t] : -2 * |t| ≤ 0)
    linarith
  have hdeficitQ : 0 ≤ 1 - 3 / q := by
    rw [sub_nonneg, div_le_one hq0]
    linarith
  rw [norm_stageAverage_criticalWall_eq hstage]
  refine le_tsum_stageWeighted hstage.hasSum_mass
    (summable_stageFirstWallMass hstage t) fun p => ?_
  rcases eq_or_ne (w p) 0 with hw | hw
  · simp [hw]
  · have hwpos : 0 < w p := lt_of_le_of_ne (hstage.nonneg p) (Ne.symm hw)
    have hqp : q ≤ ((p : ℕ) : ℝ) := hsupp p hw
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    -- Fisher deficit at the shallowest available prime
    have hpne : ((p : ℕ) : ℝ) ≠ 0 := ne_of_gt hp0
    have hfisher : (1 - 3 / q) * ((p : ℕ) : ℝ)⁻¹ ≤
        primeActivationOccupancyFisherDensity p := by
      have hdiff :=
        (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).2
      have hmul := mul_le_mul_of_nonneg_left hdiff hp0.le
      have e1 : ((p : ℕ) : ℝ) *
          (1 / ((p : ℕ) : ℝ) - primeActivationOccupancyFisherDensity p) =
            1 - ((p : ℕ) : ℝ) * primeActivationOccupancyFisherDensity p := by
        field_simp
      have e2 : ((p : ℕ) : ℝ) * (3 / ((p : ℕ) : ℝ) ^ 2) = 3 / ((p : ℕ) : ℝ) := by
        field_simp
      rw [e1, e2] at hmul
      have h3q : 3 / ((p : ℕ) : ℝ) ≤ 3 / q :=
        div_le_div_of_nonneg_left (by norm_num) hq0 hqp
      have hPF : 1 - 3 / q ≤
          ((p : ℕ) : ℝ) * primeActivationOccupancyFisherDensity p := by linarith
      calc (1 - 3 / q) * ((p : ℕ) : ℝ)⁻¹ ≤
            (((p : ℕ) : ℝ) * primeActivationOccupancyFisherDensity p) *
              ((p : ℕ) : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hPF (by positivity)
        _ = primeActivationOccupancyFisherDensity p := by field_simp
    -- character defect grows with the prime
    have hdefect : 1 - q ^ (-2 * |t|) ≤ 1 - ((p : ℕ) : ℝ) ^ (-2 * |t|) := by
      have := Real.rpow_le_rpow_of_nonpos hq0 hqp
        (by simp [abs_nonneg t] : -2 * |t| ≤ 0)
      linarith
    have hcore : (1 - q ^ (-2 * |t|)) * (1 - 3 / q) * primeHarmonicWeight p ≤
        routeRFirstWallMass t p := by
      rw [primeHarmonicWeight, routeRFirstWallMass]
      calc (1 - q ^ (-2 * |t|)) * (1 - 3 / q) * ((p : ℕ) : ℝ)⁻¹
          = (1 - q ^ (-2 * |t|)) * ((1 - 3 / q) * ((p : ℕ) : ℝ)⁻¹) := by ring
        _ ≤ (1 - ((p : ℕ) : ℝ) ^ (-2 * |t|)) *
              primeActivationOccupancyFisherDensity p :=
            mul_le_mul hdefect hfisher
              (mul_nonneg hdeficitQ (by positivity)) (by linarith)
        _ = primeActivationOccupancyFisherDensity p *
              (1 - ((p : ℕ) : ℝ) ^ (-2 * |t|)) := by ring
    calc (1 - q ^ (-2 * |t|)) * (1 - 3 / q) * (w p * primeHarmonicWeight p)
        = w p * ((1 - q ^ (-2 * |t|)) * (1 - 3 / q) * primeHarmonicWeight p) := by
          ring
      _ ≤ w p * routeRFirstWallMass t p :=
          mul_le_mul_of_nonneg_left hcore hwpos.le

/-- **A depth ceiling pins the oriented modulus from above.**  For a stage
carried by primes at most `Q`, the modulus of the first-wall average is at most
the character defect at `Q`. -/
theorem norm_stageAverage_criticalWall_le
    (hstage : IsUnitStage primeHarmonicWeight w) {Q : ℝ}
    (hceil : ∀ p : Nat.Primes, w p ≠ 0 → ((p : ℕ) : ℝ) ≤ Q) (t : ℝ) :
    ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ≤
      1 - Q ^ (-2 * |t|) := by
  rw [norm_stageAverage_criticalWall_eq hstage]
  refine tsum_stageWeighted_le hstage.hasSum_mass
    (summable_stageFirstWallMass hstage t) fun p => ?_
  rcases eq_or_ne (w p) 0 with hw | hw
  · simp [hw]
  · have hwpos : 0 < w p := lt_of_le_of_ne (hstage.nonneg p) (Ne.symm hw)
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := one_le_prime_real p
    have hdefect : 1 - ((p : ℕ) : ℝ) ^ (-2 * |t|) ≤ 1 - Q ^ (-2 * |t|) := by
      have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < ((p : ℕ) : ℝ))
        (hceil p hw) (by simp [abs_nonneg t] : -2 * |t| ≤ 0)
      linarith
    have hcore : routeRFirstWallMass t p ≤
        (1 - Q ^ (-2 * |t|)) * primeHarmonicWeight p := by
      rw [routeRFirstWallMass]
      calc primeActivationOccupancyFisherDensity p *
            (1 - ((p : ℕ) : ℝ) ^ (-2 * |t|))
          ≤ primeHarmonicWeight p * (1 - Q ^ (-2 * |t|)) :=
            mul_le_mul (activationFisherDensity_le_harmonic p) hdefect
              (primeCharacterDefect_nonneg t p) (primeHarmonicWeight_pos p).le
        _ = (1 - Q ^ (-2 * |t|)) * primeHarmonicWeight p := by ring
    calc w p * routeRFirstWallMass t p ≤
          w p * ((1 - Q ^ (-2 * |t|)) * primeHarmonicWeight p) :=
          mul_le_mul_of_nonneg_left hcore hwpos.le
      _ = (1 - Q ^ (-2 * |t|)) * (w p * primeHarmonicWeight p) := by ring

/-- **Two-sided scale law.**  Between a floor `q` and a ceiling `Q` on the
carrying primes the first-wall modulus is trapped by the character defects at
those two depths.  A stage therefore resolves the grade only at scale
`1 / log Q`, and cannot be made small by any reweighting once `|t| log q` is
large. -/
theorem stageAverage_criticalWall_sandwich
    (hstage : IsUnitStage primeHarmonicWeight w) {q Q : ℝ} (hq : 3 ≤ q)
    (hfloor : ∀ p : Nat.Primes, w p ≠ 0 → q ≤ ((p : ℕ) : ℝ))
    (hceil : ∀ p : Nat.Primes, w p ≠ 0 → ((p : ℕ) : ℝ) ≤ Q) (t : ℝ) :
    (1 - q ^ (-2 * |t|)) * (1 - 3 / q) ≤
        ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ∧
      ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ≤
        1 - Q ^ (-2 * |t|) :=
  ⟨le_norm_stageAverage_criticalWall hstage hq hfloor t,
    norm_stageAverage_criticalWall_le hstage hceil t⟩

/-- **No bounded depth decides.**  A stage carried by primes below a ceiling is
satisfied, to any prescribed tolerance, by some nonzero grade.  Hence the
deep-stage criterion genuinely needs unbounded depth: no single stage, and no
finitely supported stage, can separate neutral grade. -/
theorem exists_ne_zero_norm_stageAverage_le
    (hstage : IsUnitStage primeHarmonicWeight w) {Q : ℝ} (hQ : 2 ≤ Q)
    (hceil : ∀ p : Nat.Primes, w p ≠ 0 → ((p : ℕ) : ℝ) ≤ Q) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, t ≠ 0 ∧
      ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ≤ r := by
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have ht0 : 0 < r / (2 * Real.log Q) := div_pos hr (by linarith)
  refine ⟨r / (2 * Real.log Q), ne_of_gt ht0, ?_⟩
  refine le_trans (norm_stageAverage_criticalWall_le hstage hceil _) ?_
  have hval : Real.log Q * (-2 * (r / (2 * Real.log Q))) = -r := by
    field_simp
  rw [abs_of_pos ht0, Real.rpow_def_of_pos hQ0, hval]
  linarith [Real.add_one_le_exp (-r)]

/-- A finitely supported stage has a depth ceiling. -/
theorem exists_depthCeiling_of_finite_support {w : Nat.Primes → ℝ}
    (hfin : (Function.support w).Finite) :
    ∃ Q : ℝ, 2 ≤ Q ∧ ∀ p : Nat.Primes, w p ≠ 0 → ((p : ℕ) : ℝ) ≤ Q := by
  obtain ⟨Q, hQ⟩ :=
    (hfin.image fun p : Nat.Primes => ((p : ℕ) : ℝ)).bddAbove
  refine ⟨max 2 Q, le_max_left _ _, fun p hp => ?_⟩
  exact le_trans (hQ ⟨p, hp, rfl⟩) (le_max_right _ _)

/-- **Finitely supported stages never decide.** -/
theorem exists_ne_zero_norm_stageAverage_le_of_finite_support
    (hstage : IsUnitStage primeHarmonicWeight w)
    (hfin : (Function.support w).Finite) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, t ≠ 0 ∧
      ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ≤ r := by
  obtain ⟨Q, hQ, hceil⟩ := exists_depthCeiling_of_finite_support hfin
  exact exists_ne_zero_norm_stageAverage_le hstage hQ hceil hr

/-- **One deep stage bounds the grade.**  A modulus bound below the Fisher
deficit at depth `q` forces `|t| = O(1 / log q)`, with an explicit constant. -/
theorem abs_le_of_norm_stageAverage_le
    (hstage : IsUnitStage primeHarmonicWeight w) {q : ℝ} (hq : 4 ≤ q)
    (hsupp : ∀ p : Nat.Primes, w p ≠ 0 → q ≤ ((p : ℕ) : ℝ)) {t r : ℝ}
    (hr : r < 1 - 3 / q)
    (hbound : ‖stageAverage w (routeRPrimeGammaCriticalWallField t)‖ ≤ r) :
    |t| ≤ Real.log ((1 - 3 / q) / (1 - 3 / q - r)) / (2 * Real.log q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  set A : ℝ := 1 - 3 / q with hA
  have hApos : 0 < A := by
    rw [hA, sub_pos, div_lt_one hq0]
    linarith
  have hgap : 0 < A - r := by linarith
  have hkey : (1 - q ^ (-2 * |t|)) * A ≤ r :=
    le_trans (le_norm_stageAverage_criticalWall hstage (by linarith) hsupp t) hbound
  have hx : (A - r) / A ≤ q ^ (-2 * |t|) := by
    rw [div_le_iff₀ hApos]
    nlinarith
  -- pass to logarithms
  have hexp : q ^ (-2 * |t|) = Real.exp (Real.log q * (-2 * |t|)) :=
    Real.rpow_def_of_pos hq0 _
  have hlog : Real.log ((A - r) / A) ≤ Real.log q * (-2 * |t|) := by
    have hpos : 0 < (A - r) / A := div_pos hgap hApos
    have := Real.log_le_log hpos (le_trans hx (le_of_eq hexp))
    rwa [Real.log_exp] at this
  have hneg : Real.log (A / (A - r)) = -Real.log ((A - r) / A) := by
    rw [← Real.log_inv, inv_div]
  rw [le_div_iff₀ (by positivity)]
  calc |t| * (2 * Real.log q) = -(Real.log q * (-2 * |t|)) := by ring
    _ ≤ -Real.log ((A - r) / A) := by linarith
    _ = Real.log (A / (A - r)) := hneg.symm

end Stage

/-! ## Arbitrarily deep stages force neutral grade -/

/-- **Deep-stage criterion.**  If arbitrarily deep stages of one bounded unit
profile keep the first-wall modulus below a single threshold under the harmonic
quantum, the grade vanishes.  The stage index is unconstrained: only the depth
of the carrying primes matters. -/
theorem eq_zero_of_deepStage_norm_profileAverage_le
    {mu : ℕ → Nat.Primes → ℝ}
    (hmu : IsCofinalUnitProfile primeHarmonicWeight mu) {t r : ℝ} (hr : r < 1)
    (hdeep : ∀ Q : ℕ, ∃ N : ℕ,
      (∀ p : Nat.Primes, mu N p ≠ 0 → (Q : ℝ) ≤ ((p : ℕ) : ℝ)) ∧
      ‖profileAverage mu N (routeRPrimeGammaCriticalWallField t)‖ ≤ r) :
    t = 0 := by
  -- a depth beyond which the Fisher deficit already exceeds the threshold
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_gt (max 4 (3 / (1 - r)))
  have hrlt : 0 < 1 - r := by linarith
  have hQ₀4 : (4 : ℝ) < (Q₀ : ℝ) := lt_of_le_of_lt (le_max_left _ _) hQ₀
  have hQ₀gap : 3 / (1 - r) < (Q₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hQ₀
  have hA₀ : r < 1 - 3 / (Q₀ : ℝ) := by
    have hQpos : (0 : ℝ) < (Q₀ : ℝ) := by linarith
    rw [lt_sub_iff_add_lt, ← sub_pos]
    have : 3 / (Q₀ : ℝ) < 1 - r := by
      rw [div_lt_iff₀ hQpos]
      rw [div_lt_iff₀ hrlt] at hQ₀gap
      linarith
    linarith
  have hgap₀ : 0 < 1 - 3 / (Q₀ : ℝ) - r := by linarith
  set C : ℝ := Real.log (1 / (1 - 3 / (Q₀ : ℝ) - r)) with hC
  -- every depth beyond `Q₀` bounds the grade by `C / (2 log Q)`
  have hbound : ∀ᶠ Q : ℕ in atTop, |t| ≤ C / (2 * Real.log (Q : ℝ)) := by
    filter_upwards [eventually_ge_atTop Q₀] with Q hQ
    have hQQ₀ : (Q₀ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hQ4 : (4 : ℝ) ≤ (Q : ℝ) := by linarith
    have hQpos : (0 : ℝ) < (Q : ℝ) := by linarith
    have hmono : 3 / (Q : ℝ) ≤ 3 / (Q₀ : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hQQ₀
    have hAQ : r < 1 - 3 / (Q : ℝ) := by linarith
    obtain ⟨N, hsupp, hle⟩ := hdeep Q
    have hstage := hmu.isUnitStage N
    have hexplicit := abs_le_of_norm_stageAverage_le hstage hQ4 hsupp hAQ
      (by rwa [← profileAverage_eq_stageAverage])
    refine le_trans hexplicit ?_
    have hgapQ : 0 < 1 - 3 / (Q : ℝ) - r := by linarith
    have h3Qnn : (0 : ℝ) ≤ 3 / (Q : ℝ) := by positivity
    have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
    have hnum : (1 - 3 / (Q : ℝ)) / (1 - 3 / (Q : ℝ) - r) ≤
        1 / (1 - 3 / (Q₀ : ℝ) - r) :=
      div_le_div₀ zero_le_one (by linarith) hgap₀ (by linarith)
    have hA1 : (0 : ℝ) < 1 - 3 / (Q : ℝ) := by
      rw [sub_pos, div_lt_one hQpos]; linarith
    have hlogle : Real.log ((1 - 3 / (Q : ℝ)) / (1 - 3 / (Q : ℝ) - r)) ≤ C :=
      Real.log_le_log (div_pos hA1 hgapQ) hnum
    exact div_le_div_of_nonneg_right hlogle (by linarith)
  -- the explicit bound tends to zero
  have hlogTop : Tendsto (fun Q : ℕ => 2 * Real.log (Q : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hzero : Tendsto (fun Q : ℕ => C / (2 * Real.log (Q : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  exact abs_nonpos_iff.mp (ge_of_tendsto hzero hbound)

/-- **The deep-stage criterion cannot be localized.**  There is a bounded
cofinal prime-harmonic profile all of whose stages are carried by finitely many
primes, and at each of its stages some nonzero grade evades any prescribed
tolerance.  Unbounded depth is thus intrinsic and not an artefact of the
statement. -/
theorem exists_isCofinalUnitProfile_no_single_stage_decides :
    ∃ mu : ℕ → Nat.Primes → ℝ, IsCofinalUnitProfile primeHarmonicWeight mu ∧
      ∀ (N : ℕ) (r : ℝ), 0 < r → ∃ t : ℝ, t ≠ 0 ∧
        ‖profileAverage mu N (routeRPrimeGammaCriticalWallField t)‖ ≤ r := by
  obtain ⟨mu, hmu, hfin⟩ :=
    exists_isCofinalUnitProfile_finiteSupport_primeHarmonic nthPrimeEquiv
  refine ⟨mu, hmu, fun N r hr => ?_⟩
  obtain ⟨t, ht, hle⟩ := exists_ne_zero_norm_stageAverage_le_of_finite_support
    (hmu.isUnitStage N) (hfin N) hr
  exact ⟨t, ht, by rwa [profileAverage_eq_stageAverage]⟩

end

end RHTower
