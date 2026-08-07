import GaloisForLFunctions.RHTower.RouteEStaticAbsoluteKernelRecurrence
import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

/-!
# Moving terminal-kernel antiscale resonance

An aperture-dependent kernel supported in a terminal logarithmic prime band is explicitly small
at the physical frequency `pi / log Y`.  The result is a complete pair-indexed `tsum` estimate and
does not assume positivity, Hermitian symmetry, diagonal structure, or aperture independence.
-/

open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Terminal logarithmic prime band below aperture `Y`, with relative log-width `eta`. -/
def routeETerminalLogBand (Y eta : ℝ) (p : Nat.Primes) : Prop :=
  0 ≤ Real.log Y - Real.log (((p : Nat.Primes) : ℕ) : ℝ) ∧
    Real.log Y - Real.log (((p : Nat.Primes) : ℕ) : ℝ) ≤ eta * Real.log Y

/-- At physical frequency `pi / log Y`, every prime in the terminal log-band has antiscale seam
at most `pi * eta`. -/
theorem norm_routeEAntiscaleSeam_pi_div_log_le
    {Y eta : ℝ} (hY : 1 < Y)
    {p : Nat.Primes} (hp : routeETerminalLogBand Y eta p) :
    ‖routeEAntiscaleSeam p (Real.pi / Real.log Y)‖ ≤ Real.pi * eta := by
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hfactor : 0 ≤ Real.pi / Real.log Y := div_nonneg Real.pi_pos.le hlogY.le
  have hdiff0 := hp.1
  have hdiffle := hp.2
  have hchord := norm_exp_phase_sub_le
    ((Real.pi / Real.log Y) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) Real.pi
  have hseamEq :
      ‖routeEAntiscaleSeam p (Real.pi / Real.log Y)‖ =
        ‖Complex.exp (((((Real.pi / Real.log Y) *
            Real.log (((p : Nat.Primes) : ℕ) : ℝ) : ℝ)) : ℂ) * Complex.I) -
          Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)‖ := by
    rw [routeEAntiscaleSeam, charFn, Complex.exp_pi_mul_I]
    congr 2
    ring
  rw [hseamEq]
  refine hchord.trans ?_
  have hphase :
      (Real.pi / Real.log Y) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) - Real.pi =
        -(Real.pi / Real.log Y) *
          (Real.log Y - Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [hphase, abs_mul, abs_neg, abs_of_nonneg hfactor, abs_of_nonneg hdiff0]
  calc
    (Real.pi / Real.log Y) *
        (Real.log Y - Real.log (((p : Nat.Primes) : ℕ) : ℝ))
        ≤ (Real.pi / Real.log Y) * (eta * Real.log Y) :=
          mul_le_mul_of_nonneg_left hdiffle hfactor
    _ = Real.pi * eta := by field_simp

/-- Pairwise moving terminal-band majorant at the explicit antiscale frequency. -/
theorem norm_routeEStaticAbsoluteKernelTerm_pi_div_log_le
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    (K : Nat.Primes × Nat.Primes → ℂ)
    (hsupport : ∀ q, K q ≠ 0 →
      routeETerminalLogBand Y eta q.1 ∧ routeETerminalLogBand Y eta q.2)
    (q : Nat.Primes × Nat.Primes) :
    ‖routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) ^ 2 * ‖K q‖ := by
  by_cases hq : K q = 0
  · simp [routeEStaticAbsoluteKernelTerm, hq]
  · obtain ⟨hq₁, hq₂⟩ := hsupport q hq
    have hs₁ := norm_routeEAntiscaleSeam_pi_div_log_le hY hq₁
    have hs₂ := norm_routeEAntiscaleSeam_pi_div_log_le hY hq₂
    rw [routeEStaticAbsoluteKernelTerm, norm_mul, norm_mul, RCLike.norm_conj]
    have hpiEta : 0 ≤ Real.pi * eta := mul_nonneg Real.pi_pos.le heta
    have hseamprod :
        ‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
            ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖ ≤
          (Real.pi * eta) * (Real.pi * eta) :=
      mul_le_mul hs₁ hs₂ (norm_nonneg _) hpiEta
    calc
      ‖K q‖ * ‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
          ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖ =
        ‖K q‖ *
          (‖routeEAntiscaleSeam q.1 (Real.pi / Real.log Y)‖ *
            ‖routeEAntiscaleSeam q.2 (Real.pi / Real.log Y)‖) := by ring
      _ ≤ ‖K q‖ * ((Real.pi * eta) * (Real.pi * eta)) :=
        mul_le_mul_of_nonneg_left hseamprod (norm_nonneg _)
      _ = (Real.pi * eta) ^ 2 * ‖K q‖ := by ring

/-- **Moving terminal-kernel resonance.**  Complete cross-prime form at the explicit physical
frequency is bounded by band-width squared times total entrywise kernel mass. -/
theorem norm_tsum_routeEStaticAbsoluteKernelTerm_pi_div_log_le
    {Y eta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    {K : Nat.Primes × Nat.Primes → ℂ}
    (hK : Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖))
    (hsupport : ∀ q, K q ≠ 0 →
      routeETerminalLogBand Y eta q.1 ∧ routeETerminalLogBand Y eta q.2) :
    ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ ≤
      (Real.pi * eta) ^ 2 * ∑' q : Nat.Primes × Nat.Primes, ‖K q‖ := by
  have hsummable :=
    summable_routeEStaticAbsoluteKernelTerm hK (Real.pi / Real.log Y)
  have hcoefficient : 0 ≤ (Real.pi * eta) ^ 2 := sq_nonneg _
  calc
    ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖
        ≤ ∑' q : Nat.Primes × Nat.Primes,
            ‖routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ :=
          norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' q : Nat.Primes × Nat.Primes,
            (Real.pi * eta) ^ 2 * ‖K q‖ := by
          refine Summable.tsum_le_tsum (fun q => ?_) hsummable.norm
            (hK.mul_left ((Real.pi * eta) ^ 2))
          exact norm_routeEStaticAbsoluteKernelTerm_pi_div_log_le
            hY heta K hsupport q
    _ = (Real.pi * eta) ^ 2 * ∑' q : Nat.Primes × Nat.Primes, ‖K q‖ :=
      tsum_mul_left

/-- Explicit smallness criterion at physical terminal resonance. -/
theorem norm_tsum_routeEStaticAbsoluteKernelTerm_pi_div_log_lt
    {Y eta delta : ℝ} (hY : 1 < Y) (heta : 0 ≤ eta)
    {K : Nat.Primes × Nat.Primes → ℂ}
    (hK : Summable (fun q : Nat.Primes × Nat.Primes => ‖K q‖))
    (hsupport : ∀ q, K q ≠ 0 →
      routeETerminalLogBand Y eta q.1 ∧ routeETerminalLogBand Y eta q.2)
    (hsmall : (Real.pi * eta) ^ 2 *
      ∑' q : Nat.Primes × Nat.Primes, ‖K q‖ < delta) :
    ‖∑' q : Nat.Primes × Nat.Primes,
        routeEStaticAbsoluteKernelTerm K q (Real.pi / Real.log Y)‖ < delta :=
  (norm_tsum_routeEStaticAbsoluteKernelTerm_pi_div_log_le
    hY heta hK hsupport).trans_lt hsmall

end

end RHTower.Sieve
