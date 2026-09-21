import GaloisForLFunctions.RHTower.ArithmeticMixedRateStableQuotient
import GaloisForLFunctions.RHTower.MeixnerRootPrimeLaplaceValueFrame
import GaloisForLFunctions.RHTower.PrimeLaplaceEvenFactorialSourceTransport

/-!
# No bounded columnwise forward raw-jet bridge to shrinking Meixner root domains

The even-factorial source transport sends every raw prime-jet column to `p⁻ᵃ` times itself at
forward time `a`. To recover the Gamma--Meixner root half-density at time `θ` by a diagonal
prime-wise bridge, the exact compensating gain is `sqrt(w_θ(p)) pᵃ`.

This file proves that this gain is unbounded over the primes whenever `θ < 2a`. It then upgrades
the scalar statement to arbitrary bounded operators: no such operator can recover every marked
forward prime column into any unit-norm output channel with the required Meixner amplitude. The
result is independent of a Xi-zero hypothesis: it isolates the source-normalization obstacle
before any divisor is inserted.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Prime-diagonal gain which turns the forward raw-jet multiplier `p⁻ᵃ` into the
Gamma--Meixner root half-density `sqrt(w_θ(p))`. -/
def meixnerForwardRawJetBridgeGain (theta a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * ((p : ℝ) ^ a)

/-- The bridge gain exactly cancels the raw-jet forward multiplier. -/
theorem meixnerForwardRawJetBridgeGain_mul_forwardMultiplier
    (theta a : ℝ) (p : Nat.Primes) :
    meixnerForwardRawJetBridgeGain theta a p * ((p : ℝ) ^ (-a)) =
      Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [meixnerForwardRawJetBridgeGain]
  calc
    Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * (p : ℝ) ^ a * (p : ℝ) ^ (-a) =
        Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * ((p : ℝ) ^ a * (p : ℝ) ^ (-a)) := by
      ring
    _ = Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * (p : ℝ) ^ (a + -a) := by
      rw [← Real.rpow_add hp]
    _ = Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) := by norm_num

/-- The gain has the sharp elementary lower exponent forced by the Meixner half-density. -/
theorem rpow_le_meixnerForwardRawJetBridgeGain
    {theta a : ℝ} (htheta : 0 ≤ theta) (p : Nat.Primes) :
    ((p : ℝ) ^ (a - theta / 2)) ≤ meixnerForwardRawJetBridgeGain theta a p := by
  have hweight := (sqrt_meixnerPrimeWeight_bounds htheta p.2.one_lt.le).1
  have hpow : 0 ≤ ((p : ℝ) ^ a) := Real.rpow_nonneg (by positivity) _
  rw [meixnerForwardRawJetBridgeGain]
  calc
    ((p : ℝ) ^ (a - theta / 2)) = ((p : ℝ) ^ (-theta / 2)) * ((p : ℝ) ^ a) := by
      rw [← Real.rpow_add (by exact_mod_cast p.2.pos : 0 < (p : ℝ))]
      congr 1
      ring
    _ ≤ Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * ((p : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_right hweight hpow

/-- At every root time below twice the forward translation time, the required diagonal bridge
exceeds any proposed finite bound on some prime. -/
theorem exists_prime_meixnerForwardRawJetBridgeGain_gt
    {theta a : ℝ} (htheta : 0 ≤ theta) (hgap : theta < 2 * a) (B : ℝ) :
    ∃ p : Nat.Primes, B < meixnerForwardRawJetBridgeGain theta a p := by
  have hexp : 0 < a - theta / 2 := by linarith
  have htend : Tendsto (fun p : Nat.Primes => ((p : ℝ) ^ (a - theta / 2)))
      primeAtTop atTop := by
    exact (tendsto_rpow_atTop hexp).comp
      (tendsto_natCast_atTop_atTop.comp tendsto_primeAtTop)
  obtain ⟨p, hp⟩ := (htend.eventually_gt_atTop B).exists
  exact ⟨p, hp.trans_le (rpow_le_meixnerForwardRawJetBridgeGain htheta p)⟩

/-- No bounded prime-diagonal bridge can undo a forward raw-jet transport at a root time
`θ < 2a`. -/
theorem not_exists_uniform_meixnerForwardRawJetBridgeGain_bound
    {theta a : ℝ} (htheta : 0 ≤ theta) (hgap : theta < 2 * a) :
    ¬ ∃ B : ℝ, ∀ p : Nat.Primes, meixnerForwardRawJetBridgeGain theta a p ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨p, hp⟩ := exists_prime_meixnerForwardRawJetBridgeGain_gt htheta hgap B
  exact (not_lt_of_ge (hB p)) hp

/-- In particular, critical half-translation `p⁻¹ᐟ²` has no bounded diagonal recovery into
any Gamma--Meixner root carrier of time strictly below one. -/
theorem not_exists_uniform_meixnerHalfTranslationBridgeGain_bound
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_lt : theta < 1) :
    ¬ ∃ B : ℝ, ∀ p : Nat.Primes,
      meixnerForwardRawJetBridgeGain theta (1 / 2) p ≤ B := by
  apply not_exists_uniform_meixnerForwardRawJetBridgeGain_bound htheta
  linarith

/-- The normalized prime vector in the unweighted `ℓ²` realization of the Meixner carrier. -/
def meixnerForwardRawJetPrimeBasis (p : Nat.Primes) : MeixnerPrimeHilbert :=
  lp.single 2 p (1 : ℂ)

theorem norm_meixnerForwardRawJetPrimeBasis (p : Nat.Primes) :
    ‖meixnerForwardRawJetPrimeBasis p‖ = 1 := by
  simp [meixnerForwardRawJetPrimeBasis, lp.norm_single]

/-- Any bounded operator which recovers each marked forward prime column into a unit-norm output
channel must have norm at least the forced Meixner bridge gain. The output channels need not be
diagonal, orthogonal, or distinct. -/
theorem meixnerForwardRawJetBridgeGain_le_opNorm_of_columnwise_recovery
    {theta a : ℝ} (T : MeixnerPrimeHilbert →L[ℂ] MeixnerPrimeHilbert)
    (u : Nat.Primes → MeixnerPrimeHilbert) (hu : ∀ p, ‖u p‖ = 1)
    (hT : ∀ p : Nat.Primes,
      T ((((p : ℝ) ^ (-a) : ℝ) : ℂ) • meixnerForwardRawJetPrimeBasis p) =
        (Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ) • u p)
    (p : Nat.Primes) :
    meixnerForwardRawJetBridgeGain theta a p ≤ ‖T‖ := by
  have hbound := T.le_opNorm
    ((((p : ℝ) ^ (-a) : ℝ) : ℂ) • meixnerForwardRawJetPrimeBasis p)
  have hsingle : ‖meixnerForwardRawJetPrimeBasis p‖ = 1 :=
    norm_meixnerForwardRawJetPrimeBasis p
  have hsqrt : 0 ≤ Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) := Real.sqrt_nonneg _
  have hpow : 0 ≤ ((p : ℝ) ^ (-a)) := Real.rpow_nonneg (by positivity) _
  rw [hT p] at hbound
  have htarget : ‖(Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ)‖ =
      Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt]
  have hsource : ‖(((p : ℝ) ^ (-a) : ℝ) : ℂ)‖ = (p : ℝ) ^ (-a) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpow]
  rw [norm_smul, norm_smul, hu p, hsingle, htarget, hsource] at hbound
  simp only [mul_one] at hbound
  rw [meixnerForwardRawJetBridgeGain]
  calc
    Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) * (p : ℝ) ^ a ≤
        (‖T‖ * (p : ℝ) ^ (-a)) * (p : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg (by positivity) _)
    _ = ‖T‖ := by
      have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
      rw [show ‖T‖ * (p : ℝ) ^ (-a) * (p : ℝ) ^ a =
          ‖T‖ * ((p : ℝ) ^ (-a) * (p : ℝ) ^ a) by ring,
        ← Real.rpow_add hp]
      norm_num

/-- At a root time `θ < 2a`, no bounded operator can recover every marked forward prime column
into any family of unit-norm output channels at the required Meixner amplitudes. -/
theorem not_exists_bounded_columnwise_meixnerForwardRawJetBridge
    {theta a : ℝ} (htheta : 0 ≤ theta) (hgap : theta < 2 * a) :
    ¬ ∃ (T : MeixnerPrimeHilbert →L[ℂ] MeixnerPrimeHilbert)
      (u : Nat.Primes → MeixnerPrimeHilbert),
        (∀ p, ‖u p‖ = 1) ∧
          ∀ p : Nat.Primes,
            T ((((p : ℝ) ^ (-a) : ℝ) : ℂ) • meixnerForwardRawJetPrimeBasis p) =
              (Real.sqrt (meixnerPrimeWeight theta (p : ℕ)) : ℂ) • u p := by
  rintro ⟨T, u, hu, hT⟩
  obtain ⟨p, hp⟩ := exists_prime_meixnerForwardRawJetBridgeGain_gt htheta hgap ‖T‖
  exact (not_lt_of_ge
    (meixnerForwardRawJetBridgeGain_le_opNorm_of_columnwise_recovery T u hu hT p)) hp

/-- Along every positive null sequence of root times, any fixed positive forward raw-jet time
encounters a level at which no bounded diagonal recovery bridge exists. -/
theorem exists_nullTime_no_uniform_meixnerForwardRawJetBridgeGain_bound
    {theta : ℕ → ℝ} (htheta_pos : ∀ n, 0 < theta n)
    (htheta_zero : Tendsto theta atTop (nhds 0)) {a : ℝ} (ha : 0 < a) :
    ∃ n : ℕ, ¬ ∃ B : ℝ, ∀ p : Nat.Primes,
      meixnerForwardRawJetBridgeGain (theta n) a p ≤ B := by
  obtain ⟨n, hn⟩ :=
    (htheta_zero.eventually (eventually_lt_nhds (show 0 < 2 * a by linarith))).exists
  refine ⟨n, not_exists_uniform_meixnerForwardRawJetBridgeGain_bound
    (htheta_pos n).le hn⟩

/-- Along every positive null sequence, a bounded columnwise recovery of all marked prime
channels fails at some root time, even when each channel is allowed an arbitrary unit output. -/
theorem exists_nullTime_no_bounded_columnwise_meixnerForwardRawJetBridge
    {theta : ℕ → ℝ} (htheta_pos : ∀ n, 0 < theta n)
    (htheta_zero : Tendsto theta atTop (nhds 0)) {a : ℝ} (ha : 0 < a) :
    ∃ n : ℕ, ¬ ∃ (T : MeixnerPrimeHilbert →L[ℂ] MeixnerPrimeHilbert)
      (u : Nat.Primes → MeixnerPrimeHilbert),
        (∀ p, ‖u p‖ = 1) ∧
          ∀ p : Nat.Primes,
            T ((((p : ℝ) ^ (-a) : ℝ) : ℂ) • meixnerForwardRawJetPrimeBasis p) =
              (Real.sqrt (meixnerPrimeWeight (theta n) (p : ℕ)) : ℂ) • u p := by
  obtain ⟨n, hn⟩ :=
    (htheta_zero.eventually (eventually_lt_nhds (show 0 < 2 * a by linarith))).exists
  exact ⟨n, not_exists_bounded_columnwise_meixnerForwardRawJetBridge
    (htheta_pos n).le hn⟩

end

end RHTower
