import GaloisForLFunctions.RHTower.ThetaCuspHawkingMinimumPhaseEndpoint

/-!
# Finite same-frequency sesquilinear currents are blind to theta-Hawking all-pass phase

The remaining phase-sensitive HB proposal cannot be supplied by increasing the differential order
of a physical local Hermitian optical current.  At one real frequency, every finite family of
translation-invariant linear differential channels has the form

`channel_j(x) = symbol_j(x) * F(x)`.

Even allowing an arbitrary frequency-dependent complex coefficient matrix, its most general
same-frequency sesquilinear current factors exactly through the intensity of `F`:

`Q_x(F) = ‖F‖² Q_x(1)`.

Hence every common unit all-pass dressing is invisible.  Applied to the literal theta-Hawking Born
form factor, the canonical causal all-pass factor leaves every current in this class unchanged at
every physical frequency, although its Wigner--Smith clock is strictly positive.

This kills the complete finite same-frequency sesquilinear producer class, including every finite
local differential Hermitian/positive specialization.  The sharp survivor must compare distinct
frequencies, use a time-bilocal or external phase reference, differentiate in frequency, or use a
complex-bilinear Green current together with a separately source-fixed phase gauge.

The elementary phase ambiguity is classical.  The new content is the maximal route-level
classification and its exact theta-Hawking positive-clock separation.

`[NEW] [HB] [OPTICAL CURRENT] [ALL-PASS NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Most general finite same-frequency sesquilinear current built from common-amplitude linear
channels.  Translation-invariant differential channels are the specialization whose symbols are
polynomials in `i*x`; allowing arbitrary symbols and coefficients makes the no-go stronger. -/
def thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (x : ℝ) (amplitude : ℂ) : ℂ :=
  ∑ j, ∑ k,
    (starRingEnd ℂ) (symbol x j * amplitude) * coeff x j k *
      (symbol x k * amplitude)

/-- Exact quotient classification: every finite same-frequency sesquilinear current retains only
the intensity of the common amplitude.  No Hermiticity, positivity, order, or coefficient
restriction is needed. -/
theorem thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent_eq_intensity_mul
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (x : ℝ) (amplitude : ℂ) :
    thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
        symbol coeff x amplitude =
      (((‖amplitude‖ ^ (2 : ℕ) : ℝ)) : ℂ) *
        thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
          symbol coeff x 1 := by
  classical
  have hconj (z : ℂ) :
      (starRingEnd ℂ) z * z = (((‖z‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
  calc
    (∑ j, ∑ k,
        (starRingEnd ℂ) (symbol x j * amplitude) * coeff x j k *
          (symbol x k * amplitude)) =
        ∑ j, ∑ k,
          (((‖amplitude‖ ^ (2 : ℕ) : ℝ)) : ℂ) *
            ((starRingEnd ℂ) (symbol x j) * coeff x j k * symbol x k) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro k _hk
      rw [map_mul]
      calc
        (starRingEnd ℂ) (symbol x j) * (starRingEnd ℂ) amplitude * coeff x j k *
            (symbol x k * amplitude) =
            ((starRingEnd ℂ) amplitude * amplitude) *
              ((starRingEnd ℂ) (symbol x j) * coeff x j k * symbol x k) := by
                ring
        _ = _ := by rw [hconj]
    _ = (((‖amplitude‖ ^ (2 : ℕ) : ℝ)) : ℂ) *
        ∑ j, ∑ k,
          (starRingEnd ℂ) (symbol x j * 1) * coeff x j k *
            (symbol x k * 1) := by
      simp only [mul_one, Finset.mul_sum]

/-- A common unit phase is invisible to every current in the class. -/
theorem thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent_phase_invariant
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (x : ℝ) (amplitude phase : ℂ) (hphase : ‖phase‖ = 1) :
    thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
        symbol coeff x (phase * amplitude) =
      thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
        symbol coeff x amplitude := by
  calc
    thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
        symbol coeff x (phase * amplitude) =
        (((‖phase * amplitude‖ ^ (2 : ℕ) : ℝ)) : ℂ) *
          thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
            symbol coeff x 1 :=
      thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent_eq_intensity_mul
        symbol coeff x (phase * amplitude)
    _ = (((‖amplitude‖ ^ (2 : ℕ) : ℝ)) : ℂ) *
          thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
            symbol coeff x 1 := by
      rw [norm_mul, hphase, one_mul]
    _ = thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
          symbol coeff x amplitude :=
      (thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent_eq_intensity_mul
        symbol coeff x amplitude).symm

/-- Bare literal theta-Hawking current for arbitrary finite channel symbols and coefficients. -/
def thetaCuspHawkingFiniteSameFrequencySesquilinearBareCurrent
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ) (x : ℝ) : ℂ :=
  thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
    symbol coeff x (thetaCuspFourierLaplace (x : ℂ))

/-- Same current after the canonical causal all-pass dressing generated by a theta-Hawking
resonance. -/
def thetaCuspHawkingFiniteSameFrequencySesquilinearDressedCurrent
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) : ℂ :=
  thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent
    symbol coeff x (thetaCuspHawkingAllPassDressedBornFormFactor r x)

/-- Exact physical separation: every finite same-frequency sesquilinear current is unchanged by an
upper causal theta-Hawking all-pass sector, while that sector has a strictly positive local phase
clock. -/
theorem thetaCuspHawkingFiniteSameFrequencySesquilinearDressedCurrent_eq_bare_and_clock_pos
    {n : ℕ} (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) (x : ℝ) :
    thetaCuspHawkingFiniteSameFrequencySesquilinearDressedCurrent
        symbol coeff r x =
        thetaCuspHawkingFiniteSameFrequencySesquilinearBareCurrent
          symbol coeff x ∧
      0 < thetaCuspHawkingCausalAllPassClock r x := by
  constructor
  · exact
      thetaCuspHawkingFiniteSameFrequencySesquilinearCurrent_phase_invariant
        symbol coeff x (thetaCuspFourierLaplace (x : ℂ))
          (thetaCuspHawkingCausalAllPassBoundary r x)
            (norm_thetaCuspHawkingCausalAllPassBoundary r hr x)
  · exact thetaCuspHawkingCausalAllPassClock_pos r hr x

/-- Closed statement killing the complete finite same-frequency sesquilinear optical-current route.
All assumptions about a hypothetical upper resonance are bound inside the proposition. -/
def D4ThetaCuspHawkingFiniteSameFrequencySesquilinearOpticalCurrentRouteKilled : Prop :=
  ∀ (n : ℕ) (symbol : ℝ → Fin n → ℂ)
    (coeff : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (r : ThetaCuspHawkingBackreactionResonantMode),
    0 < r.1.im → ∀ x : ℝ,
      thetaCuspHawkingFiniteSameFrequencySesquilinearDressedCurrent
          symbol coeff r x =
          thetaCuspHawkingFiniteSameFrequencySesquilinearBareCurrent
            symbol coeff x ∧
        0 < thetaCuspHawkingCausalAllPassClock r x

/-- Premise-free Lean certificate for the route kill. -/
theorem d4ThetaCuspHawkingFiniteSameFrequencySesquilinearOpticalCurrentRouteKilled :
    D4ThetaCuspHawkingFiniteSameFrequencySesquilinearOpticalCurrentRouteKilled := by
  intro n symbol coeff r hr x
  exact
    thetaCuspHawkingFiniteSameFrequencySesquilinearDressedCurrent_eq_bare_and_clock_pos
      symbol coeff r hr x

end RHTower
