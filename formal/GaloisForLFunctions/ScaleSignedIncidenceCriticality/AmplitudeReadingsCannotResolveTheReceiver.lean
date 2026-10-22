import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RealCharacterParityPairsAndTheParityBarrier

/-!
# Amplitude readings cannot resolve the receiver

The datum is an arithmetic weight `c : ℕ → ℝ` of the damped class `|c(d)| ≤ K d^{-ε}`, the property
is boundedness of its pronic receiver energy, and the reading is the family of Ramanujan amplitudes
`|W_c(e)|`.

Two witness pairs from the corpus have equal amplitudes and opposite receivers: the damped Möbius
weight at half damping against its parity twin
(`TransHorizonIncidenceMechanics.parityPair_at_half_damping`) — the actual arithmetic source, not a
model — and, at every damping `0 < ε ≤ ½`, a real-character pair rescaled into the class
(`TransHorizonIncidenceMechanics.parity_barrier`).

* `not_resolves_amplitudeReading_receiver`: the amplitudes do not resolve the receiver at half
  damping, on the actual Möbius datum.
* `not_resolves_classAmplitudeReading`, `half_lt_of_resolves_classAmplitudeReading`: the amplitude
  reading resolves receiver boundedness only above half damping, so **the amplitude floor of the
  receiver unit is `½`** — the same number the width dictionary reads as the trivial bound.
* `not_resolves_amplitudeDerivedFamily`: and no family of amplitude-derived observables of any
  cardinality — variances, lag covariances, pronic mode masses, any statistic of the squared
  amplitudes (`sq_weightRamanujanCoeff_parityTwin`) — does better. Post-processing and joining
  blind observables keeps them blind, so the floor is a property of the *reading*, not of the
  estimate built from it.
-/

open Filter Topology

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

universe u

/-! ### 1. The amplitude reading -/

/-- The amplitude reading: the Ramanujan amplitudes of the weight at every modulus. -/
noncomputable def amplitudeReading (c : ℕ → ℝ) : ℕ → ℝ := fun e => |weightRamanujanCoeff c e|

/-- Bounded receiver at a fixed mean: the pronic energies stay below one budget. -/
def ReceiverBoundedAt (m : ℝ) (c : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ T : ℕ, weightPronicEnergy c m T ≤ B

theorem weightRamanujanCoeff_zero (c : ℕ → ℝ) : weightRamanujanCoeff c 0 = 0 := by
  simp [weightRamanujanCoeff]

/-! ### 2. The actual Möbius datum at half damping -/

/-- The twin and the damped Möbius weight have the same amplitude reading. -/
theorem amplitudeReading_parityTwin :
    amplitudeReading (parityTwinWeight (1 / 2)) =
      amplitudeReading (pmPowerDampedRealWeight (1 / 2)) := by
  obtain ⟨-, habs, -, -, -⟩ := parityPair_at_half_damping
  funext e
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [amplitudeReading, weightRamanujanCoeff_zero]
  · exact habs e he

/-- The damped Möbius weight has a bounded receiver at half damping. -/
theorem receiverBoundedAt_pmPowerDamped :
    ReceiverBoundedAt (dampedDensity (1 / 2)) (pmPowerDampedRealWeight (1 / 2)) :=
  parityPair_at_half_damping.2.2.2.1

/-- Its parity twin does not: the receiver energies diverge. -/
theorem not_receiverBoundedAt_parityTwin :
    ¬ ReceiverBoundedAt (dampedDensity (1 / 2)) (parityTwinWeight (1 / 2)) := by
  rintro ⟨B, hB⟩
  obtain ⟨T, hT⟩ := (parityPair_at_half_damping.2.2.2.2.eventually_ge_atTop (B + 1)).exists
  linarith [hB T]

/-- **The amplitudes do not resolve the receiver.** The damped Möbius weight at half damping and
its parity twin have the same amplitude reading, bounded receiver against divergent. -/
theorem not_resolves_amplitudeReading_receiver :
    ¬ Resolves amplitudeReading (ReceiverBoundedAt (dampedDensity (1 / 2))) :=
  not_resolves_of_pair amplitudeReading_parityTwin receiverBoundedAt_pmPowerDamped
    not_receiverBoundedAt_parityTwin

/-- **The parity wall gate.** The pair is identified by the amplitude reading, and every reading
that resolves the receiver separates it. -/
theorem parityWallGate :
    amplitudeReading (parityTwinWeight (1 / 2)) =
        amplitudeReading (pmPowerDampedRealWeight (1 / 2)) ∧
      ∀ (O : Type u) (r : (ℕ → ℝ) → O),
        Resolves r (ReceiverBoundedAt (dampedDensity (1 / 2))) →
          r (parityTwinWeight (1 / 2)) ≠ r (pmPowerDampedRealWeight (1 / 2)) :=
  ⟨amplitudeReading_parityTwin, fun _ _ hres heq =>
    not_resolves_of_pair heq receiverBoundedAt_pmPowerDamped not_receiverBoundedAt_parityTwin hres⟩

/-! ### 3. The amplitude floor of the receiver unit -/

/-- Weights of the damped class `|c(d)| ≤ K d^{-ε}`: the receiver data at damping `ε`. -/
def DampedWeight (K ε : ℝ) : Type := {c : ℕ → ℝ // DampedClass K ε c}

/-- The amplitude reading on the damped class. -/
noncomputable def classAmplitudeReading (K ε : ℝ) (c : DampedWeight K ε) : ℕ → ℝ :=
  amplitudeReading c.1

/-- Receiver boundedness on the damped class, at the weight's own mean. -/
def classReceiverBounded (K ε : ℝ) (c : DampedWeight K ε) : Prop := ReceiverBounded c.1

/-- **The amplitude reading does not resolve the receiver at or below half damping.** -/
theorem not_resolves_classAmplitudeReading {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ Resolves (classAmplitudeReading K ε) (classReceiverBounded K ε) := fun hres => by
  obtain ⟨Φ, hΦ⟩ := resolves_iff_exists_factorization.mp hres
  exact parity_barrier hK hε hε2 ⟨Φ, fun c hc => hΦ ⟨c, hc⟩⟩

/-- **The amplitude floor is `½`.** An amplitude-reading criterion for receiver boundedness exists
only above half damping. -/
theorem half_lt_of_resolves_classAmplitudeReading {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hres : Resolves (classAmplitudeReading K ε) (classReceiverBounded K ε)) : 1 / 2 < ε := by
  by_contra h
  push Not at h
  exact not_resolves_classAmplitudeReading hK hε h hres

/-! ### 4. Every amplitude-derived family is blind as well -/

/-- Any family of observables computed from the amplitudes is refined by the amplitude reading. -/
theorem refines_amplitudeDerivedFamily {K ε : ℝ} {ι : Type*} {O : ι → Type*}
    (g : ∀ i, (ℕ → ℝ) → O i) :
    Refines (classAmplitudeReading K ε)
      (familyReading fun i (c : DampedWeight K ε) => g i (classAmplitudeReading K ε c)) :=
  fun d e he => by
    have h : classAmplitudeReading K ε e = classAmplitudeReading K ε d := he
    exact funext fun i =>
      show g i (classAmplitudeReading K ε e) = g i (classAmplitudeReading K ε d) by rw [h]

/-- **No family of amplitude-derived observables resolves the receiver below half damping**,
whatever its cardinality: joining and post-processing blind observables keeps them blind. -/
theorem not_resolves_amplitudeDerivedFamily {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {ι : Type*} {O : ι → Type*} (g : ∀ i, (ℕ → ℝ) → O i) :
    ¬ Resolves (familyReading fun i (c : DampedWeight K ε) => g i (classAmplitudeReading K ε c))
      (classReceiverBounded K ε) := fun hres =>
  not_resolves_classAmplitudeReading hK hε hε2
    (Resolves.of_refines (refines_amplitudeDerivedFamily g) hres)

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
