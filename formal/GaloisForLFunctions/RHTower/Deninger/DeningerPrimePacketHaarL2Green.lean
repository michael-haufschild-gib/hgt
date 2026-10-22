import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockGreenSummability
import GaloisForLFunctions.RHTower.Deninger.DeningerPacketFrobeniusQuotientNontrivial
import GaloisForLFunctions.RHTower.Deninger.DeningerPacketNonlocal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Canonical Haar-L² Green form on the concrete prime packets

The full-block theorem allows arbitrary complete real Hilbert fibres.  This module instantiates
them canonically on the concrete quotient packet already constructed for each prime: take normalized
Haar `L²` of `DeningerPacketFrobeniusQuotient p`.  Unlike scalar packet averaging, this fibre keeps
every square-integrable mean-zero/Fourier/transverse mode.

The all-prime direct sum inherits unordered operator-norm summability with coefficient
`(log p)⁻²`, an exact weighted energy formula, nonnegativity, and zero radical.  The result is a
source-native candidate target, not a comparison from the arithmetic relevant complex.
-/

namespace RHTower

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal BigOperators

noncomputable section

/-- Borel measurable structure on the compact prime-packet quotient. -/
noncomputable instance deningerPacketFrobeniusQuotientMeasurableSpace (p : Nat.Primes) :
    MeasurableSpace (DeningerPacketFrobeniusQuotient p) :=
  borel (DeningerPacketFrobeniusQuotient p)

noncomputable instance deningerPacketFrobeniusQuotientBorelSpace (p : Nat.Primes) :
    BorelSpace (DeningerPacketFrobeniusQuotient p) := ⟨rfl⟩

/-- Whole compact quotient packet, bundled as the normalizing positive compact. -/
def deningerPrimePacketPositiveCompact (p : Nat.Primes) :
    PositiveCompacts (DeningerPacketFrobeniusQuotient p) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar measure normalized to give the whole quotient packet mass one. -/
def deningerPrimePacketHaarMeasure (p : Nat.Primes) :
    Measure (DeningerPacketFrobeniusQuotient p) :=
  Measure.haarMeasure (deningerPrimePacketPositiveCompact p)

theorem deningerPrimePacketHaarMeasure_univ (p : Nat.Primes) :
    deningerPrimePacketHaarMeasure p Set.univ = 1 := by
  exact Measure.haarMeasure_self

noncomputable instance deningerPrimePacketHaarMeasureProbability (p : Nat.Primes) :
    IsProbabilityMeasure (deningerPrimePacketHaarMeasure p) :=
  ⟨deningerPrimePacketHaarMeasure_univ p⟩

/-- Normalized Haar measure on the packet is positive on every nonempty open set. -/
noncomputable instance deningerPrimePacketHaarMeasureIsOpenPos (p : Nat.Primes) :
    (deningerPrimePacketHaarMeasure p).IsOpenPosMeasure := by
  unfold deningerPrimePacketHaarMeasure
  infer_instance

/-- Canonical real Hilbert fibre retaining all `L²` modes on the prime packet. -/
abbrev DeningerPrimePacketHaarL2 (p : Nat.Primes) : Type :=
  Lp ℝ 2 (deningerPrimePacketHaarMeasure p)

/-- Canonical inclusion of continuous real packet data into the full Haar-`L²` fibre. -/
def deningerPrimePacketContinuousToHaarL2 (p : Nat.Primes) :
    C(DeningerPacketFrobeniusQuotient p, ℝ) →L[ℝ] DeningerPrimePacketHaarL2 p :=
  ContinuousMap.toLp 2 (deningerPrimePacketHaarMeasure p) ℝ

/-- Probability normalization makes the continuous-to-Haar-`L²` inclusion contractive. -/
theorem deningerPrimePacketContinuousToHaarL2_norm_le (p : Nat.Primes) :
    ‖deningerPrimePacketContinuousToHaarL2 p‖ ≤ 1 := by
  have h := ContinuousMap.toLp_norm_le
    (p := 2) (deningerPrimePacketHaarMeasure p) (𝕜 := ℝ) (E := ℝ)
  have hu : measureUnivNNReal (deningerPrimePacketHaarMeasure p) = 1 := by
    simp [measureUnivNNReal]
  rw [hu] at h
  simpa [deningerPrimePacketContinuousToHaarL2] using h

/-- Haar `L²` norm is bounded by the uniform norm of continuous packet data. -/
theorem deningerPrimePacketContinuousToHaarL2_apply_norm_le
    (p : Nat.Primes) (f : C(DeningerPacketFrobeniusQuotient p, ℝ)) :
    ‖deningerPrimePacketContinuousToHaarL2 p f‖ ≤ ‖f‖ := by
  calc
    ‖deningerPrimePacketContinuousToHaarL2 p f‖ ≤
        ‖deningerPrimePacketContinuousToHaarL2 p‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (deningerPrimePacketContinuousToHaarL2_norm_le p) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- Full-support Haar measure loses no continuous packet function. -/
theorem deningerPrimePacketContinuousToHaarL2_injective (p : Nat.Primes) :
    Function.Injective (deningerPrimePacketContinuousToHaarL2 p) := by
  exact ContinuousMap.toLp_injective (deningerPrimePacketHaarMeasure p)

/-- Every quotient packet has a clopen piece of strictly intermediate Haar probability. -/
theorem deningerPrimePacket_exists_clopen_intermediateMass (p : Nat.Primes) :
    ∃ D : Set (DeningerPacketFrobeniusQuotient p), IsClopen D ∧
      0 < (deningerPrimePacketHaarMeasure p).real D ∧
      (deningerPrimePacketHaarMeasure p).real D < 1 := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (DeningerPacketFrobeniusQuotient p)
  obtain ⟨D, hD, hx, hy⟩ := exists_isClopen_of_totally_separated hxy
  have hDne : D.Nonempty := ⟨x, hx⟩
  have hDcne : Dᶜ.Nonempty := ⟨y, hy⟩
  have hpos : 0 < (deningerPrimePacketHaarMeasure p).real D := by
    exact ENNReal.toReal_pos
      (hD.isOpen.measure_ne_zero (deningerPrimePacketHaarMeasure p) hDne)
      (measure_ne_top (deningerPrimePacketHaarMeasure p) D)
  have hcomppos : 0 < (deningerPrimePacketHaarMeasure p).real Dᶜ := by
    exact ENNReal.toReal_pos
      (hD.compl.isOpen.measure_ne_zero (deningerPrimePacketHaarMeasure p) hDcne)
      (measure_ne_top (deningerPrimePacketHaarMeasure p) Dᶜ)
  refine ⟨D, hD, hpos, ?_⟩
  rw [measureReal_compl hD.isClosed.measurableSet, probReal_univ] at hcomppos
  linarith

/-- **Nonvacuous transverse sector.**  Every prime packet has a nonzero continuous mean-zero
function whose image remains nonzero in Haar `L²`. -/
theorem deningerPrimePacket_exists_nonzero_meanZeroHaarMode (p : Nat.Primes) :
    ∃ f : C(DeningerPacketFrobeniusQuotient p, ℝ),
      deningerPacketAv (deningerPrimePacketHaarMeasure p) f = 0 ∧
      deningerPrimePacketContinuousToHaarL2 p f ≠ 0 := by
  obtain ⟨D, hD, hpos, hlt⟩ := deningerPrimePacket_exists_clopen_intermediateMass p
  obtain ⟨f, havg, hf⟩ :=
    deningerPacketAv_ker_ne_bot (deningerPrimePacketHaarMeasure p) hD hpos hlt
  exact ⟨f, havg, (deningerPrimePacketContinuousToHaarL2_injective p).ne hf⟩

/-- All-prime Hilbert sum of the canonical packet Haar-`L²` fibres. -/
abbrev DeningerPrimePacketHaarHilbertSum : Type :=
  DeningerHilbertSum DeningerPrimePacketHaarL2

/-- Local prime Green form on the full Haar-`L²` packet fibre. -/
def deningerPrimePacketHaarLocalGreenForm (p : Nat.Primes) :
    DeningerPrimePacketHaarHilbertSum →L[ℝ]
      DeningerPrimePacketHaarHilbertSum →L[ℝ] ℝ :=
  deningerPrimeBlockGreenForm (Kp := DeningerPrimePacketHaarL2) p

@[simp] theorem deningerPrimePacketHaarLocalGreenForm_apply_apply
    (p : Nat.Primes) (x y : DeningerPrimePacketHaarHilbertSum) :
    deningerPrimePacketHaarLocalGreenForm p x y =
      deningerPrimeGraphGreenCoefficient p * inner ℝ (x p) (y p) := by
  exact deningerBlockCoordinateGreenForm_apply_apply _ _ _ _ _

/-- Full Haar-packet local Green forms sum unconditionally in operator norm. -/
theorem summable_deningerPrimePacketHaarLocalGreenForm :
    Summable deningerPrimePacketHaarLocalGreenForm :=
  summable_deningerPrimeBlockGreenForm
    (Kp := DeningerPrimePacketHaarL2)

/-- Global Green form on the canonical all-prime Haar-packet Hilbert sum. -/
def deningerPrimePacketHaarSummedGreenForm :
    DeningerPrimePacketHaarHilbertSum →L[ℝ]
      DeningerPrimePacketHaarHilbertSum →L[ℝ] ℝ :=
  ∑' p, deningerPrimePacketHaarLocalGreenForm p

/-- Exact weighted Haar-`L²` energy formula. -/
theorem deningerPrimePacketHaarSummedGreenForm_self
    (x : DeningerPrimePacketHaarHilbertSum) :
    deningerPrimePacketHaarSummedGreenForm x x =
      ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p * ‖x p‖ ^ 2 :=
  deningerPrimeBlockSummedGreenForm_self
    (Kp := DeningerPrimePacketHaarL2) x

/-- The canonical all-prime Haar-packet energy is nonnegative. -/
theorem deningerPrimePacketHaarSummedGreenForm_nonneg
    (x : DeningerPrimePacketHaarHilbertSum) :
    0 ≤ deningerPrimePacketHaarSummedGreenForm x x :=
  deningerPrimeBlockSummedGreenForm_nonneg
    (Kp := DeningerPrimePacketHaarL2) x

/-- No nonzero packet `L²` mode, including a mean-zero mode, lies in the global radical. -/
theorem deningerPrimePacketHaarSummedGreenForm_self_eq_zero_iff
    (x : DeningerPrimePacketHaarHilbertSum) :
    deningerPrimePacketHaarSummedGreenForm x x = 0 ↔ x = 0 :=
  deningerPrimeBlockSummedGreenForm_self_eq_zero_iff
    (Kp := DeningerPrimePacketHaarL2) x

end

end RHTower
