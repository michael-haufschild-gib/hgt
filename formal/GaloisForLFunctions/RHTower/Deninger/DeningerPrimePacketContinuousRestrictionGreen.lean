import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeBlockRestrictionAssembly
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimePacketHaarL2Green

/-!
# Continuous prime-packet restrictions and the global Haar-L² Green form

Arithmetic Cauchy data on a compact prime packet naturally arrives as a continuous function.
This module closes the analytic type conversion into the faithful Haar-`L²` packet target.
Normalized Haar measure makes the conversion contractive and full support makes it injective.
Consequently a square-summable sup-norm Bessel estimate implies the Hilbert-valued Bessel estimate
needed to assemble every prime restriction, without weakening a packet to its scalar average.

The resulting Green energy has an exact weighted formula and its radical is precisely the
simultaneous kernel of the original continuous packet restrictions.  Thus the remaining Route L
source theorem is now stated entirely before the `L²` completion: construct the arithmetic
continuous restrictions, prove their global sup-norm Bessel bound, and classify their simultaneous
kernel as the closed middle boundaries.
-/

namespace RHTower

open Filter MeasureTheory Topology
open scoped ENNReal BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous real-valued data on the concrete packet at `p`. -/
abbrev DeningerPrimePacketContinuous (p : Nat.Primes) : Type :=
  C(DeningerPacketFrobeniusQuotient p, ℝ)

/-- Convert a continuous packet-valued restriction to the canonical Haar-`L²` fibre. -/
def deningerPrimePacketContinuousRestriction
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (p : Nat.Primes) : E →L[ℝ] DeningerPrimePacketHaarL2 p :=
  (deningerPrimePacketContinuousToHaarL2 p).comp (restriction p)

@[simp] theorem deningerPrimePacketContinuousRestriction_apply
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (p : Nat.Primes) (x : E) :
    deningerPrimePacketContinuousRestriction restriction p x =
      deningerPrimePacketContinuousToHaarL2 p (restriction p x) := rfl

/-- Passage to Haar `L²` contracts each local restriction value. -/
theorem deningerPrimePacketContinuousRestriction_norm_le
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (p : Nat.Primes) (x : E) :
    ‖deningerPrimePacketContinuousRestriction restriction p x‖ ≤
      ‖restriction p x‖ := by
  exact deningerPrimePacketContinuousToHaarL2_apply_norm_le p (restriction p x)

/-- Passage to Haar `L²` preserves the local kernel of continuous packet data. -/
theorem deningerPrimePacketContinuousRestriction_eq_zero_iff
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (p : Nat.Primes) (x : E) :
    deningerPrimePacketContinuousRestriction restriction p x = 0 ↔
      restriction p x = 0 := by
  constructor
  · intro hx
    apply deningerPrimePacketContinuousToHaarL2_injective p
    simpa using hx
  · intro hx
    simp [deningerPrimePacketContinuousRestriction, hx]

/-- Square summability of the packet sup norms implies square summability of the Haar-`L²`
restrictions. -/
theorem summable_deningerPrimePacketContinuousRestriction
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    (x : E) :
    Summable fun p =>
      ‖deningerPrimePacketContinuousRestriction restriction p x‖ ^ (2 : ℝ) := by
  refine Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (norm_nonneg _) _)
    (fun p => ?_) (hSupSummable x)
  exact Real.rpow_le_rpow (norm_nonneg _)
    (deningerPrimePacketContinuousRestriction_norm_le restriction p x) (by norm_num)

/-- A sup-norm Bessel estimate descends to the canonical Haar-`L²` restrictions with the same
constant. -/
theorem deningerPrimePacketContinuousRestriction_bessel
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ}
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    ∑' p, ‖deningerPrimePacketContinuousRestriction restriction p x‖ ^ (2 : ℝ) ≤
      (C * ‖x‖) ^ (2 : ℝ) := by
  calc
    ∑' p, ‖deningerPrimePacketContinuousRestriction restriction p x‖ ^ (2 : ℝ) ≤
        ∑' p, ‖restriction p x‖ ^ (2 : ℝ) :=
      (summable_deningerPrimePacketContinuousRestriction
        restriction hSupSummable x).tsum_le_tsum
        (fun p => Real.rpow_le_rpow (norm_nonneg _)
          (deningerPrimePacketContinuousRestriction_norm_le restriction p x) (by norm_num))
        (hSupSummable x)
    _ ≤ (C * ‖x‖) ^ (2 : ℝ) := hSupBessel x

/-- One bounded comparison carrying all continuous prime-packet restrictions into the full
all-prime Haar Hilbert sum. -/
def deningerPrimePacketContinuousRestrictionOperator
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    E →L[ℝ] DeningerPrimePacketHaarHilbertSum :=
  deningerPrimeRestrictionOperator
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)

@[simp] theorem deningerPrimePacketContinuousRestrictionOperator_apply
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) (p : Nat.Primes) :
    deningerPrimePacketContinuousRestrictionOperator
      restriction hSupSummable hC hSupBessel x p =
        deningerPrimePacketContinuousToHaarL2 p (restriction p x) := rfl

/-- The assembled comparison loses exactly the vectors killed by every original continuous
packet restriction. -/
theorem deningerPrimePacketContinuousRestrictionOperator_mem_ker_iff
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    x ∈ LinearMap.ker
        (deningerPrimePacketContinuousRestrictionOperator
          restriction hSupSummable hC hSupBessel).toLinearMap ↔
      ∀ p, restriction p x = 0 := by
  rw [deningerPrimePacketContinuousRestrictionOperator,
    deningerPrimeRestrictionOperator_mem_ker_iff]
  exact forall_congr' fun p =>
    deningerPrimePacketContinuousRestriction_eq_zero_iff restriction p x

/-! ## Green energy on the arithmetic source -/

/-- Local prime-packet Green form pulled back to the source through the continuous restriction. -/
def deningerPrimePacketContinuousRestrictionLocalGreenForm
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) : E →L[ℝ] E →L[ℝ] ℝ :=
  deningerPrimeRestrictionLocalGreenForm
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)
    p

@[simp] theorem deningerPrimePacketContinuousRestrictionLocalGreenForm_apply_apply
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) (x y : E) :
    deningerPrimePacketContinuousRestrictionLocalGreenForm
        restriction hSupSummable hC hSupBessel p x y =
      deningerPrimeGraphGreenCoefficient p *
        inner ℝ
          (deningerPrimePacketContinuousToHaarL2 p (restriction p x))
          (deningerPrimePacketContinuousToHaarL2 p (restriction p y)) := by
  exact deningerPrimeRestrictionLocalGreenForm_apply_apply
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)
    p x y

/-- The pulled-back continuous-packet local Green forms are unconditionally operator-norm
summable. -/
theorem summable_deningerPrimePacketContinuousRestrictionLocalGreenForm
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    Summable (deningerPrimePacketContinuousRestrictionLocalGreenForm
      restriction hSupSummable hC hSupBessel) :=
  summable_deningerPrimeRestrictionLocalGreenForm
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)

/-- Global Green form obtained from the full continuous data on every prime packet. -/
def deningerPrimePacketContinuousRestrictionSummedGreenForm
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ)) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑' p, deningerPrimePacketContinuousRestrictionLocalGreenForm
    restriction hSupSummable hC hSupBessel p

/-- Exact weighted Haar-`L²` energy formula on the source. -/
theorem deningerPrimePacketContinuousRestrictionSummedGreenForm_self
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    deningerPrimePacketContinuousRestrictionSummedGreenForm
        restriction hSupSummable hC hSupBessel x x =
      ∑' p, deningerPrimeGraphGreenCoefficient p *
        ‖deningerPrimePacketContinuousToHaarL2 p (restriction p x)‖ ^ 2 := by
  exact deningerPrimeRestrictionSummedGreenForm_self
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)
    x

/-- Global energy from the full continuous packet data is nonnegative. -/
theorem deningerPrimePacketContinuousRestrictionSummedGreenForm_nonneg
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    0 ≤ deningerPrimePacketContinuousRestrictionSummedGreenForm
      restriction hSupSummable hC hSupBessel x x :=
  deningerPrimeRestrictionSummedGreenForm_nonneg
    (deningerPrimePacketContinuousRestriction restriction)
    (summable_deningerPrimePacketContinuousRestriction restriction hSupSummable)
    hC
    (deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel)
    x

/-- **Continuous-packet radical law.**  Green energy vanishes exactly when every original
continuous restriction vanishes. -/
theorem deningerPrimePacketContinuousRestrictionSummedGreenForm_self_eq_zero_iff
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (x : E) :
    deningerPrimePacketContinuousRestrictionSummedGreenForm
        restriction hSupSummable hC hSupBessel x x = 0 ↔
      ∀ p, restriction p x = 0 := by
  let restrictionL2 := deningerPrimePacketContinuousRestriction restriction
  let hL2Summable :=
    summable_deningerPrimePacketContinuousRestriction restriction hSupSummable
  let hL2Bessel :=
    deningerPrimePacketContinuousRestriction_bessel
      restriction hSupSummable hSupBessel
  have hradical := deningerPrimeRestrictionSummedGreenForm_self_eq_zero_iff
    restrictionL2 hL2Summable hC hL2Bessel x
  constructor
  · intro hx p
    have hxL2 : deningerPrimeRestrictionSummedGreenForm
        restrictionL2 hL2Summable hC hL2Bessel x x = 0 := by
      exact hx
    exact (deningerPrimePacketContinuousRestriction_eq_zero_iff
      restriction p x).mp (hradical.mp hxL2 p)
  · intro hx
    have hzero : ∀ p, restrictionL2 p x = 0 := fun p =>
      (deningerPrimePacketContinuousRestriction_eq_zero_iff
        restriction p x).mpr (hx p)
    have hxL2 : deningerPrimeRestrictionSummedGreenForm
        restrictionL2 hL2Summable hC hL2Bessel x x = 0 :=
      hradical.mpr hzero
    exact hxL2

/-- Boundary classification of the continuous packet restrictions is exactly the remaining
radical-identification theorem. -/
theorem deningerPrimePacketContinuousRestrictionSummedGreenForm_self_eq_zero_iff_mem_boundaries
    (restriction : ∀ p, E →L[ℝ] DeningerPrimePacketContinuous p)
    (hSupSummable : ∀ x,
      Summable fun p => ‖restriction p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hSupBessel : ∀ x,
      ∑' p, ‖restriction p x‖ ^ (2 : ℝ) ≤ (C * ‖x‖) ^ (2 : ℝ))
    (boundaries : Submodule ℝ E)
    (hclassifies : ∀ x, (∀ p, restriction p x = 0) ↔ x ∈ boundaries)
    (x : E) :
    deningerPrimePacketContinuousRestrictionSummedGreenForm
        restriction hSupSummable hC hSupBessel x x = 0 ↔
      x ∈ boundaries := by
  rw [deningerPrimePacketContinuousRestrictionSummedGreenForm_self_eq_zero_iff,
    hclassifies]

end

end RHTower
