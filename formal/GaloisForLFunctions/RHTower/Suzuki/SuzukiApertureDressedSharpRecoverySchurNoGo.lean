import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureDressedSchurTaxUniformBound
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentSharpSourceDomainNoGo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompletedMellinPositiveDomainNoGo

/-!
# Sharp recovery obstruction for Suzuki's dressed scalar Schur channel

A fixed scalar Schur ratio is harmless after actual aperture dressing, but such a fixed gain cannot
recover the observer-free sharp wall source.  This module proves the complementary obstruction:
allowing arbitrary prime-dependent apertures and gains does not repair the scalar diagonal route.
Whenever the amplified dressed atom dominates every sharp source coordinate, its Schur tax
dominates the nonsummable sharp source square prime by prime.

The positive survivor is sharp.  Exact coefficientwise recovery cancels all aperture and height
dependence and leaves the critical Suzuki prime mass.  A prime-log trace displacement `delta`
makes this exact recovery tax summable if and only if `1 / 2 < delta`.  Thus an ordinary scalar
trace cannot carry exact sharp recovery; exponential prime-log displacement must cross precisely
half a unit.

No RH premise, Xi-zero hypothesis, computation, asymptotic estimate, or added axiom is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Scalar Schur tax after a prime-dependent gain is applied to one dressed depth-zero atom. -/
def suzukiCriticalApertureDressedSharpRecoveryTax
    (h t : ℝ) (aperture gain : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  suzukiCriticalApertureDressedScalarSchurTax
    h (aperture p) t 1 (gain p) (p, 0)

theorem suzukiCriticalApertureDressedSharpRecoveryTax_eq_sq
    (h t : ℝ) (aperture gain : Nat.Primes → ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDressedSharpRecoveryTax h t aperture gain p =
      (gain p * ‖suzukiCriticalApertureBoundaryAtom
        h (aperture p) t p 0‖) ^ (2 : ℕ) := by
  rw [suzukiCriticalApertureDressedSharpRecoveryTax,
    suzukiCriticalApertureDressedScalarSchurTax,
    Complex.normSq_eq_norm_sq]
  ring

theorem suzukiCriticalApertureDressedSharpRecoveryTax_nonneg
    (h t : ℝ) (aperture gain : Nat.Primes → ℝ) (p : Nat.Primes) :
    0 ≤ suzukiCriticalApertureDressedSharpRecoveryTax h t aperture gain p := by
  rw [suzukiCriticalApertureDressedSharpRecoveryTax_eq_sq]
  positivity

theorem not_summable_suzukiCriticalApertureDressedSharpRecoveryTax
    (h t : ℝ) (aperture gain : Nat.Primes → ℝ)
    (hrecovers : ∀ p : Nat.Primes,
      suzukiCriticalEntryWallBareAmplitude p 0 ≤
        gain p * ‖suzukiCriticalApertureBoundaryAtom
          h (aperture p) t p 0‖) :
    ¬ Summable
      (suzukiCriticalApertureDressedSharpRecoveryTax h t aperture gain) := by
  intro htax
  apply not_summable_sq_suzukiCriticalEntryWallBareAmplitude_zero
  refine Summable.of_nonneg_of_le
    (fun p => sq_nonneg (suzukiCriticalEntryWallBareAmplitude p 0))
    (fun p => ?_) htax
  rw [suzukiCriticalApertureDressedSharpRecoveryTax_eq_sq]
  have hsource : 0 ≤ suzukiCriticalEntryWallBareAmplitude p 0 :=
    Real.sqrt_nonneg _
  have hresponse :
      0 ≤ gain p * ‖suzukiCriticalApertureBoundaryAtom
        h (aperture p) t p 0‖ :=
    hsource.trans (hrecovers p)
  exact (sq_le_sq₀ hsource hresponse).2 (hrecovers p)

/-- No scalar diagonal carrier can simultaneously recover every exact sharp source coordinate and
pay finite total dressed Schur tax, even with arbitrary prime-dependent apertures and gains. -/
theorem no_summable_suzukiCriticalApertureDressedSharpRecovery :
    ∀ (h t : ℝ) (aperture : Nat.Primes → ℝ),
      ¬ ∃ gain : Nat.Primes → ℝ,
        (∀ p : Nat.Primes,
          suzukiCriticalEntryWallBareAmplitude p 0 ≤
            gain p * ‖suzukiCriticalApertureBoundaryAtom
              h (aperture p) t p 0‖) ∧
        Summable
          (suzukiCriticalApertureDressedSharpRecoveryTax h t aperture gain) := by
  intro h t aperture
  rintro ⟨gain, hrecovers, htax⟩
  exact not_summable_suzukiCriticalApertureDressedSharpRecoveryTax
    h t aperture gain hrecovers htax

/-- Every finite scalar capacity is exceeded by one finite packet under sharp recovery. -/
theorem exists_finset_suzukiCriticalApertureDressedSharpRecoveryTax_gt
    (h t : ℝ) (aperture gain : Nat.Primes → ℝ)
    (hrecovers : ∀ p : Nat.Primes,
      suzukiCriticalEntryWallBareAmplitude p 0 ≤
        gain p * ‖suzukiCriticalApertureBoundaryAtom
          h (aperture p) t p 0‖)
    (B : ℝ) :
    ∃ F : Finset Nat.Primes,
      B < ∑ p ∈ F,
        suzukiCriticalApertureDressedSharpRecoveryTax h t aperture gain p := by
  by_contra hbound
  simp only [not_exists, not_lt] at hbound
  apply not_summable_suzukiCriticalApertureDressedSharpRecoveryTax
    h t aperture gain hrecovers
  exact summable_of_sum_le
    (suzukiCriticalApertureDressedSharpRecoveryTax_nonneg h t aperture gain)
    hbound

/-! ## Sharp positive trace-displacement survivor -/

/-- Pointwise scalar gain recovering the observer-free sharp source from one nonzero dressed
depth-zero boundary atom. -/
def suzukiCriticalApertureExactSharpRecoveryGain
    (h a t : ℝ) (p : Nat.Primes) : ℝ :=
  suzukiCriticalEntryWallBareAmplitude p 0 /
    ‖suzukiCriticalApertureBoundaryAtom h a t p 0‖

theorem suzukiCriticalApertureExactSharpRecoveryGain_mul_norm_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureExactSharpRecoveryGain h a t p *
        ‖suzukiCriticalApertureBoundaryAtom h a t p 0‖ =
      suzukiCriticalEntryWallBareAmplitude p 0 := by
  rw [suzukiCriticalApertureExactSharpRecoveryGain]
  apply div_mul_cancel₀
  intro hnorm
  have hq := normSq_suzukiCriticalApertureBoundaryAtom_pos hh ha t (p, 0)
  rw [Complex.normSq_eq_norm_sq, hnorm] at hq
  norm_num at hq

theorem suzukiCriticalApertureExactSharpRecoveryTax_eq_sharpPrimeMass
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureDressedSharpRecoveryTax h t (fun _ => a)
        (suzukiCriticalApertureExactSharpRecoveryGain h a t) p =
      suzukiCriticalSharpPrimeMass p := by
  rw [suzukiCriticalApertureDressedSharpRecoveryTax_eq_sq,
    suzukiCriticalApertureExactSharpRecoveryGain_mul_norm_eq hh ha,
    suzukiCriticalSharpPrimeMass]

/-- Trace displacement applied after exact scalar source recovery. -/
def suzukiCriticalApertureDisplacedExactSharpRecoveryTax
    (h a t delta : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-delta * Real.log (p : ℝ)) *
    suzukiCriticalApertureDressedSharpRecoveryTax h t (fun _ => a)
      (suzukiCriticalApertureExactSharpRecoveryGain h a t) p

theorem suzukiCriticalApertureDisplacedExactSharpRecoveryTax_eq_mellinMass
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t delta : ℝ)
    (p : Nat.Primes) :
    suzukiCriticalApertureDisplacedExactSharpRecoveryTax h a t delta p =
      suzukiCriticalMellinWeightedPrimeMass (delta + 1 / 2) p := by
  rw [suzukiCriticalApertureDisplacedExactSharpRecoveryTax,
    suzukiCriticalApertureExactSharpRecoveryTax_eq_sharpPrimeMass hh ha,
    suzukiCriticalMellinWeightedPrimeMass, suzukiCriticalMellinProfile]
  rw [show -(delta + 1 / 2 - 1 / 2) * Real.log (p : ℝ) =
      -delta * Real.log (p : ℝ) by ring]
  ring

/-- **Sharp scalar-recovery trace threshold.** After exact coefficientwise recovery of the sharp
Suzuki source, a displaced scalar Schur trace is summable exactly beyond half a prime-log unit. -/
theorem summable_suzukiCriticalApertureDisplacedExactSharpRecoveryTax_iff
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t delta : ℝ) :
    Summable
        (suzukiCriticalApertureDisplacedExactSharpRecoveryTax h a t delta) ↔
      1 / 2 < delta := by
  rw [show Summable
      (suzukiCriticalApertureDisplacedExactSharpRecoveryTax h a t delta) ↔
      Summable (suzukiCriticalMellinWeightedPrimeMass (delta + 1 / 2)) by
    apply summable_congr
    intro p
    exact suzukiCriticalApertureDisplacedExactSharpRecoveryTax_eq_mellinMass
      hh ha t delta p]
  rw [summable_suzukiCriticalMellinWeightedPrimeMass_iff]
  constructor <;> intro hdelta <;> linarith

end

end RHTower
