import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFiniteEvaluationBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerTateGraphGreenPrimeSector
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Rational-Witt first suspension-mode transgression

Finite rational-Witt evaluation produces functions on the profinite quotient packet.  That is the
horizontal sector of the prime fibre, not yet its positive transverse middle sector.  The literal
prime fibre is the product of the quotient packet with the period-`log p` suspension circle.

This module tensors every complex packet `L²` vector with the canonical first Fourier character of
that circle.  The resulting map is an isometric complex-linear embedding, is orthogonal to the
circle-horizontal sector, and has prime-independent Tate-normalized energy `2π ‖f‖²`.

Every nonzero finite packet function therefore has both an arithmetic-Frobenius-fixed witness in
the published complexified rational-Witt presentation and a nonzero positive-energy first
suspension mode on the literal prime fibre.  This is a local variance correction.  It does not
assert the still-missing global Bessel or middle-boundary theorem.
-/

namespace RHTower

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

noncomputable instance deningerPrimeLogPeriodPositive (p : Nat.Primes) :
    Fact (0 < Real.log (p : ℝ)) :=
  ⟨Real.log_pos (by exact_mod_cast p.prop.one_lt)⟩

/-- Complex Haar `L²` on the profinite quotient packet. -/
abbrev DeningerPrimePacketComplexHaarL2 (p : Nat.Primes) : Type :=
  Lp ℂ 2 (deningerPrimePacketHaarMeasure p)

/-- Complex Haar `L²` on the literal product presentation of the prime mapping torus. -/
abbrev DeningerPrimeSuspensionHaarL2 (p : Nat.Primes) : Type :=
  Lp ℂ 2 ((deningerPrimePacketHaarMeasure p).prod
    (AddCircle.haarAddCircle :
      Measure (AddCircle (Real.log (p : ℝ)))))

/-- First Fourier mode on the prime-period suspension circle. -/
abbrev deningerPrimeFirstCircleMode (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle :
      Measure (AddCircle (Real.log (p : ℝ)))) :=
  fourierLp 2 1

theorem norm_deningerPrimeFirstCircleMode (p : Nat.Primes) :
    ‖deningerPrimeFirstCircleMode p‖ = 1 :=
  (orthonormal_fourier
    (T := Real.log (p : ℝ))).1 1

/-- Canonical first-mode transgression from the packet to its mapping-torus prime fibre. -/
def deningerPrimeSuspensionFirstMode (p : Nat.Primes) :
    DeningerPrimePacketComplexHaarL2 p →L[ℂ]
      DeningerPrimeSuspensionHaarL2 p :=
  MeasureTheory.l2SeparatedProductContinuousBilinear.flip
    (deningerPrimeFirstCircleMode p)

@[simp]
theorem deningerPrimeSuspensionFirstMode_apply
    (p : Nat.Primes) (f : DeningerPrimePacketComplexHaarL2 p) :
    deningerPrimeSuspensionFirstMode p f =
      MeasureTheory.l2SeparatedProduct f
        (deningerPrimeFirstCircleMode p) := rfl

/-- The first suspension-mode transgression preserves Haar `L²` norm exactly. -/
theorem norm_deningerPrimeSuspensionFirstMode
    (p : Nat.Primes) (f : DeningerPrimePacketComplexHaarL2 p) :
    ‖deningerPrimeSuspensionFirstMode p f‖ = ‖f‖ := by
  rw [deningerPrimeSuspensionFirstMode_apply,
    MeasureTheory.l2SeparatedProduct_norm,
    norm_deningerPrimeFirstCircleMode, mul_one]

/-- The first suspension-mode transgression is injective. -/
theorem deningerPrimeSuspensionFirstMode_injective (p : Nat.Primes) :
    Function.Injective (deningerPrimeSuspensionFirstMode p) := by
  intro f g hfg
  apply sub_eq_zero.mp
  rw [← norm_eq_zero]
  rw [← norm_deningerPrimeSuspensionFirstMode p (f - g),
    map_sub, hfg, sub_self, norm_zero]

/-- Circle-horizontal inclusion, using the zero Fourier mode. -/
def deningerPrimeSuspensionHorizontalMode (p : Nat.Primes) :
    DeningerPrimePacketComplexHaarL2 p →L[ℂ]
      DeningerPrimeSuspensionHaarL2 p :=
  MeasureTheory.l2SeparatedProductContinuousBilinear.flip
    (fourierLp 2 0 :
      Lp ℂ 2 (AddCircle.haarAddCircle :
        Measure (AddCircle (Real.log (p : ℝ)))))

/-- First suspension modes are orthogonal to every circle-horizontal packet function. -/
theorem inner_deningerPrimeSuspensionFirstMode_horizontal
    (p : Nat.Primes)
    (f g : DeningerPrimePacketComplexHaarL2 p) :
    inner ℂ (deningerPrimeSuspensionFirstMode p f)
        (deningerPrimeSuspensionHorizontalMode p g) = 0 := by
  rw [deningerPrimeSuspensionFirstMode_apply]
  change inner ℂ
      (MeasureTheory.l2SeparatedProduct f (fourierLp 2 1))
      (MeasureTheory.l2SeparatedProduct g (fourierLp 2 0)) = 0
  rw [MeasureTheory.l2SeparatedProduct_inner]
  rw [(orthonormal_fourier
    (T := Real.log (p : ℝ))).2 (by norm_num : (1 : ℤ) ≠ 0),
    mul_zero]

/-- Unsmoothed Tate-normalized Green energy of a first suspension mode. -/
noncomputable def deningerPrimeSuspensionFirstModeGreenEnergy
    (p : Nat.Primes) (f : DeningerPrimePacketComplexHaarL2 p) : ℝ :=
  deningerTateCircleModeRate 1 *
    ‖deningerPrimeSuspensionFirstMode p f‖ ^ 2

/-- Exact first-mode energy: the Tate-normalized eigenvalue is the prime-independent `2π`. -/
theorem deningerPrimeSuspensionFirstModeGreenEnergy_eq
    (p : Nat.Primes) (f : DeningerPrimePacketComplexHaarL2 p) :
    deningerPrimeSuspensionFirstModeGreenEnergy p f =
      (2 * Real.pi) * ‖f‖ ^ 2 := by
  rw [deningerPrimeSuspensionFirstModeGreenEnergy,
    norm_deningerPrimeSuspensionFirstMode]
  simp [deningerTateCircleModeRate]

/-- Every nonzero packet coefficient acquires strictly positive first-mode Tate energy. -/
theorem deningerPrimeSuspensionFirstModeGreenEnergy_pos
    (p : Nat.Primes) {f : DeningerPrimePacketComplexHaarL2 p}
    (hf : f ≠ 0) :
    0 < deningerPrimeSuspensionFirstModeGreenEnergy p f := by
  rw [deningerPrimeSuspensionFirstModeGreenEnergy_eq]
  exact mul_pos (mul_pos zero_lt_two Real.pi_pos)
    (sq_pos_of_pos (norm_pos_iff.mpr hf))

/-- Complex pullback of a finite packet function to the literal profinite packet. -/
def deningerPrimeFiniteStageComplexPullback (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    C(DeningerPacketFrobeniusQuotient p, ℂ) where
  toFun x := F (deningerPrimeFiniteStageQuotientReduction p s x)
  continuous_toFun :=
    continuous_of_discreteTopology.comp
      (deningerPrimeFiniteStageQuotientReduction_continuous p s)

/-- Finite packet function in complex packet Haar `L²`. -/
def deningerPrimeFiniteStageComplexHaarL2 (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    DeningerPrimePacketComplexHaarL2 p :=
  ContinuousMap.toLp 2 (deningerPrimePacketHaarMeasure p) ℂ
    (deningerPrimeFiniteStageComplexPullback p s F)

/-- Canonical first suspension mode of a finite packet function. -/
def deningerPrimeFiniteStageFirstSuspensionMode (p : Nat.Primes)
    (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    DeningerPrimeSuspensionHaarL2 p :=
  deningerPrimeSuspensionFirstMode p
    (deningerPrimeFiniteStageComplexHaarL2 p s F)

/-- A nonzero finite packet function gives a nonzero first suspension mode. -/
theorem deningerPrimeFiniteStageFirstSuspensionMode_ne_zero
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) :
    deningerPrimeFiniteStageFirstSuspensionMode p s F ≠ 0 := by
  intro hmode
  have hLp : deningerPrimeFiniteStageComplexHaarL2 p s F = 0 := by
    apply deningerPrimeSuspensionFirstMode_injective p
    rw [map_zero]
    exact hmode
  have hzero : deningerPrimeFiniteStageComplexPullback p s F = 0 := by
    apply ContinuousMap.toLp_injective
      (𝕜 := ℂ) (p := 2) (E := ℂ)
      (deningerPrimePacketHaarMeasure p)
    rw [map_zero]
    exact hLp
  apply hF
  funext q
  obtain ⟨x, hx⟩ :=
    deningerPrimeFiniteStageQuotientReduction_surjective p s q
  have hpoint := DFunLike.congr_fun hzero x
  change F (deningerPrimeFiniteStageQuotientReduction p s x) = 0 at hpoint
  simpa [hx] using hpoint

/-- A nonzero finite packet function has strictly positive first-mode Tate energy. -/
theorem deningerPrimeFiniteStageFirstSuspensionMode_energy_pos
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    {F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ}
    (hF : F ≠ 0) :
    0 < deningerPrimeSuspensionFirstModeGreenEnergy p
      (deningerPrimeFiniteStageComplexHaarL2 p s F) := by
  apply deningerPrimeSuspensionFirstModeGreenEnergy_pos
  intro hzero
  apply deningerPrimeFiniteStageFirstSuspensionMode_ne_zero p s hF
  change deningerPrimeSuspensionFirstMode p
      (deningerPrimeFiniteStageComplexHaarL2 p s F) = 0
  rw [hzero, map_zero]

/-- **Actual Wrat first-mode admission.**  Every nonzero finite packet function has both a fixed
rational-Witt witness and a nonzero positive-energy first suspension mode on the literal prime
fibre. -/
theorem deningerPrimeComplexifiedRationalWitt_exists_nonzero_firstSuspensionMode
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ)
    (hF : F ≠ 0) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      (∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u)) ∧
      deningerPrimeFiniteStageFirstSuspensionMode p s F ≠ 0 ∧
      0 < deningerPrimeSuspensionFirstModeGreenEnergy p
        (deningerPrimeFiniteStageComplexHaarL2 p s F) := by
  obtain ⟨w, hw, heval⟩ :=
    deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective p s F
  exact ⟨w, hw, heval,
    deningerPrimeFiniteStageFirstSuspensionMode_ne_zero p s hF,
    deningerPrimeFiniteStageFirstSuspensionMode_energy_pos p s hF⟩

end

end RHTower
