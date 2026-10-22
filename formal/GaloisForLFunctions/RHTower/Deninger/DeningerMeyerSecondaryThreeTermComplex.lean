import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerSecondaryPoissonRegulator
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittPoissonBoundarySamplingObstruction
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermCohomology

/-!
# The Meyer--Poisson secondary three-term complex

This file constructs a source-derived three-term complex on the separated
Meyer/Rational-Witt sector.  Its first differential is the literal pair of
physical and Fourier Meyer sums.  Its second differential is the maximal
all-prime secondary Poisson regulator.  Poisson reflection proves `d₁ d₀ = 0`.

The construction is not an assertion that this complex is the full
sheaf-theoretic arithmetic complex.  In particular, equality of its
degree-one cycles and boundaries remains a separate global problem.
-/

namespace RHTower

open scoped FourierTransform SchwartzMap

noncomputable section

/-- The physical Meyer sum vanishes at the excluded zero radius. -/
lemma deningerMeyerSum_zero (f : DeningerMeyerCap) :
    deningerMeyerSum f 0 = 0 := by
  have hf0 := ((deningerMeyerCap_mem_iff f).mp f.property).2.1
  rw [deningerMeyerSum]
  simp [hf0]

/-- The Fourier Meyer sum also vanishes at the excluded zero radius. -/
lemma deningerMeyerFourierSum_zero (f : DeningerMeyerCap) :
    deningerMeyerSum
      (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) 0 = 0 := by
  rw [deningerMeyerSum]
  simp

/-- The literal physical/Fourier Meyer--Poisson boundary, bundled linearly. -/
def deningerMeyerPoissonBoundaryPairLM :
    DeningerMeyerCap →ₗ[ℂ] DeningerMeyerRadialCochainPair where
  toFun := deningerMeyerPoissonBoundaryPair
  map_add' f g := by
    apply Prod.ext
    · funext x
      change deningerMeyerSum (f + g : DeningerMeyerCap) x =
        deningerMeyerSum f x + deningerMeyerSum g x
      by_cases hx : x = 0
      · subst x
        rw [deningerMeyerSum_zero, deningerMeyerSum_zero,
          deningerMeyerSum_zero, zero_add]
      · exact map_add
          ((deningerMeyerPositiveSumLM x hx).comp
            DeningerMeyerCap.subtype) f g
    · funext x
      change deningerMeyerSum
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
            (f + g : DeningerMeyerCap)) x =
        deningerMeyerSum
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) x +
          deningerMeyerSum
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) g) x
      by_cases hx : x = 0
      · subst x
        rw [deningerMeyerFourierSum_zero,
          deningerMeyerFourierSum_zero, deningerMeyerFourierSum_zero,
          zero_add]
      · change deningerMeyerPositiveSumLM x hx
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
              (f + g : DeningerMeyerCap)) =
          deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) +
            deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) g)
        change deningerMeyerPositiveSumLM x hx
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
              ((f : SchwartzMap ℝ ℂ) + (g : SchwartzMap ℝ ℂ))) =
          deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) +
            deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) g)
        rw [map_add, map_add]
  map_smul' c f := by
    apply Prod.ext
    · funext x
      change deningerMeyerSum (c • f : DeningerMeyerCap) x =
        c • deningerMeyerSum f x
      by_cases hx : x = 0
      · subst x
        rw [deningerMeyerSum_zero, deningerMeyerSum_zero, smul_zero]
      · exact map_smul
          ((deningerMeyerPositiveSumLM x hx).comp
            DeningerMeyerCap.subtype) c f
    · funext x
      change deningerMeyerSum
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
            (c • f : DeningerMeyerCap)) x =
        c • deningerMeyerSum
          (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f) x
      by_cases hx : x = 0
      · subst x
        rw [deningerMeyerFourierSum_zero,
          deningerMeyerFourierSum_zero, smul_zero]
      · change deningerMeyerPositiveSumLM x hx
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
              (c • f : DeningerMeyerCap)) =
          c • deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
        change deningerMeyerPositiveSumLM x hx
            (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ)
              (c • (f : SchwartzMap ℝ ℂ))) =
          c • deningerMeyerPositiveSumLM x hx
              (FourierTransform.fourierCLE ℂ (SchwartzMap ℝ ℂ) f)
        rw [map_smul, map_smul]

@[simp]
lemma deningerMeyerPoissonBoundaryPairLM_apply (f : DeningerMeyerCap) :
    deningerMeyerPoissonBoundaryPairLM f =
      deningerMeyerPoissonBoundaryPair f :=
  rfl

variable (packet : ∀ p, DeningerPrimePacketComplexHaarL2 p)

/-- First differential: the literal Meyer boundary with its proved Bessel certificate. -/
def deningerMeyerPoissonBoundaryLM :
    DeningerMeyerCap →ₗ[ℂ]
      DeningerMeyerSecondaryBesselDomain packet :=
  deningerMeyerPoissonBoundaryPairLM.codRestrict
    (DeningerMeyerSecondaryBesselDomain packet)
    (fun f =>
      (deningerMeyerPoissonBoundaryInSecondaryBesselDomain
        packet f).property)

@[simp]
lemma deningerMeyerPoissonBoundaryLM_coe (f : DeningerMeyerCap) :
    (deningerMeyerPoissonBoundaryLM packet f :
      DeningerMeyerRadialCochainPair) =
      deningerMeyerPoissonBoundaryPair f :=
  rfl

/--
The separated Meyer--Poisson secondary complex
`MeyerCap → Bessel radial pairs → first-suspension Hilbert sum`.
-/
def deningerMeyerSecondaryThreeTermComplex :
    DeningerArithmeticThreeTermComplex ℂ
      DeningerMeyerCap
      (DeningerMeyerSecondaryBesselDomain packet)
      DeningerPrimeFirstSuspensionHilbertSum where
  d0 := deningerMeyerPoissonBoundaryLM packet
  d1 := deningerMeyerSecondaryMaximalRestriction packet
  d1_comp_d0 := by
    apply LinearMap.ext
    intro f
    exact deningerMeyerPoissonBoundary_secondaryRestriction_zero packet f

/-- Exact classification of degree-one cycles by reflected prime relations. -/
theorem deningerMeyerSecondaryThreeTerm_cycles1_iff
    (h : DeningerMeyerSecondaryBesselDomain packet) :
    h ∈ (deningerMeyerSecondaryThreeTermComplex packet).cycles1 ↔
      ∀ p : Nat.Primes,
        (h : DeningerMeyerRadialCochainPair).1 (p : ℝ) =
            (((p : ℝ)⁻¹ : ℝ) : ℂ) *
              (h : DeningerMeyerRadialCochainPair).2
                ((p : ℝ)⁻¹) ∨
          packet p = 0 := by
  change deningerMeyerSecondaryMaximalRestriction packet h = 0 ↔ _
  exact deningerMeyerSecondaryMaximalRestriction_eq_zero_iff packet h

/-- The first differential is genuinely nonzero, witnessed at every prime by the probe. -/
theorem deningerMeyerPrimeBoundaryProbe_d0_ne_zero :
    (deningerMeyerSecondaryThreeTermComplex packet).d0
        DeningerMeyerPrimeBoundaryCap ≠
      0 := by
  intro hzero
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hp := congrArg
    (fun h : DeningerMeyerSecondaryBesselDomain packet =>
      (h : DeningerMeyerRadialCochainPair).1 (p2 : ℝ))
    hzero
  change deningerMeyerSum deningerMeyerPrimeBoundaryProbe
      (p2 : ℝ) = 0 at hp
  exact deningerMeyerPrimeBoundaryProbe_meyerSum_ne_zero p2 hp

/-- The nonzero probe boundary is nevertheless annihilated by the second differential. -/
theorem deningerMeyerPrimeBoundaryProbe_d1_d0_zero :
    (deningerMeyerSecondaryThreeTermComplex packet).d1
      ((deningerMeyerSecondaryThreeTermComplex packet).d0
        DeningerMeyerPrimeBoundaryCap) =
      0 :=
  LinearMap.congr_fun
    (deningerMeyerSecondaryThreeTermComplex packet).d1_comp_d0
    DeningerMeyerPrimeBoundaryCap

end

end RHTower
