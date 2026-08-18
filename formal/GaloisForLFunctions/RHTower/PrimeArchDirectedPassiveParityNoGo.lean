import GaloisForLFunctions.HTGeometry.PrimeLogKMSRealization
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesReflectedCompactCarrier
import GaloisForLFunctions.RHTower.GammaSewnApertureExteriorHeight
import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource

/-!
# Directed passive prime--Gamma parity no-go

Two canonical source-native directed passive families fail before any RH sign transfer.  At the
centered point `I / 4`, reflection oddness forces the completed prime--Gamma response to have zero
real part.  The directed prime-log KMS limit has strictly negative real part, while the directed
Gamma-sewn Stokes limit has strictly positive real part.  Neither family can converge pointwise to
the completed response.

The positive survivor is exact: source-native finite passivity is unconditional, but a candidate
for completed comparison must impose the missing reflected/Hermitian completion before taking its
thermodynamic limit.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A centered upper-half-plane point fixed by the Xi negative-conjugation involution. -/
def primeArchDirectedPassiveNoGoPoint : ℂ := Complex.I / 4

private theorem primeArchDirectedPassiveNoGoPoint_star :
    (starRingEnd ℂ) primeArchDirectedPassiveNoGoPoint = -Complex.I / 4 := by
  have hfour : (starRingEnd ℂ) (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  rw [primeArchDirectedPassiveNoGoPoint, map_div₀, hfour]
  simp [Complex.conj_I]

private theorem primeArchDirectedPassiveNoGoPoint_domain :
    CCMContinuedCauchyDomain primeArchDirectedPassiveNoGoPoint := by
  have hzetaQuarter : riemannZeta (((1 / 4 : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_real_strip_ne_zero (σ := 1 / 4) (by norm_num) (by norm_num)
  have hzetaThreeQuarter : riemannZeta (((3 / 4 : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_real_strip_ne_zero (σ := 3 / 4) (by norm_num) (by norm_num)
  have hquarter : (1 / 2 : ℂ) + primeArchDirectedPassiveNoGoPoint * Complex.I =
      ((1 / 4 : ℝ) : ℂ) := by
    rw [primeArchDirectedPassiveNoGoPoint]
    apply Complex.ext <;> norm_num
  have hthreeQuarter :
      (1 / 2 : ℂ) + (starRingEnd ℂ) primeArchDirectedPassiveNoGoPoint * Complex.I =
        ((3 / 4 : ℝ) : ℂ) := by
    rw [primeArchDirectedPassiveNoGoPoint_star]
    apply Complex.ext <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hquarter]
    norm_num
  · rw [hquarter]
    norm_num
  · rw [hquarter]
    exact hzetaQuarter
  · rw [hthreeQuarter]
    norm_num
  · rw [hthreeQuarter]
    norm_num
  · rw [hthreeQuarter]
    exact hzetaThreeQuarter

private theorem continuedPrimeArchSourceRelativeTrace_noGoPoint_re_eq_zero :
    (continuedPrimeArchSourceRelativeTrace primeArchDirectedPassiveNoGoPoint).re = 0 := by
  have hreflect := continuedPrimeArchSourceRelativeTrace_negConj
    primeArchDirectedPassiveNoGoPoint_domain
  have hfixed : xiCenteredNegConj primeArchDirectedPassiveNoGoPoint =
      primeArchDirectedPassiveNoGoPoint := by
    unfold xiCenteredNegConj
    rw [primeArchDirectedPassiveNoGoPoint_star]
    rw [primeArchDirectedPassiveNoGoPoint]
    ring
  rw [hfixed] at hreflect
  have hre := congrArg Complex.re hreflect
  simp only [Complex.neg_re, Complex.conj_re] at hre
  linarith

private theorem primeLogHerglotz_zero_noGoPoint_re_pos :
    0 < (primeLogHerglotz (fun _ => 0) primeArchDirectedPassiveNoGoPoint).re := by
  have hz : 0 < primeArchDirectedPassiveNoGoPoint.im := by
    norm_num [primeArchDirectedPassiveNoGoPoint]
  have hweights : Summable fun p : Nat.Primes =>
      ‖(primeDyadicWeight (fun _ => 0) p : ℂ)‖ :=
    summable_norm_primeDyadicWeight (fun _ => 0) 0 (by intro p; simp)
  have hsum : Summable fun p : Nat.Primes =>
      (primeDyadicWeight (fun _ => 0) p : ℂ) *
        ((primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint)⁻¹ :=
    summable_discreteHerglotz_term primeLogSupport
      (primeDyadicWeight (fun _ => 0)) primeArchDirectedPassiveNoGoPoint hz hweights
  have hatom : ∀ p : Nat.Primes,
      0 < ((primeDyadicWeight (fun _ => 0) p : ℂ) *
        ((primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint)⁻¹).re := by
    intro p
    have hlog : 0 < primeLogSupport p := by
      unfold primeLogSupport
      exact Real.log_pos (by exact_mod_cast p.prop.two_le)
    have hne : (primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      norm_num [primeArchDirectedPassiveNoGoPoint] at him
    have hden : 0 < Complex.normSq
        ((primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint) :=
      Complex.normSq_pos.mpr hne
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [Complex.inv_re]
    have hre : ((primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint).re =
        primeLogSupport p := by
      simp [primeArchDirectedPassiveNoGoPoint]
    rw [hre]
    exact mul_pos (primeDyadicWeight_pos (fun _ => 0) p) (div_pos hlog hden)
  rw [primeLogHerglotz, discreteHerglotz, Complex.re_tsum hsum]
  have hsumRe : Summable fun p : Nat.Primes =>
      ((primeDyadicWeight (fun _ => 0) p : ℂ) *
        ((primeLogSupport p : ℂ) - primeArchDirectedPassiveNoGoPoint)⁻¹).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  exact hsumRe.tsum_pos (fun p => (hatom p).le)
    ⟨2, Nat.prime_two⟩ (hatom ⟨2, Nat.prime_two⟩)

private theorem neg_primeLogHerglotz_zero_noGoPoint_re_neg :
    (-primeLogHerglotz (fun _ => 0) primeArchDirectedPassiveNoGoPoint).re < 0 := by
  have h := primeLogHerglotz_zero_noGoPoint_re_pos
  simp only [Complex.neg_re]
  linarith

/-- Canonical directed prime-log finite KMS responses cannot converge to the completed
prime--Gamma source, already at the fixed centered point `I / 4`. -/
theorem not_tendsto_directedPrimeLogKMSResponse_continuedPrimeArch_noGoPoint :
    ¬ Tendsto
      (fun P : Finset Nat.Primes =>
        HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity 1
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteAmplitude P (fun _ => 0) 1))
          (primeLogKMSFiniteEnergy P) primeArchDirectedPassiveNoGoPoint)
      atTop
      (nhds (continuedPrimeArchSourceRelativeTrace primeArchDirectedPassiveNoGoPoint)) := by
  intro hsource
  have hprime := finiteKMSWightmanResponse_tendsto_primeLogHerglotz
    (fun _ => 0) 0 (by intro p; simp) 1 primeArchDirectedPassiveNoGoPoint
    (by norm_num [primeArchDirectedPassiveNoGoPoint])
  have hresponse : Tendsto
      (fun P : Finset Nat.Primes =>
        HTGeometry.finiteTransitionPassiveResponse
          (HTGeometry.finiteKMSWightmanTransitionIntensity 1
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteAmplitude P (fun _ => 0) 1))
          (primeLogKMSFiniteEnergy P) primeArchDirectedPassiveNoGoPoint)
      atTop
      (nhds (-primeLogHerglotz (fun _ => 0) primeArchDirectedPassiveNoGoPoint)) := by
    simpa only [neg_neg] using hprime.neg
  have heq := tendsto_nhds_unique hresponse hsource
  have hre := congrArg Complex.re heq
  rw [continuedPrimeArchSourceRelativeTrace_noGoPoint_re_eq_zero] at hre
  have hneg := neg_primeLogHerglotz_zero_noGoPoint_re_neg
  linarith

private theorem gammaSewnMobiusApertureStokesDualFeatureCoefficient_half_pos
    (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk := by
  unfold gammaSewnMobiusApertureStokesDualFeatureCoefficient
  exact div_pos
    (gammaSewnMobiusContinuousApertureFeature_pos (by norm_num) pk.1 pk.2)
    (by positivity)

private theorem gammaSewnMobiusApertureStokesOneSubtractedAtom_half_noGoPoint_re_pos
    (pk : Nat.Primes × ℕ) :
    0 < (gammaSewnMobiusApertureStokesOneSubtractedAtom
      (1 / 2) primeArchDirectedPassiveNoGoPoint pk).re := by
  let b := gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk
  let g := gammaSewnMobiusApertureStokesGap (1 / 2) pk
  have hb : 0 < b :=
    gammaSewnMobiusApertureStokesDualFeatureCoefficient_half_pos pk
  have hg : 0 < g := gammaSewnMobiusApertureStokesGap_pos (by norm_num) pk
  have hz : 0 < primeArchDirectedPassiveNoGoPoint.im := by
    norm_num [primeArchDirectedPassiveNoGoPoint]
  have hden : 0 < Complex.normSq
      (primeArchDirectedPassiveNoGoPoint - (g : ℂ)) :=
    HTGeometry.normSq_sub_ofReal_pos hz
  have hnumRe : ((b : ℂ) * primeArchDirectedPassiveNoGoPoint).re = 0 := by
    simp [primeArchDirectedPassiveNoGoPoint]
  have hnumIm : ((b : ℂ) * primeArchDirectedPassiveNoGoPoint).im = b / 4 := by
    simp [primeArchDirectedPassiveNoGoPoint]
    ring
  have hdenRe : (primeArchDirectedPassiveNoGoPoint - (g : ℂ)).re = -g := by
    simp [primeArchDirectedPassiveNoGoPoint]
  have hdenIm : (primeArchDirectedPassiveNoGoPoint - (g : ℂ)).im = 1 / 4 := by
    simp [primeArchDirectedPassiveNoGoPoint]
  unfold gammaSewnMobiusApertureStokesOneSubtractedAtom
  change 0 < (((b : ℂ) * primeArchDirectedPassiveNoGoPoint /
    (primeArchDirectedPassiveNoGoPoint - (g : ℂ))).re)
  rw [Complex.div_re, hnumRe, hnumIm, hdenRe, hdenIm]
  simp only [zero_mul, zero_div, zero_add]
  exact div_pos (mul_pos (div_pos hb (by norm_num)) (by norm_num)) hden

private theorem gammaSewnMobiusApertureStokesOneSubtractedResponse_half_noGoPoint_re_pos :
    0 < (gammaSewnMobiusApertureStokesOneSubtractedResponse
      (1 / 2) primeArchDirectedPassiveNoGoPoint).re := by
  have hz : 0 < primeArchDirectedPassiveNoGoPoint.im := by
    norm_num [primeArchDirectedPassiveNoGoPoint]
  have hsum := summable_gammaSewnMobiusApertureStokesOneSubtractedAtom
    (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hz
  rw [gammaSewnMobiusApertureStokesOneSubtractedResponse, Complex.re_tsum hsum]
  have hsumRe := (Complex.hasSum_re hsum.hasSum).summable
  exact hsumRe.tsum_pos
    (fun pk =>
      (gammaSewnMobiusApertureStokesOneSubtractedAtom_half_noGoPoint_re_pos pk).le)
    ⟨⟨2, Nat.prime_two⟩, 0⟩
    (gammaSewnMobiusApertureStokesOneSubtractedAtom_half_noGoPoint_re_pos
      ⟨⟨2, Nat.prime_two⟩, 0⟩)

/-- Every canonical finite subcritical Stokes response is passive at the no-go point. -/
theorem gammaSewnMobiusApertureStokesFiniteResponse_half_noGoPoint_im_nonpos
    (F : Finset (Nat.Primes × ℕ)) :
    (∑ pk ∈ F, gammaSewnMobiusApertureStokesOneSubtractedAtom
      (1 / 2) primeArchDirectedPassiveNoGoPoint pk).im ≤ 0 := by
  rw [Complex.im_sum]
  exact Finset.sum_nonpos fun pk _ =>
    gammaSewnMobiusApertureStokesOneSubtractedAtom_im_nonpos
      (s := (1 / 2 : ℝ)) (by norm_num)
      (z := primeArchDirectedPassiveNoGoPoint)
      (by norm_num [primeArchDirectedPassiveNoGoPoint]) pk

/-- Source-native subcritical Stokes finite responses cannot converge to the completed
prime--Gamma source, already at `I / 4`. -/
theorem not_tendsto_gammaSewnMobiusApertureStokesFiniteResponse_continuedPrimeArch_noGoPoint :
    ¬ Tendsto
      (fun F : Finset (Nat.Primes × ℕ) =>
        ∑ pk ∈ F, gammaSewnMobiusApertureStokesOneSubtractedAtom
          (1 / 2) primeArchDirectedPassiveNoGoPoint pk)
      atTop
      (nhds (continuedPrimeArchSourceRelativeTrace primeArchDirectedPassiveNoGoPoint)) := by
  intro hsource
  have hz : 0 < primeArchDirectedPassiveNoGoPoint.im := by
    norm_num [primeArchDirectedPassiveNoGoPoint]
  have hsum := summable_gammaSewnMobiusApertureStokesOneSubtractedAtom
    (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hz
  have hresponse : HasSum
      (gammaSewnMobiusApertureStokesOneSubtractedAtom
        (1 / 2) primeArchDirectedPassiveNoGoPoint)
      (gammaSewnMobiusApertureStokesOneSubtractedResponse
        (1 / 2) primeArchDirectedPassiveNoGoPoint) := by
    simpa only [gammaSewnMobiusApertureStokesOneSubtractedResponse] using hsum.hasSum
  have hresponse' : Tendsto
      (fun F : Finset (Nat.Primes × ℕ) =>
        ∑ pk ∈ F, gammaSewnMobiusApertureStokesOneSubtractedAtom
          (1 / 2) primeArchDirectedPassiveNoGoPoint pk)
      atTop
      (nhds (gammaSewnMobiusApertureStokesOneSubtractedResponse
        (1 / 2) primeArchDirectedPassiveNoGoPoint)) := by
    exact hresponse
  have heq := tendsto_nhds_unique hresponse' hsource
  have hre := congrArg Complex.re heq
  rw [continuedPrimeArchSourceRelativeTrace_noGoPoint_re_eq_zero] at hre
  have hpos :=
    gammaSewnMobiusApertureStokesOneSubtractedResponse_half_noGoPoint_re_pos
  linarith

/-- Canonical finite reflected source response at the fixed subcritical aperture. -/
def gammaSewnMobiusApertureStokesReflectedFiniteResponse
    (F : Finset (Nat.Primes × ℕ)) (z : ℂ) : ℂ :=
  ∑ pk ∈ F, gammaSewnMobiusApertureStokesReflectedAtom (1 / 2) z pk

/-- Every canonical finite reflected source response is passive at the centered no-go point. -/
theorem gammaSewnMobiusApertureStokesReflectedFiniteResponse_noGoPoint_im_nonpos
    (F : Finset (Nat.Primes × ℕ)) :
    (gammaSewnMobiusApertureStokesReflectedFiniteResponse
      F primeArchDirectedPassiveNoGoPoint).im ≤ 0 := by
  rw [gammaSewnMobiusApertureStokesReflectedFiniteResponse, Complex.im_sum]
  exact Finset.sum_nonpos fun pk _ =>
    gammaSewnMobiusApertureStokesReflectedAtom_im_nonpos
      (s := (1 / 2 : ℝ)) (by norm_num)
      (z := primeArchDirectedPassiveNoGoPoint)
      (by norm_num [primeArchDirectedPassiveNoGoPoint]) pk

/-- Reflected finite stages preserve the centered oddness absent from directed stages. -/
theorem gammaSewnMobiusApertureStokesReflectedFiniteResponse_neg
    (F : Finset (Nat.Primes × ℕ)) (z : ℂ) :
    gammaSewnMobiusApertureStokesReflectedFiniteResponse F (-z) =
      -gammaSewnMobiusApertureStokesReflectedFiniteResponse F z := by
  rw [gammaSewnMobiusApertureStokesReflectedFiniteResponse,
    gammaSewnMobiusApertureStokesReflectedFiniteResponse]
  calc
    (∑ pk ∈ F, gammaSewnMobiusApertureStokesReflectedAtom (1 / 2) (-z) pk) =
        ∑ pk ∈ F, -gammaSewnMobiusApertureStokesReflectedAtom (1 / 2) z pk := by
      exact Finset.sum_congr rfl fun pk _ =>
        gammaSewnMobiusApertureStokesReflectedAtom_neg (1 / 2) z pk
    _ = -(∑ pk ∈ F,
        gammaSewnMobiusApertureStokesReflectedAtom (1 / 2) z pk) := by
      rw [Finset.sum_neg_distrib]

/-- Canonical reflected finite responses converge pointwise to the source-native reflected
response at the centered no-go point.  No completed-source comparison is asserted. -/
theorem gammaSewnMobiusApertureStokesReflectedFiniteResponse_tendsto_noGoPoint :
    Tendsto
      (fun F : Finset (Nat.Primes × ℕ) =>
        gammaSewnMobiusApertureStokesReflectedFiniteResponse
          F primeArchDirectedPassiveNoGoPoint)
      atTop
      (nhds (gammaSewnMobiusApertureStokesReflectedResponse
        (1 / 2) primeArchDirectedPassiveNoGoPoint)) := by
  have hsum := summable_gammaSewnMobiusApertureStokesReflectedAtom
    (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (z := primeArchDirectedPassiveNoGoPoint)
    (by norm_num [primeArchDirectedPassiveNoGoPoint])
  have hresponse : HasSum
      (gammaSewnMobiusApertureStokesReflectedAtom
        (1 / 2) primeArchDirectedPassiveNoGoPoint)
      (gammaSewnMobiusApertureStokesReflectedResponse
        (1 / 2) primeArchDirectedPassiveNoGoPoint) := by
    simpa only [gammaSewnMobiusApertureStokesReflectedResponse] using hsum.hasSum
  exact hresponse

end

end RHTower
