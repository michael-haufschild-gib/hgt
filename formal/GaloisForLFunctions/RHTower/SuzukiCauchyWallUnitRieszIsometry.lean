import GaloisForLFunctions.RHTower.SuzukiWallFieldAntidiagonalGramLift
import GaloisForLFunctions.RHTower.CCMUnitRieszCompletedCoherentBarycenter
import GaloisForLFunctions.HTGeometry.CauchyKernelStripDecay
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener

/-!
# Cauchy-height isometry between Suzuki wall phases and the unit-Riesz coherent frame

This module identifies the normalized literal Suzuki wall phase with the unit-exponential
coherent kernel after Cauchy-height averaging.  It also evaluates the entire polar continuum as
one rational counterterm, so prime and polar channels can be recentered before taking a scalar
trace or a cofinal limit.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- Half-log wall character at logarithmic source coordinate `x`. -/
def suzukiCauchyWallPhase (x t : ℝ) : ℂ :=
  suzukiOscillatoryKernel (t : ℂ) (x / 2)

theorem suzukiCauchyWallPhase_eq
    (x t : ℝ) :
    suzukiCauchyWallPhase x t =
      Complex.exp ((((x * t / 2 : ℝ) : ℂ) * I)) := by
  rw [suzukiCauchyWallPhase, suzukiOscillatoryKernel]
  congr 1
  push_cast
  ring

/-- Two wall phases multiply to the Fourier character of their half-log difference. -/
theorem suzukiCauchyWallPhase_mul_star
    (x y t : ℝ) :
    suzukiCauchyWallPhase x t * star (suzukiCauchyWallPhase y t) =
      GaloisForLFunctions.HTGeometry.cauchyFourierWeight ((y - x) / 2) t := by
  rw [suzukiCauchyWallPhase_eq, suzukiCauchyWallPhase_eq,
    GaloisForLFunctions.HTGeometry.cauchyFourierWeight]
  change Complex.exp ((((x * t / 2 : ℝ) : ℂ) * I)) *
      conj (Complex.exp ((((y * t / 2 : ℝ) : ℂ) * I))) =
    Complex.exp ((((-(((y - x) / 2) * t) : ℝ) : ℂ) * I))
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Cauchy-height inner product of two normalized Suzuki wall phases. -/
def suzukiCauchyWallPhaseInner (x y : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∫ t : ℝ,
      suzukiCauchyWallPhase x t * star (suzukiCauchyWallPhase y t) *
        (((1 + t ^ (2 : ℕ) : ℝ) : ℂ))⁻¹

/-- Cauchy height converts wall phase difference into the exponential coherent kernel. -/
theorem suzukiCauchyWallPhaseInner_eq
    (x y : ℝ) :
    suzukiCauchyWallPhaseInner x y =
      (Real.exp (-|x - y| / 2) : ℂ) := by
  have hmass :
      (∫ t : ℝ,
          suzukiCauchyWallPhase x t * star (suzukiCauchyWallPhase y t) *
            (((1 + t ^ (2 : ℕ) : ℝ) : ℂ))⁻¹) =
        GaloisForLFunctions.HTGeometry.massPairing
          (GaloisForLFunctions.HTGeometry.cauchyFourierWeight ((y - x) / 2))
          0 1 := by
    rw [GaloisForLFunctions.HTGeometry.massPairing]
    apply integral_congr_ae
    filter_upwards with t
    rw [suzukiCauchyWallPhase_mul_star]
    norm_num
  rw [suzukiCauchyWallPhaseInner, hmass,
    GaloisForLFunctions.HTGeometry.massPairing_cauchyFourierWeight_zero
      (by norm_num : (0 : ℝ) < 1)]
  norm_num
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_sub_comm]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Cauchy wall Gram after anchoring both source coordinates at `a`. -/
def suzukiCauchyAnchoredWallGram (a x y : ℝ) : ℂ :=
  suzukiCauchyWallPhaseInner a a -
    suzukiCauchyWallPhaseInner a y -
    suzukiCauchyWallPhaseInner x a +
    suzukiCauchyWallPhaseInner x y

/-- **Wall/coherent isometry.**  Anchored Cauchy wall Gram is exactly the unit-exponential
coherent increment Gram. -/
theorem suzukiCauchyAnchoredWallGram_eq_unitExponentialCoherentIncrementGram
    (a x y : ℝ) :
    suzukiCauchyAnchoredWallGram a x y =
      (unitExponentialCoherentIncrementGram a x y : ℂ) := by
  rw [suzukiCauchyAnchoredWallGram,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    unitExponentialCoherentIncrementGram_eq]
  simp only [sub_self, abs_zero, neg_zero]
  push_cast
  norm_num

/-- Positive polar continuum's spectral counterterm. -/
def suzukiCauchyWallPolarCounterterm (t : ℝ) : ℂ :=
  (I * (t / 2 : ℂ)) / (1 + I * (t / 2 : ℂ))

/-- The full polar continuum is exactly one rational wall counterterm. -/
theorem integral_suzukiCauchyWallPolarCounterterm
    (t : ℝ) :
    (∫ p in Ioi (0 : ℝ),
        (Real.exp (-p) : ℂ) *
          (1 - suzukiCauchyWallPhase (-p) t)) =
      suzukiCauchyWallPolarCounterterm t := by
  let b : ℂ := 1 + I * (t / 2 : ℂ)
  have hb : 0 < b.re := by simp [b]
  have hfirst :
      (∫ p in Ioi (0 : ℝ), (Real.exp (-p) : ℂ)) = 1 := by
    simpa using integral_Ioi_cexp_neg_mul (b := (1 : ℂ)) (by norm_num)
  have hsecond :
      (∫ p in Ioi (0 : ℝ),
          (Real.exp (-p) : ℂ) * suzukiCauchyWallPhase (-p) t) = b⁻¹ := by
    rw [← integral_Ioi_cexp_neg_mul hb]
    apply integral_congr_ae
    filter_upwards with p
    rw [suzukiCauchyWallPhase_eq]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp only [b]
    push_cast
    ring
  have hfirstInt : IntegrableOn (fun p : ℝ => (Real.exp (-p) : ℂ)) (Ioi 0) := by
    simpa using integrableOn_Ioi_cexp_neg_mul (b := (1 : ℂ)) (by norm_num)
  have hsecondInt : IntegrableOn
      (fun p : ℝ => (Real.exp (-p) : ℂ) * suzukiCauchyWallPhase (-p) t)
      (Ioi 0) := by
    have h := integrableOn_Ioi_cexp_neg_mul hb
    refine h.congr_fun ?_ measurableSet_Ioi
    intro p hp
    change Complex.exp (-(b * (p : ℂ))) =
      (Real.exp (-p) : ℂ) * suzukiCauchyWallPhase (-p) t
    rw [suzukiCauchyWallPhase_eq]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp only [b]
    push_cast
    ring
  calc
    (∫ p in Ioi (0 : ℝ),
        (Real.exp (-p) : ℂ) * (1 - suzukiCauchyWallPhase (-p) t)) =
      (∫ p in Ioi (0 : ℝ),
          (Real.exp (-p) : ℂ) -
            (Real.exp (-p) : ℂ) * suzukiCauchyWallPhase (-p) t) := by
        apply integral_congr_ae
        filter_upwards with p
        ring
    _ = (∫ p in Ioi (0 : ℝ), (Real.exp (-p) : ℂ)) -
        ∫ p in Ioi (0 : ℝ),
          (Real.exp (-p) : ℂ) * suzukiCauchyWallPhase (-p) t :=
      integral_sub hfirstInt hsecondInt
    _ = suzukiCauchyWallPolarCounterterm t := by
      rw [hfirst, hsecond, suzukiCauchyWallPolarCounterterm]
      have hbne : b ≠ 0 := by
        intro hz
        rw [hz] at hb
        simp at hb
      change 1 - b⁻¹ = (I * (t / 2 : ℂ)) / b
      rw [div_eq_mul_inv]
      calc
        1 - b⁻¹ = b * b⁻¹ - b⁻¹ := by rw [mul_inv_cancel₀ hbne]
        _ = (b - 1) * b⁻¹ := by ring
        _ = I * (t / 2 : ℂ) * b⁻¹ := by
          congr 1
          dsimp only [b]
          ring

@[simp] theorem suzukiCauchyWallPolarCounterterm_zero :
    suzukiCauchyWallPolarCounterterm 0 = 0 := by
  simp [suzukiCauchyWallPolarCounterterm]

/-- Finite completed prime-minus-polar wall symbol at aperture `N`. -/
def suzukiUnitRieszCompletedCauchyWallSymbol (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 N,
      (ArithmeticFunction.vonMangoldt k / Real.sqrt N : ℂ) *
        (1 - suzukiCauchyWallPhase
          (-(Real.log N - Real.log k)) t) -
    (Real.sqrt N : ℂ) * suzukiCauchyWallPolarCounterterm t

/-- Prime and polar masses cancel at zero height before any scalar trace or cofinal limit. -/
@[simp] theorem suzukiUnitRieszCompletedCauchyWallSymbol_zero
    (N : ℕ) :
    suzukiUnitRieszCompletedCauchyWallSymbol N 0 = 0 := by
  simp [suzukiUnitRieszCompletedCauchyWallSymbol,
    suzukiCauchyWallPhase, suzukiOscillatoryKernel]

/-- A literal prime-power wall phase is the normalized Suzuki wall field. -/
theorem suzukiCauchyWallPhase_log_primePower_eq_normalizedWall
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCauchyWallPhase
        (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) t =
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ)⁻¹ *
        suzukiCriticalWallField t p e := by
  rw [suzukiCauchyWallPhase, suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiPrimePowerEntryWallAperture]
  have hne : (suzukiCriticalEntryWallBareAmplitude p e : ℂ) ≠ 0 := by
    exact_mod_cast (suzukiCriticalEntryWallBareAmplitude_pos p e).ne'
  field_simp

end

end GaloisForLFunctions.RHTower
