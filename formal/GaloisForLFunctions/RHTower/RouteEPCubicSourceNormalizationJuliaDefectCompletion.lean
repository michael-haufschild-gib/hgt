import GaloisForLFunctions.RHTower.RouteEPCubicSourceNormalizationKreinShorting
import GaloisForLFunctions.RHTower.RoutePPrimitiveHankelDepthSquareIntertwiner
import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Hilbert-amplitude contraction attached to two coefficient-faithful depth-square steps. -/
def routeEPCubicFourthDepthNormalizedContraction : ℝ := 1 / 8

/-- Canonical Julia defect of the literal fourth-depth contraction. -/
def routeEPCubicFourthDepthJuliaDefect : ℝ :=
  Real.sqrt (1 - routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ))

theorem routeEPCubicFourthDepthNormalizedContraction_sq :
    routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ) = 1 / 64 := by
  norm_num [routeEPCubicFourthDepthNormalizedContraction]

theorem routeEPCubicFourthDepthJuliaDefect_sq :
    routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = 63 / 64 := by
  rw [routeEPCubicFourthDepthJuliaDefect, Real.sq_sqrt]
  · rw [routeEPCubicFourthDepthNormalizedContraction_sq]
    norm_num
  · rw [routeEPCubicFourthDepthNormalizedContraction_sq]
    norm_num

theorem routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight :
    routeEPCubicFourthDepthJuliaDefect = Real.sqrt 63 / 8 := by
  have hleft : 0 ≤ routeEPCubicFourthDepthJuliaDefect := by
    exact Real.sqrt_nonneg _
  have hright : 0 ≤ Real.sqrt 63 / 8 := by positivity
  have hleftSq := routeEPCubicFourthDepthJuliaDefect_sq
  have hsqrt : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem routeEPCubicFourthDepthJulia_pythagoras :
    routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ) +
        routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = 1 := by
  rw [routeEPCubicFourthDepthNormalizedContraction_sq,
    routeEPCubicFourthDepthJuliaDefect_sq]
  norm_num

/-- Canonical oriented Julia rotation completing the fourth-depth contraction. -/
def routeEPCubicFourthDepthJuliaSourceTransportV (v : ℝ × ℝ) : ℝ × ℝ :=
  let c := routeEPCubicFourthDepthNormalizedContraction
  let d := routeEPCubicFourthDepthJuliaDefect
  (c * v.1 - d * v.2, d * v.1 + c * v.2)

theorem routeEPCubicFourthDepthJuliaSourceTransportV_normSq (v : ℝ × ℝ) :
    (routeEPCubicFourthDepthJuliaSourceTransportV v).1 ^ (2 : ℕ) +
        (routeEPCubicFourthDepthJuliaSourceTransportV v).2 ^ (2 : ℕ) =
      v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ) := by
  unfold routeEPCubicFourthDepthJuliaSourceTransportV
  dsimp only
  calc
    (routeEPCubicFourthDepthNormalizedContraction * v.1 -
          routeEPCubicFourthDepthJuliaDefect * v.2) ^ (2 : ℕ) +
        (routeEPCubicFourthDepthJuliaDefect * v.1 +
          routeEPCubicFourthDepthNormalizedContraction * v.2) ^ (2 : ℕ) =
      (routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ) +
        routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ)) * (v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ)) := by ring
    _ = v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ) := by
      rw [routeEPCubicFourthDepthJulia_pythagoras]
      ring

/-- The strict fourth-depth contraction cannot preserve the source axis without an environment. -/
theorem routeEPCubicFourthDepthNormalizedContraction_not_scalar_isometry :
    ¬ ∀ u : ℝ,
      (routeEPCubicFourthDepthNormalizedContraction * u) ^ (2 : ℕ) = u ^ (2 : ℕ) := by
  intro h
  have hunit := h 1
  norm_num [routeEPCubicFourthDepthNormalizedContraction] at hunit

theorem routeEPCubicFourthDepthJuliaSourceTransportV_unique_positive_lift
    {a b : ℝ}
    (hsecond : a ^ (2 : ℕ) + b ^ (2 : ℕ) = 1)
    (horth : routeEPCubicFourthDepthNormalizedContraction * a +
      routeEPCubicFourthDepthJuliaDefect * b = 0)
    (horient : 0 < routeEPCubicFourthDepthNormalizedContraction * b -
      routeEPCubicFourthDepthJuliaDefect * a) :
    a = -routeEPCubicFourthDepthJuliaDefect ∧
      b = routeEPCubicFourthDepthNormalizedContraction := by
  exact orientedPlaneIsometry_secondColumn_unique
    routeEPCubicFourthDepthJulia_pythagoras hsecond horth horient

/-- Two physical dyadic steps: quarter amplitude at fourfold scale. -/
def routePPrimitiveFourthDepthPhysicalDilation (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (1 / 4 : ℂ) * f (4 * r)

theorem integral_normSq_routePPrimitiveFourthDepthPhysicalDilation (f : ℝ → ℂ) :
    (∫ r : ℝ in Ioi 0, Complex.normSq
        (routePPrimitiveFourthDepthPhysicalDilation f r)) =
      (1 / 64 : ℝ) * ∫ r : ℝ in Ioi 0, Complex.normSq (f r) := by
  have houter := integral_normSq_half_dyadic_dilation
    (fun r : ℝ => (1 / 2 : ℂ) * f (2 * r))
  have hinner := integral_normSq_half_dyadic_dilation f
  calc
    (∫ r : ℝ in Ioi 0, Complex.normSq
        (routePPrimitiveFourthDepthPhysicalDilation f r)) =
      ∫ r : ℝ in Ioi 0, Complex.normSq
        ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * f (2 * (2 * r)))) := by
          apply integral_congr_ae
          filter_upwards with r
          congr 1
          unfold routePPrimitiveFourthDepthPhysicalDilation
          rw [show (4 : ℝ) * r = 2 * (2 * r) by ring]
          ring
    _ = (1 / 8 : ℝ) * ∫ r : ℝ in Ioi 0,
        Complex.normSq ((1 / 2 : ℂ) * f (2 * r)) := houter
    _ = (1 / 8 : ℝ) * ((1 / 8 : ℝ) *
        ∫ r : ℝ in Ioi 0, Complex.normSq (f r)) := by rw [hinner]
    _ = (1 / 64 : ℝ) * ∫ r : ℝ in Ioi 0, Complex.normSq (f r) := by ring

theorem routePPrimitiveFourthDepth_literalEnergy_eq_JuliaCompression
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
        routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) =
      routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ) *
        routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq,
    routeEPCubicFourthDepthNormalizedContraction_sq]
  ring

def routePPrimitiveFourthDepthParentAmplitude (pe : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt (routePPrimitiveBaseCauchyCubicWeight pe)

def routePPrimitiveFourthDepthJuliaChildAmplitude (pe : Nat.Primes × ℕ) : ℝ :=
  routeEPCubicFourthDepthNormalizedContraction *
    routePPrimitiveFourthDepthParentAmplitude pe

def routePPrimitiveFourthDepthJuliaDefectAmplitude (pe : Nat.Primes × ℕ) : ℝ :=
  routeEPCubicFourthDepthJuliaDefect * routePPrimitiveFourthDepthParentAmplitude pe

theorem routePPrimitiveFourthDepthParentAmplitude_sq (pe : Nat.Primes × ℕ) :
    routePPrimitiveFourthDepthParentAmplitude pe ^ (2 : ℕ) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveFourthDepthParentAmplitude, Real.sq_sqrt]
  exact (routePPrimitiveBaseCauchyCubicWeight_pos pe).le

theorem routePPrimitiveFourthDepthJuliaChildAmplitude_sq (pe : Nat.Primes × ℕ) :
    routePPrimitiveFourthDepthJuliaChildAmplitude pe ^ (2 : ℕ) =
      routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
        routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) := by
  rw [routePPrimitiveFourthDepthJuliaChildAmplitude, mul_pow,
    routePPrimitiveFourthDepthParentAmplitude_sq,
    routePPrimitiveFourthDepth_literalEnergy_eq_JuliaCompression]

theorem routePPrimitiveFourthDepthJuliaDefectAmplitude_sq (pe : Nat.Primes × ℕ) :
    routePPrimitiveFourthDepthJuliaDefectAmplitude pe ^ (2 : ℕ) =
      63 / 64 * routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveFourthDepthJuliaDefectAmplitude, mul_pow,
    routeEPCubicFourthDepthJuliaDefect_sq,
    routePPrimitiveFourthDepthParentAmplitude_sq]

theorem routePPrimitiveFourthDepthJulia_defectCompletesLiteralEnergy
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) +
        routePPrimitiveFourthDepthJuliaDefectAmplitude pe ^ (2 : ℕ) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq,
    routePPrimitiveFourthDepthJuliaDefectAmplitude_sq]
  ring

theorem routePPrimitiveFourthDepthJulia_parent_defect_pairing
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveFourthDepthParentAmplitude pe *
        routePPrimitiveFourthDepthJuliaDefectAmplitude pe =
      routeEPCubicFourthDepthQuantizedPolarCross
        (routePPrimitiveBaseCauchyCubicWeight pe) := by
  rw [routePPrimitiveFourthDepthJuliaDefectAmplitude,
    routeEPCubicFourthDepthQuantizedPolarCross,
    routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  calc
    routePPrimitiveFourthDepthParentAmplitude pe * ((Real.sqrt 63 / 8) *
          routePPrimitiveFourthDepthParentAmplitude pe) =
        (Real.sqrt 63 / 8) *
          routePPrimitiveFourthDepthParentAmplitude pe ^ (2 : ℕ) := by ring
    _ = (Real.sqrt 63 / 8) *
          routePPrimitiveBaseCauchyCubicWeight pe := by
      rw [routePPrimitiveFourthDepthParentAmplitude_sq]

theorem routePPrimitiveFourthDepthJuliaSourceTransportV_sourceAxis
    (pe : Nat.Primes × ℕ) :
    routeEPCubicFourthDepthJuliaSourceTransportV
        (routePPrimitiveFourthDepthParentAmplitude pe, 0) =
      (routePPrimitiveFourthDepthJuliaChildAmplitude pe,
        routePPrimitiveFourthDepthJuliaDefectAmplitude pe) := by
  simp [routeEPCubicFourthDepthJuliaSourceTransportV,
    routePPrimitiveFourthDepthJuliaChildAmplitude,
    routePPrimitiveFourthDepthJuliaDefectAmplitude]

theorem routePPrimitiveFourthDepth_JuliaKreinCompletion (pe : Nat.Primes × ℕ) :
    let w := routePPrimitiveBaseCauchyCubicWeight pe
    routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) +
        routePPrimitiveFourthDepthJuliaDefectAmplitude pe ^ (2 : ℕ) = w ∧
      routePPrimitiveFourthDepthParentAmplitude pe *
          routePPrimitiveFourthDepthJuliaDefectAmplitude pe =
        routeEPCubicFourthDepthQuantizedPolarCross w ∧
      routeEPCubicPolarPivotShortedFourthDepthEnergy w
          (routePPrimitiveFourthDepthParentAmplitude pe *
            routePPrimitiveFourthDepthJuliaDefectAmplitude pe) = w := by
  dsimp
  refine ⟨routePPrimitiveFourthDepthJulia_defectCompletesLiteralEnergy pe,
    routePPrimitiveFourthDepthJulia_parent_defect_pairing pe, ?_⟩
  rw [routePPrimitiveFourthDepthJulia_parent_defect_pairing]
  exact routeEPCubicPolarPivotShortedFourthDepthEnergy_quantized _
    (routePPrimitiveBaseCauchyCubicWeight_pos pe)

end

end RHTower
