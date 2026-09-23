import GaloisForLFunctions.RHTower.XiMassSharpSpacelikeConeSummability
import GaloisForLFunctions.HTGeometry.BesselOrderExteriorEnvelope

/-!
# The exterior Bessel envelope of the mass profile

Outside a fixed slope cone `h ≥ κ u` with `κ > 1` the mass profile obeys the exact Bessel
envelope of its own propagation argument.  Writing `z_u(h) = √(τ_u² + h²)` with `τ_u = σ + iu` and
principal root, the real part of `z_u(h)` dominates all three quantities the envelope needs:

`Re z_u(h) ≥ √(h² − u² + σ²) ≥ σ`,  `Re z_u(h) ≥ √(h² − u²)`,  `Re z_u(h) ≥ √(κ²−1) · u`.

Feeding these into the corpus curved-contour estimate and the order-one Schlaefli envelope gives
the two exterior bounds

`|F_u(h)| ≤ C₀ e^{-a√(h²−u²)}`  and  `|F_u(h)| ≤ C₁ u^{-1/2} e^{-a√(h²−u²)}`,

the second valid for every positive height.  The square-root gain in the second is exactly the
stationary-phase gain of the Bessel carrier, and it is what makes the endpoint slope
`κ_B = a/√(a²−1/4)` admissible.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Principal-root exterior geometry -/

/-- The propagation argument written with a squared complex height. -/
theorem xiMassSpacelikePropagationArgument_eq (sigma u h : ℝ) :
    xiMassSpacelikePropagationArgument sigma u h
      = ((sigma : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + (h : ℂ) ^ (2 : ℕ) := by
  rw [xiMassSpacelikePropagationArgument, Complex.ofReal_pow]

/-- **(17.5), first half.**  The principal root of the propagation argument has real part at least
the full spacelike gap. -/
theorem sqrt_fullGap_le_csqrtRe_propagationArgument {sigma u h : ℝ}
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h) :
    Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ))
      ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
  rw [xiMassSpacelikePropagationArgument_eq]
  exact HTGeometry.sqrt_le_csqrtRe hsigma hu huh

/-- The damping rate itself is a lower bound for the propagation rate. -/
theorem sigma_le_csqrtRe_propagationArgument {sigma u h : ℝ}
    (hsigma : 0 < sigma) (hu : 0 ≤ u) (huh : u ≤ h) :
    sigma ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
  refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu huh)
  have hgap : 0 ≤ h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hmono : Real.sqrt (sigma ^ (2 : ℕ)) ≤ Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt (by linarith)
  rwa [Real.sqrt_sq hsigma.le] at hmono

/-- **(17.5), second half.**  On a slope-`κ` cone the propagation rate grows at least linearly in
the height. -/
theorem sqrt_slopeGap_mul_le_csqrtRe_propagationArgument {sigma kappa u h : ℝ}
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u) (hcone : kappa * u ≤ h) :
    Real.sqrt (kappa ^ (2 : ℕ) - 1) * u
      ≤ HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu huh)
  have hkappa2 : (0 : ℝ) ≤ kappa ^ (2 : ℕ) - 1 := by nlinarith
  have hsq : (Real.sqrt (kappa ^ (2 : ℕ) - 1) * u) ^ (2 : ℕ) ≤ h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ) := by
    have hsqrt : Real.sqrt (kappa ^ (2 : ℕ) - 1) ^ (2 : ℕ) = kappa ^ (2 : ℕ) - 1 := Real.sq_sqrt hkappa2
    have hcone2 : (kappa * u) ^ (2 : ℕ) ≤ h ^ (2 : ℕ) := by nlinarith [mul_nonneg hkappa0.le hu]
    calc (Real.sqrt (kappa ^ (2 : ℕ) - 1) * u) ^ (2 : ℕ)
        = (kappa ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) := by rw [mul_pow, hsqrt]
      _ ≤ h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ) := by nlinarith
  have hnn : 0 ≤ Real.sqrt (kappa ^ (2 : ℕ) - 1) * u :=
    mul_nonneg (Real.sqrt_nonneg _) hu
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ) by nlinarith),
    Real.sqrt_nonneg (h ^ (2 : ℕ) - u ^ (2 : ℕ) + sigma ^ (2 : ℕ))]

/-! ## The two exterior envelopes -/

/-- The plain exterior envelope constant. -/
def xiMassBesselExteriorConstant (a sigma kappa : ℝ) : ℝ :=
  2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (a * sigma) *
    GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1

/-- The exterior envelope constant carrying the square-root gain. -/
def xiMassBesselExteriorSqrtConstant (a sigma kappa : ℝ) : ℝ :=
  2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (1 / (2 * (a * sigma))) *
    Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1)))

theorem xiMassBesselExteriorConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) :
    0 ≤ xiMassBesselExteriorConstant a sigma kappa := by
  have hK := (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos
    (mul_pos ha hsigma) 1).le
  have hratio : 0 ≤ (kappa + 1) / (kappa - 1) := by
    have h1 : (0 : ℝ) < kappa - 1 := by linarith
    positivity
  rw [xiMassBesselExteriorConstant]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hratio) (Real.exp_nonneg _)) hK

theorem xiMassBesselExteriorSqrtConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hkappa : 1 < kappa) :
    0 ≤ xiMassBesselExteriorSqrtConstant a sigma kappa := by
  have hratio : 0 ≤ (kappa + 1) / (kappa - 1) := by
    have h1 : (0 : ℝ) < kappa - 1 := by linarith
    positivity
  rw [xiMassBesselExteriorSqrtConstant]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hratio) (Real.exp_nonneg _))
    (Real.sqrt_nonneg _)

/-- **(17.6) The exterior Bessel envelope.**  On every slope-`κ` cone with `κ > 1`, the mass
profile decays at the full Bessel rate of the spacelike gap. -/
theorem norm_stripFourier_xiMass_le_besselExterior {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u) (hh : 0 < h)
    (hcone : kappa * u ≤ h) :
    ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖
      ≤ xiMassBesselExteriorConstant a sigma kappa
        * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  have hsig := sigma_le_csqrtRe_propagationArgument hsigma hu huh
  have hbase := norm_stripFourier_xiMass_le_optimal_full_exponent_uniformBoost
    (a := a) (sigma := sigma) (alpha := kappa) (u := u) (h := h) (q₀ := sigma)
    ha hsigma hkappa hu hh hcone hsigma hsig
  simp only at hbase
  set K : ℝ := HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) with hK
  have hgap : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ≤ K := by
    refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu huh)
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hexp : Real.exp (-(a * (K - sigma)))
      ≤ Real.exp (a * sigma) * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hKpos : 0 ≤ GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1 :=
    (GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder_pos (mul_pos ha hsigma) 1).le
  have hcoef : 0 ≤ 2 * a * ((kappa + 1) / (kappa - 1)) := by
    have h1 : (0 : ℝ) < kappa - 1 := by linarith
    positivity
  refine hbase.trans ?_
  rw [xiMassBesselExteriorConstant]
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp hcoef) hKpos
  calc 2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (-(a * (K - sigma)))
        * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1
      = (2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (-(a * (K - sigma))))
        * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1 := by ring
    _ ≤ (2 * a * ((kappa + 1) / (kappa - 1))
          * (Real.exp (a * sigma) * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))))))
        * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1 := hstep
    _ = 2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (a * sigma)
          * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * sigma) 1
          * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by ring

/-- **(17.7) The exterior Bessel envelope with the square-root gain.**  At positive height the
Bessel carrier contributes an extra factor `u^{-1/2}`. -/
theorem norm_stripFourier_xiMass_le_besselExteriorSqrt {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u)
    (hcone : kappa * u ≤ h) :
    ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖
      ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hkappa2 : (0 : ℝ) < kappa ^ (2 : ℕ) - 1 := by nlinarith
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  have hh : 0 < h := lt_of_lt_of_le hu huh
  set K : ℝ := HTGeometry.csqrtRe (xiMassSpacelikePropagationArgument sigma u h) with hKdef
  have hsig : sigma ≤ K := sigma_le_csqrtRe_propagationArgument hsigma hu.le huh
  have hKpos : 0 < K := lt_of_lt_of_le hsigma hsig
  have hbase := norm_stripFourier_xiMass_le_optimal_full_exponent_uniformBoost
    (a := a) (sigma := sigma) (alpha := kappa) (u := u) (h := h) (q₀ := K)
    ha hsigma hkappa hu.le hh hcone hKpos le_rfl
  simp only at hbase
  rw [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at hbase
  have hgap : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ≤ K := by
    refine le_trans ?_ (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu.le huh)
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hslope : Real.sqrt (kappa ^ (2 : ℕ) - 1) * u ≤ K :=
    sqrt_slopeGap_mul_le_csqrtRe_propagationArgument hsigma hkappa hu.le hcone
  have henv := HTGeometry.realModifiedBesselKOrder_one_le (s := a * K) (mul_pos ha hKpos)
  have h1 : Real.exp (-(a * K)) ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (1 / (2 * (a * K))) ≤ Real.exp (1 / (2 * (a * sigma))) := by
    refine Real.exp_le_exp.2 ?_
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h3 : Real.sqrt (2 * Real.pi / (a * K))
      ≤ Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1))) / Real.sqrt u := by
    have hsq : (0 : ℝ) < Real.sqrt (kappa ^ (2 : ℕ) - 1) := Real.sqrt_pos.2 hkappa2
    have hval : Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1))) / Real.sqrt u
        = Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1) * u)) := by
      rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1)))]
      congr 1
      field_simp
    rw [hval]
    refine Real.sqrt_le_sqrt ?_
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  have hcoef : 0 ≤ 2 * a * ((kappa + 1) / (kappa - 1)) := by
    have h1' : (0 : ℝ) < kappa - 1 := by linarith
    positivity
  refine hbase.trans ?_
  rw [xiMassBesselExteriorSqrtConstant]
  have hchain : GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * K) 1
      ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) * Real.exp (1 / (2 * (a * sigma)))
        * (Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1))) / Real.sqrt u) := by
    refine henv.trans ?_
    have e1 : (0 : ℝ) ≤ Real.exp (-(a * K)) := Real.exp_nonneg _
    have e2 : (0 : ℝ) ≤ Real.exp (1 / (2 * (a * K))) := Real.exp_nonneg _
    have e3 : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi / (a * K)) := Real.sqrt_nonneg _
    have hfirst : Real.exp (-(a * K)) * Real.exp (1 / (2 * (a * K)))
        ≤ Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) * Real.exp (1 / (2 * (a * sigma))) :=
      mul_le_mul h1 h2 e2 (Real.exp_nonneg _)
    exact mul_le_mul hfirst h3 e3 (by positivity)
  have hfinal := mul_le_mul_of_nonneg_left hchain hcoef
  calc 2 * a * ((kappa + 1) / (kappa - 1))
        * GaloisForLFunctions.HTGeometry.realModifiedBesselKOrder (a * K) 1
      ≤ 2 * a * ((kappa + 1) / (kappa - 1))
        * (Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) * Real.exp (1 / (2 * (a * sigma)))
          * (Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1))) / Real.sqrt u)) := hfinal
    _ = 2 * a * ((kappa + 1) / (kappa - 1)) * Real.exp (1 / (2 * (a * sigma)))
          * Real.sqrt (2 * Real.pi / (a * Real.sqrt (kappa ^ (2 : ℕ) - 1))) / Real.sqrt u
          * Real.exp (-(a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)))) := by ring

end

end RHTower
