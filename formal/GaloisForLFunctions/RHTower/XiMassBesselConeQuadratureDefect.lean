import GaloisForLFunctions.RHTower.XiMassBesselConeTail

/-!
# The quadrature defect of the closed sharp Bessel cone

The continuum half of the Bessel cone is bounded by the same exterior exponent.  On the exterior
of a slope-`κ` cone the growing profile obeys

`‖e^{h/2} F_u(h)‖ ≤ C₀ e^{-η_κ u} e^{-(a-1/2)(h - κu)}`,

so the continuum integral between two cone edges is at most `C₀ e^{-η_κ u}/(a-1/2)`, uniformly.
Splitting the continuum prefix of the slope-`κ` cone against the prefix of a legal interior depth
therefore bounds it uniformly, and the finite Stieltjes identity turns the closed-cone criterion
into a criterion on the quadrature defect between the true-prime logarithmic measure and its
continuum density.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The exterior continuum tail -/

/-- The exterior envelope of the growing profile. -/
theorem norm_xiMassCriticalGrowingFourierProfile_exterior_le {a sigma kappa u h : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u) (hh : 0 < h)
    (hcone : kappa * u ≤ h) :
    ‖xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ xiMassBesselExteriorConstant a sigma kappa
        * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp (-((a - 1 / 2) * (h - kappa * u)))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hF := norm_stripFourier_xiMass_le_besselExterior ha0 hsigma hkappa hu hh hcone
  have hexpo := xiMassBessel_exterior_exponent_le ha hkappa hu hcone
  have hnorm : ‖xiMassCriticalGrowingFourierProfile a sigma u h‖
      = Real.exp (h / 2)
        * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖ := by
    rw [xiMassCriticalGrowingFourierProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have hC : 0 ≤ xiMassBesselExteriorConstant a sigma kappa :=
    xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa
  have hstep : Real.exp (h / 2)
      * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)‖
      ≤ Real.exp (h / 2)
        * (xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
    mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
  refine hstep.trans ?_
  have hcomb : Real.exp (h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
      ≤ Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp (-((a - 1 / 2) * (h - kappa * u))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc Real.exp (h / 2)
        * (xiMassBesselExteriorConstant a sigma kappa
          * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = xiMassBesselExteriorConstant a sigma kappa
        * (Real.exp (h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by ring
    _ ≤ xiMassBesselExteriorConstant a sigma kappa
        * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp (-((a - 1 / 2) * (h - kappa * u)))) :=
        mul_le_mul_of_nonneg_left hcomb hC

/-- The exponential majorant integrates to a bounded amount on every right ray. -/
theorem integral_exp_neg_shift_le {δ b c e : ℝ} (hδ : 0 < δ) :
    ∫ h in c..e, Real.exp (-(δ * (h - b))) ≤ Real.exp (-(δ * (c - b))) / δ := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun h : ℝ => -(Real.exp (-(δ * (h - b))) / δ))
      (Real.exp (-(δ * (x - b)))) x := by
    intro x
    have hb : HasDerivAt (fun h : ℝ => δ * (h - b)) δ x := by
      simpa using ((hasDerivAt_id x).sub_const b).const_mul δ
    have h1 : HasDerivAt (fun h : ℝ => -(δ * (h - b))) (-δ) x := hb.neg
    have h2 : HasDerivAt (fun h : ℝ => Real.exp (-(δ * (h - b))))
        (Real.exp (-(δ * (x - b))) * -δ) x := h1.exp
    have h3 := (h2.div_const δ).neg
    have hval : -(Real.exp (-(δ * (x - b))) * -δ / δ) = Real.exp (-(δ * (x - b))) := by
      field_simp
    rwa [hval] at h3
  have hint : ∫ h in c..e, Real.exp (-(δ * (h - b)))
      = -(Real.exp (-(δ * (e - b))) / δ) - -(Real.exp (-(δ * (c - b))) / δ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      ((by fun_prop : Continuous fun h : ℝ => Real.exp (-(δ * (h - b)))).intervalIntegrable c e)
  rw [hint]
  have hdivpos : 0 < Real.exp (-(δ * (e - b))) / δ := div_pos (Real.exp_pos _) hδ
  linarith

/-- The continuum tail constant on the exterior of a slope-`κ` cone. -/
def xiMassBesselContinuumTailConstant (a sigma kappa : ℝ) : ℝ :=
  xiMassBesselExteriorConstant a sigma kappa / (a - 1 / 2)

/-- **(17.16) The exterior continuum tail.**  The continuum integral of the growing profile
between two cone edges is uniformly bounded. -/
theorem norm_integral_growingFourierProfile_exterior_le {a sigma kappa u c e : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 ≤ u)
    (hc : 0 < c) (hccone : kappa * u ≤ c) (hce : c ≤ e) :
    ‖∫ h in c..e, xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ xiMassBesselContinuumTailConstant a sigma kappa
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hGcont : Continuous (xiMassCriticalGrowingFourierProfile a sigma u) := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalGrowingFourierProfile ha0 hsigma u h).continuousAt
  have hnormle : ‖∫ h in c..e, xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ ∫ h in c..e, ‖xiMassCriticalGrowingFourierProfile a sigma u h‖ :=
    intervalIntegral.norm_integral_le_integral_norm hce
  refine hnormle.trans ?_
  set C : ℝ := xiMassBesselExteriorConstant a sigma kappa with hC
  have hC0 : 0 ≤ C := xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa
  have hmono : ∫ h in c..e, ‖xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ ∫ h in c..e, C * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp (-((a - 1 / 2) * (h - kappa * u))) := by
    refine intervalIntegral.integral_mono_on hce
      ((hGcont.norm).intervalIntegrable c e) ((by fun_prop : Continuous fun h : ℝ =>
        C * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp (-((a - 1 / 2) * (h - kappa * u)))).intervalIntegrable c e) ?_
    intro x hx
    have hxc : c ≤ x := hx.1
    have hxpos : 0 < x := lt_of_lt_of_le hc hxc
    have hxcone : kappa * u ≤ x := le_trans hccone hxc
    have := norm_xiMassCriticalGrowingFourierProfile_exterior_le
      (a := a) (sigma := sigma) (kappa := kappa) (u := u) (h := x)
      ha hsigma hkappa hu hxpos hxcone
    rw [← hC] at this
    calc ‖xiMassCriticalGrowingFourierProfile a sigma u x‖
        ≤ C * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp (-((a - 1 / 2) * (x - kappa * u)))) := this
      _ = C * Real.exp (-(xiMassBesselConeExponent a kappa * u))
            * Real.exp (-((a - 1 / 2) * (x - kappa * u))) := by ring
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have htail := integral_exp_neg_shift_le (δ := a - 1 / 2) (b := kappa * u) (c := c) (e := e) hδ
  have hshift : Real.exp (-((a - 1 / 2) * (c - kappa * u))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hcoef : 0 ≤ C * Real.exp (-(xiMassBesselConeExponent a kappa * u)) :=
    mul_nonneg hC0 (Real.exp_nonneg _)
  have hstep := mul_le_mul_of_nonneg_left htail hcoef
  refine hstep.trans ?_
  rw [xiMassBesselContinuumTailConstant, ← hC]
  have hE : 0 ≤ Real.exp (-(xiMassBesselConeExponent a kappa * u)) := Real.exp_nonneg _
  have hbase : 0 ≤ C * Real.exp (-(xiMassBesselConeExponent a kappa * u)) / (a - 1 / 2) :=
    div_nonneg (mul_nonneg hC0 hE) hδ.le
  calc C * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * (Real.exp (-((a - 1 / 2) * (c - kappa * u))) / (a - 1 / 2))
      = (C * Real.exp (-(xiMassBesselConeExponent a kappa * u)) / (a - 1 / 2))
        * Real.exp (-((a - 1 / 2) * (c - kappa * u))) := by ring
    _ ≤ (C * Real.exp (-(xiMassBesselConeExponent a kappa * u)) / (a - 1 / 2)) * 1 :=
        mul_le_mul_of_nonneg_left hshift hbase
    _ = C / (a - 1 / 2) * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by ring


/-! ## The closed-cone quadrature defect -/

/-- The cone edge is positive and dominates the cone height. -/
theorem xiMassCriticalConeEdge_pos {kappa u : ℝ} (hkappa : 1 < kappa) (hu : 0 ≤ u) :
    0 < xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa) u := by
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hH : xiMassConeDepthOfSlope kappa * u / (xiMassConeDepthOfSlope kappa - 1 / 2) = kappa * u :=
    xiMassConeDepthOfSlope_height hkappa u
  have hone : (1 : ℝ) ≤ Real.exp (kappa * u) := Real.one_le_exp (mul_nonneg hkappa0.le hu)
  have hfloor : 1 ≤ ⌊Real.exp (kappa * u)⌋₊ := Nat.le_floor (by exact_mod_cast hone)
  rw [xiMassCriticalConeEdge, hH]
  refine Real.log_pos ?_
  have : (1 : ℝ) ≤ ((⌊Real.exp (kappa * u)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor
  linarith

/-- Cone edges increase with the slope. -/
theorem xiMassCriticalConeEdge_mono_slope {kappa kappa' u : ℝ} (hkappa : 1 < kappa)
    (hkk : kappa ≤ kappa') (hu : 0 ≤ u) :
    xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa) u
      ≤ xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa') u := by
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  rw [xiMassCriticalConeEdge, xiMassCriticalConeEdge, xiMassConeDepthOfSlope_height hkappa,
    xiMassConeDepthOfSlope_height hkappa']
  have hfl : ⌊Real.exp (kappa * u)⌋₊ ≤ ⌊Real.exp (kappa' * u)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith))
  have hcast : ((⌊Real.exp (kappa * u)⌋₊ : ℕ) : ℝ) ≤ ((⌊Real.exp (kappa' * u)⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast hfl
  refine Real.log_le_log (by positivity) (by linarith)

/-- **(17.16) The closed-cone continuum prefix is uniformly bounded.** -/
theorem exists_norm_integral_growingFourierProfile_at_besselCone_le {a sigma kappa : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa)
    (hsharp : xiMassSpacelikeSharpSlope a ≤ kappa) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖∫ h in (0 : ℝ)..xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa) u,
        xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ B := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  set kappa' : ℝ := max kappa (a / (a - 1 / 2)) + 1 with hkappa'def
  have hkk : kappa ≤ kappa' := by
    rw [hkappa'def]
    have := le_max_left kappa (a / (a - 1 / 2))
    linarith
  have hkappa' : 1 < kappa' := lt_of_lt_of_le hkappa hkk
  have hslopelt : a / (a - 1 / 2) < kappa' := by
    rw [hkappa'def]
    have := le_max_right kappa (a / (a - 1 / 2))
    linarith
  set d' : ℝ := xiMassConeDepthOfSlope kappa' with hd'
  have hd'half : 1 / 2 < d' := xiMassConeDepthOfSlope_half_lt hkappa'
  have hd'a : d' < a := (xiMassConeDepthOfSlope_lt_iff ha hkappa').2 hslopelt
  have hGcont : ∀ u : ℝ, Continuous (xiMassCriticalGrowingFourierProfile a sigma u) := by
    intro u
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalGrowingFourierProfile ha0 hsigma u h).continuousAt
  have heta : 0 ≤ xiMassBesselConeExponent a kappa :=
    xiMassBesselConeExponent_nonneg ha hkappa hsharp
  refine ⟨(2 * Real.pi + 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d' - 1 / 2)
    + 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))))
    + xiMassBesselContinuumTailConstant a sigma kappa, fun u hu => ?_⟩
  set W : ℝ := xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa) u with hW
  set W' : ℝ := xiMassCriticalConeEdge d' u with hW'
  have hWpos : 0 < W := xiMassCriticalConeEdge_pos hkappa hu
  have hWW' : W ≤ W' := by
    rw [hW, hW', hd']
    exact xiMassCriticalConeEdge_mono_slope hkappa hkk hu
  have hWcone : kappa * u ≤ W := by
    have := xiMassCriticalConeEdge_ge (xiMassConeDepthOfSlope kappa) u
    rwa [xiMassConeDepthOfSlope_height hkappa] at this
  have hsplit : (∫ h in (0 : ℝ)..W, xiMassCriticalGrowingFourierProfile a sigma u h)
      + ∫ h in W..W', xiMassCriticalGrowingFourierProfile a sigma u h
      = ∫ h in (0 : ℝ)..W', xiMassCriticalGrowingFourierProfile a sigma u h :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hGcont u).intervalIntegrable 0 W) ((hGcont u).intervalIntegrable W W')
  have hsolve : (∫ h in (0 : ℝ)..W, xiMassCriticalGrowingFourierProfile a sigma u h)
      = (∫ h in (0 : ℝ)..W', xiMassCriticalGrowingFourierProfile a sigma u h)
        - ∫ h in W..W', xiMassCriticalGrowingFourierProfile a sigma u h := by
    rw [← hsplit]; ring
  have hprefix : ‖∫ h in (0 : ℝ)..W', xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ 2 * Real.pi + 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d' - 1 / 2)
        + 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
    rw [hW']
    exact norm_integral_xiMassCriticalGrowingFourierProfile_at_cone_le
      hd'half hd'a hsigma hu (xiMassCriticalConeEdge_ge d' u)
  have htail : ‖∫ h in W..W', xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ xiMassBesselContinuumTailConstant a sigma kappa := by
    refine le_trans (norm_integral_growingFourierProfile_exterior_le
      ha hsigma hkappa hu hWpos hWcone hWW') ?_
    have hexp : Real.exp (-(xiMassBesselConeExponent a kappa * u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hC0 : 0 ≤ xiMassBesselContinuumTailConstant a sigma kappa := by
      rw [xiMassBesselContinuumTailConstant]
      exact div_nonneg (xiMassBesselExteriorConstant_nonneg ha0 hsigma hkappa) hδ.le
    nlinarith
  rw [hsolve]
  exact (norm_sub_le _ _).trans (add_le_add hprefix htail)

/-- The line-bound property of the slope-`κ` quadrature defect. -/
def XiMassCriticalBesselQuadratureDefectLineBound (a sigma kappa : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalPrimeQuadratureDefect a sigma (xiMassConeDepthOfSlope kappa) u‖ ≤ C

/-- **(17.15) The closed sharp Bessel quadrature-defect criterion.**  For every slope at or above
the Bessel balance slope, RH is equivalent to uniform boundedness of the quadrature defect between
the true-prime logarithmic measure and its continuum density inside that cone. -/
theorem riemannHypothesis_iff_xiMassCriticalBesselQuadratureDefectLineBound
    {a c sigma kappa : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (hkappa : 1 < kappa) (hsharp : xiMassSpacelikeSharpSlope a ≤ kappa) :
    RiemannHypothesis ↔ XiMassCriticalBesselQuadratureDefectLineBound a sigma kappa := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  obtain ⟨B, hB⟩ := exists_norm_integral_growingFourierProfile_at_besselCone_le
    ha hsigma hkappa hsharp
  rw [riemannHypothesis_iff_xiMassCriticalBesselConeLineBound hhalf hca hsigma hkappa hsharp]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    rw [xiMassCriticalPrimeQuadratureDefect]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hB u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
        = xiMassCriticalPrimeQuadratureDefect a sigma (xiMassConeDepthOfSlope kappa) u
          + ∫ h in (0 : ℝ)..xiMassCriticalConeEdge (xiMassConeDepthOfSlope kappa) u,
              xiMassCriticalGrowingFourierProfile a sigma u h := by
      rw [xiMassCriticalPrimeQuadratureDefect]
      ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hB u hu))

end

end RHTower
