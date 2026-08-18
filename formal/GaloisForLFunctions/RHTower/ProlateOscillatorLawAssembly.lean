import GaloisForLFunctions.RHTower.ProlateSignedModeLadderPin
import GaloisForLFunctions.RHTower.ProlateProfileMassTransfer
import GaloisForLFunctions.RHTower.ProlateHermiteTailMass
import GaloisForLFunctions.RHTower.ProlateIndexedPairingFloor
import GaloisForLFunctions.RHTower.ProlateSharpMassRatio

/-!
# Assembling the two-sided oscillator law

The ladder pin bounds the distance from the rescaled separation constant to an oscillator rung by
`sup|u| · ∫|W| / (c · |⟨u, φ⟩|)`.  Both factors are homogeneous of degree one in the profile, so the
normalisation may be chosen freely; the origin normalisation is the one carrying a uniform square
mass, hence a `c^{3/4}` sup bound, and a pairing floor.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace RHTower

/-- The canonical radial representative does not vanish at the origin. -/
theorem signedModeRadialData_R_zero_ne_zero {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) : (signedModeRadialData a n).R 0 ≠ 0 := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a n).R :=
    hD.2.2.2.2.2.1
  have heven : Function.Even (signedModeRadialData a n).R := hD.2.2.2.2.2.2.1
  have hR1 : (signedModeRadialData a n).R 1 = 1 := hD.2.2.2.2.2.2.2.1
  have hne : (signedModeRadialData a n).R ≠ 0 := by
    intro h
    have : (signedModeRadialData a n).R 1 = 0 := by rw [h]; rfl
    rw [hR1] at this
    exact one_ne_zero this
  exact value_zero_ne_of_even_joint_prolate_band_eigen hsm hne heven
    (pow_ne_zero 2 hvalue) (bandTransform_signedModeRadialData_R ha n hvalue)
    hD.2.2.2.2.2.2.2.2.2.1

/-- The endpoint-normalised rescaled profile is the origin-normalised one, scaled by the central
value. -/
theorem signedModeRescaledProfile_eq_smul {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) (ξ : ℝ) :
    signedModeRescaledProfile a n ξ
      = (signedModeRadialData a n).R 0
        * GaloisForLFunctions.RHTower.indexedOscillatorProfile n ⟨a, ha⟩ ξ := by
  have h0 : (signedModeRadialData a n).R 0 ≠ 0 := signedModeRadialData_R_zero_ne_zero ha n hvalue
  show prolateHermiteRescale (signedModeRadialBandwidth a) (signedModeRadialData a n).R ξ
    = (signedModeRadialData a n).R 0
      * (prolateHermiteRescale (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth ⟨a, ha⟩)
          (signedModeRadialData a n).R ξ / (signedModeRadialData a n).R 0)
  rw [show GaloisForLFunctions.RHTower.indexedOscillatorBandwidth ⟨a, ha⟩
      = signedModeRadialBandwidth a from rfl]
  field_simp


/-- The origin-normalised radial representative is again a band eigenfunction. -/
theorem bandTransform_signedModeRadialData_R_div {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    bandTransform (signedModeRadialBandwidth a)
        (fun y => (signedModeRadialData a n).R y / (signedModeRadialData a n).R 0) x
      = evenProlateSignedValue a n ^ 2
          * ((signedModeRadialData a n).R x / (signedModeRadialData a n).R 0) := by
  have hfun : (fun y => (signedModeRadialData a n).R y / (signedModeRadialData a n).R 0)
      = fun y => ((signedModeRadialData a n).R 0)⁻¹ * (signedModeRadialData a n).R y := by
    funext y
    rw [div_eq_mul_inv]
    ring
  rw [hfun, GaloisForLFunctions.RHTower.bandTransform_const_mul,
    bandTransform_signedModeRadialData_R ha n hvalue]
  ring

/-- **Sup bound for the canonical origin-normalised profile from its square mass.** -/
theorem abs_indexedOscillatorProfile_le {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) {N : ℝ}
    (hmass : GaloisForLFunctions.RHTower.indexedOscillatorTotalMass n ⟨a, ha⟩ ≤ N) (ξ : ℝ) :
    |GaloisForLFunctions.RHTower.indexedOscillatorProfile n ⟨a, ha⟩ ξ|
      ≤ |evenProlateSignedValue a n ^ 2|⁻¹
        * (signedModeRadialBandwidth a / Real.pi
            * ((1 + N / 2) / Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)))) := by
  have hc : 0 < signedModeRadialBandwidth a := signedModeRadialBandwidth_pos ha
  have h0 : (signedModeRadialData a n).R 0 ≠ 0 := signedModeRadialData_R_zero_ne_zero ha n hvalue
  have hD := signedModeRadialData_isExact ha n hvalue
  have hcont : Continuous (signedModeRadialData a n).R := (hD.2.2.2.2.2.1).continuous
  have hpt : ∀ z : ℝ,
      prolateHermiteRescale (signedModeRadialBandwidth a)
          (fun y => (signedModeRadialData a n).R y / (signedModeRadialData a n).R 0) z
        = GaloisForLFunctions.RHTower.indexedOscillatorProfile n ⟨a, ha⟩ z := fun z => rfl
  have hmass' : (∫ z in (-Real.sqrt (signedModeRadialBandwidth a))..
      (Real.sqrt (signedModeRadialBandwidth a)),
      prolateHermiteRescale (signedModeRadialBandwidth a)
        (fun y => (signedModeRadialData a n).R y / (signedModeRadialData a n).R 0) z ^ 2) ≤ N := by
    refine le_trans (le_of_eq ?_) hmass
    exact intervalIntegral.integral_congr fun z _ => by rw [hpt z]
  have h := abs_le_of_rescaled_mass_le (c := signedModeRadialBandwidth a)
    (lam := evenProlateSignedValue a n ^ 2) hc (pow_ne_zero 2 hvalue)
    (hcont.div_const _) (bandTransform_signedModeRadialData_R_div ha n hvalue) hmass'
    (ξ / Real.sqrt (signedModeRadialBandwidth a))
  have hval : (signedModeRadialData a n).R (ξ / Real.sqrt (signedModeRadialBandwidth a))
      / (signedModeRadialData a n).R 0
      = GaloisForLFunctions.RHTower.indexedOscillatorProfile n ⟨a, ha⟩ ξ := rfl
  rwa [hval] at h

/-- The canonical square mass is eventually bounded, by convergence. -/
theorem eventually_indexedOscillatorTotalMass_le (n : ℕ) :
    ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      GaloisForLFunctions.RHTower.indexedOscillatorTotalMass n a
        ≤ sharpInteriorLimit n + 1 := by
  have h := (tendsto_indexedOscillatorTotalMass n).eventually
    (eventually_lt_nhds (by linarith : sharpInteriorLimit n < sharpInteriorLimit n + 1))
  exact h.mono fun x hx => hx.le


/-! ## The limiting window pairing, explicitly -/

/-- The limiting window pairing is the Hermite window mass over the central value. -/
theorem abs_integral_oscProfile_mul_hermiteFun_eq {n : ℕ} (hn : Even n) {K : ℝ} (hK : 0 ≤ K) :
    |∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x|
      = (∫ x in (-K)..K, hermiteFun n x ^ 2) / |hermiteFun n 0| := by
  have h0 : hermiteFun n 0 ≠ 0 := hermiteFun_zero_ne_zero hn
  have hpt : ∀ x : ℝ, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x
      = hermiteFun n x ^ 2 / hermiteFun n 0 := by
    intro x
    have h := congrFun (hermiteFun_div_eq_oscProfile hn) x
    rw [← h]
    field_simp
  have hrw : (∫ x in (-K)..K, oscProfile (2 * (n : ℝ) + 1) x * hermiteFun n x)
      = (∫ x in (-K)..K, hermiteFun n x ^ 2) / hermiteFun n 0 := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  rw [hrw, abs_div, abs_of_nonneg]
  exact intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _

/-- The Hermite window mass grows with the window. -/
theorem integral_hermiteFun_sq_mono {n : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    (∫ x in (-1 : ℝ)..1, hermiteFun n x ^ 2) ≤ ∫ x in (-K)..K, hermiteFun n x ^ 2 := by
  have hcont : Continuous fun x : ℝ => hermiteFun n x ^ 2 := (continuous_hermiteFun n).pow 2
  have h1 : (∫ x in (-K)..(-1 : ℝ), hermiteFun n x ^ 2)
      + ∫ x in (-1 : ℝ)..1, hermiteFun n x ^ 2 = ∫ x in (-K)..1, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have h2 : (∫ x in (-K)..(1 : ℝ), hermiteFun n x ^ 2)
      + ∫ x in (1 : ℝ)..K, hermiteFun n x ^ 2 = ∫ x in (-K)..K, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hleft : (0 : ℝ) ≤ ∫ x in (-K)..(-1 : ℝ), hermiteFun n x ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hright : (0 : ℝ) ≤ ∫ x in (1 : ℝ)..K, hermiteFun n x ^ 2 :=
    intervalIntegral.integral_nonneg hK fun x _ => sq_nonneg _
  linarith [h1, h2, hleft, hright]

/-- The positive window floor at the unit window. -/
theorem integral_hermiteFun_sq_unit_pos (n : ℕ) :
    0 < ∫ x in (-1 : ℝ)..1, hermiteFun n x ^ 2 :=
  integral_hermiteFun_sq_pos n (by norm_num)



/-- The weighted square of a Hermite function is integrable. -/
theorem integrable_sq_mul_hermiteFun_sq (n : ℕ) :
    Integrable (fun x : ℝ => x ^ 2 * hermiteFun n x ^ 2) := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  refine (integrable_polyEval_mul_gauss (Polynomial.X ^ 2 * p ^ 2) (b := 1)
    (by norm_num)).congr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  show Polynomial.eval x (Polynomial.X ^ 2 * p ^ 2) * Real.exp (-(1 * x ^ 2))
    = x ^ 2 * hermiteFun n x ^ 2
  rw [hp x, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_X]
  have hexp : Real.exp (-(1 / 2 * x ^ 2)) * Real.exp (-(1 / 2 * x ^ 2))
      = Real.exp (-(1 * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc x ^ 2 * p.eval x ^ 2 * Real.exp (-(1 * x ^ 2))
      = x ^ 2 * (p.eval x ^ 2 * (Real.exp (-(1 / 2 * x ^ 2))
        * Real.exp (-(1 / 2 * x ^ 2)))) := by rw [hexp]; ring
    _ = x ^ 2 * (p.eval x * Real.exp (-(1 / 2 * x ^ 2))) ^ 2 := by ring

/-- The truncated weighted square never exceeds its whole-line value. -/
theorem intervalIntegral_sq_mul_hermiteFun_sq_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in (-R)..R, x ^ 2 * hermiteFun n x ^ 2)
      ≤ ∫ x, x ^ 2 * hermiteFun n x ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_le_integral (integrable_sq_mul_hermiteFun_sq n)
    (Filter.Eventually.of_forall fun x => by positivity)

/-! ## The whole-line pairing floor -/

/-- The fourth root of the bandwidth grows. -/
theorem tendsto_quartRoot_indexedOscillatorBandwidth :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      Real.sqrt (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    GaloisForLFunctions.RHTower.tendsto_indexedOscillatorBandwidth_atTop)

/-- The reciprocal squared signed value tends to one. -/
theorem tendsto_inv_evenProlateSignedValue_sq (n : ℕ) :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹) atTop (𝓝 1) := by
  have hval := (evenProlateSignedValue_sq_tendsto_one n).comp
    GaloisForLFunctions.RHTower.tendsto_prolatePositiveAperture_val_atTop
  have habs : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      |evenProlateSignedValue (a : ℝ) n ^ 2|) atTop (𝓝 1) := by
    have h := hval.abs
    simpa using h
  have h := habs.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa using h

/-- The outer-tail contribution vanishes. -/
theorem tendsto_outerTail_zero (n : ℕ) (N C : ℝ) :
    Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
        * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
            * ((1 + N / 2)
              / Real.sqrt (Real.sqrt
                (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))))
        * (2 * C / (3 * Real.sqrt
            (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) ^ 3)))
      atTop (𝓝 0) := by
  set K₁ : ℝ := 2 * C * (1 + N / 2) / (3 * Real.pi) with hK₁
  have hq := tendsto_quartRoot_indexedOscillatorBandwidth
  have hcube : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
      K₁ / Real.sqrt (Real.sqrt
        (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) ^ 3) atTop (𝓝 0) := by
    have hpow : Tendsto (fun a : GaloisForLFunctions.RHTower.ProlatePositiveAperture =>
        Real.sqrt (Real.sqrt
          (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hq
    have hinv := hpow.inv_tendsto_atTop
    have h := hinv.const_mul K₁
    rw [mul_zero] at h
    refine h.congr fun a => ?_
    simp [div_eq_mul_inv]
  have hprod := (tendsto_inv_evenProlateSignedValue_sq n).mul hcube
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [] with a
  have hc : 0 < GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a :=
    GaloisForLFunctions.RHTower.indexedOscillatorBandwidth_pos a
  have hs : 0 < Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) :=
    Real.sqrt_pos.2 hc
  set q : ℝ := Real.sqrt (Real.sqrt
    (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 hs
  have hq2 : q ^ 2 = Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) :=
    Real.sq_sqrt hs.le
  have hs2 : Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) ^ 2
      = GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a := Real.sq_sqrt hc.le
  have hcq : GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a = q ^ 4 := by
    rw [← hs2, ← hq2]
    ring
  rw [← hq2, hcq, hK₁]
  field_simp



/-- **The whole-line pairing floor for the canonical profile.** -/
theorem exists_floor_abs_integral_indexedOscillator (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      δ ≤ |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
              * hermiteFun (2 * n) x| := by
  classical
  have hn : Even (2 * n) := ⟨n, by ring⟩
  have hφ0 : hermiteFun (2 * n) 0 ≠ 0 := hermiteFun_zero_ne_zero hn
  have hφcont : Continuous (hermiteFun (2 * n)) := continuous_hermiteFun (2 * n)
  set F1 : ℝ := (∫ x in (-1 : ℝ)..1, hermiteFun (2 * n) x ^ 2) / |hermiteFun (2 * n) 0|
    with hF1def
  have hF1 : 0 < F1 := div_pos (integral_hermiteFun_sq_unit_pos (2 * n)) (abs_pos.2 hφ0)
  set N : ℝ := sharpInteriorLimit n + 1 with hNdef
  have hSIL : 0 < sharpInteriorLimit n :=
    sharpInteriorLimit_pos n
  have hN0 : 0 ≤ N := by rw [hNdef]; linarith
  set Cφ : ℝ := ∫ x, x ^ 2 * hermiteFun (2 * n) x ^ 2 with hCφdef
  have hCφ0 : 0 ≤ Cφ := integral_nonneg fun x => by positivity
  set M : ℝ := (4 * (n : ℝ) + 2) * N + Cφ with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ 4 * (n : ℝ) + 2 := by positivity
    nlinarith [hN0, hCφ0]
  set K₀ : ℝ := max 1 (4 * M / F1 + 1) with hK₀def
  have hK₀1 : (1 : ℝ) ≤ K₀ := le_max_left _ _
  have hK₀pos : (0 : ℝ) < K₀ := lt_of_lt_of_le one_pos hK₀1
  have hK₀sq : 4 * M / F1 ≤ K₀ ^ 2 := by
    have h1 : 4 * M / F1 + 1 ≤ K₀ := le_max_right _ _
    nlinarith [hK₀1, h1]
  obtain ⟨Ctail, hCtail0, hCtail⟩ := exists_bound_abs_integral_sub_window (2 * n)
  refine ⟨F1 / 4, by linarith, ?_⟩
  have houter := (tendsto_outerTail_zero n N Ctail).eventually
    (eventually_lt_nhds (by linarith : (0 : ℝ) < F1 / 8))
  have hval : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      evenProlateSignedValue (a : ℝ) n ≠ 0 :=
    GaloisForLFunctions.RHTower.tendsto_prolatePositiveAperture_val_atTop.eventually
      (eventually_evenProlateSignedValue_ne_zero n)
  have hsep : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      GaloisForLFunctions.RHTower.indexedOscillatorSeparation n a ≤ 4 * (n : ℝ) + 2 := by
    have h := (GaloisForLFunctions.RHTower.tendsto_indexedOscillatorSeparation_atTop n).eventually
      (eventually_lt_nhds (by linarith : 4 * (n : ℝ) + 1 < 4 * (n : ℝ) + 2))
    exact h.mono fun a ha => ha.le
  have hbig : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      K₀ ^ 2 ≤ GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a :=
    GaloisForLFunctions.RHTower.tendsto_indexedOscillatorBandwidth_atTop.eventually_ge_atTop _
  filter_upwards [GaloisForLFunctions.RHTower.eventually_abs_indexedOscillator_window_pairing_ge n hK₀pos,
    eventually_indexedOscillatorTotalMass_le n, hsep, hval, hbig, houter] with a
    hwinfloor hmassa hsepa hvala hbiga houtera
  have hc : 0 < GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a :=
    GaloisForLFunctions.RHTower.indexedOscillatorBandwidth_pos a
  have hsc : 0 < Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) :=
    Real.sqrt_pos.2 hc
  have hK₀sc : K₀ ≤ Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) := by
    have h := Real.sqrt_le_sqrt hbiga
    rwa [Real.sqrt_sq hK₀pos.le] at h
  have hsc1 : (1 : ℝ) ≤ Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) :=
    le_trans hK₀1 hK₀sc
  have hvcont : Continuous (GaloisForLFunctions.RHTower.indexedOscillatorProfile n a) :=
    Differentiable.continuous fun x =>
      (GaloisForLFunctions.RHTower.indexedOscillatorProfile_hasDerivAt n a x).differentiableAt
  -- the sup bound
  set Bsup : ℝ := |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
    * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
      * ((1 + N / 2) / Real.sqrt (Real.sqrt
          (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)))) with hBsupdef
  have hsup : ∀ ξ, |GaloisForLFunctions.RHTower.indexedOscillatorProfile n a ξ| ≤ Bsup := by
    intro ξ
    have hmasseq : GaloisForLFunctions.RHTower.indexedOscillatorTotalMass n
        ⟨(a : ℝ), a.property⟩ ≤ N := by
      have : (⟨(a : ℝ), a.property⟩ : GaloisForLFunctions.RHTower.ProlatePositiveAperture) = a :=
        Subtype.ext rfl
      rw [this]
      exact hmassa
    have h := abs_indexedOscillatorProfile_le a.property n hvala hmasseq ξ
    have hsame : (⟨(a : ℝ), a.property⟩ : GaloisForLFunctions.RHTower.ProlatePositiveAperture)
        = a := Subtype.ext rfl
    rw [hsame] at h
    exact h
  have hBsup0 : 0 ≤ Bsup := le_trans (abs_nonneg _) (hsup 0)
  have hint : Integrable fun x =>
      GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x :=
    integrable_bounded_mul hvcont hsup (hermiteFun_package (2 * n)).1
  -- the window floor
  have hwin : F1 ≤ |∫ x in (-K₀)..K₀, oscProfile (2 * ((2 * n : ℕ) : ℝ) + 1) x
      * hermiteFun (2 * n) x| := by
    rw [abs_integral_oscProfile_mul_hermiteFun_eq hn hK₀pos.le, hF1def]
    have habs : (0 : ℝ) < |hermiteFun (2 * n) 0| := abs_pos.2 hφ0
    gcongr
    exact integral_hermiteFun_sq_mono hK₀1
  have hfloor2 : F1 / 2
      ≤ |∫ x in (-K₀)..K₀, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
          * hermiteFun (2 * n) x| := by
    refine le_trans ?_ hwinfloor
    linarith [hwin]
  -- the middle region
  have hmid : |(∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
        (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
        GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
      - ∫ x in (-K₀)..K₀,
        GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x|
      ≤ F1 / 8 := by
    have hbase := GaloisForLFunctions.HTGeometry.abs_window_pairing_sub_le_of_secondMoment
      hK₀pos hK₀sc hvcont hφcont
    have hsm : (∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
        (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
        x ^ 2 * GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x ^ 2)
        ≤ (4 * (n : ℝ) + 2) * N := by
      have hle := GaloisForLFunctions.RHTower.indexedOscillatorSecondMoment_le n a
      have hmass0 := GaloisForLFunctions.RHTower.indexedOscillatorTotalMass_nonneg n a
      have hsep0 : 0 ≤ GaloisForLFunctions.RHTower.indexedOscillatorSeparation n a := by
        exact mul_nonneg (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth_pos a).le
          (signedModeRadialData_isExact_of_pos a.property n).2.2.2.2.2.2.2.2.2.2.2.1
      refine le_trans hle ?_
      exact mul_le_mul hsepa hmassa hmass0 (by linarith)
    have hsφ : (∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
        (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
        x ^ 2 * hermiteFun (2 * n) x ^ 2) ≤ Cφ :=
      intervalIntegral_sq_mul_hermiteFun_sq_le (2 * n) hsc.le
    refine le_trans hbase ?_
    have hsum : (∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
        (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
        x ^ 2 * GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x ^ 2)
        + ∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
          (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
          x ^ 2 * hermiteFun (2 * n) x ^ 2 ≤ M := by
      rw [hMdef]
      linarith [hsm, hsφ]
    have hK₀sq0 : (0 : ℝ) < 2 * K₀ ^ 2 := by positivity
    have hstep : 1 / (2 * K₀ ^ 2) * M ≤ F1 / 8 := by
      rw [div_le_iff₀ hF1] at hK₀sq
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hK₀sq0 (by norm_num : (0:ℝ) < 8)]
      nlinarith [hK₀sq, hF1, hM0]
    calc 1 / (2 * K₀ ^ 2) * _ ≤ 1 / (2 * K₀ ^ 2) * M := by
          refine mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ F1 / 8 := hstep
  -- the outer region
  have hout : |(∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
        * hermiteFun (2 * n) x)
      - ∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
        (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
        GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x|
      ≤ F1 / 8 := by
    have h := hCtail (GaloisForLFunctions.RHTower.indexedOscillatorProfile n a) Bsup
      (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) hsc1 hBsup0
      hvcont hsup hint
    exact le_trans h houtera.le
  -- assemble
  have habs1 := abs_sub_abs_le_abs_sub
    (∫ x in (-K₀)..K₀,
      GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
    (∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
  have hcomm := abs_sub_comm
    (∫ x in (-K₀)..K₀,
      GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
    (∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
  have htri : |(∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
        * hermiteFun (2 * n) x)
      - ∫ x in (-K₀)..K₀,
        GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x|
      ≤ F1 / 8 + F1 / 8 := by
    have hsplit : (∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
          * hermiteFun (2 * n) x)
        - ∫ x in (-K₀)..K₀,
          GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x
        = ((∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
              * hermiteFun (2 * n) x)
            - ∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
              (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
              GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
          + ((∫ x in (-Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))..
              (Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)),
              GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
            - ∫ x in (-K₀)..K₀,
              GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                * hermiteFun (2 * n) x) := by ring
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (by linarith [hout, hmid])
  linarith [habs1, htri, hfloor2, hcomm.le, hcomm.ge]


/-- **The two-sided oscillator law with a rate.**  The scaled separation constant of every fixed
canonical prolate mode is within `K·c^{-1/4}` of its even oscillator rung at every large aperture. -/
theorem exists_rate_abs_signedModeRadialBandwidth_mul_s_sub_rung (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ a : ℝ in atTop,
      |signedModeRadialBandwidth a * (signedModeRadialData a n).s - (4 * (n : ℝ) + 1)|
        ≤ K / Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) := by
  classical
  obtain ⟨δ, hδ, hfloor⟩ := exists_floor_abs_integral_indexedOscillator n
  set W : ℝ := ∫ x, |prolateDefectWeight (2 * n) x| with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => abs_nonneg _
  set N : ℝ := sharpInteriorLimit n + 1 with hNdef
  have hSIL : 0 < sharpInteriorLimit n := sharpInteriorLimit_pos n
  have hN0 : 0 ≤ N := by rw [hNdef]; linarith
  set K : ℝ := 2 * (1 + N / 2) * W / (Real.pi * δ) + 1 with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ 2 * (1 + N / 2) * W / (Real.pi * δ) := by
      have : (0 : ℝ) < Real.pi * δ := by positivity
      positivity
    linarith
  refine ⟨K, hK0, ?_⟩
  -- the estimate on the positive-aperture type
  have hlam2 : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹ ≤ 2 := by
    have h := (tendsto_inv_evenProlateSignedValue_sq n).eventually
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
    exact h.mono fun a ha => ha.le
  have hval : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      evenProlateSignedValue (a : ℝ) n ≠ 0 :=
    GaloisForLFunctions.RHTower.tendsto_prolatePositiveAperture_val_atTop.eventually
      (eventually_evenProlateSignedValue_ne_zero n)
  have hc1 : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      (1 : ℝ) ≤ GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a :=
    GaloisForLFunctions.RHTower.tendsto_indexedOscillatorBandwidth_atTop.eventually_ge_atTop _
  have hcomb : ∀ᶠ a : GaloisForLFunctions.RHTower.ProlatePositiveAperture in atTop,
      |GaloisForLFunctions.RHTower.indexedOscillatorSeparation n a - (4 * (n : ℝ) + 1)|
        ≤ K / Real.sqrt (Real.sqrt
            (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) := by
    filter_upwards [hfloor, eventually_indexedOscillatorTotalMass_le n, hlam2, hval, hc1]
      with a hfl hmassa hlama hvala hc1a
    have hc : 0 < GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a :=
      GaloisForLFunctions.RHTower.indexedOscillatorBandwidth_pos a
    have hsc : 0 < Real.sqrt (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a) :=
      Real.sqrt_pos.2 hc
    have hq : 0 < Real.sqrt (Real.sqrt
        (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) := Real.sqrt_pos.2 hsc
    have hsame : (⟨(a : ℝ), a.property⟩ : GaloisForLFunctions.RHTower.ProlatePositiveAperture)
        = a := Subtype.ext rfl
    have hvcont : Continuous (GaloisForLFunctions.RHTower.indexedOscillatorProfile n a) :=
      Differentiable.continuous fun x =>
        (GaloisForLFunctions.RHTower.indexedOscillatorProfile_hasDerivAt n a x).differentiableAt
    set Bsup : ℝ := |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
      * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
        * ((1 + N / 2) / Real.sqrt (Real.sqrt
            (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)))) with hBsupdef
    have hsup : ∀ ξ, |GaloisForLFunctions.RHTower.indexedOscillatorProfile n a ξ| ≤ Bsup := by
      intro ξ
      have hmasseq : GaloisForLFunctions.RHTower.indexedOscillatorTotalMass n
          ⟨(a : ℝ), a.property⟩ ≤ N := by rw [hsame]; exact hmassa
      have h := abs_indexedOscillatorProfile_le a.property n hvala hmasseq ξ
      rw [hsame] at h
      exact h
    have hBsup0 : 0 ≤ Bsup := le_trans (abs_nonneg _) (hsup 0)
    have hR0 : (signedModeRadialData (a : ℝ) n).R 0 ≠ 0 :=
      signedModeRadialData_R_zero_ne_zero a.property n hvala
    have hueq : ∀ ξ, signedModeRescaledProfile (a : ℝ) n ξ
        = (signedModeRadialData (a : ℝ) n).R 0
          * GaloisForLFunctions.RHTower.indexedOscillatorProfile n a ξ := by
      intro ξ
      have h := signedModeRescaledProfile_eq_smul a.property n hvala ξ
      rw [hsame] at h
      exact h
    have hBval : ∀ x, |signedModeRescaledProfile (a : ℝ) n x|
        ≤ |(signedModeRadialData (a : ℝ) n).R 0| * Bsup := by
      intro x
      rw [hueq x, abs_mul]
      exact mul_le_mul_of_nonneg_left (hsup x) (abs_nonneg _)
    have hintv : Integrable fun x =>
        GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x :=
      integrable_bounded_mul hvcont hsup (hermiteFun_package (2 * n)).1
    have hpair : (∫ x, signedModeRescaledProfile (a : ℝ) n x * hermiteFun (2 * n) x)
        = (signedModeRadialData (a : ℝ) n).R 0
          * ∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
              * hermiteFun (2 * n) x := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show signedModeRescaledProfile (a : ℝ) n x * hermiteFun (2 * n) x
        = (signedModeRadialData (a : ℝ) n).R 0
          * (GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x * hermiteFun (2 * n) x)
      rw [hueq x]
      ring
    have hfl' : δ ≤ |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
        * hermiteFun (2 * n) x| := hfl
    have hne : (∫ x, signedModeRescaledProfile (a : ℝ) n x * hermiteFun (2 * n) x) ≠ 0 := by
      rw [hpair]
      refine mul_ne_zero hR0 ?_
      intro h
      rw [h, abs_zero] at hfl'
      linarith
    have hpin := abs_signedMode_scaledSeparation_sub_rung_le a.property n hvala (2 * n)
      hBval hne
    -- rewrite the rung and the pairing
    have hrung : (2 * ((2 * n : ℕ) : ℝ) + 1) = 4 * (n : ℝ) + 1 := by push_cast; ring
    rw [hrung, hpair, abs_mul] at hpin
    have hR0pos : 0 < |(signedModeRadialData (a : ℝ) n).R 0| := abs_pos.2 hR0
    have hbound : |(signedModeRadialData (a : ℝ) n).R 0| * Bsup * W
        / (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
          * (|(signedModeRadialData (a : ℝ) n).R 0|
            * |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                * hermiteFun (2 * n) x|))
        ≤ K / Real.sqrt (Real.sqrt
            (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a)) := by
      have hden : 0 < |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
          * hermiteFun (2 * n) x| := lt_of_lt_of_le hδ hfl'
      rw [div_le_div_iff₀ (by positivity) hq]
      have hBsupval : Bsup * Real.sqrt (Real.sqrt
          (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))
          = |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
            * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
              * (1 + N / 2)) := by
        rw [hBsupdef]
        field_simp
      have hK1 : 2 * (1 + N / 2) * W / (Real.pi * δ) ≤ K := by rw [hKdef]; linarith
      have hlam0 : 0 ≤ |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹ := by positivity
      have hstep : |(signedModeRadialData (a : ℝ) n).R 0| * Bsup * W
          * Real.sqrt (Real.sqrt
            (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))
          ≤ K * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
            * (|(signedModeRadialData (a : ℝ) n).R 0|
              * |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                  * hermiteFun (2 * n) x|)) := by
        have hexp : |(signedModeRadialData (a : ℝ) n).R 0| * Bsup * W
            * Real.sqrt (Real.sqrt
              (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a))
            = |(signedModeRadialData (a : ℝ) n).R 0| * W
              * (|evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
                * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
                  * (1 + N / 2))) := by
          rw [← hBsupval]
          ring
        rw [hexp]
        have hlamle : |evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
            * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
              * (1 + N / 2))
            ≤ 2 * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
              * (1 + N / 2)) := by
          refine mul_le_mul_of_nonneg_right hlama ?_
          have : (0 : ℝ) ≤ 1 + N / 2 := by linarith
          positivity
        have hmid : |(signedModeRadialData (a : ℝ) n).R 0| * W
            * (|evenProlateSignedValue (a : ℝ) n ^ 2|⁻¹
              * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
                * (1 + N / 2)))
            ≤ |(signedModeRadialData (a : ℝ) n).R 0| * W
              * (2 * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
                * (1 + N / 2))) := by
          refine mul_le_mul_of_nonneg_left hlamle ?_
          positivity
        refine le_trans hmid ?_
        have hKdiv : 2 * (1 + N / 2) * W / Real.pi ≤ K * δ := by
          have hKδ : K * δ = 2 * (1 + N / 2) * W / Real.pi + δ := by
            rw [hKdef]
            field_simp
          rw [hKδ]
          linarith
        have hfl2 : δ ≤ |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
            * hermiteFun (2 * n) x| := hfl'
        have hchain : |(signedModeRadialData (a : ℝ) n).R 0|
            * GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
            * (2 * (1 + N / 2) * W / Real.pi)
            ≤ |(signedModeRadialData (a : ℝ) n).R 0|
              * GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
              * (K * |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                  * hermiteFun (2 * n) x|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans hKdiv (mul_le_mul_of_nonneg_left hfl2 hK0.le)
        calc |(signedModeRadialData (a : ℝ) n).R 0| * W
              * (2 * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a / Real.pi
                * (1 + N / 2)))
            = |(signedModeRadialData (a : ℝ) n).R 0|
                * GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
                * (2 * (1 + N / 2) * W / Real.pi) := by ring
          _ ≤ |(signedModeRadialData (a : ℝ) n).R 0|
                * GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
                * (K * |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                    * hermiteFun (2 * n) x|) := hchain
          _ = K * (GaloisForLFunctions.RHTower.indexedOscillatorBandwidth a
                * (|(signedModeRadialData (a : ℝ) n).R 0|
                  * |∫ x, GaloisForLFunctions.RHTower.indexedOscillatorProfile n a x
                      * hermiteFun (2 * n) x|)) := by ring
      linarith [hstep]
    exact le_trans hpin hbound
  -- transfer to the real aperture axis
  obtain ⟨a₀, ha₀⟩ := Filter.eventually_atTop.mp hcomb
  apply Filter.eventually_atTop.mpr
  refine ⟨(a₀ : ℝ), fun a haa => ?_⟩
  have haPos : 0 < a := lt_of_lt_of_le a₀.property haa
  have h := ha₀ ⟨a, haPos⟩ haa
  exact h

end RHTower

end
