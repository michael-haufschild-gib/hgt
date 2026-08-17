import GaloisForLFunctions.RHTower.ProlateLeakageMassIdentity
import GaloisForLFunctions.RHTower.ProlateIndexedTotalMass
import GaloisForLFunctions.RHTower.ProlateIndexedProfileIntegral
import GaloisForLFunctions.RHTower.HermiteLineIntegral
import GaloisForLFunctions.RHTower.ProlateLeakageLowerSharp
import GaloisForLFunctions.RHTower.ProlateExteriorMassBound
import GaloisForLFunctions.RHTower.ProlateLeakageLadderRatio

/-!
# The leakage against the central amplitude, sharply

The exterior mass of the endpoint-normalized radial datum is `Θ(1/c)` — both constants are already
available — and its interior mass is `Θ(c^{-1/2})` times the squared central value, because the
rescaled profile converges to a Hermite function.  Feeding both into the mass quotient gives the
leakage two-sided against a single object:

```text
d_n(a)  ≍  1 / ( sqrt(c) · R(0)² ) .
```

No barrier, no WKB action and no window enter: the exponential is carried entirely by `R(0)`.  This
is the form in which the ratio of two leakages at one aperture reduces to the ratio of two central
amplitudes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The limit of the rescaled interior mass. -/
def sharpInteriorLimit (n : ℕ) : ℝ :=
  (∫ x, hermiteFun (2 * n) x ^ 2) / (hermiteFun (2 * n) 0) ^ 2

theorem sharpInteriorLimit_pos (n : ℕ) : 0 < sharpInteriorLimit n := by
  have hnum : 0 < ∫ x, hermiteFun (2 * n) x ^ 2 := integral_hermiteFun_sq_pos_line (2 * n)
  have hden : (0 : ℝ) < (hermiteFun (2 * n) 0) ^ 2 := by
    have := indexedRungAmplitude_ne_zero n
    rw [indexedRungAmplitude] at this
    positivity
  rw [sharpInteriorLimit]
  positivity

/-- The rescaled total mass is the interior mass in the original variable, normalized by the
squared central value. -/
theorem indexedOscillatorTotalMass_eq (n : ℕ) (a : ProlatePositiveAperture) :
    indexedOscillatorTotalMass n a
      = Real.sqrt (indexedOscillatorBandwidth a)
        * (∫ y in (-1 : ℝ)..1, (signedModeRadialData (a : ℝ) n).R y ^ 2)
        / ((signedModeRadialData (a : ℝ) n).R 0) ^ 2 := by
  have hc : 0 < indexedOscillatorBandwidth a := indexedOscillatorBandwidth_pos a
  rw [indexedOscillatorTotalMass]
  set c : ℝ := indexedOscillatorBandwidth a with hcdef
  set R : ℝ → ℝ := (signedModeRadialData (a : ℝ) n).R with hR
  have hfun : (fun x : ℝ => (indexedOscillatorProfile n a x) ^ 2)
      = fun x : ℝ => (fun y : ℝ => (R y / R 0) ^ 2) (x / Real.sqrt c) := rfl
  have hcov : (∫ x in (-Real.sqrt c)..(Real.sqrt c),
        (fun y : ℝ => (R y / R 0) ^ 2) (x / Real.sqrt c))
      = Real.sqrt c * ∫ y in (-1 : ℝ)..1, (R y / R 0) ^ 2 :=
    integral_comp_div_sqrt hc (fun y : ℝ => (R y / R 0) ^ 2)
  have hdiv : (∫ y in (-1 : ℝ)..1, (R y / R 0) ^ 2)
      = (∫ y in (-1 : ℝ)..1, R y ^ 2) / (R 0) ^ 2 := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext y
    rw [div_pow]
  rw [hfun, hcov, hdiv]
  ring

/-- **The rescaled interior mass converges.** -/
theorem tendsto_indexedOscillatorTotalMass (n : ℕ) :
    Tendsto (fun a : ProlatePositiveAperture => indexedOscillatorTotalMass n a)
      atTop (𝓝 (sharpInteriorLimit n)) := by
  have hκ : (hermiteFun (2 * n) 0) ≠ 0 := by
    have := indexedRungAmplitude_ne_zero n
    rwa [indexedRungAmplitude] at this
  have hbase := tendsto_indexedRung_totalMass n
  have hdiv := hbase.div_const ((hermiteFun (2 * n) 0) ^ 2)
  refine hdiv.congr fun a => ?_
  rw [indexedRungAmplitude]
  field_simp

/-- The interior-mass limit on the aperture axis. -/
theorem tendsto_interiorMass_ratio_atTop (n : ℕ) :
    Tendsto (fun a : ℝ =>
        Real.sqrt (signedModeRadialBandwidth a)
          * (∫ y in (-1 : ℝ)..1, (signedModeRadialData a n).R y ^ 2)
          / ((signedModeRadialData a n).R 0) ^ 2)
      atTop (𝓝 (sharpInteriorLimit n)) := by
  have hmap : Filter.map (Subtype.val :
      GaloisForLFunctions.RHTower.ProlatePositiveAperture → ℝ) atTop = atTop := by
    refine Filter.map_val_atTop_of_Ici_subset (a := (1 : ℝ)) (s := {x : ℝ | 0 < x}) ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    exact lt_of_lt_of_le zero_lt_one hx1
  have h := (tendsto_indexedOscillatorTotalMass n).congr
    (fun a => indexedOscillatorTotalMass_eq n a)
  rw [← hmap, Filter.tendsto_map'_iff]
  exact h

/-- **The leakage against the central amplitude, two-sided.**  Both bounds carry the same power
`c^{-1/2}` and the same object `R(0)²`; only the constants differ. -/
theorem eventually_signedLeakage_sharp_two_sided (n : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      (signedModeRadialData a n).R 0 ≠ 0 ∧
      besselEnergyFloor / 1728 / sharpInteriorLimit n
          / (Real.sqrt (signedModeRadialBandwidth a) * (signedModeRadialData a n).R 0 ^ 2)
        ≤ evenProlateSignedLeakage a n ∧
      evenProlateSignedLeakage a n
        ≤ 4 * radialProlateExteriorMassConstant / sharpInteriorLimit n
          / (Real.sqrt (signedModeRadialBandwidth a) * (signedModeRadialData a n).R 0 ^ 2) := by
  have hSIL : 0 < sharpInteriorLimit n := sharpInteriorLimit_pos n
  have hF : 0 < besselEnergyFloor := besselEnergyFloor_pos
  have hM : (0 : ℝ) ≤ radialProlateExteriorMassConstant := radialProlateExteriorMassConstant_nonneg
  have hT : (0 : ℝ) ≤ radialProlateDensityTransferConstant :=
    radialProlateDensityTransferConstant_nonneg
  have hlim := tendsto_interiorMass_ratio_atTop n
  have hlow : ∀ᶠ a : ℝ in atTop,
      sharpInteriorLimit n / 2
        ≤ Real.sqrt (signedModeRadialBandwidth a)
            * (∫ y in (-1 : ℝ)..1, (signedModeRadialData a n).R y ^ 2)
            / ((signedModeRadialData a n).R 0) ^ 2 :=
    (hlim.eventually (eventually_gt_nhds (by linarith))).mono fun a h => h.le
  have hhigh : ∀ᶠ a : ℝ in atTop,
      Real.sqrt (signedModeRadialBandwidth a)
          * (∫ y in (-1 : ℝ)..1, (signedModeRadialData a n).R y ^ 2)
          / ((signedModeRadialData a n).R 0) ^ 2
        ≤ 2 * sharpInteriorLimit n :=
    (hlim.eventually (eventually_lt_nhds (by linarith))).mono fun a h => h.le
  have hσlim := evenProlateSignedValue_sq_tendsto_one n
  have hσ : ∀ᶠ a : ℝ in atTop, 1 / 2 < evenProlateSignedValue a n ^ 2 :=
    hσlim.eventually (eventually_gt_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_signedModeRadialData_isExact n,
    eventually_evenProlateSignedValue_ne_zero n, hlow, hhigh, hσ,
    eventually_signedModeRadialData_s_pos n,
    eventually_signedModeRadialData_s_le n (show (0 : ℝ) < 1 / 2 by norm_num),
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop
      (max 8 (1728 * radialProlateDensityTransferConstant / besselEnergyFloor))]
    with a hapos hex hvne hlo hhi hsig hs0 hs2 hcb
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set s : ℝ := (signedModeRadialData a n).s with hsdef
  set R : ℝ → ℝ := (signedModeRadialData a n).R with hRdef
  have hc8 : (8 : ℝ) ≤ c := le_trans (le_max_left _ _) hcb
  have hcT : 1728 * radialProlateDensityTransferConstant / besselEnergyFloor ≤ c :=
    le_trans (le_max_right _ _) hcb
  have hc0 : (0 : ℝ) < c := by linarith
  have hsqc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.2 hc0
  -- the central value is nonzero
  have hM0 : R 0 ^ 2 ≠ 0 := by
    intro hcon
    rw [hcon, div_zero] at hlo
    linarith
  have hM0pos : (0 : ℝ) < R 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hM0)
  have hRne : R 0 ≠ 0 := by
    intro hcon
    exact hM0 (by rw [hcon]; ring)
  -- structural data
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := hex.2.2.2.2.2.1
  have hR1 : R 1 = 1 := hex.2.2.2.2.2.2.2.1
  have hode : ∀ x : ℝ, (x ^ 2 - 1) * deriv (deriv R) x + 2 * x * deriv R x
      - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x = 0 := hex.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hdiff : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hsm).1
  have hdiff2 : Differentiable ℝ (deriv R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hRd : ∀ t : ℝ, HasDerivAt R (deriv R t) t := fun t => (hdiff t).hasDerivAt
  have hDRd : ∀ t : ℝ, HasDerivAt (deriv R) (deriv (deriv R) t) t := fun t => (hdiff2 t).hasDerivAt
  -- exterior mass, two-sided
  have hextup : (∫ x in Ioi (1 : ℝ), R x ^ 2) ≤ radialProlateExteriorMassConstant / c :=
    integral_Ioi_one_radialProlate_sq_le hs0.le hs2 (by linarith) hR1 hRd hDRd hode
  have hint : IntegrableOn (fun x => R x ^ 2) (Ioi (1 : ℝ)) :=
    (integrable_sq_signedModeRadialData hapos n hvne).integrableOn
  have hextlow2 : besselEnergyFloor / 864 / c ≤ ∫ x in Ioi (2 : ℝ), R x ^ 2 :=
    integral_Ioi_radialProlate_sq_ge_half hs0.le hs2 hc8 hcT hR1 hRd hDRd hode
  have hmono : (∫ x in Ioi (2 : ℝ), R x ^ 2) ≤ ∫ x in Ioi (1 : ℝ), R x ^ 2 := by
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards with x using sq_nonneg _
    · filter_upwards with x hx using lt_trans one_lt_two hx
  have hextlow : besselEnergyFloor / 864 / c ≤ ∫ x in Ioi (1 : ℝ), R x ^ 2 := by linarith
  -- interior mass, two-sided
  have hintpos : (0 : ℝ) < ∫ y in (-1 : ℝ)..1, R y ^ 2 :=
    interval_integral_sq_pos_of_endpoint_one hsm.continuous hR1
  have hIlo : sharpInteriorLimit n / 2 * (R 0 ^ 2) / Real.sqrt c
      ≤ ∫ y in (-1 : ℝ)..1, R y ^ 2 := by
    rw [le_div_iff₀ hM0pos] at hlo
    rw [div_le_iff₀ hsqc]
    nlinarith [hlo, hM0pos, hsqc]
  have hIhi : (∫ y in (-1 : ℝ)..1, R y ^ 2)
      ≤ 2 * sharpInteriorLimit n * (R 0 ^ 2) / Real.sqrt c := by
    rw [div_le_iff₀ hM0pos] at hhi
    rw [le_div_iff₀ hsqc]
    nlinarith [hhi, hM0pos, hsqc]
  -- the mass quotient
  have hquot := evenProlateSignedLeakage_eq_mass_quotient hapos n hvne
  have hσ1 : evenProlateSignedValue a n ^ 2 ≤ 1 := by
    have := one_sub_evenProlateSignedValue_sq_nonneg a n
    linarith
  have hσ2 : (1 : ℝ) / 2 ≤ evenProlateSignedValue a n ^ 2 := hsig.le
  set E : ℝ := ∫ x in Ioi (1 : ℝ), R x ^ 2 with hE
  set I : ℝ := ∫ y in (-1 : ℝ)..1, R y ^ 2 with hI
  set V : ℝ := evenProlateSignedValue a n ^ 2 with hV
  set Z : ℝ := R 0 ^ 2 with hZ
  set Q : ℝ := Real.sqrt c with hQ
  have hQ2 : Q * Q = c := Real.mul_self_sqrt hc0.le
  have hQpos : (0 : ℝ) < Q := hsqc
  have hE0 : (0 : ℝ) ≤ E := by
    rw [hE]
    refine setIntegral_nonneg measurableSet_Ioi ?_
    intro x _
    exact sq_nonneg _
  have hYpos : (0 : ℝ) < 2 * sharpInteriorLimit n * Z / Q := by positivity
  have hXpos : (0 : ℝ) < sharpInteriorLimit n / 2 * Z / Q := by positivity
  have hVE : (0 : ℝ) ≤ 2 * V * E := mul_nonneg (by linarith) hE0
  refine ⟨hRne, ?_, ?_⟩
  · have hnum : besselEnergyFloor / 864 / c ≤ 2 * V * E := by
      have h1 : (1 : ℝ) ≤ 2 * V := by linarith
      calc besselEnergyFloor / 864 / c ≤ E := hextlow
        _ = 1 * E := (one_mul E).symm
        _ ≤ (2 * V) * E := mul_le_mul_of_nonneg_right h1 hE0
        _ = 2 * V * E := by ring
    have hstep : besselEnergyFloor / 864 / c / (2 * sharpInteriorLimit n * Z / Q)
        ≤ 2 * V * E / I :=
      div_le_div₀ hVE hnum hintpos hIhi
    have hval : besselEnergyFloor / 864 / c / (2 * sharpInteriorLimit n * Z / Q)
        = besselEnergyFloor / 1728 / sharpInteriorLimit n / (Q * Z) := by
      rw [← hQ2]
      field_simp
      ring
    rw [hquot, ← hval]
    exact hstep
  · have hnum : 2 * V * E ≤ 2 * (radialProlateExteriorMassConstant / c) := by
      have h1 : 2 * V * E ≤ 2 * E := by nlinarith [hσ1, hE0]
      have h2 : 2 * E ≤ 2 * (radialProlateExteriorMassConstant / c) := by linarith [hextup]
      linarith
    have hstep : 2 * V * E / I
        ≤ 2 * (radialProlateExteriorMassConstant / c) / (sharpInteriorLimit n / 2 * Z / Q) :=
      div_le_div₀ (by positivity) hnum hXpos hIlo
    have hval : 2 * (radialProlateExteriorMassConstant / c)
          / (sharpInteriorLimit n / 2 * Z / Q)
        = 4 * radialProlateExteriorMassConstant / sharpInteriorLimit n / (Q * Z) := by
      rw [← hQ2]
      field_simp
      ring
    rw [hquot, ← hval]
    exact hstep

end RHTower

end
