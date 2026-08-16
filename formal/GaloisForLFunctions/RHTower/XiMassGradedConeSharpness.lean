import GaloisForLFunctions.RHTower.XiMassSubthresholdConeSharpness
import GaloisForLFunctions.RHTower.XiMassGradedBesselConePhase

/-!
# Sharpness of the graded cone slope

The exterior action `Γ_a(κ) = κ/2 − a√(κ²−1)` is strictly decreasing on `κ > 1`, so the graded
slope `κ_{a,λ}` solving `Γ_a(κ) = λ` is the exact threshold: every smaller slope has
`Γ_a(κ) > λ`, and Theorem 17.5 then produces an annulus of size `c u^{-1/2} e^{Γ_a(κ) u}`, which
is not of vertical type `λ`.

Together with the graded criterion this closes the cone/type phase diagram: allowed vertical type
`λ` corresponds exactly to minimal raw cone slope `κ_{a,λ}`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **The cone exponent is strictly increasing in the slope.** -/
theorem xiMassBesselConeExponent_strictMono {a kappa kappa' : ℝ} (ha : 1 / 2 < a)
    (hkappa : 1 < kappa) (hkk : kappa < kappa') :
    xiMassBesselConeExponent a kappa < xiMassBesselConeExponent a kappa' := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa' : 1 < kappa' := lt_trans hkappa hkk
  have h2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have h2' : (0 : ℝ) ≤ kappa' ^ 2 - 1 := by nlinarith
  have hs : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt h2
  have hs' : Real.sqrt (kappa' ^ 2 - 1) ^ 2 = kappa' ^ 2 - 1 := Real.sq_sqrt h2'
  have hsnn : 0 ≤ Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_nonneg _
  have hsnn' : 0 ≤ Real.sqrt (kappa' ^ 2 - 1) := Real.sqrt_nonneg _
  have hsk : Real.sqrt (kappa ^ 2 - 1) < kappa := by nlinarith
  have hsk' : Real.sqrt (kappa' ^ 2 - 1) < kappa' := by nlinarith
  have hspos' : 0 < Real.sqrt (kappa' ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
  have hsum : 0 < Real.sqrt (kappa ^ 2 - 1) + Real.sqrt (kappa' ^ 2 - 1) := by linarith
  have hid : (Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1))
      * (Real.sqrt (kappa' ^ 2 - 1) + Real.sqrt (kappa ^ 2 - 1)) = kappa' ^ 2 - kappa ^ 2 := by
    nlinarith [hs, hs']
  have hkey : (kappa' - kappa) / 2 * (Real.sqrt (kappa ^ 2 - 1) + Real.sqrt (kappa' ^ 2 - 1))
      < a * ((Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1))
        * (Real.sqrt (kappa' ^ 2 - 1) + Real.sqrt (kappa ^ 2 - 1))) := by
    rw [hid]
    have hpos : (0 : ℝ) < (kappa' - kappa) * (kappa + kappa') := by nlinarith
    nlinarith [hpos, hsk, hsk']
  have hdiv : (kappa' - kappa) / 2
      < a * (Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1)) := by
    by_contra hcon
    have hcon' : a * (Real.sqrt (kappa' ^ 2 - 1) - Real.sqrt (kappa ^ 2 - 1))
        ≤ (kappa' - kappa) / 2 := not_lt.mp hcon
    have hmul := mul_le_mul_of_nonneg_right hcon' hsum.le
    nlinarith [hkey, hmul]
  rw [xiMassBesselConeExponent, xiMassBesselConeExponent]
  linarith

/-- **(20.4) Below the graded slope the moving annulus is not of vertical type `λ`.** -/
theorem not_bigO_subgradedAnnulus {a sigma kappa mu lam : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hlam : 0 ≤ lam) (hlamhalf : lam ≤ 1 / 2) (hkappa : 1 < kappa)
    (hsub : kappa < xiMassGradedConeSlope a lam) (hkm : kappa < mu) :
    ¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope mu) u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖
        ≤ C * Real.exp (lam * u) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, u₀, hc, hu₀, hlow⟩ := exists_subthreshold_annulus_lower_bound ha hsigma hkappa hkm
  have hstrict : xiMassBesselConeExponent a kappa
      < xiMassBesselConeExponent a (xiMassGradedConeSlope a lam) :=
    xiMassBesselConeExponent_strictMono ha hkappa hsub
  have hval := xiMassBesselConeExponent_gradedConeSlope ha hlam hlamhalf
  have hgap : (0 : ℝ) < -(xiMassBesselConeExponent a kappa) - lam := by linarith
  -- the growth of the surviving exponent
  have hbase : Tendsto (fun u : ℝ =>
      Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u) / u ^ ((1 : ℝ) / 2))
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (1 / 2) (-(xiMassBesselConeExponent a kappa) - lam) hgap
  have hcongr : Tendsto (fun u : ℝ =>
      Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u) / Real.sqrt u)
      atTop atTop := by
    refine hbase.congr fun u => ?_
    rw [Real.sqrt_eq_rpow]
  have hgrow : Tendsto (fun u : ℝ =>
      c * (Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u) / Real.sqrt u))
      atTop atTop := hcongr.const_mul_atTop hc
  obtain ⟨u, ⟨⟨hbig, huu₀⟩, hu1⟩⟩ :=
    (((hgrow.eventually_ge_atTop (C + 1)).and (eventually_ge_atTop u₀)).and
      (eventually_ge_atTop (1 : ℝ))).exists
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hexp : (0 : ℝ) < Real.exp (lam * u) := Real.exp_pos _
  have hchain : c * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u)
      ≤ C * Real.exp (lam * u) := le_trans (hlow u huu₀) (hC u hupos.le)
  have hsplit : Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u)
      * Real.exp (lam * u) = Real.exp (-(xiMassBesselConeExponent a kappa) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hupos
  have hcalc : c * (Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u) / Real.sqrt u)
      * Real.exp (lam * u) ≤ C * Real.exp (lam * u) := by
    calc c * (Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u) / Real.sqrt u)
          * Real.exp (lam * u)
        = c * ((Real.exp ((-(xiMassBesselConeExponent a kappa) - lam) * u)
            * Real.exp (lam * u)) / Real.sqrt u) := by ring
      _ = c * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u) := by
          rw [hsplit]
      _ ≤ C * Real.exp (lam * u) := hchain
  have hle := le_of_mul_le_mul_right hcalc hexp
  linarith

end

end RHTower
