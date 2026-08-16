import GaloisForLFunctions.RHTower.XiMassSubthresholdDivergence

/-!
# Sharpness of the Bessel balance slope

Below the balance slope `κ_B = a/√(a²−1/4)` the cone exponent `η_κ = a√(κ²−1) − κ/2` is strictly
negative, so the lower bound of the subthreshold annulus grows like `u^{-1/2} e^{|η_κ| u}`.  Hence
for every `1 < κ < κ_B` and every `λ > κ` the annular difference of the two finite true-prime
cones is unbounded, while at and above `κ_B` the same difference is uniformly bounded.

The balance slope is therefore exactly the threshold for bounded-coboundary equivalence of
unrenormalized prime prefixes.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Below the balance slope the cone exponent is strictly negative. -/
theorem xiMassBesselConeExponent_neg {a kappa : ℝ} (ha : 1 / 2 < a) (hkappa : 1 < kappa)
    (hsharp : kappa < xiMassSpacelikeSharpSlope a) :
    xiMassBesselConeExponent a kappa < 0 := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < a ^ 2 - 1 / 4 := by nlinarith
  have hk : (0 : ℝ) < Real.sqrt (a ^ 2 - 1 / 4) := Real.sqrt_pos.2 hden
  have hksq : Real.sqrt (a ^ 2 - 1 / 4) ^ 2 = a ^ 2 - 1 / 4 := Real.sq_sqrt hden.le
  have hslope : kappa < a / Real.sqrt (a ^ 2 - 1 / 4) := by
    simpa only [xiMassSpacelikeSharpSlope] using hsharp
  have hmul : kappa * Real.sqrt (a ^ 2 - 1 / 4) < a := by
    rw [lt_div_iff₀ hk] at hslope
    exact hslope
  have hpos : (0 : ℝ) < kappa * Real.sqrt (a ^ 2 - 1 / 4) := mul_pos (by linarith) hk
  have hsq2 : (kappa * Real.sqrt (a ^ 2 - 1 / 4)) ^ 2 < a ^ 2 := by nlinarith
  have hexpand : (kappa * Real.sqrt (a ^ 2 - 1 / 4)) ^ 2 = kappa ^ 2 * (a ^ 2 - 1 / 4) := by
    rw [mul_pow, hksq]
  have hkappa2 : (0 : ℝ) ≤ kappa ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (kappa ^ 2 - 1) ^ 2 = kappa ^ 2 - 1 := Real.sq_sqrt hkappa2
  have hsnn : 0 ≤ Real.sqrt (kappa ^ 2 - 1) := Real.sqrt_nonneg _
  have hkey : (a * Real.sqrt (kappa ^ 2 - 1)) ^ 2 < (kappa / 2) ^ 2 := by
    have hexp : (a * Real.sqrt (kappa ^ 2 - 1)) ^ 2 = a ^ 2 * (kappa ^ 2 - 1) := by
      rw [mul_pow, hsq]
    rw [hexp]
    nlinarith [hsq2, hexpand]
  rw [xiMassBesselConeExponent, sub_neg]
  nlinarith [mul_nonneg ha0.le hsnn]

/-- **The subthreshold annulus diverges.**  For `1 < κ < κ_B` the difference of the finite
true-prime cones at slopes `λ > κ` and `κ` tends to infinity. -/
theorem tendsto_subthreshold_annulus_atTop {a sigma kappa lam : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hsharp : kappa < xiMassSpacelikeSharpSlope a)
    (hkl : kappa < lam) :
    Tendsto (fun u : ℝ =>
        ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
          - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖)
      atTop atTop := by
  obtain ⟨c, u₀, hc, hu₀, hbound⟩ := exists_subthreshold_annulus_lower_bound ha hsigma hkappa hkl
  have hneg : xiMassBesselConeExponent a kappa < 0 := xiMassBesselConeExponent_neg ha hkappa hsharp
  have hbase : Tendsto (fun u : ℝ =>
      Real.exp (-(xiMassBesselConeExponent a kappa) * u) / u ^ (1 / 2 : ℝ)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (1 / 2) (-(xiMassBesselConeExponent a kappa)) (by linarith)
  have hcongr : Tendsto (fun u : ℝ =>
      Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u) atTop atTop := by
    refine hbase.congr fun u => ?_
    rw [Real.sqrt_eq_rpow]
  have hgrow : Tendsto (fun u : ℝ =>
      c * (Real.exp (-(xiMassBesselConeExponent a kappa) * u) / Real.sqrt u)) atTop atTop :=
    hcongr.const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hgrow
  filter_upwards [eventually_ge_atTop u₀] with u hu
  exact hbound u hu

/-- **Sharpness of the balance slope.**  Below it no uniform bound on the annular difference of
finite true-prime cones exists. -/
theorem not_bounded_subthreshold_annulus {a sigma kappa lam : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hsharp : kappa < xiMassSpacelikeSharpSlope a)
    (hkl : kappa < lam) :
    ¬ ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
        ‖xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
          - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u‖ ≤ C := by
  rintro ⟨C, hC⟩
  have hdiv := tendsto_subthreshold_annulus_atTop ha hsigma hkappa hsharp hkl
  obtain ⟨u, hu, hu0⟩ := ((hdiv.eventually_ge_atTop (C + 1)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  linarith [hC u hu0]

end

end RHTower
