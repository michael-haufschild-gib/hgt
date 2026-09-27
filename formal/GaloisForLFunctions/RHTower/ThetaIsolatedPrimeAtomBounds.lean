import GaloisForLFunctions.RHTower.ThetaFinitePrimeAtomPolarization
import GaloisForLFunctions.RHTower.CCMPrimeGapCrossBound
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# Isolation and continuous-interaction bounds at genuine prime atoms

Each integer logarithm above the regular-kernel sign threshold has a positive
isolation radius. The critical von Mangoldt weight tends to zero. The continuous
interaction of two narrow support balls is bounded by their radius times the
total physical mass, retaining the complete signed Gamma/pole kernel.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard GaloisForLFunctions.RHTower

theorem abs_thetaGammaPolarGroundCrossPairing_balls_le
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    {c₁ c₂ r : ℝ} (hr : 0 ≤ r)
    (hp : Function.support phi ⊆ Metric.ball c₁ r)
    (hq : Function.support psi ⊆ Metric.ball c₂ r)
    (hgap : screwSignThreshold ≤ c₂ - c₁ - 2 * r) :
    |thetaGammaPolarGroundCrossPairing phi psi| ≤
      (Real.exp ((c₂ - c₁ + 2 * r) / 2) * r) *
        (thetaGroundNormSq (thetaComplexify phi) + thetaGroundNormSq (thetaComplexify psi)) := by
  obtain ⟨A, hA, hbound⟩ := (hpc.union hqc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inl hx))
  have hqs : tsupport psi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x (Or.inr hx))
  have hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      screwSignThreshold < x - y ∧ x - y ≤ c₂ - c₁ + 2 * r := by
    intro x hx y hy
    have hx' := hq hx
    have hy' := hp hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx' hy'
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  rw [thetaGammaPolarGroundCrossPairing_eq_ccm_screw a phi psi hpc hqc hps hqs
    (fun x hx y hy => screwSignThreshold_pos.trans (hsep x hx y hy).1),
    thetaGroundNormSq_compactReal_eq_physical a phi hpc hps,
    thetaGroundNormSq_compactReal_eq_physical a psi hqc hqs]
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := ccmThetaSourceOfCompactRealProfile a psi hqc hqs
  have hus : Function.support u = Function.support phi := support_ccmThetaSourceOfCompactRealProfile _ _ _ _
  have hvs : Function.support v = Function.support psi := support_ccmThetaSourceOfCompactRealProfile _ _ _ _
  have hc := abs_screwRegularForm_ccm_le_l1 u v (by rwa [hus, hvs])
  have hm := ccmSmooth_l1_product_le_ball_mass_sum u v hr
    (by rwa [hus]) (by rwa [hvs])
  exact hc.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)

theorem exists_logNat_isolating_radius {n : ℕ} (hn : 2 ≤ n) :
    ∃ e : ℝ, 0 < e ∧ screwSignThreshold ≤ Real.log n - e ∧
      ∀ m : ℕ, 2 ≤ m → |Real.log m - Real.log n| < e → m = n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp0 : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hprev : Real.log (n - 1 : ℕ) < Real.log n :=
    Real.log_lt_log hp0 (by exact_mod_cast (by omega : n - 1 < n))
  have hnext : Real.log n < Real.log (n + 1 : ℕ) :=
    Real.log_lt_log hn0 (by exact_mod_cast Nat.lt_succ_self n)
  have hthreshold : screwSignThreshold < Real.log n := by
    unfold screwSignThreshold
    exact Real.log_lt_log plasticRoot_pos
      (plasticRoot_mem_Ioo.2.trans_le (by exact_mod_cast hn))
  let e := min (Real.log n - Real.log (n - 1 : ℕ))
    (min (Real.log (n + 1 : ℕ) - Real.log n) (Real.log n - screwSignThreshold))
  have he : 0 < e := lt_min (sub_pos.mpr hprev)
    (lt_min (sub_pos.mpr hnext) (sub_pos.mpr hthreshold))
  have heprev : e ≤ Real.log n - Real.log (n - 1 : ℕ) := min_le_left _ _
  have henext : e ≤ Real.log (n + 1 : ℕ) - Real.log n :=
    (min_le_right _ _).trans (min_le_left _ _)
  have het : e ≤ Real.log n - screwSignThreshold :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨e, he, by linarith, fun m hm hdist => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨hl, hu⟩ := abs_lt.mp hdist
  rcases lt_trichotomy m n with hmn | heq | hnm
  · have h := Real.log_le_log hm0 (show (m : ℝ) ≤ (n - 1 : ℕ) by
      exact_mod_cast (by omega : m ≤ n - 1))
    linarith
  · exact heq
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ))
      (show ((n + 1 : ℕ) : ℝ) ≤ m by exact_mod_cast hnm)
    linarith

theorem tendsto_vonMangoldt_div_sqrt_zero :
    Tendsto (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n) atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa only [pow_one, Real.sqrt_eq_rpow] using
      HTGeometry.tendsto_logPow_div_rpow (by norm_num : (0 : ℝ) < 1 / 2) 1
  exact squeeze_zero (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (fun n => div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _))
    (h.comp tendsto_natCast_atTop_atTop)

end RHTower
