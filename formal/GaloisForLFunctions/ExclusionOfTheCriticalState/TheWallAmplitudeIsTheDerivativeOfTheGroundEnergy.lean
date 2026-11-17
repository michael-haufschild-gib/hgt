import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyOfAConfinedGroundStateCutAtTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheIncrementsOfAConfinedGroundStateAreBoundedByItsConfinementMass
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGlobalTransverseGapAndResponse

/-!
# The wall amplitude is the derivative of the ground energy

Let `F` minimize the confined half-line form at a ratio `R > 0`, with ground energy `λ(R)`,
confinement coefficient `a(R)` and `M = ∫ F² e^{−8u}`, and let `ℓ` be its amplitude at the wall:
`√log(1/|u|) F(u) → ℓ` essentially as `u → 0⁻` and `L_F(k)/√log(1/k) → 2ℓ` (`IsWallAmplitude`).
Then (`IsWallAmplitude.sq_eq`, `IsWallAmplitude.hasDerivAt_groundEnergy`)

  `ℓ² = 8 a(R) M = −8 R λ'(R)`.

* **The terminal mean** (`IsWallAmplitude.tendsto_terminalMean`):
  `k⁻¹ ∫_{−k}^0 F · √log(1/k) → ℓ`, since `1 − √log(1/k)/√log(1/t) ≤ log(k/t)/(2 log(1/k))` for
  `t ≤ k` and `k⁻¹ ∫_0^k log(k/t) dt = 1`.
* **Lower bound** (`IsWallAmplitude.eight_mul_exponentialMass_le`). The wall energy inequality of
  the cut state, divided by `k`: the terminal gap costs `8 a M`, the pairing across the cut is at
  most `(L_F(k)/2k) ∫_{−k}^0 F ≤ (|ℓ| + ε)²`, and the remaining terms vanish with `F` at the wall.
* **Upper bound** (`IsWallAmplitude.sq_le_eight_mul_exponentialMass`). Cauchy–Schwarz on
  `(−k, 0)` and the upper bound for the modulus of continuity:
  `(k⁻¹ ∫_{−k}^0 F)² log(1/k) ≤ log(1/k)/k · ∫ (F − τ_k F)² ≤ 8 a M + ε`.

Consequences: `ℓ² ≥ 8 a(R) > 0`, and every confined ground state has the strict sign of its
amplitude almost everywhere near the wall (`IsWallAmplitude.exists_ae_mul_pos`).
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The amplitude -/

/-- `ℓ` is the amplitude of `F` at the wall: `L_F(k)/√log(1/k) → 2ℓ` as `k → 0⁺` and
`√log(1/|u|) F(u) → ℓ` essentially as `u → 0⁻`. -/
def IsWallAmplitude (F : ℝ → ℝ) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℝ => wallLogMoment F k / Real.sqrt (Real.log (1 / k))) (𝓝[>] 0)
      (𝓝 (2 * ℓ)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ k : ℝ, 0 < k ∧ ∀ᵐ u : ℝ, -k < u → u < 0 →
      |Real.sqrt (Real.log (1 / (-u))) * F u - ℓ| ≤ ε

/-- Every confined ground state has an amplitude at the wall. -/
theorem halfLineEnergyMinimizer_exists_isWallAmplitude {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) : ∃ ℓ : ℝ, IsWallAmplitude F ℓ :=
  halfLineEnergyMinimizer_exists_wallAmplitude hR hF

/-- The essential limit on a collar inside `(−1/4, 0)`. -/
theorem IsWallAmplitude.exists_ae_abs_mul_le {F : ℝ → ℝ} {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ)
    {ε : ℝ} (hε : 0 < ε) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 4 ∧ ∀ᵐ u : ℝ, -k < u → u < 0 →
      |wallRootLog (-u) * F u - ℓ| ≤ ε := by
  obtain ⟨k₁, hk₁, h₁⟩ := hℓ.2 ε hε
  refine ⟨min k₁ (1 / 4), lt_min hk₁ (by norm_num), min_le_right _ _,
    h₁.mono fun u hu h1 h2 => ?_⟩
  exact hu (lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) h1) h2

/-- Below the scale `t` a value within `ε` of the amplitude law is at most
`(|ℓ| + ε)/√log(1/t)`. -/
theorem abs_le_div_wallRootLog {f ℓ ε s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht4 : t ≤ 1 / 4)
    (h : |wallRootLog s * f - ℓ| ≤ ε) : |f| ≤ (|ℓ| + ε) / wallRootLog t := by
  have hw := one_le_wallRootLog (lt_of_lt_of_le hs hst) ht4
  have hwu := wallRootLog_anti hs hst
  have h1 := abs_sub_abs_le_abs_sub (wallRootLog s * f) ℓ
  rw [abs_mul, abs_of_nonneg (by linarith only [hw, hwu] : (0 : ℝ) ≤ wallRootLog s)] at h1
  have h2 := mul_le_mul_of_nonneg_right hwu (abs_nonneg f)
  rw [le_div_iff₀ (lt_of_lt_of_le one_pos hw)]
  linarith only [h, h1, h2]

/-! ### The terminal mean -/

theorem integrableOn_log_neg_Ioo (k : ℝ) :
    IntegrableOn (fun u : ℝ => Real.log (-u)) (Ioo (-k) 0) := by
  have h0 : IntegrableOn Real.log (Ioc 0 k) :=
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := k)).1
  have h1 : Integrable fun u : ℝ => (Ioc 0 k).indicator Real.log (-u) :=
    (h0.integrable_indicator measurableSet_Ioc).comp_neg
  exact (h1.integrableOn (s := Ioo (-k) 0)).congr_fun (fun u hu => by
    show (Ioc 0 k).indicator Real.log (-u) = Real.log (-u)
    exact indicator_of_mem
      (show -u ∈ Ioc 0 k from ⟨by linarith only [hu.2], by linarith only [hu.1]⟩) _)
    measurableSet_Ioo

/-- `∫_{−k}^0 log(−u) du = k log k − k`. -/
theorem integral_Ioo_log_neg {k : ℝ} (hk : 0 ≤ k) :
    ∫ u in Ioo (-k) 0, Real.log (-u) = k * Real.log k - k := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (neg_nonpos.mpr hk),
    intervalIntegral.integral_comp_neg (fun x => Real.log x), neg_zero, neg_neg, integral_log]
  simp

/-- Changing the scale of the root logarithm: if `|s f − ℓ| ≤ ε` and `1 ≤ w ≤ s`, then
`|w f − ℓ| ≤ ε + |ℓ| (s² − w²)/(2w²)`. -/
theorem abs_mul_sub_le_of_scale {w s f ℓ ε : ℝ} (hw : 1 ≤ w) (hws : w ≤ s)
    (h : |s * f - ℓ| ≤ ε) : |w * f - ℓ| ≤ ε + |ℓ| / (2 * w ^ 2) * (s ^ 2 - w ^ 2) := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hs0 : 0 < s := lt_of_lt_of_le hw0 hws
  have hρ0 : 0 ≤ w / s := (div_pos hw0 hs0).le
  have hρ1 : w / s ≤ 1 := (div_le_one hs0).mpr hws
  have hss : w / s * s = w := div_mul_cancel₀ w hs0.ne'
  have e : w * f - ℓ = w / s * (s * f - ℓ) - (1 - w / s) * ℓ := by
    have e0 : w / s * (s * f - ℓ) - (1 - w / s) * ℓ = w / s * s * f - ℓ := by ring
    rw [e0, hss]
  have h1 : 1 - w / s ≤ (s ^ 2 - w ^ 2) / (2 * w ^ 2) := by
    have e1 : 1 - w / s = (s - w) / s := by rw [sub_div, div_self hs0.ne']
    rw [e1, div_le_div_iff₀ hs0 (mul_pos two_pos (pow_pos hw0 2))]
    have h2 : 0 ≤ (s + w) * s - 2 * w ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hws) hw0.le,
        mul_nonneg (sub_nonneg.mpr hws) hs0.le]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hws) h2]
  have t1 : w / s * |s * f - ℓ| ≤ ε :=
    (mul_le_of_le_one_left (abs_nonneg _) hρ1).trans h
  have t2 : (1 - w / s) * |ℓ| ≤ (s ^ 2 - w ^ 2) / (2 * w ^ 2) * |ℓ| :=
    mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have t3 := abs_sub (w / s * (s * f - ℓ)) ((1 - w / s) * ℓ)
  rw [abs_mul, abs_mul, abs_of_nonneg hρ0, abs_of_nonneg (sub_nonneg.mpr hρ1)] at t3
  have e3 : |ℓ| / (2 * w ^ 2) * (s ^ 2 - w ^ 2) = (s ^ 2 - w ^ 2) / (2 * w ^ 2) * |ℓ| := by ring
  rw [e, e3]
  linarith only [t1, t2, t3]

/-- **The terminal mean against the amplitude law.** If `|√log(1/|u|) F(u) − ℓ| ≤ ε` almost
everywhere on `(−k, 0)`, `k ≤ 1/4`, then
`|k⁻¹ ∫_{−k}^0 F · √log(1/k) − ℓ| ≤ ε + |ℓ|/(2 log(1/k))`. -/
theorem abs_terminalMean_mul_wallRootLog_sub_le {F : ℝ → ℝ} (hF1 : Integrable F) {ℓ ε k : ℝ}
    (hk : 0 < k) (hk4 : k ≤ 1 / 4)
    (h : ∀ᵐ u : ℝ, -k < u → u < 0 → |wallRootLog (-u) * F u - ℓ| ≤ ε) :
    |(∫ u in Ioo (-k) 0, F u) / k * wallRootLog k - ℓ| ≤
      ε + |ℓ| / (2 * wallRootLog k ^ 2) := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = wallRootLog k := ⟨_, rfl⟩
  rw [← hwdef]
  have hw1 : 1 ≤ w := by
    rw [hwdef]
    exact one_le_wallRootLog hk hk4
  have hw2 : w ^ 2 = -Real.log k := by
    rw [hwdef]
    exact wallRootLog_sq hk hk4
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = |ℓ| / (2 * w ^ 2) := ⟨_, rfl⟩
  rw [← hAdef]
  have hFi : IntegrableOn F (Ioo (-k) 0) := hF1.integrableOn
  have hlogi := integrableOn_log_neg_Ioo k
  have hc1 : IntegrableOn (fun _ : ℝ => ε) (Ioo (-k) 0) :=
    integrableOn_const (hs := measure_Ioo_lt_top.ne)
  have hc2 : IntegrableOn (fun _ : ℝ => Real.log k) (Ioo (-k) 0) :=
    integrableOn_const (hs := measure_Ioo_lt_top.ne)
  have hcℓ : IntegrableOn (fun _ : ℝ => ℓ) (Ioo (-k) 0) :=
    integrableOn_const (hs := measure_Ioo_lt_top.ne)
  have hd : IntegrableOn (fun u : ℝ => Real.log k - Real.log (-u)) (Ioo (-k) 0) :=
    hc2.sub hlogi
  have hAd : IntegrableOn (fun u : ℝ => A * (Real.log k - Real.log (-u))) (Ioo (-k) 0) :=
    hd.const_mul A
  have hgi : IntegrableOn (fun u : ℝ => ε + A * (Real.log k - Real.log (-u))) (Ioo (-k) 0) :=
    hc1.add hAd
  have hvol : volume.real (Ioo (-k) (0 : ℝ)) = k := by
    rw [Real.volume_real_Ioo_of_le (by linarith only [hk]), zero_sub, neg_neg]
  have hgint : ∫ u in Ioo (-k) 0, (ε + A * (Real.log k - Real.log (-u))) = ε * k + A * k := by
    rw [integral_add hc1 hAd, integral_const_mul, integral_sub hc2 hlogi, setIntegral_const,
      setIntegral_const, hvol, integral_Ioo_log_neg hk.le, smul_eq_mul, smul_eq_mul]
    ring
  have hint : ∫ u in Ioo (-k) 0, (w * F u - ℓ) = w * (∫ u in Ioo (-k) 0, F u) - k * ℓ := by
    rw [integral_sub (hFi.const_mul w) hcℓ, integral_const_mul, setIntegral_const, hvol,
      smul_eq_mul]
  have hdiff : (∫ u in Ioo (-k) 0, F u) / k * w - ℓ =
      (∫ u in Ioo (-k) 0, (w * F u - ℓ)) / k := by
    rw [hint, eq_div_iff hk.ne']
    have hc := div_mul_cancel₀ (∫ u in Ioo (-k) 0, F u) hk.ne'
    linear_combination w * hc
  have hpt : ∀ᵐ u ∂(volume.restrict (Ioo (-k) 0)),
      ‖w * F u - ℓ‖ ≤ ε + A * (Real.log k - Real.log (-u)) := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h] with u hu hmem
    have hpos : 0 < -u := by linarith only [hmem.2]
    have hle : -u ≤ k := by linarith only [hmem.1]
    have hs := abs_mul_sub_le_of_scale hw1 (by
      rw [hwdef]
      exact wallRootLog_anti hpos hle) (hu hmem.1 hmem.2)
    rw [wallRootLog_sq hpos (hle.trans hk4), ← hAdef, hw2] at hs
    have e : -Real.log (-u) - -Real.log k = Real.log k - Real.log (-u) := by ring
    rw [e] at hs
    rw [Real.norm_eq_abs]
    exact hs
  have hle := norm_integral_le_of_norm_le hgi hpt
  rw [hgint, Real.norm_eq_abs] at hle
  rw [hdiff, abs_div, abs_of_pos hk, div_le_iff₀ hk]
  linarith only [hle]

/-- **The law of the terminal mean at every ratio.** `k⁻¹ ∫_{−k}^0 F · √log(1/k) → ℓ` as
`k → 0⁺`. -/
theorem IsWallAmplitude.tendsto_terminalMean {F : ℝ → ℝ} (hF1 : Integrable F) {ℓ : ℝ}
    (hℓ : IsWallAmplitude F ℓ) :
    Tendsto (fun k : ℝ => (∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k)))
      (𝓝[>] 0) (𝓝 ℓ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k₁, hk₁, hk₁4, h₁⟩ := hℓ.exists_ae_abs_mul_le (half_pos hε)
  have hbig : ∀ᶠ k : ℝ in 𝓝[>] 0, |ℓ| / ε < wallRootLog k :=
    tendsto_wallRootLog_nhdsGT_zero.eventually_gt_atTop _
  filter_upwards [hbig, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hk₁)] with k hkw hk0 hkk
  have hk0' : (0 : ℝ) < k := hk0
  have hkk' : k < k₁ := hkk
  have hk4 : k ≤ 1 / 4 := hkk'.le.trans hk₁4
  have hw1 := one_le_wallRootLog hk0' hk4
  have hest := abs_terminalMean_mul_wallRootLog_sub_le hF1 hk0' hk4
    (h₁.mono fun u hu h1 h2 => hu (by linarith only [h1, hkk']) h2)
  have hsmall : |ℓ| / (2 * wallRootLog k ^ 2) < ε / 2 := by
    rw [div_lt_iff₀ (mul_pos two_pos (pow_pos (lt_of_lt_of_le one_pos hw1) 2))]
    have h1 : |ℓ| < wallRootLog k * ε := (div_lt_iff₀ hε).mp hkw
    have h2 : wallRootLog k ≤ wallRootLog k ^ 2 := by nlinarith only [hw1]
    nlinarith only [h1, mul_le_mul_of_nonneg_right h2 hε.le]
  rw [Real.dist_eq]
  show |(∫ u in Ioo (-k) 0, F u) / k * wallRootLog k - ℓ| < ε
  linarith only [hest, hsmall]

/-! ### The lower bound: the cut state -/

theorem tendsto_wallRootLog_two_mul_nhdsGT_zero :
    Tendsto (fun k : ℝ => wallRootLog (2 * k)) (𝓝[>] 0) atTop := by
  have h : Continuous fun k : ℝ => 2 * k := by fun_prop
  have h0 := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [mul_zero] at h0
  have h2k : Tendsto (fun k : ℝ => 2 * k) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 ?_
    filter_upwards [self_mem_nhdsWithin] with k hk
    show (0 : ℝ) < 2 * k
    exact mul_pos two_pos (show (0 : ℝ) < k from hk)
  exact tendsto_wallRootLog_nhdsGT_zero.comp h2k

/-- **The amplitude dominates the confinement mass.** For a minimizer `F` at ratio `R` with
amplitude `ℓ` and every `ε > 0`, `8 a(R) ∫ F² e^{−8u} ≤ (|ℓ| + ε)²`. In the wall energy
inequality of the state cut at `−k`, divided by `k`, the terminal gap costs
`8 a M / (1 + 8k)`, the pairing across the cut is at most `(|ℓ| + ε)²`, and the remaining terms
are bounded by a multiple of `(|ℓ| + ε)/√log(1/2k)`. -/
theorem IsWallAmplitude.eight_mul_exponentialMass_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) {ε : ℝ}
    (hε : 0 < ε) :
    8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ (|ℓ| + ε) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := halfLineEnergyMinimizer_exists_wall_energy_le hR hF
  obtain ⟨k₁, hk₁, hk₁4, h₁⟩ := hℓ.exists_ae_abs_mul_le hε
  have ha := criticalAliasCoefficient_positive hR
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = criticalAliasCoefficient R := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = |ℓ| + ε := ⟨_, rfl⟩
  have hS : 0 < S := by
    rw [hSdef]
    exact add_pos_of_nonneg_of_pos (abs_nonneg ℓ) hε
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [← hadef] at ha hK
  rw [← hadef, ← hMdef, ← hSdef]
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = K + 1 + a * Real.exp 1 := ⟨_, rfl⟩
  -- the comparison function and its limit
  have hinv : Tendsto (fun k : ℝ => (wallRootLog (2 * k))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_wallRootLog_two_mul_nhdsGT_zero
  have hlin : Tendsto (fun k : ℝ => 1 + 8 * k) (𝓝[>] 0) (𝓝 (1 + 8 * 0)) := by
    have h : Continuous fun k : ℝ => 1 + 8 * k := by fun_prop
    exact (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun k : ℝ => (1 + 8 * k) * (S ^ 2 + c * (S * (wallRootLog (2 * k))⁻¹)))
      (𝓝[>] 0) (𝓝 ((1 + 8 * 0) * (S ^ 2 + c * (S * 0)))) :=
    hlin.mul (tendsto_const_nhds.add ((hinv.const_mul S).const_mul c))
  have hval : (1 + 8 * 0) * (S ^ 2 + c * (S * 0)) = S ^ 2 := by ring
  rw [hval] at hlim
  refine ge_of_tendsto hlim ?_
  have hLt := (Metric.tendsto_nhds.mp hℓ.1) (2 * ε) (by linarith only [hε])
  have hw2big : ∀ᶠ k : ℝ in 𝓝[>] 0, S ≤ wallRootLog (2 * k) :=
    tendsto_wallRootLog_two_mul_nhdsGT_zero.eventually_ge_atTop S
  filter_upwards [hLt, hw2big, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iio_mem_nhds (show (0 : ℝ) < k₁ / 2 by linarith only [hk₁]))] with k hLk hwk hk0 hkk
  show 8 * a * M ≤ (1 + 8 * k) * (S ^ 2 + c * (S * (wallRootLog (2 * k))⁻¹))
  have hk : (0 : ℝ) < k := hk0
  have hkk' : k < k₁ / 2 := hkk
  have hk8 : k ≤ 1 / 8 := by linarith only [hkk', hk₁4]
  -- the scales `√log(1/k)` and `√log(1/2k)`
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = wallRootLog k := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by
    rw [hwdef]
    exact one_le_wallRootLog hk (by linarith only [hk8])
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw1
  have hw21 := one_le_wallRootLog (show (0 : ℝ) < 2 * k by linarith only [hk])
    (show 2 * k ≤ 1 / 4 by linarith only [hk8])
  have hw20 : 0 < wallRootLog (2 * k) := lt_of_lt_of_le one_pos hw21
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = S / wallRootLog (2 * k) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact div_nonneg hS.le hw20.le
  have hB1 : B ≤ 1 := by
    rw [hBdef, div_le_one hw20]
    exact hwk
  -- the size of the state on `[−2k, 0)` and its integral over `(−k, 0)`
  have hB : ∀ᵐ u : ℝ, -(2 * k) ≤ u → u < 0 → |F u| ≤ B :=
    h₁.mono fun u hu h1 h2 => by
      rw [hBdef, hSdef]
      exact abs_le_div_wallRootLog (by linarith only [h2]) (by linarith only [h1])
        (by linarith only [hk8]) (hu (by linarith only [h1, hkk']) h2)
  have hI : |∫ u in Ioo (-k) 0, F u| ≤ S / w * k := by
    have h := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (s := Ioo (-k) 0) (f := F)
      (C := S / w) measure_Ioo_lt_top (by
        rw [ae_restrict_iff' measurableSet_Ioo]
        filter_upwards [h₁] with u hu hmem
        rw [Real.norm_eq_abs, hSdef, hwdef]
        exact abs_le_div_wallRootLog (by linarith only [hmem.2]) (by linarith only [hmem.1])
          (by linarith only [hk8]) (hu (by linarith only [hmem.1, hkk', hk₁]) hmem.2))
    rw [Real.volume_real_Ioo_of_le (by linarith only [hk]), zero_sub, neg_neg,
      Real.norm_eq_abs] at h
    exact h
  -- the logarithmic moment
  have hLk' : |wallLogMoment F k / wallRootLog k - 2 * ℓ| < 2 * ε := by
    rw [← Real.dist_eq]
    exact hLk
  rw [← hwdef] at hLk'
  have hLw : |wallLogMoment F k / w| ≤ 2 * S := by
    have h1 := abs_sub_abs_le_abs_sub (wallLogMoment F k / w) (2 * ℓ)
    rw [abs_mul, abs_two] at h1
    rw [hSdef]
    linarith only [h1, hLk']
  have hL : |wallLogMoment F k| ≤ 2 * S * w := by
    have e : |wallLogMoment F k| = |wallLogMoment F k / w| * w := by
      rw [← abs_of_pos hw0, ← abs_mul, abs_of_pos hw0, div_mul_cancel₀ _ hw0.ne']
    rw [e]
    exact mul_le_mul_of_nonneg_right hLw hw0.le
  have hprod : wallLogMoment F k / 2 * (∫ u in Ioo (-k) 0, F u) ≤ S ^ 2 * k := by
    have h1 := le_abs_self (wallLogMoment F k / 2 * ∫ u in Ioo (-k) 0, F u)
    rw [abs_mul, abs_div, abs_two] at h1
    have h2 : |wallLogMoment F k| / 2 * |∫ u in Ioo (-k) 0, F u| ≤ S * w * (S / w * k) :=
      mul_le_mul (by linarith only [hL]) hI (abs_nonneg _) (mul_pos hS hw0).le
    have e : S * w * (S / w * k) = S ^ 2 * k := by
      have e0 : S * w * (S / w * k) = S * (S * k) * (w * w⁻¹) := by ring
      rw [e0, mul_inv_cancel₀ hw0.ne']
      ring
    linarith only [h1, h2, e]
  -- the exponential mass left of the cut
  have hsplit := integral_add_compl (measurableSet_Iio (a := -k)) hF.1.exponential
  rw [compl_Iio, ← hMdef] at hsplit
  have htail : ∫ u in Ici (-k), F u ^ 2 * Real.exp (-(8 * u)) ≤ Real.exp 1 * B ^ 2 * k := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp 1 * B ^ 2) (Icc (-k) 0) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    have h := norm_integral_le_of_norm_le (hconst.integrable_indicator measurableSet_Icc)
      (f := (Ici (-k)).indicator fun u => F u ^ 2 * Real.exp (-(8 * u))) (by
        filter_upwards [hB] with u hu
        by_cases hmem : u ∈ Icc (-k) (0 : ℝ)
        · rw [indicator_of_mem hmem, indicator_of_mem (show u ∈ Ici (-k) from hmem.1),
            Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
          rcases eq_or_lt_of_le hmem.2 with h0 | h0
          · rw [hF.1.support u h0.ge, zero_pow two_ne_zero, zero_mul]
            exact mul_nonneg (Real.exp_pos _).le (sq_nonneg B)
          · have hFu := hu (by linarith only [hmem.1, hk]) h0
            have hsq : F u ^ 2 ≤ B ^ 2 := by
              rw [← sq_abs (F u)]
              exact pow_le_pow_left₀ (abs_nonneg _) hFu 2
            have hexp : Real.exp (-(8 * u)) ≤ Real.exp 1 :=
              Real.exp_le_exp.mpr (by linarith only [hmem.1, hk8])
            calc F u ^ 2 * Real.exp (-(8 * u)) ≤ B ^ 2 * Real.exp 1 :=
                  mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg B)
              _ = Real.exp 1 * B ^ 2 := mul_comm _ _
        · rw [indicator_of_notMem hmem]
          by_cases hm2 : u ∈ Ici (-k)
          · have h0 : 0 < u := by
              by_contra hn
              exact hmem ⟨hm2, not_lt.mp hn⟩
            rw [indicator_of_mem hm2, hF.1.support u h0.le, zero_pow two_ne_zero, zero_mul,
              norm_zero]
          · rw [indicator_of_notMem hm2, norm_zero])
    rw [integral_indicator measurableSet_Ici, integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith only [hk]), smul_eq_mul, Real.norm_eq_abs] at h
    have h' := (le_abs_self _).trans h
    linarith only [h']
  -- the cost of the terminal gap
  have hE1 := Real.exp_pos (-(8 * k))
  have h3 : (8 * k + 1) * Real.exp (-(8 * k)) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (8 * k)) hE1.le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h1
  have h4 : 0 ≤ k * Real.exp (-(8 * k)) := mul_nonneg hk.le hE1.le
  have hgap1 : 0 ≤ 1 - Real.exp (-(8 * k)) := by linarith only [h3, h4]
  have hgap2 : 1 - Real.exp (-(8 * k)) ≤ 1 := by linarith only [hE1]
  have hgap3 : 8 * k ≤ (1 - Real.exp (-(8 * k))) * (1 + 8 * k) := by linarith only [h3]
  -- the wall energy inequality
  have hmain := hK k hk (by linarith only [hk8]) B hB0 hB
  have p1 := mul_le_mul_of_nonneg_left
    (show M ≤ (∫ u in Iio (-k), F u ^ 2 * Real.exp (-(8 * u))) + Real.exp 1 * B ^ 2 * k by
      linarith only [hsplit, htail]) (mul_nonneg ha.le hgap1)
  have hnn : 0 ≤ Real.exp 1 * B ^ 2 * k :=
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le (sq_nonneg B)) hk.le
  have p2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap2 ha.le) hnn
  have p3 : B ^ 2 ≤ B := by
    rw [pow_two]
    exact mul_le_of_le_one_left hB0 hB1
  have p4 := mul_le_mul_of_nonneg_right p3 hk.le
  have p5 := mul_le_mul_of_nonneg_left p4 (mul_nonneg ha.le (Real.exp_pos 1).le)
  have hX : a * (1 - Real.exp (-(8 * k))) * M ≤ k * (S ^ 2 + c * B) := by
    rw [hcdef]
    linarith only [p1, p2, p4, p5, hmain, hprod]
  have q1 := mul_le_mul_of_nonneg_left hgap3 (mul_nonneg ha.le hM0)
  have q2 := mul_le_mul_of_nonneg_left hX (by linarith only [hk] : (0 : ℝ) ≤ 1 + 8 * k)
  have hfin : 8 * a * M * k ≤ (1 + 8 * k) * (S ^ 2 + c * B) * k := by
    linarith only [q1, q2]
  have hgoal := le_of_mul_le_mul_right hfin hk
  rw [hBdef, div_eq_mul_inv] at hgoal
  exact hgoal

/-! ### The upper bound: the modulus of continuity -/

/-- **The confinement mass dominates the amplitude.** `ℓ² ≤ 8 a(R) ∫ F² e^{−8u}`: Cauchy–Schwarz
on `(−k, 0)`, the upper bound for the modulus of continuity and the law of the terminal mean. -/
theorem IsWallAmplitude.sq_le_eight_mul_exponentialMass {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) :
    ℓ ^ 2 ≤ 8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hup := halfLineEnergyMinimizer_eventually_log_mul_sq_increment_le hR hF hε
  have hmean := (hℓ.tendsto_terminalMean hF.1.integrable).pow 2
  refine le_of_tendsto hmean ?_
  filter_upwards [hup, self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with k hk hk0 hk1
  show ((∫ u in Ioo (-k) 0, F u) / k * Real.sqrt (Real.log (1 / k))) ^ 2 ≤
    8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + ε
  have hk0' : (0 : ℝ) < k := hk0
  have hk1' : k < 1 := hk1
  have hL : 0 ≤ Real.log (1 / k) :=
    Real.log_nonneg (by rw [le_div_iff₀ hk0']; linarith only [hk1'])
  have h1 := sq_terminalMean_mul_log_le hF.1.meas hF.1.sq hk0' hk1'
  have h2 := setIntegral_Ioo_sq_le_integral_sq_increment hF.1 hk0'
  have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hL hk0'.le)
  have h4 : Real.log (1 / k) / k * ∫ u, (F u - F (u + k)) ^ 2 ≤
      8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk0']
    exact hk
  rw [mul_pow, Real.sq_sqrt hL]
  linarith only [h1, h3, h4]

/-! ### The formula -/

/-- **The wall amplitude is fixed by the confinement mass.** For a minimizer `F` of the confined
form at a ratio `R > 0` with amplitude `ℓ` at the wall, `ℓ² = 8 a(R) ∫ F² e^{−8u}`. -/
theorem IsWallAmplitude.sq_eq {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) :
    ℓ ^ 2 = 8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  refine le_antisymm (hℓ.sq_le_eight_mul_exponentialMass hR hF) ?_
  have h : Continuous fun ε : ℝ => (|ℓ| + ε) ^ 2 := by fun_prop
  have ht := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [add_zero, sq_abs] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hℓ.eight_mul_exponentialMass_le hR hF hε

/-- **The wall amplitude is the derivative of the ground energy.** At every ratio `R > 0` the
ground energy of the confined form has derivative `λ'(R) = −ℓ²/(8R)`, `ℓ` the amplitude at the
wall of a ground state at `R`. -/
theorem IsWallAmplitude.hasDerivAt_groundEnergy {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) :
    HasDerivAt criticalHalfLineGroundEnergy (-(ℓ ^ 2) / (8 * R)) R := by
  have h := hF.hasDerivAt_criticalHalfLineGroundEnergy hR
  have e : -(criticalAliasCoefficient R) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / R =
      -(ℓ ^ 2) / (8 * R) := by
    rw [hℓ.sq_eq hR hF, div_eq_div_iff hR.ne' (mul_pos (by norm_num) hR).ne']
    ring
  rw [e] at h
  exact h

/-- The amplitude is bounded below by the confinement coefficient: `ℓ² ≥ 8 a(R)`. -/
theorem IsWallAmplitude.eight_mul_aliasCoefficient_le_sq {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) :
    8 * criticalAliasCoefficient R ≤ ℓ ^ 2 := by
  have ha := criticalAliasCoefficient_positive hR
  have hM : 1 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
    have h := hF.1.square_mass_le_exponential_mass
    rwa [hF.2.1] at h
  rw [hℓ.sq_eq hR hF]
  have h := mul_le_mul_of_nonneg_left hM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) ha.le)
  rwa [mul_one] at h

/-- The amplitude of a confined ground state never vanishes. -/
theorem IsWallAmplitude.ne_zero {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) : ℓ ≠ 0 := by
  intro h0
  have h := hℓ.eight_mul_aliasCoefficient_le_sq hR hF
  rw [h0, zero_pow two_ne_zero] at h
  linarith only [h, criticalAliasCoefficient_positive hR]

/-- **Every confined ground state has a strict sign at the wall.** Near the wall `F` has the
sign of its amplitude almost everywhere. -/
theorem IsWallAmplitude.exists_ae_mul_pos {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ℓ : ℝ} (hℓ : IsWallAmplitude F ℓ) :
    ∃ k : ℝ, 0 < k ∧ ∀ᵐ u : ℝ, -k < u → u < 0 → 0 < ℓ * F u := by
  have habs : 0 < |ℓ| := abs_pos.mpr (hℓ.ne_zero hR hF)
  obtain ⟨k, hk, hk4, h⟩ := hℓ.exists_ae_abs_mul_le (half_pos habs)
  refine ⟨k, hk, h.mono fun u hu h1 h2 => ?_⟩
  have hw : 1 ≤ wallRootLog (-u) :=
    one_le_wallRootLog (by linarith only [h2]) (by linarith only [h1, hk4])
  have hb := hu h1 h2
  have h3 : -(|ℓ| * (|ℓ| / 2)) ≤ ℓ * (wallRootLog (-u) * F u - ℓ) := by
    have h4 := neg_abs_le (ℓ * (wallRootLog (-u) * F u - ℓ))
    rw [abs_mul] at h4
    have h5 := mul_le_mul_of_nonneg_left hb (abs_nonneg ℓ)
    linarith only [h4, h5]
  have h6 : |ℓ| * |ℓ| = ℓ * ℓ := abs_mul_abs_self ℓ
  have h7 : 0 < |ℓ| * |ℓ| := mul_pos habs habs
  have hpos : 0 < wallRootLog (-u) * (ℓ * F u) := by
    linarith only [h3, h6, h7]
  exact (mul_pos_iff_of_pos_left (lt_of_lt_of_le one_pos hw)).mp hpos

/-- **The wall amplitude of every confined ground state.** Every minimizer `F` of the confined
form at a ratio `R > 0` has an amplitude `ℓ` at the wall with
`ℓ² = 8 a(R) ∫ F² e^{−8u} = −8 R λ'(R)`. -/
theorem halfLineEnergyMinimizer_exists_wallAmplitude_sq {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ ℓ : ℝ, IsWallAmplitude F ℓ ∧
      ℓ ^ 2 = 8 * criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ∧
      HasDerivAt criticalHalfLineGroundEnergy (-(ℓ ^ 2) / (8 * R)) R := by
  obtain ⟨ℓ, hℓ⟩ := halfLineEnergyMinimizer_exists_isWallAmplitude hR hF
  exact ⟨ℓ, hℓ, hℓ.sq_eq hR hF, hℓ.hasDerivAt_groundEnergy hR hF⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
