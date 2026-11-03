import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNextAliasingCoefficientIsNegative
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive

/-!
# The canonical critical clock enters from the negative side

The non-aliasing horizon error is smaller than the inverse-square overlap
scale. The negative next coefficient of the tilted-spline aliasing therefore
resolves a vanishing leading pencil on the exact critical clock.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticDegenerationTheory ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Every fixed polynomial in the critical overlap and the logarithmic horizon
is smaller than the number of atoms. -/
theorem criticalCurve_pow_log_div_natCast {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) (m n : ℕ) :
    Tendsto (fun N : ℕ => c N ^ m * Real.log N ^ n / N) atTop (𝓝 0) := by
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop, c N ≤ 2 * K * Real.log N := by
    filter_upwards [hcrit.eventually (gt_mem_nhds (by linarith : K < 2 * K)),
      hlogN.eventually (eventually_gt_atTop 0)] with N h1 h2
    simp only [Function.comp_apply] at h2
    rw [div_lt_iff₀ h2] at h1
    have hcc : c N ≤ c N ^ 8 := by
      calc c N = c N ^ 1 := (pow_one _).symm
        _ ≤ c N ^ 8 := pow_le_pow_right₀ (hc1 N) (by norm_num)
    exact hcc.trans h1.le
  have hlim := (tendsto_log_pow_div_natCast (m + n)).const_mul ((2 * K) ^ m)
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => by
    have := hc1 N
    have := Real.log_natCast_nonneg N
    positivity) ?_ hlim
  filter_upwards [hev] with N hN
  have hc0 : 0 ≤ c N := by linarith [hc1 N]
  have hp := pow_le_pow_left₀ hc0 hN m
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (pow_nonneg (Real.log_natCast_nonneg N) n))
    (Nat.cast_nonneg (α := ℝ) N)
  calc c N ^ m * Real.log N ^ n / N ≤
        (2 * K * Real.log N) ^ m * Real.log N ^ n / N := hb
    _ = (2 * K) ^ m * (Real.log N ^ (m + n) / N) := by
      rw [mul_pow, pow_add]
      ring

/-- The quadratic overlap correction dominates the logarithmic symbol error. -/
theorem criticalCurve_sq_div_log {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 / Real.log N) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc1 hK hcrit).1
  have h6 := (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp hcinf
  have h := hcrit.mul (tendsto_inv_atTop_zero.comp h6)
  simp only [mul_zero] at h
  refine h.congr fun N => ?_
  have hc : c N ≠ 0 := by linarith [hc1 N]
  simp only [Function.comp_apply]
  calc c N ^ 8 / Real.log N * (c N ^ 6)⁻¹ =
        c N ^ 2 * (c N ^ 6 * (c N ^ 6)⁻¹) / Real.log N := by ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 6 hc), mul_one]

/-- A logarithm does not destroy the integrability of the low-frequency
Kuzmin–Landau majorant. -/
theorem integrable_decayWeight_mul_log {Aν : ℝ} (hAν : 0 ≤ Aν) :
    Integrable (fun τ : ℝ => decayWeight τ * (Aν + Real.log (2 + |τ|))) := by
  have hi : Integrable (fun τ : ℝ => (Aν + 8) * (1 + ‖τ‖) ^ (-(5 / 4 : ℝ))) :=
    (integrable_one_add_norm (by norm_num)).const_mul _
  refine hi.mono' ?_ (Eventually.of_forall fun τ => ?_)
  · dsimp only [decayWeight]
    fun_prop
  have ht : 0 ≤ |τ| := abs_nonneg τ
  have hbase : 0 < 1 + |τ| := by positivity
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (by positivity : 0 ≤ 2 + |τ|)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hp : (2 + |τ|) ^ (1 / 4 : ℝ) ≤ 2 * (1 + |τ|) ^ (1 / 4 : ℝ) := by
    calc (2 + |τ|) ^ (1 / 4 : ℝ) ≤ (2 * (1 + |τ|)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (1 / 4 : ℝ) :=
          Real.mul_rpow (by norm_num) hbase.le
      _ ≤ 2 * (1 + |τ|) ^ (1 / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbase.le _)
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one _
  have hpow1 : 1 ≤ (1 + |τ|) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hnum : Aν + Real.log (2 + |τ|) ≤ (Aν + 8) * (1 + |τ|) ^ (1 / 4 : ℝ) := by
    have hA := mul_le_mul_of_nonneg_left hpow1 hAν
    nlinarith only [hlog, hp, hA]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (decayWeight_nonneg τ) (by positivity)),
    decayWeight_eq, Real.norm_eq_abs]
  calc (1 + |τ|) ^ (-(3 / 2 : ℝ)) * (Aν + Real.log (2 + |τ|))
      ≤ (1 + |τ|) ^ (-(3 / 2 : ℝ)) * ((Aν + 8) * (1 + |τ|) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnum (Real.rpow_nonneg hbase.le _)
    _ = (Aν + 8) * (1 + |τ|) ^ (-(5 / 4 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hbase]
      norm_num


/-- The low-frequency symbol converges quantitatively, with a cubic cutoff cost. -/
theorem abs_lowFrequency_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N → ∀ R : ℝ, 1 ≤ R →
      R ≤ N * Real.exp (-A) →
      |(∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
          horizonSymbolIntegrand φ h c N (Real.exp (2 * (A + 1))) τ) -
          (∫ u, φ u) ^ 2 * ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
            nuSymbol (Real.exp (2 * (A + 1))) τ| ≤
        K * (Real.sqrt (c / N) + 1 / Real.sqrt R + R ^ 3 / N) := by
  let X := Real.exp (2 * (A + 1))
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (X := X) (Real.exp_pos _).le
  let V : ℝ → ℝ := fun τ => Aν + Real.log (2 + |τ|)
  have hV0 (τ : ℝ) : 0 ≤ V τ := by
    have hl : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
    exact add_nonneg hAν hl
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  obtain ⟨Cd, hCd⟩ : ∃ Cd, Cd = 2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 *
    windowConst A Bh L ^ 2) := ⟨_, rfl⟩
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  obtain ⟨I₀, hI₀⟩ : ∃ I₀, I₀ = ∫ u, |φ u| := ⟨_, rfl⟩
  have hI₀0 : 0 ≤ I₀ := by rw [hI₀]; exact integral_nonneg fun u => abs_nonneg _
  have hI₁ : (∫ u, φ u) ^ 2 ≤ I₀ ^ 2 := by
    rw [hI₀, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) abs_integral_le_integral_abs 2
  obtain ⟨C₄, hC₄⟩ : ∃ C₄, C₄ = ∫ τ, decayWeight τ * V τ := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := by
    rw [hC₄]
    exact integral_nonneg fun τ => mul_nonneg (decayWeight_nonneg τ) (hV0 τ)
  obtain ⟨C₅, hC₅⟩ : ∃ C₅, C₅ = ((Lh : ℝ) + 2 * Bh) * Real.exp (2 * A) := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; positivity
  have hHle : ∀ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 ≤ Cd / (1 + τ ^ 2) :=
    fun τ => hCd ▸ normSq_horizonTransform_le hh hA hsupp hB hL τ
  have hHn : ∀ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ≤ Real.sqrt Cd := fun τ =>
    Real.le_sqrt_of_sq_le ((hHle τ).trans (div_le_self hCd0 (by nlinarith [sq_nonneg τ])))
  refine ⟨8 * I₀ ^ 2 * Cd * C₄ + 4 * I₀ ^ 2 * Cd * C₄ +
    2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd) * (Aν + 3), by positivity,
      fun c hc N hN R hR hRT => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 ≤ c / N := by positivity
  have hRN : R ≤ N := hRT.trans (mul_le_of_le_one_right hN0.le
    (Real.exp_le_one_iff.mpr (by linarith)))
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  -- the Riemann-sum error on `|τ| ≤ R`
  have hDH : ∀ τ : ℝ, |τ| ≤ R → |‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N -
      ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2| ≤
        C₅ * R / N * (C₅ + 2 * Real.sqrt Cd) := by
    intro τ hτ
    refine (abs_normSq_div_sub_le hh hA hsupp hB hLh hN τ (hHn τ)).trans ?_
    have hE1 : ((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A) / N ≤ C₅ * R / N := by
      rw [hC₅]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [mul_assoc, mul_comm _ R, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have : (Lh : ℝ) ≤ Lh * R := le_mul_of_one_le_right (NNReal.coe_nonneg _) hR
      nlinarith
    have hE2 : C₅ * R / N ≤ C₅ := by
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hRN hC₅0
    exact mul_le_mul hE1 (by linarith) (by positivity) (by positivity)
  have hpt := abs_indicator_sub_le (P := fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2)
    (Dn := fun τ : ℝ => ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)
    (Hh := fun τ : ℝ => ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2)
    (I₁s := (∫ u, φ u) ^ 2) (I₀s := I₀ ^ 2) (sw := Real.sqrt (c / N))
    (T₀ := (N : ℝ) * Real.exp (-A)) hR hRT (sq_nonneg _) hI₁ hCd0 (Real.sqrt_nonneg _)
    (fun τ => by positivity) (fun τ => by positivity) (fun τ => by positivity)
    (fun τ => by
      have := RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) (c / N * τ)
      rw [show (((c / N * τ : ℝ)) : ℂ) = ((c / N : ℝ) : ℂ) * τ by push_cast; ring] at this
      have h' : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ≤ I₀ := by
        rw [hI₀]; simpa [cx, Complex.norm_real, Real.norm_eq_abs] using this
      exact pow_le_pow_left₀ (norm_nonneg _) h' 2)
    hHle (fun τ hτ => hCd ▸ horizonDirichlet_sq_div_le hsupp hA hB hL hN hτ)
    (fun τ => by
      have := abs_normSq_paperFT_sub_le hφ.continuous hφsupp hw0 τ
      rwa [← hI₀, Real.sqrt_mul hw0] at this)
    hDH
  let a := 8 * I₀ ^ 2 * Cd * Real.sqrt (c / N) + 4 * I₀ ^ 2 * Cd / Real.sqrt R
  let Z := I₀ ^ 2 * (C₅ * R / N * (C₅ + 2 * Real.sqrt Cd))
  have ha : 0 ≤ a := by positivity
  have hZ : 0 ≤ Z := by positivity
  have hVR (τ : ℝ) (hτ : τ ∈ Set.Icc (-R) R) : V τ ≤ (Aν + 3) * R := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |τ|)
    have hτR := abs_le.mpr hτ
    have hAR := le_mul_of_one_le_right hAν hR
    dsimp only [V]
    nlinarith only [hl, hτR, hAR, hR]
  have hptW (τ : ℝ) :
      |Set.indicator (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
        (horizonSymbolIntegrand φ h c N X) τ - (∫ u, φ u) ^ 2 *
          (‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 * nuSymbol X τ)| ≤
      a * (decayWeight τ * V τ) +
        Set.indicator (Set.Icc (-R) R) (fun _ => Z * (Aν + 3) * R) τ := by
    have hid : Set.indicator
        (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
        (horizonSymbolIntegrand φ h c N X) τ - (∫ u, φ u) ^ 2 *
          (‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 * nuSymbol X τ) =
        (Set.indicator (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
          (fun τ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)) τ -
          (∫ u, φ u) ^ 2 * ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2) * nuSymbol X τ := by
      by_cases hm : τ ∈ Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A))
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, horizonSymbolIntegrand]
        ring
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
        ring
    rw [hid, abs_mul]
    have hbase := hpt τ
    change _ ≤ a * decayWeight τ + Set.indicator (Set.Icc (-R) R) (fun _ => Z) τ at hbase
    have hz0 : 0 ≤ Set.indicator (Set.Icc (-R) R) (fun _ => Z) τ := by
      by_cases hm : τ ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem hm]; exact hZ
      · rw [Set.indicator_of_notMem hm]
    have hzV : Set.indicator (Set.Icc (-R) R) (fun _ => Z) τ * V τ ≤
        Set.indicator (Set.Icc (-R) R) (fun _ => Z * (Aν + 3) * R) τ := by
      by_cases hm : τ ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hVR τ hm) hZ
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    calc _ ≤ (a * decayWeight τ + Set.indicator (Set.Icc (-R) R) (fun _ => Z) τ) * V τ :=
          mul_le_mul hbase (hν τ) (abs_nonneg _) (add_nonneg (mul_nonneg ha (decayWeight_nonneg τ)) hz0)
      _ ≤ _ := by nlinarith only [hzV]
  have hfi : Integrable (Set.indicator
      (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))
      (horizonSymbolIntegrand φ h c N X)) :=
    (integrable_horizonSymbolIntegrand hφ hφsupp h hc hN (2 * (A + 1))).indicator measurableSet_Icc
  have hW : ContDiff ℝ 2 (halfWeight h) :=
    (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hh
  have hWc : HasCompactSupport (halfWeight h) :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
      simp only [halfWeight, hsupp y hy, mul_zero]
  have hbase := integrable_normSq_paperFT_mul_nuSymbol hW hWc (2 * (A + 1))
  have hgi : Integrable fun τ : ℝ => (∫ u, φ u) ^ 2 *
      (‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 * nuSymbol X τ) := by
    apply Integrable.const_mul
    refine hbase.congr (Eventually.of_forall fun τ => ?_)
    dsimp only
    rw [← paperFT_halfWeight_gammaOf, gammaOf_half_add]
  have hdi : Integrable (fun τ : ℝ => decayWeight τ * V τ) :=
    integrable_decayWeight_mul_log hAν
  have hci : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => Z * (Aν + 3) * R)) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hei := (hdi.const_mul a).add hci
  rw [← integral_indicator measurableSet_Icc, ← integral_const_mul, ← integral_sub hfi hgi]
  refine abs_integral_le_integral_abs.trans ((integral_mono (hfi.sub hgi).abs hei hptW).trans ?_)
  simp only [Pi.add_apply]
  rw [integral_add (hdi.const_mul a) hci, integral_const_mul,
    integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def, Real.volume_Icc,
    smul_eq_mul, ENNReal.toReal_ofReal (by linarith), ← hC₄]
  have heq : a * C₄ + (R - -R) * (Z * (Aν + 3) * R) =
      8 * I₀ ^ 2 * Cd * C₄ * Real.sqrt (c / N) +
      4 * I₀ ^ 2 * Cd * C₄ * (1 / Real.sqrt R) +
      (2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd) * (Aν + 3)) * (R ^ 3 / N) := by
    dsimp only [a, Z]
    ring
  rw [heq]
  have h1 : 0 ≤ Real.sqrt (c / N) := Real.sqrt_nonneg _
  have h2 : 0 ≤ 1 / Real.sqrt R := by positivity
  have h3 : 0 ≤ R ^ 3 / N := by positivity
  have k1 : 0 ≤ 8 * I₀ ^ 2 * Cd * C₄ := by positivity
  have k2 : 0 ≤ 4 * I₀ ^ 2 * Cd * C₄ := by positivity
  have k3 : 0 ≤ 2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd) * (Aν + 3) := by positivity
  nlinarith only [mul_nonneg k1 h2, mul_nonneg k1 h3, mul_nonneg k2 h1, mul_nonneg k2 h3,
    mul_nonneg k3 h1, mul_nonneg k3 h2]

/-- The symbol below the grid has error smaller than the quadratic overlap
correction on a critical clock. -/
theorem criticalCurve_sq_mul_lowFrequency {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 * ((∫ τ in
      Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
        horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ) -
      (∫ u, φ u) ^ 2 * ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
        nuSymbol (Real.exp (2 * (A + 1))) τ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := abs_lowFrequency_sub_le hφ hφsupp hh hA hsupp
  have hcInf := (criticalCurve_facts hc1 hK hcrit).1
  have h6N : Tendsto (fun N : ℕ => c N ^ 6 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 6 0
  have hR : ∀ᶠ N : ℕ in atTop, c N ^ 6 ≤ N * Real.exp (-A) := by
    filter_upwards [h6N.eventually (gt_mem_nhds (Real.exp_pos (-A))),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1
    simpa only [mul_comm (Real.exp (-A)) (N : ℝ)] using h1.le
  have h5N : Tendsto (fun N : ℕ => c N ^ 5 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 5 0
  have h20N : Tendsto (fun N : ℕ => c N ^ 20 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 20 0
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp h5N
  simp only [Real.sqrt_zero] at hsqrt
  have hinv := tendsto_inv_atTop_zero.comp hcInf
  have ht := ((hsqrt.add hinv).add h20N).const_mul C
  simp only [add_zero, mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hR, eventually_ge_atTop 1] with N hRN hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hb := hbound (c N) hc0 N hN (c N ^ 6) (one_le_pow₀ (hc1 N)) hRN
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  refine (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq ?_
  have hs1 : Real.sqrt (c N ^ 5 / N) = c N ^ 2 * Real.sqrt (c N / N) := by
    rw [show c N ^ 5 / N = (c N ^ 2) ^ 2 * (c N / N) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]
  have hs2 : Real.sqrt (c N ^ 6) = c N ^ 3 := by
    rw [show c N ^ 6 = (c N ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  dsimp only [Function.comp_def]
  rw [hs1, hs2]
  field_simp

/-- The energy defect is smaller than the quadratic correction on the critical clock. -/
theorem criticalCurve_sq_log_mul_energyDefect (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 * (Real.log N * (blockEnergy φ h (c N) N - lowPart φ h (c N) N A -
      2 * Real.pi * horizonAlias φ h (c N) N))) atTop (𝓝 0) := by
  have hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0) := by
    simpa only [pow_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 1 2
  obtain ⟨K₁, hK₁0, hK₁⟩ := abs_blockEnergy_sub_le hφ hφsupp hh hsupp (A := A)
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_abs_riemann_sq_sub_le hh hA hsupp
  obtain ⟨K₃, hK₃0, hK₃⟩ := abs_lowPart_sub_le hφ hφsupp hh hA hsupp
  set I₁ := ∫ u, φ u with hI₁
  have hhat := integral_normSq_horizonTransform hh hsupp
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => by
      have := hc1 N; positivity) ?_ hclog
    filter_upwards [hev3] with N hN
    have hc0 : 0 ≤ c N / N := by have := hc1 N; positivity
    calc c N / N = c N / N * 1 := (mul_one _).symm
      _ ≤ c N / N * Real.log N ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc0
      _ = c N * Real.log N ^ 2 / N := by ring
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hR4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / N) atTop (𝓝 0) := tendsto_log_pow_div_natCast 4
  have hevR : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 ≤ N * Real.exp (-A) := by
    filter_upwards [hR4.eventually (gt_mem_nhds (Real.exp_pos (-A))), eventually_ge_atTop 1]
      with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  -- the bound
  set B : ℕ → ℝ := fun N => Real.log N * (K₁ * c N / N + 2 * Real.pi * I₁ ^ 2 * (K₂ / N) +
    K₃ * (Real.sqrt (c N / N) + 1 / Real.sqrt (Real.log N ^ 4) + (Real.log N ^ 4) ^ 2 / N))
    with hB
  have hbound : ∀ᶠ N : ℕ in atTop, ‖Real.log N * (blockEnergy φ h (c N) N -
      lowPart φ h (c N) N A - 2 * Real.pi * horizonAlias φ h (c N) N)‖ ≤ B N := by
    filter_upwards [hev3, hev4, hevR, eventually_ge_atTop 1] with N h3 h4 hR hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog0 : 0 ≤ Real.log N := by linarith
    have hR1 : 1 ≤ Real.log N ^ 4 := one_le_pow₀ h3
    have e1 := hK₁ (c N) (hc1 N) N h4
    have e2 := hK₂ N hN
    have e3 := hK₃ (c N) (by linarith [hc1 N]) N hN _ hR1 hR
    rw [hhat] at e3
    have hsplit : blockEnergy φ h (c N) N - lowPart φ h (c N) N A -
        2 * Real.pi * horizonAlias φ h (c N) N =
        (blockEnergy φ h (c N) N - (2 * Real.pi / N * I₁ ^ 2 *
          ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 + 2 * Real.pi * horizonAlias φ h (c N) N)) +
        2 * Real.pi * I₁ ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 -
          ∫ y, Real.exp y * h y ^ 2) -
        (lowPart φ h (c N) N A - I₁ ^ 2 * (2 * Real.pi * ∫ y, Real.exp y * h y ^ 2)) := by
      field_simp; ring
    rw [hsplit, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0, hB]
    refine mul_le_mul_of_nonneg_left ?_ hlog0
    have hI0 : 0 ≤ 2 * Real.pi * I₁ ^ 2 := by positivity
    calc _ ≤ |blockEnergy φ h (c N) N - (2 * Real.pi / N * I₁ ^ 2 *
          ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 + 2 * Real.pi * horizonAlias φ h (c N) N)| +
        |2 * Real.pi * I₁ ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 -
          ∫ y, Real.exp y * h y ^ 2)| +
        |lowPart φ h (c N) N A - I₁ ^ 2 * (2 * Real.pi * ∫ y, Real.exp y * h y ^ 2)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ K₁ * c N / N + 2 * Real.pi * I₁ ^ 2 * (K₂ / N) +
          K₃ * (Real.sqrt (c N / N) + 1 / Real.sqrt (Real.log N ^ 4) + (Real.log N ^ 4) ^ 2 / N) := by
          rw [abs_mul, abs_of_nonneg hI0]
          gcongr
  have t1 := criticalCurve_pow_log_div_natCast hc1 hK hcrit 3 1
  have t2 := criticalCurve_pow_log_div_natCast hc1 hK hcrit 2 1
  have t5 := criticalCurve_pow_log_div_natCast hc1 hK hcrit 2 9
  simp only [pow_one] at t1 t2
  have t3 : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N * Real.sqrt (c N / N))
      atTop (𝓝 0) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp
      (criticalCurve_pow_log_div_natCast hc1 hK hcrit 5 2)
    simp only [Real.sqrt_zero] at ht
    refine ht.congr fun N => ?_
    dsimp only [Function.comp_def]
    have hlog0 := Real.log_natCast_nonneg N
    rw [show c N ^ 5 * Real.log N ^ 2 / N =
      (c N ^ 2 * Real.log N) ^ 2 * (c N / N) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have t4 : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N *
      (1 / Real.sqrt (Real.log N ^ 4))) atTop (𝓝 0) := by
    refine (criticalCurve_sq_div_log hc1 hK hcrit).congr' ?_
    filter_upwards [hev3] with N hN
    rw [show Real.log N ^ 4 = (Real.log N ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    field_simp
  have ht := ((t1.const_mul K₁).add (t2.const_mul (2 * Real.pi * I₁ ^ 2 * K₂))).add
    (((t3.add t4).add t5).const_mul K₃)
  simp only [mul_zero, add_zero] at ht
  have hBlim : Tendsto (fun N => c N ^ 2 * B N) atTop (𝓝 0) := ht.congr fun N => by
    dsimp only [B]
    ring
  refine squeeze_zero_norm' ?_ hBlim
  filter_upwards [hbound] with N hN
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left hN (sq_nonneg _)

/-- On a critical clock, every fixed complex atom frequency has error smaller
than the quadratic overlap correction. -/
theorem criticalCurve_sq_mul_atom_factor {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) (z : ℂ) :
    Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      (paperFT (cx φ) (((c N / N : ℝ) : ℂ) * z) - ((∫ u, φ u : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  have hf : Differentiable ℂ (paperFT (cx φ)) :=
    RHTower.EvenSector.differentiable_paperFT_of_compact
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left (g := Complex.ofReal) rfl)
  obtain ⟨C, hC, hbound⟩ := (hf 0).hasFDerivAt.isBigO_sub.exists_pos
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 1 0
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ) * z) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero, zero_mul] using hcN.ofReal.mul_const z
  have h3N := criticalCurve_pow_log_div_natCast hc1 hK hcrit 3 0
  simp only [pow_zero, mul_one] at h3N
  have hlim := h3N.const_mul (C * ‖z‖)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hw.eventually hbound.bound] with N hN
  have hc0 : 0 ≤ c N := by linarith [hc1 N]
  rw [sub_zero, paperFT_cx_zero] at hN
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hnorm : ‖(((c N / N : ℝ) : ℂ) * z)‖ = c N / N * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm] at hN
  calc c N ^ 2 * ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * z) - ((∫ u, φ u : ℝ) : ℂ)‖
      ≤ c N ^ 2 * (C * (c N / N * ‖z‖)) :=
        mul_le_mul_of_nonneg_left hN (sq_nonneg _)
    _ = _ := by ring

/-- The fixed complex Riemann sums converge faster than the inverse-square
critical overlap. -/
theorem criticalCurve_sq_mul_horizonDirichlet {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) :
    Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 * (((N : ℝ) : ℂ) ^ (-s) *
      dirichletPoly N (horizonWeights h N) (gammaOf s) - horizonTransform h s)) atTop (𝓝 0) := by
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have ht := (criticalCurve_pow_log_div_natCast hc1 hK hcrit 2 0).const_mul
    (((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A))
  simp only [pow_zero, mul_one, mul_zero] at ht
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hb := norm_riemannSum_sub_le hh hsupp hA hB hLh hs0 hs2 hN
  rw [riemannSum_horizonProfile h s hN] at hb
  have hc0 : 0 ≤ c N := by linarith [hc1 N]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  refine (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq ?_
  ring

private theorem tendsto_scaled_mul_sub {a u v : ℕ → ℂ} {u0 v0 : ℂ}
    (hv : Tendsto v atTop (𝓝 v0))
    (hu : Tendsto (fun N => a N * (u N - u0)) atTop (𝓝 0))
    (hv' : Tendsto (fun N => a N * (v N - v0)) atTop (𝓝 0)) :
    Tendsto (fun N => a N * (u N * v N - u0 * v0)) atTop (𝓝 0) := by
  have ht := (hu.mul hv).add (hv'.const_mul u0)
  simp only [zero_mul, mul_zero, add_zero] at ht
  exact ht.congr fun N => by ring

/-- Both pole amplitudes have an error smaller than the quadratic correction. -/
theorem criticalCurve_sq_mul_alpha {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      (alphaPlus φ h (c N) N - ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      (alphaMinus φ h (c N) N - ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1)) atTop (𝓝 0) := by
  have hp := tendsto_scaled_mul_sub (tendsto_horizonDirichlet hh.continuous hsupp hA 0)
    (criticalCurve_sq_mul_atom_factor hφ hφc hc1 hK hcrit (Complex.I / 2))
    (criticalCurve_sq_mul_horizonDirichlet hh hsupp hA hc1 hK hcrit
      (s := 0) (by norm_num) (by norm_num))
  have hm := tendsto_scaled_mul_sub (tendsto_horizonDirichlet hh.continuous hsupp hA 1)
    (criticalCurve_sq_mul_atom_factor hφ hφc hc1 hK hcrit (-Complex.I / 2))
    (criticalCurve_sq_mul_horizonDirichlet hh hsupp hA hc1 hK hcrit
      (s := 1) (by norm_num) (by norm_num))
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero, alphaPlus] using hp
  · refine hm.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [alphaMinus, gammaOf_one, Complex.cpow_neg_one]
    push_cast
    field_simp


/-- The two poles contribute no inverse-square correction on a critical clock. -/
theorem criticalCurve_sq_mul_polePart {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 *
      ((alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
        alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re -
        (∫ u, φ u) ^ 2 * (horizonTransform h 0 * conj (horizonTransform h 1) +
          horizonTransform h 1 * conj (horizonTransform h 0)).re)) atTop (𝓝 0) := by
  let p0 := ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 0
  let m0 := ((∫ u, φ u : ℝ) : ℂ) * horizonTransform h 1
  obtain ⟨hp, hm⟩ := criticalCurve_sq_mul_alpha hφ hφc hh hsupp hA hc1 hK hcrit
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 1 0
  have hqp := tendsto_alphaPlus hφ hφc hh.continuous hsupp hA hcN
  have hqm := tendsto_alphaMinus hφ hφc hh.continuous hsupp hA hcN
  have hpc : Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      (conj (alphaPlus φ h (c N) N) - conj p0)) atTop (𝓝 0) := by
    have ht := (Complex.continuous_conj.tendsto 0).comp hp
    simpa only [Function.comp_def, map_mul, map_pow, map_sub, Complex.conj_ofReal, map_zero, p0] using ht
  have hmc : Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      (conj (alphaMinus φ h (c N) N) - conj m0)) atTop (𝓝 0) := by
    have ht := (Complex.continuous_conj.tendsto 0).comp hm
    simpa only [Function.comp_def, map_mul, map_pow, map_sub, Complex.conj_ofReal, map_zero, m0] using ht
  have ht1 := tendsto_scaled_mul_sub ((Complex.continuous_conj.tendsto _).comp hqm) hp hmc
  have ht2 := tendsto_scaled_mul_sub ((Complex.continuous_conj.tendsto _).comp hqp) hm hpc
  have ht : Tendsto (fun N : ℕ => (c N : ℂ) ^ 2 *
      ((alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
        alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)) -
        (p0 * conj m0 + m0 * conj p0))) atTop (𝓝 0) := by
    have hh' := ht1.add ht2
    simp only [add_zero] at hh'
    exact hh'.congr fun N => by
      dsimp only [p0, m0, Function.comp_def]
      ring
  have hval : (p0 * conj m0 + m0 * conj p0).re =
      (∫ u, φ u) ^ 2 * (horizonTransform h 0 * conj (horizonTransform h 1) +
        horizonTransform h 1 * conj (horizonTransform h 0)).re := by
    have heq : p0 * conj m0 + m0 * conj p0 = ((∫ u, φ u) ^ 2 : ℝ) *
        (horizonTransform h 0 * conj (horizonTransform h 1) +
          horizonTransform h 1 * conj (horizonTransform h 0)) := by
      dsimp only [p0, m0]
      rw [map_mul, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [heq, Complex.re_ofReal_mul]
  have hre := (Complex.continuous_re.tendsto 0).comp ht
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.sub_re, hval, Complex.zero_re] using hre

/-- On a critical clock, the non-aliasing horizon remainder is smaller than `c⁻²`. -/
theorem criticalCurve_horizon_remainder {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-(8 : ℝ)))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 * ((c N)⁻¹ *
      (weilQuad (atomicTest N (horizonWeights h N) (atomDilate φ (c N / N))) /
        ∫ u, atomDilate φ (c N / N) u ^ 2) -
      (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) -
      Real.log N / (∫ u, φ u ^ 2) * horizonAlias φ h (c N) N)) atTop (𝓝 0) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcInf := (criticalCurve_facts hc1 hK hcrit).1
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 1 0
  have hpole := criticalCurve_sq_mul_polePart hφ.continuous hφc hh hsupp hA hc1 hK hcrit
  have hlow := criticalCurve_sq_mul_lowFrequency hφ hφsupp hh hA hsupp hc1 hK hcrit
  have hdef := criticalCurve_sq_log_mul_energyDefect hφ hφsupp hh hA hsupp hc1 hK hcrit
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  set M := ∫ u, φ u ^ 2 with hM
  set I₁ := ∫ u, φ u with hI₁
  set Ph := (horizonTransform h 0 * conj (horizonTransform h 1) +
    horizonTransform h 1 * conj (horizonTransform h 0)).re with hPh
  set Gh := ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 *
    nuSymbol (Real.exp (2 * (A + 1))) τ with hGh
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A)))ᶜ, (horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ -
        Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N))) with hRmdef
  have hRm : Tendsto (fun N => c N ^ 2 * Rm N) atTop (𝓝 0) := by
    let V := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A + 1
    have h6 := (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp hcInf
    have ht := (tendsto_inv_atTop_zero.comp h6).const_mul (2 * aliasConst Cφ 8 A Bh * V)
    simp only [mul_zero] at ht
    have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A)),
      hT.eventually (eventually_ge_atTop 2)] with N h1 h2
    have hb := abs_remainder_le hφ hφsupp (by norm_num : (1 : ℝ) < 8) hCφ hdecay
      hC0 hC (2 * (A + 1)) hsupp hA hB h1 h2 (hc0 N)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq ?_
    rw [show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
    dsimp only [V, Function.comp_def]
    have hcne : c N ≠ 0 := (hc0 N).ne'
    field_simp
  -- the identity
  have hcle : ∀ᶠ N : ℕ in atTop, c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_one hN0] at h1
    exact h1.le
  have hid : ∀ᶠ N : ℕ in atTop, M⁻¹ * ((alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
        alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re - I₁ ^ 2 * Ph) +
      M⁻¹ * ((∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
        horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ) - I₁ ^ 2 * Gh) +
      M⁻¹ * Rm N + M⁻¹ * ((2 * Real.pi)⁻¹ * (Real.log N * (blockEnergy φ h (c N) N -
        lowPart φ h (c N) N A - 2 * Real.pi * horizonAlias φ h (c N) N))) =
      (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      I₁ ^ 2 / M * weilQuad (halfWeight h) - Real.log N / M * horizonAlias φ h (c N) N := by
    filter_upwards [hcle, eventually_ge_atTop 1] with N h6 hN
    rw [horizonForm_eq hφ hφsupp hφ2 hsupp hA (hc0 N) hN h6, weilQuad_halfWeight_eq hh hsupp hA]
    have hS := integrable_horizonSymbolIntegrand hφ hφsupp h (hc0 N) hN (2 * (A + 1))
    have hE := integrable_blockIntegrand hφ hφsupp h (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A))) measurableSet_Icc hS).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A))) measurableSet_Icc hE
    have hcompl : ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ = Rm N +
          Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A)))
            ((N : ℝ) * Real.exp (-A)))ᶜ, ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
              (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) := by
      simp only [hRmdef]
      rw [integral_sub hS.integrableOn (hE.const_mul _).integrableOn, integral_const_mul]
      ring
    have hEL : ∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) =
        blockEnergy φ h (c N) N - lowPart φ h (c N) N A := by
      rw [blockEnergy, lowPart, ← hsplitE]; ring
    rw [hsplitS, hcompl, hEL, ← hM, ← hPh, ← hGh]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    field_simp
    ring
  have l1 := hpole.const_mul M⁻¹
  have l2 := hlow.const_mul M⁻¹
  have l3 := hRm.const_mul M⁻¹
  have l4 := (hdef.const_mul (2 * Real.pi)⁻¹).const_mul M⁻¹
  have ht := ((l1.add l2).add l3).add l4
  simp only [mul_zero, add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [hid] with N hN
  calc _ = c N ^ 2 * (M⁻¹ *
        ((alphaPlus φ h (c N) N * conj (alphaMinus φ h (c N) N) +
          alphaMinus φ h (c N) N * conj (alphaPlus φ h (c N) N)).re - I₁ ^ 2 * Ph) +
        M⁻¹ * ((∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
          horizonSymbolIntegrand φ h (c N) N (Real.exp (2 * (A + 1))) τ) - I₁ ^ 2 * Gh) +
        M⁻¹ * Rm N + M⁻¹ * ((2 * Real.pi)⁻¹ * (Real.log N * (blockEnergy φ h (c N) N -
          lowPart φ h (c N) N A - 2 * Real.pi * horizonAlias φ h (c N) N)))) := by
        dsimp only [M, I₁, Ph, Gh]
        ring
    _ = _ := congrArg (fun x => c N ^ 2 * x) hN


/-- The complete tilted-spline form on a synthesized horizon window,
normalized by atom mass and overlap. -/
def tiltedHorizonEnergy (h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  c⁻¹ * (weilQuad (atomicTest N (horizonWeights h N) (atomDilate tiltedUnitSpline (c / N))) /
    ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2)

/-- The third-order horizon expansion: after the leading pencil, the first
surviving correction is a strictly negative exponential moment. -/
theorem tiltedHorizonEnergy_quadratic_correction {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 * (tiltedHorizonEnergy h (c N) N -
      (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) -
      7 * tiltedJordanOne * (Real.log N / c N ^ 8) *
        ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) atTop
      (𝓝 (-(tiltedNextAliasCoefficient / K *
        ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2))) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hrem := criticalCurve_horizon_remainder contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos hC tiltedUnitSpline_decay hh hA hsupp hc1 hK hcrit
  have hcInf := (criticalCurve_facts hc1 hK hcrit).1
  have hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hK hcrit 3 0
  have halias := tendsto_twoTerm_horizonAlias hh hsupp hA hc1 hcInf hc3N
  rw [leadingAliasMoment_eq, neg_mul, nextAliasMoment_eq] at halias
  let M := ∫ u, tiltedUnitSpline u ^ 2
  let M8 := ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2
  let M10 := ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2
  have hM : M ≠ 0 := integral_tiltedUnitSpline_sq_pos.ne'
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ 8) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  have hcor : Tendsto (fun N : ℕ => c N ^ 2 *
      (Real.log N / M * horizonAlias tiltedUnitSpline h (c N) N -
        7 * tiltedJordanOne * (Real.log N / c N ^ 8) * M8)) atTop
      (𝓝 (-(tiltedNextAliasCoefficient / K * M10))) := by
    have ht := (hinv.mul halias).div_const M
    have hval : K⁻¹ * (-(M * tiltedNextAliasCoefficient * M10)) / M =
        -(tiltedNextAliasCoefficient / K * M10) := by field_simp
    change Tendsto _ atTop (𝓝 (K⁻¹ * (-(M * tiltedNextAliasCoefficient * M10)) / M)) at ht
    rw [hval] at ht
    refine ht.congr fun N => ?_
    have hcne : c N ≠ 0 := by linarith [hc1 N]
    dsimp only [M, M8]
    field_simp [integral_tiltedUnitSpline_sq_pos.ne']
  have ht := hrem.add hcor
  simp only [zero_add] at ht
  refine ht.congr fun N => ?_
  dsimp only [tiltedHorizonEnergy, M, M8]
  ring

/-- Every exponential square moment of a nonzero compact window is positive. -/
theorem halfWeight_exponentialMoment_pos {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hne : h ≠ 0) (p : ℝ) :
    0 < ∫ y, Real.exp (-(p * y)) * halfWeight h y ^ 2 := by
  have hW := contDiff_halfWeight hh
  have hWc := hasCompactSupport_halfWeight (hasCompactSupport_of_window hsupp)
  let f : ℝ → ℝ := fun y => Real.exp (-(p * y)) * halfWeight h y ^ 2
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul (hW.continuous.pow 2)
  have hfc : HasCompactSupport f :=
    (hWc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)).mul_left
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hf0 : 0 ≤ f := fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  obtain ⟨y, hy⟩ : ∃ y, h y ≠ 0 := by
    by_contra! hz
    exact hne (funext hz)
  have hWy : halfWeight h y ≠ 0 := mul_ne_zero (Real.exp_ne_zero _) hy
  have hfy : 0 < f y := mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hWy)
  change 0 < ∫ y, f y
  rw [integral_pos_iff_support_of_nonneg hf0 hfi]
  exact hf.isOpen_support.measure_pos volume ⟨y, hfy.ne'⟩

/-- An eventual exact critical clock has the prescribed limiting ratio. -/
theorem criticalCurve_ratio_of_exact {c : ℕ → ℝ} {K : ℝ}
    (hclock : ∀ᶠ N : ℕ in atTop, c N ^ 8 = K * Real.log N) :
    Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hclock, eventually_ge_atTop 2] with N hN hN2
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N))
  rw [hN, mul_div_cancel_right₀ K hlog]

/-- On the exact critical clock, a vanishing leading pencil is approached
from a negative inverse-square correction. -/
theorem tiltedHorizonEnergy_exact_critical_limit {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hclock : ∀ᶠ N : ℕ in atTop, c N ^ 8 = K * Real.log N)
    (hzero : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) = 0) :
    Tendsto (fun N : ℕ => c N ^ 2 * tiltedHorizonEnergy h (c N) N) atTop
      (𝓝 (-(tiltedNextAliasCoefficient / K *
        ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2))) := by
  have ht := tiltedHorizonEnergy_quadratic_correction hh hsupp hA hc1 hK
    (criticalCurve_ratio_of_exact hclock)
  refine ht.congr' ?_
  filter_upwards [hclock] with N hN
  have hcne : c N ≠ 0 := by linarith [hc1 N]
  have heq : Real.log N / c N ^ 8 = K⁻¹ := by
    rw [div_eq_iff (pow_ne_zero 8 hcne)]
    rw [hN]
    field_simp
  rw [heq]
  have hp : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) = -(7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := eq_neg_of_add_eq_zero_left hzero
  rw [hp]
  ring

/-- A nonzero window on the equality face has eventually negative complete
energy on the exact critical clock. -/
theorem tiltedHorizonEnergy_exact_critical_negative {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hne : h ≠ 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hclock : ∀ᶠ N : ℕ in atTop, c N ^ 8 = K * Real.log N)
    (hzero : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) = 0) :
    ∀ᶠ N : ℕ in atTop, tiltedHorizonEnergy h (c N) N < 0 := by
  have ht := tiltedHorizonEnergy_exact_critical_limit hh hsupp hA hc1 hK hclock hzero
  have hneg : -(tiltedNextAliasCoefficient / K *
      ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2) < 0 := by
    exact neg_neg_of_pos (mul_pos (div_pos tiltedNextAliasCoefficient_pos hK)
      (halfWeight_exponentialMoment_pos hh hsupp hne 10))
  filter_upwards [ht.eventually (gt_mem_nhds hneg)] with N hN
  by_contra! hnonneg
  exact (not_lt_of_ge (mul_nonneg (sq_nonneg _) hnonneg)) hN

/-- A perturbation of the critical ratio at order `c⁻²` competes exactly
with the negative next aliasing coefficient. -/
theorem tiltedHorizonEnergy_critical_shift_limit {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
    {L : ℝ} (hshift : Tendsto (fun N : ℕ => c N ^ 2 * (c N ^ 8 / Real.log N - K))
      atTop (𝓝 L))
    (hzero : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) = 0) :
    Tendsto (fun N : ℕ => c N ^ 2 * tiltedHorizonEnergy h (c N) N) atTop
      (𝓝 (-(7 * tiltedJordanOne * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) * L / K ^ 2) -
        tiltedNextAliasCoefficient / K * (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2))) := by
  let B := 7 * tiltedJordanOne * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)
  let Q := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h)
  have hQ : Q = -(B / K) := by
    dsimp only [Q, B]
    have heq : 7 * tiltedJordanOne / K * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) =
        7 * tiltedJordanOne * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) / K := by ring
    rw [heq] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hlead : Tendsto (fun N : ℕ => c N ^ 2 * (Q + B * (Real.log N / c N ^ 8)))
      atTop (𝓝 (-(B * L / K ^ 2))) := by
    have ht := (hshift.const_mul (-(B / K))).mul (hcrit.inv₀ hK.ne')
    have hval : -(B / K) * L * K⁻¹ = -(B * L / K ^ 2) := by ring
    rw [hval] at ht
    refine ht.congr' ?_
    filter_upwards [hcrit.eventually (lt_mem_nhds hK)] with N hN
    rw [inv_div, hQ]
    have hcne : c N ≠ 0 := by linarith [hc1 N]
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      intro hz
      rw [hz, div_zero] at hN
      exact lt_irrefl 0 hN
    field_simp
    ring
  have hcorr := tiltedHorizonEnergy_quadratic_correction hh hsupp hA hc1 hK hcrit
  have ht := hlead.add hcorr
  have hval : -(B * L / K ^ 2) +
      -(tiltedNextAliasCoefficient / K * (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2)) =
      -(B * L / K ^ 2) -
        tiltedNextAliasCoefficient / K * (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2) := by ring
  rw [hval] at ht
  refine ht.congr fun N => ?_
  dsimp only [B, Q]
  ring

/-- The exact critical overlap, with harmless truncation at the initial indices. -/
def canonicalCriticalClock (K : ℝ) (N : ℕ) : ℝ :=
  max 1 ((K * Real.log N) ^ (1 / 8 : ℝ))

theorem canonicalCriticalClock_one_le (K : ℝ) (N : ℕ) :
    1 ≤ canonicalCriticalClock K N := le_max_left _ _

theorem canonicalCriticalClock_tendsto {K : ℝ} (hK : 0 < K) :
    Tendsto (canonicalCriticalClock K) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
    (hlog.const_mul_atTop hK)
  refine tendsto_atTop_mono (fun N => ?_) ht
  exact le_max_right _ _

theorem canonicalCriticalClock_exact {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, canonicalCriticalClock K N ^ 8 = K * Real.log N := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
    (hlog.const_mul_atTop hK)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with N hN
  dsimp only [Function.comp_def] at hN
  rw [canonicalCriticalClock, max_eq_right hN, ← Real.rpow_natCast,
    ← Real.rpow_mul (mul_nonneg hK.le (Real.log_natCast_nonneg N))]
  norm_num

/-- The canonical overlap on the equality face has eventually negative energy. -/
theorem canonicalCriticalClock_energy_negative {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hne : h ≠ 0) {K : ℝ} (hK : 0 < K)
    (hzero : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) = 0) :
    ∀ᶠ N : ℕ in atTop, tiltedHorizonEnergy h (canonicalCriticalClock K N) N < 0 :=
  tiltedHorizonEnergy_exact_critical_negative hh hsupp hA hne
    (canonicalCriticalClock_one_le K) hK (canonicalCriticalClock_exact hK) hzero


/-- On the canonical clock every nonzero window has an eventual strict sign.
The boundary of the leading pencil belongs to the negative phase. -/
theorem canonicalCriticalClock_phase_diagram {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hne : h ≠ 0) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      (0 < tiltedHorizonEnergy h (canonicalCriticalClock K N) N ↔
        0 < (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
            (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) ∧
      (tiltedHorizonEnergy h (canonicalCriticalClock K N) N < 0 ↔
        (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
            (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) ≤ 0) := by
  let P := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
    weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
      (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)
  have hlim : Tendsto (fun N => tiltedHorizonEnergy h (canonicalCriticalClock K N) N)
      atTop (𝓝 P) :=
    horizon_layer_criticalCurve_exact hh hA hsupp (canonicalCriticalClock_one_le K) hK
      (criticalCurve_ratio_of_exact (canonicalCriticalClock_exact hK))
  by_cases hP : 0 < P
  · filter_upwards [hlim.eventually (lt_mem_nhds hP)] with N hN
    exact ⟨iff_of_true hN hP, iff_of_false (not_lt_of_ge hN.le) (not_le_of_gt hP)⟩
  · have hP0 : P ≤ 0 := le_of_not_gt hP
    have hneg : ∀ᶠ N : ℕ in atTop,
        tiltedHorizonEnergy h (canonicalCriticalClock K N) N < 0 := by
      rcases lt_or_eq_of_le hP0 with hlt | heq
      · exact hlim.eventually (gt_mem_nhds hlt)
      · exact canonicalCriticalClock_energy_negative hh hsupp hA hne hK heq
    filter_upwards [hneg] with N hN
    exact ⟨iff_of_false (not_lt_of_ge hN.le) hP, iff_of_true hN hP0⟩


/-- An inverse-overlap perturbation of the canonical critical clock. -/
def shiftedCriticalClock (K d : ℝ) (N : ℕ) : ℝ :=
  max 1 (canonicalCriticalClock K N + d / canonicalCriticalClock K N)

theorem shiftedCriticalClock_one_le (K d : ℝ) (N : ℕ) :
    1 ≤ shiftedCriticalClock K d N := le_max_left _ _

/-- An inverse-overlap perturbation realizes every finite first shift of the
critical ratio: `c²(K_N-K) → 8Kd`. -/
theorem shiftedCriticalClock_ratio_and_shift {K : ℝ} (hK : 0 < K) (d : ℝ) :
    Tendsto (fun N : ℕ => shiftedCriticalClock K d N ^ 8 / Real.log N) atTop (𝓝 K) ∧
    Tendsto (fun N : ℕ => shiftedCriticalClock K d N ^ 2 *
      (shiftedCriticalClock K d N ^ 8 / Real.log N - K)) atTop (𝓝 (8 * K * d)) := by
  let b := canonicalCriticalClock K
  have hb : Tendsto b atTop atTop := canonicalCriticalClock_tendsto hK
  have hb1 (N : ℕ) : 1 ≤ b N := canonicalCriticalClock_one_le K N
  have hdiv : Tendsto (fun N : ℕ => d / b N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hb
  have hraw : Tendsto (fun N : ℕ => b N + d / b N) atTop atTop := by
    refine tendsto_atTop.mpr fun R => ?_
    filter_upwards [hb.eventually (eventually_ge_atTop (R + 1)),
      hdiv.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with N hbN hdN
    linarith
  have hmax : ∀ᶠ N : ℕ in atTop, shiftedCriticalClock K d N = b N + d / b N := by
    filter_upwards [hraw.eventually (eventually_ge_atTop 1)] with N hN
    exact max_eq_right hN
  let u : ℕ → ℝ := fun N => d / b N ^ 2
  have hu : Tendsto u atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hb)
  let P : ℝ → ℝ := fun x => 8 + 28 * x + 56 * x ^ 2 + 70 * x ^ 3 +
    56 * x ^ 4 + 28 * x ^ 5 + 8 * x ^ 6 + x ^ 7
  have hfactor (x : ℝ) : (1 + x) ^ 8 - 1 = x * P x := by dsimp only [P]; ring
  have hP : Tendsto (fun N => P (u N)) atTop (𝓝 8) := by
    have hc : Continuous P := by dsimp only [P]; fun_prop
    have ht := (hc.tendsto 0).comp hu
    simpa only [Function.comp_def, P, zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0),
      zero_pow (by norm_num : 5 ≠ 0), zero_pow (by norm_num : 6 ≠ 0),
      zero_pow (by norm_num : 7 ≠ 0), mul_zero, add_zero] using ht
  have h1 := hu.const_add 1
  simp only [add_zero] at h1
  have hratio := (h1.pow 8).const_mul K
  simp only [one_pow, mul_one] at hratio
  have hshift := ((h1.pow 2).mul hP).const_mul (K * d)
  simp only [one_pow, one_mul] at hshift
  rw [show K * d * 8 = 8 * K * d by ring] at hshift
  have heq : ∀ᶠ N : ℕ in atTop,
      shiftedCriticalClock K d N ^ 8 / Real.log N = K * (1 + u N) ^ 8 ∧
      shiftedCriticalClock K d N ^ 2 * (shiftedCriticalClock K d N ^ 8 / Real.log N - K) =
        K * d * ((1 + u N) ^ 2 * P (u N)) := by
    filter_upwards [hmax, canonicalCriticalClock_exact hK, eventually_ge_atTop 2] with N hcN hbN hN2
    have hb0 : b N ≠ 0 := by linarith [hb1 N]
    have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by
      exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N))
    have hcu : shiftedCriticalClock K d N = b N * (1 + u N) := by
      rw [hcN]
      dsimp only [u]
      field_simp
    have huB : b N ^ 2 * u N = d := by dsimp only [u]; field_simp
    have hr : shiftedCriticalClock K d N ^ 8 / Real.log N = K * (1 + u N) ^ 8 := by
      rw [hcu, mul_pow]
      change b N ^ 8 = K * Real.log N at hbN
      rw [hbN]
      field_simp
    refine ⟨hr, ?_⟩
    rw [hr, hcu, mul_pow,
      show K * (1 + u N) ^ 8 - K = K * ((1 + u N) ^ 8 - 1) by ring, hfactor]
    calc b N ^ 2 * (1 + u N) ^ 2 * (K * (u N * P (u N))) =
          K * (b N ^ 2 * u N) * ((1 + u N) ^ 2 * P (u N)) := by ring
      _ = _ := by rw [huB]
  exact ⟨hratio.congr' (heq.mono fun N hN => hN.1.symm),
    hshift.congr' (heq.mono fun N hN => hN.2.symm)⟩

/-- Equality of the leading pencil has no schedule-independent sign: two
explicit clocks with the same critical ratio have opposite eventual signs. -/
theorem critical_ratio_equality_admits_both_signs {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    (hne : h ≠ 0) {K : ℝ} (hK : 0 < K)
    (hzero : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
      weilQuad (halfWeight h) + 7 * tiltedJordanOne / K *
        (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2) = 0) :
    ∃ cMinus cPlus : ℕ → ℝ,
      (∀ N, 1 ≤ cMinus N) ∧ (∀ N, 1 ≤ cPlus N) ∧
      Tendsto (fun N : ℕ => cMinus N ^ 8 / Real.log N) atTop (𝓝 K) ∧
      Tendsto (fun N : ℕ => cPlus N ^ 8 / Real.log N) atTop (𝓝 K) ∧
      (∀ᶠ N : ℕ in atTop, tiltedHorizonEnergy h (cMinus N) N < 0) ∧
      (∀ᶠ N : ℕ in atTop, 0 < tiltedHorizonEnergy h (cPlus N) N) := by
  let B := 7 * tiltedJordanOne * (∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)
  let T := tiltedNextAliasCoefficient * (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2)
  have hB : 0 < B := mul_pos (mul_pos (by norm_num) tiltedJordanOne_pos)
    (halfWeight_exponentialMoment_pos hh hsupp hne 8)
  have hT : 0 < T := mul_pos tiltedNextAliasCoefficient_pos
    (halfWeight_exponentialMoment_pos hh hsupp hne 10)
  let d := -T / (4 * B)
  have hclocks := shiftedCriticalClock_ratio_and_shift hK d
  have hplus : Tendsto (fun N : ℕ => shiftedCriticalClock K d N ^ 2 *
      tiltedHorizonEnergy h (shiftedCriticalClock K d N) N) atTop (𝓝 (T / K)) := by
    have ht := tiltedHorizonEnergy_critical_shift_limit hh hsupp hA
      (shiftedCriticalClock_one_le K d) hK hclocks.1 hclocks.2 hzero
    have hval : -(B * (8 * K * d) / K ^ 2) - tiltedNextAliasCoefficient / K *
        (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2) = T / K := by
      dsimp only [d, T]
      field_simp
      ring
    change Tendsto _ atTop (𝓝 (-(B * (8 * K * d) / K ^ 2) -
      tiltedNextAliasCoefficient / K * (∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2))) at ht
    rw [hval] at ht
    exact ht
  refine ⟨canonicalCriticalClock K, shiftedCriticalClock K d,
    canonicalCriticalClock_one_le K, shiftedCriticalClock_one_le K d,
    criticalCurve_ratio_of_exact (canonicalCriticalClock_exact hK), hclocks.1,
    canonicalCriticalClock_energy_negative hh hsupp hA hne hK hzero, ?_⟩
  filter_upwards [hplus.eventually (lt_mem_nhds (div_pos hT hK))] with N hN
  by_contra! hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hnonpos)) hN

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.criticalCurve_horizon_remainder
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tiltedHorizonEnergy_quadratic_correction
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.canonicalCriticalClock_energy_negative
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.critical_ratio_equality_admits_both_signs

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.canonicalCriticalClock_phase_diagram
