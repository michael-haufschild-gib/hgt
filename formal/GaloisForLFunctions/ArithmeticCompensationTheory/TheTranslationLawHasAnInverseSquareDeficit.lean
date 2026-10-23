import GaloisForLFunctions.ArithmeticCompensationTheory.TheHorizonLawHoldsAtTheDeLaValleePoussinRate

/-!
# The translation law has an inverse-square deficit

The horizon energy `J(F) = ∫∫ A_F(u − v) dμ(u) dμ(v)`, `dμ = ½e^{−u/2} du` on `u > 0`, is a double
average of the autocorrelation. It collapses to a single one:

`J(F) = ∫_{u>0} A_F(u) ½e^{−u/2} du`  (`horizonEnergy_eq_horizonIntegral_autoCorr`),

the probe of the test against its own horizon translate at depth zero. The proof integrates
`−¼e^{−v} Φ(−v)`, `Φ(w) = ∫_{s>w} A_F(s) e^{−s/2} ds`, along the half-line, using that `A_F` is even.

On the slowly varying family `F_r(x) = r^{−1/2} f(x/r)` the autocorrelation is `A_f(·/r)`, and a
`Λ`-Lipschitz profile supported in `[−1, 1]` loses at most `A_f(0) − A_f(s) ≤ Λ²s²(1 + |s|)`
(`autoCorr_zero_sub_le`: `A(0) − A(s) = ½∫(F(x) − F(x + s))²`). With the horizon moments
`∫ u^k dμ = 2^k k!` (`integral_pow_mul_horizonDensity`) this gives

`A_f(0) − Λ²(8/r² + 48/r³) ≤ J(F_r) ≤ A_f(0)`  (`horizonEnergy_rescaledTest_ge`),

and with the de la Vallée Poussin rate of the resolvent law, whose constants do not depend on the
test, the comb itself has an inverse-square deficit
(`exists_combEnergy_rescaledTest_deficit_le`):

`0 ≤ A_f(0) − E_r(F_r)/S_r² ≤ C/r²`.

The deficit is the resolvent's first correction (`J(F_r) = A_f(0) − 4‖f'‖²/r² + O(r^{−4})` for
smooth `f`), not the prime error, which is `O(exp(−c√r))`. So on the slowly varying family the
comb is a translation up to a relative error of order `r^{−2}`.
-/

open Filter Topology Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The horizon energy is a single horizon average -/

/-- **The horizon energy is the horizon average of the autocorrelation.**
`J(F) = ∫_{u>0} A_F(u) ½e^{−u/2} du`. -/
theorem horizonEnergy_eq_horizonIntegral_autoCorr {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : horizonEnergy F = horizonIntegral (autoCorr F) := by
  set A := autoCorr F
  have hA : Continuous A := continuous_autoCorr hF hFc
  have hAb : ∀ t, |A t| ≤ A 0 := abs_autoCorr_le_autoCorr_zero hF hFc
  set ψ : ℝ → ℝ := fun s => A s * Real.exp (-s / 2)
  have hψc : Continuous ψ := hA.mul (by fun_prop)
  have hψi : Integrable ψ :=
    hψc.integrable_of_hasCompactSupport (hasCompactSupport_autoCorr hFc).mul_right
  set Φ : ℝ → ℝ := fun w => ∫ s in Ioi w, ψ s
  -- `Φ(w) = Φ(0) − ∫_0^w ψ`, so `Φ' = −ψ`
  have hΦeq : Φ = fun w => Φ 0 - ∫ s in (0 : ℝ)..w, ψ s := by
    funext w
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (a := 0) (b := w) hψi.integrableOn
      hψi.integrableOn
    simp only [Φ] at h ⊢
    linarith
  have hΦd : ∀ w, HasDerivAt Φ (-ψ w) w := fun w => by
    rw [hΦeq]
    exact ((hψc.integral_hasStrictDerivAt 0 w).hasDerivAt).const_sub _
  set B := ∫ x, |ψ x|
  have hΦb : ∀ w, |Φ w| ≤ B := fun w => by
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_le_integral hψi.abs (Eventually.of_forall fun _ => abs_nonneg _)
  -- the antiderivative `W(v) = −¼e^{−v} Φ(−v)`
  set W : ℝ → ℝ := fun v => -(1 / 4) * (Real.exp (-v) * Φ (-v))
  set W' : ℝ → ℝ := fun v => 1 / 4 * Real.exp (-v) * Φ (-v) - 1 / 4 * (A v * Real.exp (-v / 2))
  have hWd : ∀ v, HasDerivAt W (W' v) v := by
    intro v
    have h1 : HasDerivAt (fun x => Real.exp (-x)) (Real.exp (-v) * -1) v := (hasDerivAt_neg v).exp
    have h2 : HasDerivAt (fun x => Φ (-x)) (-ψ (-v) * -1) v := (hΦd (-v)).comp v (hasDerivAt_neg v)
    have h3 := (h1.mul h2).const_mul (-(1 / 4 : ℝ))
    refine h3.congr_deriv ?_
    have hAe : A (-v) = A v := autoCorr_neg F v
    have he : Real.exp (-v) * Real.exp (-(-v) / 2) = Real.exp (-v / 2) := by
      rw [← Real.exp_add]; ring_nf
    simp only [W', ψ, hAe]
    rw [← he]
    ring
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun v => (hWd v).continuousAt
  have hexpi : IntegrableOn (fun v => Real.exp (-v)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun w => (hΦd w).continuousAt
  have hI1 : IntegrableOn (fun v => 1 / 4 * Real.exp (-v) * Φ (-v)) (Ioi 0) := by
    have h := hexpi.bdd_mul (hΦc.comp continuous_neg).aestronglyMeasurable
      (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hΦb (-v))
    refine (h.const_mul (1 / 4)).congr_fun (fun v _ => by simp only [Function.comp_apply]; ring)
      measurableSet_Ioi
  have hI2 : IntegrableOn (fun v => 1 / 4 * (A v * Real.exp (-v / 2))) (Ioi 0) := by
    have h := (integrableOn_mul_horizonDensity hA hAb 0).const_mul (1 / 2)
    refine h.congr_fun (fun v _ => by simp only [horizonDensity]; ring) measurableSet_Ioi
  have hlim : Tendsto W atTop (𝓝 0) := by
    have hB : Tendsto (fun v => 1 / 4 * B * Real.exp (-v)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (1 / 4 * B)
    refine squeeze_zero_norm (fun v => ?_) hB
    rw [Real.norm_eq_abs]
    simp only [W, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    have := hΦb (-v)
    have he := Real.exp_pos (-v)
    nlinarith [abs_nonneg (Φ (-v))]
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hWc.continuousWithinAt
    (fun v _ => hWd v) (hI1.sub hI2) hlim
  rw [integral_sub hI1 hI2, integral_const_mul] at hFTC
  have hW0 : W 0 = -(1 / 4) * Φ 0 := by simp [W]
  have hΦ0 : (∫ v in Ioi (0 : ℝ), A v * Real.exp (-v / 2)) = Φ 0 := rfl
  rw [hW0, hΦ0] at hFTC
  -- both sides in terms of `Φ(0)`
  have hJ : horizonEnergy F = ∫ v in Ioi (0 : ℝ), 1 / 4 * Real.exp (-v) * Φ (-v) := by
    rw [horizonEnergy, horizonIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    have hG := horizonAutoCorr_eq (F := F) v
    simp only [horizonAutoCorr] at hG
    rw [hG, horizonDensity, neg_neg]
    have he : Real.exp (-v / 2) * Real.exp (-v / 2) = Real.exp (-v) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Φ, ψ]
    rw [← he]
    ring
  have hH : horizonIntegral A = 1 / 2 * Φ 0 := by
    rw [horizonIntegral, ← hΦ0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [horizonDensity]; ring
  rw [hJ, hH]
  linarith

/-! ## The deficit of a Lipschitz autocorrelation at the origin -/

/-- A Lipschitz bound gives continuity. -/
theorem continuous_of_abs_sub_le {F : ℝ → ℝ} {Λ : ℝ} (hΛ : ∀ a b, |F a - F b| ≤ Λ * |a - b|) :
    Continuous F := by
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  refine (LipschitzWith.of_dist_le_mul (K := Λ.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hΛ0]
  exact hΛ x y

/-- **The autocorrelation deficit.** For a `Λ`-Lipschitz test supported in `[−R, R]`,
`A(0) − A(s) = ½∫(F(x) − F(x + s))² ≤ Λ² s² (R + |s|)`. -/
theorem autoCorr_zero_sub_le {F : ℝ → ℝ} {Λ R : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ x, R < |x| → F x = 0) (hΛ : ∀ a b, |F a - F b| ≤ Λ * |a - b|) (s : ℝ) :
    autoCorr F 0 - autoCorr F s ≤ Λ ^ 2 * s ^ 2 * (R + |s|) := by
  have hF := continuous_of_abs_sub_le hΛ
  have hFc : HasCompactSupport F := HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
    fun x hx => hsupp x (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hFs : HasCompactSupport fun x => F (x + s) := hFc.comp_homeomorph (Homeomorph.addRight s)
  have hi1 : Integrable fun x => F x * F (x + 0) := by
    simp only [add_zero]; exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hi2 : Integrable fun x => F x * F (x + s) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hi3 : Integrable fun x => F (x + s) * F (x + s) :=
    ((hF.comp (continuous_id.add continuous_const)).mul
      (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport hFs.mul_right
  -- `∫ (F(x) − F(x+s))² = 2A(0) − 2A(s)`
  have htrans : (∫ x, F (x + s) * F (x + s)) = ∫ x, F x * F (x + 0) := by
    rw [integral_add_right_eq_self (fun x => F x * F x) s]
    simp only [add_zero]
  have hsq : (∫ x, (F x - F (x + s)) ^ 2) = 2 * autoCorr F 0 - 2 * autoCorr F s := by
    have hpt : (fun x => (F x - F (x + s)) ^ 2) = fun x =>
        F x * F (x + 0) - 2 * (F x * F (x + s)) + F (x + s) * F (x + s) := by
      funext x; simp only [add_zero]; ring
    rw [hpt, integral_add (hi1.sub (hi2.const_mul 2)) hi3, integral_sub hi1 (hi2.const_mul 2),
      integral_const_mul, htrans, autoCorr, autoCorr]
    ring
  -- the integrand lives on `[−R − |s|, R + |s|]` and is at most `Λ²s²`
  set a := -R - |s|
  set b := R + |s|
  have hab : a ≤ b := by have := abs_nonneg s; simp only [a, b]; linarith
  have hzero : ∀ x ∉ Icc a b, (F x - F (x + s)) ^ 2 = 0 := by
    intro x hx
    have hx' : b < |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by simp only [a] at hx; linarith [abs_nonneg s])]; simp only [a, b] at hx ⊢
        linarith
      · rw [abs_of_pos (by simp only [b] at hx; linarith [abs_nonneg s])]; exact hx
    have h1 : F x = 0 := hsupp x (by simp only [b] at hx'; linarith [abs_nonneg s])
    have h2 : F (x + s) = 0 := hsupp _ (by
      have := abs_sub_abs_le_abs_sub x (-s)
      rw [sub_neg_eq_add, abs_neg] at this
      simp only [b] at hx'
      linarith)
    rw [h1, h2]; ring
  have hcont : Continuous fun x => (F x - F (x + s)) ^ 2 :=
    (hF.sub (hF.comp (continuous_id.add continuous_const))).pow 2
  have hbound : (∫ x, (F x - F (x + s)) ^ 2) ≤ (b - a) * (Λ ^ 2 * s ^ 2) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    calc (∫ x in a..b, (F x - F (x + s)) ^ 2) ≤ ∫ _ in a..b, Λ ^ 2 * s ^ 2 :=
          intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
            intervalIntegrable_const fun x _ => by
              have h := hΛ x (x + s)
              rw [show x - (x + s) = -s by ring, abs_neg] at h
              calc (F x - F (x + s)) ^ 2 = |F x - F (x + s)| ^ 2 := (sq_abs _).symm
                _ ≤ (Λ * |s|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
                _ = Λ ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
      _ = (b - a) * (Λ ^ 2 * s ^ 2) := by rw [intervalIntegral.integral_const, smul_eq_mul]
  have hba : b - a = 2 * (R + |s|) := by simp only [a, b]; ring
  rw [hsq, hba] at hbound
  linarith

/-! ## The horizon moments -/

theorem integrableOn_pow_mul_horizonDensity (k : ℕ) :
    IntegrableOn (fun u => u ^ k * horizonDensity u) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := 1 / 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) le_rfl (by norm_num)).div_const 2
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu0 : 0 < u := hu
  simp only [horizonDensity, Real.rpow_natCast, Real.rpow_one]
  ring_nf

/-- **The horizon moments.** `∫_{u>0} u^k ½e^{−u/2} du = 2^k k!`. -/
theorem integral_pow_mul_horizonDensity (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ k * horizonDensity u = 2 ^ k * k.factorial := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (k : ℝ)) (b := 1 / 2) one_pos
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num)
  have hcongr : (∫ u in Ioi (0 : ℝ), u ^ k * horizonDensity u) =
      (∫ x in Ioi (0 : ℝ), x ^ (k : ℝ) * Real.exp (-(1 / 2) * x ^ (1 : ℝ))) / 2 := by
    rw [← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [horizonDensity, Real.rpow_natCast, Real.rpow_one]
    ring_nf
  rw [hcongr, h, div_one, Real.Gamma_nat_eq_factorial]
  have hpow : (1 / 2 : ℝ) ^ (-((k : ℝ) + 1)) = 2 ^ (k + 1) := by
    rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast, Real.div_rpow (by norm_num) (by norm_num),
      Real.one_rpow]
    push_cast
    field_simp
  rw [hpow]
  ring

/-! ## The slowly varying family -/

/-- **The horizon energy of the slowly varying family.** For a `Λ`-Lipschitz profile supported in
`[−1, 1]`, `A_f(0) − Λ²(8/r² + 48/r³) ≤ J(F_r) ≤ A_f(0)`. -/
theorem horizonEnergy_rescaledTest_ge {f : ℝ → ℝ} {Λ : ℝ} (hsupp : ∀ x, 1 < |x| → f x = 0)
    (hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b|) {r : ℝ} (hr : 0 < r) :
    autoCorr f 0 - Λ ^ 2 * (8 / r ^ 2 + 48 / r ^ 3) ≤ horizonEnergy (rescaledTest f r) ∧
      horizonEnergy (rescaledTest f r) ≤ autoCorr f 0 := by
  have hf := continuous_of_abs_sub_le hΛ
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1))
    fun x hx => hsupp x (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hFr := continuous_rescaledTest hf r
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  refine ⟨?_, hA0 ▸ horizonEnergy_le hFr hFrc⟩
  rw [horizonEnergy_eq_horizonIntegral_autoCorr hFr hFrc, horizonIntegral]
  have hAf := continuous_autoCorr hf hfc
  have hAb : ∀ t, |autoCorr f t| ≤ autoCorr f 0 := abs_autoCorr_le_autoCorr_zero hf hfc
  have hmass : (∫ u in Ioi (0 : ℝ), horizonDensity u) = 1 := by
    rw [integral_Ioi_horizonDensity]; simp
  -- the deficit integrand and its moment majorant
  have hgi : IntegrableOn (fun u => (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u)
      (Ioi 0) := by
    refine integrableOn_mul_horizonDensity (M := 2 * autoCorr f 0)
      (continuous_const.sub (hAf.comp (continuous_id.div_const r))) (fun t => ?_) 0
    have h1 := hAb (t / r)
    have h0 := (abs_nonneg _).trans (hAb 0)
    rw [abs_le] at h1 ⊢
    constructor <;> linarith
  have hmi : IntegrableOn (fun u => Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u)
      (Ioi 0) := by
    have h := ((integrableOn_pow_mul_horizonDensity 2).div_const (r ^ 2)).add
      ((integrableOn_pow_mul_horizonDensity 3).div_const (r ^ 3))
    refine (h.const_mul (Λ ^ 2)).congr_fun (fun u _ => by ring) measurableSet_Ioi
  have hle : (∫ u in Ioi (0 : ℝ), (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u) ≤
      ∫ u in Ioi (0 : ℝ), Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u := by
    refine setIntegral_mono_on hgi hmi measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    refine mul_le_mul_of_nonneg_right ?_ (horizonDensity_nonneg u)
    have h := autoCorr_zero_sub_le zero_le_one hsupp hΛ (u / r)
    rw [abs_of_pos (div_pos hu0 hr)] at h
    calc autoCorr f 0 - autoCorr f (u / r) ≤ Λ ^ 2 * (u / r) ^ 2 * (1 + u / r) := h
      _ = Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) := by field_simp; ring
  have hmom : (∫ u in Ioi (0 : ℝ), Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u) =
      Λ ^ 2 * (8 / r ^ 2 + 48 / r ^ 3) := by
    have h2 := integral_pow_mul_horizonDensity 2
    have h3 := integral_pow_mul_horizonDensity 3
    have hsplit : (fun u => Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u) =
        fun u => Λ ^ 2 * ((u ^ 2 * horizonDensity u) / r ^ 2 + (u ^ 3 * horizonDensity u) / r ^ 3) := by
      funext u; ring
    rw [hsplit, integral_const_mul, integral_add
      ((integrableOn_pow_mul_horizonDensity 2).div_const _)
      ((integrableOn_pow_mul_horizonDensity 3).div_const _), integral_div, integral_div, h2, h3]
    norm_num [Nat.factorial]
  have hsplit : (∫ u in Ioi (0 : ℝ), autoCorr (rescaledTest f r) u * horizonDensity u) =
      autoCorr f 0 - ∫ u in Ioi (0 : ℝ), (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u := by
    have hci : IntegrableOn (fun u => autoCorr f 0 * horizonDensity u) (Ioi 0) :=
      (integrableOn_horizonDensity 0).const_mul _
    have hai : IntegrableOn (fun u => autoCorr f (u / r) * horizonDensity u) (Ioi 0) :=
      integrableOn_mul_horizonDensity (hAf.comp (continuous_id.div_const r)) (fun t => hAb _) 0
    simp only [sub_mul]
    rw [integral_sub hci hai, integral_const_mul, hmass, mul_one]
    simp only [autoCorr_rescaledTest hr]
    ring
  rw [hsplit]
  linarith

/-- `exp(−c√r) ≤ r^{−2}` eventually. -/
theorem eventually_exp_neg_sqrt_le_inv_sq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ r in atTop, Real.exp (-c * Real.sqrt r) ≤ 1 / r ^ 2 := by
  have h1 : Tendsto (fun x : ℝ => (c * x) ^ 4 * Real.exp (-(c * x))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp (tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun r : ℝ => (c * Real.sqrt r) ^ 4 * Real.exp (-(c * Real.sqrt r))) atTop
      (𝓝 0) := h1.comp Real.tendsto_sqrt_atTop
  filter_upwards [h2.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < c ^ 4)),
    eventually_gt_atTop 0] with r hr hr0
  have hs : Real.sqrt r ^ 4 = r ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hr0.le]
  rw [mul_pow, hs, show -(c * Real.sqrt r) = -c * Real.sqrt r by ring] at hr
  rw [le_div_iff₀ (by positivity)]
  have hc4 : 0 < c ^ 4 := by positivity
  nlinarith [Real.exp_pos (-c * Real.sqrt r)]

/-- **The comb is a translation up to an inverse-square deficit.** For a `Λ`-Lipschitz profile
supported in `[−1, 1]`, `0 ≤ A_f(0) − E_r(F_r)/S_r² ≤ C/r²` for all large `r`. -/
theorem exists_combEnergy_rescaledTest_deficit_le {f : ℝ → ℝ} {Λ : ℝ}
    (hsupp : ∀ x, 1 < |x| → f x = 0) (hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop,
      0 ≤ autoCorr f 0 - combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 ∧
      autoCorr f 0 - combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 ≤
        C / r ^ 2 := by
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combEnergy_div_sub_horizonEnergy_le
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hf := continuous_of_abs_sub_le hΛ
  have hfc : HasCompactSupport f := HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1))
    fun x hx => hsupp x (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  set N1 := ∫ x, |f x|
  have hN1 : 0 ≤ N1 := integral_nonneg fun _ => abs_nonneg _
  have hA00 : 0 ≤ autoCorr f 0 := (abs_nonneg _).trans (abs_autoCorr_le_autoCorr_zero hf hfc 0)
  refine ⟨56 * Λ ^ 2 + K * (Λ * N1 + autoCorr f 0), by positivity, ?_⟩
  filter_upwards [hev, eventually_combMass_pos, eventually_ge_atTop 1,
    eventually_exp_neg_sqrt_le_inv_sq hc] with r hE hS hr1 hexp
  have hr : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hFr := continuous_rescaledTest hf r
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  -- the rescaled test is `Λ r^{−3/2}`-Lipschitz with `‖F_r‖₁ = √r ‖f‖₁`
  set Λr := Λ * ((Real.sqrt r)⁻¹ * r⁻¹)
  have hΛr : ∀ a b, |rescaledTest f r a - rescaledTest f r b| ≤ Λr * |a - b| := by
    intro a b
    simp only [rescaledTest, Λr]
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hsr)]
    have h := hΛ (a / r) (b / r)
    rw [← sub_div, abs_div, abs_of_pos hr] at h
    calc (Real.sqrt r)⁻¹ * |f (a / r) - f (b / r)| ≤ (Real.sqrt r)⁻¹ * (Λ * (|a - b| / r)) :=
          mul_le_mul_of_nonneg_left h (inv_pos.mpr hsr).le
      _ = Λ * ((Real.sqrt r)⁻¹ * r⁻¹) * |a - b| := by ring
  have hL1 : (∫ x, |rescaledTest f r x|) = Real.sqrt r * N1 := by
    have h := Measure.integral_comp_div (fun y => |f y|) r
    simp only [rescaledTest, abs_mul, abs_of_pos (inv_pos.mpr hsr)]
    rw [integral_const_mul, h, abs_of_pos hr, smul_eq_mul]
    have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    field_simp
    rw [← hs]; ring
  have hprod : Λr * (Real.sqrt r * N1) = Λ * N1 / r := by
    simp only [Λr]; field_simp
  have hrate := hE (rescaledTest f r) Λr hFrc hΛr
  rw [hL1, hprod, hA0] at hrate
  have hJ := horizonEnergy_rescaledTest_ge hsupp hΛ hr
  -- the upper bound is Cauchy–Schwarz
  have hup : combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 ≤
      autoCorr f 0 := by
    rw [div_le_iff₀ (by positivity), ← hA0, mul_comm]
    exact combEnergy_le_combMass_sq_mul hFr hFrc r
  refine ⟨by linarith, ?_⟩
  have hr2 : 0 < r ^ 2 := by positivity
  have h8 : 8 / r ^ 2 + 48 / r ^ 3 ≤ 56 / r ^ 2 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hr2]
    nlinarith [pow_pos hr 2, pow_pos hr 3, pow_pos hr 4]
  have hΛN : Λ * N1 / r ≤ Λ * N1 := div_le_self (by positivity) hr1
  have herr : K * (Λ * N1 / r + autoCorr f 0) * Real.exp (-c * Real.sqrt r) ≤
      K * (Λ * N1 + autoCorr f 0) * (1 / r ^ 2) := by
    apply mul_le_mul _ hexp (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hK
  have hJ' : autoCorr f 0 - horizonEnergy (rescaledTest f r) ≤ Λ ^ 2 * (56 / r ^ 2) := by
    have := mul_le_mul_of_nonneg_left h8 (sq_nonneg Λ)
    linarith [hJ.1]
  have habs := (abs_le.mp hrate).1
  calc autoCorr f 0 - combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2
      = (autoCorr f 0 - horizonEnergy (rescaledTest f r)) +
        (horizonEnergy (rescaledTest f r) -
          combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2) := by ring
    _ ≤ Λ ^ 2 * (56 / r ^ 2) + K * (Λ * N1 + autoCorr f 0) * (1 / r ^ 2) := by linarith
    _ = (56 * Λ ^ 2 + K * (Λ * N1 + autoCorr f 0)) / r ^ 2 := by ring

end GaloisForLFunctions.ArithmeticCompensationTheory
