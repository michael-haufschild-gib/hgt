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
  set A := autoCorr F with hAdef
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
    exact IntegrableOn.congr_fun (h.const_mul (1 / 4))
      (fun v _ => by simp only [Function.comp_apply]; ring) measurableSet_Ioi
  have hI2 : IntegrableOn (fun v => 1 / 4 * (A v * Real.exp (-v / 2))) (Ioi 0) := by
    have h := (integrableOn_mul_horizonDensity hA hAb 0).const_mul (1 / 2)
    exact IntegrableOn.congr_fun h (fun v _ => by simp only [horizonDensity]; ring)
      measurableSet_Ioi
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
    rw [hG, horizonDensity]
    have he : Real.exp (-v / 2) * Real.exp (-v / 2) = Real.exp (-v) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Φ, ψ, hAdef]
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

/-- A test vanishing outside `[−R, R]` has compact support. -/
theorem hasCompactSupport_of_eq_zero {F : ℝ → ℝ} {R : ℝ} (hsupp : ∀ x, R < |x| → F x = 0) :
    HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => hsupp x (by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x])

/-- The autocorrelation deficit is half the energy of the increment:
`A(0) − A(s) = ½∫(F(x) − F(x + s))²`. -/
theorem autoCorr_zero_sub_eq {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) (s : ℝ) :
    autoCorr F 0 - autoCorr F s = 1 / 2 * ∫ x, (F x - F (x + s)) ^ 2 := by
  have hFs : HasCompactSupport fun x => F (x + s) := hFc.comp_homeomorph (Homeomorph.addRight s)
  have hi1 : Integrable fun x => F x * F (x + 0) := by
    simp only [add_zero]; exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hi2 : Integrable fun x => F x * F (x + s) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have hi3 : Integrable fun x => F (x + s) * F (x + s) :=
    ((hF.comp (continuous_id.add continuous_const)).mul
      (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport hFs.mul_right
  have htrans : (∫ x, F (x + s) * F (x + s)) = ∫ x, F x * F (x + 0) := by
    rw [integral_add_right_eq_self (fun x => F x * F x) s]
    simp only [add_zero]
  have hpt : (fun x => (F x - F (x + s)) ^ 2) = fun x =>
      F x * F (x + 0) - 2 * (F x * F (x + s)) + F (x + s) * F (x + s) := by
    funext x; simp only [add_zero]; ring
  have hi12 : Integrable fun x => F x * F (x + 0) - 2 * (F x * F (x + s)) :=
    hi1.sub (hi2.const_mul 2)
  rw [hpt, integral_add hi12 hi3, integral_sub hi1 (hi2.const_mul 2), integral_const_mul, htrans]
  simp only [autoCorr]
  ring

/-- **The autocorrelation deficit.** For a `Λ`-Lipschitz test supported in `[−R, R]`,
`A(0) − A(s) = ½∫(F(x) − F(x + s))² ≤ Λ² s² (R + |s|)`. -/
theorem autoCorr_zero_sub_le {F : ℝ → ℝ} {Λ R : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ x, R < |x| → F x = 0) (hΛ : ∀ a b, |F a - F b| ≤ Λ * |a - b|) (s : ℝ) :
    autoCorr F 0 - autoCorr F s ≤ Λ ^ 2 * s ^ 2 * (R + |s|) := by
  have hF := continuous_of_abs_sub_le hΛ
  have hFc : HasCompactSupport F := hasCompactSupport_of_eq_zero hsupp
  have hsq : (∫ x, (F x - F (x + s)) ^ 2) = 2 * autoCorr F 0 - 2 * autoCorr F s := by
    have := autoCorr_zero_sub_eq hF hFc s
    linarith
  -- the integrand lives on `[−R − |s|, R + |s|]` and is at most `Λ²s²`
  set a := -R - |s|
  set b := R + |s|
  have hab : a ≤ b := by have := abs_nonneg s; simp only [a, b]; linarith
  have hzero : ∀ x ∉ Icc a b, (F x - F (x + s)) ^ 2 = 0 := by
    intro x hx
    have hx' : b < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
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
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
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
  rw [hcongr, h]
  simp only [div_one]
  rw [Real.Gamma_nat_eq_factorial]
  have hpow : (1 / 2 : ℝ) ^ (-((k : ℝ) + 1)) = 2 ^ (k + 1) := by
    rw [Real.rpow_neg (by norm_num), ← Real.rpow_natCast, Real.div_rpow (by norm_num) (by norm_num),
      Real.one_rpow]
    push_cast
    field_simp
  rw [hpow]
  ring

/-! ## The slowly varying family -/

/-- The deficit integrand `(A_f(0) − A_f(u/r)) ½e^{−u/2}` is integrable on the half-line. -/
theorem integrableOn_autoCorr_deficit {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (r : ℝ) :
    IntegrableOn (fun u => (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u) (Ioi 0) := by
  have hAf := continuous_autoCorr hf hfc
  have hAb : ∀ t, |autoCorr f t| ≤ autoCorr f 0 := abs_autoCorr_le_autoCorr_zero hf hfc
  refine integrableOn_mul_horizonDensity (g := fun u => autoCorr f 0 - autoCorr f (u / r))
    (M := 2 * autoCorr f 0)
    (continuous_const.sub (hAf.comp (continuous_id.div_const r))) (fun t => ?_) 0
  show |autoCorr f 0 - autoCorr f (t / r)| ≤ 2 * autoCorr f 0
  have h1 := hAb (t / r)
  have h0 := (abs_nonneg _).trans (hAb 0)
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

/-- The horizon energy of the slowly varying family is `A_f(0)` minus the horizon average of the
deficit: `J(F_r) = A_f(0) − ∫_{u>0} (A_f(0) − A_f(u/r)) ½e^{−u/2} du`. -/
theorem horizonEnergy_rescaledTest_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {r : ℝ} (hr : 0 < r) :
    horizonEnergy (rescaledTest f r) = autoCorr f 0 -
      ∫ u in Ioi (0 : ℝ), (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u := by
  have hFr := continuous_rescaledTest hf r
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hAf := continuous_autoCorr hf hfc
  have hAb : ∀ t, |autoCorr f t| ≤ autoCorr f 0 := abs_autoCorr_le_autoCorr_zero hf hfc
  have hmass : (∫ u in Ioi (0 : ℝ), horizonDensity u) = 1 := by
    rw [integral_Ioi_horizonDensity]; simp
  have hci : IntegrableOn (fun u => autoCorr f 0 * horizonDensity u) (Ioi 0) :=
    (integrableOn_horizonDensity 0).const_mul _
  have hai : IntegrableOn (fun u => autoCorr f (u / r) * horizonDensity u) (Ioi 0) :=
    integrableOn_mul_horizonDensity (hAf.comp (continuous_id.div_const r)) (fun t => hAb _) 0
  rw [horizonEnergy_eq_horizonIntegral_autoCorr hFr hFrc, horizonIntegral]
  simp only [sub_mul]
  rw [integral_sub hci hai, integral_const_mul, hmass, mul_one]
  simp only [autoCorr_rescaledTest hr]
  ring

/-- **The horizon energy of the slowly varying family.** For a `Λ`-Lipschitz profile supported in
`[−1, 1]`, `A_f(0) − Λ²(8/r² + 48/r³) ≤ J(F_r) ≤ A_f(0)`. -/
theorem horizonEnergy_rescaledTest_ge {f : ℝ → ℝ} {Λ : ℝ} (hsupp : ∀ x, 1 < |x| → f x = 0)
    (hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b|) {r : ℝ} (hr : 0 < r) :
    autoCorr f 0 - Λ ^ 2 * (8 / r ^ 2 + 48 / r ^ 3) ≤ horizonEnergy (rescaledTest f r) ∧
      horizonEnergy (rescaledTest f r) ≤ autoCorr f 0 := by
  have hf := continuous_of_abs_sub_le hΛ
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  have hFr := continuous_rescaledTest hf r
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  refine ⟨?_, hA0 ▸ horizonEnergy_le hFr hFrc⟩
  have hmi : IntegrableOn (fun u => Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u)
      (Ioi 0) := by
    have h := ((integrableOn_pow_mul_horizonDensity 2).div_const (r ^ 2)).add
      ((integrableOn_pow_mul_horizonDensity 3).div_const (r ^ 3))
    exact IntegrableOn.congr_fun (h.const_mul (Λ ^ 2)) (fun u _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have hle : (∫ u in Ioi (0 : ℝ), (autoCorr f 0 - autoCorr f (u / r)) * horizonDensity u) ≤
      ∫ u in Ioi (0 : ℝ), Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) * horizonDensity u := by
    refine setIntegral_mono_on (integrableOn_autoCorr_deficit hf hfc r) hmi measurableSet_Ioi
      fun u hu => ?_
    have hu0 : 0 < u := hu
    refine mul_le_mul_of_nonneg_right ?_ (horizonDensity_nonneg u)
    have h := autoCorr_zero_sub_le zero_le_one hsupp hΛ (u / r)
    rw [abs_of_pos (div_pos hu0 hr)] at h
    calc autoCorr f 0 - autoCorr f (u / r) ≤ Λ ^ 2 * (u / r) ^ 2 * (1 + u / r) := h
      _ = Λ ^ 2 * (u ^ 2 / r ^ 2 + u ^ 3 / r ^ 3) := by field_simp
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
  rw [horizonEnergy_rescaledTest_eq hf hfc hr]
  linarith

/-- `r² exp(−c√r) → 0`. -/
theorem tendsto_sq_mul_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r : ℝ => r ^ 2 * Real.exp (-c * Real.sqrt r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (c * x) ^ 4 * Real.exp (-(c * x))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp (tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun r : ℝ => (c * Real.sqrt r) ^ 4 * Real.exp (-(c * Real.sqrt r))) atTop
      (𝓝 0) := h1.comp Real.tendsto_sqrt_atTop
  have h3 := h2.const_mul (c ^ 4)⁻¹
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with r hr0
  have hs : Real.sqrt r ^ 4 = r ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hr0]
  have hc4 : c ^ 4 ≠ 0 := by positivity
  rw [mul_pow, hs, show -(c * Real.sqrt r) = -c * Real.sqrt r by ring]
  field_simp

/-- `exp(−c√r) ≤ r^{−2}` eventually. -/
theorem eventually_exp_neg_sqrt_le_inv_sq {c : ℝ} (hc : 0 < c) :
    ∀ᶠ r in atTop, Real.exp (-c * Real.sqrt r) ≤ 1 / r ^ 2 := by
  filter_upwards [(tendsto_sq_mul_exp_neg_sqrt hc).eventually (eventually_le_nhds one_pos),
    eventually_gt_atTop 0] with r hr hr0
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **The prime error on the slowly varying family.** With universal `c, K`, every `Λ`-Lipschitz
profile supported in `[−1, 1]` has `|E_r(F_r)/S_r² − J(F_r)| ≤ K(Λ‖f‖₁ + A_f(0)) exp(−c√r)`. -/
theorem exists_abs_combEnergy_rescaledTest_div_sub_le :
    ∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in atTop, ∀ (f : ℝ → ℝ) (Λ : ℝ), (∀ x, 1 < |x| → f x = 0) →
      (∀ a b, |f a - f b| ≤ Λ * |a - b|) →
      |combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 -
          horizonEnergy (rescaledTest f r)| ≤
        K * (Λ * (∫ x, |f x|) + autoCorr f 0) * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combEnergy_div_sub_horizonEnergy_le
  refine ⟨c, hc, K, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with r hE hr1 f Λ hsupp hΛ
  have hr : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hf := continuous_of_abs_sub_le hΛ
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  have hA00 : 0 ≤ autoCorr f 0 := (abs_nonneg _).trans (abs_autoCorr_le_autoCorr_zero hf hfc 0)
  have hN1 : 0 ≤ ∫ x, |f x| := integral_nonneg fun _ => abs_nonneg _
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
  have hL1 : (∫ x, |rescaledTest f r x|) = Real.sqrt r * ∫ y, |f y| := by
    have h := Measure.integral_comp_div (fun y => |f y|) r
    simp only [rescaledTest, abs_mul, abs_of_pos (inv_pos.mpr hsr)]
    rw [integral_const_mul, h, abs_of_pos hr, smul_eq_mul]
    have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    calc (Real.sqrt r)⁻¹ * (r * ∫ y, |f y|) =
          (Real.sqrt r)⁻¹ * ((Real.sqrt r * Real.sqrt r) * ∫ y, |f y|) := by rw [hs]
      _ = Real.sqrt r * ∫ y, |f y| := by field_simp
  have hprod : Λr * (Real.sqrt r * ∫ y, |f y|) = Λ * (∫ y, |f y|) / r := by
    simp only [Λr]; field_simp
  have hrate := hE (rescaledTest f r) Λr hFrc hΛr
  rw [hL1, hprod, hA0] at hrate
  refine hrate.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK)
    (Real.exp_pos _).le)
  have : Λ * (∫ y, |f y|) / r ≤ Λ * ∫ y, |f y| := div_le_self (by positivity) hr1
  linarith

/-- **The comb is a translation up to an inverse-square deficit.** For a `Λ`-Lipschitz profile
supported in `[−1, 1]`, `0 ≤ A_f(0) − E_r(F_r)/S_r² ≤ C/r²` for all large `r`. -/
theorem exists_combEnergy_rescaledTest_deficit_le {f : ℝ → ℝ} {Λ : ℝ}
    (hsupp : ∀ x, 1 < |x| → f x = 0) (hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop,
      0 ≤ autoCorr f 0 - combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 ∧
      autoCorr f 0 - combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 ≤
        C / r ^ 2 := by
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combEnergy_rescaledTest_div_sub_le
  have hΛ0 : 0 ≤ Λ := by
    have h := hΛ 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have hf := continuous_of_abs_sub_le hΛ
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  set N1 := ∫ x, |f x|
  have hN1 : 0 ≤ N1 := integral_nonneg fun _ => abs_nonneg _
  have hA00 : 0 ≤ autoCorr f 0 := (abs_nonneg _).trans (abs_autoCorr_le_autoCorr_zero hf hfc 0)
  refine ⟨56 * Λ ^ 2 + K * (Λ * N1 + autoCorr f 0), by positivity, ?_⟩
  filter_upwards [hev, eventually_combMass_pos, eventually_ge_atTop 1,
    eventually_exp_neg_sqrt_le_inv_sq hc] with r hE hS hr1 hexp
  have hr : 0 < r := by linarith
  have hFr := continuous_rescaledTest hf r
  have hFrc := hasCompactSupport_rescaledTest hr hfc
  have hA0 : autoCorr (rescaledTest f r) 0 = autoCorr f 0 := by
    rw [autoCorr_rescaledTest hr, zero_div]
  have hrate := hE f Λ hsupp hΛ
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
  have herr : K * (Λ * N1 + autoCorr f 0) * Real.exp (-c * Real.sqrt r) ≤
      K * (Λ * N1 + autoCorr f 0) * (1 / r ^ 2) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
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

/-! ## The exact first correction -/

/-- **The quadratic deficit of a `C¹` profile.** `(A_f(0) − A_f(s))/s² → ½‖f′‖²` as `s → 0`. -/
theorem tendsto_autoCorr_deficit_div_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, 1 < |x| → f x = 0) :
    Tendsto (fun s => (autoCorr f 0 - autoCorr f s) / s ^ 2) (𝓝[≠] 0)
      (𝓝 (1 / 2 * ∫ x, deriv f x ^ 2)) := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  have hfcont : Continuous f := hf.continuous
  obtain ⟨Cl, hCl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  set Λ : ℝ := (Cl : ℝ)
  have hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b| := fun a b => by
    have := hCl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq] at this
  -- the difference quotients converge in `L²`
  set Q : ℝ → ℝ → ℝ := fun s x => ((f (x + s) - f x) / s) ^ 2
  have hlim : Tendsto (fun s => ∫ x, Q s x) (𝓝[≠] 0) (𝓝 (∫ x, deriv f x ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (Set.indicator (Icc (-2) 2) fun _ => Λ ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((hfcont.comp (continuous_id.add continuous_const)).sub hfcont).div_const s).pow 2
          |>.aestronglyMeasurable
    · have hball : ∀ᶠ s in 𝓝[≠] (0 : ℝ), |s| ≤ 1 := by
        refine nhdsWithin_le_nhds ?_
        filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with s hs
        simpa [Metric.mem_closedBall, Real.dist_eq] using hs
      filter_upwards [hball] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ Icc (-2 : ℝ) 2
      · rw [Set.indicator_of_mem hx]
        simp only [Q]
        rcases eq_or_ne s 0 with rfl | hs0
        · simp only [div_zero]; norm_num; positivity
        have h := hΛ (x + s) x
        rw [show x + s - x = s by ring] at h
        rw [div_pow, div_le_iff₀ (by positivity), ← sq_abs (f (x + s) - f x)]
        calc |f (x + s) - f x| ^ 2 ≤ (Λ * |s|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = Λ ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
      · rw [Set.indicator_of_notMem hx]
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        have hx2 : 2 < |x| := by
          rcases hx with hx | hx
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have h1 : f x = 0 := hsupp x (by linarith)
        have h2 : f (x + s) = 0 := hsupp _ (by
          have := abs_sub_abs_le_abs_sub x (-s)
          rw [sub_neg_eq_add, abs_neg] at this
          linarith)
        simp only [Q, h1, h2]; norm_num
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · refine Eventually.of_forall fun x => ?_
      have hd := ((hf.differentiable one_ne_zero) x).hasDerivAt.tendsto_slope_zero
      refine (hd.pow 2).congr fun s => ?_
      simp only [Q, smul_eq_mul]
      rw [div_eq_inv_mul]
  have hD := hlim.const_mul (1 / 2)
  refine hD.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  rw [autoCorr_zero_sub_eq hfcont hfc s, mul_div_assoc, ← integral_div]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Q]
  field_simp
  ring

/-- **The exact first correction of the horizon energy.** For a `C¹` profile supported in
`[−1, 1]`, `r² (A_f(0) − J(F_r)) → 4‖f′‖²`. -/
theorem tendsto_sq_mul_horizonEnergy_rescaledTest_deficit {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, 1 < |x| → f x = 0) :
    Tendsto (fun r => r ^ 2 * (autoCorr f 0 - horizonEnergy (rescaledTest f r))) atTop
      (𝓝 (4 * ∫ x, deriv f x ^ 2)) := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  have hfcont : Continuous f := hf.continuous
  obtain ⟨Cl, hCl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  set Λ : ℝ := (Cl : ℝ)
  have hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b| := fun a b => by
    have := hCl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq] at this
  set I := ∫ x, deriv f x ^ 2
  set D : ℝ → ℝ := fun s => (autoCorr f 0 - autoCorr f s) / s ^ 2
  have hDlim := tendsto_autoCorr_deficit_div_sq hf hsupp
  have hAf := continuous_autoCorr hfcont hfc
  have hAb : ∀ t, |autoCorr f t| ≤ autoCorr f 0 := abs_autoCorr_le_autoCorr_zero hfcont hfc
  -- `0 ≤ D(s) ≤ Λ²(1 + |s|)`
  have hD0 : ∀ s, 0 ≤ D s := fun s =>
    div_nonneg (by linarith [(abs_le.mp (hAb s)).2]) (sq_nonneg s)
  have hD1 : ∀ s, s ≠ 0 → D s ≤ Λ ^ 2 * (1 + |s|) := fun s hs => by
    have h := autoCorr_zero_sub_le zero_le_one hsupp hΛ s
    simp only [D]
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- dominated convergence on the half-line
  have hmeasD : Measurable D :=
    (measurable_const.sub hAf.measurable).div (continuous_pow 2).measurable
  have hlim : Tendsto (fun r => ∫ u in Ioi (0 : ℝ), u ^ 2 * D (u / r) * horizonDensity u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), u ^ 2 * (1 / 2 * I) * horizonDensity u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => Λ ^ 2 * (u ^ 2 * horizonDensity u + u ^ 3 * horizonDensity u)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun r =>
        (((continuous_pow 2).measurable.mul (hmeasD.comp (measurable_id.div_const r))).mul
          continuous_horizonDensity.measurable).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with r hr1
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : 0 < u := hu
      have hr0 : 0 < r := by linarith
      have hur : u / r ≤ u := div_le_self hu0.le hr1
      have hρ := horizonDensity_nonneg u
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hD0 (u / r); positivity)]
      have h1 := hD1 (u / r) (div_pos hu0 hr0).ne'
      rw [abs_of_pos (div_pos hu0 hr0)] at h1
      have h2 : D (u / r) ≤ Λ ^ 2 * (1 + u) := h1.trans (by nlinarith [sq_nonneg Λ])
      calc u ^ 2 * D (u / r) * horizonDensity u ≤ u ^ 2 * (Λ ^ 2 * (1 + u)) * horizonDensity u := by
            gcongr
        _ = Λ ^ 2 * (u ^ 2 * horizonDensity u + u ^ 3 * horizonDensity u) := by ring
    · exact (((integrableOn_pow_mul_horizonDensity 2).add
        (integrableOn_pow_mul_horizonDensity 3)).const_mul _)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : 0 < u := hu
      have hto : Tendsto (fun r : ℝ => u / r) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
        filter_upwards [eventually_gt_atTop 0] with r hr
        exact (div_pos hu0 hr).ne'
      exact ((hDlim.comp hto).const_mul (u ^ 2)).mul_const _
  have hval : (∫ u in Ioi (0 : ℝ), u ^ 2 * (1 / 2 * I) * horizonDensity u) = 4 * I := by
    have h2 := integral_pow_mul_horizonDensity 2
    have heq : (fun u => u ^ 2 * (1 / 2 * I) * horizonDensity u) =
        fun u => 1 / 2 * I * (u ^ 2 * horizonDensity u) := by funext u; ring
    rw [heq, integral_const_mul, h2]
    norm_num [Nat.factorial]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [horizonEnergy_rescaledTest_eq hfcont hfc hr, sub_sub_cancel, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 < u := hu
  simp only [D]
  field_simp

/-- **The exact first correction of the comb on the slowly varying family.** For a `C¹` profile
supported in `[−1, 1]`, `r² (A_f(0) − E_r(F_r)/S_r²) → 4‖f′‖²`: the comb's deficit is the
resolvent's first correction, and the prime error does not reach it. -/
theorem tendsto_sq_mul_combEnergy_rescaledTest_deficit {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ x, 1 < |x| → f x = 0) :
    Tendsto (fun r => r ^ 2 * (autoCorr f 0 -
        combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2)) atTop
      (𝓝 (4 * ∫ x, deriv f x ^ 2)) := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_eq_zero hsupp
  obtain ⟨Cl, hCl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hf one_ne_zero
  set Λ : ℝ := (Cl : ℝ)
  have hΛ : ∀ a b, |f a - f b| ≤ Λ * |a - b| := fun a b => by
    have := hCl.dist_le_mul a b
    rwa [Real.dist_eq, Real.dist_eq] at this
  obtain ⟨c, hc, K, hK, hev⟩ := exists_abs_combEnergy_rescaledTest_div_sub_le
  set M := K * (Λ * (∫ x, |f x|) + autoCorr f 0)
  -- the prime error, multiplied by `r²`, vanishes
  have herr : Tendsto (fun r => r ^ 2 * (horizonEnergy (rescaledTest f r) -
      combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2)) atTop (𝓝 0) := by
    have hmaj := (tendsto_sq_mul_exp_neg_sqrt hc).const_mul |M|
    rw [mul_zero] at hmaj
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hev] with r hr
    have h := hr f Λ hsupp hΛ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r), abs_sub_comm]
    calc r ^ 2 * |combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 -
          horizonEnergy (rescaledTest f r)| ≤ r ^ 2 * (M * Real.exp (-c * Real.sqrt r)) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg r)
      _ ≤ r ^ 2 * (|M| * Real.exp (-c * Real.sqrt r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self M)
            (Real.exp_pos _).le) (sq_nonneg r)
      _ = |M| * (r ^ 2 * Real.exp (-c * Real.sqrt r)) := by ring
  have h := (tendsto_sq_mul_horizonEnergy_rescaledTest_deficit hf hsupp).add herr
  rw [add_zero] at h
  refine h.congr fun r => ?_
  ring

end GaloisForLFunctions.ArithmeticCompensationTheory
