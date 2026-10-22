import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGammaEndpoint
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# The literal contragredient Euler collar

The positive von Mangoldt connection is absolutely summable on the concrete `L¹` adiabatic
preimage for every `a > 0`: dilation supplies the indispensable extra factor `m⁻¹`.  Fourier
transport of that honest `L¹` sum constructs the opposite collar in tempered distributions.  Its
Schwartz pairings are then the literal inverse-dilation series with coefficient
`Λ(m)m⁻ᵃ⁻¹`.

This domain-sensitive construction matters.  The inverse-dilation series is not asserted to be a
bounded operator on all of `L¹` or all tempered distributions near the critical wall.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap FourierTransform ArithmeticFunction

noncomputable section

/-- Scalar of one physical von Mangoldt dilation. -/
def deningerAdiabaticVonMangoldtScalar (a : ℝ) (m : ℕ) : ℂ :=
  (((vonMangoldt m : ℝ) * deningerAdiabaticMobiusCoefficient a m : ℝ) : ℂ)

/-- One literal full-line physical Euler term. -/
def deningerAdiabaticPhysicalEulerTerm
    (a : ℝ) (h : DeningerMeyerSource) (m : ℕ) (x : ℝ) : ℂ :=
  deningerAdiabaticVonMangoldtScalar a m *
    deningerAdiabaticEvenPreimage a h ((m : ℝ) * x)

theorem deningerAdiabaticPhysicalEulerTerm_integrable
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) (m : ℕ) :
    Integrable (deningerAdiabaticPhysicalEulerTerm a h m) := by
  by_cases hm : m = 0
  · subst m
    have hz : deningerAdiabaticPhysicalEulerTerm a h 0 = fun _ : ℝ => 0 := by
      funext x
      simp [deningerAdiabaticPhysicalEulerTerm, deningerAdiabaticVonMangoldtScalar]
    rw [hz]
    exact integrable_zero ℝ ℂ volume
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hscale := (deningerAdiabaticEvenPreimage_integrable ha h).comp_mul_left' hmR
    exact hscale.const_mul (deningerAdiabaticVonMangoldtScalar a m)

/-- Full-line absolute mass of the concrete adiabatic preimage. -/
def deningerAdiabaticEvenPreimageNormMass
    (a : ℝ) (h : DeningerMeyerSource) : ℝ :=
  ∫ x : ℝ, ‖deningerAdiabaticEvenPreimage a h x‖

theorem deningerAdiabaticEvenPreimageNormMass_nonneg
    (a : ℝ) (h : DeningerMeyerSource) :
    0 ≤ deningerAdiabaticEvenPreimageNormMass a h :=
  integral_nonneg fun _ => norm_nonneg _

theorem integral_norm_deningerAdiabaticPhysicalEulerTerm
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) {m : ℕ} (hm : 0 < m) :
    (∫ x : ℝ, ‖deningerAdiabaticPhysicalEulerTerm a h m x‖) =
      (vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
        (m : ℝ)⁻¹ * deningerAdiabaticEvenPreimageNormMass a h := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hΛ : 0 ≤ vonMangoldt m := vonMangoldt_nonneg
  have hc : 0 < deningerAdiabaticMobiusCoefficient a m := Real.exp_pos _
  simp only [deningerAdiabaticPhysicalEulerTerm, deningerAdiabaticVonMangoldtScalar,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ,
    abs_of_pos hc]
  rw [MeasureTheory.integral_const_mul]
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ => ‖deningerAdiabaticEvenPreimage a h y‖) (m : ℝ)
  rw [abs_inv, abs_of_pos hmR, smul_eq_mul] at hscale
  rw [hscale, deningerAdiabaticEvenPreimageNormMass]
  ring

/-- Summable `L¹` majorant `‖Mₐh‖₁ log(m)/m^(a+1)`. -/
def deningerAdiabaticPhysicalEulerMajorant
    (a : ℝ) (h : DeningerMeyerSource) (m : ℕ) : ℝ :=
  deningerAdiabaticEvenPreimageNormMass a h *
    (Real.log (m : ℝ) / (m : ℝ) ^ (a + 1))

theorem summable_deningerAdiabaticPhysicalEulerMajorant
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (deningerAdiabaticPhysicalEulerMajorant a h) :=
  (Mertens.summable_log_div_rpow (by linarith : 1 < a + 1)).mul_left _

theorem integral_norm_deningerAdiabaticPhysicalEulerTerm_le
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (m : ℕ) :
    (∫ x : ℝ, ‖deningerAdiabaticPhysicalEulerTerm a h m x‖) ≤
      deningerAdiabaticPhysicalEulerMajorant a h m := by
  by_cases hm : 0 < m
  · rw [integral_norm_deningerAdiabaticPhysicalEulerTerm ha.le h hm]
    have hmass := deningerAdiabaticEvenPreimageNormMass_nonneg a h
    have hcoeff : 0 ≤ deningerAdiabaticMobiusCoefficient a m := (Real.exp_pos _).le
    calc
      (vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
          (m : ℝ)⁻¹ * deningerAdiabaticEvenPreimageNormMass a h ≤
        (Real.log (m : ℝ) * deningerAdiabaticMobiusCoefficient a m) *
          (m : ℝ)⁻¹ * deningerAdiabaticEvenPreimageNormMass a h := by
            gcongr
            exact vonMangoldt_le_log
      _ = deningerAdiabaticPhysicalEulerMajorant a h m := by
        calc
          (Real.log (m : ℝ) * deningerAdiabaticMobiusCoefficient a m) *
              (m : ℝ)⁻¹ * deningerAdiabaticEvenPreimageNormMass a h =
            deningerAdiabaticEvenPreimageNormMass a h * Real.log (m : ℝ) *
              (deningerAdiabaticMobiusCoefficient a m * (m : ℝ)⁻¹) := by ring
          _ = deningerAdiabaticEvenPreimageNormMass a h * Real.log (m : ℝ) *
              (m : ℝ) ^ (-(a + 1)) := by
            rw [deningerAdiabaticMobiusCoefficient_mul_inv a hm]
          _ = deningerAdiabaticPhysicalEulerMajorant a h m := by
            rw [deningerAdiabaticPhysicalEulerMajorant,
              Real.rpow_neg (show (0 : ℝ) ≤ (m : ℝ) by positivity)]
            ring
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp [deningerAdiabaticPhysicalEulerTerm,
      deningerAdiabaticPhysicalEulerMajorant, deningerAdiabaticVonMangoldtScalar]

theorem summable_integral_norm_deningerAdiabaticPhysicalEulerTerm
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (fun m : ℕ =>
      ∫ x : ℝ, ‖deningerAdiabaticPhysicalEulerTerm a h m x‖) :=
  (summable_deningerAdiabaticPhysicalEulerMajorant ha h).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (integral_norm_deningerAdiabaticPhysicalEulerTerm_le ha h)

/-- The literal von Mangoldt sum is integrable before Fourier transport. -/
theorem deningerAdiabaticPhysicalEuler_integrable
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Integrable (fun x : ℝ =>
      ∑' m : ℕ, deningerAdiabaticPhysicalEulerTerm a h m x) :=
  GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun m => deningerAdiabaticPhysicalEulerTerm_integrable ha.le h m)
    (summable_integral_norm_deningerAdiabaticPhysicalEulerTerm ha h)

/-- The literal full-line sum is the existing physical Euler series on the radial variable. -/
theorem tsum_deningerAdiabaticPhysicalEulerTerm_eq
    (a : ℝ) (h : DeningerMeyerSource) (x : ℝ) :
    (∑' m : ℕ, deningerAdiabaticPhysicalEulerTerm a h m x) =
      deningerAdiabaticEulerPositive a (deningerAdiabaticMobiusPreimage a h) |x| := by
  rw [deningerAdiabaticEulerPositive]
  apply tsum_congr
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [deningerAdiabaticPhysicalEulerTerm, deningerAdiabaticVonMangoldtScalar]
  · have hmR : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rw [deningerAdiabaticPhysicalEulerTerm, deningerAdiabaticEvenPreimage]
    simp only [abs_mul, abs_of_nonneg hmR]
    rfl

/-- `L¹` realization of one physical von Mangoldt term. -/
def deningerAdiabaticPhysicalEulerTermLp
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) (m : ℕ) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  (deningerAdiabaticPhysicalEulerTerm_integrable ha h m).toL1
    (deningerAdiabaticPhysicalEulerTerm a h m)

theorem norm_deningerAdiabaticPhysicalEulerTermLp
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource) (m : ℕ) :
    ‖deningerAdiabaticPhysicalEulerTermLp ha h m‖ =
      ∫ x : ℝ, ‖deningerAdiabaticPhysicalEulerTerm a h m x‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Integrable.coeFn_toL1
    (deningerAdiabaticPhysicalEulerTerm_integrable ha h m)] with x hx
  have hx' : (deningerAdiabaticPhysicalEulerTermLp ha h m) x =
      deningerAdiabaticPhysicalEulerTerm a h m x := by
    change ((deningerAdiabaticPhysicalEulerTerm_integrable ha h m).toL1
      (deningerAdiabaticPhysicalEulerTerm a h m)) x = _
    exact hx
  rw [hx']

theorem summable_deningerAdiabaticPhysicalEulerTermLp
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (fun m : ℕ => deningerAdiabaticPhysicalEulerTermLp ha.le h m) := by
  refine Summable.of_norm_bounded
    (summable_integral_norm_deningerAdiabaticPhysicalEulerTerm ha h) fun m => ?_
  exact (norm_deningerAdiabaticPhysicalEulerTermLp ha.le h m).le

theorem summable_norm_deningerAdiabaticPhysicalEulerTermLp
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (fun m : ℕ => ‖deningerAdiabaticPhysicalEulerTermLp ha.le h m‖) :=
  (summable_integral_norm_deningerAdiabaticPhysicalEulerTerm ha h).congr
    (fun m => (norm_deningerAdiabaticPhysicalEulerTermLp ha.le h m).symm)

/-- The physical von Mangoldt `L¹` sum is exactly the derivative already constructed from the
Möbius side. -/
theorem tsum_deningerAdiabaticPhysicalEulerTermLp_eq
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    (∑' m : ℕ, deningerAdiabaticPhysicalEulerTermLp ha.le h m) =
      deningerAdiabaticEulerPositiveLp a h := by
  apply MeasureTheory.Lp.ext
  have hcoe := MeasureTheory.Lp.coeFn_tsum
    ((tsum_enorm_ne_top_iff_summable_norm).2
      (summable_norm_deningerAdiabaticPhysicalEulerTermLp ha h))
  have hterm : ∀ m : ℕ,
      (fun x : ℝ => (deningerAdiabaticPhysicalEulerTermLp ha.le h m) x) =ᵐ[volume]
        deningerAdiabaticPhysicalEulerTerm a h m :=
    fun m => Integrable.coeFn_toL1
      (deningerAdiabaticPhysicalEulerTerm_integrable ha.le h m)
  have htermAll : ∀ᵐ x : ℝ ∂volume, ∀ m : ℕ,
      (deningerAdiabaticPhysicalEulerTermLp ha.le h m) x =
        deningerAdiabaticPhysicalEulerTerm a h m x :=
    eventually_countable_forall.2 hterm
  filter_upwards [hcoe, htermAll,
    deningerAdiabaticEulerPositiveLp_ae_eq_physical ha h] with x hsum hterms hphysical
  rw [hsum, hphysical, ← tsum_deningerAdiabaticPhysicalEulerTerm_eq a h x]
  exact tsum_congr hterms

/-- The physical Euler derivative as an actual integrable-density distribution. -/
theorem deningerAdiabaticEulerPositiveDistribution_eq_physical
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    deningerAdiabaticEulerPositiveDistribution a h =
      deningerL1Distribution (deningerAdiabaticPhysicalEuler_integrable ha h) := by
  ext g
  rw [deningerAdiabaticEulerPositiveDistribution,
    MeasureTheory.Lp.toTemperedDistribution_apply, deningerL1Distribution_apply]
  apply integral_congr_ae
  filter_upwards [deningerAdiabaticEulerPositiveLp_ae_eq_physical ha h] with x hx
  rw [hx, tsum_deningerAdiabaticPhysicalEulerTerm_eq]

/-- The opposite Euler connection on the concrete Fourier collar. -/
def deningerAdiabaticEulerNegativeDistribution
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  𝓕 (deningerAdiabaticEulerPositiveDistribution a h)

/-- One opposite-collar pairing term before rewriting it as an inverse dilation. -/
def deningerAdiabaticEulerNegativePairingTerm
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource)
    (g : 𝓢(ℝ, ℂ)) (m : ℕ) : ℂ :=
  deningerL1SchwartzPairing (𝓕 g)
    (deningerAdiabaticPhysicalEulerTermLp ha h m)

/-- Exact additive-Fourier modulus of one positive physical Euler term. -/
theorem fourier_deningerAdiabaticPhysicalEulerTerm
    (a : ℝ) (h : DeningerMeyerSource) {m : ℕ} (hm : 0 < m) (ξ : ℝ) :
    𝓕 (deningerAdiabaticPhysicalEulerTerm a h m) ξ =
      ((((vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
        (m : ℝ)⁻¹ : ℝ) : ℂ)) *
        𝓕 (deningerAdiabaticEvenPreimage a h) ((m : ℝ)⁻¹ * ξ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  let F : ℝ → ℂ := deningerAdiabaticEvenPreimage a h
  let c : ℂ := deningerAdiabaticVonMangoldtScalar a m
  have hterm : deningerAdiabaticPhysicalEulerTerm a h m =
      c • fun x : ℝ => F ((m : ℝ) * x) := by
    funext x
    simp only [deningerAdiabaticPhysicalEulerTerm, c, F, Pi.smul_apply, smul_eq_mul]
  have hfun : (fun x : ℝ => F ((m : ℝ) * x)) =
      fun x : ℝ => F (x / (m : ℝ)⁻¹) := by
    funext x
    congr 1
    field_simp
  have hscale := GaloisForLFunctions.HTGeometry.fourier_comp_div_eq_abs_smul
    (f := F) (a := (m : ℝ)⁻¹) (inv_ne_zero hmR.ne') ξ
  rw [abs_inv, abs_of_pos hmR] at hscale
  have hsmul : 𝓕 (c • fun x : ℝ => F ((m : ℝ) * x)) =
      c • 𝓕 (fun x : ℝ => F ((m : ℝ) * x)) := by
    exact VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
      (innerₗ ℝ) (fun x : ℝ => F ((m : ℝ) * x)) c
  calc
    𝓕 (deningerAdiabaticPhysicalEulerTerm a h m) ξ =
        𝓕 (c • fun x : ℝ => F ((m : ℝ) * x)) ξ := by rw [hterm]
    _ = c • 𝓕 (fun x : ℝ => F ((m : ℝ) * x)) ξ := by
      exact congrFun hsmul ξ
    _ = c • ((m : ℝ)⁻¹ • 𝓕 F ((m : ℝ)⁻¹ * ξ)) := by
      rw [hfun, hscale]
    _ = ((((vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
          (m : ℝ)⁻¹ : ℝ) : ℂ)) *
          𝓕 (deningerAdiabaticEvenPreimage a h) ((m : ℝ)⁻¹ * ξ) := by
      simp only [c, F, deningerAdiabaticVonMangoldtScalar, Complex.real_smul,
        smul_eq_mul]
      rw [← mul_assoc, ← Complex.ofReal_mul]

/-- Each opposite pairing term is literally the inverse dilation
`Λ(m)m⁻ᵃ⁻¹ U_(1/m)` of the Fourier collar. -/
theorem deningerAdiabaticEulerNegativePairingTerm_eq_inverseDilation
    {a : ℝ} (ha : 0 ≤ a) (h : DeningerMeyerSource)
    (g : 𝓢(ℝ, ℂ)) (m : ℕ) :
    deningerAdiabaticEulerNegativePairingTerm ha h g m =
      ∫ ξ : ℝ, g ξ •
        (((((vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
          (m : ℝ)⁻¹ : ℝ) : ℂ)) *
          𝓕 (deningerAdiabaticEvenPreimage a h) ((m : ℝ)⁻¹ * ξ)) := by
  by_cases hm : 0 < m
  · rw [deningerAdiabaticEulerNegativePairingTerm,
      deningerL1SchwartzPairing_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hliteral :
        (∫ x : ℝ, (𝓕 g) x • (deningerAdiabaticPhysicalEulerTermLp ha h m) x) =
          ∫ x : ℝ, (𝓕 g) x • deningerAdiabaticPhysicalEulerTerm a h m x := by
      apply integral_congr_ae
      filter_upwards [Integrable.coeFn_toL1
        (deningerAdiabaticPhysicalEulerTerm_integrable ha h m)] with x hx
      have hx' : (deningerAdiabaticPhysicalEulerTermLp ha h m) x =
          deningerAdiabaticPhysicalEulerTerm a h m x := by
        change ((deningerAdiabaticPhysicalEulerTerm_integrable ha h m).toL1
          (deningerAdiabaticPhysicalEulerTerm a h m)) x = _
        exact hx
      rw [hx']
    rw [hliteral]
    have hmove := deningerFourier_mul_formula g.integrable
      (deningerAdiabaticPhysicalEulerTerm_integrable ha h m)
    have hcoe : (((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = 𝓕 ((g : ℝ → ℂ)) :=
      SchwartzMap.fourier_coe g
    rw [hcoe, hmove]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [fourier_deningerAdiabaticPhysicalEulerTerm a h hm ξ]
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hzero : deningerAdiabaticPhysicalEulerTermLp ha h 0 = 0 := by
      apply MeasureTheory.Lp.ext
      filter_upwards [Integrable.coeFn_toL1
        (deningerAdiabaticPhysicalEulerTerm_integrable ha h 0)] with x hx
      have hx' : (deningerAdiabaticPhysicalEulerTermLp ha h 0) x =
          deningerAdiabaticPhysicalEulerTerm a h 0 x := by
        change ((deningerAdiabaticPhysicalEulerTerm_integrable ha h 0).toL1
          (deningerAdiabaticPhysicalEulerTerm a h 0)) x = _
        exact hx
      rw [hx']
      simp [deningerAdiabaticPhysicalEulerTerm, deningerAdiabaticVonMangoldtScalar]
    simp [deningerAdiabaticEulerNegativePairingTerm, hzero,
      deningerAdiabaticVonMangoldtScalar]

/-- The opposite collar is the distributional sum of all ordinary-integer terms. -/
theorem deningerAdiabaticEulerNegativeDistribution_apply_eq_tsum
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticEulerNegativeDistribution a h g =
      ∑' m : ℕ, deningerAdiabaticEulerNegativePairingTerm ha.le h g m := by
  rw [deningerAdiabaticEulerNegativeDistribution,
    TemperedDistribution.fourier_apply]
  change deningerL1SchwartzPairing (𝓕 g)
    (deningerAdiabaticEulerPositiveLp a h) = _
  rw [← tsum_deningerAdiabaticPhysicalEulerTermLp_eq ha h]
  exact (deningerL1SchwartzPairing (𝓕 g)).map_tsum
    (summable_deningerAdiabaticPhysicalEulerTermLp ha h)

/-- **Literal contragredient ordinary-integer series.** -/
theorem deningerAdiabaticEulerNegativeDistribution_apply_eq_inverseDilation_tsum
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticEulerNegativeDistribution a h g =
      ∑' m : ℕ, ∫ ξ : ℝ, g ξ •
        (((((vonMangoldt m * deningerAdiabaticMobiusCoefficient a m) *
          (m : ℝ)⁻¹ : ℝ) : ℂ)) *
          𝓕 (deningerAdiabaticEvenPreimage a h) ((m : ℝ)⁻¹ * ξ)) := by
  rw [deningerAdiabaticEulerNegativeDistribution_apply_eq_tsum ha h g]
  apply tsum_congr
  exact deningerAdiabaticEulerNegativePairingTerm_eq_inverseDilation ha.le h g

/-- The first component of the diagonal collar derivative is the concrete negative connection. -/
theorem deningerAdiabaticCollarDerivative_fst_eq_negative
    (a : ℝ) (h : DeningerMeyerSource) :
    (deningerAdiabaticCollarDerivative a h).1 =
      deningerAdiabaticEulerNegativeDistribution a h := by
  rfl

end

end RHTower
