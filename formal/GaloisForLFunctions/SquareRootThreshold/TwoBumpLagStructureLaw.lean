import GaloisForLFunctions.SquareRootThreshold.CrystallizationHidesOffLineZeros

/-!
# The two-bump lag-structure law for arbitrary configurations

For periodic configurations visibility is a Toeplitz question about the lag symbol. For an
arbitrary tempered configuration the same two-point minor is available, with the lag symbol
replaced by the **smeared lag structure**

`S_β(v) = Σ_ρ m_ρ h_{k_β}(γ_ρ) e^{iγ_ρ v}`  (`lagStructure`),

`k_β = β ⋆ β̃` the Weil kernel of a bump `β` supported in `[−w, w]`. For on-line zeros
`h_{k_β}(γ) = |h_β(γ)|²` and `S_β` is the structure factor of the ordinates, smeared at the scale
`1/w`; an off-line zero of depth `δ` enters with the weights `e^{±δv}`.

* **Two-bump identity** (`W_twoBump`). For the two-bump test `β(t + v/2) + τ β(t − v/2)`,
  `W(f, f) = (1 + |τ|²) S(0) + τ S(v) + τ̄ S(−v)`.
* **Lag-structure law** (`norm_lagStructure_le_of_weil_nonneg`,
  `exists_visible_of_lagStructure`). If the configuration is invisible at aperture `a`, then for
  every lag `0 ≤ v ≤ 2(a − w)`:  `|S(v) + conj S(−v)| ≤ 2 Re S(0)`; conversely any violation is a
  visibility witness at aperture `v/2 + w`.

The tempered summability (`summable_lagStructure`) uses the decay `|h_{k_β}(x)| ≲ (1 + |Re x|)⁻²`
(`RHTower.norm_paperFT_le_decay`) against `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞`. This turns the visibility of
an aperiodic cluster into a single scalar inequality on its smeared lag structure.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

theorem re_gammaOf (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by
  simp [gammaOf]

theorem im_gammaOf (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by
  simp [gammaOf]

/-- The smeared lag structure `S_β(v) = Σ_ρ m_ρ h_{k_β}(γ_ρ) e^{iγ_ρ v}`. -/
def lagStructure (Z : ZeroConfig) (β : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (EF.weilTest β β) (gammaOf ρ) * cexp (I * gammaOf ρ * v)

/-- The smeared lag structure of a tempered configuration converges absolutely. -/
theorem summable_lagStructure (Z : ZeroConfig) (hZ : TemperedConfig Z) {β : ℝ → ℂ}
    (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) (v : ℝ) :
    Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℂ) * paperFT (EF.weilTest β β) (gammaOf ρ) * cexp (I * gammaOf ρ * v) := by
  have hβc : HasCompactSupport β := hasCompactSupport_of_support_subset_abs hβs
  have hβts : tsupport β ⊆ Icc (-(2 * w / 2)) (2 * w / 2) := by
    rw [show 2 * w / 2 = w by ring]
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have := hβs u hu
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  have hK := EF.weilTest_contDiff hβ hβ.continuous hβc
  have hKs := weilTest_abs_le hβts hβts
  set C : ℝ := 4 * ((∫ u, ‖EF.weilTest β β u‖) + ∫ u, ‖deriv (deriv (EF.weilTest β β)) u‖)
    with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by norm_num) (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _))
  set K : ℝ := Real.exp (|2 * w|) * C * Real.exp (|v|) * (4 / 3) with hKdef
  refine Summable.of_norm_bounded (g := fun ρ : Z.carrier =>
    K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))) (hZ.mul_left K) fun ρ => ?_
  have hstrip := Z.strip ρ.1 ρ.2
  have him : |(gammaOf ρ).im| ≤ 1 / 2 := by
    rw [im_gammaOf, abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hdecay := norm_paperFT_le_decay hK hKs (gammaOf ρ)
  have hexp : ‖cexp (I * gammaOf ρ * v)‖ ≤ Real.exp |v| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (I * gammaOf ρ * v).re = -((gammaOf ρ).im * v) := by
      simp [Complex.mul_re]
    rw [this]
    have := abs_mul (gammaOf ρ).im v
    have h1 : |(gammaOf ρ).im| * |v| ≤ |v| := by nlinarith [abs_nonneg v]
    linarith [neg_abs_le ((gammaOf ρ).im * v)]
  have hden : 1 / (1 + |(gammaOf ρ).re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq (gammaOf ρ)) := by
    rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
      (by nlinarith [mul_self_nonneg (gammaOf ρ).re, mul_self_nonneg (gammaOf ρ).im])]
    have h1 : (gammaOf ρ).im * (gammaOf ρ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
    nlinarith [abs_nonneg (gammaOf ρ).re, sq_abs (gammaOf ρ).re]
  have hE1 : Real.exp (|(gammaOf ρ).im| * (2 * w)) ≤ Real.exp |2 * w| := by
    apply Real.exp_le_exp.mpr
    have := abs_mul (gammaOf ρ).im (2 * w)
    calc |(gammaOf ρ).im| * (2 * w) ≤ |(gammaOf ρ).im| * |2 * w| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
      _ ≤ 1 * |2 * w| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |2 * w| := one_mul _
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hP : ‖paperFT (EF.weilTest β β) (gammaOf ρ)‖ ≤
      Real.exp |2 * w| * C * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ))) := by
    refine hdecay.trans ?_
    rw [show Real.exp (|(gammaOf ρ).im| * (2 * w)) * C / (1 + |(gammaOf ρ).re|) ^ 2 =
      Real.exp (|(gammaOf ρ).im| * (2 * w)) * C * (1 / (1 + |(gammaOf ρ).re|) ^ 2) by ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hE1 hC0) hden (by positivity) (by positivity)
  calc (Z.mult ρ : ℝ) * ‖paperFT (EF.weilTest β β) (gammaOf ρ)‖ * ‖cexp (I * gammaOf ρ * v)‖
      ≤ (Z.mult ρ : ℝ) * (Real.exp |2 * w| * C * ((4 / 3) / (1 + Complex.normSq (gammaOf ρ)))) *
          Real.exp |v| := by
        have hN : 0 ≤ 1 + Complex.normSq (gammaOf ρ) := by
          have := Complex.normSq_nonneg (gammaOf ρ); linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left hP hm) hexp (norm_nonneg _)
          (mul_nonneg hm (mul_nonneg (mul_nonneg (Real.exp_pos _).le hC0)
            (div_nonneg (by norm_num) hN)))
    _ = K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by rw [hKdef]; ring

/-- The two-bump test `β(t + v/2) + τ β(t − v/2)`. -/
def twoBump (β : ℝ → ℂ) (v : ℝ) (τ : ℂ) : ℝ → ℂ := bumpTest β v ![1, τ]

theorem paperFT_twoBump {β : ℝ → ℂ} (hβc : Continuous β) (hβcs : HasCompactSupport β) (v : ℝ)
    (τ : ℂ) (z : ℂ) :
    paperFT (twoBump β v τ) z =
      (cexp (-(I * z * (v / 2))) + τ * cexp (I * z * (v / 2))) * paperFT β z := by
  rw [twoBump, paperFT_bumpTest hβc hβcs, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, lagPoint, Fin.val_zero,
    Fin.val_one, Nat.cast_zero, Nat.cast_one]
  congr 1
  congr 1
  · congr 1; push_cast; ring
  · congr 2; push_cast; ring

/-- **Two-bump identity.** `W(f, f) = (1 + |τ|²) S(0) + τ S(v) + τ̄ S(−v)` for the two-bump
test of a tempered configuration. -/
theorem W_twoBump (Z : ZeroConfig) (hZ : TemperedConfig Z) {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) (v : ℝ) (τ : ℂ) :
    Z.W (twoBump β v τ) (twoBump β v τ) = (1 + ‖τ‖ ^ 2) * lagStructure Z β 0 +
      τ * lagStructure Z β v + conj τ * lagStructure Z β (-v) := by
  have hβc : HasCompactSupport β := hasCompactSupport_of_support_subset_abs hβs
  have hS := fun v' => summable_lagStructure Z hZ hβ hβs v'
  have hpt : ∀ ρ : Z.carrier, Z.Wsummand (twoBump β v τ) (twoBump β v τ) ρ =
      (1 + ‖τ‖ ^ 2) * ((Z.mult ρ : ℂ) * paperFT (EF.weilTest β β) (gammaOf ρ) *
        cexp (I * gammaOf ρ * ((0 : ℝ) : ℂ))) +
      τ * ((Z.mult ρ : ℂ) * paperFT (EF.weilTest β β) (gammaOf ρ) * cexp (I * gammaOf ρ * v)) +
      conj τ * ((Z.mult ρ : ℂ) * paperFT (EF.weilTest β β) (gammaOf ρ) *
        cexp (I * gammaOf ρ * ((-v : ℝ) : ℂ))) := by
    intro ρ
    rw [ZeroConfig.Wsummand, paperFT_twoBump hβ.continuous hβc, paperFT_twoBump hβ.continuous hβc,
      EF.paperFT_weilTest hβ.continuous hβ.continuous hβc hβc]
    simp only [map_mul, map_add, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_conj,
      Complex.conj_ofReal, map_div₀, Complex.conj_ofNat]
    rw [← Complex.mul_conj' τ]
    have e1 : cexp (-(I * gammaOf ρ * (v / 2))) * cexp (-(-I * gammaOf ρ * (v / 2))) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    have e2 : cexp (-(I * gammaOf ρ * (v / 2))) * cexp (-I * gammaOf ρ * (v / 2)) =
        cexp (I * gammaOf ρ * ((-v : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e3 : cexp (I * gammaOf ρ * (v / 2)) * cexp (-(-I * gammaOf ρ * (v / 2))) =
        cexp (I * gammaOf ρ * v) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e4 : cexp (I * gammaOf ρ * (v / 2)) * cexp (-I * gammaOf ρ * (v / 2)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    linear_combination
      (↑(Z.mult ↑ρ) * paperFT β (gammaOf ↑ρ) * (starRingEnd ℂ) (paperFT β ((starRingEnd ℂ) (gammaOf ↑ρ)))) *
        (e1 + τ * conj τ * e4 + conj τ * e2 + τ * e3)
  rw [ZeroConfig.W, tsum_congr hpt, Summable.tsum_add ((hS 0).mul_left _ |>.add ((hS v).mul_left _))
    ((hS (-v)).mul_left _), Summable.tsum_add ((hS 0).mul_left _) ((hS v).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rfl

/-- **Lag-structure law.** If a tempered configuration is invisible at aperture `a`, then for every
lag `0 ≤ v` with `v/2 + w ≤ a`, `|S(v) + conj S(−v)| ≤ 2 Re S(0)`. -/
theorem norm_lagStructure_le_of_weil_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v a : ℝ}
    (hv : 0 ≤ v) (hva : v / 2 + w ≤ a)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) :
    ‖lagStructure Z β v + conj (lagStructure Z β (-v))‖ ≤ 2 * (lagStructure Z β 0).re := by
  set X := lagStructure Z β v + conj (lagStructure Z β (-v)) with hX
  have key : ∀ τ : ℂ, 0 ≤ (1 + ‖τ‖ ^ 2) * (lagStructure Z β 0).re + (τ * X).re := by
    intro τ
    have hf := contDiff_bumpTest hβ v ![1, τ]
    have hfs := tsupport_bumpTest_subset hβs hv (a := a) (n := 2) (by push_cast; linarith) ![1, τ]
    have h1 := h _ hf hfs
    rw [show bumpTest β v ![1, τ] = twoBump β v τ from rfl, W_twoBump Z hZ hβ hβs v τ] at h1
    have h2 : (conj τ * lagStructure Z β (-v)).re = (τ * conj (lagStructure Z β (-v))).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj]
    rw [Complex.add_re, Complex.add_re, h2, show (1 + (‖τ‖ : ℂ) ^ 2) = ((1 + ‖τ‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul] at h1
    rw [hX, mul_add, Complex.add_re]
    linarith
  by_cases hX0 : X = 0
  · rw [hX0, norm_zero]
    have := key 0
    simpa using this
  set τ : ℂ := -(conj X / ‖X‖) with hτ
  have hτn : ‖τ‖ = 1 := by
    rw [hτ, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.mpr hX0)]
  have hτX : (τ * X).re = -‖X‖ := by
    rw [hτ, neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    rw [show ((‖X‖ ^ 2 : ℝ) : ℂ) / (‖X‖ : ℂ) = ((‖X‖ : ℝ) : ℂ) by
      have : (‖X‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hX0
      push_cast; field_simp]
    simp
  have := key τ
  rw [hτn, hτX] at this
  linarith

/-- **Visibility from the lag structure.** If `|S(v) + conj S(−v)| > 2 Re S(0)` for some `v ≥ 0`,
the configuration is visible at aperture `v/2 + w`, by a two-bump test. -/
theorem exists_visible_of_lagStructure (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v)
    (hlt : 2 * (lagStructure Z β 0).re < ‖lagStructure Z β v + conj (lagStructure Z β (-v))‖) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) ∧
      (Z.W f f).re < 0 := by
  by_contra hcon
  push Not at hcon
  have := norm_lagStructure_le_of_weil_nonneg Z hZ hβ hβs hv le_rfl hcon
  linarith

end GaloisForLFunctions.SquareRootThreshold
