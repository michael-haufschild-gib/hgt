import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayerOfTheCubicTwistHasASmoothedMainTerm

/-!
# Continuations through the untwisted layer have smoothed main terms

A tool for the twisted unit layers. Let `G₁`, `G₂` be bounded remainders and `α`, `β` holomorphic on
`Re s > 5/4`. The function

`L(w) = α(2w)S₁(w) + (2w − 4/3)β(2w)(Λ̃₁ − Λ̃₂)(2w)`   (`layerCont`),

`S₁` the continued untwisted squarefree theta series and `Λ̃ᵢ` the regularized pairings, is holomorphic on
`5/8 < Re w < 13/6` except a simple pole at `2/3` of residue `α(4/3)Res S₁`: the factor `2w − 4/3` absorbs the at
most simple poles of the pairings (`layerCont_simple_pole`). If `α` is bounded and `β(2w)` grows at most like
`(1 + |w|)²e^{4π|Im w|}`, then `e^{w²}L(w) = O((1 + Im² w)^{−1})` (`layerCont_gaussian_bound`). So a bounded ideal
coefficient whose series agrees with `L` on `4 < Re 2w < 13/3`, `Im w > 0` has the smoothed main term
`e^{4/9}α(4/3)Res S₁·X^{2/3}` with remainder `O(X^a)` for every `5/8 < a < 2/3` (`layerCont_smoothed_main_term`).

The Gaussian-smoothed sums of bounded coefficients converge absolutely (`summable_smoothed`), so they are linear in
the coefficient; the unit-layer coefficients `φ(gen A)σ(A)` of the characters of `O/q` are bounded (`unitCoeff`).
-/

noncomputable section

open MeasureTheory Filter Function Topology Complex
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### Absolute convergence of the smoothed sums -/

namespace BoundedIdealCoefficient

variable {a : Ideal O → ℂ} (ha : BoundedIdealCoefficient a)
include ha

/-- `e^{−u²/4} ≤ e⁴e^{−2u}`, so the smoothed sum is dominated by `e⁴X²Σ_A N(A)^{−2}`. -/
theorem summable_smoothed {X : ℝ} (hX : 0 < X) :
    Summable (fun A : Ideal O =>
      a A * (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)) := by
  have hpi : 0 < 2 * Real.sqrt Real.pi := by positivity
  refine Summable.of_norm_bounded (g := fun A : Ideal O => Real.exp 4 * X ^ (2 : ℝ) / (2 * Real.sqrt Real.pi) *
    ‖unramifiedNormWeight (2 : ℂ) A‖) ((unramifiedNormWeight_summable_norm (2 : ℂ) (by norm_num)).mul_left _)
    fun A => ?_
  by_cases hA : primaryIdealGenerator A = 0
  · rw [ha.of_bad A hA, zero_mul, norm_zero]
    positivity
  · have hN : 0 < (Ideal.absNorm A : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal A hA)))
    have hy : 0 < (Ideal.absNorm A : ℝ) / X := div_pos hN hX
    set u := Real.log ((Ideal.absNorm A : ℝ) / X) with hu
    have hg0 : 0 ≤ RHTower.smoothAFELogGaussian u := by
      unfold RHTower.smoothAFELogGaussian
      positivity
    have hexp : Real.exp (-u ^ 2 / 4) ≤ Real.exp 4 * ((Ideal.absNorm A : ℝ) / X) ^ (-2 : ℝ) := by
      rw [Real.rpow_def_of_pos hy, ← hu, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (u - 4)]
    have hpow : ((Ideal.absNorm A : ℝ) / X) ^ (-2 : ℝ) = X ^ (2 : ℝ) * (Ideal.absNorm A : ℝ) ^ (-2 : ℝ) := by
      rw [Real.div_rpow hN.le hX.le, Real.rpow_neg hX.le, div_eq_mul_inv, inv_inv, mul_comm]
    have hw : ‖unramifiedNormWeight (2 : ℂ) A‖ = (Ideal.absNorm A : ℝ) ^ (-2 : ℝ) := by
      rw [unramifiedNormWeight_of_good _ A hA, Complex.norm_natCast_cpow_of_pos
        (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal A hA)))]
      norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0, hw]
    calc
      ‖a A‖ * RHTower.smoothAFELogGaussian u ≤ 1 * RHTower.smoothAFELogGaussian u :=
        mul_le_mul_of_nonneg_right (ha.norm_le A) hg0
      _ = Real.exp (-u ^ 2 / 4) / (2 * Real.sqrt Real.pi) := by
        rw [one_mul]
        rfl
      _ ≤ Real.exp 4 * ((Ideal.absNorm A : ℝ) / X) ^ (-2 : ℝ) / (2 * Real.sqrt Real.pi) :=
        div_le_div_of_nonneg_right hexp hpi.le
      _ = _ := by
        rw [hpow]
        ring

end BoundedIdealCoefficient

/-- **Linearity in the coefficient.** -/
theorem gaussianSmoothedSum_combination {a₁ a₂ a₃ : Ideal O → ℂ} (h₁ : BoundedIdealCoefficient a₁)
    (h₂ : BoundedIdealCoefficient a₂) (h₃ : BoundedIdealCoefficient a₃) (c₁ c₂ c₃ : ℂ) {X : ℝ} (hX : 0 < X) :
    gaussianSmoothedSum (fun A => c₁ * a₁ A + c₂ * a₂ A + c₃ * a₃ A) X =
      c₁ * gaussianSmoothedSum a₁ X + c₂ * gaussianSmoothedSum a₂ X + c₃ * gaussianSmoothedSum a₃ X := by
  have s₁ := (h₁.summable_smoothed hX).mul_left c₁
  have s₂ := (h₂.summable_smoothed hX).mul_left c₂
  have s₃ := (h₃.summable_smoothed hX).mul_left c₃
  unfold gaussianSmoothedSum
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← s₁.tsum_add s₂, ← (s₁.add s₂).tsum_add s₃]
  exact tsum_congr fun A => by ring

/-! ### The continuation through the untwisted layer -/

section Layer

variable {G₁ G₂ : HyperbolicSpace → ℂ} (h₁ : RemainderData G₁) (h₂ : RemainderData G₂) (α β : ℂ → ℂ)

/-- `α(2w)S₁(w) + (2w − 4/3)β(2w)(Λ̃₁ − Λ̃₂)(2w)`. -/
def layerCont (w : ℂ) : ℂ :=
  α (2 * w) * regularizedUntwistedTheta w +
    (2 * w - 4 / 3) * β (2 * w) * (h₁.regPairing (2 * w) - h₂.regPairing (2 * w))

theorem layerCont_differentiableAt (hα : ∀ s : ℂ, 5 / 4 < s.re → DifferentiableAt ℂ α s)
    (hβ : ∀ s : ℂ, 5 / 4 < s.re → DifferentiableAt ℂ β s) (w : ℂ) (hw : 5 / 8 < w.re)
    (hB : w.re < 13 / 6) (hp : w ≠ 2 / 3) : DifferentiableAt ℂ (layerCont h₁ h₂ α β) w := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 2 * w) w := differentiableAt_id.const_mul 2
  have hr : (2 * w).re = 2 * w.re := by simp
  have hs1 : 5 / 4 < (2 * w).re := by rw [hr]; linarith
  have hs2 : (2 * w).re < 13 / 3 := by rw [hr]; linarith
  have hp' : 2 * w ≠ 4 / 3 := fun h => hp (by linear_combination h / 2)
  have hX : DifferentiableAt ℂ (fun s => h₁.regPairing s - h₂.regPairing s) (2 * w) :=
    (h₁.regPairing_differentiableAt _ (by linarith) hs2 hp').sub
      (h₂.regPairing_differentiableAt _ (by linarith) hs2 hp')
  exact (((hα _ hs1).comp w hlin).mul (regularizedUntwistedTheta_differentiableAt w hw hB hp)).add
    (((hlin.sub_const _).mul ((hβ _ hs1).comp w hlin)).mul (hX.comp w hlin))

/-- **The simple pole.** `(w − 2/3)L(w) → α(4/3)Res S₁`. -/
theorem layerCont_simple_pole (hα : DifferentiableAt ℂ α (4 / 3)) (hβ : DifferentiableAt ℂ β (4 / 3)) :
    Tendsto (fun w => (w - 2 / 3) * layerCont h₁ h₂ α β w) (𝓝[≠] (2 / 3 : ℂ))
      (𝓝 (α (4 / 3) * untwistedThetaResidue)) := by
  have h43 : (2 : ℂ) * (2 / 3) = 4 / 3 := by norm_num
  have hcomp : ∀ {f : ℂ → ℂ}, DifferentiableAt ℂ f (4 / 3) →
      Tendsto (fun w : ℂ => f (2 * w)) (𝓝[≠] (2 / 3 : ℂ)) (𝓝 (f (4 / 3))) := by
    intro f hf
    have hc : ContinuousAt (fun w : ℂ => f (2 * w)) (2 / 3) :=
      ContinuousAt.comp_of_eq (g := f) (f := fun w : ℂ => 2 * w) hf.continuousAt
        (continuous_const_mul (2 : ℂ)).continuousAt (by norm_num)
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(2 / 3 : ℂ)}ᶜ))
    simpa only [h43] using h
  have hX : Tendsto (fun s => (s - 4 / 3) ^ 2 * (h₁.regPairing s - h₂.regPairing s))
      (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
    have h := h₁.regPairing_near_four_thirds.sub h₂.regPairing_near_four_thirds
    rw [sub_zero] at h
    exact h.congr fun s => by ring
  have hX2 := hX.comp two_mul_tendsto_punctured
  have hrest : Tendsto (fun w : ℂ => (w - 2 / 3) *
      ((2 * w - 4 / 3) * β (2 * w) * (h₁.regPairing (2 * w) - h₂.regPairing (2 * w))))
      (𝓝[≠] (2 / 3 : ℂ)) (𝓝 0) := by
    have h := ((hcomp hβ).mul hX2).const_mul (1 / 2 : ℂ)
    rw [mul_zero, mul_zero] at h
    refine h.congr fun w => ?_
    simp only [Function.comp]
    ring
  have hmain := ((hcomp hα).mul regularizedUntwistedTheta_simple_pole).add hrest
  rw [add_zero] at hmain
  refine hmain.congr fun w => ?_
  rw [layerCont]
  ring

/-- **The Gaussian bound.** -/
theorem layerCont_gaussian_bound (a : ℝ) (ha : 5 / 8 < a) (ha2 : a ≤ 2) {Kα Kβ : ℝ}
    (hα : ∀ s : ℂ, 2 * a ≤ s.re → s.re ≤ 4 → ‖α s‖ ≤ Kα) (hKα : 0 ≤ Kα) (hKβ : 0 ≤ Kβ)
    (hβ : ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖β (2 * w)‖ ≤ Kβ * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖Complex.exp (w ^ 2) * layerCont h₁ h₂ α β w‖ ≤ C * (1 + w.im ^ 2)⁻¹ := by
  obtain ⟨Kh, hKh, hkh⟩ := h₁.regPairing_vertical_bound (2 * a) 4 (by linarith) (by norm_num)
  obtain ⟨Ks, hKs, hks⟩ := h₂.regPairing_vertical_bound (2 * a) 4 (by linarith) (by norm_num)
  obtain ⟨C₁, hC₁, hc₁⟩ := continuedUntwistedTheta_gaussian_vertical_bound a 2 ha ha2 (by norm_num)
  have hf : ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖(2 * w - 4 / 3) * β (2 * w) * (h₁.regPairing (2 * w) - h₂.regPairing (2 * w))‖ ≤
        (2 * Kβ * (Kh + Ks)) * (1 + ‖w‖) ^ 3 * Real.exp (4 * Real.pi * |w.im|) := by
    intro w hwa hw2 hwi
    have hr : (2 * w).re = 2 * w.re := by simp
    have hi : (2 * w).im = 2 * w.im := by simp
    have hi1 : 1 ≤ |(2 * w).im| := by rw [hi, abs_mul]; norm_num; linarith
    have hsa : 2 * a ≤ (2 * w).re := by rw [hr]; linarith
    have hs4 : (2 * w).re ≤ 4 := by rw [hr]; linarith
    have hX : ‖h₁.regPairing (2 * w) - h₂.regPairing (2 * w)‖ ≤ Kh + Ks :=
      (norm_sub_le _ _).trans (add_le_add (hkh _ hsa hs4 hi1) (hks _ hsa hs4 hi1))
    have hlin : ‖2 * w - 4 / 3‖ ≤ 2 * (1 + ‖w‖) := by
      have h := norm_sub_le (2 * w) (4 / 3 : ℂ)
      rw [norm_mul] at h
      norm_num at h
      linarith only [h, norm_nonneg w]
    have hb := hβ w hwa hw2 hwi
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (2 * (1 + ‖w‖)) * (Kβ * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|)) * (Kh + Ks) := by
        gcongr
      _ = _ := by ring
  obtain ⟨C₂, hC₂, hc₂⟩ := gaussian_bound_of_exp_growth (by linarith : (0 : ℝ) ≤ a)
    (by positivity : 0 ≤ 2 * Kβ * (Kh + Ks)) 3 hf
  refine ⟨Kα * C₁ + C₂, by positivity, fun w hwa hw2 hwi => ?_⟩
  have hr : (2 * w).re = 2 * w.re := by simp
  have hi0 : w.im ≠ 0 := by intro h; rw [h, abs_zero] at hwi; linarith
  rw [layerCont, mul_add, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ (hc₂ w hwa hw2 hwi))
  rw [regularizedUntwistedTheta_eq_nonreal w (by linarith) hi0,
    show Complex.exp (w ^ 2) * (α (2 * w) * continuedUntwistedTheta w) =
      α (2 * w) * (Complex.exp (w ^ 2) * continuedUntwistedTheta w) by ring, norm_mul]
  calc
    _ ≤ Kα * (C₁ * (1 + w.im ^ 2)⁻¹) :=
      mul_le_mul (hα _ (by rw [hr]; linarith) (by rw [hr]; linarith)) (hc₁ w hwa hw2 hwi) (norm_nonneg _) hKα
    _ = _ := by ring

/-- **The smoothed main term.** A bounded ideal coefficient whose series is `L(w)` on `2 < Re w < 13/6`,
`Im w > 0` has `Σ_A c(A)g(log(N(A)/X)) = e^{4/9}α(4/3)Res S₁·X^{2/3} + O(X^a)` for `5/8 < a < 2/3`. -/
theorem layerCont_smoothed_main_term {cf : Ideal O → ℂ} (hc : BoundedIdealCoefficient cf)
    (hαd : ∀ s : ℂ, 5 / 4 < s.re → DifferentiableAt ℂ α s) (hβd : ∀ s : ℂ, 5 / 4 < s.re → DifferentiableAt ℂ β s)
    (hup : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → layerCont h₁ h₂ α β (s / 2) = idealSeries cf (s / 2))
    (a : ℝ) (ha : 5 / 8 < a) (ha' : a < 2 / 3)
    (hαb : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 * a ≤ s.re → s.re ≤ 4 → ‖α s‖ ≤ K)
    (hβb : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖β (2 * w)‖ ≤ K * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum cf X - (X : ℂ) ^ (2 / 3 : ℂ) *
        (Complex.exp ((2 / 3 : ℂ) ^ 2) * (α (4 / 3) * untwistedThetaResidue))‖ ≤ K * X ^ a := by
  obtain ⟨Kα, hKα, hα⟩ := hαb
  obtain ⟨Kβ, hKβ, hβ⟩ := hβb
  obtain ⟨C, -, hC⟩ := layerCont_gaussian_bound h₁ h₂ α β a ha (by linarith) hα hKα hKβ hβ
  have hd := layerCont_differentiableAt h₁ h₂ α β hαd hβd
  have heq : ∀ w : ℂ, 1 < w.re → w.re < 13 / 6 → layerCont h₁ h₂ α β w = idealSeries cf w := by
    intro w hw hB
    let U : Set ℂ := {z | 1 < z.re ∧ z.re < 13 / 6}
    have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    have hconv : Convex ℝ U :=
      (convex_halfSpace_gt ⟨fun _ _ => rfl, fun c z => by simp⟩ (1 : ℝ)).inter
        (convex_halfSpace_lt ⟨fun _ _ => rfl, fun c z => by simp⟩ (13 / 6 : ℝ))
    have hf : AnalyticOnNhd ℂ (layerCont h₁ h₂ α β) U := by
      apply DifferentiableOn.analyticOnNhd _ hU
      intro z hz
      apply (hd z (by linarith only [hz.1]) hz.2 ?_).differentiableWithinAt
      intro he
      have hre := hz.1
      rw [he] at hre
      norm_num at hre
    have hg : AnalyticOnNhd ℂ (idealSeries cf) U := by
      apply DifferentiableOn.analyticOnNhd _ hU
      intro z hz
      exact (hc.idealSeries_differentiableAt z hz.1).differentiableWithinAt
    have hcm : (25 / 12 + Complex.I : ℂ) ∈ U := by norm_num [U]
    apply hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected hcm _ ⟨hw, hB⟩
    have hopen : IsOpen {z : ℂ | 2 < z.re ∧ z.re < 13 / 6 ∧ 0 < z.im} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt continuous_const Complex.continuous_im))
    filter_upwards [hopen.mem_nhds (by norm_num)] with z hz
    have h := hup (2 * z) (by simp; linarith only [hz.1]) (by simp; linarith only [hz.2.1])
      (by simp; linarith only [hz.2.2])
    rwa [show 2 * z / 2 = z by ring] at h
  refine hc.gaussianSmoothedSum_main_term ha'
    (fun w hwa hw2 hp => hd w (by linarith) (by linarith) hp)
    (layerCont_simple_pole h₁ h₂ α β (hαd _ (by norm_num)) (hβd _ (by norm_num))) hC (fun t => ?_)
  exact heq _ (by norm_num) (by norm_num)

end Layer

/-! ### The unit-layer coefficients of the characters of `O/q` -/

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `φ(gen A)σ(A)` on the squarefree ideals with a primary generator. -/
def unitCoeff (φ : MulChar P.Res ℂ) (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 then
    φ (P.res (primaryIdealGenerator A)) *
      (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A) else 0

theorem unitCoeff_bounded (φ : MulChar P.Res ℂ) : BoundedIdealCoefficient (P.unitCoeff φ) where
  norm_le A := by
    unfold unitCoeff
    split_ifs with h
    · have hp := (primaryIdealGenerator_spec A h.2).2
      rw [norm_mul, norm_mul, norm_pow, norm_thetaSquareWeight A h.2 h.1, mul_one]
      exact mul_le_one₀ (P.norm_mulChar_le _ _) (pow_nonneg (norm_nonneg _) _)
        (pow_le_one₀ (norm_nonneg _) (GaloisForLFunctions.OrderSixMetaplecticTheory.norm_symbol_le _ _ hp))
    · simp only [norm_zero, zero_le_one]
  of_bad A hA := by simp [unitCoeff, hA]

theorem idealSeries_unitCoeff (φ : MulChar P.Res ℂ) (w : ℂ) :
    idealSeries (P.unitCoeff φ) w = P.twistedSquarefreeSeriesW φ 1 w := by
  unfold idealSeries twistedSquarefreeSeriesW unitCoeff
  refine tsum_congr fun A => ?_
  by_cases hA : primaryIdealGenerator A = 0
  · simp [unramifiedNormWeight_of_bad _ A hA]
  · by_cases hs : Squarefree A
    · simp [hs, hA]
    · simp [hs]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
