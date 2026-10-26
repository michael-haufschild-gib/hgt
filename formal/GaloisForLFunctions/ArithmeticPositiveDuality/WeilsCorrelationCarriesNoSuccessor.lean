import GaloisForLFunctions.ArithmeticPositiveDuality.AnAtomicArchimedeanSpectrumBlindsTheSuccessor
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Weil's correlation carries no successor

By P13 the Riemann hypothesis holds iff some positive-definite `φ` on `Aff(ℚ)` restricts on the
dilations to Weil's spline correlation `ratCorr`. This file determines the successor of every such
`φ`.

**Theorem** (`weil_successor_blind`, unconditional). If `φ` is positive definite on `Aff(ℚ)` and
`φ(x ↦ ux) = ratCorr(u)` for `u > 0`, then `φ(x ↦ x + b) = α` for all `b ≠ 0`, with
`0 ≤ α ≤ φ(1)`.

Mechanism. Such a `φ` forces RH, hence full-cone Weil positivity of `Λ`
(`weilPositiveFull_vonMangoldt_of_riemannHypothesis`), so the spline correlation is
`∫ e^{iry}|B̂(r)|² dμ_Λ(r)` (`weilFullFunctional_transl_weilTest_eq_integral`), and `μ_Λ` is carried
by the countable set of critical ordinates (`boundaryMeasure_vonMangoldt_compl_criticalOrdinates`).
The dilation part is therefore an atomic archimedean correlation `Σ_γ w_γ u^{−iγ}`,
`Σ w_γ = W(B, B) < ∞`, and the atomic blindness theorem
(`successor_blind_of_atomic_archimedean`) applies.

So there is no successor prescription compatible with Weil's correlation beyond the trivial ones:
a constant on `b ≠ 0`, with the remaining mass at `b = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open RHTower RHTower.WeilSpectral Zeta23
open RHTower.WeilConditional (criticalOrdinates countable_criticalOrdinates
  boundaryMeasure_vonMangoldt_compl_criticalOrdinates)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open ArithmeticCastelnuovoSeveri

/-! ### Reindexing a countable atomic sum by `ℕ` -/

/-- A countable set of reals and nonnegative summable weights on it are carried by an injective
sequence with nonnegative summable weights, zero off the set. -/
theorem exists_nat_reindex {S : Set ℝ} (hS : S.Countable) (w : S → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hws : Summable w) :
    ∃ (γ : ℕ → ℝ) (c : ℕ → ℝ), Function.Injective γ ∧ (∀ n, 0 ≤ c n) ∧ Summable c ∧
      ∀ F : ℝ → ℂ, ∑' n, (c n : ℂ) * F (γ n) = ∑' x : S, (w x : ℂ) * F x := by
  classical
  obtain ⟨e, he⟩ := Set.countable_iff_exists_injective.mp hS
  have hinf : (Sᶜ).Infinite := by
    intro hfin
    apply Cardinal.not_countable_real
    rw [← Set.union_compl_self S]
    exact hS.union hfin.countable
  set g := hinf.natEmbedding
  set γ : ℕ → ℝ := fun n => if h : n ∈ Set.range e then ((h.choose : S) : ℝ) else g n
  set c : ℕ → ℝ := fun n => if h : n ∈ Set.range e then w h.choose else 0
  have hchoose : ∀ x : S, (Set.mem_range_self x : e x ∈ Set.range e).choose = x := fun x =>
    he (Set.mem_range_self x).choose_spec
  have hγe : ∀ x : S, γ (e x) = x := fun x => by
    simp only [γ, dif_pos (Set.mem_range_self x), hchoose]
  have hce : ∀ x : S, c (e x) = w x := fun x => by
    simp only [c, dif_pos (Set.mem_range_self x), hchoose]
  have hc0 : ∀ n, n ∉ Set.range e → c n = 0 := fun n hn => by simp only [c, dif_neg hn]
  refine ⟨γ, c, ?_, fun n => ?_, ?_, fun F => ?_⟩
  · intro n n' h
    by_cases hn : n ∈ Set.range e <;> by_cases hn' : n' ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hn
      obtain ⟨x', rfl⟩ := hn'
      rw [hγe, hγe] at h
      rw [Subtype.ext h]
    · obtain ⟨x, rfl⟩ := hn
      simp only [γ, dif_neg hn', hγe] at h
      exact absurd (h ▸ x.2) (g n').2
    · obtain ⟨x', rfl⟩ := hn'
      simp only [γ, dif_neg hn, hγe] at h
      exact absurd (h.symm ▸ x'.2) (g n).2
    · simp only [γ, dif_neg hn, dif_neg hn'] at h
      exact g.injective (Subtype.ext h)
  · by_cases hn : n ∈ Set.range e
    · simp only [c, dif_pos hn]; exact hw _
    · rw [hc0 n hn]
  · refine (he.summable_iff fun n hn => hc0 n hn).mp ?_
    have : c ∘ e = w := funext hce
    rw [this]
    exact hws
  · have hsupp : Function.support (fun n => (c n : ℂ) * F (γ n)) ⊆ Set.range e := fun n hn => by
      by_contra h
      exact hn (by simp only [hc0 n h, Complex.ofReal_zero, zero_mul])
    rw [← he.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    simp only [hγe, hce]

/-! ### The spectral expansion of Weil's correlation -/

/-- The spline `B`. -/
abbrev splineB : ℝ → ℂ := cx cubicSpline

theorem contDiff_splineB : ContDiff ℝ 2 splineB := cx_contDiff contDiff_cubicSpline

theorem hasCompactSupport_splineB : HasCompactSupport splineB :=
  cx_hasCompactSupport hasCompactSupport_cubicSpline

/-- Under full-cone Weil positivity of `Λ`, `C(y) = ∫ e^{iry}|B̂(r)|² dμ_Λ(r)`. -/
theorem splineCorr_eq_integral
    (hW : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (y : ℝ) :
    splineCorr y = ∫ r : ℝ, cexp (I * (r : ℂ) * y) * ((‖paperFT splineB r‖ ^ 2 : ℝ) : ℂ)
      ∂boundaryMeasure hW := by
  -- `B(· − y) ⋆ B̃ = (B ⋆ B̃)(· − y)`
  have hshift : EF.weilTest (ArithmeticCastelnuovoSeveri.translate y splineB) splineB =
      transl y (EF.weilTest splineB splineB) := by
    funext x
    rw [transl, RHTower.WeilSpectral.weilTest_apply, RHTower.WeilSpectral.weilTest_apply]
    rw [← integral_add_right_eq_self (μ := volume)
      (fun u : ℝ => ArithmeticCastelnuovoSeveri.translate y splineB u * conj (splineB (u - x))) y]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ArithmeticCastelnuovoSeveri.translate, add_sub_cancel_right]
    congr 3
    ring
  unfold splineCorr
  rw [hshift, weilFullFunctional_transl_weilTest_eq_integral hW contDiff_splineB
    hasCompactSupport_splineB contDiff_splineB hasCompactSupport_splineB y]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

variable (hW : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The atomic weights `w_γ = μ_Λ{γ}·|B̂(γ)|²` on the critical ordinates. -/
def weilWeight (x : criticalOrdinates) : ℝ :=
  (boundaryMeasure hW).real {(x : ℝ)} * ‖paperFT splineB ((x : ℝ) : ℂ)‖ ^ 2

theorem weilWeight_nonneg (x : criticalOrdinates) : 0 ≤ weilWeight hW x :=
  mul_nonneg measureReal_nonneg (sq_nonneg _)

theorem integrableOn_weilIntegrand (y : ℝ) (s : Set ℝ) :
    IntegrableOn (fun r : ℝ => cexp (I * (r : ℂ) * y) * ((‖paperFT splineB r‖ ^ 2 : ℝ) : ℂ)) s
      (boundaryMeasure hW) := by
  have hint := integrable_norm_sq_paperFT hW contDiff_splineB hasCompactSupport_splineB
  refine (hint.mono' ?_ (Eventually.of_forall fun r => ?_)).integrableOn
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hint.ofReal.aestronglyMeasurable
  · rw [norm_mul, WeilSpectral.norm_cexp_I_mul_ofReal, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- The weights are summable: a finite partial sum is the integral of `|B̂|²` over a finite set. -/
theorem summable_weilWeight : Summable (weilWeight hW) := by
  have hint := integrable_norm_sq_paperFT hW contDiff_splineB hasCompactSupport_splineB
  refine summable_of_sum_le (fun x => weilWeight_nonneg hW x)
    (c := ∫ r : ℝ, ‖paperFT splineB r‖ ^ 2 ∂boundaryMeasure hW) fun T => ?_
  have h := setIntegral_finset (μ := boundaryMeasure hW) (T.map (Function.Embedding.subtype _))
    hint.integrableOn
  rw [Finset.sum_map] at h
  calc ∑ x ∈ T, weilWeight hW x
      = ∫ r in ((T.map (Function.Embedding.subtype _) : Finset ℝ) : Set ℝ),
          ‖paperFT splineB r‖ ^ 2 ∂boundaryMeasure hW := by
        rw [h]; rfl
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall fun r => sq_nonneg _)

/-- **Weil's correlation is atomic.** Under full-cone Weil positivity of `Λ`,
`ratCorr(u) = Σ_γ w_γ u^{−iγ}` over the critical ordinates. -/
theorem ratCorr_eq_tsum (u : posUnits) :
    ratCorr u = ∑' x : criticalOrdinates,
      (weilWeight hW x : ℂ) * archChar (-(x : ℝ)) ((u : ℚˣ) : ℚ) := by
  have hrestrict : (boundaryMeasure hW).restrict criticalOrdinates = boundaryMeasure hW :=
    Measure.restrict_eq_self_of_ae_mem
      (ae_iff.mpr (boundaryMeasure_vonMangoldt_compl_criticalOrdinates hW))
  rw [ratCorr, splineCorr_eq_integral hW]
  conv_lhs => rw [← hrestrict]
  rw [setIntegral_countable _ countable_criticalOrdinates (integrableOn_weilIntegrand hW _ _)]
  refine tsum_congr fun x => ?_
  rw [weilWeight, archChar, Complex.real_smul]
  simp only [logPos, Complex.ofReal_neg, mul_neg, neg_mul, Complex.ofReal_mul]
  ring

/-! ### Blindness -/

/-- **Weil's correlation carries no successor.** If `φ` is positive definite on `Aff(ℚ)` and its
dilation part is Weil's spline correlation, `φ(x ↦ ux) = ratCorr(u)` for `u > 0`, then
`φ(x ↦ x + b) = α` for every `b ≠ 0`, with `0 ≤ α ≤ φ(1)`. -/
theorem weil_successor_blind {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hdil : ∀ u : posUnits, φ (dilation (u : ℚˣ)) = ratCorr u) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ (φ 1).re ∧ ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  have hRH : RiemannHypothesis := riemannHypothesis_iff_exists_affine_posDef.mpr ⟨φ, hφ, hdil⟩
  have hW := weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  obtain ⟨γ, c, hγ, hc, hcs, hsum⟩ := exists_nat_reindex countable_criticalOrdinates
    (weilWeight hW) (weilWeight_nonneg hW) (summable_weilWeight hW)
  refine successor_blind_of_atomic_archimedean hφ (γ := fun n => -γ n)
    (fun n n' h => hγ (neg_injective h)) hc hcs fun u hu => ?_
  rw [show dilation u = dilation ((⟨u, hu⟩ : posUnits) : ℚˣ) from rfl, hdil, ratCorr_eq_tsum hW]
  exact (hsum fun r => archChar (-r) (u : ℚ)).symm

end GaloisForLFunctions.ArithmeticPositiveDuality
