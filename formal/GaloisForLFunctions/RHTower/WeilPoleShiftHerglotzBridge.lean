import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane

/-!
# The pole-shifted Weil functional is Herglotz positivity

For real weights `lam` and real `κ` put

`W_κ(k) = W_lam(k) + κ (k̂(i/2) + k̂(−i/2))`   (`shiftFunctional`),

the Weil functional with its pole term counted `1 + κ` times, and call `lam` `κ`-Weil-positive
(`WeilPositiveShift κ lam`) when `Re W_κ(f ⋆ f̃) ≥ 0` for every `C²` compactly supported test `f`.

**Theorem** (`exists_herglotz_of_weilPositiveShift`).  If `lam` is `κ`-Weil-positive, then
`Σ |lam(n)| n^{−σ} < ∞` for every `σ > 1`, and the shifted Weil function

`Φ_κ(s) = ½ψ(s/2) − ½ log π + (1 + κ)(1/s + 1/(s−1)) − Σ_{n≥2} lam(n) n^{−s}`
(`shiftWeilFunction`)

continues holomorphically from `Re s > 1` to `Re s > ½` with nonnegative real part.  No growth
hypothesis on `lam` is needed.  For `κ = 0` this is `herglotzWeilPositive_of_weilPositiveFull`.

**Proof.**
* The pole term vanishes on polar tests (`f̂(±i/2) = 0`), so `lam` is Weil-positive there and its
  Dirichlet series converges absolutely on `Re s > 1`
  (`summable_abs_div_rpow_of_weilPositiveShift`).
* The pole term is linear, Hermitian, continuous under translation and commutes with averages.  So
  `y ↦ W_κ(τ_y(f ⋆ f̃))` is positive definite and continuous, its Bochner measures `ν_f` satisfy
  `|ĝ|² ν_f = |f̂|² ν_g`, and the mollifier measures glued over shells give one measure `μ_κ` with
  `W_κ(f ⋆ f̃) = ∫ |f̂|² dμ_κ` (`shiftFunctional_weilTest_eq_lintegral`).
* On the one-sided exponential tests `W_κ` tends to `Re Φ_κ(s)/Re(s − ½)` for `Re s > 1`, the pole
  term contributing `(1 + κ)` times its `κ = 0` limit.  Hence `Re Φ_κ` is the Poisson integral of
  `μ_κ`, and `H(z) = ∫ (1/(z − ir) − ir/(1 + r²)) dμ_κ(r)` gives the continuation `H(s − ½) + iC`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real ComplexConjugate NNReal ENNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-! ## The shifted functional -/

/-- The Weil functional with the pole term counted `1 + κ` times. -/
def shiftFunctional (κ : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  weilFullFunctional lam k + (κ : ℂ) * polePart k

/-- Weil positivity with the pole term counted `1 + κ` times. -/
def WeilPositiveShift (κ : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (shiftFunctional κ lam (EF.weilTest f f)).re

theorem polePart_weilTest_eq_zero {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0) :
    polePart (EF.weilTest f f) = 0 := by
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  unfold polePart
  rw [EF.paperFT_weilTest hf hf hfc hfc, EF.paperFT_weilTest hf hf hfc hfc, hc1, hc2, neg_div,
    hp, hm]
  simp

/-- Polar tests do not see the pole term, so `κ`-Weil positivity gives polar Weil positivity. -/
theorem weilPositive_of_weilPositiveShift {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) :
    WeilPositive lam :=
  weilPositive_of_polar fun f hf hfc hp hm => by
    have h := hW f hf hfc
    rwa [shiftFunctional, polePart_weilTest_eq_zero hf.continuous hfc hp hm, mul_zero,
      add_zero] at h

/-- `κ`-Weil-positive weights converge absolutely on `Re s > 1`. -/
theorem summable_abs_div_rpow_of_weilPositiveShift {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
  WeilMeanSquare.summable_abs_div_rpow_of_weilPositive (weilPositive_of_weilPositiveShift hW) hσ

/-! ## Linearity and Hermitian symmetry -/

theorem polePart_add_of_admissible {k₁ k₂ : ℝ → ℂ} (h₁ : Admissible k₁) (h₂ : Admissible k₂) :
    polePart (k₁ + k₂) = polePart k₁ + polePart k₂ := by
  unfold polePart
  rw [paperFT_add h₁ h₂, paperFT_add h₁ h₂]
  ring

theorem polePart_smul_left (a : ℂ) (k : ℝ → ℂ) : polePart (a • k) = a * polePart k := by
  unfold polePart
  rw [paperFT_smul, paperFT_smul]
  ring

theorem polePart_tilde (k : ℝ → ℂ) : polePart (EF.tilde k) = conj (polePart k) := by
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  unfold polePart
  rw [EF.paperFT_tilde, EF.paperFT_tilde, hc1, hc2, map_add]
  ring

theorem shiftFunctional_add (κ : ℝ) (lam : ℕ → ℝ) {k₁ k₂ : ℝ → ℂ} (h₁ : Admissible k₁)
    (h₂ : Admissible k₂) :
    shiftFunctional κ lam (k₁ + k₂) = shiftFunctional κ lam k₁ + shiftFunctional κ lam k₂ := by
  unfold shiftFunctional
  rw [weilFullFunctional_add lam h₁ h₂, polePart_add_of_admissible h₁ h₂]
  ring

theorem shiftFunctional_smul (κ : ℝ) (lam : ℕ → ℝ) (a : ℂ) (k : ℝ → ℂ) :
    shiftFunctional κ lam (a • k) = a * shiftFunctional κ lam k := by
  unfold shiftFunctional
  rw [weilFullFunctional_smul, polePart_smul_left]
  ring

theorem shiftFunctional_sum (κ : ℝ) (lam : ℕ → ℝ) {ι : Type*} (s : Finset ι) {k : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, Admissible (k i)) :
    shiftFunctional κ lam (∑ i ∈ s, k i) = ∑ i ∈ s, shiftFunctional κ lam (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := shiftFunctional_smul κ lam 0 0
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      shiftFunctional_add κ lam (h a (Finset.mem_insert_self a s))
        (Admissible.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem shiftFunctional_tilde (κ : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    shiftFunctional κ lam (EF.tilde k) = conj (shiftFunctional κ lam k) := by
  unfold shiftFunctional
  rw [weilFullFunctional_tilde, polePart_tilde, map_add, map_mul, Complex.conj_ofReal]

theorem im_shiftFunctional_weilTest_self (κ : ℝ) (lam : ℕ → ℝ) (g : ℝ → ℂ) :
    (shiftFunctional κ lam (EF.weilTest g g)).im = 0 := by
  have h := shiftFunctional_tilde κ lam (EF.weilTest g g)
  rw [tilde_weilTest_self] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-! ## Bochner measures -/

/-- The shifted spectral kernel `y ↦ W_κ(τ_y(f ⋆ f̃))`. -/
def shiftKernel (κ : ℝ) (lam : ℕ → ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  shiftFunctional κ lam (transl y (EF.weilTest f f))

theorem positiveDefinite_shiftKernel {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal (shiftKernel κ lam f) := by
  intro N t c
  set g : ℝ → ℂ := ∑ j, c j • transl (t j) f with hg
  have hgc : ContDiff ℝ 2 g := by
    have : g = fun x => ∑ j, c j * f (x - t j) := by
      funext x
      simp [hg, Finset.sum_apply, transl]
    rw [this]
    exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))
  have hgs : HasCompactSupport g :=
    HasCompactSupport.finset_sum fun j _ =>
      (hfc.comp_homeomorph (Homeomorph.subRight (t j))).smul_left
  have hadm := admissible_weilTest hf hfc
  have hkey : ∑ i, ∑ j, star (c i) * shiftKernel κ lam f (t j - t i) * c j =
      shiftFunctional κ lam (EF.weilTest g g) := by
    rw [hg, weilTest_sum_transl hf.continuous hfc,
      shiftFunctional_sum κ lam _ fun i _ => Admissible.sum _ fun j _ => (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [shiftFunctional_sum κ lam _ fun j _ => (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [shiftFunctional_smul, shiftKernel]
    ring
  refine ⟨(shiftFunctional κ lam (EF.weilTest g g)).re, hW g hgc hgs, ?_⟩
  rw [hkey]
  exact Complex.ext rfl (by simpa using im_shiftFunctional_weilTest_self κ lam g)

theorem continuous_shiftKernel (κ : ℝ) (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : Admissible k) :
    Continuous fun y => shiftFunctional κ lam (transl y k) :=
  (continuous_spectralKernel lam hk).add (continuous_const.mul (continuous_polePart_transl k))

/-- **Bochner measures of the shifted functional.** -/
theorem exists_shiftMeasure {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y, charFun ν y = shiftKernel κ lam f y :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefinite_shiftKernel hW hf hfc)
    (continuous_shiftKernel κ lam (admissible_weilTest hf hfc))

/-! ## Consistency -/

/-- **The shifted functional commutes with averages.** -/
theorem shiftFunctional_average (κ : ℝ) (lam : ℕ → ℝ) {φ k : ℝ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hk : Admissible k) (y : ℝ) :
    shiftFunctional κ lam (average φ k y) =
      ∫ u, φ u * shiftFunctional κ lam (transl (y + u) k) := by
  have hcomp : Continuous fun u : ℝ => y + u := continuous_const.add continuous_id
  have i1 : Integrable fun u => φ u * weilFullFunctional lam (transl (y + u) k) :=
    integrable_mul_of_continuous hφ hφc ((continuous_spectralKernel lam hk).comp hcomp)
  have i2 : Integrable fun u => φ u * polePart (transl (y + u) k) :=
    integrable_mul_of_continuous hφ hφc ((continuous_polePart_transl k).comp hcomp)
  unfold shiftFunctional
  rw [weilFullFunctional_average lam hφ hφc hk, polePart_average hφ hφc hk.cont hk.supp,
    ← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  ring

/-- The characteristic function of `|ĝ|² ν_f` is the shifted functional of an average. -/
theorem charFun_withDensity_eq_shift {κ : ℝ} {lam : ℕ → ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = shiftKernel κ lam f y) (y : ℝ) :
    charFun (ν.withDensity fun r => (specDensity g r : ℝ≥0∞)) y =
      shiftFunctional κ lam (average (EF.weilTest g g) (EF.weilTest f f) y) := by
  have hwg := admissible_weilTest hg hgc
  have hwf := admissible_weilTest hf hfc
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  rw [shiftFunctional_average κ lam hwg.cont hwg.supp hwf, charFun_apply_real,
    integral_withDensity_eq_integral_smul (measurable_specDensity hgint)]
  have hpt : ∀ r : ℝ, (specDensity g r) • cexp ((y : ℂ) * r * I) =
      ∫ u, EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I) := by
    intro r
    rw [NNReal.smul_def, Complex.real_smul,
      specDensity_eq_paperFT_weilTest hg.continuous hgc r, paperFT, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have hint : Integrable (Function.uncurry fun (r u : ℝ) =>
      EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I)) (ν.prod volume) := by
    have hprod := (integrable_const (μ := ν) (1 : ℝ)).mul_prod hwg.integrable.norm
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hcont : Continuous (Function.uncurry fun (r u : ℝ) =>
          EF.weilTest g g u * cexp (((y + u : ℝ) : ℂ) * r * I)) := by
        change Continuous fun p : ℝ × ℝ =>
          EF.weilTest g g p.2 * cexp (((y + p.2 : ℝ) : ℂ) * p.1 * I)
        exact (hwg.cont.comp continuous_snd).mul (by fun_prop)
      exact hcont.aestronglyMeasurable
    · obtain ⟨r, u⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul, one_mul]
      rw [show ((y + u : ℝ) : ℂ) * (r : ℂ) * I = (((y + u) * r : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [integral_const_mul, ← charFun_apply_real, hν, shiftKernel]

/-- **Consistency of the shifted Bochner measures.** `|ĝ|² ν_f = |f̂|² ν_g`. -/
theorem spectralMeasure_consistency_shift {κ : ℝ} {lam : ℕ → ℝ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) {νf νg : Measure ℝ} [IsFiniteMeasure νf] [IsFiniteMeasure νg]
    (hνf : ∀ y, charFun νf y = shiftKernel κ lam f y)
    (hνg : ∀ y, charFun νg y = shiftKernel κ lam g y) :
    (νf.withDensity fun r => (specDensity g r : ℝ≥0∞)) =
      νg.withDensity fun r => (specDensity f r : ℝ≥0∞) := by
  haveI := isFiniteMeasure_withDensity_specDensity (ν := νf) g
  haveI := isFiniteMeasure_withDensity_specDensity (ν := νg) f
  refine Measure.ext_of_charFun (funext fun y => ?_)
  rw [charFun_withDensity_eq_shift hf hfc hg hgc hνf y,
    charFun_withDensity_eq_shift hg hgc hf hfc hνg y]
  congr 1
  funext x
  exact average_comm f g y x

/-! ## The boundary measure -/

theorem exists_mollifierShiftMeasure {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    (j : ℕ) : ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ y, charFun ν y = shiftKernel κ lam (WeilHerglotz.mollC j) y :=
  exists_shiftMeasure hW (contDiff_mollC j) (WeilHerglotz.hasCompactSupport_mollC j)

/-- The shifted Bochner measure of the `j`-th mollifier. -/
def mollifierShiftMeasure {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) (j : ℕ) :
    Measure ℝ :=
  Classical.choose (exists_mollifierShiftMeasure hW j)

theorem isFiniteMeasure_mollifierShiftMeasure {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) (j : ℕ) : IsFiniteMeasure (mollifierShiftMeasure hW j) :=
  (Classical.choose_spec (exists_mollifierShiftMeasure hW j)).1

theorem charFun_mollifierShiftMeasure {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    (j : ℕ) (y : ℝ) :
    charFun (mollifierShiftMeasure hW j) y = shiftKernel κ lam (WeilHerglotz.mollC j) y :=
  (Classical.choose_spec (exists_mollifierShiftMeasure hW j)).2 y

/-- **The shifted boundary measure** `μ_κ = Σ_j |ρ̂_j|⁻² ν_{ρ_j}|_{S_j}`. -/
def shiftBoundaryMeasure {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) : Measure ℝ :=
  Measure.sum fun j : ℕ => ((mollifierShiftMeasure hW j).restrict (shell j)).withDensity
    fun r => (invDensity j r : ℝ≥0∞)

/-- **The shifted Bochner measure of every test is `|f̂|² μ_κ`.** -/
theorem eq_withDensity_shiftBoundaryMeasure {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = shiftKernel κ lam f y) :
    ν = (shiftBoundaryMeasure hW).withDensity fun r => (specDensity f r : ℝ≥0∞) := by
  have hfint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  rw [shiftBoundaryMeasure, withDensity_sum]
  conv_lhs => rw [← Measure.restrict_univ (μ := ν), ← iUnion_shell,
    Measure.restrict_iUnion shell_pairwise_disjoint measurableSet_shell]
  congr 1
  funext j
  haveI := isFiniteMeasure_mollifierShiftMeasure hW j
  have hcons := spectralMeasure_consistency_shift hf hfc (contDiff_mollC j)
    (WeilHerglotz.hasCompactSupport_mollC j) hν (charFun_mollifierShiftMeasure hW j)
  have hres := congrArg (fun m : Measure ℝ => m.restrict (shell j)) hcons
  simp only [restrict_withDensity (measurableSet_shell j)] at hres
  have hmf := measurable_specDensity hfint
  have hmχ := measurable_specDensity (WeilHerglotz.integrable_mollC j)
  have hmi := measurable_invDensity j
  have hone : (fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) *
      (fun r => (invDensity j r : ℝ≥0∞)) =ᵐ[ν.restrict (shell j)] 1 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_shell j)]
    refine Eventually.of_forall fun r hr => ?_
    have hpos := specDensity_mollC_pos j hr
    simp only [Pi.mul_apply, Pi.one_apply, invDensity]
    rw [← ENNReal.coe_mul, mul_inv_cancel₀ hpos.ne', ENNReal.coe_one]
  calc ν.restrict (shell j)
      = (ν.restrict (shell j)).withDensity 1 := withDensity_one.symm
    _ = (ν.restrict (shell j)).withDensity
          ((fun r => (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)) *
            (fun r => (invDensity j r : ℝ≥0∞))) := (withDensity_congr_ae hone).symm
    _ = ((ν.restrict (shell j)).withDensity fun r =>
          (specDensity (WeilHerglotz.mollC j) r : ℝ≥0∞)).withDensity
            fun r => (invDensity j r : ℝ≥0∞) :=
        withDensity_mul _ (hmχ.coe_nnreal_ennreal) (hmi.coe_nnreal_ennreal)
    _ = (((mollifierShiftMeasure hW j).restrict (shell j)).withDensity fun r =>
          (specDensity f r : ℝ≥0∞)).withDensity fun r => (invDensity j r : ℝ≥0∞) := by
        rw [hres]
    _ = ((mollifierShiftMeasure hW j).restrict (shell j)).withDensity
          ((fun r => (specDensity f r : ℝ≥0∞)) * fun r => (invDensity j r : ℝ≥0∞)) :=
        (withDensity_mul _ (hmf.coe_nnreal_ennreal) (hmi.coe_nnreal_ennreal)).symm
    _ = ((mollifierShiftMeasure hW j).restrict (shell j)).withDensity
          ((fun r => (invDensity j r : ℝ≥0∞)) * fun r => (specDensity f r : ℝ≥0∞)) := by
        rw [mul_comm]
    _ = (((mollifierShiftMeasure hW j).restrict (shell j)).withDensity fun r =>
          (invDensity j r : ℝ≥0∞)).withDensity fun r => (specDensity f r : ℝ≥0∞) :=
        withDensity_mul _ (hmi.coe_nnreal_ennreal) (hmf.coe_nnreal_ennreal)

/-- **Spectral representation of the shifted Weil form.**  `W_κ(f ⋆ f̃) = ∫ |f̂|² dμ_κ` for every
`C²` compactly supported `f`, and the integral is finite. -/
theorem shiftFunctional_weilTest_eq_lintegral {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫⁻ r, (specDensity f r : ℝ≥0∞) ∂shiftBoundaryMeasure hW) < ⊤ ∧
      shiftFunctional κ lam (EF.weilTest f f) =
        (((∫⁻ r, (specDensity f r : ℝ≥0∞) ∂shiftBoundaryMeasure hW).toReal : ℝ) : ℂ) := by
  obtain ⟨ν, hfin, hν⟩ := exists_shiftMeasure hW hf hfc
  have heq := eq_withDensity_shiftBoundaryMeasure hW hf hfc hν
  have huniv : ν Set.univ = ∫⁻ r, (specDensity f r : ℝ≥0∞) ∂shiftBoundaryMeasure hW := by
    rw [heq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ⟨huniv ▸ measure_lt_top ν _, ?_⟩
  have h0 := hν 0
  rw [shiftKernel, transl_zero, charFun_zero] at h0
  rw [← h0, ← huniv]
  rfl

/-! ## The Poisson representation -/

/-- The shifted Weil function `Φ_lam(s) + κ(1/s + 1/(s−1))`. -/
def shiftWeilFunction (κ : ℝ) (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  weilFunction lam s + (κ : ℂ) * (1 / s + 1 / (s - 1))

theorem tendsto_prime_of_summable {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    Tendsto (fun j : ℕ => ∑' n : ℕ,
        primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, primeCoeff lam n *
        (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)))) := by
  have hw0 : 0 < w.re := by linarith
  have hsum := (hsl (1 / 2 + w.re) (by linarith)).mul_left
    (2 * (Real.exp (2 * w.re) * ∫ u, majorant w.re u))
  refine tendsto_tsum_of_dominated_convergence hsum (fun n => ?_)
    (Eventually.of_forall fun j n => norm_prime_le hw0 j n)
  exact ((tendsto_autoCorr hw0 _).add (tendsto_autoCorr hw0 _)).const_mul _

theorem summable_term_lamC_of_summable {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) : Summable fun n => LSeries.term (lamC lam) s n := by
  refine Summable.of_norm_bounded (hsl s.re hs) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · positivity
  · rw [lamC, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hn
    · rfl
    · simp only [abs_zero, zero_div]
      positivity

theorem prime_limit_eq_of_summable {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    ∑' n : ℕ, primeCoeff lam n * (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)) =
      (((LSeries (lamC lam) (w + 1 / 2)).re / w.re : ℝ) : ℂ) := by
  have hw0 : 0 < w.re := by linarith
  have hs : 1 < (w + 1 / 2).re := by norm_num; linarith
  simp_rw [prime_limit_term hw0 lam]
  rw [← Complex.ofReal_tsum, LSeries, Complex.re_tsum (summable_term_lamC_of_summable hsl hs),
    tsum_div_const]

/-- **The limit of the shifted test functionals.**  For `Re s > 1` and `w = s − ½`,
`Re W_κ(h_j ⋆ h̃_j) → Re Φ_κ(s) / Re w`. -/
theorem tendsto_re_autoCorr_shift {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {s : ℂ}
    (hs : 1 < s.re) :
    Tendsto (fun j : ℕ => (shiftFunctional κ lam (autoCorr (s - 1 / 2) j)).re) atTop
      (𝓝 ((shiftWeilFunction κ lam s).re / (s - 1 / 2).re)) := by
  set w : ℂ := s - 1 / 2 with hwdef
  have hw : 1 / 2 < w.re := by rw [hwdef]; norm_num; linarith
  have hw0 : 0 < w.re := by linarith
  have hsw : s = w + 1 / 2 := by rw [hwdef]; ring
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    summable_abs_div_rpow_of_weilPositiveShift hW hσ
  have hfun : ∀ j : ℕ, shiftFunctional κ lam (autoCorr w j) =
      (1 + (κ : ℂ)) * (paperFT (autoCorr w j) (I / 2) + paperFT (autoCorr w j) (-I / 2))
        - (∑' n : ℕ, primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)))
        + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ) := by
    intro j
    have h0 : weilFullFunctional lam (autoCorr w j) =
        (paperFT (autoCorr w j) (I / 2) + paperFT (autoCorr w j) (-I / 2))
        - (∑' n : ℕ, primeCoeff lam n * (autoCorr w j (Real.log n) + autoCorr w j (-Real.log n)))
        + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (autoCorr w j) r * (EF.gammaBracket r : ℂ) := rfl
    rw [shiftFunctional, h0, polePart]
    ring
  have hlim := (((tendsto_pole hw).const_mul (1 + (κ : ℂ))).sub
    (tendsto_prime_of_summable hsl hw)).add ((tendsto_arch hw0).const_mul (1 / (2 * π) : ℂ))
  simp_rw [← hfun] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hL : ((1 + (κ : ℂ)) * (1 / (w + 1 / 2) * conj (1 / (w - 1 / 2)) +
      1 / (w - 1 / 2) * conj (1 / (w + 1 / 2))) -
      ∑' n : ℕ, primeCoeff lam n * (oneSidedCorr w (Real.log n) + oneSidedCorr w (-Real.log n)) +
      (1 / (2 * π) : ℂ) * ∫ r : ℝ, 1 / (w - I * r) * conj (1 / (w - I * r)) *
        (EF.gammaBracket r : ℂ)).re = (shiftWeilFunction κ lam s).re / w.re := by
    rw [prime_limit_eq_of_summable hsl hw, arch_limit_eq hw0, Complex.add_re, Complex.sub_re,
      show (1 + (κ : ℂ)) = ((1 + κ : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      pole_limit_re hw, Complex.ofReal_re, Complex.ofReal_re]
    have hdig : (Complex.digamma (((1 / 4 + w.re / 2 : ℝ) : ℂ) + ((w.im / 2 : ℝ) : ℂ) * I)) =
        Complex.digamma (s / 2) := by
      congr 1
      rw [hsw]
      apply Complex.ext <;> simp; ring
    rw [hdig]
    have h1 : w + 1 / 2 = s := hsw.symm
    have h2 : w - 1 / 2 = s - 1 := by rw [hsw]; ring
    rw [h1, h2, shiftWeilFunction, weilFunction]
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re,
      Complex.re_ofReal_mul]
    field_simp
    ring
  rw [← hL]
  exact hre

/-- **Herglotz positivity on `Re s > 1`.** -/
theorem re_shiftWeilFunction_nonneg {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {s : ℂ}
    (hs : 1 < s.re) : 0 ≤ (shiftWeilFunction κ lam s).re := by
  have hw0 : 0 < (s - 1 / 2).re := by norm_num; linarith
  have h := ge_of_tendsto (tendsto_re_autoCorr_shift hW hs) (Eventually.of_forall fun j =>
    hW (testFn (s - 1 / 2) j) (contDiff_testFn _ j) (hasCompactSupport_testFn _ j))
  have := mul_nonneg h hw0.le
  rwa [div_mul_cancel₀ _ hw0.ne'] at this

/-- **The shifted Poisson representation.**  For `Re s > 1` and `w = s − ½`,
`∫ |w − ir|⁻² dμ_κ = Re Φ_κ(s) / Re w`. -/
theorem lintegral_poissonDensity_eq_shift {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    {s : ℂ} (hs : 1 < s.re) :
    (∫⁻ r, poissonDensity (s - 1 / 2) r ∂shiftBoundaryMeasure hW) =
      ENNReal.ofReal ((shiftWeilFunction κ lam s).re / (s - 1 / 2).re) := by
  set w : ℂ := s - 1 / 2 with hwdef
  have hw0 : 0 < w.re := by rw [hwdef]; norm_num; linarith
  set μ := shiftBoundaryMeasure hW with hμ
  set F : ℕ → ℝ → ℝ≥0∞ := fun j r => (specDensity (testFn w j) r : ℝ≥0∞) with hF
  have hFmeas : ∀ j, Measurable (F j) := fun j =>
    (measurable_specDensity ((continuous_testFn w j).integrable_of_hasCompactSupport
      (hasCompactSupport_testFn w j))).coe_nnreal_ennreal
  have hrep : ∀ j, (∫⁻ r, F j r ∂μ) < ⊤ ∧
      shiftFunctional κ lam (autoCorr w j) = (((∫⁻ r, F j r ∂μ).toReal : ℝ) : ℂ) := fun j =>
    shiftFunctional_weilTest_eq_lintegral hW (contDiff_testFn w j) (hasCompactSupport_testFn w j)
  have hlimR := tendsto_re_autoCorr_shift hW hs
  rw [← hwdef] at hlimR
  have hlimE : Tendsto (fun j => ∫⁻ r, F j r ∂μ) atTop
      (𝓝 (ENNReal.ofReal ((shiftWeilFunction κ lam s).re / w.re))) := by
    have := ENNReal.tendsto_ofReal hlimR
    refine this.congr fun j => ?_
    rw [(hrep j).2, Complex.ofReal_re, ENNReal.ofReal_toReal (hrep j).1.ne]
  have hfatou : (∫⁻ r, poissonDensity w r ∂μ) ≤
      ENNReal.ofReal ((shiftWeilFunction κ lam s).re / w.re) := by
    have hl := lintegral_liminf_le (μ := μ) (u := atTop) hFmeas
    have hpt : ∀ r, liminf (fun j => F j r) atTop = poissonDensity w r := fun r =>
      (tendsto_specDensity_testFn hw0 r).liminf_eq
    simp_rw [hpt] at hl
    rwa [hlimE.liminf_eq] at hl
  have hfin : (∫⁻ r, 4 * poissonDensity w r ∂μ) ≠ ⊤ := by
    rw [lintegral_const_mul _ (measurable_poissonDensity w)]
    exact ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou)
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ) (F := F)
    (fun r => 4 * poissonDensity w r) hFmeas
    (fun j => Eventually.of_forall fun r => specDensity_testFn_le hw0 j r) hfin
    (Eventually.of_forall fun r => tendsto_specDensity_testFn hw0 r)
  exact tendsto_nhds_unique hdom hlimE

theorem integrable_inv_one_add_sq_shift {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) :
    Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) (shiftBoundaryMeasure hW) := by
  have hfin : (∫⁻ r, poissonDensity 1 r ∂shiftBoundaryMeasure hW) < ⊤ := by
    have h := lintegral_poissonDensity_eq_shift hW (s := 3 / 2) (by norm_num)
    rw [show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num] at h
    rw [h]
    exact ENNReal.ofReal_lt_top
  have h := integrable_toReal_of_lintegral_ne_top (measurable_poissonDensity 1).aemeasurable
    hfin.ne
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only [poissonDensity, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm]
  rw [norm_div, norm_one, div_pow, one_pow]
  have hn : ‖(1 : ℂ) - I * (r : ℂ)‖ ^ 2 = 1 + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [hn, one_div]

theorem integrable_herglotzKernel_shift {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    {z : ℂ} (hz : 0 < z.re) : Integrable (herglotzKernel z) (shiftBoundaryMeasure hW) := by
  refine ((integrable_inv_one_add_sq_shift hW).const_mul
    ((1 + (2 * ‖z‖ + 1) * ‖z‖) / z.re + 2 * (1 + ‖z‖))).mono'
    (measurable_herglotzKernel z).aestronglyMeasurable
    (Eventually.of_forall fun r => norm_herglotzKernel_le hz le_rfl le_rfl r)

/-! ## The Herglotz function and the continuation -/

/-- The Herglotz function `H(z) = ∫ (1/(z − ir) − ir/(1 + r²)) dμ_κ(r)`. -/
def shiftHerglotzFunction {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) (z : ℂ) : ℂ :=
  ∫ r, herglotzKernel z r ∂shiftBoundaryMeasure hW

theorem hasDerivAt_shiftHerglotzFunction {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (shiftHerglotzFunction hW)
      (∫ r, -(1 / (z₀ - I * r) ^ 2) ∂shiftBoundaryMeasure hW) z₀ := by
  set c : ℝ := z₀.re / 2 with hcdef
  set R : ℝ := ‖z₀‖ + z₀.re / 2 with hRdef
  have hc : 0 < c := by positivity
  have hball : ∀ x ∈ ball z₀ c, c ≤ x.re ∧ ‖x‖ ≤ R := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    constructor
    · have := Complex.abs_re_le_norm (x - z₀)
      rw [Complex.sub_re] at this
      have := neg_abs_le (x.re - z₀.re)
      linarith
    · have := norm_le_norm_add_norm_sub' x z₀
      have h2 : ‖x - z₀‖ = ‖z₀ - x‖ := norm_sub_rev _ _
      linarith
  set N : ℝ := (1 + (2 * R + 1) ^ 2) / c ^ 2 + 8 with hN
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := shiftBoundaryMeasure hW)
    (F := fun x r => herglotzKernel x r) (x₀ := z₀) (s := ball z₀ c)
    (F' := fun x r => -(1 / (x - I * r) ^ 2)) (bound := fun r => N * (1 + r ^ 2)⁻¹)
    (ball_mem_nhds z₀ hc)
    (Eventually.of_forall fun x => (measurable_herglotzKernel x).aestronglyMeasurable)
    (integrable_herglotzKernel_shift hW hz₀)
    (by fun_prop : Measurable fun r : ℝ => -(1 / (z₀ - I * (r : ℂ)) ^ 2)).aestronglyMeasurable
    (Eventually.of_forall fun r x hx => by
      obtain ⟨hxc, hxR⟩ := hball x hx
      rw [norm_neg, norm_div, norm_one, norm_pow]
      have := inv_norm_sq_le hc hxc hxR r
      rw [div_eq_mul_inv] at this
      exact this)
    ((integrable_inv_one_add_sq_shift hW).const_mul N)
    (Eventually.of_forall fun r x hx =>
      hasDerivAt_herglotzKernel (lt_of_lt_of_le hc (hball x hx).1) r)
  exact key.2

theorem re_shiftHerglotzFunction {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {z : ℂ}
    (hz : 0 < z.re) :
    (shiftHerglotzFunction hW z).re =
      z.re * (∫⁻ r, poissonDensity z r ∂shiftBoundaryMeasure hW).toReal := by
  unfold shiftHerglotzFunction
  rw [← RCLike.re_eq_complex_re, ← integral_re (integrable_herglotzKernel_shift hW hz)]
  simp only [RCLike.re_eq_complex_re]
  simp_rw [re_herglotzKernel hz]
  rw [integral_const_mul]
  congr 1
  rw [← integral_toReal (measurable_poissonDensity z).aemeasurable
    (Eventually.of_forall fun r => ENNReal.coe_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp [poissonDensity]

/-- On `Re s > 1` the real parts of `Φ_κ(s)` and `H(s − ½)` agree. -/
theorem re_shiftHerglotzFunction_eq {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {s : ℂ}
    (hs : 1 < s.re) :
    (shiftHerglotzFunction hW (s - 1 / 2)).re = (shiftWeilFunction κ lam s).re := by
  have hw0 : 0 < (s - 1 / 2).re := by norm_num; linarith
  rw [re_shiftHerglotzFunction hW hw0, lintegral_poissonDensity_eq_shift hW hs,
    ENNReal.toReal_ofReal (div_nonneg (re_shiftWeilFunction_nonneg hW hs) hw0.le)]
  rw [mul_div_assoc']
  exact mul_div_cancel_left₀ _ hw0.ne'

theorem differentiableAt_shiftWeilFunction {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam)
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (shiftWeilFunction κ lam) s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hdig : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) s := by
    have h2 : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      linarith
    exact (differentiableAt_digamma_of_re_pos h2).comp s ((differentiableAt_id).div_const 2)
  have habs : LSeries.abscissaOfAbsConv (lamC lam) < s.re := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (x := 1) fun y hy => ?_) (by exact_mod_cast hs)
    exact summable_term_lamC_of_summable
      (fun σ hσ => summable_abs_div_rpow_of_weilPositiveShift hW hσ) (by simpa using hy)
  have hL := (LSeries_hasDerivAt habs).differentiableAt
  have hpole : DifferentiableAt ℂ (fun s : ℂ => 1 / s + 1 / (s - 1)) s :=
    ((differentiableAt_const _).div differentiableAt_id hs0).add
      ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1)
  have hW' : DifferentiableAt ℂ (weilFunction lam) s := by
    unfold weilFunction
    exact ((((hdig.div_const 2).sub (differentiableAt_const _)).add
      ((differentiableAt_const _).div differentiableAt_id hs0)).add
      ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1)).sub hL
  unfold shiftWeilFunction
  exact hW'.add ((differentiableAt_const _).mul hpole)

/-- The continuation `s ↦ H(s − ½) + (Φ_κ(2) − H(3/2))`. -/
def shiftWeilContinuation {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) (s : ℂ) : ℂ :=
  shiftHerglotzFunction hW (s - 1 / 2) +
    (shiftWeilFunction κ lam 2 - shiftHerglotzFunction hW (2 - 1 / 2))

theorem shiftWeilContinuation_eq {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {s : ℂ}
    (hs : 1 < s.re) : shiftWeilContinuation hW s = shiftWeilFunction κ lam s := by
  set U : Set ℂ := {z | 1 < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ U := convex_halfSpace_re_gt 1
  set g : ℂ → ℂ := fun z => shiftWeilFunction κ lam z - shiftHerglotzFunction hW (z - 1 / 2)
    with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hz' : 1 < z.re := hz
    have hh : DifferentiableAt ℂ (fun z => shiftHerglotzFunction hW (z - 1 / 2)) z := by
      have hpos : 0 < (z - 1 / 2).re := by norm_num; linarith
      have hH : DifferentiableAt ℂ (shiftHerglotzFunction hW) (z - 1 / 2) :=
        (hasDerivAt_shiftHerglotzFunction hW hpos).differentiableAt
      exact DifferentiableAt.comp (g := shiftHerglotzFunction hW) (f := fun z : ℂ => z - 1 / 2)
        z hH (by fun_prop)
    exact ((differentiableAt_shiftWeilFunction hW hz').sub hh).differentiableWithinAt
  have hgre : ∀ z ∈ U, (g z).re = 0 := by
    intro z hz
    simp only [hg, Complex.sub_re]
    rw [re_shiftHerglotzFunction_eq hW hz]
    ring
  have h2 : (2 : ℂ) ∈ U := by
    show 1 < (2 : ℂ).re
    norm_num
  have hconst := eq_of_re_eq_zero hU hUc hgd hgre hs h2
  simp only [hg] at hconst
  unfold shiftWeilContinuation
  linear_combination -hconst

theorem re_shiftWeilContinuation_nonneg {κ : ℝ} {lam : ℕ → ℝ} (hW : WeilPositiveShift κ lam) {s : ℂ}
    (hs : 1 / 2 < s.re) : 0 ≤ (shiftWeilContinuation hW s).re := by
  have h2 : (shiftWeilFunction κ lam 2 - shiftHerglotzFunction hW (2 - 1 / 2)).re = 0 := by
    rw [Complex.sub_re, re_shiftHerglotzFunction_eq hW (by norm_num)]
    ring
  unfold shiftWeilContinuation
  rw [Complex.add_re, h2, add_zero, re_shiftHerglotzFunction hW (by norm_num; linarith)]
  exact mul_nonneg (by norm_num; linarith) ENNReal.toReal_nonneg

theorem differentiableOn_shiftWeilContinuation {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) :
    DifferentiableOn ℂ (shiftWeilContinuation hW) {s | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  have hpos : 0 < (s - 1 / 2).re := by norm_num; linarith
  have hH : DifferentiableAt ℂ (shiftHerglotzFunction hW) (s - 1 / 2) :=
    (hasDerivAt_shiftHerglotzFunction hW hpos).differentiableAt
  exact ((DifferentiableAt.comp (g := shiftHerglotzFunction hW) (f := fun z : ℂ => z - 1 / 2) s
    hH (by fun_prop)).add_const _).differentiableWithinAt

/-- **`κ`-Weil positivity is Herglotz positivity of the shifted Weil function.**  If the Weil
functional with the pole counted `1 + κ` times is nonnegative on every autocorrelation, then the
weights converge absolutely on `Re s > 1` and `Φ_κ` continues holomorphically to `Re s > ½` with
nonnegative real part. -/
theorem exists_herglotz_of_weilPositiveShift {κ : ℝ} {lam : ℕ → ℝ}
    (hW : WeilPositiveShift κ lam) :
    (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) ∧
      ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
          ∀ s : ℂ, 1 < s.re → Φ s = shiftWeilFunction κ lam s :=
  ⟨fun _ hσ => summable_abs_div_rpow_of_weilPositiveShift hW hσ, shiftWeilContinuation hW,
    differentiableOn_shiftWeilContinuation hW, fun _ hs => re_shiftWeilContinuation_nonneg hW hs,
    fun _ hs => shiftWeilContinuation_eq hW hs⟩

end RHTower.WeilSpectral

end
