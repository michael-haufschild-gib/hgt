import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventSpectrum
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# The Dirichlet form of `T_a`, ergodicity, and small eigenvalues from test vectors

Fix `a > 1`, `c = a(a − 1)`, and the kernel `K_a(y, z) = Σ_γ k_a(u(y, γz))` of `T_a` on `L²(F)`.

* Rows have mass `∫_F K_a(y, z) dz = ∫_ℍ k_a(u(y, z)) dz = 1/c`, so `T_a 1 = 1/c` (`resOp_oneL`).
* **Dirichlet form**: `∬ K_a(y, z)|f(y) − f(z)|² = 2‖f‖²/c − 2 Re⟨f, T_a f⟩` (`integral_energy`).
* **Ergodicity**: `k_a > 0`, so an eigenvector with eigenvalue `1/c` has vanishing energy and is
  constant (`exists_eq_smul_oneL`).
* **Small eigenvalues**: if `f ⊥ 1`, `f ≠ 0` and `Re⟨f, T_a f⟩ > ‖f‖²/(c + ¼)`, then the constrained
  norm of `T_a` on `1^⊥` is an eigenvalue `μ > 1/(c + ¼)`, so `λ = 1/μ − c < ¼`, and `λ ≠ 0` by
  ergodicity (`exists_spectralParam_mem_Ioo`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- `k_s(u) > 0` for `u ≥ 0`: the Abel integrand is positive on `(u, ∞)`. -/
theorem resKernel_pos (s : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 < resKernel s u := by
  unfold resKernel
  have hm : Measurable fun w : ℝ => (Ioi u).indicator
      (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - u))⁻¹)) w :=
    ((measurable_greenDensity s).mul
      (Real.continuous_sqrt.measurable.comp (measurable_id.sub_const u)).inv).ennreal_ofReal.indicator
      measurableSet_Ioi
  have hsub : Ioi u ⊆ Function.support fun w : ℝ => (Ioi u).indicator
      (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - u))⁻¹)) w := by
    intro w hw
    rw [Function.mem_support, indicator_of_mem hw]
    have hw0 : 0 < w := hu.trans_lt hw
    have hg : 0 < greenDensity s w :=
      div_pos (Real.rpow_pos_of_pos (rho_pos hw0.le) _)
        (Real.sqrt_pos.mpr (mul_pos hw0 (by linarith)))
    exact (ENNReal.ofReal_pos.mpr
      (mul_pos hg (inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hw))))).ne'
  have hpos : 0 < ∫⁻ w : ℝ, (Ioi u).indicator
      (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - u))⁻¹)) w := by
    rw [lintegral_pos_iff_support hm]
    calc (0 : ℝ≥0∞) < volume (Ioi u) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hpos.ne'

namespace CompactQuotient

variable (X : CompactQuotient)

/-- The kernel of `T_a` as a real function. -/
def kerA (a : ℝ) (y z : ℍ) : ℝ := (autK X.Γ (resKernel a) y z).toReal

theorem measurable_kerA (a : ℝ) : Measurable (Function.uncurry (X.kerA a)) :=
  (measurable_autK (Γ := X.Γ) (measurable_resKernel a)).ennreal_toReal

theorem kerA_nonneg (a : ℝ) (y z : ℍ) : 0 ≤ X.kerA a y z := ENNReal.toReal_nonneg

theorem kerA_comm (a : ℝ) (y z : ℍ) : X.kerA a y z = X.kerA a z y := by
  rw [kerA, kerA, autK_comm]

theorem autK_resKernel_pos (a : ℝ) (y z : ℍ) : 0 < autK X.Γ (resKernel a) y z := by
  rw [autK]
  calc (0 : ℝ≥0∞) < resKernel a (pairU y (((1 : X.Γ) : SL(2, ℝ)) • z)) :=
        resKernel_pos a (pairU_nonneg _ _)
    _ ≤ _ := ENNReal.le_tsum (f := fun γ : X.Γ => resKernel a (pairU y ((γ : SL(2, ℝ)) • z))) 1

variable {a : ℝ} (ha : 1 < a)

/-- The Schur kernel of `T_a`. -/
abbrev resKer : SchurKernel X.μ :=
  X.profileKernel (measurable_resKernel a) (lintegral_resKernel_mass_lt_top ha)

theorem resOp_eq : X.resOp ha = (X.resKer ha).op := rfl

include ha

/-- **Row mass.**  `∫_F K_a(y, z) dz = 1/(a(a − 1))`. -/
theorem lintegral_autK_resKernel (y : ℍ) :
    ∫⁻ z in X.F, autK X.Γ (resKernel a) y z = ENNReal.ofReal (1 / (a * (a - 1))) := by
  rw [setLIntegral_autK X.isFundamentalDomain (measurable_resKernel a), lintegral_pairU_eq_I,
    lintegral_resKernel_mass ha]

theorem ae_autK_lt_top (y : ℍ) : ∀ᵐ z ∂X.μ, autK X.Γ (resKernel a) y z < ∞ :=
  ae_lt_top (measurable_autK (Γ := X.Γ) (measurable_resKernel a)).of_uncurry_left
    (by rw [X.lintegral_autK_resKernel ha]; exact ENNReal.ofReal_ne_top)

theorem lintegral_ofReal_kerA (y : ℍ) :
    ∫⁻ z, ENNReal.ofReal (X.kerA a y z) ∂X.μ = ENNReal.ofReal (1 / (a * (a - 1))) := by
  rw [← X.lintegral_autK_resKernel ha y]
  refine lintegral_congr_ae ?_
  filter_upwards [X.ae_autK_lt_top ha y] with z hz
  exact ENNReal.ofReal_toReal hz.ne

theorem integral_kerA (y : ℍ) : ∫ z, X.kerA a y z ∂X.μ = 1 / (a * (a - 1)) := by
  have hc : 0 ≤ 1 / (a * (a - 1)) := by
    have : 0 < a * (a - 1) := by nlinarith
    positivity
  simp only [kerA]
  rw [integral_toReal (measurable_autK (Γ := X.Γ) (measurable_resKernel a)).of_uncurry_left.aemeasurable
    (X.ae_autK_lt_top ha y), X.lintegral_autK_resKernel ha, ENNReal.toReal_ofReal hc]

theorem lintegral_prod_kerA_mul {h : ℍ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2) * h p.1 ∂(X.μ.prod X.μ) =
      ENNReal.ofReal (1 / (a * (a - 1))) * ∫⁻ y, h y ∂X.μ := by
  have hrow : ∀ y, Measurable fun z => ENNReal.ofReal (X.kerA a y z) := fun y =>
    (X.measurable_kerA a).of_uncurry_left.ennreal_ofReal
  calc ∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2) * h p.1 ∂(X.μ.prod X.μ)
      = ∫⁻ y, ∫⁻ z, ENNReal.ofReal (X.kerA a y z) * h y ∂X.μ ∂X.μ :=
        lintegral_prod _ ((X.measurable_kerA a).ennreal_ofReal.mul
          (hh.comp measurable_fst)).aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (1 / (a * (a - 1))) * h y ∂X.μ :=
        lintegral_congr fun y => by rw [lintegral_mul_const _ (hrow y), X.lintegral_ofReal_kerA ha]
    _ = ENNReal.ofReal (1 / (a * (a - 1))) * ∫⁻ y, h y ∂X.μ := lintegral_const_mul _ hh

/-! ### The constant function -/

omit ha in
/-- The constant function `1` in `L²(F)`. -/
def oneL : Lp ℂ 2 X.μ := (memLp_const (1 : ℂ)).toLp fun _ => (1 : ℂ)

omit ha in
theorem coeFn_oneL : (X.oneL : ℍ → ℂ) =ᵐ[X.μ] fun _ => 1 := MemLp.coeFn_toLp _

/-- **`T_a 1 = 1/(a(a − 1))`.** -/
theorem resOp_oneL : X.resOp ha X.oneL = (((a * (a - 1))⁻¹ : ℝ) : ℂ) • X.oneL := by
  apply Lp.ext
  have h1 : (X.resOp ha X.oneL : ℍ → ℂ) =ᵐ[X.μ] (X.resKer ha).apply X.oneL :=
    (X.resKer ha).op_coeFn X.oneL
  filter_upwards [h1, Lp.coeFn_smul (((a * (a - 1))⁻¹ : ℝ) : ℂ) X.oneL, X.coeFn_oneL]
    with y hy hs ho
  rw [hy, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one, SchurKernel.apply]
  calc ∫ z, (X.resKer ha).toFun y z * (X.oneL : ℍ → ℂ) z ∂X.μ
      = ∫ z, ((X.kerA a y z : ℝ) : ℂ) ∂X.μ := by
        refine integral_congr_ae ?_
        filter_upwards [X.coeFn_oneL] with z hz
        rw [hz, mul_one]
        rfl
    _ = ((∫ z, X.kerA a y z ∂X.μ : ℝ) : ℂ) := integral_ofReal
    _ = (((a * (a - 1))⁻¹ : ℝ) : ℂ) := by rw [X.integral_kerA ha, one_div]

/-! ### The Dirichlet form -/

omit ha in
/-- `K‖u − v‖² = K‖u‖² + K‖v‖² − 2 Re(ū K v)`. -/
theorem energy_pointwise (K : ℝ) (u v : ℂ) :
    K * ‖u - v‖ ^ 2 = K * ‖u‖ ^ 2 + K * ‖v‖ ^ 2 - 2 * ((starRingEnd ℂ) u * (K : ℂ) * v).re := by
  have h : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h, h, h]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem integrable_kerA_mul_norm_sq (f : Lp ℂ 2 X.μ) :
    Integrable (fun p : ℍ × ℍ => X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1‖ ^ 2) (X.μ.prod X.μ) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  refine ⟨((X.measurable_kerA a).mul ((hf.comp measurable_fst).norm.pow_const 2)).aestronglyMeasurable,
    ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ p, ‖X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1‖ ^ 2‖ₑ ∂(X.μ.prod X.μ)
      = ∫⁻ p, ENNReal.ofReal (X.kerA a p.1 p.2) * ‖(f : ℍ → ℂ) p.1‖ₑ ^ 2 ∂(X.μ.prod X.μ) := by
        refine lintegral_congr fun p => ?_
        rw [enorm_mul, Real.enorm_of_nonneg (X.kerA_nonneg a _ _), enorm_pow, enorm_norm]
    _ = ENNReal.ofReal (1 / (a * (a - 1))) * ∫⁻ y, ‖(f : ℍ → ℂ) y‖ₑ ^ 2 ∂X.μ :=
        X.lintegral_prod_kerA_mul ha (hf.enorm.pow_const 2)
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        rw [← eLpNorm_two_sq]; exact (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)).lt_top)

theorem integrable_kerA_mul_norm_sq_snd (f : Lp ℂ 2 X.μ) :
    Integrable (fun p : ℍ × ℍ => X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.2‖ ^ 2) (X.μ.prod X.μ) := by
  refine (X.integrable_kerA_mul_norm_sq ha f).swap.congr (Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [X.kerA_comm]

theorem integrable_energy (f : Lp ℂ 2 X.μ) :
    Integrable (fun p : ℍ × ℍ => X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1 - f p.2‖ ^ 2)
      (X.μ.prod X.μ) := by
  have h3 : Integrable (fun p : ℍ × ℍ =>
      ((starRingEnd ℂ) ((f : ℍ → ℂ) p.1) * (X.kerA a p.1 p.2 : ℂ) * (f : ℍ → ℂ) p.2).re)
      (X.μ.prod X.μ) := ((X.resKer ha).integrable_triple f f).re
  refine (((X.integrable_kerA_mul_norm_sq ha f).add (X.integrable_kerA_mul_norm_sq_snd ha f)).sub
    (h3.const_mul 2)).congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [energy_pointwise]

/-- **The Dirichlet form of `T_a`.**
`∬ K_a(y, z)|f(y) − f(z)|² = 2‖f‖²/(a(a − 1)) − 2 Re⟨f, T_a f⟩`. -/
theorem integral_energy (f : Lp ℂ 2 X.μ) :
    ∫ p, X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1 - f p.2‖ ^ 2 ∂(X.μ.prod X.μ) =
      2 * ‖f‖ ^ 2 / (a * (a - 1)) - 2 * (⟪f, X.resOp ha f⟫_ℂ).re := by
  have h1 := X.integrable_kerA_mul_norm_sq ha f
  have h2 := X.integrable_kerA_mul_norm_sq_snd ha f
  have h3c := (X.resKer ha).integrable_triple f f
  have h3 : Integrable (fun p : ℍ × ℍ =>
      ((starRingEnd ℂ) ((f : ℍ → ℂ) p.1) * (X.kerA a p.1 p.2 : ℂ) * (f : ℍ → ℂ) p.2).re)
      (X.μ.prod X.μ) := h3c.re
  have e1 : ∫ p, X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1‖ ^ 2 ∂(X.μ.prod X.μ) =
      ‖f‖ ^ 2 / (a * (a - 1)) := by
    rw [integral_prod _ h1]
    simp only [integral_mul_const, X.integral_kerA ha]
    rw [integral_const_mul, ← _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    ring
  have e2 : ∫ p, X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.2‖ ^ 2 ∂(X.μ.prod X.μ) =
      ∫ p, X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1‖ ^ 2 ∂(X.μ.prod X.μ) := by
    calc ∫ p, X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.2‖ ^ 2 ∂(X.μ.prod X.μ)
        = ∫ p, (fun q : ℍ × ℍ => X.kerA a q.1 q.2 * ‖(f : ℍ → ℂ) q.1‖ ^ 2) p.swap
            ∂(X.μ.prod X.μ) := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          simp only [Prod.fst_swap, Prod.snd_swap]
          rw [X.kerA_comm]
      _ = _ := integral_prod_swap _
  have e3 : ∫ p, ((starRingEnd ℂ) ((f : ℍ → ℂ) p.1) * (X.kerA a p.1 p.2 : ℂ) *
      (f : ℍ → ℂ) p.2).re ∂(X.μ.prod X.μ) = (⟪f, X.resOp ha f⟫_ℂ).re := by
    calc _ = (∫ p, (starRingEnd ℂ) ((f : ℍ → ℂ) p.1) * (X.kerA a p.1 p.2 : ℂ) *
          (f : ℍ → ℂ) p.2 ∂(X.μ.prod X.μ)).re := integral_re h3c
      _ = (∫ y, ∫ z, (starRingEnd ℂ) ((f : ℍ → ℂ) y) * (X.kerA a y z : ℂ) *
          (f : ℍ → ℂ) z ∂X.μ ∂X.μ).re := congrArg Complex.re (integral_prod _ h3c)
      _ = (⟪f, X.resOp ha f⟫_ℂ).re := (congrArg Complex.re ((X.resKer ha).inner_op f f)).symm
  have hpt : (fun p : ℍ × ℍ => X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1 - f p.2‖ ^ 2) =
      fun p => (X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.1‖ ^ 2 + X.kerA a p.1 p.2 * ‖(f : ℍ → ℂ) p.2‖ ^ 2)
        - 2 * ((starRingEnd ℂ) ((f : ℍ → ℂ) p.1) * (X.kerA a p.1 p.2 : ℂ) * (f : ℍ → ℂ) p.2).re :=
    funext fun p => energy_pointwise _ _ _
  rw [hpt, integral_sub (h1.add h2) (h3.const_mul 2), integral_add h1 h2, integral_const_mul, e2,
    e1, e3]
  ring

/-! ### Ergodicity -/

/-- **Ergodicity.**  An eigenvector of `T_a` with the top eigenvalue `1/(a(a − 1))` is constant:
its energy `∬ K_a|x(y) − x(z)|²` vanishes and `K_a > 0`. -/
theorem exists_eq_smul_oneL {x : Lp ℂ 2 X.μ}
    (hx : X.resOp ha x = (((a * (a - 1))⁻¹ : ℝ) : ℂ) • x) : ∃ α : ℂ, x = α • X.oneL := by
  have hE : ∫ p, X.kerA a p.1 p.2 * ‖(x : ℍ → ℂ) p.1 - x p.2‖ ^ 2 ∂(X.μ.prod X.μ) = 0 := by
    rw [X.integral_energy ha, hx, inner_smul_right, inner_self_eq_norm_sq_to_K,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv]
    ring
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun p => mul_nonneg (X.kerA_nonneg a _ _) (sq_nonneg _)) (X.integrable_energy ha x)).mp hE
  have hfin : ∀ᵐ p ∂(X.μ.prod X.μ), autK X.Γ (resKernel a) p.1 p.2 < ∞ := by
    refine ae_lt_top (measurable_autK (Γ := X.Γ) (measurable_resKernel a)) ?_
    rw [lintegral_prod _ (measurable_autK (Γ := X.Γ) (measurable_resKernel a)).aemeasurable]
    simp only [Function.uncurry_apply_pair]
    simp only [X.lintegral_autK_resKernel ha, lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hpair : ∀ᵐ p ∂(X.μ.prod X.μ), (x : ℍ → ℂ) p.1 = x p.2 := by
    filter_upwards [hz, hfin] with p hp hp'
    simp only [Pi.zero_apply] at hp
    have hK : 0 < X.kerA a p.1 p.2 :=
      ENNReal.toReal_pos (X.autK_resKernel_pos a p.1 p.2).ne' hp'.ne
    have h0 : ‖(x : ℍ → ℂ) p.1 - x p.2‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hp with h | h
      · linarith
      · exact h
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h0))
  by_cases hμ : X.μ = 0
  · refine ⟨0, Lp.ext ?_⟩
    have hbot : ae X.μ = ⊥ := ae_eq_bot.mpr hμ
    show ∀ᶠ p in ae X.μ, _
    rw [hbot]
    exact Filter.eventually_bot
  · haveI : (ae X.μ).NeBot := ae_neBot.mpr hμ
    obtain ⟨y₀, hy₀⟩ := (Measure.ae_ae_of_ae_prod hpair).exists
    refine ⟨(x : ℍ → ℂ) y₀, Lp.ext ?_⟩
    filter_upwards [hy₀, Lp.coeFn_smul ((x : ℍ → ℂ) y₀) X.oneL, X.coeFn_oneL] with z hz hs ho
    rw [hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact hz.symm

/-! ### Small eigenvalues from a test vector -/

/-- **A small eigenvalue from a test vector.**  If `f ⊥ 1`, `f ≠ 0` and
`Re⟨f, T_a f⟩ > ‖f‖²/(a(a − 1) + ¼)`, then some spectral parameter lies in `(0, ¼)`. -/
theorem exists_spectralParam_mem_Ioo {f : Lp ℂ 2 X.μ} (hf0 : f ≠ 0)
    (hf1 : ⟪X.oneL, f⟫_ℂ = 0)
    (hR : ‖f‖ ^ 2 / (a * (a - 1) + 1 / 4) < (⟪f, X.resOp ha f⟫_ℂ).re) :
    ∃ j : X.SpecIndex ha, 0 < X.spectralParam ha j ∧ X.spectralParam ha j < 1 / 4 := by
  set S := X.resOp ha with hS
  set c := a * (a - 1) with hc
  have hc0 : 0 < c := by simp only [hc]; nlinarith
  have hq0 : 0 < c + 1 / 4 := by linarith
  set v : ℕ → Lp ℂ 2 X.μ := fun _ => X.oneL with hv
  have hvS : ∀ m < 1, ∃ r : ℝ, S (v m) = (r : ℂ) • v m := fun m _ => ⟨c⁻¹, X.resOp_oneL ha⟩
  have hfn : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  -- the normalized test vector
  set y : Lp ℂ 2 X.μ := ((‖f‖⁻¹ : ℝ) : ℂ) • f with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hfn,
      inv_mul_cancel₀ hfn.ne']
  have hy2 : ∀ m < 1, ⟪v m, y⟫_ℂ = 0 := fun m _ => by
    simp only [hv, hy, inner_smul_right, hf1, mul_zero]
  have hRy : ‖f‖ ^ 2 * (⟪y, S y⟫_ℂ).re = (⟪f, S f⟫_ℂ).re := by
    rw [hy, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul, ← mul_assoc, ← sq, inv_pow,
      mul_inv_cancel₀ (by positivity), one_mul]
  have hSy : (c + 1 / 4)⁻¹ < ‖S y‖ := by
    have h1 : (⟪y, S y⟫_ℂ).re ≤ ‖S y‖ := by
      calc (⟪y, S y⟫_ℂ).re ≤ ‖⟪y, S y⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖y‖ * ‖S y‖ := norm_inner_le_norm _ _
        _ = ‖S y‖ := by rw [hy1, one_mul]
    have h2 : (c + 1 / 4)⁻¹ < (⟪y, S y⟫_ℂ).re := by
      have hf2 : 0 < ‖f‖ ^ 2 := by positivity
      rw [← hRy, div_eq_mul_inv] at hR
      exact lt_of_mul_lt_mul_left hR hf2.le
    linarith
  have hsup : (c + 1 / 4)⁻¹ < ContinuousLinearMap.orthSup S v 1 :=
    hSy.trans_le (ContinuousLinearMap.le_orthSup S v 1 hy1.le hy2)
  have hne : ContinuousLinearMap.orthSup S v 1 ≠ 0 := (lt_trans (by positivity) hsup).ne'
  obtain ⟨x, hx1, hx2, μr, hμabs, hSx⟩ := ContinuousLinearMap.exists_signed_eigenvector_orthSup
    (X.isCompactOperator_resOp ha) (X.isSymmetric_resOp ha) v 1 hvS hne
  have hμ0 : (μr : ℂ) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero] at h
    rw [h, abs_zero] at hμabs
    exact hne hμabs.symm
  have hxmem : x ∈ nonzeroEigenspace S ⟨(μr : ℂ), hμ0⟩ := Module.End.mem_eigenspace_iff.mpr hSx
  have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  have hrank : 0 < Module.finrank ℂ (nonzeroEigenspace S ⟨(μr : ℂ), hμ0⟩) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hxmem⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  set j : X.SpecIndex ha := ⟨⟨(μr : ℂ), hμ0⟩, ⟨0, hrank⟩⟩ with hj
  have hμj : X.specMu ha j = μr := by simp [specMu, hj]
  have hμpos : 0 < μr := hμj ▸ X.specMu_pos ha j
  have hμbig : (c + 1 / 4)⁻¹ < μr := by rw [← abs_of_pos hμpos, hμabs]; exact hsup
  have hlam : X.spectralParam ha j = 1 / μr - c := by rw [spectralParam, hμj]
  refine ⟨j, ?_, ?_⟩
  · rcases (X.spectralParam_nonneg ha j).lt_or_eq with h | h
    · exact h
    · exfalso
      have hμc : μr = c⁻¹ := by
        rw [hlam] at h
        have : 1 / μr = c := by linarith
        rw [← this, one_div, inv_inv]
      obtain ⟨α, hα⟩ := X.exists_eq_smul_oneL ha (x := x) (by rw [← hμc]; exact hSx)
      have h0 := hx2 0 zero_lt_one
      simp only [hv] at h0
      rw [hα, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
      rcases mul_eq_zero.mp h0 with h' | h'
      · rw [h', zero_smul] at hα; exact hx0 hα
      · have : ‖X.oneL‖ = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
        rw [norm_eq_zero] at this
        rw [this, smul_zero] at hα
        exact hx0 hα
  · rw [hlam]
    have : 1 / μr < c + 1 / 4 := by
      rw [one_div]
      exact (inv_lt_comm₀ hμpos hq0).mp hμbig
    linarith

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
