import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import GaloisForLFunctions.HTGeometry.HolomorphicPoincareSeriesCuspForm
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Petersson integrand of a cusp form against a Poincaré series

For a cusp form `f` of weight `k` and the exponential seed `e_m(z) = exp(2πi m z)`, the Petersson
integrand `ψ = petersson k f e_m`, `ψ(z) = conj(f z) · e(mz) · y^k`, is `T`-periodic, and the
weight-`k` transformation law of `f` gives, for every coprime row `(c, d)` with matrix `M_{c,d}`,

  `ψ(M_{c,d} z) = conj(f z) · (cz + d)^{-k} e(m M_{c,d} z) · y^k`,

so that `petersson k f P_m = Σ_{(c,d)} ψ ∘ M_{c,d}` pointwise.  The bound
`‖f z‖ ≤ C y^{-k/2}` makes `‖ψ(z)‖ ≤ C e^{-2π m y} y^{k/2}`, which is integrable on the strip
`0 ≤ Re z < 1` as soon as `k > 2` and `m ≥ 1`.
-/

open UpperHalfPlane hiding I
open MeasureTheory Set ModularForm EisensteinSeries Complex Filter
open scoped MatrixGroups ModularForm ComplexConjugate Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The exponential seed -/

/-- The seed `e(mz) = exp(2πi m z)`. -/
def expSeed (m : ℕ) (z : ℍ) : ℂ := Complex.exp (2 * π * I * m * (z : ℂ))

theorem continuous_expSeed (m : ℕ) : Continuous (expSeed m) :=
  Complex.continuous_exp.comp (continuous_const.mul continuous_coe)

theorem expSeed_T_zpow_smul (m : ℕ) (n : ℤ) (z : ℍ) :
    expSeed m (ModularGroup.T ^ n • z) = expSeed m z := by
  unfold expSeed
  rw [ModularGroup.coe_T_zpow_smul_eq, mul_add, Complex.exp_add]
  have : Complex.exp (2 * π * I * m * n) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (m * n)]
    congr 1
    push_cast
    ring
  rw [this, mul_one]

theorem re_two_pi_I_mul_coe (m : ℕ) (w : ℍ) :
    (2 * π * I * m * (w : ℂ)).re = -(2 * π * m * w.im) := by
  have : (2 * π * I * m * (w : ℂ)) = ((2 * π * m : ℝ) : ℂ) * (I * (w : ℂ)) := by
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem norm_expSeed (m : ℕ) (z : ℍ) : ‖expSeed m z‖ = Real.exp (-(2 * π * m * z.im)) := by
  rw [expSeed, Complex.norm_exp, re_two_pi_I_mul_coe]

/-- The slash of the seed by `M_{c,d}` is the Poincaré summand. -/
theorem expSeed_slash_gammaSetMatrix (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) (z : ℍ) :
    (expSeed m ∣[k] gammaSetMatrix v) z = poincareSummand k m v z := by
  rw [SL_slash_apply, ModularGroup.denom_apply, gammaSetMatrix_apply_one_zero,
    gammaSetMatrix_apply_one_one, poincareSummand, eisSummand, mul_comm, expSeed]

/-! ## Cusp forms of level one are `T`-periodic -/

theorem cuspForm_T_zpow_smul {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℤ) (z : ℍ) :
    f (ModularGroup.T ^ n • z) = f z := by
  have hf : ⇑f ∣[k] (ModularGroup.T ^ n) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ ⟨ModularGroup.T ^ n, rfl⟩
  have := congrFun hf z
  rw [SL_slash_apply, ModularGroup.denom_apply] at this
  simpa [ModularGroup.coe_T_zpow] using this

/-! ## The Petersson integrand along `M_{c,d}` -/

/-- **Transport of the Petersson integrand.** For a cusp form `f` and the seed `e_m`,
`petersson k f e_m (M_{c,d} z) = conj(f z) · (poincareSummand) · y^k`. -/
theorem petersson_expSeed_gammaSetMatrix_smul {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k)
    (v : gammaSet 1 1 0) (z : ℍ) :
    petersson k f (expSeed m) (gammaSetMatrix v • z)
      = conj (f z) * poincareSummand k m v z * (z.im : ℂ) ^ k := by
  have hf : ⇑f ∣[k] gammaSetMatrix v = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ ⟨gammaSetMatrix v, rfl⟩
  rw [← petersson_slash_SL, hf, petersson, expSeed_slash_gammaSetMatrix]

/-- **The Petersson integrand of `P_m` is the sum of the transported seeds.** -/
theorem petersson_poincareSeries_eq_tsum {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    petersson k f (poincareSeries k m) z
      = ∑' v : gammaSet 1 1 0, petersson k f (expSeed m) (gammaSetMatrix v • z) := by
  simp_rw [petersson_expSeed_gammaSetMatrix_smul]
  rw [petersson, poincareSeries, ← tsum_mul_left, ← tsum_mul_right]

theorem petersson_expSeed_T_zpow_smul {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) (n : ℤ) (z : ℍ) :
    petersson k f (expSeed m) (ModularGroup.T ^ n • z) = petersson k f (expSeed m) z := by
  rw [petersson, petersson, expSeed_T_zpow_smul, ModularGroup.im_T_zpow_smul,
    cuspForm_T_zpow_smul]

theorem continuous_petersson_expSeed {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) :
    Continuous (petersson k f (expSeed m)) :=
  petersson_continuous k (CuspFormClass.holo f).continuous (continuous_expSeed m)

/-! ## Integrability on the strip from a bound -/

/-- `∫_0^∞ e^{-a y} y^{s} dy` converges for `a > 0`, `s > -1`. -/
theorem integrableOn_exp_neg_mul_mul_rpow_Ioi {a s : ℝ} (ha : 0 < a) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ => Real.exp (-(a * y)) * y ^ s) (Ioi 0) volume := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ s) (Ioi 0) volume := by
    have := Real.GammaIntegral_convergent (s := s + 1) (by linarith)
    simpa using this
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(a * x)) * (a * x) ^ s) (Ioi 0) volume := by
    have := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ s) 0 ha).mpr
      (by simpa using h1)
    simpa using this
  have h3 : IntegrableOn (fun x : ℝ => (a ^ s)⁻¹ * (Real.exp (-(a * x)) * (a * x) ^ s)) (Ioi 0)
      volume := h2.const_mul _
  refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx' : (0 : ℝ) < x := hx
  show (a ^ s)⁻¹ * (Real.exp (-(a * x)) * (a * x) ^ s) = Real.exp (-(a * x)) * x ^ s
  rw [Real.mul_rpow ha.le hx'.le]
  have : a ^ s ≠ 0 := (Real.rpow_pos_of_pos ha s).ne'
  field_simp

/-- Continuity of the chart integrand on `(0, ∞) × [0, 1)`. -/
theorem continuousOn_stripChartIntegrand {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn (stripChartIntegrand F) (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := by
  intro p hp
  have hy : (0 : ℝ) < p.1 := hp.1
  apply ContinuousAt.continuousWithinAt
  have hmk : Continuous fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ) := by
    have : (fun q : ℝ × ℝ => (⟨q.2, q.1⟩ : ℂ)) = fun q : ℝ × ℝ => (q.2 : ℂ) + (q.1 : ℂ) * I := by
      funext q
      apply Complex.ext <;> simp
    rw [this]
    fun_prop
  have hof : ContinuousAt (fun q : ℝ × ℝ => ofComplex (⟨q.2, q.1⟩ : ℂ)) p :=
    (contMDiffAt_ofComplex (n := 0) (by simpa using hy)).continuousAt.comp hmk.continuousAt
  have hinv : ContinuousAt (fun q : ℝ × ℝ => (q.1 ^ 2)⁻¹) p :=
    ((continuous_fst.pow 2).continuousAt).inv₀ (by show p.1 ^ 2 ≠ 0; positivity)
  exact hinv.smul (hF.continuousAt.comp hof)

/-- **Integrability on the strip** from the bound `‖F z‖ ≤ C e^{-a y} y^r`, `a > 0`, `r > 1`. -/
theorem integrableOn_modularStrip_of_bound {F : ℍ → ℂ} (hF : Continuous F) {C a r : ℝ}
    (ha : 0 < a) (hr : 1 < r)
    (hbound : ∀ z : ℍ, ‖F z‖ ≤ C * Real.exp (-(a * z.im)) * z.im ^ r) :
    IntegrableOn F modularStrip volume := by
  rw [integrableOn_modularStrip_iff, Measure.volume_eq_prod]
  have hR : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1) := measurableSet_Ioi.prod measurableSet_Ico
  have hg : Integrable (fun y : ℝ => C * (Real.exp (-(a * y)) * y ^ (r - 2)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_neg_mul_mul_rpow_Ioi ha (by linarith)).const_mul C
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    integrableOn_const (by simp)
  have hG : Integrable (fun p : ℝ × ℝ => C * (Real.exp (-(a * p.1)) * p.1 ^ (r - 2)) * 1)
      ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ico (0 : ℝ) 1)) := by
    rw [← Measure.prod_restrict]
    exact hg.mul_prod h1
  refine hG.mono ((continuousOn_stripChartIntegrand hF).aestronglyMeasurable hR) ?_
  refine ae_restrict_of_forall_mem hR fun p hp => ?_
  have hy : (0 : ℝ) < p.1 := hp.1
  have him : (ofComplex (⟨p.2, p.1⟩ : ℂ)).im = p.1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  rw [stripChartIntegrand, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
  refine le_trans ?_ (le_abs_self _)
  rw [abs_of_pos (by positivity)]
  calc (p.1 ^ 2)⁻¹ * ‖F (ofComplex ⟨p.2, p.1⟩)‖
      ≤ (p.1 ^ 2)⁻¹ * (C * Real.exp (-(a * p.1)) * p.1 ^ r) := by
        have := hbound (ofComplex ⟨p.2, p.1⟩)
        rw [him] at this
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = C * (Real.exp (-(a * p.1)) * p.1 ^ (r - 2)) := by
        rw [Real.rpow_sub hy, Real.rpow_two]
        field_simp

/-! ## The Petersson integrand is integrable on the strip -/

theorem norm_petersson_expSeed {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    ‖petersson k f (expSeed m) z‖ = ‖f z‖ * Real.exp (-(2 * π * m * z.im)) * z.im ^ k := by
  rw [petersson, norm_mul, norm_mul, Complex.norm_conj, norm_expSeed, norm_zpow,
    Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]

/-- The bound `‖ψ(z)‖ ≤ C e^{-2π m y} y^{k/2}`. -/
theorem exists_bound_petersson_expSeed {k : ℤ} (m : ℕ) (f : CuspForm 𝒮ℒ k) :
    ∃ C : ℝ, ∀ z : ℍ, ‖petersson k f (expSeed m) z‖
      ≤ C * Real.exp (-(2 * π * m * z.im)) * z.im ^ ((k : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun z => ?_⟩
  rw [norm_petersson_expSeed]
  have hy := z.im_pos
  have hzk : z.im ^ k = z.im ^ ((k : ℝ) / 2) * z.im ^ ((k : ℝ) / 2) := by
    rw [← Real.rpow_add hy, ← Real.rpow_intCast]
    congr 1
    ring
  calc ‖f z‖ * Real.exp (-(2 * π * m * z.im)) * z.im ^ k
      ≤ (C / z.im ^ ((k : ℝ) / 2)) * Real.exp (-(2 * π * m * z.im)) * z.im ^ k := by
        gcongr
        exact hC z
    _ = C * Real.exp (-(2 * π * m * z.im)) * z.im ^ ((k : ℝ) / 2) := by
        rw [hzk]
        have : z.im ^ ((k : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
        field_simp

/-- **Integrability of the Petersson integrand on the strip** for `k ≥ 3`, `m ≥ 1`. -/
theorem integrableOn_modularStrip_petersson_expSeed {k : ℤ} (hk : 3 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (f : CuspForm 𝒮ℒ k) : IntegrableOn (petersson k f (expSeed m)) modularStrip volume := by
  obtain ⟨C, hC⟩ := exists_bound_petersson_expSeed m f
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  exact integrableOn_modularStrip_of_bound (continuous_petersson_expSeed m f) (C := C)
    (a := 2 * π * m) (by positivity) (r := (k : ℝ) / 2) (by linarith) hC

end

end GaloisForLFunctions.HTGeometry
