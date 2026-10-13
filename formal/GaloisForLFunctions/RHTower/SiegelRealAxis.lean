import GaloisForLFunctions.RHTower.DirichletLLogStrip
import GaloisForLFunctions.RHTower.SiegelProductLFunction
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Dirichlet L-functions of quadratic characters on the real axis

Inputs for Siegel's theorem, for a nontrivial character `χ` modulo `N`:

* `norm_LFunction_one_le_log`: `|L(1, χ)| ≤ log N + 5` (truncate the Dirichlet series at `N`; the
  truncation error is `≤ 4N/(N + 1)`).
* For quadratic `χ` and real `σ > 0`, `L(σ, χ)` is real (`LFunction_ofReal_im`), being the limit
  of real partial sums; `ζ(σ)` is real (`riemannZeta_ofReal_im`).
* `LFunction_two_re_pos`: `L(2, χ) > 0`, since `ζ(2)L(2, χ) = ∑ (1 ⋆ χ)(n) n^{−2} ≥ 1`.
* `LFunction_re_pos_of_no_zero`: if `L(σ, χ) ≠ 0` for `β ≤ σ < 1`, then `L(σ, χ) > 0` on `[β, 2]`
  (intermediate values, and no zeros on `σ ≥ 1`).
* `exists_riemannZeta_neg`: `ζ(σ) < 0` for `σ` in a left neighbourhood of `1`.
-/

open DirichletCharacter Complex Filter Topology
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma quadratic_apply_im {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hq a with h | h | h <;> simp [h]

lemma norm_ofReal_cpow_neg {x : ℝ} (hx : 0 < x) (σ : ℝ) :
    ‖((x : ℂ)) ^ (-(σ : ℂ))‖ = x ^ (-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

/-- `|L(1, χ)| ≤ log N + 5` for a nontrivial character modulo `N`. -/
theorem norm_LFunction_one_le_log {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ‖LFunction χ 1‖ ≤ Real.log N + 5 := by
  have h := norm_LFunction_sub_character_partial_le hχ (s := 1) (by norm_num) N
  simp only [Complex.one_re, norm_one, div_one] at h
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have herr : 2 * (N : ℝ) * (1 + 1) * ((N : ℝ) + 1) ^ (-(1 : ℝ)) ≤ 4 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith
  have hS : ‖dirichletPartialSum (fun j => χ (j + 1)) N 1‖ ≤ 1 + Real.log N := by
    unfold dirichletPartialSum
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (harmonic_le_one_add_log N)
    rw [harmonic]
    push_cast
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := norm_ofReal_cpow_neg hn 1
    push_cast at this
    rw [this, Real.rpow_neg_one]
    exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  calc ‖LFunction χ 1‖
      ≤ ‖LFunction χ 1 - dirichletPartialSum (fun j => χ (j + 1)) N 1‖
        + ‖dirichletPartialSum (fun j => χ (j + 1)) N 1‖ := norm_le_norm_sub_add _ _
    _ ≤ 4 + (1 + Real.log N) := add_le_add (h.trans herr) hS
    _ = Real.log N + 5 := by ring

/-- For a quadratic character and real `σ > 0`, `L(σ, χ)` is real. -/
theorem LFunction_ofReal_im {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 0 < σ) : (LFunction χ σ).im = 0 := by
  have hbound : ∀ M : ℕ, |(LFunction χ σ).im| ≤ 4 * N * ((M : ℝ) + 1) ^ (-σ) := by
    intro M
    have h := norm_LFunction_sub_character_partial_le hχ (s := σ) (by simpa using hσ) M
    have hσn : ‖(σ : ℂ)‖ / σ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ, div_self hσ.ne']
    simp only [Complex.ofReal_re, hσn] at h
    have him : (dirichletPartialSum (fun j => χ (j + 1)) M σ).im = 0 := by
      unfold dirichletPartialSum
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun n _ => ?_
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hn, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re]
      have := quadratic_apply_im hq ((n + 1 : ℕ) : ZMod N)
      push_cast at this
      rw [this]; ring
    calc |(LFunction χ σ).im|
        = |(LFunction χ σ - dirichletPartialSum (fun j => χ (j + 1)) M σ).im| := by
          rw [Complex.sub_im, him, sub_zero]
      _ ≤ ‖LFunction χ σ - dirichletPartialSum (fun j => χ (j + 1)) M σ‖ :=
          Complex.abs_im_le_norm _
      _ ≤ 2 * N * (1 + 1) * ((M : ℝ) + 1) ^ (-σ) := h
      _ = 4 * N * ((M : ℝ) + 1) ^ (-σ) := by ring
  have ht : Tendsto (fun M : ℕ => 4 * (N : ℝ) * ((M : ℝ) + 1) ^ (-σ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => ((M : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop hσ).comp h1
    simpa using this.const_mul (4 * (N : ℝ))
  have : |(LFunction χ σ).im| ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hbound)
  exact abs_nonpos_iff.mp this

/-- `ζ(σ)` is real for real `σ`. -/
lemma riemannZeta_ofReal_im (σ : ℝ) : (riemannZeta σ).im = 0 := by
  have h := riemannZeta_conj σ
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

open scoped ComplexOrder in
/-- `L(2, χ) > 0` for a nontrivial quadratic character. -/
theorem LFunction_two_re_pos {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) :
    0 < (LFunction χ 2).re := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) 2 := by
    simpa [ArithmeticFunction.natCoe_apply] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have h1 := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ.norm_le_one n) hs
  have hX : LSeries (fun n => χ.zetaMul n) 2 = riemannZeta 2 * LFunction χ 2 := by
    rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' hz h1,
      LSeries_toArithmeticFunction, LFunction_eq_LSeries χ hs]
    congr 1
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    congr 1
  have hge := one_le_re_LSeries_two (a := fun n => χ.zetaMul n) (fun n => zetaMul_nonneg hq n)
    (by simpa using (χ.isMultiplicative_zetaMul).map_one)
    (ArithmeticFunction.LSeriesSummable_mul hz h1)
  rw [hX, riemannZeta_two] at hge
  have hπ : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have e : (((Real.pi : ℂ) ^ 2 / 6) * LFunction χ 2).re = Real.pi ^ 2 / 6 * (LFunction χ 2).re := by
    rw [show ((Real.pi : ℂ) ^ 2 / 6) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [e] at hge
  by_contra hneg
  push Not at hneg
  nlinarith

/-- **Positivity on the real axis.**  If a nontrivial quadratic `L(s, χ)` has no zero in
`[β, 1)`, `β > 0`, then `L(σ, χ) > 0` for `β ≤ σ ≤ 2`. -/
theorem LFunction_re_pos_of_no_zero {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : 0 < β) (hz : ∀ σ : ℝ, β ≤ σ → σ < 1 → LFunction χ σ ≠ 0) {σ : ℝ}
    (hσ1 : β ≤ σ) (hσ2 : σ ≤ 2) : 0 < (LFunction χ σ).re := by
  set f : ℝ → ℝ := fun t => (LFunction χ t).re with hf
  have hfc : Continuous f :=
    Complex.continuous_re.comp ((differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal)
  have hreal : ∀ t : ℝ, 0 < t → LFunction χ t = (f t : ℂ) := fun t ht =>
    Complex.ext (by simp [hf]) (by simp [LFunction_ofReal_im hq hχ ht])
  by_contra hneg
  push Not at hneg
  have h2 : 0 < f 2 := by simpa [hf] using LFunction_two_re_pos hq
  obtain ⟨t, ⟨ht1, ht2⟩, hft⟩ := intermediate_value_Icc hσ2 hfc.continuousOn
    ⟨hneg, h2.le⟩
  have ht0 : 0 < t := by linarith
  have hL : LFunction χ t = 0 := by rw [hreal t ht0, hft]; simp
  rcases lt_or_ge t 1 with h | h
  · exact hz t (by linarith) h hL
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using h) hL

/-- `ζ(σ) < 0` in a left neighbourhood of `1`. -/
theorem exists_riemannZeta_neg : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ σ : ℝ, 1 - δ₀ < σ → σ < 1 → (riemannZeta σ).re < 0 := by
  have ht := tendsto_riemannZeta_sub_one_div
  have hev := ht.eventually (Metric.ball_mem_nhds (Real.eulerMascheroniConstant : ℂ) one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hev
  refine ⟨min δ (1 / 2), by positivity, min_le_right _ _, fun σ hσ1 hσ2 => ?_⟩
  have hdist : dist (σ : ℂ) 1 < δ := by
    rw [Complex.dist_eq, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith [min_le_left δ (1 / 2)]
  have hne : (σ : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact_mod_cast hσ2.ne
  have hb := hball ⟨Metric.mem_ball.mpr hdist, hne⟩
  rw [Complex.dist_eq] at hb
  have hre := (Complex.abs_re_le_norm _).trans hb.le
  rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
    show (1 : ℂ) / ((σ : ℂ) - 1) = (((σ - 1)⁻¹ : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re] at hre
  have hγ : Real.eulerMascheroniConstant < 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hinv : (σ - 1)⁻¹ ≤ -2 := by
    have hneg : σ - 1 < 0 := by linarith
    rw [inv_eq_one_div, div_le_iff_of_neg hneg]
    nlinarith [min_le_right δ (1 / 2)]
  have := (abs_le.mp hre).2
  linarith

end RHTower
