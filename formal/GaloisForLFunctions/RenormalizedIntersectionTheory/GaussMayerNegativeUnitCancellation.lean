import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRankOneDeterminantPole
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantRankOne
import GaloisForLFunctions.HTGeometry.RankOneHilbertSchmidt

/-!
# Successor cancellation in the negative-unit Mayer determinant

The actual response `f_w(z)=1-(1+z)^(-w)` telescopes under the Gauss branches
and satisfies `(I+R(w))f_w=1`, with `f_w(0)=0`, throughout `Re w>0`.
Cauchy analysis carries this identity and evaluation at zero to the existing
Hilbert realization. The rank-one determinant update then cancels its own
trace exponential, proving `det(I+R(w)+tP)=det(I+R(w))` for every scalar `t`.
Consequently the actual source determinant at spectral parameter `-1` is
holomorphic through the operator's pole, including its assigned value there.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter

set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation

private theorem digit_re_pos {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    0 < ((n : ℂ) + z).re := by
  have hr := (neg_le_abs (z - 1).re).trans (Complex.abs_re_le_norm (z - 1))
  have hd : ‖z - 1‖ ≤ (3 / 2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Complex.sub_re, Complex.one_re] at hr
  simp only [Complex.add_re, Complex.natCast_re]
  linarith only [hr, hd, hn']

/-- The principal branches respect this successor quotient throughout the right half-plane. -/
private theorem cpow_successor {a : ℂ} (ha : 0 < a.re) (v : ℂ) :
    a^v * (1 + a⁻¹)^v = (a + 1)^v := by
  have ha0 : a ≠ 0 := by intro he; simp only [he, Complex.zero_re, lt_self_iff_false] at ha
  have hc : 0 < (a + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith only [ha]
  have hc0 : a + 1 ≠ 0 := by intro he; simp only [he, Complex.zero_re, lt_self_iff_false] at hc
  have he : 1 + a⁻¹ = (a + 1) / a := by field_simp [ha0]
  have hb0 : 1 + a⁻¹ ≠ 0 := by rw [he]; exact div_ne_zero hc0 ha0
  have hargA := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hargC := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hc))
  have hlo : -Real.pi < (Complex.log (a + 1) - Complex.log a).im := by
    simp only [Complex.sub_im, Complex.log_im]
    linarith only [hargA.2, hargC.1]
  have hhi : (Complex.log (a + 1) - Complex.log a).im ≤ Real.pi := by
    simp only [Complex.sub_im, Complex.log_im]
    linarith only [hargA.1, hargC.2]
  have hexp : Complex.exp (Complex.log (a + 1) - Complex.log a) = (a + 1) / a := by
    rw [Complex.exp_sub, Complex.exp_log hc0, Complex.exp_log ha0]
  have hlog : Complex.log (1 + a⁻¹) = Complex.log (a + 1) - Complex.log a := by
    rw [he, ← hexp, Complex.log_exp hlo hhi]
  rw [Complex.cpow_def_of_ne_zero ha0, Complex.cpow_def_of_ne_zero hb0,
    Complex.cpow_def_of_ne_zero hc0, ← Complex.exp_add, hlog]
  congr 1
  ring

private theorem weight_differentiableOn (w : ℂ) :
    DifferentiableOn ℂ (fun z : ℂ => (1 + z)^(-w)) outer := by
  intro z hz
  have hr : 0 < (1 + z).re := by
    simpa only [Nat.cast_one] using digit_re_pos (n := 1) le_rfl hz
  exact (((hasDerivAt_id z).const_add 1).cpow_const
    (c := -w) (Complex.mem_slitPlane_iff.mpr (Or.inl hr))).differentiableAt.differentiableWithinAt

/-- A vanishing-at-zero source response, holomorphic on the actual disc for every exponent. -/
def response (w : ℂ) : DiscSpace :=
  ofHolomorphic (fun z => 1 - (1 + z)^(-w))
    (continuousOn_const.sub (weight_differentiableOn w).continuousOn)
    (((weight_differentiableOn w).const_sub 1).mono ball_subset_closedBall)

@[simp] theorem response_apply (w : ℂ) (z : Disc) :
    (response w).1 z = 1 - (1 + z.1)^(-w) := rfl

theorem projection_response (w : ℂ) : constantProjection (response w) = 0 := by
  apply Subtype.ext
  ext z
  change (1 : ℂ) - (1 + 0)^(-w) = 0
  rw [add_zero, Complex.one_cpow, sub_self]

/-- The actual branch terms telescope throughout the source half-plane. -/
theorem branch_response {w : ℂ} (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n) (z : Disc) :
    (branch w hw n hn (response w)).1 z =
      ((n : ℂ) + z.1)^(-w) - (((n : ℂ) + z.1) + 1)^(-w) := by
  rw [branch_apply]
  have hz : ((n : ℂ) + z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num) (inverse_branch_inner hn z.property)
  rw [plane_eq (response w) ⟨_, hz⟩, response_apply, mul_sub, mul_one,
    cpow_successor (digit_re_pos hn z.property)]

/-- The first `N` actual response weights telescope with an explicit tail. -/
theorem partial_telescope (w z : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((((n + 1 : ℕ) : ℂ) + z)^(-w) - ((((n + 1 : ℕ) : ℂ) + z) + 1)^(-w))) =
      (1 + z)^(-w) - (((N + 1 : ℕ) : ℂ) + z)^(-w) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (((N + 1 : ℕ) : ℂ) + z) + 1 = ((N + 1 + 1 : ℕ) : ℂ) + z := by
      push_cast
      ring
    rw [he]
    ring

private theorem power_tail_tendsto {w : ℂ} (hw : 0 < w.re) (z : Disc) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℂ) + z.1)^(-w)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hn : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp := ((_root_.tendsto_rpow_neg_atTop hw).comp hn).const_mul (powerBound w)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => norm_branch_weight_le hw
    (n := N + 1) (by omega) z.property)
  simpa only [Function.comp_apply, mul_zero] using hp

/-- The exact response is supplied by the genuine holomorphic remainder at every source parameter. -/
theorem remainder_response {w : ℂ} (hw : 0 < w.re) :
    remainder w (response w) = constant 1 - response w := by
  have hs : Summable (fun n => entireRemainder n w) := remainder_locallyUniform.summable hw
  apply Subtype.ext
  ext z
  have hv := (evaluation z).hasSum
    ((ContinuousLinearMap.apply ℂ DiscSpace (response w)).hasSum hs.hasSum)
  change HasSum (fun n => (entireRemainder n w (response w)).1 z)
    ((remainder w (response w)).1 z) at hv
  have he : (fun n => (entireRemainder n w (response w)).1 z) =
      fun n => ((((n + 1 : ℕ) : ℂ) + z.1)^(-w) -
        ((((n + 1 : ℕ) : ℂ) + z.1) + 1)^(-w)) := by
    funext n
    rw [entireRemainder_eq hw, branchRemainder, _root_.sub_apply,
      _root_.smul_apply, projection_response, smul_zero, sub_zero]
    exact branch_response hw _ (by omega) z
  rw [he] at hv
  have ht := hv.tendsto_sum_nat
  have hp : (fun N => ∑ n ∈ Finset.range N,
      ((((n + 1 : ℕ) : ℂ) + z.1)^(-w) - ((((n + 1 : ℕ) : ℂ) + z.1) + 1)^(-w))) =
      fun N => (1 + z.1)^(-w) - (((N + 1 : ℕ) : ℂ) + z.1)^(-w) :=
    funext (partial_telescope w z.1)
  rw [hp] at ht
  have heq : (remainder w (response w)).1 z = (1 + z.1)^(-w) :=
    tendsto_nhds_unique ht (by simpa only [sub_zero] using
      (tendsto_const_nhds.sub (power_tail_tendsto hw z)))
  rw [heq]
  change (1 + z.1)^(-w) = 1 - (1 - (1 + z.1)^(-w))
  ring

/-- The same actual response works for every scalar constant-mode perturbation. -/
theorem perturbed_response {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    response w + (remainder w + t • constantProjection) (response w) = constant 1 := by
  rw [_root_.add_apply, _root_.smul_apply, projection_response, smul_zero, add_zero,
    remainder_response hw]
  abel

/-- Evaluation at zero in the rescaled Cauchy coordinates. -/
def evaluationWeight (j : ℕ) : ℂ := ((balanceRadius : ℂ)^j)⁻¹ * (-1 : ℂ)^j

private def coefficientCoordinate (j : ℕ) : SequenceSpace →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j

private theorem norm_coefficientCoordinate_le (j : ℕ) : ‖coefficientCoordinate j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x : ℕ → ℂ) j‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x j

private theorem norm_evaluationWeight (j : ℕ) : ‖evaluationWeight j‖ = balanceRadius⁻¹ ^ j := by
  rw [evaluationWeight, norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg balanceRadius_pos.le, norm_pow, norm_neg, norm_one, one_pow,
    mul_one, inv_pow]

private theorem summable_norm_evaluationTerm :
    Summable (fun j => ‖evaluationWeight j • coefficientCoordinate j‖) := by
  apply (summable_geometric_of_lt_one (inv_nonneg.mpr balanceRadius_pos.le)
    (by norm_num [balanceRadius])).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  rw [norm_smul, norm_evaluationWeight]
  exact mul_le_of_le_one_right (pow_nonneg (inv_nonneg.mpr balanceRadius_pos.le) _)
    (norm_coefficientCoordinate_le j)

/-- Bounded evaluation functional defined by its summable coefficient coordinates. -/
def coefficientEvaluation : SequenceSpace →L[ℂ] ℂ :=
  ∑' j, evaluationWeight j • coefficientCoordinate j

/-- Evaluation is the convergent weighted sum of the Hilbert coordinates. -/
theorem coefficientEvaluation_hasSum (x : SequenceSpace) :
    HasSum (fun j => evaluationWeight j * (x : ℕ → ℂ) j) (coefficientEvaluation x) := by
  have hs : HasSum (fun j => evaluationWeight j • coefficientCoordinate j)
      coefficientEvaluation := summable_norm_evaluationTerm.of_norm.hasSum
  have h := (ContinuousLinearMap.apply ℂ ℂ x).hasSum hs
  exact h

theorem coefficientEvaluation_single (j : ℕ) :
    coefficientEvaluation (lp.single 2 j 1) = evaluationWeight j := by
  rw [← (coefficientEvaluation_hasSum (lp.single 2 j 1)).tsum_eq, tsum_eq_single j]
  · rw [lp.single_apply_self, mul_one]
  · intro k hk
    rw [lp.single_apply_ne _ _ _ hk, mul_zero]

/-- Cauchy's formula proves that the Hilbert functional is actual source evaluation. -/
theorem coefficientEvaluation_analysis (f : DiscSpace) :
    coefficientEvaluation (analysisMap f) = f.1 zeroPoint := by
  have hsum := coefficientEvaluation_hasSum (analysisMap f)
  have hd : DifferentiableOn ℂ (plane f) (closedBall 1 coefficientRadius) :=
    (differentiableOn_plane f).mono (closedBall_subset_ball radii.2.2)
  have ht := DiscCoefficients.hasSum_coeff coefficientRadius_pos balanceRadius_pos hd
    (z := 0) (by norm_num [mem_ball, dist_eq_norm, coefficientRadius])
  have he : (fun j => evaluationWeight j * (analysisMap f : ℕ → ℂ) j) =
      fun j => DiscCoefficients.coeff 1 coefficientRadius balanceRadius j (plane f) *
        (((0 : ℂ) - 1) / (balanceRadius : ℂ))^j := by
    funext j
    rw [analysis_coordinate]
    change (((balanceRadius : ℂ)^j)⁻¹ * (-1 : ℂ)^j) *
      ((balanceRadius : ℂ)^j * DiscCoefficients.cauchyCoeff 1 coefficientRadius j (plane f)) =
      ((balanceRadius : ℂ)^j * DiscCoefficients.cauchyCoeff 1 coefficientRadius j (plane f)) *
        (((0 : ℂ) - 1) / (balanceRadius : ℂ))^j
    rw [zero_sub, div_pow, div_eq_mul_inv]
    ring
  rw [he] at hsum
  exact (hsum.unique ht).trans (plane_eq f zeroPoint)

/-- The Hilbert vector carrying the actual constant output. -/
def constantVector : SequenceSpace := analysisMap (constant 1)

/-- The rank-one pole projection on the established Hilbert realization. -/
def hilbertProjection : SequenceSpace →L[ℂ] SequenceSpace :=
  coefficientEvaluation.smulRight constantVector

private theorem constant_smul_one (c : ℂ) : constant c = c • constant 1 := by
  apply Subtype.ext
  ext z
  change c = c * 1
  rw [mul_one]

theorem hilbertProjection_analysis (f : DiscSpace) :
    hilbertProjection (analysisMap f) = analysisMap (constantProjection f) := by
  rw [hilbertProjection, ContinuousLinearMap.smulRight_apply, coefficientEvaluation_analysis]
  change f.1 zeroPoint • analysisMap (constant 1) = analysisMap (constant (f.1 zeroPoint))
  conv_rhs => rw [constant_smul_one, map_smul]

theorem matrixOf_hilbertProjection :
    HilbertSchmidt.matrixOf hilbertProjection = fun p => MayerPole.projectionMatrix p.1 p.2 := by
  funext p
  change (hilbertProjection (lp.single 2 p.2 1) : ℕ → ℂ) p.1 = _
  rw [hilbertProjection, ContinuousLinearMap.smulRight_apply, coefficientEvaluation_single]
  change evaluationWeight p.2 * (analysisMap (constant 1) : ℕ → ℂ) p.1 = _
  rw [analysis_coordinate]
  change evaluationWeight p.2 * ((balanceRadius : ℂ)^p.1 *
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 p.1 (constant 1)) = _
  rw [MayerPole.coefficient_constant, MayerPole.projectionMatrix_eq]
  by_cases hi : p.1 = 0
  · rw [hi]
    simp only [ite_true, pow_zero, mul_one]
    rfl
  · rw [if_neg hi, mul_zero, mul_zero, if_neg hi]

/-- Remove only the zeta constant mode from the existing Hilbert source operator. -/
def remainderOperator (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] SequenceSpace :=
  hilbertOperator w hw - riemannZeta w • hilbertProjection

theorem remainderOperator_analysis {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    remainderOperator w hw (analysisMap f) = analysisMap (remainder w f) := by
  rw [remainderOperator, _root_.sub_apply, _root_.smul_apply, hilbertProjection_analysis]
  have hs := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f) (synthesis_comp_analysis hw)
  change synthesisMap w hw (analysisMap f) = regularized w hw f at hs
  change analysisMap (synthesisMap w hw (analysisMap f)) -
    riemannZeta w • analysisMap (constantProjection f) = _
  rw [hs, ← source_eq hw, source, _root_.add_apply, _root_.smul_apply,
    map_add, map_smul, add_sub_cancel_left]

theorem hilbert_response {w : ℂ} (hw : 0 < w.re) :
    analysisMap (response w) + remainderOperator w hw (analysisMap (response w)) =
      constantVector := by
  rw [remainderOperator_analysis hw, ← map_add, remainder_response hw]
  have he : response w + (constant 1 - response w) = constant 1 := by abel
  rw [he]
  rfl

theorem coefficientEvaluation_response (w : ℂ) :
    coefficientEvaluation (analysisMap (response w)) = 0 := by
  rw [coefficientEvaluation_analysis]
  change (1 : ℂ) - (1 + 0)^(-w) = 0
  rw [add_zero, Complex.one_cpow, sub_self]

theorem coefficientEvaluation_constant : coefficientEvaluation constantVector = 1 := by
  rw [constantVector, coefficientEvaluation_analysis]
  rfl

theorem isHilbertSchmidt_remainderOperator {w : ℂ} (hw : 0 < w.re) :
    ContinuousLinearMap.IsHilbertSchmidt (remainderOperator w hw) := by
  have hs : ContinuousLinearMap.IsHilbertSchmidt (hilbertOperator w hw) := by
    rw [← toOperator_kernel hw]
    exact HilbertSchmidt.isHilbertSchmidt_toOperator _
  exact hs.sub ((isHilbertSchmidt_smulRight coefficientEvaluation constantVector).smul (riemannZeta w))

/-- The fixed Cauchy geometric decay gives a Hilbert–Schmidt kernel. -/
theorem geometric_isHS {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) :
    HilbertSchmidt.IsHS (fun p : ℕ × ℕ => M p.1 p.2) := by
  have hs : Summable (fun k : ℕ => (rate ^ 2) ^ k) :=
    summable_geometric_of_lt_one (sq_nonneg rate)
      (GeomFredholm.sq_lt_one rate_bounds.1 rate_bounds.2)
  have hp : Summable (fun p : ℕ × ℕ => (rate ^ 2) ^ p.1 * (rate ^ 2) ^ p.2) :=
    summable_mul_of_summable_norm hs.norm hs.norm
  apply (hp.mul_left (C ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro p
  calc
    ‖M p.1 p.2‖ ^ 2 ≤ (C * rate ^ p.1 * rate ^ p.2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hM.bound p.1 p.2) 2
    _ = _ := by simp only [mul_pow, ← pow_mul, Nat.mul_comm]; ring

/-- The same fixed geometric bound makes the diagonal absolutely summable. -/
theorem geometric_diagonal_summable {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) : Summable (fun i => M i i) := by
  have hs := (GeomFredholm.hasSum_pow_two_mul rate_bounds.1 rate_bounds.2).summable.mul_left C
  have hn : Summable (fun i => ‖M i i‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i =>
      (hM.bound i i).trans_eq (mul_assoc _ _ _))
  exact hn.of_norm

/-- The geometric Fredholm limit has its genuine diagonal correction at the negative unit. -/
theorem fdet_negative_one_eq_entireDet2 {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) :
    GeomFredholm.fdet M (-1) =
      entireDet2 (fun p : ℕ × ℕ => M p.1 p.2) (-1) * Complex.exp (∑' i, M i i) := by
  let K : ℕ × ℕ → ℂ := fun p => M p.1 p.2
  have hreg : Tendsto (fun N => finiteDet2 (-(GeomFredholm.trunc M N)) (-1))
      atTop (𝓝 (entireDet2 K (-1))) := by
    have he (N : ℕ) : finiteDet2 (-(GeomFredholm.trunc M N)) (-1) =
        finiteDet2 (-(HilbertSchmidt.blockMatrix K (Finset.range N))) (-1) := by
      let e : Fin N ≃ Finset.range N :=
        { toFun := fun i => ⟨i, Finset.mem_range.mpr i.isLt⟩
          invFun := fun i => ⟨i, Finset.mem_range.mp i.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hm : -(GeomFredholm.trunc M N) =
          (-(HilbertSchmidt.blockMatrix K (Finset.range N))).submatrix e e := by
        ext i j
        rfl
      rw [hm, finiteDet2_submatrix]
    simp only [he]
    exact (tendsto_finiteDet2_entireDet2 (geometric_isHS hM) (-1)).comp Filter.tendsto_finset_range
  have htr : Tendsto (fun N => (GeomFredholm.trunc M N).trace) atTop (𝓝 (∑' i, M i i)) := by
    have he (N : ℕ) : (GeomFredholm.trunc M N).trace = ∑ i ∈ Finset.range N, M i i := by
      simp only [Matrix.trace, Matrix.diag_apply, GeomFredholm.trunc, Matrix.of_apply]
      exact Fin.sum_univ_eq_sum_range (fun i => M i i) N
    simp only [he]
    exact (geometric_diagonal_summable hM).hasSum.tendsto_sum_nat
  have hdiag := (Complex.continuous_exp.tendsto _).comp htr
  have he (N : ℕ) : GeomFredholm.truncDet M (-1) N =
      finiteDet2 (-(GeomFredholm.trunc M N)) (-1) *
        Complex.exp (GeomFredholm.trunc M N).trace := by
    rw [finiteDet2_neg_neg_one]
    unfold finiteDet2 GeomFredholm.truncDet
    simp only [one_smul, one_mul, neg_smul, one_smul, sub_neg_eq_add]
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have ht := hreg.mul hdiag
  have hf : Tendsto (GeomFredholm.truncDet M (-1)) atTop
      (𝓝 (entireDet2 K (-1) * Complex.exp (∑' i, M i i))) := by
    simpa only [Function.comp_apply, ← he] using ht
  exact tendsto_nhds_unique (GeomFredholm.tendsto_truncDet hM (-1)) hf

private theorem matrixOf_remainderOperator {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.matrixOf (remainderOperator w hw) =
      fun p => MayerPole.remainderMatrix w p.1 p.2 := by
  funext p
  change HilbertSchmidt.matrixOf (hilbertOperator w hw) p -
    riemannZeta w * HilbertSchmidt.matrixOf hilbertProjection p = _
  rw [matrixOf_hilbertOperator, matrixOf_hilbertProjection]
  rw [← sourceMatrix_eq hw]
  change sourceMatrix w p.1 p.2 - riemannZeta w * MayerPole.projectionMatrix p.1 p.2 = _
  rw [MayerPole.sourceMatrix_decomposition]
  ring

private theorem matrixOf_perturbed {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    HilbertSchmidt.matrixOf (remainderOperator w hw + t • hilbertProjection) =
      fun p => MayerPole.perturbedMatrix w t p.1 p.2 := by
  funext p
  change HilbertSchmidt.matrixOf (remainderOperator w hw) p +
    t * HilbertSchmidt.matrixOf hilbertProjection p = _
  rw [matrixOf_remainderOperator hw, matrixOf_hilbertProjection]
  rfl

/-- The canonical Hilbert basis leaves the actual coefficient matrix unchanged. -/
theorem coordMatrix_canonical (T : SequenceSpace →L[ℂ] SequenceSpace) :
    _root_.RHTower.coordMatrix (HilbertSchmidt.lpBasis ℕ) T = HilbertSchmidt.matrixOf T := by
  rfl

/-- The exact response makes the regularized determinant acquire only its trace exponential. -/
theorem det2_perturbed {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (remainderOperator w hw + t • hilbertProjection) =
      _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (remainderOperator w hw) * Complex.exp (-t) := by
  let y : SequenceSpace := (InnerProductSpace.toDual ℂ SequenceSpace).symm coefficientEvaluation
  have hy (x : SequenceSpace) : inner ℂ y x = coefficientEvaluation x :=
    InnerProductSpace.toDual_symm_apply
  have hu : t • analysisMap (response w) + remainderOperator w hw (t • analysisMap (response w)) =
      t • constantVector := by
    rw [map_smul, ← smul_add, hilbert_response hw]
  have he : InnerProductSpace.rankOne ℂ (t • constantVector) y = t • hilbertProjection := by
    apply ContinuousLinearMap.ext
    intro x
    rw [InnerProductSpace.rankOne_apply, hy]
    change coefficientEvaluation x • (t • constantVector) =
      t • (coefficientEvaluation x • constantVector)
    exact smul_comm _ _ _
  have h := det2Op_rankOne_update (HilbertSchmidt.lpBasis ℕ) (isHilbertSchmidt_remainderOperator hw)
    (t • analysisMap (response w)) (t • constantVector) y hu
  rw [he, hy, hy, map_smul, map_smul, coefficientEvaluation_response,
    coefficientEvaluation_constant, smul_eq_mul, smul_eq_mul, mul_zero, mul_one,
    add_zero, mul_one] at h
  exact h

private theorem perturbed_geometric {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    ∃ C, GeomFredholm.GeomDecay (MayerPole.perturbedMatrix w t) C rate := by
  obtain ⟨r, C, hr, _, hC⟩ := MayerPole.remainderMatrix_local_bound hw
  have hR := hC w (mem_closedBall_self hr.le)
  refine ⟨C + ‖t‖, ⟨add_nonneg hR.const_nonneg (norm_nonneg _),
    rate_bounds.1, rate_bounds.2, fun i j => ?_⟩⟩
  have hP : ‖MayerPole.projectionMatrix i j‖ ≤ rate^i * rate^j := by
    simpa only [one_mul] using MayerPole.geomDecay_projection.bound i j
  change ‖MayerPole.remainderMatrix w i j + t * MayerPole.projectionMatrix i j‖ ≤ _
  calc
    _ ≤ ‖MayerPole.remainderMatrix w i j‖ + ‖t‖ * ‖MayerPole.projectionMatrix i j‖ := by
      simpa only [norm_mul] using norm_add_le (MayerPole.remainderMatrix w i j)
        (t * MayerPole.projectionMatrix i j)
    _ ≤ C * rate^i * rate^j + ‖t‖ * (rate^i * rate^j) :=
      add_le_add (hR.bound i j) (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
    _ = _ := by ring

private theorem perturbed_diagonal {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    (∑' i, MayerPole.perturbedMatrix w t i i) =
      (∑' i, MayerPole.remainderMatrix w i i) + t := by
  obtain ⟨r, C, hr, _, hC⟩ := MayerPole.remainderMatrix_local_bound hw
  have hR := geometric_diagonal_summable (hC w (mem_closedBall_self hr.le))
  have hP := geometric_diagonal_summable MayerPole.geomDecay_projection
  have hp : (∑' i, MayerPole.projectionMatrix i i) = 1 := by
    rw [tsum_eq_single 0]
    · simp only [MayerPole.projectionMatrix_eq, ite_true, pow_zero, inv_one, one_mul]
    · intro i hi
      rw [MayerPole.projectionMatrix_eq, if_neg hi]
  change (∑' i, (MayerPole.remainderMatrix w i i + t * MayerPole.projectionMatrix i i)) = _
  rw [hR.tsum_add (hP.mul_left t), tsum_mul_left, hp, mul_one]

private theorem perturbedDeterminant_eq_det2 {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    MayerPole.perturbedDeterminant w t (-1) =
      _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (remainderOperator w hw + t • hilbertProjection) *
        Complex.exp ((∑' i, MayerPole.remainderMatrix w i i) + t) := by
  obtain ⟨C, hC⟩ := perturbed_geometric hw t
  rw [MayerPole.perturbedDeterminant, fdet_negative_one_eq_entireDet2 hC,
    _root_.RHTower.det2Op, coordMatrix_canonical, matrixOf_perturbed hw, perturbed_diagonal hw]

/-- The actual negative-unit determinant is insensitive to the scalar pole coefficient. -/
theorem perturbedDeterminant_negative_one {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    MayerPole.perturbedDeterminant w t (-1) = MayerPole.perturbedDeterminant w 0 (-1) := by
  rw [perturbedDeterminant_eq_det2 hw t, perturbedDeterminant_eq_det2 hw 0,
    det2_perturbed hw t, det2_perturbed hw 0]
  simp only [neg_zero, Complex.exp_zero, mul_one, add_zero]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The nonzero spectral parameter `−1` annihilates the entire scalar pole coefficient. -/
theorem polePart_negative_one {w : ℂ} (hw : 0 < w.re) : MayerPole.polePart w (-1) = 0 := by
  rw [MayerPole.polePart, perturbedDeterminant_negative_one hw 1, sub_self]

/-- The actual source determinant equals its holomorphic remainder determinant at `λ=−1`. -/
theorem sourceDeterminant_negative_one {w : ℂ} (hw : 0 < w.re) :
    sourceDeterminant w (-1) = MayerPole.regularPart w (-1) := by
  rw [MayerPole.sourceDeterminant_decomposition hw, polePart_negative_one hw, mul_zero, add_zero]

/-- Cancellation holds throughout the source half-plane, including the actual value at one. -/
theorem differentiableOn_sourceDeterminant_negative_one :
    DifferentiableOn ℂ (fun w => sourceDeterminant w (-1)) {w : ℂ | 0 < w.re} :=
  (MayerPole.differentiableOn_regularPart (-1)).congr fun _ hw => sourceDeterminant_negative_one hw

/-- The genuine negative-unit source determinant is analytic at the operator's pole. -/
theorem analyticAt_sourceDeterminant_negative_one :
    AnalyticAt ℂ (fun w => sourceDeterminant w (-1)) 1 :=
  differentiableOn_sourceDeterminant_negative_one.analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))

#print axioms branch_response
#print axioms remainder_response
#print axioms perturbed_response

#print axioms coefficientEvaluation_analysis
#print axioms matrixOf_hilbertProjection
#print axioms hilbert_response
#print axioms isHilbertSchmidt_remainderOperator
#print axioms det2_perturbed
#print axioms perturbedDeterminant_negative_one
#print axioms polePart_negative_one
#print axioms sourceDeterminant_negative_one
#print axioms differentiableOn_sourceDeterminant_negative_one
#print axioms analyticAt_sourceDeterminant_negative_one

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation
