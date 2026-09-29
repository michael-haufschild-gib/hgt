import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Compact observers are blind to strongly vanishing nuclear families

On `ℓ²(ι)` the coordinate truncations `P_F y = ∑_{i ∈ F} y_i e_i` are contractions converging
strongly to the identity.  A compact operator `C` maps the unit ball into a relatively compact set,
which a finite `ε`-net controls, so `‖C - P_F C‖ ≤ ε` for a suitable finite `F`.

Hence if nuclear operators `N_t` have uniformly bounded trace norm and `N_t → 0` strongly, then for
every compact observer `C`

`tr(N_t C) → 0`:

`tr(N_t (C - P_F C))` is at most `‖N_t‖₁ ‖C - P_F C‖`, and `tr(N_t P_F C) = ∑_{i ∈ F} ⟨C* e_i, N_t
e_i⟩`
is a finite sum of vanishing terms.
-/

open Filter Topology ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate truncation `P_F = ∑_{i ∈ F} |e_i⟩⟨e_i|`. -/
def coordTruncation (F : Finset ι) : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  ∑ i ∈ F, rankOne ℂ (lpBasisVec i) (lpBasisVec i)

theorem inner_lpBasisVec (i : ι) (y : lp (fun _ : ι => ℂ) 2) : ⟪lpBasisVec i, y⟫_ℂ = y i := by
  rw [lpBasisVec, lp.inner_single_left]
  simp

theorem coordTruncation_apply (F : Finset ι) (y : lp (fun _ : ι => ℂ) 2) :
    coordTruncation F y = ∑ i ∈ F, lp.single 2 i (y i) := by
  rw [coordTruncation, FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rankOne_apply, inner_lpBasisVec, lpBasisVec, ← lp.single_smul]
  simp

theorem norm_coordTruncation_apply_le (F : Finset ι) (y : lp (fun _ : ι => ℂ) 2) :
    ‖coordTruncation F y‖ ≤ ‖y‖ := by
  rw [coordTruncation_apply]
  have h1 := lp.norm_sum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) (fun i => y i) F
  have h2 := lp.norm_rpow_eq_tsum (E := fun _ : ι => ℂ) (p := 2) (by norm_num) y
  have hsum := (lp.memℓp y).summable (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
  have h3 : ∑ i ∈ F, ‖y i‖ ^ (2 : ℝ≥0∞).toReal ≤ ∑' i, ‖y i‖ ^ (2 : ℝ≥0∞).toReal :=
    hsum.sum_le_tsum F fun i _ => by positivity
  rw [← h1, ← h2] at h3
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h3

theorem eventually_norm_sub_coordTruncation_lt (y : lp (fun _ : ι => ℂ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ F in atTop, ‖y - coordTruncation F y‖ < ε := by
  have h := (lp.hasSum_single (E := fun _ : ι => ℂ) (p := 2) (by norm_num) y)
  rw [HasSum, Metric.tendsto_nhds] at h
  filter_upwards [h ε hε] with F hF
  rw [dist_eq_norm] at hF
  rw [coordTruncation_apply, norm_sub_rev]
  exact hF

/-- **Finite-rank truncation of compact operators.** -/
theorem exists_norm_sub_coordTruncation_comp_le
    {C : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hC : IsCompactOperator C) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ‖C - coordTruncation F ∘L C‖ ≤ ε := by
  set S := C '' Metric.closedBall 0 1
  have hS : IsCompact (closure S) := hC.isCompact_closure_image_closedBall 1
  obtain ⟨t, htS, htfin, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hS (show 0 < ε / 3 by positivity)
  have hev : ∀ᶠ F in atTop, ∀ y ∈ t, ‖y - coordTruncation F y‖ < ε / 3 :=
    (htfin.eventually_all).mpr fun y _ => eventually_norm_sub_coordTruncation_lt y (by positivity)
  obtain ⟨F, hF⟩ := hev.exists
  refine ⟨F, opNorm_le_bound _ hε.le fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set u : lp (fun _ : ι => ℂ) 2 := (‖x‖⁻¹ : ℂ) • x
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hxpos.ne']
  have hmem : C u ∈ S := ⟨u, by rw [Metric.mem_closedBall, dist_zero_right, hu], rfl⟩
  obtain ⟨y, hy, hyball⟩ := Set.mem_iUnion₂.mp (hcover hmem)
  rw [Metric.mem_ball, dist_eq_norm] at hyball
  have hbound : ‖(C - coordTruncation F ∘L C) u‖ ≤ ε := by
    rw [sub_apply, comp_apply]
    calc ‖C u - coordTruncation F (C u)‖
        = ‖(C u - y) + (y - coordTruncation F y) + coordTruncation F (y - C u)‖ := by
          rw [map_sub]
          congr 1
          abel
      _ ≤ ‖C u - y‖ + ‖y - coordTruncation F y‖ + ‖coordTruncation F (y - C u)‖ :=
          norm_add₃_le
      _ ≤ ε / 3 + ε / 3 + ‖y - C u‖ :=
          add_le_add (add_le_add hyball.le (hF y hy).le) (norm_coordTruncation_apply_le F _)
      _ ≤ ε := by
          rw [norm_sub_rev]
          linarith
  have hxne : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hxu : x = (‖x‖ : ℂ) • u := by
    rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
  have hsm : (C - coordTruncation F ∘L C) x = (‖x‖ : ℂ) • (C - coordTruncation F ∘L C) u := by
    rw [← map_smul, ← hxu]
  calc ‖(C - coordTruncation F ∘L C) x‖ = ‖x‖ * ‖(C - coordTruncation F ∘L C) u‖ := by
        rw [hsm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = ε * ‖x‖ := mul_comm _ _

omit [DecidableEq ι] in
theorem hasRankLE_rankOne (u v : lp (fun _ : ι => ℂ) 2) : RHTower.HasRankLE (rankOne ℂ u v) 1 := by
  refine ⟨Submodule.span ℂ {u}, FiniteDimensional.span_of_finite ℂ (Set.finite_singleton u), ?_,
    fun x => ?_⟩
  · have := finrank_span_le_card (R := ℂ) ({u} : Set (lp (fun _ : ι => ℂ) 2))
    simpa using this
  · rw [rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

omit [DecidableEq ι] in
theorem memSchattenClass_one_rankOne (u v : lp (fun _ : ι => ℂ) 2) :
    RHTower.MemSchattenClass 1 (rankOne ℂ u v) :=
  RHTower.memSchattenClass_of_hasRankLE one_pos (hasRankLE_rankOne u v)

theorem memSchattenClass_one_sum_rankOne (F : Finset ι) (u v : ι → lp (fun _ : ι => ℂ) 2) :
    RHTower.MemSchattenClass 1 (∑ i ∈ F, rankOne ℂ (u i) (v i)) := by
  induction F using Finset.induction_on with
  | empty =>
      simpa using RHTower.memSchattenClass_of_hasRankLE one_pos
        (RHTower.hasRankLE_zero (H := lp (fun _ : ι => ℂ) 2) 0)
  | insert j F hj ih =>
      rw [Finset.sum_insert hj]
      have h1 := memSchattenClass_one_rankOne (u j) (v j)
      exact RHTower.memSchattenClass_one_add (h1.isCompactOperator one_pos)
        (ih.isCompactOperator one_pos) h1 ih

theorem opTrace_sum_rankOne (F : Finset ι) (u v : ι → lp (fun _ : ι => ℂ) 2) :
    opTrace (∑ i ∈ F, rankOne ℂ (u i) (v i)) = ∑ i ∈ F, ⟪v i, u i⟫_ℂ := by
  induction F using Finset.induction_on with
  | empty =>
      simp [opTrace]
  | insert j F hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        RHTower.opTrace_add_of_memSchattenClass_one (memSchattenClass_one_rankOne _ _)
          (memSchattenClass_one_sum_rankOne F u v), ih, opTrace_rankOne]

theorem comp_coordTruncation_comp_eq (N C : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (F : Finset ι) :
    N ∘L (coordTruncation F ∘L C)
      = ∑ i ∈ F, rankOne ℂ (N (lpBasisVec i)) (adjoint C (lpBasisVec i)) := by
  ext y
  simp only [comp_apply, coordTruncation, FunLike.coe_sum, Finset.sum_apply,
    rankOne_apply, map_sum, map_smul, adjoint_inner_left]

/-- **Compact observers are blind.**  If `N_t` are nuclear with trace norms at most `B` and
`N_t → 0` strongly, then `tr(N_t C) → 0` for every compact `C`. -/
theorem tendsto_opTrace_comp_of_isCompactOperator {α : Type*} {l : Filter α}
    (N : α → lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (hN : ∀ t, RHTower.MemSchattenClass 1 (N t)) {B : ℝ}
    (hB : ∀ t, RHTower.traceNorm (lp (fun _ : ι => ℂ) 2) (N t) ≤ B)
    (hstrong : ∀ x, Tendsto (fun t => N t x) l (𝓝 0))
    {C : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2} (hC : IsCompactOperator C) :
    Tendsto (fun t => opTrace (N t ∘L C)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' := max B 0
  have hB0 : 0 ≤ B' := le_max_right _ _
  obtain ⟨F, hF⟩ := exists_norm_sub_coordTruncation_comp_le hC
    (show 0 < ε / (2 * (B' + 1)) by positivity)
  have hfin : Tendsto (fun t => ∑ i ∈ F, ⟪adjoint C (lpBasisVec i), N t (lpBasisVec i)⟫_ℂ) l
      (𝓝 0) := by
    have : Tendsto (fun t => ∑ i ∈ F, ⟪adjoint C (lpBasisVec i), N t (lpBasisVec i)⟫_ℂ) l
        (𝓝 (∑ i ∈ F, ⟪adjoint C (lpBasisVec i), (0 : lp (fun _ : ι => ℂ) 2)⟫_ℂ)) :=
      tendsto_finsetSum _ fun i _ => tendsto_const_nhds.inner (hstrong (lpBasisVec i))
    simpa using this
  filter_upwards [Metric.tendsto_nhds.mp hfin (ε / 2) (by positivity)] with t ht
  rw [dist_zero_right] at ht ⊢
  have hsplit : N t ∘L C
      = N t ∘L (C - coordTruncation F ∘L C) + N t ∘L (coordTruncation F ∘L C) := by
    rw [← ContinuousLinearMap.comp_add, sub_add_cancel]
  have hS1a := (hN t).one_comp_right (C - coordTruncation F ∘L C)
  have hS1b := (hN t).one_comp_right (coordTruncation F ∘L C)
  rw [hsplit, RHTower.opTrace_add_of_memSchattenClass_one hS1a hS1b,
    comp_coordTruncation_comp_eq, opTrace_sum_rankOne]
  have h1 := RHTower.norm_opTrace_comp_le_norm_mul_traceNorm (hN t) (C - coordTruncation F ∘L C)
  have h2 : RHTower.traceNorm (lp (fun _ : ι => ℂ) 2) (N t) * ‖C - coordTruncation F ∘L C‖
      ≤ B' * (ε / (2 * (B' + 1))) :=
    mul_le_mul ((hB t).trans (le_max_left _ _)) hF (norm_nonneg _) hB0
  have h3 : B' * (ε / (2 * (B' + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖opTrace (N t ∘L (C - coordTruncation F ∘L C))
        + ∑ i ∈ F, ⟪adjoint C (lpBasisVec i), N t (lpBasisVec i)⟫_ℂ‖
      ≤ ‖opTrace (N t ∘L (C - coordTruncation F ∘L C))‖
        + ‖∑ i ∈ F, ⟪adjoint C (lpBasisVec i), N t (lpBasisVec i)⟫_ℂ‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans (h2.trans h3.le)) ht
    _ = ε := by ring

end GaloisForLFunctions.HTGeometry
