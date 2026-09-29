import GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness

/-!
# Dynamics of the forced Hodge survival shift

The forced survival shift `C e_n = √r_n e_{n+1}`, `r_n = m_{n+1}/m_n = (2n+3)/(2n+9)`, with exit
defect `D₂ = I - C*C = diag(h_n)`, satisfies:

* **(PHSF.4)** `Cᴺ e_k = √(m_{k+N}/m_k) e_{k+N}`, so `‖Cᴺ e_k‖² = m_{k+N}/m_k` and `Cᴺ → 0`
  strongly;
* **(PHSF.5)** nevertheless `‖Cᴺ‖ = 1` for every `N`, since `m_{k+N}/m_k → 1` as `k → ∞`;
* **(PHSF.9)** `C*ʲ D₂ Cʲ = diag(w_{k+j}/m_k)` and `C*ᴺ Cᴺ = diag(m_{k+N}/m_k)`, hence
  `I - C*ᴺ Cᴺ = ∑_{j<N} C*ʲ D₂ Cʲ`;
* **(PHSF.10)** exact observability `∑_j ‖√D₂ Cʲ x‖² = ‖x‖²`;
* **(PHSF.11)** `⟨Cⁿ e_0, D₂ Cⁿ e_0⟩ = w_n`;
* `C - S` is compact for the unilateral shift `S`;
* a positive nearest-neighbour history with survival tails `m_n` has weights `√r_n`.
-/

open Filter Topology Set ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-- The coordinate basis of `ℓ²(ℕ)`. -/
abbrev historyCoord : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  _root_.HTGeometry.ellTwoCoordinateBasis ℕ

theorem historyCoord_eq (n : ℕ) : historyCoord n = lp.single 2 n (1 : ℂ) :=
  _root_.HTGeometry.ellTwoCoordinateBasis_apply n

/-! ## Weighted shifts -/

/-- `(C^N) e_k = (∏_{j<N} √r_{k+j}) e_{k+N}` for the survival shift. -/
theorem survivalShift_pow_basis_prod (N k : ℕ) :
    (primeHodgeHistorySurvivalShift ^ N) (historyCoord k)
      = (∏ j ∈ Finset.range N, primeHodgeHistorySurvivalWeight (k + j)) • historyCoord (k + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, comp_apply, ih, map_smul,
      primeHodgeHistorySurvivalShift_basis,
      smul_smul, Finset.prod_range_succ, ← add_assoc]

theorem prod_survivalWeight (N k : ℕ) :
    ∏ j ∈ Finset.range N, primeHodgeHistorySurvivalWeight (k + j)
      = ((Real.sqrt (PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) : ℝ) : ℂ) := by
  induction N with
  | zero => simp [div_self (PrimeHodgeHistory.m_pos k).ne']
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, primeHodgeHistorySurvivalWeight, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (div_nonneg (PrimeHodgeHistory.m_pos _).le (PrimeHodgeHistory.m_pos _).le),
      PrimeHodgeHistory.survivalRatio, ← add_assoc]
    congr 2
    have h1 := (PrimeHodgeHistory.m_pos k).ne'
    have h2 := (PrimeHodgeHistory.m_pos (k + N)).ne'
    field_simp

/-- **(PHSF.4).**  `Cᴺ e_k = √(m_{k+N}/m_k) e_{k+N}`. -/
theorem survivalShift_pow_basis (N k : ℕ) :
    (primeHodgeHistorySurvivalShift ^ N) (historyCoord k)
      = ((Real.sqrt (PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) : ℝ) : ℂ) •
        historyCoord (k + N) := by
  rw [survivalShift_pow_basis_prod, prod_survivalWeight]

theorem norm_historyCoord (n : ℕ) : ‖historyCoord n‖ = 1 :=
  historyCoord.orthonormal.1 n

/-- **(PHSF.4).**  `‖Cᴺ e_k‖² = m_{k+N}/m_k`. -/
theorem norm_survivalShift_pow_basis_sq (N k : ℕ) :
    ‖(primeHodgeHistorySurvivalShift ^ N) (historyCoord k)‖ ^ 2
      = PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k := by
  rw [survivalShift_pow_basis, norm_smul, norm_historyCoord, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt
      (div_nonneg (PrimeHodgeHistory.m_pos _).le (PrimeHodgeHistory.m_pos _).le)]

theorem norm_survivalShift_le_one : ‖primeHodgeHistorySurvivalShift‖ ≤ 1 := by
  refine (opNorm_comp_le _ _).trans ?_
  have h1 : ‖GaloisForLFunctions.HTGeometry.shiftOp 1‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have h2 : ‖primeHodgeHistorySurvivalDiagonal‖ ≤ 1 :=
    _root_.HTGeometry.norm_ellTwoDiagonal_le _ _ zero_le_one
  calc ‖GaloisForLFunctions.HTGeometry.shiftOp 1‖ * ‖primeHodgeHistorySurvivalDiagonal‖
      ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_survivalShift_pow_apply_le (N : ℕ) (x : lp (fun _ : ℕ => ℂ) 2) :
    ‖(primeHodgeHistorySurvivalShift ^ N) x‖ ≤ ‖x‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, comp_apply]
    exact (le_opNorm _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      norm_survivalShift_le_one).trans ih)

theorem norm_survivalShift_pow_le (N : ℕ) : ‖primeHodgeHistorySurvivalShift ^ N‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact norm_survivalShift_pow_apply_le N x

/-- **(PHSF.4).**  `Cᴺ → 0` strongly. -/
theorem tendsto_survivalShift_pow_apply (x : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun N => (primeHodgeHistorySurvivalShift ^ N) x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := (eventually_norm_sub_coordTruncation_lt x (show 0 < ε / 2 by positivity)).exists
  have hbasis : ∀ k, Tendsto (fun N => ‖(primeHodgeHistorySurvivalShift ^ N) (historyCoord k)‖)
      atTop (𝓝 0) := fun k => by
    have hm0 : Tendsto (fun N => PrimeHodgeHistory.m (N + k) / PrimeHodgeHistory.m k) atTop
        (𝓝 (0 / PrimeHodgeHistory.m k)) :=
      (PrimeHodgeHistory.m_tendsto_zero.comp (tendsto_add_atTop_nat k)).div_const _
    rw [zero_div] at hm0
    have hm : Tendsto (fun N => PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) atTop
        (𝓝 0) := hm0.congr fun N => by rw [add_comm]
    have hs := (Real.continuous_sqrt.tendsto 0).comp hm
    rw [Real.sqrt_zero] at hs
    refine hs.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← Real.sqrt_sq (norm_nonneg _), norm_survivalShift_pow_basis_sq]
  have hfin : Tendsto (fun N => ∑ k ∈ F, ‖(x : ℕ → ℂ) k‖ *
      ‖(primeHodgeHistorySurvivalShift ^ N) (historyCoord k)‖) atTop (𝓝 0) := by
    have h := tendsto_finsetSum F fun k _ => (hbasis k).const_mul ‖(x : ℕ → ℂ) k‖
    simpa using h
  filter_upwards [Metric.tendsto_nhds.mp hfin (ε / 2) (by positivity)] with N hN
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))] at hN
  rw [dist_zero_right, Real.norm_eq_abs, abs_norm]
  set P := primeHodgeHistorySurvivalShift ^ N
  have hsplit : x = (x - coordTruncation F x) + coordTruncation F x := by abel
  have hPF : P (coordTruncation F x) = ∑ k ∈ F, (x : ℕ → ℂ) k • P (historyCoord k) := by
    rw [coordTruncation_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [historyCoord_eq, ← map_smul, ← lp.single_smul, smul_eq_mul, mul_one]
  calc ‖P x‖ = ‖P (x - coordTruncation F x) + P (coordTruncation F x)‖ := by
        rw [← map_add, ← hsplit]
    _ ≤ ‖P (x - coordTruncation F x)‖ + ‖P (coordTruncation F x)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_le_of_lt ((norm_survivalShift_pow_apply_le N _).trans hF.le) ?_
        rw [hPF]
        refine (norm_sum_le _ _).trans_lt (lt_of_le_of_lt (Finset.sum_le_sum fun k _ => ?_) hN)
        rw [norm_smul]
    _ = ε := by ring

theorem tendsto_ratio_add (a : ℝ) (b : ℕ) (ha : 0 < a) :
    Tendsto (fun k : ℕ => (2 * (k : ℝ) + a) / (2 * ((k + b : ℕ) : ℝ) + a)) atTop (𝓝 1) := by
  have hden : Tendsto (fun k : ℕ => 2 * ((k + b : ℕ) : ℝ) + a) atTop atTop := by
    refine tendsto_atTop_add_const_right _ a ?_
    refine Tendsto.const_mul_atTop two_pos ?_
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat b)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_const_nhds (x := 2 * (b : ℝ)).div_atTop hden)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hden.eventually_gt_atTop 0] with k hk
  push_cast at hk ⊢
  field_simp
  ring

/-- `m_{k+N}/m_k → 1` as `k → ∞`. -/
theorem tendsto_m_add_div_m (N : ℕ) :
    Tendsto (fun k => PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) atTop (𝓝 1) := by
  have h := ((tendsto_ratio_add 3 N (by norm_num)).mul (tendsto_ratio_add 5 N (by norm_num))).mul
    (tendsto_ratio_add 7 N (by norm_num))
  rw [one_mul, one_mul] at h
  refine h.congr fun k => ?_
  simp only [PrimeHodgeHistory.m]
  push_cast
  have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (k : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (k : ℝ) + 7) ≠ 0 := by positivity
  have h3' : (2 * ((k : ℝ) + N) + 3) ≠ 0 := by positivity
  have h5' : (2 * ((k : ℝ) + N) + 5) ≠ 0 := by positivity
  have h7' : (2 * ((k : ℝ) + N) + 7) ≠ 0 := by positivity
  field_simp

/-- **(PHSF.5).**  `‖Cᴺ‖ = 1` for every `N`. -/
theorem norm_survivalShift_pow (N : ℕ) : ‖primeHodgeHistorySurvivalShift ^ N‖ = 1 := by
  refine le_antisymm (norm_survivalShift_pow_le N) ?_
  have hlim := (Real.continuous_sqrt.tendsto 1).comp (tendsto_m_add_div_m N)
  rw [Real.sqrt_one] at hlim
  refine le_of_tendsto' hlim fun k => ?_
  simp only [Function.comp_apply]
  have h := le_opNorm (primeHodgeHistorySurvivalShift ^ N) (historyCoord k)
  rw [norm_historyCoord, mul_one, ← Real.sqrt_sq (norm_nonneg _),
    norm_survivalShift_pow_basis_sq] at h
  exact h

/-! ## Exit records as operator telescopes -/

theorem historyCoord_ext {A B : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2}
    (h : ∀ i j, ⟪historyCoord i, A (historyCoord j)⟫_ℂ = ⟪historyCoord i, B (historyCoord j)⟫_ℂ) :
    A = B := by
  refine ContinuousLinearMap.ext_on (s := Set.range historyCoord)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr historyCoord.dense_span) ?_
  rintro _ ⟨j, rfl⟩
  apply historyCoord.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  exact h i j

theorem inner_historyCoord (i k : ℕ) :
    ⟪historyCoord i, historyCoord k⟫_ℂ = if i = k then 1 else 0 :=
  orthonormal_iff_ite.mp historyCoord.orthonormal i k

theorem diagonal_historyCoord (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (k : ℕ) :
    _root_.HTGeometry.ellTwoDiagonal lam hC (historyCoord k) = lam k • historyCoord k :=
  _root_.HTGeometry.ellTwoDiagonal_coordinateBasis lam hC k

theorem inner_diagonal_historyCoord (lam : ℕ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (i k : ℕ) :
    ⟪historyCoord i, _root_.HTGeometry.ellTwoDiagonal lam hC (historyCoord k)⟫_ℂ
      = if i = k then lam k else 0 := by
  rw [diagonal_historyCoord, inner_smul_right, inner_historyCoord]
  split_ifs <;> simp

theorem survivalAmplitude_sq (N k : ℕ) :
    ((Real.sqrt (PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) : ℝ) : ℂ) *
        ((Real.sqrt (PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) : ℝ) : ℂ)
      = ((PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt
    (div_nonneg (PrimeHodgeHistory.m_pos _).le (PrimeHodgeHistory.m_pos _).le)]

theorem inner_survivalShift_pow (N i k : ℕ) (T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (lam : ℕ → ℂ) (hT : ∀ n, T (historyCoord n) = lam n • historyCoord n) :
    ⟪(primeHodgeHistorySurvivalShift ^ N) (historyCoord i),
      T ((primeHodgeHistorySurvivalShift ^ N) (historyCoord k))⟫_ℂ
      = if i = k then ((PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k : ℝ) : ℂ) *
          lam (k + N) else 0 := by
  rw [survivalShift_pow_basis, survivalShift_pow_basis, map_smul, hT, smul_smul, inner_smul_left,
    inner_smul_right, inner_historyCoord, Complex.conj_ofReal]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, if_pos rfl, mul_one, ← mul_assoc, survivalAmplitude_sq]
  · rw [if_neg (by omega), if_neg hik, mul_zero, mul_zero]

/-- **(PHSF.9).**  `C*ʲ D₂ Cʲ = diag(w_{k+j}/m_k)`. -/
theorem adjoint_survivalShift_pow_exitDefect (j : ℕ) :
    adjoint (primeHodgeHistorySurvivalShift ^ j) ∘L primeHodgeHistoryExitDefect ∘L
        primeHodgeHistorySurvivalShift ^ j = primeHodgeHistoryExitRecordAt j := by
  refine historyCoord_ext fun i k => ?_
  rw [comp_apply, comp_apply, adjoint_inner_right,
    inner_survivalShift_pow j i k primeHodgeHistoryExitDefect
      (fun n => (PrimeHodgeHistory.exitHazard n : ℂ)) (fun n => diagonal_historyCoord _ _ n),
    primeHodgeHistoryExitRecordAt, inner_diagonal_historyCoord]
  split_ifs
  · rw [PrimeHodgeHistory.conditionalExitWeight, PrimeHodgeHistory.w_eq_m_mul_exitHazard]
    push_cast
    ring
  · rfl

/-- **(PHSF.9).**  `C*ᴺ Cᴺ = diag(m_{k+N}/m_k)`. -/
theorem adjoint_survivalShift_pow_comp (N : ℕ) :
    adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L primeHodgeHistorySurvivalShift ^ N
      = primeHodgeHistorySurvivalRemainder N := by
  refine historyCoord_ext fun i k => ?_
  have h := inner_survivalShift_pow N i k (ContinuousLinearMap.id ℂ _) (fun _ => 1)
    (fun n => by rw [one_smul, id_apply])
  rw [comp_apply, adjoint_inner_right, primeHodgeHistorySurvivalRemainder,
    inner_diagonal_historyCoord]
  rw [id_apply] at h
  rw [h]
  split_ifs
  · rw [mul_one]
    rfl
  · rfl

/-- **(PHSF.10).**  `I - C*ᴺ Cᴺ = ∑_{j<N} C*ʲ D₂ Cʲ`. -/
theorem survival_exit_operator_telescope (N : ℕ) :
    ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) -
      adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L
        primeHodgeHistorySurvivalShift ^ N
      = ∑ j ∈ Finset.range N, adjoint (primeHodgeHistorySurvivalShift ^ j) ∘L
          primeHodgeHistoryExitDefect ∘L primeHodgeHistorySurvivalShift ^ j := by
  simp_rw [adjoint_survivalShift_pow_exitDefect, adjoint_survivalShift_pow_comp]
  rw [← primeHodgeHistory_operator_exit_telescope N, add_sub_cancel_right]

/-- The positive square root `√D₂ = diag(√h_n)` of the exit defect. -/
def sqrtExitDefect : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  _root_.HTGeometry.ellTwoDiagonal (fun n => ((Real.sqrt (PrimeHodgeHistory.exitHazard n) : ℝ) : ℂ))
    (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (PrimeHodgeHistory.exitHazard_le_one n))

theorem adjoint_sqrtExitDefect_comp : adjoint sqrtExitDefect ∘L sqrtExitDefect
    = primeHodgeHistoryExitDefect := by
  rw [sqrtExitDefect, _root_.HTGeometry.adjoint_ellTwoDiagonal]
  ext f n
  simp only [comp_apply, _root_.HTGeometry.ellTwoDiagonal_apply, primeHodgeHistoryExitDefect,
    Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (PrimeHodgeHistory.exitHazard_pos n).le]

theorem norm_sqrtExitDefect_sq (y : lp (fun _ : ℕ => ℂ) 2) :
    ‖sqrtExitDefect y‖ ^ 2 = (⟪y, primeHodgeHistoryExitDefect y⟫_ℂ).re := by
  rw [← adjoint_sqrtExitDefect_comp, comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **(PHSF.10).**  Exact observability: `∑_j ‖√D₂ Cʲ x‖² = ‖x‖²`. -/
theorem hasSum_norm_sqrtExitDefect_survival (x : lp (fun _ : ℕ => ℂ) 2) :
    HasSum (fun j => ‖sqrtExitDefect ((primeHodgeHistorySurvivalShift ^ j) x)‖ ^ 2) (‖x‖ ^ 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ => sq_nonneg _)]
  have hpart : ∀ N, ∑ j ∈ Finset.range N,
      ‖sqrtExitDefect ((primeHodgeHistorySurvivalShift ^ j) x)‖ ^ 2
        = ‖x‖ ^ 2 - ‖(primeHodgeHistorySurvivalShift ^ N) x‖ ^ 2 := fun N => by
    have happ := congrArg (fun T => (⟪x, T x⟫_ℂ).re) (survival_exit_operator_telescope N)
    simp only [sub_apply, id_apply, inner_sub_right, Complex.sub_re, comp_apply,
      adjoint_inner_right, FunLike.coe_sum, Finset.sum_apply, inner_sum, Complex.re_sum] at happ
    have hre : ∀ y : lp (fun _ : ℕ => ℂ) 2, (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := fun y => by
      have := @inner_self_eq_norm_sq ℂ _ _ _ _ y
      simpa using this
    rw [hre, hre] at happ
    rw [happ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_sqrtExitDefect_sq]
  simp_rw [hpart]
  have h0 := ((tendsto_survivalShift_pow_apply x).norm.pow 2).const_sub (‖x‖ ^ 2)
  simpa using h0

/-- **(PHSF.11).**  `⟨Cⁿ e_0, D₂ Cⁿ e_0⟩ = w_n`. -/
theorem inner_survivalShift_pow_exitDefect_initial (n : ℕ) :
    ⟪(primeHodgeHistorySurvivalShift ^ n) (historyCoord 0),
      primeHodgeHistoryExitDefect ((primeHodgeHistorySurvivalShift ^ n) (historyCoord 0))⟫_ℂ
      = (PrimeHodgeHistory.w n : ℂ) := by
  rw [inner_survivalShift_pow n 0 0 primeHodgeHistoryExitDefect
      (fun n => (PrimeHodgeHistory.exitHazard n : ℂ)) (fun n => diagonal_historyCoord _ _ n),
    if_pos rfl, zero_add, PrimeHodgeHistory.m_zero, div_one,
    PrimeHodgeHistory.w_eq_m_mul_exitHazard]
  push_cast
  ring

/-! ## Compactness of `C - S` -/

theorem tendsto_sqrt_survivalRatio :
    Tendsto (fun n => Real.sqrt (PrimeHodgeHistory.survivalRatio n)) atTop (𝓝 1) := by
  have h := tendsto_ratio_add 3 3 (by norm_num)
  have h' : Tendsto PrimeHodgeHistory.survivalRatio atTop (𝓝 1) := by
    refine h.congr fun n => ?_
    rw [PrimeHodgeHistory.survivalRatio_formula]
    push_cast
    ring_nf
  have := (Real.continuous_sqrt.tendsto 1).comp h'
  rwa [Real.sqrt_one] at this

/-- `C - S` is compact: the survival shift is a compact perturbation of the unilateral shift. -/
theorem isCompactOperator_survivalShift_sub_shift :
    IsCompactOperator
      (primeHodgeHistorySurvivalShift - GaloisForLFunctions.HTGeometry.shiftOp 1) := by
  have hdiag : IsCompactOperator (primeHodgeHistorySurvivalDiagonal -
      ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2)) := by
    refine isCompactOperator_of_diag_tendsto_cofinite historyCoord
      (c := fun n => primeHodgeHistorySurvivalWeight n - 1) (fun n => ?_) ?_
    · rw [sub_apply, primeHodgeHistorySurvivalDiagonal, diagonal_historyCoord, id_apply, sub_smul,
        one_smul]
    · rw [Nat.cofinite_eq_atTop]
      have h := (Complex.continuous_ofReal.tendsto 1).comp tendsto_sqrt_survivalRatio
      have h2 := (h.sub_const (1 : ℂ)).norm
      simp only [Function.comp_apply, Complex.ofReal_one, sub_self, norm_zero] at h2
      exact h2
  have h := hdiag.clm_comp (GaloisForLFunctions.HTGeometry.shiftOp 1)
  have hEq : primeHodgeHistorySurvivalShift - GaloisForLFunctions.HTGeometry.shiftOp 1
      = GaloisForLFunctions.HTGeometry.shiftOp 1 ∘L (primeHodgeHistorySurvivalDiagonal -
        ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2)) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    rfl
  rw [hEq, ContinuousLinearMap.coe_comp]
  exact h

/-! ## Uniqueness of the forced survival weights -/

/-- A positive nearest-neighbour history with survival tails `m_n` has weights `√r_n`. -/
theorem survivalWeight_forced {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (h : ∀ N, ∏ j ∈ Finset.range N, c j ^ 2 = PrimeHodgeHistory.m N) (n : ℕ) :
    c n = Real.sqrt (PrimeHodgeHistory.survivalRatio n) := by
  have h1 := h (n + 1)
  rw [Finset.prod_range_succ, h n] at h1
  have hm := (PrimeHodgeHistory.m_pos n).ne'
  have hsq : c n ^ 2 = PrimeHodgeHistory.survivalRatio n := by
    rw [PrimeHodgeHistory.survivalRatio, ← h1]
    field_simp
  rw [← hsq, Real.sqrt_sq (hc n).le]

/-- **The Hodge survival colligation.**  The forced shift is a pure weighted shift that is
strongly stable but of norm one at every time, its exit records are the conditional exit weights
and telescope to the identity, its exit channel is exactly observable, and it is a compact
perturbation of the unilateral shift. -/
theorem hodge_survival_shift_dynamics :
    (∀ N k, (primeHodgeHistorySurvivalShift ^ N) (historyCoord k)
      = ((Real.sqrt (PrimeHodgeHistory.m (k + N) / PrimeHodgeHistory.m k) : ℝ) : ℂ) •
        historyCoord (k + N)) ∧
      (∀ x, Tendsto (fun N => (primeHodgeHistorySurvivalShift ^ N) x) atTop (𝓝 0)) ∧
      (∀ N, ‖primeHodgeHistorySurvivalShift ^ N‖ = 1) ∧
      (∀ N, ContinuousLinearMap.id ℂ (lp (fun _ : ℕ => ℂ) 2) -
          adjoint (primeHodgeHistorySurvivalShift ^ N) ∘L primeHodgeHistorySurvivalShift ^ N
        = ∑ j ∈ Finset.range N, adjoint (primeHodgeHistorySurvivalShift ^ j) ∘L
            primeHodgeHistoryExitDefect ∘L primeHodgeHistorySurvivalShift ^ j) ∧
      (∀ x, HasSum (fun j => ‖sqrtExitDefect ((primeHodgeHistorySurvivalShift ^ j) x)‖ ^ 2)
        (‖x‖ ^ 2)) ∧
      (∀ n, ⟪(primeHodgeHistorySurvivalShift ^ n) (historyCoord 0),
        primeHodgeHistoryExitDefect ((primeHodgeHistorySurvivalShift ^ n) (historyCoord 0))⟫_ℂ
          = (PrimeHodgeHistory.w n : ℂ)) ∧
      IsCompactOperator
        (primeHodgeHistorySurvivalShift - GaloisForLFunctions.HTGeometry.shiftOp 1) :=
  ⟨survivalShift_pow_basis, tendsto_survivalShift_pow_apply, norm_survivalShift_pow,
    survival_exit_operator_telescope, hasSum_norm_sqrtExitDefect_survival,
    inner_survivalShift_pow_exitDefect_initial, isCompactOperator_survivalShift_sub_shift⟩

end GaloisForLFunctions.HTGeometry
