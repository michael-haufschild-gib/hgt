import GaloisForLFunctions.HTGeometry.SourceCompleteFusionRecovery

/-!
# Source-complete corona: countermodels and load-bearing hypotheses

* **(SC.43)–(SC.44)** On the explicit carrier, `T_n = |e_n⟩⟨e_n|` satisfies every source-completeness
  hypothesis with `tr T_n = ‖T_n‖₁ = 1`: it moves to the corona, and its energy for `C e_j = (j+1) e_j`
  is `n + 1 → ∞`.  Properness, not another compact observer, is the selection law.
* Finite dimension, full support, label simplicity, normality and reporter compactness are each
  load-bearing (§9.2–§9.6).
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate ENNReal ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

/-! ## §9.1 Source completeness without properness does not select -/

/-- The heat source whose projector is the fusion projector `P = |Ω⟩⟨Ω|`. -/
def fusionHeatSource : HeatSource ℕ where
  lam _ := 1
  gap := 1
  gap_pos := one_pos
  gap_le _ := le_rfl
  v := fusionVector

theorem fusionHeatSource_heatProjection : fusionHeatSource.heatProjection = fusionProjection := rfl

theorem lpCoordProjection_comm_lpDiag {ι : Type*} [DecidableEq ι] (lam : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖lam i‖ ≤ M) (j : ι) :
    lpCoordProjection j ∘L LpDiagonal.lpDiag lam M hM hb = LpDiagonal.lpDiag lam M hM hb ∘L lpCoordProjection j := by
  ext1 x
  simp only [comp_apply, lpCoordProjection_apply, LpDiagonal.lpDiag_coe, map_smul, LpDiagonal.lpDiag_single]
  rw [smul_smul, mul_comm]

theorem opTrace_lpCoordProjection {ι : Type*} [DecidableEq ι] (j : ι) :
    opTrace (lpCoordProjection (ι := ι) j) = 1 := by
  rw [lpCoordProjection, opTrace_rankOne, inner_single_one_left, lp.single_apply_self]

theorem tendsto_fusionCoeff : Tendsto fusionCoeff atTop (𝓝 0) := by
  have h := hasSum_norm_fusionCoeff_sq.summable.tendsto_atTop_zero
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_zero] at h2
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h2.congr fun n => ?_)
  simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

/-- **(SC.43)–(SC.44) The coordinate countermodel.**  `T_n = |e_n⟩⟨e_n|` satisfies **(SC.7)** for the
explicit pair `(L, P)`, has `tr T_n = ‖T_n‖₁ = 1`, so it does not vanish in trace norm, and its
energy for the proper cost `C e_j = (j+1) e_j` is `n + 1 → ∞`. -/
theorem coordinate_countermodel :
    IsAsymptoticallySourceInvariant ![sourceLabel, fusionProjection] (fun n => lpCoordProjection (ι := ℕ) n) ∧
    (∀ n, opTrace (lpCoordProjection (ι := ℕ) n) = 1) ∧
    (∀ n, traceNorm ℓ²ℕ (lpCoordProjection (ι := ℕ) n) = 1) ∧
    (∀ n, properCostEnergy (HilbertSchmidt.lpBasis ℕ) (fun j => (j : ℝ) + 1) (lpCoordProjection n) =
      ENNReal.ofReal ((n : ℝ) + 1)) ∧
    Tendsto (fun n => properCostEnergy (HilbertSchmidt.lpBasis ℕ) (fun j => (j : ℝ) + 1)
      (lpCoordProjection (ι := ℕ) n)) atTop (𝓝 ⊤) := by
  have henergy : ∀ n, properCostEnergy (HilbertSchmidt.lpBasis ℕ) (fun j => (j : ℝ) + 1)
      (lpCoordProjection (ι := ℕ) n) = ENNReal.ofReal ((n : ℝ) + 1) := fun n => by
    rw [properCostEnergy, tsum_eq_single n fun k hk => ?_]
    · rw [HilbertSchmidt.lpBasis_apply, lpCoordProjection_apply, lp.single_apply_self, one_smul,
        inner_single_one_left, lp.single_apply_self, Complex.one_re, mul_one]
    · rw [HilbertSchmidt.lpBasis_apply, lpCoordProjection_apply]
      simp [lp.single_apply, Pi.single_eq_of_ne hk.symm]
  refine ⟨⟨fun n => isPositive_lpCoordProjection n, fun n => memSchattenClass_lpCoordProjection n,
    ⟨1, fun n => by rw [opTrace_lpCoordProjection, Complex.one_re]⟩, fun a => ?_⟩,
    opTrace_lpCoordProjection, traceNorm_lpCoordProjection, henergy, ?_⟩
  · fin_cases a
    · show Tendsto (fun n => traceNorm ℓ²ℕ (lpCoordProjection n ∘L sourceLabel -
        sourceLabel ∘L lpCoordProjection n)) atTop (𝓝 0)
      refine tendsto_const_nhds.congr fun n => ?_
      rw [sourceLabel, lpCoordProjection_comm_lpDiag, sub_self, traceNorm_zero]
    · show Tendsto (fun n => traceNorm ℓ²ℕ (lpCoordProjection n ∘L fusionProjection -
        fusionProjection ∘L lpCoordProjection n)) atTop (𝓝 0)
      have hb : Tendsto (fun n => 2 * ‖fusionCoeff n‖ * ‖fusionVector‖) atTop (𝓝 0) := by
        simpa using ((tendsto_fusionCoeff.norm).const_mul 2).mul_const ‖fusionVector‖
      refine squeeze_zero (fun n => traceNorm_nonneg _) (fun n => ?_) hb
      exact fusionHeatSource.traceNorm_lpCoordProjection_commutator_le n
  · simp_rw [henergy]
    exact ENNReal.tendsto_ofReal_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- **§9.6 Reporter compactness is load-bearing.**  For the coordinate countermodel every compact
observer sees `tr(K T_n) → 0`, while the non-compact identity detects `tr T_n = 1`. -/
theorem coordinate_countermodel_compact_vs_identity :
    (∀ K : ℓ²ℕ →L[ℂ] ℓ²ℕ, IsCompactOperator K →
      Tendsto (fun n => opTrace (K ∘L lpCoordProjection (ι := ℕ) n)) atTop (𝓝 0)) ∧
    (∀ n, opTrace (ContinuousLinearMap.id ℂ ℓ²ℕ ∘L lpCoordProjection (ι := ℕ) n) = 1) ∧
    ¬ IsCompactOperator (ContinuousLinearMap.id ℂ ℓ²ℕ) :=
  ⟨fun K hK => coordinate_countermodel.1.tendsto_opTrace_comp (HilbertSchmidt.lpBasis ℕ)
      isSourceComplete_sourceLabel_fusion K hK,
    fun n => by rw [id_comp, opTrace_lpCoordProjection],
    not_isCompactOperator_id (HilbertSchmidt.lpBasis ℕ)⟩

/-! ## §9.2 Finite dimension -/

theorem memSchattenClass_one_of_finiteDimensional {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →L[ℂ] H) : MemSchattenClass 1 T := by
  have hr : HasRankLE T (Module.finrank ℂ H) :=
    ⟨⊤, inferInstance, (finrank_top ℂ H).le, fun _ => Submodule.mem_top⟩
  have h0 : ∀ n, Module.finrank ℂ H ≤ n → approxNumber T n = 0 := fun n hn =>
    le_antisymm ((approxNumber_le T n T (hr.mono hn)).trans (by simp)) (approxNumber_nonneg _ _)
  unfold MemSchattenClass
  refine summable_of_ne_finset_zero (s := Finset.range (Module.finrank ℂ H)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [h0 n hn, Real.zero_rpow one_ne_zero]

/-- **§9.2 Finite dimension does not convert scalarity into extinction.**  On `ℂ^N` a simple diagonal
label and a full-support vector are source-complete, yet `N^{-1}·1` is a nonzero invariant positive
trace-one defect. -/
theorem finiteDimension_countermodel {N : ℕ} (hN : 0 < N) (lam : Fin N → ℂ) (hlam : Function.Injective lam)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, ‖lam i‖ ≤ M) (ω : lp (fun _ : Fin N => ℂ) 2) (hω : ∀ i, ω i ≠ 0) :
    IsSourceComplete ![LpDiagonal.lpDiag lam M hM hb, InnerProductSpace.rankOne ℂ ω ω] ∧
    let T : lp (fun _ : Fin N => ℂ) 2 →L[ℂ] lp (fun _ : Fin N => ℂ) 2 :=
      ((N : ℂ)⁻¹) • ContinuousLinearMap.id ℂ _
    T ≠ 0 ∧ T.IsPositive ∧ MemSchattenClass 1 T ∧ opTrace T = 1 ∧
      ∀ X : lp (fun _ : Fin N => ℂ) 2 →L[ℂ] lp (fun _ : Fin N => ℂ) 2, T ∘L X = X ∘L T := by
  refine ⟨isSourceComplete_diag_rankOne lam hlam hM hb ω hω, ?_⟩
  intro T
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hS : MemSchattenClass 1 T := memSchattenClass_one_of_finiteDimensional T
  refine ⟨fun h0 => ?_, ?_, hS, ?_, fun X => ?_⟩
  · have h1 := congrArg (fun A : lp (fun _ : Fin N => ℂ) 2 →L[ℂ] lp (fun _ : Fin N => ℂ) 2 =>
      A (lp.single 2 ⟨0, hN⟩ (1 : ℂ)) ⟨0, hN⟩) h0
    simp [T, hN'] at h1
  · refine (isPositive_id (𝕜 := ℂ) (E := lp (fun _ : Fin N => ℂ) 2)).smul_of_nonneg ?_
    rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.zero_le_real.2 (by positivity)
  · rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis (Fin N)), tsum_fintype]
    simp only [T, smul_apply, id_apply, inner_smul_right, HilbertSchmidt.lpBasis_apply,
      inner_single_one_left, lp.single_apply_self, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · simp only [T, smul_comp, comp_smul, id_comp, comp_id]

/-! ## §9.3 Full support -/

/-- **§9.3 Full support is load-bearing.**  If `Ω_k = 0`, the nonzero finite-rank defect `|e_k⟩⟨e_k|`
commutes with every diagonal label and with `|Ω⟩⟨Ω|`. -/
theorem fullSupport_countermodel {ι : Type*} [DecidableEq ι] (lam : ι → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖lam i‖ ≤ M) (ω : lp (fun _ : ι => ℂ) 2) {k : ι} (hk : ω k = 0) :
    lpCoordProjection k ≠ 0 ∧ MemSchattenClass 1 (lpCoordProjection (ι := ι) k) ∧
    lpCoordProjection k ∘L LpDiagonal.lpDiag lam M hM hb = LpDiagonal.lpDiag lam M hM hb ∘L lpCoordProjection k ∧
    lpCoordProjection k ∘L InnerProductSpace.rankOne ℂ ω ω = InnerProductSpace.rankOne ℂ ω ω ∘L lpCoordProjection k := by
  refine ⟨fun h0 => ?_, memSchattenClass_lpCoordProjection k, lpCoordProjection_comm_lpDiag lam hM hb k, ?_⟩
  · have h1 := congrArg (fun A : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 =>
      A (lp.single 2 k (1 : ℂ)) k) h0
    simp [lpCoordProjection_apply] at h1
  · ext1 x
    simp only [comp_apply, lpCoordProjection_apply, InnerProductSpace.rankOne_apply, map_smul,
      hk, smul_zero, inner_single_one_right, map_zero, zero_smul]

/-! ## §9.4 Label simplicity -/

theorem rankOne_comp_rankOne_of_inner_eq_zero {ι : Type*} {u ω : lp (fun _ : ι => ℂ) 2}
    (h : ⟪ω, u⟫_ℂ = 0) :
    InnerProductSpace.rankOne ℂ u u ∘L InnerProductSpace.rankOne ℂ ω ω = 0 ∧
      InnerProductSpace.rankOne ℂ ω ω ∘L InnerProductSpace.rankOne ℂ u u = 0 := by
  have h' : ⟪u, ω⟫_ℂ = 0 := by rw [← inner_conj_symm, h, map_zero]
  refine ⟨ContinuousLinearMap.ext fun x => ?_, ContinuousLinearMap.ext fun x => ?_⟩
  · simp [InnerProductSpace.rankOne_apply, h']
  · simp [InnerProductSpace.rankOne_apply, h]

/-- **§9.4 Label simplicity is load-bearing.**  If a real diagonal label repeats an eigenvalue,
`λ_i = λ_j` with `i ≠ j`, some nonzero vector of that eigenspace is orthogonal to `Ω`, and its rank-one
projection commutes with the label and with `|Ω⟩⟨Ω|`. -/
theorem simplicity_countermodel {ι : Type*} [DecidableEq ι] (lam : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k, ‖((lam k : ℝ) : ℂ)‖ ≤ M) (ω : lp (fun _ : ι => ℂ) 2) {i j : ι} (hij : i ≠ j)
    (hlam : lam i = lam j) :
    ∃ u : lp (fun _ : ι => ℂ) 2, u ≠ 0 ∧ ⟪ω, u⟫_ℂ = 0 ∧ (∀ k, u k ≠ 0 → lam k = lam i) ∧
      InnerProductSpace.rankOne ℂ u u ∘L LpDiagonal.lpDiag (fun k => (lam k : ℂ)) M hM hb =
        LpDiagonal.lpDiag (fun k => (lam k : ℂ)) M hM hb ∘L InnerProductSpace.rankOne ℂ u u ∧
      InnerProductSpace.rankOne ℂ u u ∘L InnerProductSpace.rankOne ℂ ω ω =
        InnerProductSpace.rankOne ℂ ω ω ∘L InnerProductSpace.rankOne ℂ u u := by
  set D := LpDiagonal.lpDiag (fun k => (lam k : ℂ)) M hM hb
  obtain ⟨u, hu0, hωu, hsupp⟩ : ∃ u : lp (fun _ : ι => ℂ) 2, u ≠ 0 ∧ ⟪ω, u⟫_ℂ = 0 ∧
      ∀ k, u k ≠ 0 → lam k = lam i := by
    by_cases hωi : ω i = 0
    · refine ⟨lp.single 2 i 1, fun h => ?_, ?_, fun k hk => ?_⟩
      · have := congrArg (fun x : lp (fun _ : ι => ℂ) 2 => x i) h
        simp at this
      · rw [inner_single_one_right, hωi, map_zero]
      · by_cases hki : k = i
        · rw [hki]
        · simp [lp.single_apply, Pi.single_eq_of_ne hki] at hk
    · refine ⟨starRingEnd ℂ (ω j) • lp.single 2 i 1 - starRingEnd ℂ (ω i) • lp.single 2 j 1, fun h => ?_,
        ?_, fun k hk => ?_⟩
      · have := congrArg (fun x : lp (fun _ : ι => ℂ) 2 => x j) h
        simp [lp.single_apply, Pi.single_eq_of_ne (Ne.symm hij), hωi] at this
      · rw [inner_sub_right, inner_smul_right, inner_smul_right, inner_single_one_right,
          inner_single_one_right]
        ring
      · by_cases hki : k = i
        · rw [hki]
        · by_cases hkj : k = j
          · rw [hkj, hlam]
          · simp [lp.single_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj] at hk
  have hDu : D u = ((lam i : ℝ) : ℂ) • u := by
    refine lp.ext (funext fun k => ?_)
    rw [LpDiagonal.lpDiag_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hk : u k = 0
    · rw [hk, mul_zero, mul_zero]
    · rw [hsupp k hk]
  have huD : ∀ x, ⟪u, D x⟫_ℂ = ((lam i : ℝ) : ℂ) * ⟪u, x⟫_ℂ := fun x => by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [LpDiagonal.lpDiag_coe, RCLike.inner_apply, RCLike.inner_apply]
    by_cases hk : u k = 0
    · simp [hk]
    · rw [hsupp k hk]
      ring
  refine ⟨u, hu0, hωu, hsupp, ContinuousLinearMap.ext fun x => ?_, ?_⟩
  · simp only [comp_apply, InnerProductSpace.rankOne_apply, map_smul, hDu, huD, smul_smul, mul_comm]
  · rw [(rankOne_comp_rankOne_of_inner_eq_zero hωu).1, (rankOne_comp_rankOne_of_inner_eq_zero hωu).2]

/-! ## §9.5 Normality -/

section Normality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem tendsto_inner_hilbertBasis (b : HilbertBasis ℕ ℂ E) (z : E) :
    Tendsto (fun n => ⟪z, b n⟫_ℂ) atTop (𝓝 0) := by
  have hs : Summable fun n => ‖b.repr z n‖ ^ 2 := summable_norm_sq_lp (b.repr z)
  have h1 := (Real.continuous_sqrt.tendsto 0).comp hs.tendsto_atTop_zero
  simp only [Real.sqrt_zero] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun n => ?_)
  rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _), HilbertBasis.repr_apply_apply, ← inner_conj_symm,
    Complex.norm_conj]

/-- **§9.5** The corona character `ω_∞(K + c1) = c` is positive on the unitization: a positive
`K + c1` with `K` compact has `c ≥ 0` (test against the weakly null basis). -/
theorem coronaCharacter_nonneg (b : HilbertBasis ℕ ℂ E) {K : E →L[ℂ] E} (hK : IsCompactOperator K) {c : ℂ}
    (hX : (K + c • ContinuousLinearMap.id ℂ E).IsPositive) : 0 ≤ c := by
  have hKb := tendsto_norm_compact_of_weaklyNull K hK (fun n => b n) (fun n => (b.orthonormal.1 n).le)
    (tendsto_inner_hilbertBasis b)
  have h1 : Tendsto (fun n => ⟪b n, (K + c • ContinuousLinearMap.id ℂ E) (b n)⟫_ℂ) atTop (𝓝 c) := by
    have h2 : Tendsto (fun n => ⟪b n, K (b n)⟫_ℂ) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hKb.norm)
      calc ‖⟪b n, K (b n)⟫_ℂ‖ ≤ ‖b n‖ * ‖K (b n)‖ := norm_inner_le_norm _ _
        _ = ‖K (b n)‖ := by rw [b.orthonormal.1 n, one_mul]
    have h3 := h2.add_const c
    rw [zero_add] at h3
    refine h3.congr fun n => ?_
    rw [add_apply, smul_apply, id_apply, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 n]
    simp
  exact ge_of_tendsto' h1 fun n => hX.inner_nonneg_right _

/-- **§9.5** The corona character is unitarily invariant: `U(K + c1)U* = UKU* + c1` with `UKU*`
compact. -/
theorem coronaCharacter_invariant {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [CompleteSpace E'] {U : E →L[ℂ] E'} (hU : U ∘L adjoint U = ContinuousLinearMap.id ℂ E')
    {K : E →L[ℂ] E} (hK : IsCompactOperator K) (c : ℂ) :
    cornerConj U (K + c • ContinuousLinearMap.id ℂ E) = cornerConj U K + c • ContinuousLinearMap.id ℂ E' ∧
      IsCompactOperator (cornerConj U K) := by
  refine ⟨?_, (hK.comp_clm (adjoint U)).clm_comp U⟩
  simp only [cornerConj, add_comp, comp_add, smul_comp, comp_smul, id_comp, hU]

/-- **§9.5 Normality is load-bearing.**  No trace-class density represents the corona character:
`tr((K + c1)D) = c` for all compact `K` would give `tr D = 1` while every head trace vanishes. -/
theorem coronaCharacter_not_normal (b : HilbertBasis ℕ ℂ E) :
    ¬ ∃ D : E →L[ℂ] E, MemSchattenClass 1 D ∧ ∀ K : E →L[ℂ] E, IsCompactOperator K → ∀ c : ℂ,
      opTrace ((K + c • ContinuousLinearMap.id ℂ E) ∘L D) = c := by
  rintro ⟨D, hD, hrep⟩
  have h1 : opTrace D = 1 := by
    have := hrep 0 isCompactOperator_zero 1
    rwa [zero_add, one_smul, id_comp] at this
  have hhead : ∀ r, ∑ i ∈ Finset.range (r + 1), ⟪b i, D (b i)⟫_ℂ = 0 := fun r => by
    have := hrep (basisHead b r) (isCompactOperator_basisHead b r) 0
    rwa [zero_smul, add_zero, opTrace_basisHead_comp b hD] at this
  have hsum : HasSum (fun i => ⟪b i, D (b i)⟫_ℂ) (opTrace D) := by
    rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hD b]
    exact (hD.one_summable_inner_diag_basis b).hasSum
  have hlim := (hsum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h0 : Tendsto (fun r => ∑ i ∈ Finset.range (r + 1), ⟪b i, D (b i)⟫_ℂ) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun r => (hhead r).symm
  rw [h1] at hlim
  exact one_ne_zero (tendsto_nhds_unique hlim h0)

end Normality

end GaloisForLFunctions.HTGeometry
