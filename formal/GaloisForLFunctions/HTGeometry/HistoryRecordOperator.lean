import GaloisForLFunctions.HTGeometry.PrimeHodgeHistoryTensorDefect

/-!
# Dephased history records and stable colligations

For vectors `e_n ∈ E` with `∑ ‖e_n‖² < ∞`, the record synthesis `c ↦ (c_n e_n)_n` from `ℓ²(ℕ)`
to `ℓ²(ℕ; E)` is Hilbert–Schmidt with `‖·‖²_HS = ∑ ‖e_n‖²`, and the dephased record

`𝖳 = ⊕ₙ |e_n⟩⟨e_n|`,  `(𝖳 f)_n = ⟪e_n, f_n⟫ e_n`,

is its Gram square: positive, Schatten-one, `tr 𝖳 = ‖𝖳‖₁ = ∑ ‖e_n‖²`, with tail traces
`∑_{k ≥ n} ‖e_k‖²`, operator norm `max ‖e_n‖²`, and trace-norm continuity
`‖𝖳_a - 𝖳_b‖₁ ≤ (‖a‖ + ‖b‖) ‖a - b‖`.  For `ψ ∈ ℓ²(ℕ; E)` the grade-dephased partial sums
`∑_{n < N} P_n |ψ⟩⟨ψ| P_n` converge in trace norm to the record of `(ψ_n)_n`.

A colligation `S*S + E₀*E₀ = 1` obeys the operator telescope
`∑_{n < N} S*ⁿ E₀* E₀ Sⁿ + S*ᴺ Sᴺ = 1`; if `Sᴺ → 0` strongly, the observability map
`(O f)_n = E₀ Sⁿ f` is an isometry into `ℓ²(ℕ; E)` and the exit masses `‖E₀ Sⁿ f‖²` sum to
`‖f‖²` with tails `‖Sⁿ f‖²`.
-/

open Filter Topology Set ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The scalar history space `ℓ²(ℕ)`. -/
abbrev HistoryScalar := lp (fun _ : ℕ => ℂ) 2

/-! ## The record synthesis -/

section Record

variable (e : ℕ → E) (he : Summable fun n => ‖e n‖ ^ 2)

omit [CompleteSpace E] in
theorem norm_smul_record_sq_le (c : HistoryScalar) (n : ℕ) :
    ‖c n • e n‖ ^ 2 ≤ ‖c‖ ^ 2 * ‖e n‖ ^ 2 := by
  rw [norm_smul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (lp.norm_apply_le_norm (by norm_num) c n) 2) (sq_nonneg _)

omit [CompleteSpace E] in
include he in
theorem memℓp_recordSynthesis (c : HistoryScalar) : Memℓp (fun n => c n • e n) 2 := by
  refine (memℓp_gen_iff two_toReal_pos).mpr ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact (he.mul_left (‖c‖ ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _)
    (norm_smul_record_sq_le e c)

/-- The record synthesis as a linear map. -/
def recordSynthesisLinear : HistoryScalar →ₗ[ℂ] HistoryL2 E where
  toFun c := ⟨fun n => c n • e n, memℓp_recordSynthesis e he c⟩
  map_add' c d := by
    ext n
    simp [add_smul]
  map_smul' a c := by
    ext n
    simp [smul_smul]

omit [CompleteSpace E] in
theorem norm_recordSynthesisLinear_le (c : HistoryScalar) :
    ‖recordSynthesisLinear e he c‖ ≤ Real.sqrt (∑' n, ‖e n‖ ^ 2) * ‖c‖ := by
  refine lp.norm_le_of_tsum_le two_toReal_pos (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hle : ∀ n, ‖(recordSynthesisLinear e he c) n‖ ^ 2 ≤ ‖c‖ ^ 2 * ‖e n‖ ^ 2 := fun n => by
    change ‖c n • e n‖ ^ 2 ≤ _
    exact norm_smul_record_sq_le e c n
  have hs := he.mul_left (‖c‖ ^ 2)
  calc ∑' n, ‖(recordSynthesisLinear e he c) n‖ ^ 2 ≤ ∑' n, ‖c‖ ^ 2 * ‖e n‖ ^ 2 :=
        (hs.of_nonneg_of_le (fun n => sq_nonneg _) hle).tsum_le_tsum hle hs
    _ = (Real.sqrt (∑' n, ‖e n‖ ^ 2) * ‖c‖) ^ 2 := by
        rw [tsum_mul_left, mul_pow, Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)]
        ring

/-- The record synthesis `c ↦ (c_n e_n)_n`. -/
def recordSynthesis : HistoryScalar →L[ℂ] HistoryL2 E :=
  (recordSynthesisLinear e he).mkContinuous (Real.sqrt (∑' n, ‖e n‖ ^ 2))
    (norm_recordSynthesisLinear_le e he)

omit [CompleteSpace E] in
@[simp] theorem recordSynthesis_apply (c : HistoryScalar) (n : ℕ) :
    recordSynthesis e he c n = c n • e n := rfl

omit [CompleteSpace E] in
theorem recordSynthesis_single (k : ℕ) (a : ℂ) :
    recordSynthesis e he (lp.single 2 k a) = lp.single 2 k (a • e k) := by
  ext n
  rw [recordSynthesis_apply, lp.single_apply, lp.single_apply]
  by_cases h : n = k
  · subst h
    simp
  · simp [h]

/-- The record readout `f ↦ (⟪e_n, f_n⟫)_n`. -/
def recordReadout : HistoryL2 E →L[ℂ] HistoryScalar := adjoint (recordSynthesis e he)

theorem recordReadout_apply (f : HistoryL2 E) (n : ℕ) :
    recordReadout e he f n = ⟪e n, f n⟫_ℂ := by
  have h := adjoint_inner_right (recordSynthesis e he) (lp.single 2 n (1 : ℂ)) f
  rw [lp.inner_single_left, recordSynthesis_single, one_smul, lp.inner_single_left] at h
  rw [recordReadout, ← h]
  simp

theorem adjoint_recordReadout : adjoint (recordReadout e he) = recordSynthesis e he := by
  rw [recordReadout, adjoint_adjoint]

/-- **The dephased record** `𝖳 = ⊕ₙ |e_n⟩⟨e_n|`. -/
def recordOp : HistoryL2 E →L[ℂ] HistoryL2 E := recordSynthesis e he ∘L recordReadout e he

theorem recordOp_apply (f : HistoryL2 E) (n : ℕ) :
    recordOp e he f n = ⟪e n, f n⟫_ℂ • e n := by
  rw [recordOp, comp_apply, recordSynthesis_apply, recordReadout_apply]

theorem recordOp_eq_adjoint_comp :
    recordOp e he = adjoint (recordReadout e he) ∘L recordReadout e he := by
  rw [adjoint_recordReadout, recordOp]

theorem recordOp_congr {e' : ℕ → E} (he' : Summable fun n => ‖e' n‖ ^ 2) (h : e = e') :
    recordOp e he = recordOp e' he' := by
  subst h
  rfl

/-- **Matrix entries.**  `⟪δ_n ⊗ x, 𝖳 (δ_k ⊗ y)⟫ = 1_{n=k} ⟪x, e_n⟫ ⟪e_n, y⟫`. -/
theorem inner_single_recordOp_single (n k : ℕ) (x y : E) :
    ⟪(lp.single 2 n x : HistoryL2 E), recordOp e he (lp.single 2 k y)⟫_ℂ
      = if n = k then ⟪x, e n⟫_ℂ * ⟪e n, y⟫_ℂ else 0 := by
  rw [lp.inner_single_left, recordOp_apply, lp.single_apply]
  by_cases h : n = k
  · subst h
    simp [inner_smul_right, mul_comm]
  · simp [h]

omit [CompleteSpace E] in
theorem norm_recordSynthesis_basis_sq (n : ℕ) :
    ‖recordSynthesis e he (HilbertSchmidt.lpBasis ℕ n)‖ ^ 2 = ‖e n‖ ^ 2 := by
  rw [HilbertSchmidt.lpBasis_apply, recordSynthesis_single, one_smul,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem isHilbertSchmidt_recordSynthesis : IsHilbertSchmidt (recordSynthesis e he) := by
  refine isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ℕ) ?_
  simp_rw [norm_recordSynthesis_basis_sq]
  exact he

theorem hsNormSq_recordSynthesis :
    ContinuousLinearMap.hsNormSq (recordSynthesis e he) = ∑' n, ‖e n‖ ^ 2 := by
  rw [hsNormSq_eq (isHilbertSchmidt_recordSynthesis e he) (HilbertSchmidt.lpBasis ℕ)]
  simp_rw [norm_recordSynthesis_basis_sq]

theorem isHilbertSchmidt_recordReadout : IsHilbertSchmidt (recordReadout e he) :=
  (isHilbertSchmidt_recordSynthesis e he).adjoint

theorem hsNormSq_recordReadout :
    ContinuousLinearMap.hsNormSq (recordReadout e he) = ∑' n, ‖e n‖ ^ 2 := by
  rw [recordReadout, (isHilbertSchmidt_recordSynthesis e he).hsNormSq_adjoint,
    hsNormSq_recordSynthesis]

/-- **Nuclearity.**  `𝖳 ≥ 0`, `𝖳 ∈ S₁`, `tr 𝖳 = ∑ ‖e_n‖²`. -/
theorem recordOp_traceClass :
    (recordOp e he).IsPositive ∧ MemSchattenClass 1 (recordOp e he) ∧
      opTrace (recordOp e he) = ((∑' n, ‖e n‖ ^ 2 : ℝ) : ℂ) := by
  have hV := isHilbertSchmidt_recordReadout e he
  rw [recordOp_eq_adjoint_comp]
  refine ⟨isPositive_adjoint_comp_self _, memSchattenClass_one_comp hV.adjoint hV, ?_⟩
  rw [opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq', hsNormSq_recordReadout]

theorem adjoint_recordOp : adjoint (recordOp e he) = recordOp e he :=
  (recordOp_traceClass e he).1.isSelfAdjoint.adjoint_eq

/-- `‖𝖳‖₁ = ∑ ‖e_n‖²`. -/
theorem traceNorm_recordOp : traceNorm (HistoryL2 E) (recordOp e he) = ∑' n, ‖e n‖ ^ 2 := by
  obtain ⟨hpos, hS1, htr⟩ := recordOp_traceClass e he
  rw [traceNorm_eq_re_opTrace_of_isPositive hS1 hpos, htr, Complex.ofReal_re]

/-! ### Tails -/

omit [CompleteSpace E] in
include he in
theorem summable_historyTail_record (N : ℕ) :
    Summable fun n => ‖historyTail N n • e n‖ ^ 2 :=
  he.of_nonneg_of_le (fun _ => sq_nonneg _) fun n => by
    rw [norm_smul]
    unfold historyTail
    split_ifs <;> simp

theorem historyTailProjection_comp_recordOp (N : ℕ) :
    historyTailProjection N ∘L recordOp e he
      = recordOp (fun n => historyTail N n • e n) (summable_historyTail_record e he N) := by
  ext f n
  rw [comp_apply, historyTailProjection, historyMap_apply, recordOp_apply, recordOp_apply,
    id_apply]
  unfold historyTail
  split_ifs <;> simp

omit [CompleteSpace E] in
include he in
theorem tsum_historyTail_record (N : ℕ) :
    ∑' n, ‖historyTail N n • e n‖ ^ 2 = ∑' k, ‖e (k + N)‖ ^ 2 := by
  rw [← (summable_historyTail_record e he N).sum_add_tsum_nat_add N]
  have hz : ∑ i ∈ Finset.range N, ‖historyTail N i • e i‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [historyTail, if_neg (not_le.mpr (Finset.mem_range.mp hi))]
      simp
  rw [hz, zero_add]
  refine tsum_congr fun k => ?_
  rw [historyTail, if_pos (Nat.le_add_left N k), one_smul]

/-- **Tail traces.**  `tr((Q_N ⊗ 1) 𝖳) = ∑_{k ≥ N} ‖e_k‖²`. -/
theorem opTrace_historyTail_recordOp (N : ℕ) :
    opTrace (historyTailProjection N ∘L recordOp e he) = ((∑' k, ‖e (k + N)‖ ^ 2 : ℝ) : ℂ) := by
  rw [historyTailProjection_comp_recordOp, (recordOp_traceClass _ _).2.2,
    tsum_historyTail_record e he N]

/-! ### Operator norm -/

theorem norm_recordOp_apply_le {k : ℕ} (hk : ∀ n, ‖e n‖ ≤ ‖e k‖) (f : HistoryL2 E) :
    ‖recordOp e he f‖ ≤ ‖e k‖ ^ 2 * ‖f‖ := by
  refine lp.norm_le_of_tsum_le two_toReal_pos (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hle : ∀ n, ‖recordOp e he f n‖ ^ 2 ≤ (‖e k‖ ^ 2) ^ 2 * ‖f n‖ ^ 2 := fun n => by
    rw [recordOp_apply, norm_smul, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc ‖⟪e n, f n⟫_ℂ‖ * ‖e n‖ ≤ (‖e n‖ * ‖f n‖) * ‖e n‖ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖e n‖ ^ 2 * ‖f n‖ := by ring
      _ ≤ ‖e k‖ ^ 2 * ‖f n‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hk n) 2) (norm_nonneg _)
  have hs := (summable_norm_sq_historyL2 f).mul_left ((‖e k‖ ^ 2) ^ 2)
  calc ∑' n, ‖recordOp e he f n‖ ^ 2 ≤ ∑' n, (‖e k‖ ^ 2) ^ 2 * ‖f n‖ ^ 2 :=
        (hs.of_nonneg_of_le (fun n => sq_nonneg _) hle).tsum_le_tsum hle hs
    _ = (‖e k‖ ^ 2 * ‖f‖) ^ 2 := by rw [tsum_mul_left, ← norm_sq_historyL2]; ring

/-- **Operator norm.**  If `‖e_k‖` is maximal, `‖𝖳‖ = ‖e_k‖²`. -/
theorem norm_recordOp {k : ℕ} (hk : ∀ n, ‖e n‖ ≤ ‖e k‖) : ‖recordOp e he‖ = ‖e k‖ ^ 2 := by
  refine le_antisymm (opNorm_le_bound _ (by positivity) (norm_recordOp_apply_le e he hk)) ?_
  have h1 : recordOp e he (lp.single 2 k (e k)) = lp.single 2 k (⟪e k, e k⟫_ℂ • e k) := by
    ext n
    rw [recordOp_apply, lp.single_apply, lp.single_apply]
    by_cases h : n = k
    · subst h
      simp
    · simp [h]
  have h2 := le_opNorm (recordOp e he) (lp.single 2 k (e k))
  rw [h1, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_smul, inner_self_eq_norm_sq_to_K,
    norm_pow, RCLike.norm_ofReal, abs_norm] at h2
  rcases (norm_nonneg (e k)).eq_or_lt with h0 | h0
  · rw [← h0]
    simp
  · exact le_of_mul_le_mul_right h2 h0

/-! ### Transport and phases -/

/-- **Transport.**  `(1 ⊗ W) 𝖳_e (1 ⊗ W)* = 𝖳_{We}`. -/
theorem recordOp_conj_historyMap (W : E →L[ℂ] F) (hW : Summable fun n => ‖W (e n)‖ ^ 2) :
    historyMap (fun _ => 1) (fun _ => norm_one.le) W ∘L recordOp e he ∘L
        adjoint (historyMap (fun _ => 1) (fun _ => norm_one.le) W)
      = recordOp (fun n => W (e n)) hW := by
  ext f n
  rw [comp_apply, comp_apply, historyMap_apply, recordOp_apply, recordOp_apply, adjoint_historyMap,
    historyMap_apply, map_smul, one_smul, map_one, one_smul, adjoint_inner_right]

/-- **Phase blindness.**  Unimodular grade phases leave the record unchanged. -/
theorem recordOp_phase {σ : ℕ → ℂ} (hσ : ∀ n, ‖σ n‖ = 1)
    (hσe : Summable fun n => ‖σ n • e n‖ ^ 2) :
    recordOp (fun n => σ n • e n) hσe = recordOp e he := by
  ext f n
  rw [recordOp_apply, recordOp_apply, inner_smul_left, smul_smul]
  congr 1
  rw [mul_comm, ← mul_assoc, RCLike.mul_conj, hσ n]
  simp

/-! ### Trace-norm continuity -/

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem summable_norm_sub_sq {a b : ℕ → E} (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2) : Summable fun n => ‖(a - b) n‖ ^ 2 :=
  ((ha.mul_left 2).add (hb.mul_left 2)).of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
    rw [Pi.sub_apply]
    have h := mul_self_le_mul_self (norm_nonneg _) (norm_sub_le (a n) (b n))
    nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]

theorem recordReadout_sub {a b : ℕ → E} (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2) :
    recordReadout a ha - recordReadout b hb
      = recordReadout (a - b) (summable_norm_sub_sq ha hb) := by
  have hs : recordSynthesis a ha - recordSynthesis b hb
      = recordSynthesis (a - b) (summable_norm_sub_sq ha hb) := by
    ext c n
    simp [smul_sub]
  rw [recordReadout, recordReadout, recordReadout, ← map_sub, hs]

/-- **Trace-norm continuity.**  `‖𝖳_a - 𝖳_b‖₁ ≤ (‖a‖ + ‖b‖) ‖a - b‖` in `ℓ²(ℕ; E)`. -/
theorem traceNorm_recordOp_sub_le {a b : ℕ → E} (ha : Summable fun n => ‖a n‖ ^ 2)
    (hb : Summable fun n => ‖b n‖ ^ 2) :
    traceNorm (HistoryL2 E) (recordOp a ha - recordOp b hb)
      ≤ (Real.sqrt (∑' n, ‖a n‖ ^ 2) + Real.sqrt (∑' n, ‖b n‖ ^ 2)) *
          Real.sqrt (∑' n, ‖a n - b n‖ ^ 2) := by
  have h := traceNorm_adjoint_comp_self_sub_le (isHilbertSchmidt_recordReadout a ha)
    (isHilbertSchmidt_recordReadout b hb)
  rw [← recordOp_eq_adjoint_comp, ← recordOp_eq_adjoint_comp, recordReadout_sub ha hb] at h
  simp only [ContinuousLinearMap.hsNorm, hsNormSq_recordReadout, Pi.sub_apply] at h
  exact h

end Record

/-! ## History dephasing -/

section Dephasing

/-- The grade projection `P_n ⊗ 1`. -/
def historyGrade (n : ℕ) : HistoryL2 E →L[ℂ] HistoryL2 E :=
  historyMap (fun k => if k = n then 1 else 0)
    (fun k => by split_ifs <;> simp) (ContinuousLinearMap.id ℂ E)

omit [CompleteSpace E] in
theorem historyGrade_apply (n : ℕ) (f : HistoryL2 E) :
    historyGrade n f = lp.single 2 n (f n) := by
  ext k
  rw [historyGrade, historyMap_apply, id_apply, lp.single_apply]
  by_cases h : k = n
  · subst h
    simp
  · simp [h]

/-- The rank-one lift `|ψ⟩⟨ψ|`. -/
def historyRankOne (ψ : HistoryL2 E) : HistoryL2 E →L[ℂ] HistoryL2 E :=
  (innerSL ℂ ψ).smulRight ψ

omit [CompleteSpace E] in
theorem historyRankOne_apply (ψ f : HistoryL2 E) : historyRankOne ψ f = ⟪ψ, f⟫_ℂ • ψ := rfl

omit [CompleteSpace E] in
/-- **Cross-grade blocks.**  `⟪δ_n ⊗ x, |ψ⟩⟨ψ| (δ_k ⊗ y)⟫ = ⟪x, ψ_n⟫ ⟪ψ_k, y⟫`. -/
theorem inner_single_historyRankOne_single (ψ : HistoryL2 E) (n k : ℕ) (x y : E) :
    ⟪(lp.single 2 n x : HistoryL2 E), historyRankOne ψ (lp.single 2 k y)⟫_ℂ
      = ⟪x, ψ n⟫_ℂ * ⟪ψ k, y⟫_ℂ := by
  rw [historyRankOne_apply, inner_smul_right, lp.inner_single_right, lp.inner_single_left,
    mul_comm]

omit [CompleteSpace E] in
theorem summable_truncate (ψ : HistoryL2 E) (N : ℕ) :
    Summable fun n => ‖(if n < N then ψ n else 0 : E)‖ ^ 2 :=
  (summable_norm_sq_historyL2 ψ).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => by
    split_ifs <;> simp

/-- **Finite dephasing.**  `∑_{n < N} P_n |ψ⟩⟨ψ| P_n` is the record of the truncated history. -/
theorem sum_historyGrade_rankOne (ψ : HistoryL2 E) (N : ℕ) :
    ∑ n ∈ Finset.range N, historyGrade n ∘L historyRankOne ψ ∘L historyGrade n
      = recordOp (fun n => if n < N then ψ n else 0) (summable_truncate ψ N) := by
  induction N with
  | zero =>
    ext f n
    simp [recordOp_apply]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ext f k
    rw [add_apply, lp.coeFn_add, Pi.add_apply, comp_apply, comp_apply, historyGrade_apply,
      historyGrade_apply, historyRankOne_apply, lp.inner_single_right, recordOp_apply,
      recordOp_apply, lp.single_apply]
    rcases lt_trichotomy k N with hk | hk | hk
    · have hk' : k < N + 1 := by omega
      simp [hk, hk', hk.ne]
    · subst hk
      simp
    · have h1 : ¬k < N := by omega
      have h2 : ¬k < N + 1 := by omega
      simp [h1, h2, hk.ne']

/-- The dephased record of a history vector, `D_hist(|ψ⟩⟨ψ|) = ⊕ₙ |ψ_n⟩⟨ψ_n|`. -/
def historyDephased (ψ : HistoryL2 E) : HistoryL2 E →L[ℂ] HistoryL2 E :=
  recordOp (fun n => ψ n) (summable_norm_sq_historyL2 ψ)

omit [CompleteSpace E] in
theorem summable_truncate_tail (ψ : HistoryL2 E) (N : ℕ) :
    Summable fun n => ‖(if n < N then 0 else ψ n : E)‖ ^ 2 :=
  (summable_norm_sq_historyL2 ψ).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => by
    split_ifs <;> simp

/-- **Dephasing as a trace-norm limit.**  `∑_{n < N} P_n |ψ⟩⟨ψ| P_n → D_hist(|ψ⟩⟨ψ|)` in `S₁`. -/
theorem tendsto_traceNorm_historyDephased_sub (ψ : HistoryL2 E) :
    Tendsto (fun N => traceNorm (HistoryL2 E) (historyDephased ψ -
      ∑ n ∈ Finset.range N, historyGrade n ∘L historyRankOne ψ ∘L historyGrade n))
      atTop (𝓝 0) := by
  have hdiff : ∀ N, historyDephased ψ -
      ∑ n ∈ Finset.range N, historyGrade n ∘L historyRankOne ψ ∘L historyGrade n
        = recordOp (fun n => if n < N then 0 else ψ n) (summable_truncate_tail ψ N) := by
    intro N
    rw [sum_historyGrade_rankOne]
    ext f k
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, historyDephased, recordOp_apply, recordOp_apply,
      recordOp_apply]
    split_ifs <;> simp
  have htail : ∀ N, ∑' n, ‖(if n < N then 0 else ψ n : E)‖ ^ 2 = ∑' k, ‖ψ (k + N)‖ ^ 2 := by
    intro N
    have h := tsum_historyTail_record (fun n => ψ n) (summable_norm_sq_historyL2 ψ) N
    rw [← h]
    refine tsum_congr fun n => ?_
    unfold historyTail
    by_cases hn : n < N
    · rw [if_pos hn, if_neg (not_le.mpr hn)]
      simp
    · rw [if_neg hn, if_pos (not_lt.mp hn), one_smul]
  simp_rw [hdiff, traceNorm_recordOp, htail]
  exact tendsto_sum_nat_add fun k => ‖ψ k‖ ^ 2

end Dephasing

/-! ## Stable colligations -/

section Colligation

variable {S E₀ : E →L[ℂ] E}

theorem colligation_apply
    (hcol : adjoint S ∘L S + adjoint E₀ ∘L E₀ = ContinuousLinearMap.id ℂ E) (x : E) :
    adjoint S (S x) + adjoint E₀ (E₀ x) = x := by
  have h := congrArg (fun A : E →L[ℂ] E => A x) hcol
  simpa using h

theorem norm_sq_add_norm_sq_of_colligation
    (hcol : adjoint S ∘L S + adjoint E₀ ∘L E₀ = ContinuousLinearMap.id ℂ E) (x : E) :
    ‖S x‖ ^ 2 + ‖E₀ x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := congrArg (fun y => ⟪x, y⟫_ℂ) (colligation_apply hcol x)
  simp only [inner_add_right, adjoint_inner_right] at h
  have h2 := congrArg RCLike.re h
  rw [map_add, inner_self_eq_norm_sq, inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h2
  exact h2

/-- **(CCRHD.8).**  `∑_{n < N} S*ⁿ E₀* E₀ Sⁿ + S*ᴺ Sᴺ = 1`. -/
theorem colligation_telescope
    (hcol : adjoint S ∘L S + adjoint E₀ ∘L E₀ = ContinuousLinearMap.id ℂ E) (N : ℕ) :
    ∑ n ∈ Finset.range N, adjoint (S ^ n) ∘L adjoint E₀ ∘L E₀ ∘L S ^ n
      + adjoint (S ^ N) ∘L S ^ N = ContinuousLinearMap.id ℂ E := by
  induction N with
  | zero =>
    ext x
    simp [one_def]
  | succ N ih =>
    have hstep : adjoint (S ^ N) ∘L adjoint E₀ ∘L E₀ ∘L S ^ N
        + adjoint (S ^ (N + 1)) ∘L S ^ (N + 1) = adjoint (S ^ N) ∘L S ^ N := by
      ext x
      rw [pow_succ', mul_def, adjoint_comp]
      simp only [add_apply, comp_apply]
      rw [← map_add, add_comm, colligation_apply hcol]
    rw [Finset.sum_range_succ, add_assoc, hstep, ih]

/-- The quadratic telescope `∑_{n < N} ‖E₀ Sⁿ x‖² + ‖Sᴺ x‖² = ‖x‖²`. -/
theorem sum_norm_exit_sq_add
    (hcol : adjoint S ∘L S + adjoint E₀ ∘L E₀ = ContinuousLinearMap.id ℂ E) (x : E) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖E₀ ((S ^ n) x)‖ ^ 2 + ‖(S ^ N) x‖ ^ 2 = ‖x‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ' S N, mul_def, comp_apply]
    have h := norm_sq_add_norm_sq_of_colligation hcol ((S ^ N) x)
    linarith

variable (hcol : adjoint S ∘L S + adjoint E₀ ∘L E₀ = ContinuousLinearMap.id ℂ E)
  (hstab : ∀ x, Tendsto (fun N => (S ^ N) x) atTop (𝓝 0))

include hcol hstab in
/-- **Exit masses.**  `∑ₙ ‖E₀ Sⁿ x‖² = ‖x‖²`. -/
theorem hasSum_norm_exit_sq (x : E) : HasSum (fun n => ‖E₀ ((S ^ n) x)‖ ^ 2) (‖x‖ ^ 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg _)]
  have h : Tendsto (fun N => ‖(S ^ N) x‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((hstab x).norm.pow 2)
  have h2 := (tendsto_const_nhds (x := ‖x‖ ^ 2)).sub h
  rw [sub_zero] at h2
  refine h2.congr fun N => ?_
  have := sum_norm_exit_sq_add hcol x N
  linarith

include hcol hstab in
/-- **Survival tails.**  `∑_{k ≥ n} ‖E₀ Sᵏ x‖² = ‖Sⁿ x‖²`. -/
theorem hasSum_norm_exit_sq_tail (x : E) (n : ℕ) :
    HasSum (fun k => ‖E₀ ((S ^ (k + n)) x)‖ ^ 2) (‖(S ^ n) x‖ ^ 2) := by
  refine (hasSum_norm_exit_sq hcol hstab ((S ^ n) x)).congr_fun fun k => ?_
  rw [pow_add, mul_def, comp_apply]

include hcol hstab in
theorem memℓp_exit (x : E) : Memℓp (fun n => E₀ ((S ^ n) x)) 2 := by
  refine (memℓp_gen_iff two_toReal_pos).mpr ?_
  simpa [Real.rpow_two] using (hasSum_norm_exit_sq hcol hstab x).summable

/-- The observability map as a linear map. -/
def observabilityLinear : E →ₗ[ℂ] HistoryL2 E where
  toFun x := ⟨fun n => E₀ ((S ^ n) x), memℓp_exit hcol hstab x⟩
  map_add' x y := by
    ext n
    simp
  map_smul' c x := by
    ext n
    simp

theorem norm_observabilityLinear (x : E) : ‖observabilityLinear hcol hstab x‖ = ‖x‖ := by
  have h := norm_sq_historyL2 (observabilityLinear hcol hstab x)
  have h2 : ∑' n, ‖(observabilityLinear hcol hstab x) n‖ ^ 2 = ‖x‖ ^ 2 :=
    (hasSum_norm_exit_sq hcol hstab x).tsum_eq
  rw [h2] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **(CCRHD.7).**  The observability map `(O f)_n = E₀ Sⁿ f`. -/
def observability : E →L[ℂ] HistoryL2 E :=
  (observabilityLinear hcol hstab).mkContinuous 1 fun x => by
    rw [norm_observabilityLinear, one_mul]

theorem observability_apply (x : E) (n : ℕ) :
    observability hcol hstab x n = E₀ ((S ^ n) x) := rfl

/-- **Theorem CCRHD-B.**  `O` is an isometry. -/
theorem norm_observability_apply (x : E) : ‖observability hcol hstab x‖ = ‖x‖ :=
  norm_observabilityLinear hcol hstab x

theorem adjoint_observability_comp :
    adjoint (observability hcol hstab) ∘L observability hcol hstab = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_observability_apply hcol hstab)

end Colligation

end GaloisForLFunctions.HTGeometry
