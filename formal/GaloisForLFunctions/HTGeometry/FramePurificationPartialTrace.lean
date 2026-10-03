import GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis
import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.RHTower.NuclearRankOneTrace

/-!
# Purification of a square-summable frame and partial traces

For a Hilbert space `K` and an index set `ι`, `ℓ²(ι; K)` realizes `ℓ²(ι) ⊗ K`, and the ampliation
`I ⊗ B` acts coordinatewise.  A trace-class operator `R` on `K` is the partial trace of `X` over
`ℓ²(ι)` when `Tr(R B) = Tr(X (I ⊗ B))` for every bounded `B`; such an `R` is unique (test against
rank-one `B`).

A square-summable family `α` has the purification `Ψ = ∑ δ_i ⊗ α_i`, with `‖Ψ‖² = ∑ ‖α_i‖²`, and
its frame operator `∑ |α_i⟩⟨α_i|` is the partial trace of `|Ψ⟩⟨Ψ|`.  For a unit vector `Ψ` and
summable weights `w`, the diagonal history `∑ w_n |δ_n ⊗ Ψ⟩⟨δ_n ⊗ Ψ|` has partial trace
`(∑ w_n) |Ψ⟩⟨Ψ|`.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The ampliation `I ⊗ B` on `ℓ²(ι; K)`. -/
def ampliation (ι : Type*) (B : K →L[ℂ] K) : lp (fun _ : ι => K) 2 →L[ℂ] lp (fun _ : ι => K) 2 :=
  blockOperator (fun _ => B) (norm_nonneg B) (fun _ => le_rfl)

@[simp] theorem ampliation_apply (B : K →L[ℂ] K) (x : lp (fun _ : ι => K) 2) (i : ι) :
    ampliation ι B x i = B (x i) := rfl

/-- Evaluation commutes with a summable series of operators. -/
theorem tsum_clm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ι → E →L[ℂ] E} (hf : Summable f) (x : E) : (∑' i, f i) x = ∑' i, f i x :=
  (ContinuousLinearMap.apply ℂ E x).map_tsum hf

/-- Right composition commutes with a summable series of operators. -/
theorem tsum_clm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ι → E →L[ℂ] E} (hf : Summable f) (C : E →L[ℂ] E) :
    (∑' i, f i) ∘L C = ∑' i, f i ∘L C :=
  ((ContinuousLinearMap.compL ℂ E E E).flip C).map_tsum hf

theorem norm_adjoint_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) : ‖adjoint A‖ = ‖A‖ :=
  ContinuousLinearMap.adjoint.norm_map A

variable [CompleteSpace K]

/-- `R` is the partial trace of `X` over the `ℓ²(ι)` factor. -/
def IsPartialTrace (X : lp (fun _ : ι => K) 2 →L[ℂ] lp (fun _ : ι => K) 2) (R : K →L[ℂ] K) :
    Prop :=
  MemSchattenClass 1 R ∧ ∀ B : K →L[ℂ] K, opTrace (R ∘L B) = opTrace (X ∘L ampliation ι B)

theorem opTrace_comp_rankOne (R : K →L[ℂ] K) (x y : K) :
    opTrace (R ∘L rankOne ℂ x y) = ⟪y, R x⟫_ℂ := by
  rw [comp_rankOne, opTrace_rankOne]

theorem opTrace_rankOne_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (x : E) (A : E →L[ℂ] E) :
    opTrace (rankOne ℂ x x ∘L A) = ⟪x, A x⟫_ℂ := by
  rw [rankOne_comp, opTrace_rankOne, adjoint_inner_left]

/-- The partial trace is unique. -/
theorem IsPartialTrace.unique {X : lp (fun _ : ι => K) 2 →L[ℂ] lp (fun _ : ι => K) 2}
    {R R' : K →L[ℂ] K} (h : IsPartialTrace X R) (h' : IsPartialTrace X R') : R = R' := by
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
  have h1 := h.2 (rankOne ℂ x y)
  have h2 := h'.2 (rankOne ℂ x y)
  rw [opTrace_comp_rankOne] at h1 h2
  rw [h1, ← h2]

/-! ## Frames -/

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem memℓp_frame {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) :
    Memℓp α 2 := by
  refine (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 ?_
  simpa using hα

/-- The purification `Ψ = ∑ δ_i ⊗ α_i ∈ ℓ²(ι; K)`. -/
def framePurification (α : ι → K) (hα : Summable fun i => ‖α i‖ ^ 2) : lp (fun _ : ι => K) 2 :=
  ⟨α, memℓp_frame hα⟩

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
@[simp] theorem framePurification_apply {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) (i : ι) :
    framePurification α hα i = α i := rfl

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem norm_sq_framePurification {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) :
    ‖framePurification α hα‖ ^ 2 = ∑' i, ‖α i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (framePurification α hα)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h

/-- The frame operator `∑ |α_i⟩⟨α_i|`. -/
def frameOperator (α : ι → K) : K →L[ℂ] K := ∑' i, rankOne ℂ (α i) (α i)

omit [CompleteSpace K] in
theorem summable_norm_rankOne_frame {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) :
    Summable fun i => ‖rankOne ℂ (α i) (α i)‖ :=
  hα.congr fun i => by rw [norm_rankOne, sq]

omit [CompleteSpace K] in
theorem hasRankLE_one_rankOne (x y : K) : HasRankLE (rankOne ℂ x y) 1 := by
  have h := hasRankLE_sum_range_rankOne (fun _ : ℕ => x) (fun _ : ℕ => y) 1
  rwa [Finset.sum_range_one] at h

theorem frameOperator_apply {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) (x : K) :
    frameOperator α x = ∑' i, ⟪α i, x⟫_ℂ • α i := by
  rw [frameOperator, tsum_clm_apply (Summable.of_norm (summable_norm_rankOne_frame hα))]
  rfl

theorem frameOperator_memSchattenClass_one {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) :
    MemSchattenClass 1 (frameOperator α) :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm _
    (fun _ => hasRankLE_one_rankOne _ _) (summable_norm_rankOne_frame hα)

/-- The frame operator is the left Gram `W W*` of the synthesis `W`. -/
theorem frameOperator_eq_leftGram [DecidableEq ι] {α : ι → K}
    (hα : Summable fun i => ‖α i‖ ^ 2) :
    frameOperator α = squareSummableSynthesis α hα ∘L adjoint (squareSummableSynthesis α hα) := by
  ext x
  rw [frameOperator_apply hα, comp_apply, squareSummableSynthesis_apply]
  exact tsum_congr fun i => by rw [adjoint_squareSummableSynthesis_apply]

/-- `Tr(F B) = ∑ ⟨α_i, B α_i⟩` for the frame operator `F`. -/
theorem opTrace_frameOperator_comp {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2)
    (B : K →L[ℂ] K) : opTrace (frameOperator α ∘L B) = ∑' i, ⟪α i, B (α i)⟫_ℂ := by
  have hsum : Summable fun i => ‖rankOne ℂ (α i) (adjoint B (α i))‖ := by
    refine (hα.mul_left ‖B‖).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_
    rw [norm_rankOne]
    calc ‖α i‖ * ‖adjoint B (α i)‖ ≤ ‖α i‖ * (‖B‖ * ‖α i‖) := by
          gcongr
          rw [← norm_adjoint_eq B]
          exact le_opNorm _ _
      _ = ‖B‖ * ‖α i‖ ^ 2 := by ring
  have hcomp : frameOperator α ∘L B = ∑' i, rankOne ℂ (α i) (adjoint B (α i)) := by
    rw [frameOperator, tsum_clm_comp (Summable.of_norm (summable_norm_rankOne_frame hα))]
    exact tsum_congr fun _ => rankOne_comp _ _ _
  rw [hcomp, opTrace_tsum_rankOneTerms_of_summable_norm _
    (fun _ => hasRankLE_one_rankOne _ _) hsum]
  exact tsum_congr fun i => by rw [opTrace_rankOne, adjoint_inner_left]

/-- **Purification.**  The frame operator is the partial trace of `|Ψ⟩⟨Ψ|`. -/
theorem frameOperator_isPartialTrace {α : ι → K} (hα : Summable fun i => ‖α i‖ ^ 2) :
    IsPartialTrace (rankOne ℂ (framePurification α hα) (framePurification α hα))
      (frameOperator α) := by
  refine ⟨frameOperator_memSchattenClass_one hα, fun B => ?_⟩
  rw [opTrace_frameOperator_comp hα, opTrace_rankOne_comp, lp.inner_eq_tsum]
  rfl

/-! ## The ray history of a unit vector -/

/-- The history ray `ε_n = δ_n ⊗ Ψ`. -/
def historyRay (Ψ : K) (n : ℕ) : lp (fun _ : ℕ => K) 2 := lp.single 2 n Ψ

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem norm_historyRay (Ψ : K) (n : ℕ) : ‖historyRay Ψ n‖ = ‖Ψ‖ := by
  rw [historyRay, lp.norm_single (E := fun _ : ℕ => K) (by norm_num) n Ψ]

/-- The diagonal history `∑ w_n |ε_n⟩⟨ε_n|`. -/
def rayDiagonalHistory (Ψ : K) (w : ℕ → ℝ) : lp (fun _ : ℕ => K) 2 →L[ℂ] lp (fun _ : ℕ => K) 2 :=
  ∑' n, (w n : ℂ) • rankOne ℂ (historyRay Ψ n) (historyRay Ψ n)

theorem summable_norm_rayDiagonalHistory (Ψ : K) {w : ℕ → ℝ} (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) :
    Summable fun n => ‖(w n : ℂ) • rankOne ℂ (historyRay Ψ n) (historyRay Ψ n)‖ := by
  refine (hw.mul_right (‖Ψ‖ ^ 2)).congr fun n => ?_
  rw [norm_smul, norm_rankOne, norm_historyRay, Complex.norm_real, Real.norm_of_nonneg (hw0 n)]
  ring

omit [CompleteSpace K] in
theorem hasRankLE_smul_rankOne (c : ℂ) (x y : K) : HasRankLE (c • rankOne ℂ x y) 1 :=
  hasRankLE_smul (hasRankLE_one_rankOne x y) c

theorem rayDiagonalHistory_memSchattenClass_one (Ψ : K) {w : ℕ → ℝ} (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) : MemSchattenClass 1 (rayDiagonalHistory Ψ w) :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm _
    (fun _ => hasRankLE_smul_rankOne _ _ _) (summable_norm_rayDiagonalHistory Ψ hw hw0)

theorem opTrace_rayDiagonalHistory (Ψ : K) {w : ℕ → ℝ} (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) :
    opTrace (rayDiagonalHistory Ψ w) = ((∑' n, w n) * ‖Ψ‖ ^ 2 : ℝ) := by
  rw [rayDiagonalHistory, opTrace_tsum_rankOneTerms_of_summable_norm _
    (fun _ => hasRankLE_smul_rankOne _ _ _) (summable_norm_rayDiagonalHistory Ψ hw hw0)]
  simp_rw [opTrace_smul_rankOne_self, norm_historyRay]
  rw [tsum_mul_right, Complex.ofReal_mul, Complex.ofReal_tsum]
  push_cast
  rfl

/-- **Closing the history.**  The partial trace of `∑ w_n |ε_n⟩⟨ε_n|` over `ℓ²(ℕ)` is
`(∑ w_n) |Ψ⟩⟨Ψ|`. -/
theorem rayDiagonalHistory_isPartialTrace (Ψ : K) {w : ℕ → ℝ} (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) :
    IsPartialTrace (rayDiagonalHistory Ψ w) (((∑' n, w n : ℝ) : ℂ) • rankOne ℂ Ψ Ψ) := by
  refine ⟨?_, fun B => ?_⟩
  · simpa using memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
      (fun _ : Unit => ((∑' n, w n : ℝ) : ℂ) • rankOne ℂ Ψ Ψ)
      (fun _ => hasRankLE_smul_rankOne _ _ _) (Summable.of_finite)
  have hsum : Summable fun n =>
      ‖(w n : ℂ) • rankOne ℂ (historyRay Ψ n) (adjoint (ampliation ℕ B) (historyRay Ψ n))‖ := by
    refine (hw.mul_right (‖Ψ‖ * (‖ampliation ℕ B‖ * ‖Ψ‖))).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    rw [norm_smul, norm_rankOne, norm_historyRay, Complex.norm_real, Real.norm_of_nonneg (hw0 n)]
    have hb : ‖adjoint (ampliation ℕ B) (historyRay Ψ n)‖ ≤ ‖ampliation ℕ B‖ * ‖Ψ‖ := by
      calc ‖adjoint (ampliation ℕ B) (historyRay Ψ n)‖
          ≤ ‖adjoint (ampliation ℕ B)‖ * ‖historyRay Ψ n‖ := le_opNorm _ _
        _ = ‖ampliation ℕ B‖ * ‖Ψ‖ := by rw [norm_adjoint_eq, norm_historyRay]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (hw0 n)
  have hcomp : rayDiagonalHistory Ψ w ∘L ampliation ℕ B =
      ∑' n, (w n : ℂ) • rankOne ℂ (historyRay Ψ n) (adjoint (ampliation ℕ B) (historyRay Ψ n)) := by
    rw [rayDiagonalHistory, tsum_clm_comp
      (Summable.of_norm (summable_norm_rayDiagonalHistory Ψ hw hw0))]
    exact tsum_congr fun _ => by rw [smul_comp, rankOne_comp]
  rw [hcomp, opTrace_tsum_rankOneTerms_of_summable_norm _
    (fun _ => hasRankLE_smul_rankOne _ _ _) hsum, smul_comp, opTrace_smul,
    opTrace_rankOne_comp]
  have hterm : ∀ n, opTrace ((w n : ℂ) • rankOne ℂ (historyRay Ψ n)
      (adjoint (ampliation ℕ B) (historyRay Ψ n))) = (w n : ℂ) * ⟪Ψ, B Ψ⟫_ℂ := fun n => by
    rw [opTrace_smul, opTrace_rankOne, adjoint_inner_left, historyRay, lp.inner_single_left,
      ampliation_apply, lp.single_apply_self]
  simp_rw [hterm]
  rw [tsum_mul_right, Complex.ofReal_tsum]

end GaloisForLFunctions.HTGeometry
