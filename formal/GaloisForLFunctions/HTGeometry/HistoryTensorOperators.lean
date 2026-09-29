import GaloisForLFunctions.HTGeometry.SourceStokesNormalizedChildUnit
import GaloisForLFunctions.HTGeometry.KummerPhaseWallBlowup

/-!
# History tensors on `ℓ²(ℕ; E)`

The Hilbert direct sum `ℓ²(ℕ; E)` realizes `ℓ²(ℕ) ⊗ E`.  For a weight `a` with `|a_n| ≤ 1` and a
bounded `B : E → F`, the history tensor `(a ⊗ B) f = (a_n B f_n)_n` is bounded with
`‖a ⊗ B‖ ≤ (sup |a_n|) ‖B‖`, and

* `(a ⊗ B)* = ā ⊗ B*`, `(a ⊗ B)(a' ⊗ B') = aa' ⊗ BB'`;
* the vectors `δ_n ⊗ b_i` form a Hilbert basis for any Hilbert basis `b` of `E`, so
  `‖a ⊗ B‖²_HS = (∑ |a_n|²) ‖B‖²_HS`;
* for `w ≥ 0` summable and Hilbert–Schmidt `S`, `w ⊗ S*S = (√w ⊗ S)*(√w ⊗ S)` is positive and
  Schatten-one with trace `(∑ w_n) ‖S‖²_HS`;
* strong convergence `B_t → 0` of a bounded family passes to `a ⊗ B_t`.
-/

open Filter Topology Set ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The history space `ℓ²(ℕ; E) = ℓ²(ℕ) ⊗ E`. -/
abbrev HistoryL2 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  lp (fun _ : ℕ => E) 2

theorem two_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

omit [CompleteSpace E] in
theorem norm_sq_historyL2 (f : HistoryL2 E) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum two_toReal_pos f
  simpa [Real.rpow_two] using h

omit [CompleteSpace E] in
theorem summable_norm_sq_historyL2 (f : HistoryL2 E) : Summable fun n => ‖f n‖ ^ 2 := by
  have h := (lp.memℓp f).summable two_toReal_pos
  simpa [Real.rpow_two] using h

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_smul_apply_le {a : ℂ} {C : ℝ} (ha : ‖a‖ ≤ C) (B : E →L[ℂ] F) (x : E) :
    ‖a • B x‖ ≤ C * ‖B‖ * ‖x‖ := by
  rw [norm_smul, mul_assoc]
  exact mul_le_mul ha (le_opNorm _ _) (norm_nonneg _) ((norm_nonneg _).trans ha)

omit [CompleteSpace E] [CompleteSpace F] in
theorem memℓp_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) (f : HistoryL2 E) :
    Memℓp (fun n => a n • B (f n)) 2 := by
  refine (memℓp_gen_iff two_toReal_pos).mpr ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine ((summable_norm_sq_historyL2 f).mul_left ((1 * ‖B‖) ^ 2)).of_nonneg_of_le
    (fun n => sq_nonneg _) fun n => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_smul_apply_le (ha n) B (f n)) 2

/-- The history tensor as a linear map. -/
def historyMapLinear (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) :
    HistoryL2 E →ₗ[ℂ] HistoryL2 F where
  toFun f := ⟨fun n => a n • B (f n), memℓp_historyMap a ha B f⟩
  map_add' f g := by
    ext n
    simp [smul_add]
  map_smul' c f := by
    ext n
    simp [smul_comm (a n) c]

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_historyMapLinear_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n, ‖a n‖ ≤ C) (f : HistoryL2 E) :
    ‖historyMapLinear a ha B f‖ ≤ C * ‖B‖ * ‖f‖ := by
  refine lp.norm_le_of_tsum_le two_toReal_pos (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hle : ∀ n, ‖(historyMapLinear a ha B f) n‖ ^ 2 ≤ (C * ‖B‖) ^ 2 * ‖f n‖ ^ 2 := fun n => by
    change ‖a n • B (f n)‖ ^ 2 ≤ _
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_smul_apply_le (hC n) B (f n)) 2
  have hs := (summable_norm_sq_historyL2 f).mul_left ((C * ‖B‖) ^ 2)
  calc ∑' n, ‖(historyMapLinear a ha B f) n‖ ^ 2 ≤ ∑' n, (C * ‖B‖) ^ 2 * ‖f n‖ ^ 2 :=
        (hs.of_nonneg_of_le (fun n => sq_nonneg _) hle).tsum_le_tsum hle hs
    _ = (C * ‖B‖ * ‖f‖) ^ 2 := by rw [tsum_mul_left, ← norm_sq_historyL2]; ring

/-- The history tensor `a ⊗ B`. -/
def historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) :
    HistoryL2 E →L[ℂ] HistoryL2 F :=
  (historyMapLinear a ha B).mkContinuous ‖B‖ fun f => by
    have := norm_historyMapLinear_le a ha B zero_le_one ha f
    rwa [one_mul] at this

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem historyMap_apply (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F)
    (f : HistoryL2 E) (n : ℕ) : historyMap a ha B f n = a n • B (f n) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_historyMap_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ n, ‖a n‖ ≤ C) : ‖historyMap a ha B‖ ≤ C * ‖B‖ :=
  opNorm_le_bound _ (by positivity) (norm_historyMapLinear_le a ha B hC0 hC)

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_congr {a a' : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (ha' : ∀ n, ‖a' n‖ ≤ 1)
    (h : a = a') (B : E →L[ℂ] F) : historyMap a ha B = historyMap a' ha' B := by
  subst h
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_single (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) (k : ℕ) (x : E) :
    historyMap a ha B (lp.single 2 k x) = lp.single 2 k (a k • B x) := by
  ext n
  rw [historyMap_apply, lp.single_apply, lp.single_apply]
  by_cases h : n = k
  · subst h
    simp
  · simp [h]

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_sub (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B B' : E →L[ℂ] F) :
    historyMap a ha (B - B') = historyMap a ha B - historyMap a ha B' := by
  ext f n
  simp [smul_sub]

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_smul (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℂ) (B : E →L[ℂ] F) :
    historyMap a ha (c • B) = c • historyMap a ha B := by
  ext f n
  simp [smul_comm (a n) c]

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_zero (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    historyMap a ha (0 : E →L[ℂ] F) = 0 := by
  ext f n
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_neg (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) :
    historyMap a ha (-B) = -historyMap a ha B := by
  ext f n
  simp

theorem norm_conj_le_one {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) : ‖conj (a n)‖ ≤ 1 := by
  rw [RCLike.norm_conj]
  exact ha n

theorem adjoint_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) :
    adjoint (historyMap a ha B) = historyMap (fun n => conj (a n)) (norm_conj_le_one ha)
      (adjoint B) := by
  refine ((eq_adjoint_iff _ _).mpr fun f g => ?_).symm
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [historyMap_apply, historyMap_apply, inner_smul_left, inner_smul_right, adjoint_inner_left,
    RCLike.conj_conj]

theorem norm_mul_le_one {a a' : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (ha' : ∀ n, ‖a' n‖ ≤ 1) (n : ℕ) :
    ‖a n * a' n‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (ha n) (norm_nonneg _) (ha' n)

omit [CompleteSpace E] [CompleteSpace F] in
theorem historyMap_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : F →L[ℂ] G) (a' : ℕ → ℂ) (ha' : ∀ n, ‖a' n‖ ≤ 1)
    (B' : E →L[ℂ] F) :
    historyMap a ha B ∘L historyMap a' ha' B'
      = historyMap (fun n => a n * a' n) (norm_mul_le_one ha ha') (B ∘L B') := by
  ext f n
  simp [smul_smul]

/-! ## The product Hilbert basis -/

omit [CompleteSpace E] in
theorem inner_single_single (n k : ℕ) (x y : E) :
    ⟪(lp.single 2 n x : HistoryL2 E), lp.single 2 k y⟫_ℂ = if n = k then ⟪x, y⟫_ℂ else 0 := by
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : n = k
  · subst h
    simp
  · simp [h]

omit [CompleteSpace E] in
theorem orthonormal_historySingle {ι : Type*} (b : HilbertBasis ι ℂ E) :
    Orthonormal ℂ fun ni : ℕ × ι => (lp.single 2 ni.1 (b ni.2) : HistoryL2 E) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, i⟩ ⟨k, j⟩
  rw [inner_single_single]
  have hb := orthonormal_iff_ite.mp b.orthonormal i j
  by_cases hnk : n = k
  · subst hnk
    simp only [if_true, hb, Prod.mk.injEq, true_and]
  · simp [hnk]

omit [CompleteSpace E] in
theorem orthogonal_span_historySingle {ι : Type*} (b : HilbertBasis ι ℂ E) :
    (Submodule.span ℂ (Set.range fun ni : ℕ × ι =>
      (lp.single 2 ni.1 (b ni.2) : HistoryL2 E)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have h : ∀ n i, ⟪b i, f n⟫_ℂ = 0 := fun n i => by
    have := (Submodule.mem_orthogonal _ f).mp hf _ (Submodule.subset_span ⟨(n, i), rfl⟩)
    rwa [lp.inner_single_left] at this
  have hfn : ∀ n, f n = 0 := fun n => b.repr.injective (by
    ext i
    rw [HilbertBasis.repr_apply_apply, h, map_zero]
    rfl)
  ext n
  simp [hfn n]

/-- The product Hilbert basis `δ_n ⊗ b_i` of `ℓ²(ℕ; E)`. -/
def historyBasis {ι : Type*} (b : HilbertBasis ι ℂ E) : HilbertBasis (ℕ × ι) ℂ (HistoryL2 E) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_historySingle b) (orthogonal_span_historySingle b)

theorem historyBasis_apply {ι : Type*} (b : HilbertBasis ι ℂ E) (ni : ℕ × ι) :
    historyBasis b ni = lp.single 2 ni.1 (b ni.2) := by
  rw [historyBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-! ## Hilbert–Schmidt and trace laws -/

omit [CompleteSpace F] in
theorem norm_historyMap_basis_sq (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] F) {ι : Type*}
    (b : HilbertBasis ι ℂ E) (ni : ℕ × ι) :
    ‖historyMap a ha B (historyBasis b ni)‖ ^ 2 = ‖a ni.1‖ ^ 2 * ‖B (b ni.2)‖ ^ 2 := by
  rw [historyBasis_apply, historyMap_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_smul, mul_pow]

theorem isHilbertSchmidt_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha2 : Summable fun n => ‖a n‖ ^ 2) {B : E →L[ℂ] F} (hB : IsHilbertSchmidt B) :
    IsHilbertSchmidt (historyMap a ha B) := by
  refine isHilbertSchmidt_of_summable (historyBasis (hsBasis ℂ E)) ?_
  simp_rw [norm_historyMap_basis_sq]
  exact summable_mul_of_summable_norm (f := fun n => ‖a n‖ ^ 2)
    (g := fun i => ‖B (hsBasis ℂ E i)‖ ^ 2) (by simpa using ha2) (by simpa using hB.summable _)

/-- `‖a ⊗ B‖²_HS = (∑ |a_n|²) ‖B‖²_HS`. -/
theorem hsNormSq_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha2 : Summable fun n => ‖a n‖ ^ 2) {B : E →L[ℂ] F} (hB : IsHilbertSchmidt B) :
    ContinuousLinearMap.hsNormSq (historyMap a ha B)
      = (∑' n, ‖a n‖ ^ 2) * ContinuousLinearMap.hsNormSq B := by
  rw [hsNormSq_eq (isHilbertSchmidt_historyMap a ha ha2 hB) (historyBasis (hsBasis ℂ E))]
  simp_rw [norm_historyMap_basis_sq]
  rw [ContinuousLinearMap.hsNormSq, tsum_mul_tsum_of_summable_norm (f := fun n => ‖a n‖ ^ 2)
    (g := fun i => ‖B (hsBasis ℂ E i)‖ ^ 2) (by simpa using ha2) (by simpa using hB.summable _)]

theorem hsNorm_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (ha2 : Summable fun n => ‖a n‖ ^ 2) {B : E →L[ℂ] F} (hB : IsHilbertSchmidt B) :
    ContinuousLinearMap.hsNorm (historyMap a ha B)
      = Real.sqrt (∑' n, ‖a n‖ ^ 2) * ContinuousLinearMap.hsNorm B := by
  rw [ContinuousLinearMap.hsNorm, hsNormSq_historyMap a ha ha2 hB,
    Real.sqrt_mul (tsum_nonneg fun _ => sq_nonneg _), ← ContinuousLinearMap.hsNorm]

/-- Complex weights of a real sequence in `[0, 1]`. -/
theorem norm_ofReal_weight_le_one {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) (n : ℕ) :
    ‖((w n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 n)]
  exact hw1 n

theorem norm_sqrt_ofReal_le_one {w : ℕ → ℝ} (hw1 : ∀ n, w n ≤ 1) (n : ℕ) :
    ‖((Real.sqrt (w n) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (hw1 n)

/-- **Positive factorization.**  `w ⊗ S*S = (√w ⊗ S)*(√w ⊗ S)`. -/
theorem historyMap_adjoint_comp_self {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (S : E →L[ℂ] F) :
    historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1) (adjoint S ∘L S)
      = adjoint (historyMap (fun n => ((Real.sqrt (w n) : ℝ) : ℂ)) (norm_sqrt_ofReal_le_one hw1) S)
        ∘L historyMap (fun n => ((Real.sqrt (w n) : ℝ) : ℂ)) (norm_sqrt_ofReal_le_one hw1) S := by
  rw [adjoint_historyMap, historyMap_comp]
  refine historyMap_congr _ _ (funext fun n => ?_) _
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw0 n)]

theorem summable_norm_sqrt_sq {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hws : Summable w) :
    Summable fun n => ‖((Real.sqrt (w n) : ℝ) : ℂ)‖ ^ 2 := by
  refine hws.congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw0 n)]

theorem tsum_norm_sqrt_sq {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) :
    ∑' n, ‖((Real.sqrt (w n) : ℝ) : ℂ)‖ ^ 2 = ∑' n, w n := by
  refine tsum_congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw0 n)]

/-- `w ⊗ S*S` is positive and Schatten-one with trace `(∑ w_n) ‖S‖²_HS`. -/
theorem historyMap_weight_traceClass {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hws : Summable w) {S : E →L[ℂ] F} (hS : IsHilbertSchmidt S) :
    (historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1)
        (adjoint S ∘L S)).IsPositive ∧
      MemSchattenClass 1
        (historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1)
          (adjoint S ∘L S)) ∧
      opTrace (historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1)
        (adjoint S ∘L S)) = (((∑' n, w n) * ContinuousLinearMap.hsNormSq S : ℝ) : ℂ) := by
  have hV := isHilbertSchmidt_historyMap _ (norm_sqrt_ofReal_le_one hw1)
    (summable_norm_sqrt_sq hw0 hws) hS
  rw [historyMap_adjoint_comp_self hw0 hw1]
  refine ⟨isPositive_adjoint_comp_self _, memSchattenClass_one_comp hV.adjoint hV, ?_⟩
  rw [opTrace_adjoint_comp_self, hsInner_self_eq_ofReal_hsNormSq',
    hsNormSq_historyMap _ _ (summable_norm_sqrt_sq hw0 hws) hS, tsum_norm_sqrt_sq hw0]

/-- **Trace-norm difference.**
`‖w ⊗ (V*V - W*W)‖₁ ≤ (∑ w_n)(‖V‖_HS + ‖W‖_HS) ‖V - W‖_HS`. -/
theorem traceNorm_historyMap_sub_le {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hws : Summable w) {V W : E →L[ℂ] F} (hV : IsHilbertSchmidt V) (hW : IsHilbertSchmidt W) :
    traceNorm (HistoryL2 E)
      (historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1) (adjoint V ∘L V)
        - historyMap (fun n => ((w n : ℝ) : ℂ)) (norm_ofReal_weight_le_one hw0 hw1)
          (adjoint W ∘L W))
      ≤ (∑' n, w n) * ((ContinuousLinearMap.hsNorm V + ContinuousLinearMap.hsNorm W) *
        ContinuousLinearMap.hsNorm (V - W)) := by
  have hs := summable_norm_sqrt_sq hw0 hws
  have h𝒱 := isHilbertSchmidt_historyMap _ (norm_sqrt_ofReal_le_one hw1) hs hV
  have h𝒲 := isHilbertSchmidt_historyMap _ (norm_sqrt_ofReal_le_one hw1) hs hW
  rw [historyMap_adjoint_comp_self hw0 hw1, historyMap_adjoint_comp_self hw0 hw1]
  refine (traceNorm_adjoint_comp_self_sub_le h𝒱 h𝒲).trans (le_of_eq ?_)
  rw [← historyMap_sub, hsNorm_historyMap _ _ hs hV, hsNorm_historyMap _ _ hs hW,
    hsNorm_historyMap _ _ hs (hV.sub hW), tsum_norm_sqrt_sq hw0]
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ ∑' n, w n from tsum_nonneg hw0)
  calc (Real.sqrt (∑' n, w n) * ContinuousLinearMap.hsNorm V
        + Real.sqrt (∑' n, w n) * ContinuousLinearMap.hsNorm W)
        * (Real.sqrt (∑' n, w n) * ContinuousLinearMap.hsNorm (V - W))
      = (Real.sqrt (∑' n, w n) * Real.sqrt (∑' n, w n)) *
          ((ContinuousLinearMap.hsNorm V + ContinuousLinearMap.hsNorm W) *
            ContinuousLinearMap.hsNorm (V - W)) := by ring
    _ = _ := by rw [hsq]

/-! ## Strong convergence -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- A bounded family converging strongly to zero stays so after tensoring with history. -/
theorem tendsto_historyMap_apply {α : Type*} {l : Filter α} (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {B : α → E →L[ℂ] F} {K : ℝ} (hK : ∀ t, ‖B t‖ ≤ K)
    (hB : ∀ x, Tendsto (fun t => B t x) l (𝓝 0)) (f : HistoryL2 E) :
    Tendsto (fun t => historyMap a ha (B t) f) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun t => ‖historyMap a ha (B t) f‖ ^ 2) l (𝓝 0) := by
    simp_rw [norm_sq_historyL2, historyMap_apply]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := l)
      (f := fun t n => ‖a n • B t (f n)‖ ^ 2) (g := fun _ => 0)
      (bound := fun n => K ^ 2 * ‖f n‖ ^ 2) ((summable_norm_sq_historyL2 f).mul_left _)
      (fun n => by
        have h1 := ((hB (f n)).const_smul (a n)).norm.pow 2
        simpa using h1)
      (Eventually.of_forall fun t n => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_smul_apply_le (ha n) (B t) (f n)).trans ?_
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (hK t) (norm_nonneg _))
    simpa using h
  have h := hsq.sqrt
  simp only [Real.sqrt_zero] at h
  exact h.congr fun t => Real.sqrt_sq (norm_nonneg _)

/-! ## Matrix entries -/

omit [CompleteSpace E] in
theorem inner_historyMap_single (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (B : E →L[ℂ] E) (n k : ℕ)
    (x y : E) :
    ⟪(lp.single 2 n x : HistoryL2 E), historyMap a ha B (lp.single 2 k y)⟫_ℂ
      = if n = k then a n * ⟪x, B y⟫_ℂ else 0 := by
  rw [historyMap_single, inner_single_single]
  by_cases h : n = k
  · subst h
    rw [if_pos rfl, if_pos rfl, inner_smul_right]
  · rw [if_neg h, if_neg h]

/-- The history tail weights `1_{k ≥ n}`. -/
def historyTail (n : ℕ) (k : ℕ) : ℂ := if n ≤ k then 1 else 0

theorem norm_historyTail_le (n k : ℕ) : ‖historyTail n k‖ ≤ 1 := by
  unfold historyTail
  split_ifs <;> simp

end GaloisForLFunctions.HTGeometry
