import GaloisForLFunctions.HTGeometry.TwoPolarizationTightFormation
import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import GaloisForLFunctions.HTGeometry.BoundedFredholmStability
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CompactObserverHorizon
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Formation does not commute with the compact quotient

On a Hilbert direct sum `H = ⊕_n H_n` with coordinate projections `S_n` and unit vectors
`e_n ∈ H_n` (rank-one projections `E_n`):

* **Countertheorem 4.1.**  `C_n = S_n - E_n` is a projection with `C_n*C_n - S_n = -E_n` compact, so
  every channel has the Calkin class of `S_n`; the assembled analysis map `x ↦ (C_n x)_n` is bounded
  with `Σ_n ‖C_n x‖² = ‖x‖² - Σ_n |⟨e_n, x_n⟩|²`, yet its kernel is the closed span of the `e_n`,
  infinite-dimensional, and the assembled residual `Σ_n (C_n*C_n - S_n) = -E` is minus a
  noncompact projection with norm and essential norm one.
* **Countertheorem 4.2.**  With `T_n x = ⟨e, x⟩ f_n` (`e ∈ H_0`, `f_n ∈ H_n` unit) and
  `D_n = S_n + T_n`, `D_n*D_n - S_n = T_n + T_n* + E_e` has finite rank, but `D_n e = f_n`, so
  `Σ_n ‖D_n e‖² = ∞` and no bounded analysis operator exists.
* **Theorem 4.3.**  For compact `K ≠ 0` and unitaries `U_n, V_n`, the block diagonal of the compact
  blocks `V_n K U_n*` has norm and essential norm `‖K‖` and is not compact.

The common mechanism is a compact perturbation lower bound: along an orthonormal sequence a compact
operator tends to zero, so `‖T - K‖ ≥ inf_n ‖T g_n‖`.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

/-! ### Rank-one operators and the compact perturbation lower bound -/

section General

variable {X Y Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]

/-- The rank-one operator `x ↦ ⟨a, x⟩ b`. -/
def rankOne (a : X) (b : Y) : X →L[ℂ] Y := (innerSL ℂ a).smulRight b

@[simp] theorem rankOne_apply (a : X) (b : Y) (x : X) : rankOne a b x = ⟪a, x⟫_ℂ • b := rfl

theorem norm_rankOne (a : X) (b : Y) : ‖rankOne a b‖ = ‖a‖ * ‖b‖ := by
  rw [rankOne, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem isCompactOperator_rankOne (a : X) (b : Y) : IsCompactOperator (rankOne a b) := by
  have h := (isCompactOperator_of_finiteDimensional_codomain (innerSL ℂ a)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ b)
  have heq : (rankOne a b : X → Y) =
      ⇑(ContinuousLinearMap.toSpanSingleton ℂ b) ∘ ⇑(innerSL ℂ a) := by
    funext x
    simp [rankOne_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rw [heq]
  exact h

theorem adjoint_rankOne [CompleteSpace X] [CompleteSpace Y] (a : X) (b : Y) :
    ContinuousLinearMap.adjoint (rankOne a b) = rankOne b a := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y x
  simp only [rankOne_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem comp_rankOne (T : Y →L[ℂ] Z) (a : X) (b : Y) : T ∘L rankOne a b = rankOne a (T b) := by
  ext x
  simp

theorem rankOne_comp [CompleteSpace X] [CompleteSpace Y] (a : Y) (b : Z) (T : X →L[ℂ] Y) :
    rankOne a b ∘L T = rankOne (ContinuousLinearMap.adjoint T a) b := by
  ext x
  simp [ContinuousLinearMap.adjoint_inner_left]

theorem rankOne_comp_rankOne (a : X) (b c : Y) (d : Z) :
    rankOne c d ∘L rankOne a b = ⟪c, b⟫_ℂ • rankOne a d := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, rankOne_apply, inner_smul_right, smul_smul,
    smul_apply]
  ring_nf

/-- **Compact perturbation lower bound.**  If `‖T g_n‖ ≥ c` along an orthonormal sequence then
`‖T - K‖ ≥ c` for every compact `K`, since `K g_n → 0`. -/
theorem le_norm_sub_of_orthonormal [CompleteSpace X] [CompleteSpace Y] (T K : X →L[ℂ] Y)
    (hK : IsCompactOperator K) {g : ℕ → X}
    (hg : Orthonormal ℂ g) {c : ℝ} (hc : ∀ n, c ≤ ‖T (g n)‖) : c ≤ ‖T - K‖ := by
  have hK0 := _root_.HTGeometry.ConstraintMotiveRelativity.tendsto_norm_image_orthonormal K hK hg
  have hlim : Tendsto (fun n => c - ‖K (g n)‖) atTop (𝓝 (c - 0)) := tendsto_const_nhds.sub hK0
  rw [sub_zero] at hlim
  refine le_of_tendsto' hlim fun n => ?_
  have h1 := (T - K).le_opNorm (g n)
  rw [hg.1 n, mul_one, sub_apply] at h1
  have h2 := norm_sub_norm_le (T (g n)) (K (g n))
  linarith [hc n]

theorem le_essentialNorm_of_orthonormal [CompleteSpace X] (T : X →L[ℂ] X) {g : ℕ → X}
    (hg : Orthonormal ℂ g)
    {c : ℝ} (hc : ∀ n, c ≤ ‖T (g n)‖) : c ≤ RHTower.essentialNorm T :=
  RHTower.le_essentialNorm T c fun K hK => le_norm_sub_of_orthonormal T K hK hg hc

theorem not_isCompactOperator_of_orthonormal [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℂ] Y) {g : ℕ → X} (hg : Orthonormal ℂ g)
    {c : ℝ} (hc0 : 0 < c) (hc : ∀ n, c ≤ ‖T (g n)‖) : ¬ IsCompactOperator T := fun hT => by
  have h := le_norm_sub_of_orthonormal T T hT hg hc
  rw [sub_self, norm_zero] at h
  linarith

end General

/-! ### Coordinate projections of a Hilbert direct sum -/

section DirectSum

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]

private theorem norm_single_id_le (n i : ℕ) :
    ‖(Pi.single n (ContinuousLinearMap.id ℂ (E n)) : ∀ i, E i →L[ℂ] E i) i‖ ≤ 1 := by
  rcases eq_or_ne i n with rfl | h
  · rw [Pi.single_eq_same]
    exact ContinuousLinearMap.norm_id_le
  · rw [Pi.single_eq_of_ne h, norm_zero]
    exact zero_le_one

/-- The coordinate projection `S_n` of `⊕_k H_k` onto `H_n`. -/
def coordProj (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  blockOperator (Pi.single n (ContinuousLinearMap.id ℂ (E n))) zero_le_one (norm_single_id_le n)

theorem coordProj_apply (n : ℕ) (x : lp E 2) : coordProj n x = lp.single 2 n (x n) := by
  refine lp.ext (funext fun i => ?_)
  rw [coordProj, blockOperator_apply]
  rcases eq_or_ne i n with rfl | h
  · rw [Pi.single_eq_same, lp.single_apply_self]
    rfl
  · rw [Pi.single_eq_of_ne h, lp.single_apply_ne _ _ _ h]
    rfl

theorem coordProj_single (n : ℕ) (v : E n) : coordProj n (lp.single 2 n v) = lp.single 2 n v := by
  rw [coordProj_apply, lp.single_apply_self]

theorem coordProj_single_ne {n m : ℕ} (h : m ≠ n) (v : E m) :
    coordProj n (lp.single 2 m v) = 0 := by
  rw [coordProj_apply, lp.single_apply_ne _ _ _ (Ne.symm h), lp.single_zero]

theorem adjoint_coordProj [∀ n, CompleteSpace (E n)] (n : ℕ) :
    ContinuousLinearMap.adjoint (coordProj (E := E) n) = coordProj n := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [coordProj_apply, coordProj_apply, lp.inner_single_left, lp.inner_single_right]

theorem coordProj_comp_self (n : ℕ) : coordProj (E := E) n ∘L coordProj n = coordProj n := by
  ext1 x
  rw [ContinuousLinearMap.comp_apply, coordProj_apply n x, coordProj_single]

/-- The unit vector `e_n` placed in coordinate `n`. -/
def coordUnit (e : ∀ n, E n) (n : ℕ) : lp E 2 := lp.single 2 n (e n)

theorem orthonormal_coordUnit {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    Orthonormal ℂ (coordUnit e) := by
  refine ⟨fun n => by rw [coordUnit, lp.norm_single (by norm_num), he], fun m n hmn => ?_⟩
  simp only [coordUnit]
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ hmn, inner_zero_right]

theorem coordProj_coordUnit (e : ∀ n, E n) (n : ℕ) : coordProj n (coordUnit e n) = coordUnit e n :=
  coordProj_single n (e n)

/-! ### Countertheorem 4.1 -/

/-- The modified channel `C_n = S_n - E_n`. -/
def calkinChannel (e : ∀ n, E n) (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  coordProj n - rankOne (coordUnit e n) (coordUnit e n)

theorem calkinChannel_apply (e : ∀ n, E n) (n : ℕ) (x : lp E 2) :
    calkinChannel e n x = lp.single 2 n (x n - ⟪e n, x n⟫_ℂ • e n) := by
  rw [calkinChannel, sub_apply, coordProj_apply, rankOne_apply, coordUnit,
    lp.inner_single_left, lp.single_sub, lp.single_smul]

theorem adjoint_calkinChannel [∀ n, CompleteSpace (E n)] (e : ∀ n, E n) (n : ℕ) :
    ContinuousLinearMap.adjoint (calkinChannel e n) = calkinChannel e n := by
  rw [calkinChannel, map_sub, adjoint_coordProj, adjoint_rankOne]

theorem calkinChannel_comp_self [∀ n, CompleteSpace (E n)] {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1)
    (n : ℕ) :
    calkinChannel e n ∘L calkinChannel e n = calkinChannel e n := by
  have hu : ⟪coordUnit e n, coordUnit e n⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (orthonormal_coordUnit he).1 n]
    simp
  rw [calkinChannel, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_sub, coordProj_comp_self, comp_rankOne, rankOne_comp,
    rankOne_comp_rankOne, adjoint_coordProj, coordProj_coordUnit, hu, one_smul]
  abel

/-- **Countertheorem 4.1 (1)**: `C_n = C_n* = C_n²`. -/
theorem isStarProjection_calkinChannel [∀ n, CompleteSpace (E n)] {e : ∀ n, E n}
    (he : ∀ n, ‖e n‖ = 1) (n : ℕ) :
    IsStarProjection (calkinChannel e n) :=
  ⟨calkinChannel_comp_self he n, adjoint_calkinChannel e n⟩

/-- **Countertheorem 4.1 (2)**: `C_n*C_n - S_n = -E_n`, a rank-one operator. -/
theorem calkinChannel_gram_sub [∀ n, CompleteSpace (E n)] {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1)
    (n : ℕ) :
    ContinuousLinearMap.adjoint (calkinChannel e n) ∘L calkinChannel e n - coordProj n =
      -rankOne (coordUnit e n) (coordUnit e n) := by
  rw [adjoint_calkinChannel, calkinChannel_comp_self he, calkinChannel]
  abel

/-- **Countertheorem 4.1 (3)**: every local Gram has the Calkin class of `S_n`. -/
theorem isCompactOperator_calkinChannel_gram_sub [∀ n, CompleteSpace (E n)] {e : ∀ n, E n}
    (he : ∀ n, ‖e n‖ = 1) (n : ℕ) :
    IsCompactOperator (ContinuousLinearMap.adjoint (calkinChannel e n) ∘L calkinChannel e n -
      coordProj n : lp E 2 →L[ℂ] lp E 2) := by
  rw [calkinChannel_gram_sub he]
  exact (isCompactOperator_rankOne _ _).neg

/-- Fibrewise Pythagoras: `‖w - ⟨e, w⟩ e‖² = ‖w‖² - |⟨e, w⟩|²` for a unit vector `e`. -/
theorem norm_sq_sub_inner_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {e : F} (he : ‖e‖ = 1) (w : F) : ‖w - ⟪e, w⟫_ℂ • e‖ ^ 2 = ‖w‖ ^ 2 - ‖⟪e, w⟫_ℂ‖ ^ 2 := by
  have hre : RCLike.re ⟪w, ⟪e, w⟫_ℂ • e⟫_ℂ = ‖⟪e, w⟫_ℂ‖ ^ 2 := by
    rw [inner_smul_right, ← inner_conj_symm w e, RCLike.mul_conj, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
  rw [@norm_sub_sq ℂ, hre, norm_smul, he, mul_one]
  ring

theorem norm_calkinChannel_le {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (n : ℕ) (x : lp E 2) :
    ‖calkinChannel e n x‖ ≤ ‖(x : ∀ i, E i) n‖ := by
  rw [calkinChannel_apply, lp.norm_single (by norm_num)]
  have h := norm_sq_sub_inner_smul (he n) ((x : ∀ i, E i) n)
  have h' : ‖(x : ∀ i, E i) n - ⟪e n, (x : ∀ i, E i) n⟫_ℂ • e n‖ ^ 2 ≤
      ‖(x : ∀ i, E i) n‖ ^ 2 := by
    rw [h]
    linarith [sq_nonneg ‖⟪e n, (x : ∀ i, E i) n⟫_ℂ‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

omit [∀ n, InnerProductSpace ℂ (E n)] in
theorem hasSum_norm_sq_coord (x : lp E 2) :
    HasSum (fun n => ‖(x : ∀ i, E i) n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) x
  simpa using h

theorem summable_norm_sq_calkinChannel {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (x : lp E 2) :
    Summable fun n => ‖calkinChannel e n x‖ ^ 2 := by
  have hs : Summable fun n => ‖(x : ∀ i, E i) n‖ ^ 2 := (hasSum_norm_sq_coord x).summable
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => pow_le_pow_left₀ (norm_nonneg _) (norm_calkinChannel_le he n x) 2) hs

/-- The assembled analysis map `x ↦ (C_n x)_n` (linear part). -/
def calkinAnalysisLin {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2 where
  toFun x := ⟨fun n => calkinChannel e n x, (memℓp_gen_iff (by norm_num)).2 (by
    simpa using summable_norm_sq_calkinChannel he x)⟩
  map_add' x y := lp.ext (funext fun n => map_add _ _ _)
  map_smul' c x := lp.ext (funext fun n => map_smul _ _ _)

/-- **Countertheorem 4.1 (4)**: the assembled analysis map `C x = (C_n x)_n` is bounded. -/
def calkinAnalysis {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    lp E 2 →L[ℂ] lp (fun _ : ℕ => lp E 2) 2 :=
  (calkinAnalysisLin he).mkContinuous 1 fun x => by
    have h : ‖calkinAnalysisLin he x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [norm_sq_lp, ← (hasSum_norm_sq_coord x).tsum_eq]
      exact (summable_norm_sq_calkinChannel he x).tsum_le_tsum
        (fun n => pow_le_pow_left₀ (norm_nonneg _) (norm_calkinChannel_le he n x) 2)
        (hasSum_norm_sq_coord x).summable
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem calkinAnalysis_apply {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (x : lp E 2) (n : ℕ) :
    (calkinAnalysis he x : ℕ → lp E 2) n = calkinChannel e n x := rfl

/-- **`(4.4)`**: `Σ_n ‖C_n x‖² = ‖x‖² - Σ_n |⟨e_n, x_n⟩|²`. -/
theorem hasSum_norm_sq_calkinChannel {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (x : lp E 2) :
    HasSum (fun n => ‖calkinChannel e n x‖ ^ 2)
      (‖x‖ ^ 2 - ∑' n, ‖⟪e n, (x : ∀ i, E i) n⟫_ℂ‖ ^ 2) := by
  have hcoef : Summable fun n => ‖⟪e n, (x : ∀ i, E i) n⟫_ℂ‖ ^ 2 :=
    (hasSum_norm_sq_coord x).summable.of_nonneg_of_le (fun n => by positivity) fun n => by
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖⟪e n, (x : ∀ i, E i) n⟫_ℂ‖ ≤ ‖e n‖ * ‖(x : ∀ i, E i) n‖ := norm_inner_le_norm _ _
        _ = ‖(x : ∀ i, E i) n‖ := by rw [he, one_mul]
  refine ((hasSum_norm_sq_coord x).sub hcoef.hasSum).congr_fun fun n => ?_
  rw [calkinChannel_apply, lp.norm_single (by norm_num), norm_sq_sub_inner_smul (he n)]

theorem calkinChannel_eq_zero_iff (e : ∀ n, E n) (n : ℕ) (x : lp E 2) :
    calkinChannel e n x = 0 ↔ (x : ∀ i, E i) n = ⟪e n, (x : ∀ i, E i) n⟫_ℂ • e n := by
  rw [calkinChannel_apply]
  constructor
  · intro h
    have := congrArg (fun z : lp E 2 => (z : ∀ i, E i) n) h
    simp only [lp.single_apply_self, lp.coeFn_zero, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  · intro h
    rw [← h, sub_self, lp.single_zero]

theorem calkinChannel_coordUnit {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (n m : ℕ) :
    calkinChannel e n (coordUnit e m) = 0 := by
  rw [calkinChannel_eq_zero_iff]
  rcases eq_or_ne m n with rfl | h
  · rw [coordUnit, lp.single_apply_self, inner_self_eq_norm_sq_to_K, he]
    simp
  · rw [coordUnit, lp.single_apply_ne _ _ _ (Ne.symm h), inner_zero_right, zero_smul]

/-- **Countertheorem 4.1 (5), `(4.2)`**: `ker C` is the closed span of the `e_n`. -/
theorem ker_calkinAnalysis {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    LinearMap.ker (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2) =
      (Submodule.span ℂ (Set.range (coordUnit e))).topologicalClosure := by
  have hker : ∀ x : lp E 2, x ∈ LinearMap.ker
      (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2) ↔
        ∀ n, calkinChannel e n x = 0 := fun x => by
    rw [LinearMap.mem_ker]
    constructor
    · intro h n
      have := congrArg (fun z : lp (fun _ : ℕ => lp E 2) 2 => (z : ℕ → lp E 2) n) h
      simpa [calkinAnalysis_apply] using this
    · intro h
      exact lp.ext (funext fun n => h n)
  apply le_antisymm
  · intro x hx
    rw [hker] at hx
    have hsum := lp.hasSum_single (p := 2) (by norm_num) x
    have hx' : (fun n => lp.single 2 n ((x : ∀ i, E i) n)) =
        fun n => ⟪e n, (x : ∀ i, E i) n⟫_ℂ • coordUnit e n := funext fun n => by
      rw [coordUnit, ← lp.single_smul, ← (calkinChannel_eq_zero_iff e n x).1 (hx n)]
    rw [hx'] at hsum
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine mem_closure_of_tendsto hsum (Eventually.of_forall fun t => ?_)
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · refine Submodule.topologicalClosure_minimal _ ?_ ((calkinAnalysis he).isClosed_ker)
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact (hker _).2 fun n => calkinChannel_coordUnit he n m

/-- **Countertheorem 4.1 (5)**: the global kernel is infinite-dimensional. -/
theorem not_finiteDimensional_ker_calkinAnalysis {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    ¬ FiniteDimensional ℂ
      (LinearMap.ker (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2)) := by
  intro hfin
  have hmem : ∀ n, coordUnit e n ∈
      LinearMap.ker (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2) := fun n => by
    rw [ker_calkinAnalysis he]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  have hli : LinearIndependent ℂ fun n => (⟨coordUnit e n, hmem n⟩ :
      LinearMap.ker (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2)) :=
    LinearIndependent.of_comp (Submodule.subtype _) (orthonormal_coordUnit he).linearIndependent
  haveI := hli.finite
  exact not_finite ℕ

/-- The assembled residual projection `E = Σ_n E_n`, blockwise projection onto `ℂ e_n`. -/
def residualProj {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) : lp E 2 →L[ℂ] lp E 2 :=
  blockOperator (fun n => rankOne (e n) (e n)) zero_le_one fun n => by
    rw [norm_rankOne, he, one_mul]

theorem residualProj_apply {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (x : lp E 2) (n : ℕ) :
    (residualProj he x : ∀ i, E i) n = ⟪e n, (x : ∀ i, E i) n⟫_ℂ • e n := rfl

/-- **Countertheorem 4.1 (6), `(4.3)`**: `Σ_n (C_n*C_n - S_n) = -E` strongly. -/
theorem hasSum_calkinChannel_gram_sub [∀ n, CompleteSpace (E n)] {e : ∀ n, E n}
    (he : ∀ n, ‖e n‖ = 1) (x : lp E 2) :
    HasSum (fun n => ((ContinuousLinearMap.adjoint (calkinChannel e n) ∘L calkinChannel e n -
      coordProj n : lp E 2 →L[ℂ] lp E 2) x)) (-residualProj he x) := by
  have h := (lp.hasSum_single (p := 2) (by norm_num) (residualProj he x)).neg
  refine h.congr_fun fun n => ?_
  rw [calkinChannel_gram_sub he, neg_apply, rankOne_apply, coordUnit,
    lp.inner_single_left, ← lp.single_smul, residualProj_apply]

theorem residualProj_coordUnit {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) (n : ℕ) :
    residualProj he (coordUnit e n) = coordUnit e n := by
  refine lp.ext (funext fun i => ?_)
  rw [residualProj_apply]
  rcases eq_or_ne i n with rfl | h
  · rw [coordUnit, lp.single_apply_self, inner_self_eq_norm_sq_to_K, he]
    simp
  · rw [coordUnit, lp.single_apply_ne _ _ _ h, inner_zero_right, zero_smul]

/-- **Countertheorem 4.1 (6)**: `E` is a projection onto `ker C`. -/
theorem residualProj_projects [∀ n, CompleteSpace (E n)] {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    IsStarProjection (residualProj he) ∧
      LinearMap.range (residualProj he : lp E 2 →ₗ[ℂ] lp E 2) =
        LinearMap.ker (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2) := by
  have hcoord : ∀ x : lp E 2, ∀ n, ⟪e n, ⟪e n, (x : ∀ i, E i) n⟫_ℂ • e n⟫_ℂ =
      ⟪e n, (x : ∀ i, E i) n⟫_ℂ := fun x n => by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, he]
    simp
  have hidem : ∀ x, residualProj he (residualProj he x) = residualProj he x := fun x =>
    lp.ext (funext fun n => by rw [residualProj_apply, residualProj_apply, hcoord])
  have hker : ∀ x : lp E 2, x ∈ LinearMap.ker
      (calkinAnalysis he : lp E 2 →ₗ[ℂ] lp (fun _ : ℕ => lp E 2) 2) ↔
        residualProj he x = x := fun x => by
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      refine lp.ext (funext fun n => ?_)
      have hn : calkinChannel e n x = 0 := by
        have := congrArg (fun z : lp (fun _ : ℕ => lp E 2) 2 => (z : ℕ → lp E 2) n) h
        simpa [calkinAnalysis_apply] using this
      rw [residualProj_apply]
      exact ((calkinChannel_eq_zero_iff e n x).1 hn).symm
    · intro h
      refine lp.ext (funext fun n => ?_)
      change calkinChannel e n x = 0
      rw [calkinChannel_eq_zero_iff, ← residualProj_apply he x n, h]
  refine ⟨⟨ContinuousLinearMap.ext hidem, ?_⟩, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    change ⟪residualProj he x, y⟫_ℂ = ⟪x, residualProj he y⟫_ℂ
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun n => ?_
    rw [residualProj_apply, residualProj_apply, inner_smul_left, inner_smul_right,
      inner_conj_symm]
    ring
  · ext x
    rw [LinearMap.mem_range, hker]
    constructor
    · rintro ⟨y, rfl⟩
      exact hidem y
    · intro h
      exact ⟨x, h⟩

/-- **Countertheorem 4.1 (6)**: the assembled residual is noncompact with norm and essential norm
one. -/
theorem residualProj_size [∀ n, CompleteSpace (E n)] {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1) :
    ¬ IsCompactOperator (residualProj he) ∧ ‖residualProj he‖ = 1 ∧
      RHTower.essentialNorm (residualProj he) = 1 := by
  have hu := orthonormal_coordUnit he
  have hc : ∀ n, (1 : ℝ) ≤ ‖residualProj he (coordUnit e n)‖ := fun n => by
    rw [residualProj_coordUnit, hu.1 n]
  have hnorm : ‖residualProj he‖ = 1 := by
    apply le_antisymm
    · exact norm_blockOperator_le _ _ _
    · have h := (residualProj he).le_opNorm (coordUnit e 0)
      rw [residualProj_coordUnit, hu.1 0, mul_one] at h
      exact h
  refine ⟨not_isCompactOperator_of_orthonormal _ hu one_pos hc, hnorm, le_antisymm ?_
    (le_essentialNorm_of_orthonormal _ hu hc)⟩
  have h := RHTower.essentialNorm_le (residualProj he) 0 isCompactOperator_zero
  rwa [sub_zero, hnorm] at h

/-! ### Countertheorem 4.2 -/

/-- The cross-coordinate rank-one term `T_n x = ⟨e, x⟩ f_n` with `e ∈ H_0`, `f_n ∈ H_n`. -/
def crossTerm (e₀ : E 0) (f : ∀ n, E n) (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  rankOne (lp.single 2 0 e₀) (lp.single 2 (n + 1) (f (n + 1)))

/-- The channel `D_n = S_n + T_n` (`n ≥ 1`, indexed as `n + 1`). -/
def besselBreakingChannel (e₀ : E 0) (f : ∀ n, E n) (n : ℕ) : lp E 2 →L[ℂ] lp E 2 :=
  coordProj (n + 1) + crossTerm e₀ f n

/-- **Countertheorem 4.2, proof of `(4.6)`**: `D_n*D_n - S_n = T_n + T_n* + E_e`. -/
theorem besselBreakingChannel_gram_sub [∀ n, CompleteSpace (E n)] (e₀ : E 0) {f : ∀ n, E n}
    (hf : ∀ n, ‖f n‖ = 1) (n : ℕ) :
    ContinuousLinearMap.adjoint (besselBreakingChannel e₀ f n) ∘L besselBreakingChannel e₀ f n -
        coordProj (n + 1) =
      crossTerm e₀ f n + ContinuousLinearMap.adjoint (crossTerm e₀ f n) +
        rankOne (lp.single 2 0 e₀) (lp.single 2 0 e₀) := by
  have hff : ⟪lp.single 2 (n + 1) (f (n + 1)), lp.single 2 (n + 1) (f (n + 1))⟫_ℂ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, lp.norm_single (by norm_num), hf]
    simp
  rw [besselBreakingChannel, map_add, adjoint_coordProj, crossTerm, adjoint_rankOne,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add,
    coordProj_comp_self, comp_rankOne, rankOne_comp, adjoint_coordProj, rankOne_comp_rankOne,
    coordProj_single, hff, one_smul]
  abel

/-- **Countertheorem 4.2, `(4.6)`**: every local Gram is a finite-rank perturbation of `S_n`. -/
theorem isCompactOperator_besselBreakingChannel_gram_sub [∀ n, CompleteSpace (E n)] (e₀ : E 0)
    {f : ∀ n, E n}
    (hf : ∀ n, ‖f n‖ = 1) (n : ℕ) :
    IsCompactOperator (ContinuousLinearMap.adjoint (besselBreakingChannel e₀ f n) ∘L
      besselBreakingChannel e₀ f n - coordProj (n + 1) : lp E 2 →L[ℂ] lp E 2) := by
  rw [besselBreakingChannel_gram_sub e₀ hf, crossTerm, adjoint_rankOne]
  exact ((isCompactOperator_rankOne _ _).add (isCompactOperator_rankOne _ _)).add
    (isCompactOperator_rankOne _ _)

/-- **Countertheorem 4.2, `(4.7)`**: `D_n e = f_n`. -/
theorem besselBreakingChannel_apply_e {e₀ : E 0} (he₀ : ‖e₀‖ = 1) (f : ∀ n, E n) (n : ℕ) :
    besselBreakingChannel e₀ f n (lp.single 2 0 e₀) = lp.single 2 (n + 1) (f (n + 1)) := by
  rw [besselBreakingChannel, add_apply, coordProj_single_ne (by omega),
    crossTerm, rankOne_apply, inner_self_eq_norm_sq_to_K, lp.norm_single (by norm_num), he₀]
  simp

/-- **Countertheorem 4.2, `(4.7)`**: `Σ_n ‖D_n e‖² = ∞`, so no bounded analysis operator
`x ↦ (D_n x)_n` exists. -/
theorem not_bessel_besselBreakingChannel {e₀ : E 0} (he₀ : ‖e₀‖ = 1) {f : ∀ n, E n}
    (hf : ∀ n, ‖f n‖ = 1) :
    ¬ Summable (fun n => ‖besselBreakingChannel e₀ f n (lp.single 2 0 e₀)‖ ^ 2) ∧
      ¬ ∃ A : lp E 2 →L[ℂ] lp (fun _ : ℕ => lp E 2) 2,
        ∀ x n, (A x : ℕ → lp E 2) n = besselBreakingChannel e₀ f n x := by
  have hone : ∀ n, ‖besselBreakingChannel e₀ f n (lp.single 2 0 e₀)‖ ^ 2 = 1 := fun n => by
    rw [besselBreakingChannel_apply_e he₀, lp.norm_single (by norm_num), hf, one_pow]
  have hns : ¬ Summable (fun n => ‖besselBreakingChannel e₀ f n (lp.single 2 0 e₀)‖ ^ 2) := by
    intro hs
    have h0 := hs.tendsto_atTop_zero
    simp_rw [hone] at h0
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h0)
  refine ⟨hns, fun ⟨A, hA⟩ => hns ?_⟩
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp (A (lp.single 2 0 e₀)))
  simpa [hA] using h

end DirectSum

/-! ### Theorem 4.3: diagonal formation of compact residuals -/

section Diagonal

variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]

/-- The conjugated compact block `K_n = V_n K U_n*`. -/
def conjBlock (K : H₀ →L[ℂ] H₀) (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) (n : ℕ) : H₀ →L[ℂ] H₀ :=
  (V n).toContinuousLinearEquiv.toContinuousLinearMap ∘L K ∘L
    (U n).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem conjBlock_apply (K : H₀ →L[ℂ] H₀) (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) (n : ℕ) (v : H₀) :
    conjBlock K U V n v = V n (K ((U n).symm v)) := rfl

theorem norm_conjBlock_le (K : H₀ →L[ℂ] H₀) (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) (n : ℕ) :
    ‖conjBlock K U V n‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
    rw [conjBlock_apply, LinearIsometryEquiv.norm_map]
    calc ‖K ((U n).symm v)‖ ≤ ‖K‖ * ‖(U n).symm v‖ := K.le_opNorm _
      _ = ‖K‖ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]

/-- The diagonal formation `𝐊 (x_n) = (K_n x_n)` on `ℓ²(ℕ; H₀)`. -/
def diagonalFormation (K : H₀ →L[ℂ] H₀) (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) :
    lp (fun _ : ℕ => H₀) 2 →L[ℂ] lp (fun _ : ℕ => H₀) 2 :=
  blockOperator (conjBlock K U V) (norm_nonneg K) (norm_conjBlock_le K U V)

/-- Every block of the diagonal formation is compact. -/
theorem isCompactOperator_conjBlock {K : H₀ →L[ℂ] H₀} (hK : IsCompactOperator K)
    (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) (n : ℕ) : IsCompactOperator (conjBlock K U V n) :=
  (hK.comp_clm _).clm_comp _

theorem orthonormal_single_unitary (U : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) {w : H₀} (hw : ‖w‖ = 1) :
    Orthonormal ℂ fun n => (lp.single 2 n (U n w) : lp (fun _ : ℕ => H₀) 2) := by
  refine ⟨fun n => by rw [lp.norm_single (by norm_num), LinearIsometryEquiv.norm_map, hw],
    fun m n hmn => ?_⟩
  dsimp only
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ hmn, inner_zero_right]

theorem diagonalFormation_single (K : H₀ →L[ℂ] H₀) (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) (n : ℕ) (w : H₀) :
    ‖diagonalFormation K U V (lp.single 2 n (U n w))‖ = ‖K w‖ := by
  rw [diagonalFormation, blockOperator_single, lp.norm_single (by norm_num), conjBlock_apply,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map]

/-- `‖K‖ ≤ ‖𝐊 - C‖` for every compact `C`. -/
theorem norm_le_norm_diagonalFormation_sub [CompleteSpace H₀] (K : H₀ →L[ℂ] H₀)
    (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀)
    (C : lp (fun _ : ℕ => H₀) 2 →L[ℂ] lp (fun _ : ℕ => H₀) 2) (hC : IsCompactOperator C) :
    ‖K‖ ≤ ‖diagonalFormation K U V - C‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : H₀ := ((‖v‖ : ℂ)⁻¹) • v with hw_def
  have hw : ‖w‖ = 1 := by
    rw [hw_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hvpos.le,
      inv_mul_cancel₀ hvpos.ne']
  have h := le_norm_sub_of_orthonormal (diagonalFormation K U V) C hC
    (orthonormal_single_unitary U hw) (c := ‖K w‖) fun n => (diagonalFormation_single K U V n w).ge
  have hKw : ‖K w‖ = ‖v‖⁻¹ * ‖K v‖ := by
    rw [hw_def, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hvpos.le]
  rw [hKw] at h
  calc ‖K v‖ = ‖v‖ * (‖v‖⁻¹ * ‖K v‖) := by field_simp
    _ ≤ ‖v‖ * ‖diagonalFormation K U V - C‖ := mul_le_mul_of_nonneg_left h hvpos.le
    _ = ‖diagonalFormation K U V - C‖ * ‖v‖ := mul_comm _ _

/-- **Theorem 4.3, `(4.9)`**: the diagonal formation of the compact blocks `V_n K U_n*` has
`‖𝐊‖ = ‖𝐊‖_ess = ‖K‖` and is not compact when `K ≠ 0`, although every block is compact. -/
theorem diagonalFormation_essential [CompleteSpace H₀] {K : H₀ →L[ℂ] H₀} (hK : IsCompactOperator K)
    (hK0 : K ≠ 0)
    (U V : ℕ → H₀ ≃ₗᵢ[ℂ] H₀) :
    (∀ n, IsCompactOperator (conjBlock K U V n)) ∧ ‖diagonalFormation K U V‖ = ‖K‖ ∧
      RHTower.essentialNorm (diagonalFormation K U V) = ‖K‖ ∧
      ¬ IsCompactOperator (diagonalFormation K U V) := by
  have hle : ‖diagonalFormation K U V‖ ≤ ‖K‖ := norm_blockOperator_le _ _ _
  have hge := norm_le_norm_diagonalFormation_sub K U V 0 isCompactOperator_zero
  rw [sub_zero] at hge
  have hess : RHTower.essentialNorm (diagonalFormation K U V) = ‖K‖ := by
    apply le_antisymm
    · have h := RHTower.essentialNorm_le (diagonalFormation K U V) 0 isCompactOperator_zero
      rw [sub_zero] at h
      exact h.trans hle
    · exact RHTower.le_essentialNorm _ _ fun C hC => norm_le_norm_diagonalFormation_sub K U V C hC
  refine ⟨isCompactOperator_conjBlock hK U V, le_antisymm hle hge, hess, fun hcpt => ?_⟩
  have h := norm_le_norm_diagonalFormation_sub K U V _ hcpt
  rw [sub_self, norm_zero] at h
  exact hK0 (norm_le_zero_iff.1 h)

end Diagonal

end GaloisForLFunctions.HTGeometry.TightFormation
