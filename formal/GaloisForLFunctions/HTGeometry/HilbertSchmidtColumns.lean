import GaloisForLFunctions.HTGeometry.UnitaryCompactCommutant
import GaloisForLFunctions.HTGeometry.TranslationFrameOperators
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.GramianInverseForm
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# The column model of Hilbert–Schmidt operators and unitary conjugation

Fix a Hilbert basis `b` of a complex Hilbert space `E`.  A Hilbert–Schmidt operator `T` is
recorded by its columns `(T bⱼ)ⱼ ∈ ℓ²(ι; E)`, with `‖(T bⱼ)ⱼ‖ = ‖T‖_HS`; conversely every
`x ∈ ℓ²(ι; E)` is the column family of the Hilbert–Schmidt operator `y ↦ ∑ⱼ ⟨bⱼ, y⟩ xⱼ`.  So the
Hilbert–Schmidt ideal is the Hilbert space `ℓ²(ι; E)`.

For a unitary `U`, conjugation `α(T) = U* T U` is an isometry of this Hilbert space.  If `U` has no
eigenvectors, the fixed space of `α` is zero (a fixed Hilbert–Schmidt operator is compact and
commutes with `U`), so:

* the Cesàro formation `N⁻¹ ∑_{n<N} αⁿ(T)` tends to `0` in Hilbert–Schmidt norm for every
  Hilbert–Schmidt `T` (von Neumann's mean ergodic theorem);
* the transgression `δ = 1 - α` is injective with dense range;
* if `U` moreover has approximate eigenvectors, `δ` is not bounded below, so its range is not
  closed.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*} (b : HilbertBasis ι ℂ E)

/-! ### Columns -/

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem hasSum_norm_sq_lp' (x : lp (fun _ : ι => E) 2) :
    HasSum (fun j => ‖(x : ι → E) j‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The column family `(T bⱼ)ⱼ` of a Hilbert–Schmidt operator. -/
def hsColumns {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) : lp (fun _ : ι => E) 2 :=
  ⟨fun j => T (b j), memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hT.summable b⟩

@[simp] theorem hsColumns_apply {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) (j : ι) :
    (hsColumns b hT : ι → E) j = T (b j) := rfl

/-- The column norm is the Hilbert–Schmidt norm. -/
theorem norm_hsColumns {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) :
    ‖hsColumns b hT‖ = hsNorm T := by
  have h := (hasSum_norm_sq_lp' (hsColumns b hT)).tsum_eq
  simp only [hsColumns_apply] at h
  rw [hsNorm, hsNormSq_eq hT b, h, Real.sqrt_sq (norm_nonneg _)]

omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem summable_norm_sq_lpVec (x : lp (fun _ : ι => E) 2) :
    Summable fun j => ‖(x : ι → E) j‖ ^ 2 :=
  (hasSum_norm_sq_lp' x).summable

/-- The operator with prescribed columns: `y ↦ ∑ⱼ ⟨bⱼ, y⟩ xⱼ`. -/
def columnOperator (x : lp (fun _ : ι => E) 2) : E →L[ℂ] E :=
  ContinuousLinearMap.adjoint
      (besselAnalysis (fun j => (x : ι → E) j)
        (isBesselFamily_of_summable_sq (summable_norm_sq_lpVec x))) ∘L
    b.repr.toLinearIsometry.toContinuousLinearMap

theorem columnOperator_basis [DecidableEq ι] (x : lp (fun _ : ι => E) 2) (k : ι) :
    columnOperator b x (b k) = (x : ι → E) k := by
  simp only [columnOperator, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    HilbertBasis.repr_self, besselSynthesis_single, one_smul]

theorem isHilbertSchmidt_columnOperator (x : lp (fun _ : ι => E) 2) :
    IsHilbertSchmidt (columnOperator b x) := by
  classical
  refine isHilbertSchmidt_of_summable b ?_
  simp only [columnOperator_basis]
  exact summable_norm_sq_lpVec x

/-- Columns of the column operator: `cols (T_x) = x`. -/
theorem hsColumns_columnOperator (x : lp (fun _ : ι => E) 2) :
    hsColumns b (isHilbertSchmidt_columnOperator b x) = x := by
  classical
  exact lp.ext (funext fun k => columnOperator_basis b x k)

/-- A Hilbert–Schmidt operator is recovered from its columns. -/
theorem columnOperator_hsColumns {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) :
    columnOperator b (hsColumns b hT) = T := by
  classical
  exact ext_hilbertBasis b fun k => columnOperator_basis b _ k

theorem columnOperator_add (x y : lp (fun _ : ι => E) 2) :
    columnOperator b (x + y) = columnOperator b x + columnOperator b y := by
  classical
  refine ext_hilbertBasis b fun k => ?_
  rw [add_apply, columnOperator_basis, columnOperator_basis, columnOperator_basis]
  rfl

theorem columnOperator_smul (c : ℂ) (x : lp (fun _ : ι => E) 2) :
    columnOperator b (c • x) = c • columnOperator b x := by
  classical
  refine ext_hilbertBasis b fun k => ?_
  rw [smul_apply, columnOperator_basis, columnOperator_basis]
  rfl

theorem norm_columnOperator_hs (x : lp (fun _ : ι => E) 2) :
    hsNorm (columnOperator b x) = ‖x‖ := by
  rw [← norm_hsColumns b (isHilbertSchmidt_columnOperator b x), hsColumns_columnOperator]

/-! ### Unitary conjugation -/

/-- The bounded operator underlying a unitary. -/
def unitaryCLM (U : E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E := U.toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] theorem unitaryCLM_apply (U : E ≃ₗᵢ[ℂ] E) (x : E) : unitaryCLM U x = U x := rfl

omit [CompleteSpace E] in
theorem norm_unitaryCLM_le (U : E ≃ₗᵢ[ℂ] E) : ‖unitaryCLM U‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

/-- Unitary conjugation `α(T) = U* T U`. -/
def hsConj (U : E ≃ₗᵢ[ℂ] E) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  unitaryCLM U.symm ∘L T ∘L unitaryCLM U

omit [CompleteSpace E] in
@[simp] theorem hsConj_apply (U : E ≃ₗᵢ[ℂ] E) (T : E →L[ℂ] E) (x : E) :
    hsConj U T x = U.symm (T (U x)) := rfl

theorem isHilbertSchmidt_hsConj {U : E ≃ₗᵢ[ℂ] E} {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (hsConj U T) :=
  (hT.comp_right _).comp_left _

/-- Conjugation by a unitary preserves the Hilbert–Schmidt norm. -/
theorem hsNorm_hsConj (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) :
    hsNorm (hsConj U T) = hsNorm T := by
  have hle : ∀ (V : E ≃ₗᵢ[ℂ] E) {S : E →L[ℂ] E}, IsHilbertSchmidt S →
      hsNorm (hsConj V S) ≤ hsNorm S := by
    intro V S hS
    calc hsNorm (hsConj V S) ≤ ‖unitaryCLM V.symm‖ * hsNorm (S ∘L unitaryCLM V) :=
          (hS.comp_right _).hsNorm_comp_left_le _
      _ ≤ 1 * (hsNorm S * ‖unitaryCLM V‖) :=
          mul_le_mul (norm_unitaryCLM_le _) (hS.hsNorm_comp_right_le _) (hsNorm_nonneg _)
            zero_le_one
      _ ≤ hsNorm S := by
          rw [one_mul]
          exact mul_le_of_le_one_right (hsNorm_nonneg _) (norm_unitaryCLM_le _)
  refine le_antisymm (hle U hT) ?_
  have hback : hsConj U.symm (hsConj U T) = T := by
    ext x
    simp
  calc hsNorm T = hsNorm (hsConj U.symm (hsConj U T)) := by rw [hback]
    _ ≤ hsNorm (hsConj U T) := hle U.symm (isHilbertSchmidt_hsConj hT)

/-- Conjugation on columns, as a linear map of `ℓ²(ι; E)`. -/
def columnConjₗ (U : E ≃ₗᵢ[ℂ] E) : lp (fun _ : ι => E) 2 →ₗ[ℂ] lp (fun _ : ι => E) 2 where
  toFun x := hsColumns b (isHilbertSchmidt_hsConj (U := U) (isHilbertSchmidt_columnOperator b x))
  map_add' x y := lp.ext (funext fun j => by
    simp only [hsColumns_apply, columnOperator_add, hsConj_apply, add_apply, map_add,
      lp.coeFn_add, Pi.add_apply])
  map_smul' c x := lp.ext (funext fun j => by
    simp only [hsColumns_apply, columnOperator_smul, hsConj_apply, smul_apply, map_smul,
      lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply])

/-- Conjugation on columns is an isometry of `ℓ²(ι; E)`. -/
theorem norm_columnConjₗ (U : E ≃ₗᵢ[ℂ] E) (x : lp (fun _ : ι => E) 2) :
    ‖columnConjₗ b U x‖ = ‖x‖ := by
  show ‖hsColumns b (isHilbertSchmidt_hsConj (U := U) (isHilbertSchmidt_columnOperator b x))‖ = ‖x‖
  rw [norm_hsColumns, hsNorm_hsConj U (isHilbertSchmidt_columnOperator b x),
    norm_columnOperator_hs]

/-- Conjugation on columns, as a bounded operator. -/
def columnConj (U : E ≃ₗᵢ[ℂ] E) : lp (fun _ : ι => E) 2 →L[ℂ] lp (fun _ : ι => E) 2 :=
  LinearMap.mkContinuous (columnConjₗ b U) 1 fun x => by rw [norm_columnConjₗ, one_mul]

theorem norm_columnConj_le (U : E ≃ₗᵢ[ℂ] E) : ‖columnConj b U‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `α̃(cols T) = cols (α T)`. -/
theorem columnConj_hsColumns (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) :
    columnConj b U (hsColumns b hT) = hsColumns b (isHilbertSchmidt_hsConj (U := U) hT) := by
  apply lp.ext
  funext j
  show hsConj U (columnOperator b (hsColumns b hT)) (b j) = hsConj U T (b j)
  rw [columnOperator_hsColumns]

theorem isHilbertSchmidt_hsConj_iterate (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E}
    (hT : IsHilbertSchmidt T) (n : ℕ) : IsHilbertSchmidt ((hsConj U)^[n] T) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact isHilbertSchmidt_hsConj ih

theorem columnConj_iterate_hsColumns (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E}
    (hT : IsHilbertSchmidt T) (n : ℕ) :
    (columnConj b U)^[n] (hsColumns b hT) =
      hsColumns b (isHilbertSchmidt_hsConj_iterate U hT n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, columnConj_hsColumns]
      apply lp.ext
      funext j
      simp only [hsColumns_apply, Function.iterate_succ_apply']

/-- The fixed columns of conjugation by a unitary without eigenvectors vanish. -/
theorem eq_zero_of_columnConj_eq {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U)
    {x : lp (fun _ : ι => E) 2} (hx : columnConj b U x = x) : x = 0 := by
  set T := columnOperator b x
  have hfix : hsConj U T = T := by
    have h := congrArg (columnOperator b) hx
    rw [show columnConj b U x =
        hsColumns b (isHilbertSchmidt_hsConj (U := U) (isHilbertSchmidt_columnOperator b x))
      from rfl, columnOperator_hsColumns] at h
    exact h
  have hcomm : ∀ y, T (U y) = U (T y) := by
    intro y
    have := congrArg (fun S : E →L[ℂ] E => U (S y)) hfix
    simpa using this
  have hT0 : T = 0 :=
    eq_zero_of_isCompactOperator_of_comm hU
      (isHilbertSchmidt_columnOperator b x).isCompactOperator hcomm
  rw [← hsColumns_columnOperator b x]
  apply lp.ext
  funext j
  simp [hsColumns_apply, show columnOperator b x = 0 from hT0]

/-! ### The transgression `δ = 1 - α` -/

/-- A contraction without nonzero fixed points has dense `f - 1` range. -/
theorem dense_range_sub_one_of_fixed {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : F →L[ℂ] F) (hf : ‖f‖ ≤ 1) (hfix : ∀ x, f x = x → x = 0) :
    Dense (Set.range (f - 1 : F →L[ℂ] F)) := by
  have horth : (LinearMap.range ((f - 1 : F →L[ℂ] F) : F →ₗ[ℂ] F))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine hfix y (eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ) ?_ ?_)
    · simpa using f.le_of_opNorm_le hf y
    · have : ∀ z, ⟪f z, y⟫_ℂ = ⟪z, y⟫_ℂ := by
        intro z
        have h := (Submodule.mem_orthogonal _ _).mp hy ((f - 1) z) ⟨z, rfl⟩
        rwa [sub_apply, one_apply_eq_self, inner_sub_left, sub_eq_zero] at h
      simp only [this, inner_self_eq_norm_sq_to_K]
      norm_cast
  have hclos := Submodule.orthogonal_orthogonal_eq_closure
    (LinearMap.range ((f - 1 : F →L[ℂ] F) : F →ₗ[ℂ] F))
  rw [horth, Submodule.bot_orthogonal_eq_top] at hclos
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos.symm

/-- **Mean ergodic theorem without fixed points.**  The Cesàro averages of a contraction of a
Hilbert space with no nonzero fixed point tend to zero. -/
theorem tendsto_birkhoffAverage_zero_of_fixed {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (f : F →L[ℂ] F) (hf : ‖f‖ ≤ 1)
    (hfix : ∀ x, f x = x → x = 0) (x : F) :
    Tendsto (fun N => birkhoffAverage ℂ f _root_.id N x) atTop (𝓝 0) := by
  have h := (f : F →ₗ[ℂ] F).tendsto_birkhoffAverage_of_ker_subset_closure
    (f.lipschitz.weaken hf) 0 (fun y => Subtype.ext (hfix y y.2).symm)
    (fun y _ => (dense_range_sub_one_of_fixed f hf hfix) y) x
  simp only [zero_apply, ZeroMemClass.coe_zero] at h
  exact h

/-- **Dense transgression.**  For a unitary without eigenvectors, `δ = 1 - α` on the
Hilbert–Schmidt ideal has dense range. -/
theorem dense_range_columnTransgression {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U) :
    Dense (Set.range (columnConj b U - 1 : lp (fun _ : ι => E) 2 →L[ℂ] lp (fun _ : ι => E) 2)) :=
  dense_range_sub_one_of_fixed _ (norm_columnConj_le b U) fun _ hx =>
    eq_zero_of_columnConj_eq b hU hx

/-! ### Cesàro formation in the Hilbert–Schmidt norm -/

/-- The Cesàro formation `M_N(T) = N⁻¹ ∑_{n<N} αⁿ(T)`. -/
def hsCesaro (U : E ≃ₗᵢ[ℂ] E) (N : ℕ) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  (N : ℂ)⁻¹ • ∑ n ∈ Finset.range N, (hsConj U)^[n] T

theorem isHilbertSchmidt_hsCesaro (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T)
    (N : ℕ) : IsHilbertSchmidt (hsCesaro U N T) := by
  refine IsHilbertSchmidt.smul ?_ _
  induction N with
  | zero => simpa using isHilbertSchmidt_zero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (isHilbertSchmidt_hsConj_iterate U hT N)

theorem hsColumns_hsCesaro (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) (N : ℕ) :
    hsColumns b (isHilbertSchmidt_hsCesaro U hT N) =
      birkhoffAverage ℂ (columnConj b U) _root_.id N (hsColumns b hT) := by
  apply lp.ext
  funext j
  simp only [birkhoffAverage, birkhoffSum, id, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum,
    Finset.sum_apply, hsColumns_apply, hsCesaro, smul_apply, sum_apply,
    columnConj_iterate_hsColumns]

/-- **Hilbert–Schmidt disappearance.**  For a unitary without eigenvectors, the Cesàro formation
of every Hilbert–Schmidt operator tends to zero in Hilbert–Schmidt norm. -/
theorem tendsto_hsNorm_hsCesaro {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U) {T : E →L[ℂ] E}
    (hT : IsHilbertSchmidt T) :
    Tendsto (fun N => hsNorm (hsCesaro U N T)) atTop (𝓝 0) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  have h := (tendsto_birkhoffAverage_zero_of_fixed (columnConj b U) (norm_columnConj_le b U)
    (fun _ hx => eq_zero_of_columnConj_eq b hU hx) (hsColumns b hT)).norm
  rw [norm_zero] at h
  refine h.congr fun N => ?_
  rw [← hsColumns_hsCesaro b U hT N, norm_hsColumns]


/-- Operator reading of density: every Hilbert–Schmidt operator is a Hilbert–Schmidt limit of
transgressions `α(S) - S`. -/
theorem exists_hsNorm_sub_transgression_lt {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U)
    {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : E →L[ℂ] E, IsHilbertSchmidt S ∧ hsNorm (T - (hsConj U S - S)) < ε := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.mp
    ((dense_range_columnTransgression b hU) (hsColumns b hT)) ε hε
  refine ⟨columnOperator b x, isHilbertSchmidt_columnOperator b x, ?_⟩
  have hHS : IsHilbertSchmidt (T - (hsConj U (columnOperator b x) - columnOperator b x)) :=
    hT.sub ((isHilbertSchmidt_hsConj (isHilbertSchmidt_columnOperator b x)).sub
      (isHilbertSchmidt_columnOperator b x))
  have heq : hsColumns b hHS = hsColumns b hT - (columnConj b U - 1) x := by
    classical
    apply lp.ext
    funext j
    show (T - (hsConj U (columnOperator b x) - columnOperator b x)) (b j) =
      T (b j) - (hsConj U (columnOperator b x) (b j) - (x : _ → E) j)
    rw [sub_apply, sub_apply, columnOperator_basis]
  rw [← norm_hsColumns b hHS, heq, ← dist_eq_norm]
  exact hx

/-- **No Hilbert–Schmidt survivor.**  A Hilbert–Schmidt operator fixed by conjugation with a unitary
without eigenvectors vanishes. -/
theorem eq_zero_of_hsConj_eq {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U) {T : E →L[ℂ] E}
    (hT : IsHilbertSchmidt T) (hfix : hsConj U T = T) : T = 0 := by
  refine eq_zero_of_isCompactOperator_of_comm hU hT.isCompactOperator fun y => ?_
  have := congrArg (fun S : E →L[ℂ] E => U (S y)) hfix
  simpa using this

/-! ### Approximate eigenvectors and nonclosed range -/

/-- A unitary has **approximate eigenvectors** when for every `ε > 0` some unit vector `u` and
unimodular `w` satisfy `‖U u - w u‖ ≤ ε`. -/
def HasApproxEigenvectors (U : E ≃ₗᵢ[ℂ] E) : Prop :=
  ∀ ε > 0, ∃ (u : E) (w : ℂ), ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ ‖U u - w • u‖ ≤ ε

theorem hsNorm_rankOne (x y : E) : hsNorm (InnerProductSpace.rankOne ℂ x y) = ‖x‖ * ‖y‖ := by
  rw [hsNorm, hsNormSq_rankOne, ← mul_pow, Real.sqrt_sq (by positivity)]

omit [CompleteSpace E] in
theorem hsConj_rankOne (U : E ≃ₗᵢ[ℂ] E) (u : E) :
    hsConj U (InnerProductSpace.rankOne ℂ u u) =
      InnerProductSpace.rankOne ℂ (U.symm u) (U.symm u) := by
  ext y
  simp only [hsConj_apply, InnerProductSpace.rankOne_apply, map_smul]
  rw [← U.inner_map_map (U.symm u) y, LinearIsometryEquiv.apply_symm_apply]

omit [CompleteSpace E] in
theorem rankOne_smul_unimodular (u : E) {w : ℂ} (hw : ‖w‖ = 1) :
    InnerProductSpace.rankOne ℂ (w • u) (w • u) = InnerProductSpace.rankOne ℂ u u := by
  ext y
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  rw [mul_right_comm, Complex.conj_mul', hw]
  simp

/-- **The transgression is not bounded below.**  If `U` has approximate eigenvectors, no constant
`c > 0` satisfies `c ‖T‖_HS ≤ ‖α(T) - T‖_HS` on the Hilbert–Schmidt operators: rank-one
projections onto approximate eigenvectors are almost fixed. -/
theorem not_exists_hsTransgression_lowerBound {U : E ≃ₗᵢ[ℂ] E} (hU : HasApproxEigenvectors U) :
    ¬ ∃ c > 0, ∀ T : E →L[ℂ] E, IsHilbertSchmidt T → c * hsNorm T ≤ hsNorm (hsConj U T - T) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨u, w, hu, hw, hclose⟩ := hU (c / 4) (by positivity)
  set v := w • U.symm u
  have hv : ‖v‖ = 1 := by rw [norm_smul, hw, LinearIsometryEquiv.norm_map, hu, one_mul]
  have hvu : ‖v - u‖ ≤ c / 4 := by
    have : v - u = U.symm (w • u - U u) := by
      rw [map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [this, LinearIsometryEquiv.norm_map, norm_sub_rev]
    exact hclose
  have hdecomp : hsConj U (InnerProductSpace.rankOne ℂ u u) - InnerProductSpace.rankOne ℂ u u =
      InnerProductSpace.rankOne ℂ (v - u) v + InnerProductSpace.rankOne ℂ u (v - u) := by
    rw [hsConj_rankOne, ← rankOne_smul_unimodular (U.symm u) hw, map_sub, map_sub]
    show InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ u u =
      InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ u v +
        (InnerProductSpace.rankOne ℂ u v - InnerProductSpace.rankOne ℂ u u)
    abel
  have h := hbound _ (isHilbertSchmidt_rankOne u u)
  rw [hsNorm_rankOne, hu, mul_one, mul_one, hdecomp] at h
  have h2 := hsNorm_add_le (isHilbertSchmidt_rankOne (v - u) v) (isHilbertSchmidt_rankOne u (v - u))
  rw [hsNorm_rankOne, hsNorm_rankOne, hv, hu, mul_one, one_mul] at h2
  linarith

/-- **Nonclosed transgression.**  For a unitary without eigenvectors but with approximate
eigenvectors, `δ = 1 - α` on the Hilbert–Schmidt ideal is injective with non-closed range. -/
theorem not_isClosed_range_columnTransgression {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U)
    (hU' : HasApproxEigenvectors U) :
    ¬ IsClosed (Set.range
      (columnConj b U - 1 : lp (fun _ : ι => E) 2 →L[ℂ] lp (fun _ : ι => E) 2)) := by
  intro hcl
  obtain ⟨c, hc, hlow⟩ := (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range _).mpr hcl
  have hker : LinearMap.ker ((columnConj b U - 1 : lp (fun _ : ι => E) 2 →L[ℂ] _) :
      lp (fun _ : ι => E) 2 →ₗ[ℂ] lp (fun _ : ι => E) 2) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    refine eq_zero_of_columnConj_eq b hU ?_
    have : columnConj b U x - x = 0 := hx
    exact sub_eq_zero.mp this
  refine not_exists_hsTransgression_lowerBound hU' ⟨c, hc, fun T hT => ?_⟩
  have h := hlow (hsColumns b hT) (by rw [hker, Submodule.bot_orthogonal_eq_top]; trivial)
  have hHS : IsHilbertSchmidt (hsConj U T - T) := (isHilbertSchmidt_hsConj hT).sub hT
  have heq : (columnConj b U - 1 : lp (fun _ : ι => E) 2 →L[ℂ] _) (hsColumns b hT) =
      hsColumns b hHS := by
    rw [sub_apply, one_apply_eq_self, columnConj_hsColumns]
    rfl
  rwa [heq, norm_hsColumns, norm_hsColumns] at h

end GaloisForLFunctions.HTGeometry
