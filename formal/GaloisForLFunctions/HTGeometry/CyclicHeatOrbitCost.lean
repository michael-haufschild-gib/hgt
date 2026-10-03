import GaloisForLFunctions.HTGeometry.GramianInverseForm
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenbasis
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.PrimeHodgeReachabilityProperness

/-!
# The endogenous proper cost of a cyclic heat source

For a cyclic heat source (simple spectrum tending to infinity, fully supported marked vector) the
orbit Gramian `G` is positive, compact and injective.  Its eigenvectors form a Hilbert basis
`(f_k)` with eigenvalues `γ_k > 0`, `γ_k ≤ ‖G‖`, `γ_k → 0` (**(OG.12)**).  On this basis:

* `C = G^{-1}` (domain `Ran G`) is self-adjoint and positive, with compact resolvent
  `(C + 1)^{-1} f_k = γ_k/(1 + γ_k) f_k` (**(OG.27)**);
* its form `q_G(x) = Σ_k |⟨f_k, x⟩|²/γ_k ∈ [0, ∞]` (**(OG.13)**) is `‖y‖²` at `x = G^{1/2} y`,
  infinite off `Ran G^{1/2}`, equals `⟨Cx, x⟩` on `Dom C`, is lower semicontinuous and equals the
  conjugate form `sup_y (2 Re⟨y, x⟩ - ⟨y, G y⟩)`;
* every sublevel `{q_G ≤ M}` is compact (**(OG.14)**);
* the reachability map factors as `W = G^{1/2} V` with `V V^* = 1` (**(OG.35b)**), hence
  `Ran W = Ran G^{1/2}` and `q_G(x) = min {‖u‖² : W u = x}` (**(OG.15)–(OG.16)**).

Finally the construction is natural (**(OG.22)**): rescaling `L ↦ aL` gives `G ↦ a^{-1} G`,
`C ↦ a C`, `q_G ↦ a q_G`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-! ## Real basis-diagonal operators are self-adjoint -/

section RealDiag

variable {κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isSelfAdjoint_basisDiag_ofReal (b : HilbertBasis κ ℂ E) (r : κ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hr : ∀ k, ‖((r k : ℝ) : ℂ)‖ ≤ M) : IsSelfAdjoint (basisDiag b (fun k => (r k : ℂ)) hM hr) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← b.tsum_inner_mul_inner, ← b.tsum_inner_mul_inner]
  refine tsum_congr fun k => ?_
  rw [inner_basis_basisDiag, ← inner_conj_symm, inner_basis_basisDiag, map_mul, Complex.conj_ofReal,
    inner_conj_symm, ← inner_conj_symm x (b k)]
  ring

end RealDiag

/-! ## Cyclic heat sources -/

/-- A cyclic heat source: simple spectrum tending to infinity and a fully supported marked
vector. -/
structure CyclicHeatSource (ι : Type*) extends HeatSource ι where
  simple : toHeatSource.Simple
  proper : toHeatSource.Proper
  fullSupport : toHeatSource.FullSupport

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

theorem orbitGramian_injective : Function.Injective c.orbitGramian :=
  c.toHeatSource.orbitGramian_injective c.simple c.proper c.fullSupport

theorem isPositive_orbitGramian : c.orbitGramian.IsPositive := c.orbitGramian_traceClass.1

theorem isSelfAdjoint_orbitGramian : IsSelfAdjoint c.orbitGramian :=
  c.isPositive_orbitGramian.isSelfAdjoint

theorem isCompactOperator_orbitGramian : IsCompactOperator c.orbitGramian :=
  c.orbitGramian_traceClass.2.1.isCompactOperator one_pos

instance factCompact : Fact (IsCompactOperator c.orbitGramian) := ⟨c.isCompactOperator_orbitGramian⟩

theorem isSymmetric_orbitGramian : (c.orbitGramian : ℓ²ι →ₗ[ℂ] ℓ²ι).IsSymmetric :=
  c.isSelfAdjoint_orbitGramian.isSymmetric

/-- **(OG.12)** The eigenvector Hilbert basis of `G`. -/
def orbitEigenbasis : HilbertBasis (EigenIndex c.orbitGramian) ℂ ℓ²ι :=
  eigenHilbertBasis c.isSymmetric_orbitGramian fun v hv =>
    c.orbitGramian_injective (by rw [hv, map_zero])

/-- **(OG.12)** The eigenvalues `γ_k` of `G`. -/
def orbitEigenvalue (k : EigenIndex c.orbitGramian) : ℝ := k.1.1.re

theorem orbitGramian_orbitEigenbasis (k : EigenIndex c.orbitGramian) :
    c.orbitGramian (c.orbitEigenbasis k) = (c.orbitEigenvalue k : ℂ) • c.orbitEigenbasis k := by
  rw [orbitEigenbasis, eigenHilbertBasis_apply, orbitEigenvalue,
    eigenValue_real c.isSymmetric_orbitGramian k, apply_eigenVec]

theorem norm_orbitEigenbasis (k : EigenIndex c.orbitGramian) : ‖c.orbitEigenbasis k‖ = 1 :=
  c.orbitEigenbasis.orthonormal.1 k

/-- **(OG.12)** `γ_k > 0`. -/
theorem orbitEigenvalue_pos (k : EigenIndex c.orbitGramian) : 0 < c.orbitEigenvalue k := by
  have hreal := eigenValue_real c.isSymmetric_orbitGramian k
  have h1 : (⟪c.orbitEigenbasis k, c.orbitGramian (c.orbitEigenbasis k)⟫_ℂ).re =
      c.orbitEigenvalue k := by
    rw [orbitGramian_orbitEigenbasis, inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_orbitEigenbasis]
    simp
  have h0 : 0 ≤ c.orbitEigenvalue k := h1 ▸ c.isPositive_orbitGramian.re_inner_nonneg_right _
  refine lt_of_le_of_ne h0 fun h => k.1.2 ?_
  rw [← hreal, orbitEigenvalue] at *
  rw [← h, Complex.ofReal_zero]

/-- **(OG.12)** `γ_k ≤ ‖G‖`. -/
theorem orbitEigenvalue_le (k : EigenIndex c.orbitGramian) : c.orbitEigenvalue k ≤ ‖c.orbitGramian‖ := by
  have h := c.orbitGramian.le_opNorm (c.orbitEigenbasis k)
  rw [orbitGramian_orbitEigenbasis, norm_smul, norm_orbitEigenbasis, mul_one, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (c.orbitEigenvalue_pos k).le] at h
  exact h

/-- **(OG.12)** For every `ε > 0` only finitely many `γ_k` are at least `ε`. -/
theorem finite_orbitEigenvalue_ge {ε : ℝ} (hε : 0 < ε) : {k | ε ≤ c.orbitEigenvalue k}.Finite := by
  have h := finite_of_orthonormal_eigenvectors_of_le_norm (𝕜' := ℂ) c.isCompactOperator_orbitGramian
    (e := fun k : {k | ε ≤ c.orbitEigenvalue k} => c.orbitEigenbasis k)
    (c.orbitEigenbasis.orthonormal.comp _ Subtype.val_injective)
    (lam := fun k => (c.orbitEigenvalue k : ℂ)) (fun k => c.orbitGramian_orbitEigenbasis k) hε
    (fun k => by
      rw [Complex.norm_real, Real.norm_of_nonneg (c.orbitEigenvalue_pos k).le]
      exact k.2)
  exact Set.toFinite _

/-- **(OG.12)** `γ_k → 0`. -/
theorem tendsto_orbitEigenvalue : Tendsto c.orbitEigenvalue cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  refine (c.finite_orbitEigenvalue_ge hε).subset fun k hk => ?_
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero, not_lt] at hk ⊢
  rwa [abs_of_pos (c.orbitEigenvalue_pos k)] at hk

theorem norm_eigenvalue_le (k : EigenIndex c.orbitGramian) :
    ‖((c.orbitEigenvalue k : ℝ) : ℂ)‖ ≤ ‖c.orbitGramian‖ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (c.orbitEigenvalue_pos k).le]
  exact c.orbitEigenvalue_le k

theorem orbitGramian_eq_basisDiag :
    c.orbitGramian = basisDiag c.orbitEigenbasis (fun k => (c.orbitEigenvalue k : ℂ))
      (norm_nonneg _) c.norm_eigenvalue_le := by
  refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
  rw [basisDiag_basis, orbitGramian_orbitEigenbasis]

theorem inner_orbitEigenbasis_orbitGramian (k : EigenIndex c.orbitGramian) (x : ℓ²ι) :
    ⟪c.orbitEigenbasis k, c.orbitGramian x⟫_ℂ = (c.orbitEigenvalue k : ℂ) * ⟪c.orbitEigenbasis k, x⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, c.isSelfAdjoint_orbitGramian.adjoint_eq,
    orbitGramian_orbitEigenbasis, inner_smul_left, Complex.conj_ofReal]

/-! ## The square root `G^{1/2}` -/

theorem norm_sqrtEigenvalue_le (k : EigenIndex c.orbitGramian) :
    ‖((Real.sqrt (c.orbitEigenvalue k) : ℝ) : ℂ)‖ ≤ Real.sqrt ‖c.orbitGramian‖ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (c.orbitEigenvalue_le k)

/-- The square root `G^{1/2}`, diagonal on the eigenbasis. -/
def orbitRoot : ℓ²ι →L[ℂ] ℓ²ι :=
  basisDiag c.orbitEigenbasis (fun k => (Real.sqrt (c.orbitEigenvalue k) : ℂ)) (Real.sqrt_nonneg _)
    c.norm_sqrtEigenvalue_le

theorem inner_orbitEigenbasis_orbitRoot (k : EigenIndex c.orbitGramian) (x : ℓ²ι) :
    ⟪c.orbitEigenbasis k, c.orbitRoot x⟫_ℂ =
      (Real.sqrt (c.orbitEigenvalue k) : ℂ) * ⟪c.orbitEigenbasis k, x⟫_ℂ :=
  inner_basis_basisDiag _ _ _ _ _ _

theorem orbitRoot_orbitEigenbasis (k : EigenIndex c.orbitGramian) :
    c.orbitRoot (c.orbitEigenbasis k) = (Real.sqrt (c.orbitEigenvalue k) : ℂ) • c.orbitEigenbasis k :=
  basisDiag_basis _ _ _ _ _

theorem isSelfAdjoint_orbitRoot : IsSelfAdjoint c.orbitRoot :=
  isSelfAdjoint_basisDiag_ofReal _ _ _ _

theorem orbitRoot_comp_self : c.orbitRoot ∘L c.orbitRoot = c.orbitGramian := by
  refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
  rw [ContinuousLinearMap.comp_apply, orbitRoot_orbitEigenbasis, map_smul, orbitRoot_orbitEigenbasis,
    smul_smul, orbitGramian_orbitEigenbasis, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (c.orbitEigenvalue_pos k).le]

theorem orbitRoot_injective : Function.Injective c.orbitRoot := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine c.orbitEigenbasis.repr.injective (lp.ext (funext fun k => ?_))
  have h := c.inner_orbitEigenbasis_orbitRoot k x
  rw [hx, inner_zero_right] at h
  have hs : (Real.sqrt (c.orbitEigenvalue k) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (c.orbitEigenvalue_pos k)).ne'
  rw [HilbertBasis.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
  exact (mul_eq_zero.1 h.symm).resolve_left hs

theorem isCompactOperator_orbitRoot : IsCompactOperator c.orbitRoot := by
  refine isCompactOperator_basisDiag _ _ _ _ ?_
  have h := (Real.continuous_sqrt.tendsto 0).comp c.tendsto_orbitEigenvalue
  rw [Real.sqrt_zero] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

theorem norm_orbitRoot_sq (y : ℓ²ι) : ‖c.orbitRoot y‖ ^ 2 = (⟪y, c.orbitGramian y⟫_ℂ).re := by
  have h : ⟪y, c.orbitRoot (c.orbitRoot y)⟫_ℂ = ⟪c.orbitRoot y, c.orbitRoot y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, c.isSelfAdjoint_orbitRoot.adjoint_eq]
  rw [← c.orbitRoot_comp_self, ContinuousLinearMap.comp_apply, h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-! ## The inverse-Gramian form -/

theorem norm_sq_eq_tsum_eigen (y : ℓ²ι) :
    ‖y‖ ^ 2 = ∑' k, ‖⟪c.orbitEigenbasis k, y⟫_ℂ‖ ^ 2 := by
  rw [← c.orbitEigenbasis.repr.norm_map, lp_two_norm_sq_eq_tsum]
  simp_rw [HilbertBasis.repr_apply_apply]

theorem summable_eigen_sq (y : ℓ²ι) : Summable fun k => ‖⟪c.orbitEigenbasis k, y⟫_ℂ‖ ^ 2 :=
  c.orbitEigenbasis.orthonormal.inner_products_summable y

/-- **(OG.13)** The inverse-Gramian form `q_G(x) = Σ_k |⟨f_k, x⟩|²/γ_k ∈ [0, ∞]`. -/
def orbitCostForm (x : ℓ²ι) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (‖⟪c.orbitEigenbasis k, x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k)

/-- **(OG.13)** `q_G(G^{1/2} y) = ‖y‖²`. -/
theorem orbitCostForm_orbitRoot (y : ℓ²ι) : c.orbitCostForm (c.orbitRoot y) = ENNReal.ofReal (‖y‖ ^ 2) := by
  have hterm : ∀ k, ‖⟪c.orbitEigenbasis k, c.orbitRoot y⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k =
      ‖⟪c.orbitEigenbasis k, y⟫_ℂ‖ ^ 2 := fun k => by
    rw [inner_orbitEigenbasis_orbitRoot, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (c.orbitEigenvalue_pos k).le]
    field_simp [(c.orbitEigenvalue_pos k).ne']
  rw [orbitCostForm]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (c.summable_eigen_sq y),
    c.norm_sq_eq_tsum_eigen]

theorem summable_of_orbitCostForm_lt_top {x : ℓ²ι} (hx : c.orbitCostForm x < ⊤) :
    Summable fun k => ‖⟪c.orbitEigenbasis k, x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k := by
  have h := ENNReal.summable_toReal hx.ne
  refine h.congr fun k => ?_
  rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (c.orbitEigenvalue_pos k).le)]

/-- **(OG.13)** `q_G(x) < ∞` exactly on `Ran G^{1/2}`. -/
theorem orbitCostForm_lt_top_iff (x : ℓ²ι) : c.orbitCostForm x < ⊤ ↔ ∃ y, c.orbitRoot y = x := by
  constructor
  · intro hx
    have hs := c.summable_of_orbitCostForm_lt_top hx
    set a : EigenIndex c.orbitGramian → ℂ := fun k =>
      ⟪c.orbitEigenbasis k, x⟫_ℂ / (Real.sqrt (c.orbitEigenvalue k) : ℂ) with ha
    have hnorm : ∀ k, ‖a k‖ ^ 2 = ‖⟪c.orbitEigenbasis k, x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k := fun k => by
      rw [ha, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (c.orbitEigenvalue_pos k).le]
    have hmem : Memℓp a 2 := memℓp_gen (by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      simp_rw [hnorm]
      exact hs)
    refine ⟨c.orbitEigenbasis.repr.symm ⟨a, hmem⟩, c.orbitEigenbasis.repr.injective
      (lp.ext (funext fun k => ?_))⟩
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_orbitEigenbasis_orbitRoot,
      ← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    change (Real.sqrt (c.orbitEigenvalue k) : ℂ) * a k = _
    rw [ha, mul_div_cancel₀]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (c.orbitEigenvalue_pos k)).ne'
  · rintro ⟨y, rfl⟩
    rw [orbitCostForm_orbitRoot]
    exact ENNReal.ofReal_lt_top

/-- **(OG.13)** The form is lower semicontinuous (closed). -/
theorem lowerSemicontinuous_orbitCostForm : LowerSemicontinuous c.orbitCostForm := by
  refine lowerSemicontinuous_tsum fun k => ?_
  refine Continuous.lowerSemicontinuous ?_
  exact ENNReal.continuous_ofReal.comp
    (((continuous_const.inner continuous_id).norm.pow 2).div_const _)

/-- **(OG.28)** On a sublevel `q_G(x) ≤ M` the spectral tail is uniformly small:
`Σ_{γ_k < ε} |⟨f_k, x⟩|² ≤ ε M`. -/
theorem tail_le_of_orbitCostForm_le {x : ℓ²ι} {M : ℝ} (hM0 : 0 ≤ M)
    (hx : c.orbitCostForm x ≤ ENNReal.ofReal M) {ε : ℝ} (hε : 0 < ε) :
    ∑' k : {k // c.orbitEigenvalue k < ε}, ‖⟪c.orbitEigenbasis (k : EigenIndex c.orbitGramian), x⟫_ℂ‖ ^ 2 ≤
      ε * M := by
  have hlt : c.orbitCostForm x < ⊤ := lt_of_le_of_lt hx ENNReal.ofReal_lt_top
  have hs := c.summable_of_orbitCostForm_lt_top hlt
  have hsM : ∑' k, ‖⟪c.orbitEigenbasis k, x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k ≤ M := by
    rw [orbitCostForm, ← ENNReal.ofReal_tsum_of_nonneg (fun k => div_nonneg (sq_nonneg _)
      (c.orbitEigenvalue_pos k).le) hs] at hx
    exact (ENNReal.ofReal_le_ofReal_iff hM0).1 hx
  calc ∑' k : {k // c.orbitEigenvalue k < ε}, ‖⟪c.orbitEigenbasis (k : EigenIndex c.orbitGramian), x⟫_ℂ‖ ^ 2
      ≤ ∑' k : {k // c.orbitEigenvalue k < ε},
          ε * (‖⟪c.orbitEigenbasis (k : EigenIndex c.orbitGramian), x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k) := by
        refine Summable.tsum_le_tsum (fun k => ?_) ((c.summable_eigen_sq x).subtype _)
          ((hs.subtype _).mul_left ε)
        have hγ := c.orbitEigenvalue_pos k
        rw [mul_div_assoc', le_div_iff₀ hγ]
        exact (mul_le_mul_of_nonneg_left k.2.le (sq_nonneg _)).trans_eq (mul_comm _ _)
    _ = ε * ∑' k : {k // c.orbitEigenvalue k < ε},
          ‖⟪c.orbitEigenbasis (k : EigenIndex c.orbitGramian), x⟫_ℂ‖ ^ 2 / c.orbitEigenvalue k :=
        tsum_mul_left
    _ ≤ ε * M := mul_le_mul_of_nonneg_left ((Summable.tsum_subtype_le _ _ (fun k =>
          div_nonneg (sq_nonneg _) (c.orbitEigenvalue_pos k).le) hs).trans hsM) hε.le

/-- **(OG.14) Properness.**  Every sublevel of `q_G` is compact. -/
theorem isCompact_orbitCostForm_sublevel [Countable ι] {M : ℝ} (hM : 0 ≤ M) :
    IsCompact {x : ℓ²ι | c.orbitCostForm x ≤ ENNReal.ofReal M} := by
  haveI := separableSpace_lp_countable (ι := ι)
  have heq : {x : ℓ²ι | c.orbitCostForm x ≤ ENNReal.ofReal M} =
      c.orbitRoot '' Metric.closedBall 0 (Real.sqrt M) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (c.orbitCostForm_lt_top_iff x).1 (lt_of_le_of_lt hx ENNReal.ofReal_lt_top)
      refine ⟨y, ?_, rfl⟩
      have h := hx
      rw [Set.mem_setOf_eq, orbitCostForm_orbitRoot, ENNReal.ofReal_le_ofReal_iff hM] at h
      simpa using Real.le_sqrt_of_sq_le h
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_setOf_eq, orbitCostForm_orbitRoot]
      refine ENNReal.ofReal_le_ofReal ?_
      have hy' : ‖y‖ ≤ Real.sqrt M := by simpa using hy
      calc ‖y‖ ^ 2 ≤ Real.sqrt M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy' 2
        _ = M := Real.sq_sqrt hM
  rw [heq]
  exact isCompact_image_closedBall_of_isCompactOperator _ c.isCompactOperator_orbitRoot _

/-! ## The inverse operator `C = G^{-1}` -/

/-- **(OG.13)** The endogenous cost operator `C = G^{-1}`, defined on `Ran G`. -/
def orbitCost : ℓ²ι →ₗ.[ℂ] ℓ²ι := gramInverse c.orbitGramian c.orbitGramian_injective

/-- **(OG.13)** `C` is self-adjoint. -/
theorem isSelfAdjoint_orbitCost : IsSelfAdjoint c.orbitCost :=
  isSelfAdjoint_gramInverse _ c.isSelfAdjoint_orbitGramian

/-- **(OG.13)** `C` is positive. -/
theorem re_inner_orbitCost_nonneg (x : c.orbitCost.domain) :
    0 ≤ (⟪c.orbitCost x, (x : ℓ²ι)⟫_ℂ).re :=
  re_inner_gramInverse_nonneg _ c.isPositive_orbitGramian x

/-- **(OG.13)** On `Dom C` the form is `q_G(x) = ⟨Cx, x⟩`. -/
theorem orbitCostForm_eq_inner_orbitCost (x : c.orbitCost.domain) :
    c.orbitCostForm x = ENNReal.ofReal (⟪c.orbitCost x, (x : ℓ²ι)⟫_ℂ).re := by
  obtain ⟨u, hu⟩ := x.2
  have hCx : c.orbitCost x = u := gramInverse_eq_of_apply _ x.2 hu
  have hx : (x : ℓ²ι) = c.orbitRoot (c.orbitRoot u) := by
    rw [← hu, ← ContinuousLinearMap.comp_apply, c.orbitRoot_comp_self]
    rfl
  rw [hCx, hx, orbitCostForm_orbitRoot, norm_orbitRoot_sq, ← hx, ← hu]
  rfl

/-- The resolvent multipliers `γ_k/(1 + γ_k)`. -/
theorem norm_resolventMultiplier_le (k : EigenIndex c.orbitGramian) :
    ‖((c.orbitEigenvalue k / (1 + c.orbitEigenvalue k) : ℝ) : ℂ)‖ ≤ 1 := by
  have h := c.orbitEigenvalue_pos k
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
  linarith

/-- **(OG.27)** The resolvent `(C + 1)^{-1}`, diagonal with eigenvalues `γ_k/(1 + γ_k)`. -/
def orbitCostResolvent : ℓ²ι →L[ℂ] ℓ²ι :=
  basisDiag c.orbitEigenbasis (fun k => ((c.orbitEigenvalue k / (1 + c.orbitEigenvalue k) : ℝ) : ℂ))
    zero_le_one c.norm_resolventMultiplier_le

theorem norm_resolventFactor_le (k : EigenIndex c.orbitGramian) :
    ‖(((1 + c.orbitEigenvalue k)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
  have h := c.orbitEigenvalue_pos k
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith)

/-- **(OG.27)** `(C + 1)^{-1} f_k = γ_k/(1 + γ_k) f_k`. -/
theorem orbitCostResolvent_orbitEigenbasis (k : EigenIndex c.orbitGramian) :
    c.orbitCostResolvent (c.orbitEigenbasis k) =
      ((c.orbitEigenvalue k / (1 + c.orbitEigenvalue k) : ℝ) : ℂ) • c.orbitEigenbasis k :=
  basisDiag_basis _ _ _ _ _

/-- **(OG.13)/(OG.27) Compact resolvent.**  `R = (C + 1)^{-1}` is compact, maps into `Dom C`, and
inverts `C + 1` on both sides. -/
theorem orbitCost_compactResolvent :
    IsCompactOperator c.orbitCostResolvent ∧
      (∀ x : ℓ²ι, ∃ hx : c.orbitCostResolvent x ∈ c.orbitCost.domain,
        c.orbitCost ⟨_, hx⟩ + c.orbitCostResolvent x = x) ∧
      ∀ z : c.orbitCost.domain, c.orbitCostResolvent (c.orbitCost z + z) = z := by
  set D := basisDiag c.orbitEigenbasis (fun k => (((1 + c.orbitEigenvalue k)⁻¹ : ℝ) : ℂ))
    zero_le_one c.norm_resolventFactor_le with hD
  have hRG : c.orbitCostResolvent = c.orbitGramian ∘L D := by
    refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
    rw [ContinuousLinearMap.comp_apply, hD, basisDiag_basis, map_smul, orbitGramian_orbitEigenbasis,
      smul_smul, orbitCostResolvent_orbitEigenbasis, ← Complex.ofReal_mul]
    congr 2
    ring
  have hDG : D + c.orbitGramian ∘L D = 1 := by
    refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
    rw [add_apply, ContinuousLinearMap.comp_apply, hD, basisDiag_basis, map_smul,
      orbitGramian_orbitEigenbasis, smul_smul, ← add_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      one_apply_eq_self]
    have h := c.orbitEigenvalue_pos k
    rw [show ((1 + c.orbitEigenvalue k)⁻¹ + (1 + c.orbitEigenvalue k)⁻¹ * c.orbitEigenvalue k) = 1 by
      field_simp]
    simp
  refine ⟨?_, fun x => ?_, fun z => ?_⟩
  · refine isCompactOperator_basisDiag _ _ _ _ ?_
    have h := c.tendsto_orbitEigenvalue
    have h' : Tendsto (fun k => c.orbitEigenvalue k / (1 + c.orbitEigenvalue k)) cofinite (𝓝 0) := by
      have := h.div (tendsto_const_nhds.add h) (by norm_num : (1 : ℝ) + 0 ≠ 0)
      rw [add_zero, zero_div] at this
      exact this
    have h'' := h'.norm
    rw [norm_zero] at h''
    refine h''.congr fun k => ?_
    rw [Complex.norm_real]
  · have hmem : c.orbitCostResolvent x ∈ c.orbitCost.domain := ⟨D x, by rw [hRG]; rfl⟩
    refine ⟨hmem, ?_⟩
    have hC : c.orbitCost ⟨_, hmem⟩ = D x :=
      gramInverse_eq_of_apply _ hmem (by rw [hRG]; rfl)
    rw [hC, hRG]
    have := congrArg (fun T : ℓ²ι →L[ℂ] ℓ²ι => T x) hDG
    simpa using this
  · obtain ⟨u, hu⟩ := z.2
    have hCz : c.orbitCost z = u := gramInverse_eq_of_apply _ z.2 hu
    have hcomm : D ∘L c.orbitGramian = c.orbitGramian ∘L D := by
      refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
      simp only [ContinuousLinearMap.comp_apply]
      rw [orbitGramian_orbitEigenbasis, map_smul, hD, basisDiag_basis, map_smul,
        orbitGramian_orbitEigenbasis, smul_smul, smul_smul, mul_comm]
    have h2 : D (c.orbitGramian u) = c.orbitGramian (D u) := by
      have := congrArg (fun T : ℓ²ι →L[ℂ] ℓ²ι => T u) hcomm
      simpa using this
    have h3 : D u + c.orbitGramian (D u) = u := by
      have := congrArg (fun T : ℓ²ι →L[ℂ] ℓ²ι => T u) hDG
      simpa using this
    have hz : (z : ℓ²ι) = c.orbitGramian u := hu.symm
    rw [hCz, hz, hRG]
    show c.orbitGramian (D (u + c.orbitGramian u)) = c.orbitGramian u
    rw [map_add, h2, h3]

/-! ## The conjugate form -/

theorem two_re_sub_le {x y : ℂ} {g : ℝ} (hg : 0 < g) :
    2 * (starRingEnd ℂ y * x).re - g * ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 / g := by
  rw [le_div_iff₀ hg]
  have hx : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hy : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hx, hy]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (x.re - g * y.re), sq_nonneg (x.im - g * y.im)]

/-- **(OG.13)** `q_G` is the conjugate form `sup_y (2 Re⟨y, x⟩ - ⟨y, G y⟩)`. -/
theorem orbitCostForm_eq_legendreForm (x : ℓ²ι) : c.orbitCostForm x = legendreForm c.orbitGramian x := by
  set f := c.orbitEigenbasis
  set γ := c.orbitEigenvalue
  refine le_antisymm ?_ ?_
  · rw [orbitCostForm, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    set y : ℓ²ι := ∑ k ∈ F, (⟪f k, x⟫_ℂ / (γ k : ℂ)) • f k with hy
    refine le_trans (le_of_eq ?_) (le_iSup _ y)
    have hγ : ∀ k, (γ k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.2 (c.orbitEigenvalue_pos k).ne'
    have h1 : ⟪y, x⟫_ℂ = ∑ k ∈ F, ((‖⟪f k, x⟫_ℂ‖ ^ 2 / γ k : ℝ) : ℂ) := by
      rw [hy, sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_smul_left, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
      push_cast
      ring
    have hyk : ∀ k ∈ F, ⟪f k, y⟫_ℂ = ⟪f k, x⟫_ℂ / (γ k : ℂ) := fun k hk => by
      rw [hy]
      exact f.orthonormal.inner_right_sum _ hk
    have hGy : c.orbitGramian y = ∑ k ∈ F, ⟪f k, x⟫_ℂ • f k := by
      rw [hy, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, orbitGramian_orbitEigenbasis, smul_smul, div_mul_cancel₀ _ (hγ k)]
    have h2 : ⟪y, c.orbitGramian y⟫_ℂ = ∑ k ∈ F, ((‖⟪f k, x⟫_ℂ‖ ^ 2 / γ k : ℝ) : ℂ) := by
      rw [hGy, inner_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [inner_smul_right, ← inner_conj_symm y (f k), hyk k hk, map_div₀, Complex.conj_ofReal,
        mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [h1, h2, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg (sq_nonneg _)
      (c.orbitEigenvalue_pos k).le)]
    congr 1
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
    ring
  · refine iSup_le fun y => ?_
    by_cases hx : c.orbitCostForm x = ⊤
    · rw [hx]; exact le_top
    have hs := c.summable_of_orbitCostForm_lt_top (lt_top_iff_ne_top.2 hx)
    have hxy := f.hasSum_inner_mul_inner y x
    have hyy := f.hasSum_inner_mul_inner y (c.orbitGramian y)
    have hre1 := Complex.hasSum_re hxy
    have hre2 := Complex.hasSum_re hyy
    have hcomb := (hre1.mul_left 2).sub hre2
    have hpt : ∀ k, 2 * (⟪y, f k⟫_ℂ * ⟪f k, x⟫_ℂ).re - (⟪y, f k⟫_ℂ * ⟪f k, c.orbitGramian y⟫_ℂ).re ≤
        ‖⟪f k, x⟫_ℂ‖ ^ 2 / γ k := fun k => by
      rw [inner_orbitEigenbasis_orbitGramian, ← inner_conj_symm y (f k)]
      have := two_re_sub_le (x := ⟪f k, x⟫_ℂ) (y := ⟪f k, y⟫_ℂ) (c.orbitEigenvalue_pos k)
      have e : (starRingEnd ℂ ⟪f k, y⟫_ℂ * ((γ k : ℂ) * ⟪f k, y⟫_ℂ)).re = γ k * ‖⟪f k, y⟫_ℂ‖ ^ 2 := by
        rw [mul_left_comm, Complex.conj_mul']
        norm_cast
      rw [e]
      exact this
    have hle := hasSum_le hpt hcomb hs.hasSum
    rw [orbitCostForm, ← ENNReal.ofReal_tsum_of_nonneg (fun k => div_nonneg (sq_nonneg _)
      (c.orbitEigenvalue_pos k).le) hs]
    exact ENNReal.ofReal_le_ofReal hle

/-! ## The reachability map: polar factorization and minimum energy -/

theorem inner_heatAnalysis_orbitEigenbasis (k l : EigenIndex c.orbitGramian) :
    ⟪c.heatAnalysis (c.orbitEigenbasis k), c.heatAnalysis (c.orbitEigenbasis l)⟫_ℂ =
      if k = l then (c.orbitEigenvalue k : ℂ) else 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change ⟪c.orbitEigenbasis k, c.orbitGramian (c.orbitEigenbasis l)⟫_ℂ = _
  rw [orbitGramian_orbitEigenbasis, inner_smul_right, orthonormal_iff_ite.1 c.orbitEigenbasis.orthonormal]
  split_ifs with h
  · subst h; simp
  · simp

/-- The orthonormal reachability columns `g_k = W^* f_k / √γ_k`. -/
def orbitColumn (k : EigenIndex c.orbitGramian) : HalfLineL2 :=
  ((Real.sqrt (c.orbitEigenvalue k))⁻¹ : ℂ) • c.heatAnalysis (c.orbitEigenbasis k)

theorem orthonormal_orbitColumn : Orthonormal ℂ c.orbitColumn := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [orbitColumn, orbitColumn, inner_smul_left, inner_smul_right, inner_heatAnalysis_orbitEigenbasis]
  split_ifs with h
  · subst h
    have hs := Real.sqrt_pos.2 (c.orbitEigenvalue_pos k)
    have hsq := Real.sq_sqrt (c.orbitEigenvalue_pos k).le
    have hsC : (Real.sqrt (c.orbitEigenvalue k) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    rw [map_inv₀, Complex.conj_ofReal, show (c.orbitEigenvalue k : ℂ) =
      (Real.sqrt (c.orbitEigenvalue k) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, hsq]]
    field_simp
  · simp

/-- The isometry `V^* : ℓ² → L²`, `f_k ↦ g_k`. -/
def orbitCoisometryAdjoint : ℓ²ι →L[ℂ] HalfLineL2 :=
  c.orthonormal_orbitColumn.orthogonalFamily.linearIsometry.toContinuousLinearMap ∘L
    c.orbitEigenbasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem orbitCoisometryAdjoint_orbitEigenbasis (k : EigenIndex c.orbitGramian) :
    c.orbitCoisometryAdjoint (c.orbitEigenbasis k) = c.orbitColumn k := by
  classical
  simp only [orbitCoisometryAdjoint, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    HilbertBasis.repr_self, LinearIsometry.coe_toContinuousLinearMap,
    OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply, one_smul]

theorem norm_orbitCoisometryAdjoint (y : ℓ²ι) : ‖c.orbitCoisometryAdjoint y‖ = ‖y‖ := by
  simp [orbitCoisometryAdjoint]

theorem inner_orbitCoisometryAdjoint (y z : ℓ²ι) :
    ⟪c.orbitCoisometryAdjoint y, c.orbitCoisometryAdjoint z⟫_ℂ = ⟪y, z⟫_ℂ := by
  simp only [orbitCoisometryAdjoint, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

/-- **(OG.35b)** The coisometric polar factor `V : L² → ℓ²`. -/
def orbitCoisometry : HalfLineL2 →L[ℂ] ℓ²ι := ContinuousLinearMap.adjoint c.orbitCoisometryAdjoint

/-- **(OG.35b)** `V V^* = 1`: `V` is a coisometry onto `ℓ²`. -/
theorem orbitCoisometry_comp_adjoint : c.orbitCoisometry ∘L c.orbitCoisometryAdjoint = 1 := by
  refine ContinuousLinearMap.ext fun y => ext_inner_right ℂ fun z => ?_
  rw [ContinuousLinearMap.comp_apply, orbitCoisometry, ContinuousLinearMap.adjoint_inner_left,
    inner_orbitCoisometryAdjoint, one_apply_eq_self]

theorem norm_orbitCoisometry_le (u : HalfLineL2) : ‖c.orbitCoisometry u‖ ≤ ‖u‖ := by
  have hA : ‖c.orbitCoisometryAdjoint‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [norm_orbitCoisometryAdjoint, one_mul]
  have h := c.orbitCoisometry.le_opNorm u
  rw [orbitCoisometry, LinearIsometryEquiv.norm_map] at h
  calc ‖c.orbitCoisometry u‖ ≤ ‖c.orbitCoisometryAdjoint‖ * ‖u‖ := h
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖u‖ := one_mul _

/-- `W^* = V^* G^{1/2}`. -/
theorem heatAnalysis_eq : c.heatAnalysis = c.orbitCoisometryAdjoint ∘L c.orbitRoot := by
  refine ext_hilbertBasis c.orbitEigenbasis fun k => ?_
  rw [ContinuousLinearMap.comp_apply, orbitRoot_orbitEigenbasis, map_smul,
    orbitCoisometryAdjoint_orbitEigenbasis, orbitColumn, smul_smul, mul_inv_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (c.orbitEigenvalue_pos k)).ne'

/-- **(OG.35b) Polar factorization.**  `W = G^{1/2} V`. -/
theorem heatReachability_eq : c.heatReachability = c.orbitRoot ∘L c.orbitCoisometry := by
  rw [HeatSource.heatReachability, heatAnalysis_eq, ContinuousLinearMap.adjoint_comp,
    c.isSelfAdjoint_orbitRoot.adjoint_eq]
  rfl

omit [DecidableEq ι] in
/-- **(OG.15)** `W W^* = G`. -/
theorem heatReachability_comp_heatAnalysis : c.heatReachability ∘L c.heatAnalysis = c.orbitGramian :=
  rfl

/-- Every reachable vector costs at most its control energy. -/
theorem orbitCostForm_heatReachability_le (u : HalfLineL2) :
    c.orbitCostForm (c.heatReachability u) ≤ ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [heatReachability_eq, ContinuousLinearMap.comp_apply, orbitCostForm_orbitRoot]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (c.norm_orbitCoisometry_le u) 2)

/-- **(OG.16)** A vector of finite cost has a control of exactly that energy. -/
theorem exists_minimalControl {x : ℓ²ι} (hx : c.orbitCostForm x < ⊤) :
    ∃ u, c.heatReachability u = x ∧ ENNReal.ofReal (‖u‖ ^ 2) = c.orbitCostForm x := by
  obtain ⟨y, rfl⟩ := (c.orbitCostForm_lt_top_iff x).1 hx
  refine ⟨c.orbitCoisometryAdjoint y, ?_, ?_⟩
  · rw [heatReachability_eq, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply
      c.orbitCoisometry, orbitCoisometry_comp_adjoint, one_apply_eq_self]
  · rw [norm_orbitCoisometryAdjoint, orbitCostForm_orbitRoot]

/-- **(OG.16) Minimum energy.**  `q_G(x) = min {‖u‖² : W u = x}` (infinite when unreachable). -/
theorem orbitCostForm_eq_iInf (x : ℓ²ι) :
    c.orbitCostForm x = ⨅ (u : HalfLineL2) (_ : c.heatReachability u = x), ENNReal.ofReal (‖u‖ ^ 2) := by
  refine le_antisymm (le_iInf₂ fun u hu => hu ▸ c.orbitCostForm_heatReachability_le u) ?_
  by_cases hx : c.orbitCostForm x = ⊤
  · rw [hx]; exact le_top
  obtain ⟨u, hu, hE⟩ := c.exists_minimalControl (lt_top_iff_ne_top.2 hx)
  exact (iInf₂_le u hu).trans hE.le

/-- **(OG.15)** `Ran W = Ran G^{1/2} = {q_G < ∞}`. -/
theorem range_heatReachability :
    Set.range c.heatReachability = Set.range c.orbitRoot ∧
      Set.range c.heatReachability = {x | c.orbitCostForm x < ⊤} := by
  have h2 : Set.range c.heatReachability = {x | c.orbitCostForm x < ⊤} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact lt_of_le_of_lt (c.orbitCostForm_heatReachability_le u) ENNReal.ofReal_lt_top
    · intro hx
      obtain ⟨u, hu, -⟩ := c.exists_minimalControl hx
      exact ⟨u, hu⟩
  refine ⟨?_, h2⟩
  rw [h2]
  ext x
  exact c.orbitCostForm_lt_top_iff x

end CyclicHeatSource

/-! ## Naturality: rescaling the source clock -/

namespace HeatSource

variable (s : HeatSource ι)

/-- The rescaled source `L ↦ aL`. -/
def scale {a : ℝ} (ha : 0 < a) : HeatSource ι where
  lam j := a * s.lam j
  gap := a * s.gap
  gap_pos := mul_pos ha s.gap_pos
  gap_le j := mul_le_mul_of_nonneg_left (s.gap_le j) ha.le
  v := s.v

/-- `e^{-t(aL)} = e^{-(at)L}`. -/
theorem heatSemigroup_scale {a : ℝ} (ha : 0 < a) (t : ℝ) :
    heatSemigroup (s.scale ha).lam_nonneg t = heatSemigroup s.lam_nonneg (a * t) := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun j => ?_)
  rw [heatSemigroup_apply, heatSemigroup_apply, heatFactor, heatFactor]
  congr 4
  change max t 0 * (a * s.lam j) = max (a * t) 0 * s.lam j
  rw [show max (a * t) 0 = a * max t 0 by rw [mul_max_of_nonneg _ _ ha.le, mul_zero]]
  ring

variable [DecidableEq ι]

/-- **(OG.22)** `G_{aL} = a^{-1} G_L`. -/
theorem orbitGramian_scale {a : ℝ} (ha : 0 < a) :
    (s.scale ha).orbitGramian = (a⁻¹ : ℂ) • s.orbitGramian := by
  refine ext_of_inner_single fun i j => ?_
  rw [inner_single_orbitGramian, smul_apply, inner_smul_right, inner_single_orbitGramian]
  change s.v i * starRingEnd ℂ (s.v j) / ((a * s.lam i + a * s.lam j : ℝ) : ℂ) = _
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hS : ((s.lam i : ℂ) + s.lam j) ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < s.lam i + s.lam j by linarith [s.lam_pos i, s.lam_pos j]).ne'
  push_cast
  field_simp

end HeatSource

theorem gramInverse_congr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {G G' : H →L[ℂ] H} (h : G = G') (hG : Function.Injective G) (hG' : Function.Injective G') :
    gramInverse G hG = gramInverse G' hG' := by
  subst h
  rfl

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι)

/-- The rescaled cyclic source `L ↦ aL`. -/
def scale {a : ℝ} (ha : 0 < a) : CyclicHeatSource ι where
  toHeatSource := c.toHeatSource.scale ha
  simple _ _ h := c.simple (mul_left_cancel₀ ha.ne' h)
  proper := tendsto_id.const_mul_atTop ha |>.comp c.proper
  fullSupport := c.fullSupport

variable [DecidableEq ι]

theorem scale_orbitGramian {a : ℝ} (ha : 0 < a) :
    (c.scale ha).orbitGramian = (a⁻¹ : ℂ) • c.orbitGramian :=
  c.toHeatSource.orbitGramian_scale ha

/-- **(OG.22)** `C_{aL} = a C_L`. -/
theorem orbitCost_scale {a : ℝ} (ha : 0 < a) : (c.scale ha).orbitCost = (a : ℂ) • c.orbitCost := by
  have hinj : Function.Injective ((a⁻¹ : ℂ) • c.orbitGramian) := by
    rw [← c.scale_orbitGramian ha]
    exact (c.scale ha).orbitGramian_injective
  rw [orbitCost, gramInverse_congr (c.scale_orbitGramian ha) _ hinj,
    gramInverse_smul c.orbitGramian_injective ha hinj]
  rfl

/-- **(OG.22)** `q_{G_{aL}} = a q_{G_L}`. -/
theorem orbitCostForm_scale {a : ℝ} (ha : 0 < a) (x : ℓ²ι) :
    (c.scale ha).orbitCostForm x = ENNReal.ofReal a * c.orbitCostForm x := by
  rw [orbitCostForm_eq_legendreForm, orbitCostForm_eq_legendreForm, c.scale_orbitGramian ha,
    show (a⁻¹ : ℂ) = ((a⁻¹ : ℝ) : ℂ) by push_cast; rfl, legendreForm_smul (inv_pos.2 ha), inv_inv]

end CyclicHeatSource

/-! ## Naturality: unitary transport of the source -/

namespace HeatSource

variable (s : HeatSource ι)

theorem integrable_laplace_heatSemigroup (x : ℓ²ι) :
    IntegrableOn (fun t => (Real.exp (-t) : ℂ) • heatSemigroup s.lam_nonneg t x) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_mul one_pos).mul_const ‖x‖)
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul
      (continuous_heatSemigroup_apply s.lam_nonneg x)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have h := (heatSemigroup s.lam_nonneg t).le_opNorm x
  have hn : ‖heatSemigroup s.lam_nonneg t‖ ≤ 1 :=
    LpDiagonal.norm_lpDiag_le _ _ _ _
  nlinarith [norm_nonneg x]

variable [DecidableEq ι]

/-- **(OG.6)** The reporter is the Laplace transform of the heat semigroup:
`D x = (1 + L)^{-1} x = ∫_0^∞ e^{-t} S_t x dt`. -/
theorem heatReporter_eq_integral (x : ℓ²ι) :
    s.heatReporter x = ∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • heatSemigroup s.lam_nonneg t x := by
  refine lp.ext (funext fun j => ?_)
  have h := integral_inner (𝕜 := ℂ) (s.integrable_laplace_heatSemigroup x) (lp.single 2 j (1 : ℂ))
  rw [inner_single_one_left] at h
  rw [s.heatReporter_apply, ← h]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ⟪(lp.single 2 j (1 : ℂ) : ℓ²ι),
      (Real.exp (-t) : ℂ) • heatSemigroup s.lam_nonneg t x⟫_ℂ =
      x j * ((Real.exp (-((1 + s.lam j) * t)) : ℝ) : ℂ) := fun t ht => by
    rw [inner_smul_right, inner_single_one_left, heatSemigroup_apply,
      heatFactor_of_nonneg _ (le_of_lt ht)]
    rw [show -((1 + s.lam j) * t) = -t + -(t * s.lam j) by ring, Real.exp_add]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_complex_ofReal,
    integral_exp_neg_mul (by linarith [s.lam_nonneg j])]
  push_cast
  ring

end HeatSource

namespace CyclicHeatSource

variable (c : CyclicHeatSource ι) [DecidableEq ι]

/-- **(OG.22) Unitary covariance.**  Transporting the source by a unitary `U` transports the orbit
Gramian, the source projection, the reporter (as the Laplace transform of the transported
semigroup), the cost operator and the cost form by conjugation. -/
theorem naturality_unitary {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : ℓ²ι ≃ₗᵢ[ℂ] H') :
    let U' := U.toContinuousLinearEquiv.toContinuousLinearMap
    let U'' := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
    (orbitGramianOf (fun t => U' ∘L heatSemigroup c.lam_nonneg t ∘L U'') (U c.v) : H' →L[ℂ] H') =
        U' ∘L c.orbitGramian ∘L U'' ∧
      InnerProductSpace.rankOne ℂ (U c.v) (U c.v) = U' ∘L c.heatProjection ∘L U'' ∧
      (∀ y : H', ∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) • (U' ∘L heatSemigroup c.lam_nonneg t ∘L U'') y =
        (U' ∘L c.heatReporter ∘L U'') y) ∧
      (∀ y : ℓ²ι, ∃ hy, gramInverse (U' ∘L c.orbitGramian ∘L U'')
        (by
          intro a b h
          have h1 : c.orbitGramian (U.symm a) = c.orbitGramian (U.symm b) := U.injective h
          exact U.symm.injective (c.orbitGramian_injective h1))
        ⟨U (c.orbitGramian y), hy⟩ = U y) ∧
      ∀ x : ℓ²ι, legendreForm (U' ∘L c.orbitGramian ∘L U'') (U x) = c.orbitCostForm x := by
  intro U' U''
  refine ⟨?_, ?_, fun y => ?_, fun y => gramInverse_conj U _ y, fun x => ?_⟩
  · rw [orbitGramianOf_conj U _ _ (continuous_heatSemigroup_apply _ _)
      c.integrableOn_norm_heatOrbit_sq]
    change U' ∘L (c.orbitGramianS1 : ℓ²ι →L[ℂ] ℓ²ι) ∘L U'' = _
    rw [c.orbitGramianS1_eq]
  · refine ContinuousLinearMap.ext fun y => ?_
    show ⟪U c.v, y⟫_ℂ • U c.v = U (c.heatProjection (U.symm y))
    rw [HeatSource.heatProjection, InnerProductSpace.rankOne_apply, map_smul, ← U.inner_map_map,
      LinearIsometryEquiv.apply_symm_apply]
  · have hcomm : ∀ t, (Real.exp (-t) : ℂ) • (U' ∘L heatSemigroup c.lam_nonneg t ∘L U'') y =
        U' ((Real.exp (-t) : ℂ) • heatSemigroup c.lam_nonneg t (U'' y)) := fun t => by
      simp [U', U'']
    simp_rw [hcomm]
    rw [U'.integral_comp_comm (c.integrable_laplace_heatSemigroup (U'' y)),
      ← c.heatReporter_eq_integral]
    rfl
  · rw [legendreForm_conj, orbitCostForm_eq_legendreForm]

end CyclicHeatSource

end GaloisForLFunctions.HTGeometry
