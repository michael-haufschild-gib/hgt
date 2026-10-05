import GaloisForLFunctions.HTGeometry.BlockFormationSemiFredholm
import GaloisForLFunctions.HTGeometry.BoundedFredholmStability

/-!
# Local Fredholmness and the two cofinal failures

**Countertheorem 5.4.**  Let `e_n ∈ H_n` be unit vectors with rank-one projections `E_n`.

1. `T_n = I - E_n` differs from `I` by a compact operator, has closed range and one-dimensional
   kernel `ℂ e_n`, yet `⊕_n T_n` has infinite-dimensional kernel.
2. `R_n = I - (1 - 1/(n+1)) E_n` is invertible with `R_n - I` of rank one (every Calkin class is the
   identity), but `γ(R_n) = 1/(n+1) → 0`, so `⊕_n R_n` has nonclosed range and no bounded decoder.

**Corollary 5.5.**  For orthogonal shell projections `S_n` onto `K_n` and blocks `D_n` with
`D_n - S_n` compact, the compressions `B_n = S_n D_n S_n|_{K_n}` are identity plus compact, hence
Fredholm, and `⊕_n B_n` is upper semi-Fredholm exactly when `inf_n γ(B_n) > 0` and
`Σ_n dim ker B_n < ∞`.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

/-! ### Countertheorem 5.4 -/

section Countertheorem

variable {E : ℕ → Type} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  {e : ∀ n, E n} (he : ∀ n, ‖e n‖ = 1)

/-- The block `T_n = I - E_n`. -/
def kernelBlock (e : ∀ n, E n) (n : ℕ) : E n →L[ℂ] E n := 1 - rankOne (e n) (e n)

theorem kernelBlock_apply (n : ℕ) (x : E n) : kernelBlock e n x = x - ⟪e n, x⟫_ℂ • e n := rfl

include he in
theorem norm_kernelBlock_le (n : ℕ) : ‖kernelBlock e n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul, kernelBlock_apply]
    have h := norm_sq_sub_inner_smul (he n) x
    have h' : ‖x - ⟪e n, x⟫_ℂ • e n‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [h]
      nlinarith [sq_nonneg ‖⟪e n, x⟫_ℂ‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

include he in
theorem kernelBlock_idem (n : ℕ) (x : E n) : kernelBlock e n
    (kernelBlock e n x) = kernelBlock e n x := by
  have hee : ⟪e n, e n⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    simp
  simp only [kernelBlock_apply, inner_sub_right, inner_smul_right, hee, mul_one, sub_self,
    zero_smul, sub_zero]

include he in
theorem mem_ker_kernelBlock_iff (n : ℕ) (x : E n) :
    x ∈ LinearMap.ker (kernelBlock e n : E n →ₗ[ℂ] E n) ↔ x ∈ Submodule.span ℂ {e n} := by
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change kernelBlock e n x = 0 ↔ _
  rw [kernelBlock_apply, sub_eq_zero]
  constructor
  · intro h
    exact ⟨_, h.symm⟩
  · rintro ⟨a, rfl⟩
    have hee : ⟪e n, e n⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he]
      simp
    rw [inner_smul_right, hee, mul_one]

include he in
/-- **Countertheorem 5.4 (1)**: each `T_n` is a compact perturbation of the identity with closed
range and one-dimensional kernel `ℂ e_n`. -/
theorem kernelBlock_local (n : ℕ) :
    IsCompactOperator (kernelBlock e n - 1 : E n →L[ℂ] E n) ∧ IsClosed (Set.range
    (kernelBlock e n)) ∧
      Module.finrank ℂ (LinearMap.ker (kernelBlock e n : E n →ₗ[ℂ] E n)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kernelBlock, sub_sub_cancel_left]
    exact (isCompactOperator_rankOne _ _).neg
  · have hrange : Set.range (kernelBlock e n) = {x | kernelBlock e n x = x} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact kernelBlock_idem he n y
      · intro hx
        exact ⟨x, hx⟩
    rw [hrange]
    exact isClosed_eq (kernelBlock e n).continuous continuous_id
  · have hker : LinearMap.ker (kernelBlock e n : E n →ₗ[ℂ] E n) = Submodule.span ℂ {e n} := by
      ext x
      exact mem_ker_kernelBlock_iff he n x
    rw [hker, finrank_span_singleton]
    intro h0
    have h1 := he n
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

include he in
/-- **Countertheorem 5.4 (1)**: `⊕_n T_n` has infinite-dimensional kernel. -/
theorem not_finiteDimensional_ker_kernelBlock :
    ¬ FiniteDimensional ℂ (LinearMap.ker (blockFormation (kernelBlock e) zero_le_one
      (norm_kernelBlock_le he) : lp E 2 →ₗ[ℂ] lp E 2)) := by
  intro hfin
  have hmem : ∀ n, coordUnit e n ∈ LinearMap.ker (blockFormation (kernelBlock e) zero_le_one
      (norm_kernelBlock_le he) : lp E 2 →ₗ[ℂ] lp E 2) := fun n => by
    rw [mem_ker_blockFormation]
    intro m
    rcases eq_or_ne m n with rfl | h
    · rw [coordUnit, lp.single_apply_self, mem_ker_kernelBlock_iff he]
      exact Submodule.mem_span_singleton_self _
    · rw [coordUnit, lp.single_apply_ne _ _ _ h]
      exact Submodule.zero_mem _
  have hli : LinearIndependent ℂ fun n => (⟨coordUnit e n, hmem n⟩ :
      LinearMap.ker (blockFormation (kernelBlock e) zero_le_one
        (norm_kernelBlock_le he) : lp E 2 →ₗ[ℂ] lp E 2)) :=
    LinearIndependent.of_comp (Submodule.subtype _) (orthonormal_coordUnit he).linearIndependent
  haveI := hli.finite
  exact not_finite ℕ

/-- The block `R_n = I - (1 - 1/(n+1)) E_n`. -/
def gapBlock (e : ∀ n, E n) (n : ℕ) : E n →L[ℂ] E n :=
  1 - ((1 - ((n : ℂ) + 1)⁻¹) • rankOne (e n) (e n))

theorem gapBlock_apply (n : ℕ) (x : E n) :
    gapBlock e n x = (x - ⟪e n, x⟫_ℂ • e n) + ((n : ℂ) + 1)⁻¹ • (⟪e n, x⟫_ℂ • e n) := by
  simp only [gapBlock, sub_apply, one_apply_eq_self, smul_apply, rankOne_apply, sub_smul,
    one_smul]
  abel

include he in
/-- `‖R_n x‖² = ‖x - ⟨e,x⟩e‖² + (n+1)⁻² |⟨e, x⟩|²`. -/
theorem norm_sq_gapBlock (n : ℕ) (x : E n) :
    ‖gapBlock e n x‖ ^ 2 = (‖x‖ ^ 2 - ‖⟪e n, x⟫_ℂ‖ ^ 2) +
    ((n : ℝ) + 1)⁻¹ ^ 2 * ‖⟪e n, x⟫_ℂ‖ ^ 2 := by
  have hee : ⟪e n, e n⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    simp
  have horth : ⟪x - ⟪e n, x⟫_ℂ • e n, ((n : ℂ) + 1)⁻¹ • (⟪e n, x⟫_ℂ • e n)⟫_ℂ = 0 := by
    rw [inner_smul_right, inner_smul_right, inner_sub_left, inner_smul_left, hee, mul_one,
      ← inner_conj_symm (e n) x, RCLike.conj_conj, sub_self, mul_zero, mul_zero]
  rw [gapBlock_apply, @norm_add_sq ℂ, horth, map_zero, mul_zero, add_zero,
    norm_sq_sub_inner_smul (he n), norm_smul, norm_smul, he n, mul_one, norm_inv]
  have : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [this, mul_pow]

include he in
theorem norm_gapBlock_le (n : ℕ) : ‖gapBlock e n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    have h := norm_sq_gapBlock he n x
    have hinv : ((n : ℝ) + 1)⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow]
      exact inv_le_one_of_one_le₀ (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have h' : ‖gapBlock e n x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [h]
      nlinarith [sq_nonneg ‖⟪e n, x⟫_ℂ‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

include he in
/-- `‖R_n x‖ ≥ (n+1)⁻¹ ‖x‖`. -/
theorem le_norm_gapBlock (n : ℕ) (x : E n) : ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ ‖gapBlock e n x‖ := by
  have h := norm_sq_gapBlock he n x
  have hinv : ((n : ℝ) + 1)⁻¹ ^ 2 ≤ 1 := by
    rw [inv_pow]
    exact inv_le_one_of_one_le₀ (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hcoef : ‖⟪e n, x⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have := norm_inner_le_norm (𝕜 := ℂ) (e n) x
    rw [he, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hsq : (((n : ℝ) + 1)⁻¹ * ‖x‖) ^ 2 ≤ ‖gapBlock e n x‖ ^ 2 := by
    rw [h, mul_pow]
    nlinarith [sq_nonneg ‖⟪e n, x⟫_ℂ‖]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq

include he in
theorem norm_gapBlock_unit (n : ℕ) : ‖gapBlock e n (e n)‖ = ((n : ℝ) + 1)⁻¹ := by
  have h := norm_sq_gapBlock he n (e n)
  have hee : ‖⟪e n, e n⟫_ℂ‖ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    simp
  rw [hee, he, sub_self, zero_add, one_pow, mul_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

include he in
/-- `(I + n E_n) R_n = I` and `R_n (I + n E_n) = I`. -/
theorem gapBlock_inverse (n : ℕ) :
    gapBlock e n * (1 + (n : ℂ) • rankOne (e n) (e n)) = 1 ∧
      (1 + (n : ℂ) • rankOne (e n) (e n)) * gapBlock e n = 1 := by
  have hee : ⟪e n, e n⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    simp
  have hEE : rankOne (e n) (e n) * rankOne (e n) (e n) = rankOne (e n) (e n) := by
    rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hee, one_smul]
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    norm_cast
  have hcoef : (n : ℂ) - (1 - ((n : ℂ) + 1)⁻¹) - (1 - ((n : ℂ) + 1)⁻¹) * n = 0 := by
    field_simp
    ring
  have expand : ∀ a b : ℂ, (1 - a • rankOne (e n) (e n)) * (1 + b • rankOne (e n) (e n)) =
      1 + (b - a - a * b) • rankOne (e n) (e n) := fun a b => by
    simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hEE]
    module
  have expand' : ∀ a b : ℂ, (1 + b • rankOne (e n) (e n)) * (1 - a • rankOne (e n) (e n)) =
      1 + (b - a - a * b) • rankOne (e n) (e n) := fun a b => by
    simp only [mul_sub, add_mul, one_mul, mul_one, smul_mul_smul_comm, hEE]
    module
  constructor
  · rw [gapBlock, expand, hcoef, zero_smul, add_zero]
  · rw [gapBlock, expand', hcoef, zero_smul, add_zero]

include he in
theorem gapBlock_injective (n : ℕ) : Function.Injective (gapBlock e n) := fun x y hxy => by
  have h := (gapBlock_inverse he n).2
  have hx := congrArg (fun T : E n →L[ℂ] E n => T x) h
  have hy := congrArg (fun T : E n →L[ℂ] E n => T y) h
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    one_apply_eq_self] at hx hy
  rw [← hx, ← hy, hxy]

include he in
/-- **Countertheorem 5.4 (2)**: `R_n` is invertible, `R_n - I` has rank one (its Calkin class is the
identity), and `γ(R_n) = 1/(n+1)`. -/
theorem gapBlock_local (n : ℕ) :
    IsCompactOperator (gapBlock e n - 1 : E n →L[ℂ] E n) ∧
      IsUnit (gapBlock e n) ∧
      reducedMinModulus (gapBlock e n) = (((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) := by
  refine ⟨?_, ⟨⟨gapBlock e n, 1 + (n : ℂ) • rankOne (e n) (e n), (gapBlock_inverse he n).1,
    (gapBlock_inverse he n).2⟩, rfl⟩, ?_⟩
  · rw [gapBlock, sub_sub_cancel_left]
    exact ((isCompactOperator_rankOne _ _).smul _).neg
  · apply le_antisymm
    · refine (iInf₂_le (e n) (mem_ker_orthogonal_of_injective (gapBlock_injective he n) _)).trans
        (iInf_le_of_le (he n) ?_)
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, norm_gapBlock_unit he]
      push_cast
      exact le_rfl
    · rw [le_reducedMinModulus_iff]
      intro x _
      push_cast
      exact le_norm_gapBlock he n x

include he in
/-- **Countertheorem 5.4 (2)**: `⊕_n R_n` has nonclosed range and admits no bounded decoder. -/
theorem gapBlock_global [∀ n, CompleteSpace (E n)] :
    ¬ IsClosed (Set.range (blockFormation (gapBlock e) zero_le_one (norm_gapBlock_le he))) ∧
      ¬ ∃ L : lp E 2 →L[ℂ] lp E 2, ∀ x,
        L (blockFormation (gapBlock e) zero_le_one (norm_gapBlock_le he) x) = x := by
  have hnot : ¬ (0 < ⨅ n, reducedMinModulus (gapBlock e n)) := by
    rw [pos_iInf_reducedMinModulus_iff]
    rintro ⟨c, hc, h⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
    have hx := h n (e n) (mem_ker_orthogonal_of_injective (gapBlock_injective he n) _)
    rw [he, mul_one, norm_gapBlock_unit he] at hx
    rw [one_div] at hn
    linarith
  have hclosed : ¬ IsClosed (Set.range (blockFormation (gapBlock e) zero_le_one
      (norm_gapBlock_le he))) := by
    rw [isClosed_range_blockFormation_iff]
    exact hnot
  refine ⟨hclosed, fun ⟨L, hL⟩ => hclosed ?_⟩
  have hrange : Set.range (blockFormation (gapBlock e) zero_le_one (norm_gapBlock_le he)) =
      {v | blockFormation (gapBlock e) zero_le_one (norm_gapBlock_le he) (L v) = v} := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg _ (hL x)
    · intro hv
      exact ⟨_, hv⟩
  rw [hrange]
  exact isClosed_eq (by fun_prop) continuous_id

end Countertheorem

/-! ### Corollary 5.5: the exact source-shell gate -/

section SourceShellGate

variable {ι : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (K : ι → Submodule ℂ H) [∀ n, CompleteSpace (K n)] (D : ι → H →L[ℂ] H)

/-- The compressed block `B_n = S_n D_n S_n|_{K_n}`. -/
def compressedBlock (n : ι) : K n →L[ℂ] K n :=
  (K n).orthogonalProjectionOnto ∘L D n ∘L (K n).subtypeL

theorem compressedBlock_sub_one (n : ι) :
    (compressedBlock K D n - 1 : K n →L[ℂ] K n) =
      (K n).orthogonalProjectionOnto ∘L (D n - (K n).starProjection) ∘L (K n).subtypeL := by
  ext1 v
  simp only [compressedBlock, sub_apply, ContinuousLinearMap.comp_apply,
    one_apply_eq_self, map_sub, Submodule.subtypeL_apply,
    Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem norm_compressedBlock_le (n : ι) : ‖compressedBlock K D n‖ ≤ ‖D n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  calc ‖compressedBlock K D n v‖ = ‖(K n).orthogonalProjectionOnto (D n (v : H))‖ := rfl
    _ ≤ ‖(K n).orthogonalProjectionOnto‖ * ‖D n (v : H)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖D n (v : H)‖ := mul_le_mul_of_nonneg_right
        (Submodule.orthogonalProjectionOnto_norm_le _) (norm_nonneg _)
    _ ≤ ‖D n‖ * ‖(v : H)‖ := by rw [one_mul]; exact (D n).le_opNorm _
    _ = ‖D n‖ * ‖v‖ := by rw [Submodule.coe_norm]

/-- **Corollary 5.5**: if `D_n - S_n` is compact then `B_n` is identity plus compact, hence
Fredholm: finite-dimensional kernel and closed range. -/
theorem compressedBlock_fredholm (hD : ∀ n, IsCompactOperator (D n - (K n).starProjection))
    (n : ι) :
    IsCompactOperator (compressedBlock K D n - 1 : K n →L[ℂ] K n) ∧
      IsFredholmOp (compressedBlock K D n) := by
  have hc : IsCompactOperator (compressedBlock K D n - 1 : K n →L[ℂ] K n) := by
    rw [compressedBlock_sub_one]
    exact ((hD n).comp_clm (K n).subtypeL).clm_comp (K n).orthogonalProjectionOnto
  refine ⟨hc, ?_⟩
  have := isFredholmOp_one_add_compact hc
  rwa [add_sub_cancel] at this

/-- **Corollary 5.5, `(5.17)`**: the source formation `⊕_n B_n` is upper semi-Fredholm exactly when
`inf_n γ(B_n) > 0` and `Σ_n dim ker B_n < ∞`. -/
theorem sourceShellGate [DecidableEq ι] {M : ℝ} (hM : 0 ≤ M) (hDM : ∀ n, ‖D n‖ ≤ M) :
    (IsClosed (Set.range (blockFormation (compressedBlock K D) hM
        fun n => (norm_compressedBlock_le K D n).trans (hDM n))) ∧
      FiniteDimensional ℂ (LinearMap.ker (blockFormation (compressedBlock K D) hM
        (fun n => (norm_compressedBlock_le K D n).trans (hDM n)) :
          lp (fun n => K n) 2 →ₗ[ℂ] lp (fun n => K n) 2))) ↔
      0 < ⨅ n, reducedMinModulus (compressedBlock K D n) ∧
        Cardinal.sum (fun n => Module.rank ℂ
          (LinearMap.ker (compressedBlock K D n : K n →ₗ[ℂ] K n))) < Cardinal.aleph0 :=
  blockFormation_upperSemiFredholm_iff _ _ _

end SourceShellGate

end GaloisForLFunctions.HTGeometry.TightFormation
