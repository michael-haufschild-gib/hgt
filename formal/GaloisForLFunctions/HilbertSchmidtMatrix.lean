/-
# The kernel ↔ operator bridge on `ℓ²(ι)`

The coordinate model (`HilbertSchmidt`: square-summable kernels `K : ι × ι → ℂ`) and the
coordinate-free model (`ContinuousLinearMap.IsHilbertSchmidt`: operators with square-summable
values on a Hilbert basis) describe the same objects.  This file constructs the dictionary on the
space `ℓ²(ι)`:

* `lpBasis` — the canonical Hilbert basis of `ℓ²(ι)`, `lpBasis ι i = lp.single 2 i 1`.
* `toOperator` — a Hilbert–Schmidt kernel `K` acts on `ℓ²(ι)` by `(K·f)(i) = ∑ⱼ K(i,j)·f(j)`,
  a bounded operator with `‖K·‖ ≤ ‖K‖_HS` (`norm_toOperator_le`).
* `toOperator_single`, `matrixOf`, `matrixOf_toOperator`, `toOperator_matrixOf` — the operator's
  matrix against the canonical basis is `K`, and a Hilbert–Schmidt operator is recovered from its
  matrix (agreement on the basis extends over its dense span).
* `isHilbertSchmidt_toOperator`, `isHS_matrixOf` — the two Hilbert–Schmidt conditions correspond:
  the kernel's column energies are the squared norms of the operator's basis values (Parseval).
* `hsNormSq_toOperator`, `hsInner_toOperator` — the Hilbert–Schmidt norm and inner product agree
  across the bridge; the operator-side pairing is computed on `lpBasis` by the basis-independence
  of `ContinuousLinearMap.hsInner`.
-/
import GaloisForLFunctions.HilbertSchmidt
import GaloisForLFunctions.HilbertSchmidtOperator

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace HilbertSchmidt

variable {ι : Type*}

/-- A square-summable coordinate family: the entries of an `ℓ²(ι)` element. -/
theorem summable_coe_sq (f : lp (fun _ : ι => ℂ) 2) : Summable (fun i => ‖f i‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp (lp.memℓp f)
  refine h.congr fun i => ?_
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `ℓ²(ι)` norm squared is the coordinate sum: `‖f‖² = ∑ᵢ ‖f i‖²`. -/
theorem lp_norm_sq_eq (f : lp (fun _ : ι => ℂ) 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f
  simp only [ENNReal.toReal_ofNat] at h
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [Real.rpow_natCast] at h
  exact h

/-- The canonical Hilbert basis of `ℓ²(ι)`: the basis whose representation is the identity. -/
noncomputable def lpBasis (ι : Type*) : HilbertBasis ι ℂ (lp (fun _ : ι => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem lpBasis_apply [DecidableEq ι] (i : ι) : lpBasis ι i = lp.single 2 i (1 : ℂ) := by
  have h := (lpBasis ι).repr_self i
  simpa [lpBasis] using h

/-- Row action of a Hilbert–Schmidt kernel on an `ℓ²` element converges: `ℓ²·ℓ² ⊆ ℓ¹`. -/
theorem summable_row_mul {K : ι × ι → ℂ} (hK : IsHS K) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    Summable fun j => K (i, j) * f j := by
  apply Summable.of_norm_bounded (g := fun j => (‖K (i, j)‖ ^ 2 + ‖f j‖ ^ 2) / 2)
  · exact ((isHS_row hK i).add (summable_coe_sq f)).div_const 2
  · intro j
    rw [norm_mul]
    nlinarith [sq_nonneg (‖K (i, j)‖ - ‖f j‖), norm_nonneg (K (i, j)), norm_nonneg (f j)]

private theorem memℓp_mulVec {K : ι × ι → ℂ} (hK : IsHS K) (f : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun i => ∑' j, K (i, j) * f j) 2 := by
  refine memℓp_of_sq ?_
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_row hK).mul_right (‖f‖ ^ 2))
  calc ‖∑' j, K (i, j) * f j‖ ^ 2
      ≤ (∑' j, ‖K (i, j)‖ ^ 2) * (∑' j, ‖f j‖ ^ 2) :=
        hsComp_entry_bound (isHS_row hK i) (summable_coe_sq f)
    _ = (∑' j, ‖K (i, j)‖ ^ 2) * ‖f‖ ^ 2 := by rw [lp_norm_sq_eq]

private theorem norm_mulVec_le {K : ι × ι → ℂ} (hK : IsHS K) (f : lp (fun _ : ι => ℂ) 2) :
    ‖(⟨fun i => ∑' j, K (i, j) * f j, memℓp_mulVec hK f⟩ : lp (fun _ : ι => ℂ) 2)‖
      ≤ hsNorm K * ‖f‖ := by
  set g : lp (fun _ : ι => ℂ) 2 := ⟨fun i => ∑' j, K (i, j) * f j, memℓp_mulVec hK f⟩ with hg
  have hgsq : ‖g‖ ^ 2 ≤ hsNormSq K * ‖f‖ ^ 2 := by
    rw [lp_norm_sq_eq g]
    calc ∑' i, ‖g i‖ ^ 2
        ≤ ∑' i, (∑' j, ‖K (i, j)‖ ^ 2) * ‖f‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun i => ?_) (summable_coe_sq g)
            ((summable_row hK).mul_right (‖f‖ ^ 2))
          calc ‖g i‖ ^ 2 = ‖∑' j, K (i, j) * f j‖ ^ 2 := rfl
            _ ≤ (∑' j, ‖K (i, j)‖ ^ 2) * (∑' j, ‖f j‖ ^ 2) :=
                hsComp_entry_bound (isHS_row hK i) (summable_coe_sq f)
            _ = (∑' j, ‖K (i, j)‖ ^ 2) * ‖f‖ ^ 2 := by rw [lp_norm_sq_eq]
      _ = (∑' i, ∑' j, ‖K (i, j)‖ ^ 2) * ‖f‖ ^ 2 := tsum_mul_right
      _ = hsNormSq K * ‖f‖ ^ 2 := by rw [tsum_row_normSq hK]
  have h1 : ‖g‖ ≤ Real.sqrt (hsNormSq K * ‖f‖ ^ 2) := by
    have h2 := Real.sqrt_le_sqrt hgsq
    rwa [Real.sqrt_sq (norm_nonneg g)] at h2
  calc ‖g‖ ≤ Real.sqrt (hsNormSq K * ‖f‖ ^ 2) := h1
    _ = Real.sqrt (hsNormSq K) * Real.sqrt (‖f‖ ^ 2) := Real.sqrt_mul (hsNormSq_nonneg K) _
    _ = hsNorm K * ‖f‖ := by rw [Real.sqrt_sq (norm_nonneg f), hsNorm]

/-- **The operator on `ℓ²(ι)` represented by a Hilbert–Schmidt kernel**:
`(K·f)(i) = ∑ⱼ K(i,j)·f(j)`, bounded with `‖K·‖ ≤ ‖K‖_HS`. -/
noncomputable def toOperator {K : ι × ι → ℂ} (hK : IsHS K) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => ∑' j, K (i, j) * f j, memℓp_mulVec hK f⟩
      map_add' := fun f g => by
        apply lp.ext
        funext i
        show ∑' j, K (i, j) * (f + g) j = (∑' j, K (i, j) * f j) + ∑' j, K (i, j) * g j
        rw [← (summable_row_mul hK f i).tsum_add (summable_row_mul hK g i)]
        refine tsum_congr fun j => ?_
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply lp.ext
        funext i
        show ∑' j, K (i, j) * (c • f) j = c • ∑' j, K (i, j) * f j
        rw [smul_eq_mul, ← tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    (hsNorm K)
    (fun f => norm_mulVec_le hK f)

theorem toOperator_apply {K : ι × ι → ℂ} (hK : IsHS K) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    toOperator hK f i = ∑' j, K (i, j) * f j := rfl

/-- The represented operator is bounded by the Hilbert–Schmidt norm of the kernel. -/
theorem norm_toOperator_le {K : ι × ι → ℂ} (hK : IsHS K) : ‖toOperator hK‖ ≤ hsNorm K :=
  LinearMap.mkContinuous_norm_le _ (hsNorm_nonneg K) _

/-- The represented operator sends the canonical basis to the kernel columns:
`(K·eⱼ)(i) = K(i,j)`. -/
theorem toOperator_single [DecidableEq ι] {K : ι × ι → ℂ} (hK : IsHS K) (i j : ι) :
    toOperator hK (lp.single 2 j (1 : ℂ)) i = K (i, j) := by
  rw [toOperator_apply,
    tsum_eq_single j (fun j' hj' => by rw [lp.single_apply_ne _ _ _ hj', mul_zero])]
  rw [lp.single_apply_self, mul_one]

/-- The squared norm of a represented column is the column energy of the kernel. -/
theorem norm_toOperator_single_sq [DecidableEq ι] {K : ι × ι → ℂ} (hK : IsHS K) (j : ι) :
    ‖toOperator hK (lp.single 2 j (1 : ℂ))‖ ^ 2 = ∑' i, ‖K (i, j)‖ ^ 2 := by
  rw [lp_norm_sq_eq]
  exact tsum_congr fun i => by rw [toOperator_single hK i j]

/-- **Kernel → operator, Hilbert–Schmidt side.**  A Hilbert–Schmidt kernel represents a genuinely
Hilbert–Schmidt operator on `ℓ²(ι)`: the operator's basis values have the kernel's column
energies, whose sum is `‖K‖²_HS`. -/
theorem isHilbertSchmidt_toOperator {K : ι × ι → ℂ} (hK : IsHS K) :
    (toOperator hK).IsHilbertSchmidt := by
  classical
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable (lpBasis ι) ?_
  refine (summable_col hK).congr fun j => ?_
  rw [lpBasis_apply, norm_toOperator_single_sq hK]

/-- The Hilbert–Schmidt norms agree across the bridge: `‖K·‖²_HS = ‖K‖²_HS`. -/
theorem hsNormSq_toOperator {K : ι × ι → ℂ} (hK : IsHS K) :
    ContinuousLinearMap.hsNormSq (toOperator hK) = hsNormSq K := by
  classical
  rw [ContinuousLinearMap.hsNormSq_eq (isHilbertSchmidt_toOperator hK) (lpBasis ι),
    ← tsum_col_normSq hK]
  exact tsum_congr fun j => by rw [lpBasis_apply, norm_toOperator_single_sq hK]

/-- The matrix of an operator on `ℓ²(ι)`: the columns are the operator values on the canonical
basis, `K_T(i, j) = (T eⱼ)(i)`. -/
noncomputable def matrixOf [DecidableEq ι]
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) : ι × ι → ℂ :=
  fun p => T (lp.single 2 p.2 (1 : ℂ)) p.1

/-- **Operator → kernel, Hilbert–Schmidt side.**  The matrix of a Hilbert–Schmidt operator on
`ℓ²(ι)` is a Hilbert–Schmidt kernel: each column is square-summable, and the column energies are
`‖T eⱼ‖²` by Parseval, summable since `T` is Hilbert–Schmidt. -/
theorem isHS_matrixOf [DecidableEq ι] {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hT : T.IsHilbertSchmidt) : IsHS (matrixOf T) := by
  have hcols : ∀ j, Summable (fun i => ‖T (lp.single 2 j (1 : ℂ)) i‖ ^ 2) := fun j =>
    summable_coe_sq (T (lp.single 2 j (1 : ℂ)))
  have henergy : Summable (fun j => ∑' i, ‖T (lp.single 2 j (1 : ℂ)) i‖ ^ 2) := by
    refine (hT.summable (lpBasis ι)).congr fun j => ?_
    rw [lpBasis_apply, lp_norm_sq_eq]
  have hswap : Summable (fun q : ι × ι => ‖T (lp.single 2 q.1 (1 : ℂ)) q.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun q => by positivity)]
    exact ⟨fun j => (hcols j).congr fun i => rfl,
      henergy.congr fun j => tsum_congr fun i => rfl⟩
  have h := (Equiv.prodComm ι ι).summable_iff.mpr hswap
  exact h.congr fun p => rfl

/-- Round trip kernel → operator → kernel: the matrix of `toOperator hK` is `K`. -/
theorem matrixOf_toOperator [DecidableEq ι] {K : ι × ι → ℂ} (hK : IsHS K) :
    matrixOf (toOperator hK) = K := by
  funext p
  show toOperator hK (lp.single 2 p.2 (1 : ℂ)) p.1 = K p
  rw [toOperator_single hK p.1 p.2]

/-- **Round trip operator → kernel → operator.**  A Hilbert–Schmidt operator on `ℓ²(ι)` is
recovered from its matrix: both operators agree on the canonical basis, whose span is dense. -/
theorem toOperator_matrixOf [DecidableEq ι]
    {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2} (hT : T.IsHilbertSchmidt) :
    toOperator (isHS_matrixOf hT) = T := by
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (lpBasis ι).dense_span) ?_
  rintro x ⟨j, rfl⟩
  rw [lpBasis_apply]
  apply lp.ext
  funext i
  show toOperator (isHS_matrixOf hT) (lp.single 2 j (1 : ℂ)) i = T (lp.single 2 j (1 : ℂ)) i
  rw [toOperator_single (isHS_matrixOf hT) i j]
  rfl

/-- **The Hilbert–Schmidt inner products agree across the bridge.**
`⟨K·, L·⟩_HS = ⟨K, L⟩_HS`: compute the operator pairing on the canonical basis — legitimate by
its basis-independence — where each column contributes `∑ᵢ conj(K(i,j))·L(i,j)`, and collapse the
iterated sum. -/
theorem hsInner_toOperator [DecidableEq ι] {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    ContinuousLinearMap.hsInner (toOperator hK) (toOperator hL) = hsInner K L := by
  rw [ContinuousLinearMap.hsInner_eq_tsum_basis (isHilbertSchmidt_toOperator hK)
    (isHilbertSchmidt_toOperator hL) (lpBasis ι)]
  have hcol : ∀ j, inner ℂ (toOperator hK (lpBasis ι j)) (toOperator hL (lpBasis ι j))
      = ∑' i, (starRingEnd ℂ) (K (i, j)) * L (i, j) := by
    intro j
    rw [lpBasis_apply, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    rw [RCLike.inner_apply, toOperator_single hK i j, toOperator_single hL i j]
    exact mul_comm _ _
  rw [tsum_congr hcol]
  have hswap : Summable (fun q : ι × ι => (starRingEnd ℂ) (K (q.2, q.1)) * L (q.2, q.1)) := by
    have h := (Equiv.prodComm ι ι).summable_iff.mpr (hsInner_summable hK hL)
    refine h.congr fun q => ?_
    simp only [Function.comp, Equiv.prodComm_apply, Prod.swap]
  calc ∑' j, ∑' i, (starRingEnd ℂ) (K (i, j)) * L (i, j)
      = ∑' q : ι × ι, (starRingEnd ℂ) (K (q.2, q.1)) * L (q.2, q.1) := (hswap.tsum_prod).symm
    _ = hsInner K L := by
        rw [hsInner, ← (Equiv.prodComm ι ι).tsum_eq (fun p => (starRingEnd ℂ) (K p) * L p)]
        refine tsum_congr fun q => ?_
        simp only [Equiv.prodComm_apply, Prod.swap]

end HilbertSchmidt
