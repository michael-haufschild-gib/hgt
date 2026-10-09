import GaloisForLFunctions.HTGeometry.WienerHopfIndexTheorem

/-!
# Matrix Wiener–Hopf operators on `L²(ℝ)ⁿ`

* `l2BlockOp`, `l2BlockOpHom`: an operator matrix acts on the Hilbert direct sum `L²(ℝ)ⁿ`
  (`(Ax)_i = ∑_j A_{ij} x_j`); this is a unital `*`-homomorphism `Mₙ(B(L²)) → B(L²ⁿ)` with
  `‖A‖ ≤ ∑ ‖A_{ij}‖`, compact when all entries are compact, and continuous in the entries.
* `isFredholmOp_l2BlockOp_diagonal`: a block-diagonal operator with Fredholm blocks is Fredholm and
  its index is the sum of the indices (kernel and cokernel split as products).
* `idempotentToeplitz_mul`: in any ring with an idempotent `P`, `T_a T_b = T_{ab} - H₊(a) H₋(b)` for
  `T_a = P a P + (1 - P)`.
* `matWH`: the matrix Wiener–Hopf lift `P̂ C_U P̂ + (1 - P̂)` of a matrix symbol on the circle;
  its Hankel operators are block operators with compact entries, so by Atkinson the lift of a
  unitary symbol is Fredholm (`isFredholmOp_matWH`).
* `fredholmIndex_eq_of_continuous'`: the index is constant along norm-continuous paths of
  Fredholm operators on any Hilbert space.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Matrix
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Block operators on `L²(ℝ)ⁿ` -/

/-- `L²(ℝ)ⁿ`, the Hilbert direct sum of `n` copies of `L²(ℝ)`. -/
abbrev L2Vec (n : ℕ) : Type := PiLp 2 (fun _ : Fin n => L2Real)

variable {n : ℕ}

/-- The operator on `L²(ℝ)ⁿ` with operator matrix `A`. -/
def l2BlockOp (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) : L2Vec n →L[ℂ] L2Vec n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2Real)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j, (A i j).comp (PiLp.proj 2 (fun _ : Fin n => L2Real) j))

theorem l2BlockOp_apply (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) (x : L2Vec n)
    (i : Fin n) : l2BlockOp A x i = ∑ j, A i j (x j) := by
  simp [l2BlockOp]

theorem L2Vec.ext {x y : L2Vec n} (h : ∀ i, x i = y i) : x = y := PiLp.ext h

theorem l2BlockOp_mul (A B : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp (A * B) = l2BlockOp A * l2BlockOp B := by
  ext1 x
  refine L2Vec.ext fun i => ?_
  change l2BlockOp (A * B) x i = l2BlockOp A (l2BlockOp B x) i
  simp only [l2BlockOp_apply, Matrix.mul_apply, map_sum, FunLike.coe_sum, Finset.sum_apply,
    mul_apply_eq_comp]
  rw [Finset.sum_comm]

theorem l2BlockOp_one : l2BlockOp (1 : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) = 1 := by
  ext1 x
  refine L2Vec.ext fun i => ?_
  rw [l2BlockOp_apply, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq]
    rfl
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj)]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem l2BlockOp_add (A B : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp (A + B) = l2BlockOp A + l2BlockOp B := by
  ext1 x
  refine L2Vec.ext fun i => ?_
  change l2BlockOp (A + B) x i = (l2BlockOp A x + l2BlockOp B x) i
  rw [PiLp.add_apply, l2BlockOp_apply, l2BlockOp_apply, l2BlockOp_apply, ← Finset.sum_add_distrib]
  rfl

theorem l2BlockOp_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp (c • A) = c • l2BlockOp A := by
  ext1 x
  refine L2Vec.ext fun i => ?_
  change l2BlockOp (c • A) x i = (c • l2BlockOp A x) i
  rw [PiLp.smul_apply, l2BlockOp_apply, l2BlockOp_apply, Finset.smul_sum]
  rfl

theorem l2BlockOp_zero : l2BlockOp (0 : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) = 0 := by
  ext1 x
  refine L2Vec.ext fun i => ?_
  rw [l2BlockOp_apply]
  simp

theorem l2BlockOp_star (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp (star A) = ContinuousLinearMap.adjoint (l2BlockOp A) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [l2BlockOp_apply, Matrix.star_apply, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- **Operator matrices act on `L²(ℝ)ⁿ`**: a unital `*`-homomorphism `Mₙ(B(L²)) → B(L²ⁿ)`. -/
def l2BlockOpHom : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real) →⋆ₐ[ℂ] (L2Vec n →L[ℂ] L2Vec n) where
  toFun := l2BlockOp
  map_one' := l2BlockOp_one
  map_mul' := l2BlockOp_mul
  map_zero' := l2BlockOp_zero
  map_add' := l2BlockOp_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, l2BlockOp_smul, l2BlockOp_one, Algebra.algebraMap_eq_smul_one]
  map_star' A := by rw [l2BlockOp_star, ContinuousLinearMap.star_eq_adjoint]

/-- The inclusion of the `i`-th summand of `L²(ℝ)ⁿ`. -/
def l2VecIncl (i : Fin n) : L2Real →L[ℂ] L2Vec n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2Real)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => L2Real) i)

theorem l2VecIncl_apply (i : Fin n) (v : L2Real) (k : Fin n) :
    l2VecIncl i v k = Pi.single (M := fun _ : Fin n => L2Real) i v k := rfl

theorem norm_l2VecIncl_le (i : Fin n) : ‖l2VecIncl i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact (PiLp.norm_single 2 (fun _ : Fin n => L2Real) i v).le

theorem norm_l2VecProj_le (j : Fin n) : ‖PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact PiLp.norm_apply_le x j

theorem l2BlockOp_eq_sum (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp A = ∑ i, ∑ j, (l2VecIncl i).comp ((A i j).comp
      (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j)) := by
  ext1 x
  refine L2Vec.ext fun k => ?_
  have hk : ∀ y : L2Vec n, y k = PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) k y :=
    fun _ => rfl
  rw [l2BlockOp_apply, hk]
  simp only [FunLike.coe_sum, Finset.sum_apply, map_sum, ContinuousLinearMap.coe_comp,
    Function.comp_apply, PiLp.proj_apply]
  simp only [l2VecIncl_apply, Pi.single_apply]
  simp

theorem norm_l2BlockOp_le (A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    ‖l2BlockOp A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  rw [l2BlockOp_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  calc ‖(l2VecIncl i).comp ((A i j).comp (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j))‖
      ≤ ‖l2VecIncl i‖ * (‖A i j‖ * ‖PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A i j‖ * 1) := by
        gcongr
        · exact norm_l2VecIncl_le i
        · exact norm_l2VecProj_le j
    _ = ‖A i j‖ := by ring

/-- An operator matrix with compact entries is compact. -/
theorem isCompactOperator_l2BlockOp {A : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)}
    (hA : ∀ i j, IsCompactOperator (A i j)) : IsCompactOperator (l2BlockOp A) := by
  rw [l2BlockOp_eq_sum]
  have hmem : ∀ i j, (l2VecIncl i).comp ((A i j).comp
      (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j)) ∈
        compactOperator (RingHom.id ℂ) (L2Vec n) (L2Vec n) :=
    fun i j => show IsCompactOperator ((l2VecIncl i).comp ((A i j).comp
      (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j))) from
      ((hA i j).comp_clm (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j)).clm_comp (l2VecIncl i)
  exact (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => hmem i j :
    _ ∈ compactOperator (RingHom.id ℂ) (L2Vec n) (L2Vec n))

theorem continuous_l2BlockOp : Continuous (l2BlockOp (n := n)) := by
  have h : (l2BlockOp (n := n)) = fun A => ∑ i, ∑ j, (l2VecIncl i).comp ((A i j).comp
      (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) j)) := funext l2BlockOp_eq_sum
  rw [h]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.clm_comp
    (((continuous_apply j).comp (continuous_apply i)).clm_comp continuous_const)

/-! ## Block-diagonal operators: the index is additive -/

theorem l2BlockOp_diagonal_apply (d : Fin n → (L2Real →L[ℂ] L2Real)) (x : L2Vec n) (i : Fin n) :
    l2BlockOp (Matrix.diagonal d) x i = d i (x i) := by
  rw [l2BlockOp_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

section BlockDiagonal

variable (d : Fin n → (L2Real →L[ℂ] L2Real))

/-- The kernel of a block-diagonal operator is the product of the kernels. -/
noncomputable def blockDiagKerEquiv :
    LinearMap.ker ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) : L2Vec n →ₗ[ℂ] L2Vec n)
      ≃ₗ[ℂ] (∀ i, LinearMap.ker ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real)) where
  toFun x i := ⟨(x : L2Vec n) i, by
    have h := congrArg (fun y : L2Vec n => y i) (LinearMap.mem_ker.mp x.2)
    rw [LinearMap.mem_ker]
    change d i ((x : L2Vec n) i) = 0
    rw [← l2BlockOp_diagonal_apply]
    exact h⟩
  invFun y := ⟨WithLp.toLp 2 (fun i => (y i : L2Real)), by
    rw [LinearMap.mem_ker]
    refine L2Vec.ext fun i => ?_
    change l2BlockOp (Matrix.diagonal d) _ i = 0
    rw [l2BlockOp_diagonal_apply]
    exact LinearMap.mem_ker.mp (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem mem_range_l2BlockOp_diagonal_iff (y : L2Vec n) :
    y ∈ LinearMap.range ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) :
      L2Vec n →ₗ[ℂ] L2Vec n) ↔
      ∀ i, y i ∈ LinearMap.range ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real) := by
  constructor
  · rintro ⟨x, rfl⟩ i
    exact ⟨x i, (l2BlockOp_diagonal_apply d x i).symm⟩
  · intro h
    choose x hx using h
    refine ⟨WithLp.toLp 2 x, L2Vec.ext fun i => ?_⟩
    change l2BlockOp (Matrix.diagonal d) _ i = y i
    rw [l2BlockOp_diagonal_apply]
    exact hx i

/-- The quotient map onto the product of the cokernels. -/
def blockDiagCokerMap : L2Vec n →ₗ[ℂ]
    (∀ i, L2Real ⧸ LinearMap.range ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real)) :=
  LinearMap.pi fun i => (LinearMap.range ((d i : L2Real →L[ℂ] L2Real) :
    L2Real →ₗ[ℂ] L2Real)).mkQ ∘ₗ (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) i : L2Vec n →ₗ[ℂ] L2Real)

theorem blockDiagCokerMap_surjective : Function.Surjective (blockDiagCokerMap d) := by
  intro z
  choose w hw using fun i => Submodule.mkQ_surjective _ (z i)
  refine ⟨WithLp.toLp 2 w, funext fun i => ?_⟩
  exact hw i

theorem ker_blockDiagCokerMap :
    LinearMap.ker (blockDiagCokerMap d) =
      LinearMap.range ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) :
        L2Vec n →ₗ[ℂ] L2Vec n) := by
  ext y
  rw [mem_range_l2BlockOp_diagonal_iff, LinearMap.mem_ker]
  constructor
  · intro h i
    have := congrFun h i
    exact (Submodule.Quotient.mk_eq_zero _).mp this
  · intro h
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h i)

/-- The cokernel of a block-diagonal operator is the product of the cokernels. -/
def blockDiagCokerEquiv :
    (L2Vec n ⧸ LinearMap.range ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) :
      L2Vec n →ₗ[ℂ] L2Vec n)) ≃ₗ[ℂ]
      (∀ i, L2Real ⧸ LinearMap.range ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real)) :=
  (Submodule.quotEquivOfEq _ _ (ker_blockDiagCokerMap d).symm).trans
    ((blockDiagCokerMap d).quotKerEquivOfSurjective (blockDiagCokerMap_surjective d))

/-- **Block-diagonal operators**: Fredholm with index the sum of the indices. -/
theorem isFredholmOp_l2BlockOp_diagonal {d : Fin n → (L2Real →L[ℂ] L2Real)}
    (hd : ∀ i, IsFredholmOp (d i)) :
    IsFredholmOp (l2BlockOp (Matrix.diagonal d)) ∧
      fredholmIndex (l2BlockOp (Matrix.diagonal d)) = ∑ i, fredholmIndex (d i) := by
  haveI : ∀ i, FiniteDimensional ℂ
      (LinearMap.ker ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real)) :=
    fun i => (hd i).finiteDimensional_ker
  haveI : ∀ i, FiniteDimensional ℂ
      (L2Real ⧸ LinearMap.range ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real)) :=
    fun i => (hd i).finiteDimensional_coker
  have hK := (blockDiagKerEquiv d).symm.finiteDimensional
  have hC := (blockDiagCokerEquiv d).symm.finiteDimensional
  have hclosed : IsClosed (LinearMap.range ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) :
      L2Vec n →ₗ[ℂ] L2Vec n) : Set (L2Vec n)) := by
    have hset : (LinearMap.range ((l2BlockOp (Matrix.diagonal d) : L2Vec n →L[ℂ] L2Vec n) :
        L2Vec n →ₗ[ℂ] L2Vec n) : Set (L2Vec n)) =
        ⋂ i, (PiLp.proj 2 (fun _ : Fin n => L2Real) (𝕜 := ℂ) i) ⁻¹'
          (LinearMap.range ((d i : L2Real →L[ℂ] L2Real) : L2Real →ₗ[ℂ] L2Real) : Set L2Real) := by
      ext y
      simp only [SetLike.mem_coe, mem_iInter, mem_preimage, PiLp.proj_apply]
      exact mem_range_l2BlockOp_diagonal_iff d y
    rw [hset]
    exact isClosed_iInter fun i => (hd i).isClosed_range.preimage (PiLp.proj _ _ i).continuous
  refine ⟨⟨hK, hclosed, hC⟩, ?_⟩
  rw [fredholmIndex, (blockDiagKerEquiv d).finrank_eq, (blockDiagCokerEquiv d).finrank_eq,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [fredholmIndex]
  push_cast
  rw [Finset.sum_sub_distrib]

end BlockDiagonal

/-! ## Toeplitz algebra in a ring with an idempotent -/

section Idempotent

variable {R : Type*} [Ring R] {P : R} (hP : P * P = P)
include hP

theorem idem_mul_one_sub : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]

theorem one_sub_mul_idem : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]

theorem one_sub_idem_mul_self : (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, one_mul, mul_sub, mul_one, hP, sub_self, sub_zero]

/-- `T_a T_b = T_{ab} - H₊(a) H₋(b)` for `T_a = P a P + (1 - P)`. -/
theorem idempotentToeplitz_mul (a b : R) :
    (P * a * P + (1 - P)) * (P * b * P + (1 - P)) =
      P * (a * b) * P + (1 - P) - P * a * (1 - P) * ((1 - P) * b * P) := by
  have h1 : P * a * P * (P * b * P) = P * a * P * b * P := by
    rw [show P * a * P * (P * b * P) = P * a * (P * P) * b * P by noncomm_ring, hP]
  have h2 : P * a * P * (1 - P) = 0 := by
    rw [mul_assoc (P * a) P, idem_mul_one_sub hP, mul_zero]
  have h3 : (1 - P) * (P * b * P) = 0 := by
    rw [← mul_assoc, ← mul_assoc, one_sub_mul_idem hP, zero_mul, zero_mul]
  have h4 : P * a * (1 - P) * ((1 - P) * b * P) = P * a * (1 - P) * b * P := by
    rw [show P * a * (1 - P) * ((1 - P) * b * P) = P * a * ((1 - P) * (1 - P)) * b * P by
      noncomm_ring, one_sub_idem_mul_self hP]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, one_sub_idem_mul_self hP, h4]
  noncomm_ring

end Idempotent

/-! ## Homotopy invariance of the index on any Hilbert space -/

theorem fredholmIndex_eq_of_continuous' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {T : ℝ → E →L[ℂ] E} (hT : Continuous T) (hF : ∀ t, IsFredholmOp (T t))
    (a b : ℝ) : fredholmIndex (T a) = fredholmIndex (T b) := by
  have hloc : IsLocallyConstant (fun t => fredholmIndex (T t)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨δ, hδ, hstab⟩ := (hF t₀).exists_stable
    have hev : ∀ᶠ t in nhds t₀, ‖T t - T t₀‖ < δ :=
      ((Metric.tendsto_nhds.mp (hT.tendsto t₀)) δ hδ).mono fun t ht => by
        rwa [dist_eq_norm] at ht
    filter_upwards [hev] with t ht
    have h := (hstab _ ht).2
    rwa [add_sub_cancel] at h
  exact hloc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ a) (Set.mem_univ b)

/-! ## Matrix symbols and matrix Wiener–Hopf operators -/

/-- The block multiplier `C_U` of a matrix symbol on the circle. -/
def matCircle (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) : L2Vec n →L[ℂ] L2Vec n :=
  l2BlockOp (U.map circleMultiplier)

theorem matCircle_mul (U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    matCircle (U * V) = matCircle U * matCircle V := by
  rw [matCircle, matCircle, matCircle, ← l2BlockOp_mul]
  congr 1
  exact Matrix.map_mul (f := (circleMultiplierHom : C(UnitCircle, ℂ) →+* (L2Real →L[ℂ] L2Real)))

theorem matCircle_star (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    matCircle (star U) = star (matCircle U) := by
  rw [matCircle, matCircle, ContinuousLinearMap.star_eq_adjoint, ← l2BlockOp_star]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.star_apply, circleMultiplier_star]

theorem matCircle_one : matCircle (1 : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) = 1 := by
  rw [matCircle, ← l2BlockOp_one]
  congr 1
  exact Matrix.map_one _ (map_zero circleMultiplierHom) circleMultiplier_one

theorem l2BlockOp_sub (A B : Matrix (Fin n) (Fin n) (L2Real →L[ℂ] L2Real)) :
    l2BlockOp (A - B) = l2BlockOp A - l2BlockOp B := map_sub l2BlockOpHom A B

theorem continuous_matCircle : Continuous (matCircle (n := n)) :=
  continuous_l2BlockOp.comp (continuous_pi fun i => continuous_pi fun j =>
    continuous_circleMultiplier.comp ((continuous_apply j).comp (continuous_apply i)))

/-- The half-line projection on every summand of `L²(ℝ)ⁿ`. -/
def halfProjVec : L2Vec n →L[ℂ] L2Vec n := l2BlockOp (Matrix.diagonal fun _ => halfProj)

theorem halfProjVec_mul_self : halfProjVec * halfProjVec = (halfProjVec : L2Vec n →L[ℂ] L2Vec n) := by
  rw [halfProjVec, ← l2BlockOp_mul, Matrix.diagonal_mul_diagonal]
  simp only [halfProj_mul_self]

theorem one_sub_halfProjVec :
    1 - halfProjVec = l2BlockOp (Matrix.diagonal fun _ : Fin n => (1 : L2Real →L[ℂ] L2Real) - halfProj) := by
  rw [halfProjVec, ← l2BlockOp_one, ← Matrix.diagonal_one, ← l2BlockOp_sub, Matrix.diagonal_sub]

theorem diagonal_mul_mul_diagonal_apply {R : Type*} [Semiring R] (d e : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Matrix.diagonal d * M * Matrix.diagonal e) i j = d i * M i j * e j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The matrix Wiener–Hopf lift** `T_U = P̂ C_U P̂ + (1 - P̂)` on `L²(ℝ)ⁿ`. -/
def matWH (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) : L2Vec n →L[ℂ] L2Vec n :=
  halfProjVec * matCircle U * halfProjVec + (1 - halfProjVec)

theorem matHankelPlus_eq (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    halfProjVec * matCircle U * (1 - halfProjVec) = l2BlockOp fun i j => hankelPlus (U i j) := by
  rw [one_sub_halfProjVec, halfProjVec, matCircle, ← l2BlockOp_mul, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [diagonal_mul_mul_diagonal_apply, Matrix.map_apply, hankelPlus]

theorem matHankelMinus_eq (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    (1 - halfProjVec) * matCircle U * halfProjVec = l2BlockOp fun i j => hankelMinus (U i j) := by
  rw [one_sub_halfProjVec, halfProjVec, matCircle, ← l2BlockOp_mul, ← l2BlockOp_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [diagonal_mul_mul_diagonal_apply, Matrix.map_apply, hankelMinus]

theorem isCompactOperator_matHankelPlus (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    IsCompactOperator ⇑(halfProjVec * matCircle U * (1 - halfProjVec) : L2Vec n →L[ℂ] L2Vec n) := by
  rw [matHankelPlus_eq]
  exact isCompactOperator_l2BlockOp fun i j => (compactHankel (U i j)).1

theorem isCompactOperator_matHankelMinus (U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    IsCompactOperator ⇑((1 - halfProjVec) * matCircle U * halfProjVec : L2Vec n →L[ℂ] L2Vec n) := by
  rw [matHankelMinus_eq]
  exact isCompactOperator_l2BlockOp fun i j => (compactHankel (U i j)).2

theorem matWH_mul (U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) :
    matWH U * matWH V = matWH (U * V) -
      halfProjVec * matCircle U * (1 - halfProjVec) * ((1 - halfProjVec) * matCircle V * halfProjVec) := by
  rw [matWH, matWH, matWH, idempotentToeplitz_mul halfProjVec_mul_self, matCircle_mul]

theorem matWH_one : matWH (1 : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)) = 1 := by
  rw [matWH, matCircle_one, mul_one, halfProjVec_mul_self, add_sub_cancel]

theorem continuous_matWH : Continuous (matWH (n := n)) :=
  ((continuous_const.mul continuous_matCircle).mul continuous_const).add continuous_const

theorem isCompactOperator_vec_mul_left {A K : L2Vec n →L[ℂ] L2Vec n}
    (hK : IsCompactOperator ⇑K) : IsCompactOperator ⇑(A * K) := hK.clm_comp A

theorem isCompactOperator_vec_mul_right {A K : L2Vec n →L[ℂ] L2Vec n}
    (hK : IsCompactOperator ⇑K) : IsCompactOperator ⇑(K * A) := hK.comp_clm A

theorem isCompactOperator_matWH_mul_sub_one (U V : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ))
    (hUV : U * V = 1) : IsCompactOperator ⇑(matWH U * matWH V - 1) := by
  have h : matWH U * matWH V - 1 = -((halfProjVec * matCircle U * (1 - halfProjVec)) *
      ((1 - halfProjVec) * matCircle V * halfProjVec)) := by
    rw [matWH_mul, hUV, matWH_one, sub_sub_cancel_left]
  rw [h]
  exact (isCompactOperator_vec_mul_left (isCompactOperator_matHankelMinus V)).neg

/-- **The matrix Wiener–Hopf lift of a unitary symbol is Fredholm** (Atkinson). -/
theorem isFredholmOp_matWH {U : Matrix (Fin n) (Fin n) C(UnitCircle, ℂ)} (hU : star U * U = 1) :
    IsFredholmOp (matWH U) :=
  isFredholmOp_of_inverse_mod_compact (S := matWH (star U))
    (isCompactOperator_matWH_mul_sub_one _ _ hU)
    (isCompactOperator_matWH_mul_sub_one _ _ (mul_eq_one_comm.mp hU))

end GaloisForLFunctions.HTGeometry
