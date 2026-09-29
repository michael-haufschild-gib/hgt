import GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint

/-!
# The theta-completed Plücker singular sandwich

Fix primes `p < q`.  Let `M_e` be the physical `4 × 4` Plücker spectral matrix of the packet
`(p,e),(p,e+1),(q,e),(q,e+1)`.  It is positive semidefinite of rank three, so `τ_e = tr M_e > 0`
and `A_e = M_e/τ_e` is positive with trace one.  On `H = ℓ²(ℕ × Fin 4) = ⊕_e ℂ⁴` put
`B = ⊕_e π_e A_e`, `Θ = ⊕_e w_e A_e` and `S = ⊕_e s_e I₄` on its maximal domain, where `π`, `w` and
`s = √(w/π)` are the physical depth law, the theta first-exit law and the formation half-density.

* `B` and `Θ` are positive and Schatten-one with trace and trace norm one.
* `S` is positive, self-adjoint, closed and unbounded, and `Dom S = Dom(N+1)` with equivalent graph
  norms.
* On the finitely supported core `S B S = Θ`; the core operator is closable with closure `Θ`.
* `S` is the unique nonnegative block-scalar operator with this property.
* Every block of `Θ` is `w_e A_e`, of rank three, with one-dimensional kernel spanned by the
  Stokes-gap vector `((e+1)I_p, (e+2)I_p, (e+1)I_q, (e+2)I_q)` and a nonzero off-diagonal entry;
  consecutive block kernels differ.
* `Θ` is not `diag(w) ⊗ A` for any fixed `4 × 4` matrix `A`.
-/

open Filter Topology Set
open scoped ENNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower _root_.RHTower.HedenmalmThetaSource

/-! ## Real positive-semidefinite blocks -/

section RealBlocks

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem posSemidef_real_apply_symm {A : Matrix n n ℝ} (hA : A.PosSemidef) (i j : n) :
    A j i = A i j := by
  simpa using hA.1.apply i j

theorem posSemidef_real_quadratic_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (i j : n)
    (c : ℝ) : 0 ≤ A i i + c * (A i j + A j i) + c ^ 2 * A j j := by
  have := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + c • Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, single_dotProduct,
    smul_eq_mul, one_mul, Matrix.col_apply] at this
  linarith [this]

/-- Every entry of a real positive-semidefinite matrix is bounded by its trace. -/
theorem posSemidef_real_abs_apply_le_trace {A : Matrix n n ℝ} (hA : A.PosSemidef) (i j : n) :
    |A i j| ≤ A.trace := by
  have hs := posSemidef_real_apply_symm hA i j
  have h1 := posSemidef_real_quadratic_nonneg hA i j 1
  have h2 := posSemidef_real_quadratic_nonneg hA i j (-1)
  rw [hs] at h1 h2
  have hd : ∀ k, 0 ≤ A k k := fun k => hA.diag_nonneg
  have hab : |A i j| ≤ (A i i + A j j) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have htr : A.trace = ∑ k, A k k := rfl
  have hii : A i i ≤ A.trace := by
    rw [htr]
    exact Finset.single_le_sum (fun k _ => hd k) (Finset.mem_univ i)
  by_cases hij : i = j
  · subst hij
    linarith
  · have hpair : A i i + A j j ≤ A.trace := by
      rw [htr, ← Finset.sum_pair hij (f := fun k => A k k)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => hd k
    linarith [hd i, hd j]

omit [DecidableEq n] in
/-- The real quadratic form of a real positive-semidefinite matrix on a complex vector. -/
theorem posSemidef_real_re_quadratic_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (v : n → ℂ) : 0 ≤ (∑ i, ∑ j, conj (v i) * (A i j : ℂ) * v j).re := by
  have hr := hA.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have hi := hA.dotProduct_mulVec_nonneg (fun i => (v i).im)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum] at hr hi
  have key : (∑ i, ∑ j, conj (v i) * (A i j : ℂ) * v j).re =
      (∑ i, ∑ j, (v i).re * (A i j * (v j).re)) +
        ∑ i, ∑ j, (v i).im * (A i j * (v j).im) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact add_nonneg hr hi

end RealBlocks

/-! ## Depth-block operators on `ℓ²(ℕ × Fin d)` -/

section DepthBlocks

variable {d : ℕ}

/-- `(M x)_{(e,i)} = ∑_j M_e(i,j) x_{(e,j)}`. -/
def depthBlockApply (M : ℕ → Matrix (Fin d) (Fin d) ℝ) (x : ℕ × Fin d → ℂ) : ℕ × Fin d → ℂ :=
  fun z => ∑ j, (M z.1 z.2 j : ℂ) * x (z.1, j)

theorem summable_comp_fst_of_summable {g : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hg : Summable g) :
    Summable (fun z : ℕ × Fin d => g z.1) := by
  refine (summable_prod_of_nonneg fun z => hg0 z.1).2 ⟨fun _ => Summable.of_finite, ?_⟩
  simpa [tsum_fintype] using hg.mul_left (d : ℝ)

theorem tsum_comp_fst {g : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hg : Summable g) :
    ∑' z : ℕ × Fin d, g z.1 = d * ∑' e, g e := by
  rw [(summable_comp_fst_of_summable hg0 hg).tsum_prod, ← tsum_mul_left]
  simp [tsum_fintype]

theorem summable_blockEnergy (x : DiagonalL2 (ℕ × Fin d)) :
    Summable (fun e : ℕ => ∑ j, ‖x (e, j)‖ ^ 2) := by
  simpa [tsum_fintype] using (HilbertSchmidt.summable_coe_sq x).prod

theorem tsum_blockEnergy (x : DiagonalL2 (ℕ × Fin d)) :
    ∑' e : ℕ, ∑ j, ‖x (e, j)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq, (HilbertSchmidt.summable_coe_sq x).tsum_prod]
  simp [tsum_fintype]

variable {M : ℕ → Matrix (Fin d) (Fin d) ℝ} {C : ℝ} (hM : ∀ e i j, |M e i j| ≤ C)
include hM

theorem norm_depthBlockApply_sq_le (x : ℕ × Fin d → ℂ) (z : ℕ × Fin d) :
    ‖depthBlockApply M x z‖ ^ 2 ≤ d * C ^ 2 * ∑ j, ‖x (z.1, j)‖ ^ 2 := by
  have h1 : ‖depthBlockApply M x z‖ ≤ ∑ j, C * ‖x (z.1, j)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _ _ _) (norm_nonneg _)
  calc ‖depthBlockApply M x z‖ ^ 2 ≤ (∑ j, C * ‖x (z.1, j)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Finset.univ : Finset (Fin d)).card * ∑ j, (C * ‖x (z.1, j)‖) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ = d * C ^ 2 * ∑ j, ‖x (z.1, j)‖ ^ 2 := by
        rw [Finset.card_univ, Fintype.card_fin]
        simp only [mul_pow]
        rw [← Finset.mul_sum]
        ring

theorem memℓp_depthBlockApply (x : DiagonalL2 (ℕ × Fin d)) :
    Memℓp (depthBlockApply M x) 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_)
    ((summable_comp_fst_of_summable (fun e => Finset.sum_nonneg fun j _ => by positivity)
      (summable_blockEnergy x)).mul_left ((d : ℝ) * C ^ 2))
  rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact norm_depthBlockApply_sq_le hM x z

theorem norm_depthBlockApply_le (x : DiagonalL2 (ℕ × Fin d)) :
    ‖(⟨depthBlockApply M x, memℓp_depthBlockApply hM x⟩ : DiagonalL2 (ℕ × Fin d))‖ ≤
      d * |C| * ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (by positivity) ?_
  have hg0 : ∀ e, 0 ≤ ∑ j, ‖x (e, j)‖ ^ 2 := fun e => Finset.sum_nonneg fun j _ => by positivity
  have hS := summable_comp_fst_of_summable (d := d) hg0 (summable_blockEnergy x)
  calc ∑' z, ‖depthBlockApply M x z‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' z : ℕ × Fin d, (d * C ^ 2) * ∑ j, ‖x (z.1, j)‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun z => ?_)
          ((memℓp_gen_iff h2).1 (memℓp_depthBlockApply hM x)) (hS.mul_left _)
        rw [ENNReal.toReal_ofNat, Real.rpow_two]
        exact norm_depthBlockApply_sq_le hM x z
    _ = (d * |C| * ‖x‖) ^ (2 : ℝ≥0∞).toReal := by
        rw [tsum_mul_left, tsum_comp_fst hg0 (summable_blockEnergy x), tsum_blockEnergy,
          ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, mul_pow, sq_abs]
        ring

omit hM in
/-- The depth-block operator `x ↦ (∑_j M_e(i,j) x_{(e,j)})_{(e,i)}` for uniformly bounded real
blocks. -/
def depthBlockOperator (M : ℕ → Matrix (Fin d) (Fin d) ℝ) {C : ℝ}
    (hM : ∀ e i j, |M e i j| ≤ C) : DiagonalL2 (ℕ × Fin d) →L[ℂ] DiagonalL2 (ℕ × Fin d) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨depthBlockApply M x, memℓp_depthBlockApply hM x⟩
      map_add' := fun x y => by
        apply lp.ext
        funext z
        change depthBlockApply M ⇑(x + y) z = depthBlockApply M ⇑x z + depthBlockApply M ⇑y z
        simp only [depthBlockApply, lp.coeFn_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        apply lp.ext
        funext z
        change depthBlockApply M ⇑(c • x) z = c * depthBlockApply M ⇑x z
        simp only [depthBlockApply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
    (d * |C|) (norm_depthBlockApply_le hM)

theorem depthBlockOperator_apply (x : DiagonalL2 (ℕ × Fin d)) (z : ℕ × Fin d) :
    depthBlockOperator M hM x z = ∑ j, (M z.1 z.2 j : ℂ) * x (z.1, j) := rfl

theorem depthBlockOperator_single (e : ℕ) (j : Fin d) (e' : ℕ) (i : Fin d) :
    depthBlockOperator M hM (lp.single 2 (e, j) 1) (e', i) =
      if e' = e then (M e i j : ℂ) else 0 := by
  rw [depthBlockOperator_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [lp.single_apply_ne _ _ _ (by simp [hk]), mul_zero]) (by simp),
      lp.single_apply_self, mul_one]
  · exact Finset.sum_eq_zero fun k _ => by rw [lp.single_apply_ne _ _ _ (by simp [h]), mul_zero]

/-- Matrix elements: `⟨δ_{(e,i)}, M δ_{(e',j)}⟩ = δ_{ee'} M_e(i,j)`. -/
theorem inner_single_depthBlockOperator_single (e : ℕ) (i : Fin d) (e' : ℕ) (j : Fin d) :
    ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin d)),
        depthBlockOperator M hM (lp.single 2 (e', j) 1)⟫_ℂ =
      if e = e' then (M e i j : ℂ) else 0 := by
  rw [lp.inner_single_left, depthBlockOperator_single]
  split_ifs with h
  · subst h
    simp
  · simp

theorem inner_depthBlockOperator (x y : DiagonalL2 (ℕ × Fin d)) :
    ⟪x, depthBlockOperator M hM y⟫_ℂ =
      ∑' e, ∑ i, ∑ j, conj (x (e, i)) * (M e i j : ℂ) * y (e, j) := by
  have hs : Summable (fun z : ℕ × Fin d => ⟪x z, depthBlockOperator M hM y z⟫_ℂ) :=
    lp.summable_inner _ _
  rw [lp.inner_eq_tsum, hs.tsum_prod]
  refine tsum_congr fun e => ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, depthBlockOperator_apply, Finset.sum_mul]
  dsimp only
  exact Finset.sum_congr rfl fun j _ => by ring

theorem summable_inner_depthBlockOperator (x y : DiagonalL2 (ℕ × Fin d)) :
    Summable (fun e => ∑ i, ∑ j, conj (x (e, i)) * (M e i j : ℂ) * y (e, j)) := by
  have hs : Summable (fun z : ℕ × Fin d => ⟪x z, depthBlockOperator M hM y z⟫_ℂ) :=
    lp.summable_inner _ _
  refine hs.prod.congr fun e => ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, depthBlockOperator_apply, Finset.sum_mul]
  dsimp only
  exact Finset.sum_congr rfl fun j _ => by ring

theorem depthBlockOperator_isSymmetric (hsym : ∀ e i j, M e j i = M e i j) :
    (depthBlockOperator M hM :
      DiagonalL2 (ℕ × Fin d) →ₗ[ℂ] DiagonalL2 (ℕ × Fin d)).IsSymmetric := by
  intro x y
  change ⟪depthBlockOperator M hM x, y⟫_ℂ = ⟪x, depthBlockOperator M hM y⟫_ℂ
  rw [← inner_conj_symm, inner_depthBlockOperator, inner_depthBlockOperator, Complex.conj_tsum]
  refine tsum_congr fun e => ?_
  simp only [map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym e i j]
  ring

/-- A depth-block operator with symmetric positive-semidefinite blocks is positive. -/
theorem depthBlockOperator_isPositive (hsym : ∀ e i j, M e j i = M e i j)
    (hpsd : ∀ e, (M e).PosSemidef) : (depthBlockOperator M hM).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨depthBlockOperator_isSymmetric hM hsym, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re,
    RCLike.re_to_complex, inner_depthBlockOperator,
    Complex.re_tsum (summable_inner_depthBlockOperator hM x x)]
  exact tsum_nonneg fun e => posSemidef_real_re_quadratic_nonneg (hpsd e) (fun k => x (e, k))

/-- A positive depth-block operator with summable block traces is Schatten-one, and its trace is the
sum of the block traces. -/
theorem depthBlockOperator_traceClass (hsym : ∀ e i j, M e j i = M e i j)
    (hpsd : ∀ e, (M e).PosSemidef) (hsum : Summable fun e => (M e).trace) :
    MemSchattenClass 1 (depthBlockOperator M hM) ∧
      (depthBlockOperator M hM).opTrace = ((∑' e, (M e).trace : ℝ) : ℂ) := by
  let b := HilbertSchmidt.lpBasis (ℕ × Fin d)
  have hdiag : ∀ z : ℕ × Fin d,
      ⟪b z, depthBlockOperator M hM (b z)⟫_ℂ = ((M z.1 z.2 z.2 : ℝ) : ℂ) := by
    rintro ⟨e, i⟩
    rw [HilbertSchmidt.lpBasis_apply, inner_single_depthBlockOperator_single, if_pos rfl]
  have hsumR : Summable fun z : ℕ × Fin d => M z.1 z.2 z.2 := by
    refine (summable_prod_of_nonneg fun z => (hpsd z.1).diag_nonneg).2
      ⟨fun _ => Summable.of_finite, ?_⟩
    simpa [tsum_fintype, Matrix.trace] using hsum
  have hsumC : Summable fun z => ⟪b z, depthBlockOperator M hM (b z)⟫_ℂ := by
    simp_rw [hdiag]
    exact Complex.summable_ofReal.2 hsumR
  have hS := memSchattenClass_one_of_isPositive_of_summable_diagonal b
    (depthBlockOperator_isPositive hM hsym hpsd) hsumC
  refine ⟨hS, ?_⟩
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS b]
  simp_rw [hdiag]
  rw [← Complex.ofReal_tsum, hsumR.tsum_prod]
  simp [tsum_fintype, Matrix.trace]

theorem depthBlockOperator_mem_core {x : DiagonalL2 (ℕ × Fin d)}
    (hx : (Function.support (x : ℕ × Fin d → ℂ)).Finite) :
    (Function.support (depthBlockOperator M hM x : ℕ × Fin d → ℂ)).Finite := by
  refine ((hx.image Prod.fst).prod (Set.finite_univ (α := Fin d))).subset ?_
  rintro ⟨e, i⟩ hz
  rw [Function.mem_support, depthBlockOperator_apply] at hz
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact ⟨⟨(e, j), right_ne_zero_of_mul hj, rfl⟩, Set.mem_univ _⟩

end DepthBlocks

/-! ## Maximal diagonal operators and the finitely supported core -/

section MaximalDiagonal

variable {ι : Type*}

/-- The finitely supported vectors of `ℓ²(ι)`. -/
def finiteSupportCore (ι : Type*) : Submodule ℂ (DiagonalL2 ι) where
  carrier := {x | (Function.support (x : ι → ℂ)).Finite}
  zero_mem' := by
    change (Function.support ((0 : DiagonalL2 ι) : ι → ℂ)).Finite
    rw [lp.coeFn_zero, Function.support_zero]
    exact Set.finite_empty
  add_mem' := fun {x y} hx hy => by
    change (Function.support ((x + y : DiagonalL2 ι) : ι → ℂ)).Finite
    rw [lp.coeFn_add]
    exact (hx.union hy).subset (Function.support_add _ _)
  smul_mem' := fun c x hx => by
    change (Function.support ((c • x : DiagonalL2 ι) : ι → ℂ)).Finite
    rw [lp.coeFn_smul]
    exact hx.subset (Function.support_const_smul_subset c _)

theorem mem_finiteSupportCore {x : DiagonalL2 ι} :
    x ∈ finiteSupportCore ι ↔ (Function.support (x : ι → ℂ)).Finite := Iff.rfl

theorem finiteSupportCore_le_domain (energy : ι → ℝ) :
    finiteSupportCore ι ≤ (maximalRealDiagonal energy).domain := by
  intro x hx
  change Memℓp (fun i => (energy i : ℂ) * x i) 2
  refine (memℓp_zero ?_).of_exponent_ge (by simp)
  exact hx.subset fun i hi => right_ne_zero_of_mul hi

theorem maximalRealDiagonal_mem_core (energy : ι → ℝ) {x : DiagonalL2 ι}
    (hx : x ∈ finiteSupportCore ι) :
    (maximalRealDiagonal energy ⟨x, finiteSupportCore_le_domain energy hx⟩ : DiagonalL2 ι) ∈
      finiteSupportCore ι := by
  rw [mem_finiteSupportCore]
  refine hx.subset fun i hi => ?_
  rw [Function.mem_support, maximalRealDiagonal_apply] at hi
  exact right_ne_zero_of_mul hi

theorem maximalRealDiagonal_single [DecidableEq ι] (energy : ι → ℝ) (i : ι)
    (h : (lp.single 2 i (1 : ℂ) : DiagonalL2 ι) ∈ (maximalRealDiagonal energy).domain) :
    (maximalRealDiagonal energy ⟨lp.single 2 i 1, h⟩ : DiagonalL2 ι) =
      (energy i : ℂ) • (lp.single 2 i 1 : DiagonalL2 ι) := by
  apply lp.ext
  funext j
  rw [maximalRealDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  change (energy j : ℂ) * (lp.single 2 i (1 : ℂ) : ι → ℂ) j =
    (energy i : ℂ) * (lp.single 2 i (1 : ℂ) : ι → ℂ) j
  by_cases hji : j = i
  · rw [hji]
  · rw [lp.single_apply_ne _ _ _ hji, mul_zero, mul_zero]

theorem dense_finiteSupportCore [DecidableEq ι] :
    Dense (finiteSupportCore ι : Set (DiagonalL2 ι)) := by
  have hbasis : Dense (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ι)) :
      Set (DiagonalL2 ι)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ι).dense_span
  refine hbasis.mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_finiteSupportCore]
  refine (Set.finite_singleton i).subset fun j hj => ?_
  by_contra hji
  rw [Function.mem_support, HilbertSchmidt.lpBasis_apply, lp.single_apply_ne _ _ _ hji] at hj
  exact hj rfl

/-- A maximal diagonal operator with nonnegative multipliers is positive. -/
theorem re_inner_maximalRealDiagonal_nonneg {energy : ι → ℝ} (h0 : ∀ i, 0 ≤ energy i)
    (x : (maximalRealDiagonal energy).domain) :
    0 ≤ (⟪(x : DiagonalL2 ι), maximalRealDiagonal energy x⟫_ℂ).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  refine tsum_nonneg fun i => ?_
  rw [maximalRealDiagonal_apply, RCLike.inner_apply]
  have hc : (energy i : ℂ) * (x : DiagonalL2 ι) i * (starRingEnd ℂ) ((x : DiagonalL2 ι) i) =
      ((energy i * ‖(x : DiagonalL2 ι) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj']
    push_cast
    ring
  rw [hc, Complex.ofReal_re]
  exact mul_nonneg (h0 i) (by positivity)

/-- A maximal diagonal operator is closed. -/
theorem maximalRealDiagonal_isClosed [DecidableEq ι] (energy : ι → ℝ) :
    (maximalRealDiagonal energy).IsClosed := by
  have h := LinearPMap.adjoint_isClosed (maximalRealDiagonal_dense energy)
  rwa [LinearPMap.isSelfAdjoint_def.1 (maximalRealDiagonal_isSelfAdjoint energy)] at h

/-- A maximal diagonal operator with unbounded multipliers is unbounded. -/
theorem maximalRealDiagonal_not_bounded [DecidableEq ι] {energy : ι → ℝ}
    (h : ¬ BddAbove (range fun i => |energy i|)) :
    ¬ ∃ C : ℝ, ∀ x : (maximalRealDiagonal energy).domain,
      ‖maximalRealDiagonal energy x‖ ≤ C * ‖(x : DiagonalL2 ι)‖ := by
  rintro ⟨C, hC⟩
  refine h ⟨C, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi := hC ⟨(lp.single 2 i (1 : ℂ) : DiagonalL2 ι), by
    rw [← HilbertSchmidt.lpBasis_apply]
    exact lpBasis_mem_maximalRealDiagonalDomain energy i⟩
  rw [maximalRealDiagonal_single, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    lp.norm_single (by norm_num), norm_one, mul_one, mul_one] at hi
  exact hi

theorem memℓp_mul_of_abs_le {u v : ι → ℝ} {c : ℝ} (huv : ∀ i, |u i| ≤ c * |v i|)
    {x : ι → ℂ} (hv : Memℓp (fun i => (v i : ℂ) * x i) 2) :
    Memℓp (fun i => (u i : ℂ) * x i) 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2] at hv ⊢
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) (hv.mul_left (c ^ 2))
  rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.rpow_two, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    show c ^ 2 * (|v i| * ‖x i‖) ^ 2 = (c * (|v i| * ‖x i‖)) ^ 2 by ring]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (huv i) (norm_nonneg _)

/-- Comparable multipliers have the same maximal domain. -/
theorem maximalRealDiagonal_domain_eq_of_comparable {a b : ι → ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ i, c₁ * |b i| ≤ |a i|) (hup : ∀ i, |a i| ≤ c₂ * |b i|) :
    (maximalRealDiagonal a).domain = (maximalRealDiagonal b).domain := by
  ext x
  change Memℓp (fun i => (a i : ℂ) * x i) 2 ↔ Memℓp (fun i => (b i : ℂ) * x i) 2
  refine ⟨memℓp_mul_of_abs_le (c := c₁⁻¹) fun i => ?_, memℓp_mul_of_abs_le hup⟩
  rw [le_inv_mul_iff₀ hc₁]
  exact hlow i

end MaximalDiagonal

/-! ## Closure of a bounded operator restricted to a dense core -/

/-- A bounded operator restricted to a dense submodule is closable, with closure the operator on the
whole space. -/
theorem closure_toPMap_of_dense {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) {D : Submodule ℂ E} (hD : Dense (D : Set E)) :
    ((T : E →ₗ[ℂ] E).toPMap D).IsClosable ∧
      ((T : E →ₗ[ℂ] E).toPMap D).closure = (T : E →ₗ[ℂ] E).toPMap ⊤ := by
  have hmem : ∀ z : E × E, z ∈ ((T : E →ₗ[ℂ] E).toPMap ⊤).graph ↔ T z.1 = z.2 := by
    intro z
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      rw [← hy2, ← hy1]
      rfl
    · intro h
      exact ⟨⟨z.1, Submodule.mem_top⟩, rfl, h⟩
  have hgraph : ((T : E →ₗ[ℂ] E).toPMap D).graph.topologicalClosure =
      ((T : E →ₗ[ℂ] E).toPMap ⊤).graph := by
    apply le_antisymm
    · refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · intro z hz
        rw [LinearPMap.mem_graph_iff] at hz
        obtain ⟨y, hy1, hy2⟩ := hz
        rw [hmem, ← hy1, ← hy2]
        rfl
      · have hset : (((T : E →ₗ[ℂ] E).toPMap ⊤).graph : Set (E × E)) = {z | T z.1 = z.2} :=
          Set.ext hmem
        rw [hset]
        exact isClosed_eq (T.continuous.comp continuous_fst) continuous_snd
    · intro z hz
      rw [hmem] at hz
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      have hφ : Continuous fun x : E => (x, T x) := continuous_id.prodMk T.continuous
      have hz' : z = (z.1, T z.1) := Prod.ext rfl hz.symm
      rw [hz']
      refine closure_mono ?_
        (mem_closure_image (f := fun x : E => (x, T x)) hφ.continuousAt (hD z.1))
      rintro _ ⟨x, hxD, rfl⟩
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      exact ⟨⟨x, hxD⟩, rfl, rfl⟩
  have hcl : ((T : E →ₗ[ℂ] E).toPMap D).IsClosable := ⟨_, hgraph⟩
  refine ⟨hcl, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hcl.graph_closure_eq_closure_graph, hgraph]

/-! ## The normalized physical Plücker blocks -/

section PluckerBlocks

variable (p q : Nat.Primes)

/-- `τ_e = tr M_e` of the physical Plücker spectral matrix. -/
def pluckerSpectralTrace (e : ℕ) : ℝ :=
  (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).trace

/-- The normalized block `A_e = M_e/τ_e`. -/
def normalizedPluckerBlock (e : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (pluckerSpectralTrace p q e)⁻¹ • gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q

variable {p q} (hpq : (p : ℕ) < (q : ℕ))
include hpq

theorem pluckerSpectralTrace_pos (e : ℕ) : 0 < pluckerSpectralTrace p q e := by
  have hM := gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef (e := e) hpq
  refine lt_of_le_of_ne hM.trace_nonneg fun h => ?_
  have h0 := hM.trace_eq_zero_iff.1 h.symm
  have hr := gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three (e := e) hpq
  rw [h0, Matrix.rank_zero] at hr
  exact absurd hr (by norm_num)

theorem normalizedPluckerBlock_posSemidef (e : ℕ) : (normalizedPluckerBlock p q e).PosSemidef :=
  (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef hpq).smul
    (inv_nonneg.2 (pluckerSpectralTrace_pos hpq e).le)

theorem normalizedPluckerBlock_trace (e : ℕ) : (normalizedPluckerBlock p q e).trace = 1 := by
  rw [normalizedPluckerBlock, Matrix.trace_smul, smul_eq_mul]
  exact inv_mul_cancel₀ (pluckerSpectralTrace_pos hpq e).ne'

theorem normalizedPluckerBlock_symm (e : ℕ) (i j : Fin 4) :
    normalizedPluckerBlock p q e j i = normalizedPluckerBlock p q e i j :=
  posSemidef_real_apply_symm (normalizedPluckerBlock_posSemidef hpq e) i j

theorem abs_normalizedPluckerBlock_le (e : ℕ) (i j : Fin 4) :
    |normalizedPluckerBlock p q e i j| ≤ 1 :=
  (posSemidef_real_abs_apply_le_trace (normalizedPluckerBlock_posSemidef hpq e) i j).trans_eq
    (normalizedPluckerBlock_trace hpq e)

omit hpq in
theorem mulVecLin_normalizedPluckerBlock (e : ℕ) :
    (normalizedPluckerBlock p q e).mulVecLin =
      (pluckerSpectralTrace p q e)⁻¹ •
        (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVecLin := by
  ext x i
  simp [normalizedPluckerBlock]

/-- `A_e` keeps the rank-three quotient of `M_e`. -/
theorem normalizedPluckerBlock_rank (e : ℕ) : (normalizedPluckerBlock p q e).rank = 3 := by
  have h : (normalizedPluckerBlock p q e).rank =
      (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).rank := by
    unfold Matrix.rank
    rw [mulVecLin_normalizedPluckerBlock,
      LinearMap.range_smul _ _ (inv_ne_zero (pluckerSpectralTrace_pos hpq e).ne')]
  rw [h, gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three hpq]

/-- `ker A_e` is the line of the physical Stokes-gap vector. -/
theorem normalizedPluckerBlock_ker (e : ℕ) :
    LinearMap.ker (normalizedPluckerBlock p q e).mulVecLin =
      ℝ ∙ gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q := by
  rw [mulVecLin_normalizedPluckerBlock,
    LinearMap.ker_smul _ _ (inv_ne_zero (pluckerSpectralTrace_pos hpq e).ne'),
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_ker_eq_span hpq]

/-- `A_e` couples two distinct coordinates. -/
theorem exists_normalizedPluckerBlock_offDiagonal_ne_zero (e : ℕ) :
    ∃ i j : Fin 4, i ≠ j ∧ normalizedPluckerBlock p q e i j ≠ 0 := by
  obtain ⟨i, j, hij, h⟩ :=
    exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero
      (e := e) hpq
  refine ⟨i, j, hij, ?_⟩
  rw [normalizedPluckerBlock, Matrix.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (pluckerSpectralTrace_pos hpq e).ne') h

omit hpq in
/-- **(TCPSS.6).**  The Stokes-gap kernel vector is
`((e+1)I_p, (e+2)I_p, (e+1)I_q, (e+2)I_q)`, with `I_r > 0` the inverse tilts at aperture `1/2`. -/
theorem pluckerSpectralKernelVector_eq (e : ℕ) :
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q =
      ![((e : ℝ) + 1) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p,
        ((e : ℝ) + 2) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p,
        ((e : ℝ) + 1) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) q,
        ((e : ℝ) + 2) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) q] := by
  have key : ∀ i, gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q i =
      gammaSewnMobiusApertureStokesGap (1 / 2)
        (gammaSewnOrderedPrimeDepthPlucker_cell e p q i) := by
    intro i
    simp only [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
      gammaSewnCriticalPrimeDepthPacket_node, gammaSewnMobiusApertureStokesSquaredReciprocalGapNode,
      gammaSewnMobiusApertureStokesReciprocalGapNode]
    rw [Real.sqrt_sq (inv_nonneg.2 (gammaSewnMobiusApertureStokesGap_pos (by norm_num) _).le),
      inv_inv]
  funext i
  rw [key]
  fin_cases i <;>
    simp only [gammaSewnMobiusApertureStokesGap, gammaSewnOrderedPrimeDepthPlucker_cell,
      Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> push_cast <;> ring

omit hpq in
/-- **Moving kernel.**  Consecutive Stokes-gap vectors are not collinear. -/
theorem pluckerSpectralKernelVector_ne_smul_succ (e : ℕ) (c : ℝ) :
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q ≠
      c • gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector (e + 1) p q := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [pluckerSpectralKernelVector_eq, pluckerSpectralKernelVector_eq] at h0 h1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  push_cast at h0 h1
  have hI := gammaSewnMobiusApertureStokesInverseTilt_pos (s := 1 / 2) (by norm_num) p
  set I := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  have h0' : (e : ℝ) + 1 = c * ((e : ℝ) + 2) := by
    apply mul_right_cancel₀ hI.ne'
    linear_combination h0
  have h1' : (e : ℝ) + 2 = c * ((e : ℝ) + 3) := by
    apply mul_right_cancel₀ hI.ne'
    linear_combination h1
  have : (1 : ℝ) = 0 := by linear_combination (-((e : ℝ) + 3)) * h0' + ((e : ℝ) + 2) * h1'
  exact one_ne_zero this

/-- Consecutive blocks have different kernels. -/
theorem normalizedPluckerBlock_ker_ne_succ (e : ℕ) :
    LinearMap.ker (normalizedPluckerBlock p q e).mulVecLin ≠
      LinearMap.ker (normalizedPluckerBlock p q (e + 1)).mulVecLin := by
  intro h
  rw [normalizedPluckerBlock_ker hpq, normalizedPluckerBlock_ker hpq] at h
  have hmem : gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q ∈
      ℝ ∙ gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector (e + 1) p q :=
    h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact pluckerSpectralKernelVector_ne_smul_succ e c hc.symm

end PluckerBlocks

/-! ## The singular sandwich -/

section Sandwich

variable {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))

/-- Weighted normalized blocks `c_e A_e`. -/
def weightedPluckerBlock (p q : Nat.Primes) (c : ℕ → ℝ) (e : ℕ) : Matrix (Fin 4) (Fin 4) ℝ :=
  c e • normalizedPluckerBlock p q e

include hpq in
theorem abs_weightedPluckerBlock_le {c : ℕ → ℝ} (hc : ∀ e, |c e| ≤ 1) (e : ℕ) (i j : Fin 4) :
    |weightedPluckerBlock p q c e i j| ≤ 1 := by
  rw [weightedPluckerBlock, Matrix.smul_apply, smul_eq_mul, abs_mul]
  calc |c e| * |normalizedPluckerBlock p q e i j| ≤ 1 * 1 :=
        mul_le_mul (hc e) (abs_normalizedPluckerBlock_le hpq e i j) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

include hpq in
theorem abs_pluckerDepthLaw_le (e : ℕ) : |pluckerDepthLaw p q e| ≤ 1 := by
  rw [abs_of_pos (pluckerDepthLaw_pos hpq e)]
  exact pluckerDepthLaw_le_one hpq e

theorem abs_thetaCuspMellinSixFlux_le (e : ℕ) : |thetaCuspMellinSixFlux e| ≤ 1 := by
  rw [abs_of_pos (thetaCuspMellinSixFlux_pos e)]
  exact thetaCuspMellinSixFlux_le_one e

/-- The physical Plücker operator `B = ⊕_e π_e A_e`. -/
def physicalPluckerOperator : DiagonalL2 (ℕ × Fin 4) →L[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  depthBlockOperator (weightedPluckerBlock p q (pluckerDepthLaw p q))
    (abs_weightedPluckerBlock_le hpq (abs_pluckerDepthLaw_le hpq))

/-- The theta-completed Plücker operator `Θ = ⊕_e w_e A_e`. -/
def thetaCompletedPluckerOperator : DiagonalL2 (ℕ × Fin 4) →L[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  depthBlockOperator (weightedPluckerBlock p q thetaCuspMellinSixFlux)
    (abs_weightedPluckerBlock_le hpq abs_thetaCuspMellinSixFlux_le)

/-- The block-scalar half-density `S = ⊕_e s_e I₄` on its maximal domain. -/
def formationHalfDensityOperator (p q : Nat.Primes) :
    DiagonalL2 (ℕ × Fin 4) →ₗ.[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  maximalRealDiagonal fun z : ℕ × Fin 4 => formationHalfDensity p q z.1

/-- The shifted depth number operator `N + 1` on its maximal domain. -/
def depthNumberSuccOperator : DiagonalL2 (ℕ × Fin 4) →ₗ.[ℂ] DiagonalL2 (ℕ × Fin 4) :=
  maximalRealDiagonal fun z : ℕ × Fin 4 => (z.1 : ℝ) + 1

include hpq

theorem weightedPluckerBlock_symm {c : ℕ → ℝ} (e : ℕ) (i j : Fin 4) :
    weightedPluckerBlock p q c e j i = weightedPluckerBlock p q c e i j := by
  simp only [weightedPluckerBlock, Matrix.smul_apply, smul_eq_mul,
    normalizedPluckerBlock_symm hpq e i j]

theorem weightedPluckerBlock_posSemidef {c : ℕ → ℝ} (hc : ∀ e, 0 ≤ c e) (e : ℕ) :
    (weightedPluckerBlock p q c e).PosSemidef :=
  (normalizedPluckerBlock_posSemidef hpq e).smul (hc e)

/-- A probability-weighted normalized block operator is positive, Schatten-one, of trace one and
trace norm one. -/
theorem weightedPluckerOperator_traceClass {c : ℕ → ℝ} (hc0 : ∀ e, 0 ≤ c e) (hc1 : HasSum c 1)
    (hc : ∀ e, |c e| ≤ 1) :
    (depthBlockOperator (weightedPluckerBlock p q c)
        (abs_weightedPluckerBlock_le hpq hc)).IsPositive ∧
      MemSchattenClass 1
        (depthBlockOperator (weightedPluckerBlock p q c) (abs_weightedPluckerBlock_le hpq hc)) ∧
      (depthBlockOperator (weightedPluckerBlock p q c)
        (abs_weightedPluckerBlock_le hpq hc)).opTrace = 1 ∧
      traceNorm (DiagonalL2 (ℕ × Fin 4))
        (depthBlockOperator (weightedPluckerBlock p q c)
          (abs_weightedPluckerBlock_le hpq hc)) = 1 := by
  have htr : ∀ e, (weightedPluckerBlock p q c e).trace = c e := fun e => by
    rw [weightedPluckerBlock, Matrix.trace_smul, smul_eq_mul, normalizedPluckerBlock_trace hpq e,
      mul_one]
  have hsym := weightedPluckerBlock_symm (c := c) hpq
  have hpsd := weightedPluckerBlock_posSemidef hpq hc0
  have hpos := depthBlockOperator_isPositive (abs_weightedPluckerBlock_le hpq hc) hsym hpsd
  obtain ⟨hS, hT⟩ := depthBlockOperator_traceClass (abs_weightedPluckerBlock_le hpq hc) hsym hpsd
    (by simpa only [htr] using hc1.summable)
  simp only [htr, hc1.tsum_eq, Complex.ofReal_one] at hT
  refine ⟨hpos, hS, hT, ?_⟩
  rw [traceNorm_eq_re_opTrace_of_isPositive hS hpos, hT, Complex.one_re]

/-- **(TCPSS, 1).**  `B` and `Θ` are positive Schatten-one operators of trace and trace norm one. -/
theorem physical_and_theta_pluckerOperator_traceClass :
    ((physicalPluckerOperator hpq).IsPositive ∧ MemSchattenClass 1 (physicalPluckerOperator hpq) ∧
      (physicalPluckerOperator hpq).opTrace = 1 ∧
      traceNorm (DiagonalL2 (ℕ × Fin 4)) (physicalPluckerOperator hpq) = 1) ∧
    ((thetaCompletedPluckerOperator hpq).IsPositive ∧
      MemSchattenClass 1 (thetaCompletedPluckerOperator hpq) ∧
      (thetaCompletedPluckerOperator hpq).opTrace = 1 ∧
      traceNorm (DiagonalL2 (ℕ × Fin 4)) (thetaCompletedPluckerOperator hpq) = 1) := by
  refine ⟨weightedPluckerOperator_traceClass hpq (fun e => (pluckerDepthLaw_pos hpq e).le)
    (hasSum_pluckerDepthLaw hpq) (abs_pluckerDepthLaw_le hpq), ?_⟩
  have hw : HasSum thetaCuspMellinSixFlux 1 := by
    simpa only [← funext thetaCuspMellinSixFlux_eq_primeHodgeHistory_w] using
      PrimeHodgeHistory.hasSum_w
  exact weightedPluckerOperator_traceClass hpq (fun e => (thetaCuspMellinSixFlux_pos e).le) hw
    abs_thetaCuspMellinSixFlux_le

/-- The half-density multiplier on `ℕ × Fin 4` is comparable to `e + 1`. -/
theorem exists_formationHalfDensity_comparable :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℕ × Fin 4,
      c₁ * |(z.1 : ℝ) + 1| ≤ |formationHalfDensity p q z.1| ∧
        |formationHalfDensity p q z.1| ≤ c₂ * |(z.1 : ℝ) + 1| := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_formationHalfDensity_bounds hpq
  refine ⟨c₁, c₂, hc₁, hc₂, fun z => ?_⟩
  rw [abs_of_pos (formationHalfDensity_pos hpq z.1), abs_of_pos (by positivity)]
  exact hb z.1

/-- **(TCPSS, 2).**  `S` is self-adjoint, closed, positive and unbounded, `Dom S = Dom(N+1)`, and
the graph norms `‖x‖ + ‖Sx‖` and `‖x‖ + ‖(N+1)x‖` are uniformly equivalent. -/
theorem formationHalfDensityOperator_properties :
    IsSelfAdjoint (formationHalfDensityOperator p q) ∧
    (formationHalfDensityOperator p q).IsClosed ∧
    (∀ x : (formationHalfDensityOperator p q).domain,
      0 ≤ (⟪(x : DiagonalL2 (ℕ × Fin 4)), formationHalfDensityOperator p q x⟫_ℂ).re) ∧
    (¬ ∃ C : ℝ, ∀ x : (formationHalfDensityOperator p q).domain,
      ‖formationHalfDensityOperator p q x‖ ≤ C * ‖(x : DiagonalL2 (ℕ × Fin 4))‖) ∧
    (formationHalfDensityOperator p q).domain = depthNumberSuccOperator.domain ∧
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : (formationHalfDensityOperator p q).domain)
      (y : depthNumberSuccOperator.domain), (x : DiagonalL2 (ℕ × Fin 4)) = y →
        c * (‖(x : DiagonalL2 (ℕ × Fin 4))‖ + ‖depthNumberSuccOperator y‖) ≤
            ‖(x : DiagonalL2 (ℕ × Fin 4))‖ + ‖formationHalfDensityOperator p q x‖ ∧
          ‖(x : DiagonalL2 (ℕ × Fin 4))‖ + ‖formationHalfDensityOperator p q x‖ ≤
            C * (‖(x : DiagonalL2 (ℕ × Fin 4))‖ + ‖depthNumberSuccOperator y‖) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := exists_formationHalfDensity_comparable hpq
  refine ⟨maximalRealDiagonal_isSelfAdjoint _, maximalRealDiagonal_isClosed _,
    re_inner_maximalRealDiagonal_nonneg fun z => (formationHalfDensity_pos hpq z.1).le, ?_,
    maximalRealDiagonal_domain_eq_of_comparable hc₁ (fun z => (hb z).1) (fun z => (hb z).2), ?_⟩
  · refine maximalRealDiagonal_not_bounded fun ⟨C, hC⟩ => ?_
    refine not_bddAbove_formationHalfDensity hpq ⟨C, ?_⟩
    rintro _ ⟨e, rfl⟩
    have := hC ⟨(e, 0), rfl⟩
    dsimp only at this
    rwa [abs_of_pos (formationHalfDensity_pos hpq e)] at this
  · refine ⟨min 1 c₁, max 1 c₂, lt_min one_pos hc₁, lt_max_of_lt_left one_pos,
      fun x y hxy => ?_⟩
    have hco : ∀ z : ℕ × Fin 4, ‖(formationHalfDensityOperator p q x : DiagonalL2 (ℕ × Fin 4)) z‖ =
        |formationHalfDensity p q z.1| * ‖(x : DiagonalL2 (ℕ × Fin 4)) z‖ := fun z => by
      change ‖(formationHalfDensity p q z.1 : ℂ) * (x : DiagonalL2 (ℕ × Fin 4)) z‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcn : ∀ z : ℕ × Fin 4, ‖(depthNumberSuccOperator y : DiagonalL2 (ℕ × Fin 4)) z‖ =
        |(z.1 : ℝ) + 1| * ‖(x : DiagonalL2 (ℕ × Fin 4)) z‖ := fun z => by
      change ‖(((z.1 : ℝ) + 1 : ℝ) : ℂ) * (y : DiagonalL2 (ℕ × Fin 4)) z‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hxy]
    have hup : ‖formationHalfDensityOperator p q x‖ ≤ c₂ * ‖depthNumberSuccOperator y‖ :=
      norm_le_of_forall_norm_apply_le hc₂.le fun z => by
        rw [hco, hcn, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hb z).2 (norm_nonneg _)
    have hlow : ‖depthNumberSuccOperator y‖ ≤ c₁⁻¹ * ‖formationHalfDensityOperator p q x‖ :=
      norm_le_of_forall_norm_apply_le (by positivity) fun z => by
        rw [hco, hcn, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right ((le_inv_mul_iff₀ hc₁).2 (hb z).1) (norm_nonneg _)
    rw [le_inv_mul_iff₀ hc₁] at hlow
    have hm1 : min 1 c₁ ≤ 1 := min_le_left _ _
    have hm2 : min 1 c₁ ≤ c₁ := min_le_right _ _
    have hM1 : 1 ≤ max 1 c₂ := le_max_left _ _
    have hM2 : c₂ ≤ max 1 c₂ := le_max_right _ _
    have hx := norm_nonneg (x : DiagonalL2 (ℕ × Fin 4))
    have hy := norm_nonneg (depthNumberSuccOperator y)
    constructor <;> nlinarith

omit hpq in
/-- `S` maps the finitely supported core into itself. -/
theorem formationHalfDensityOperator_mem_core {x : DiagonalL2 (ℕ × Fin 4)}
    (hx : x ∈ finiteSupportCore (ℕ × Fin 4)) :
    (formationHalfDensityOperator p q ⟨x, finiteSupportCore_le_domain _ hx⟩ :
      DiagonalL2 (ℕ × Fin 4)) ∈ finiteSupportCore (ℕ × Fin 4) :=
  maximalRealDiagonal_mem_core _ hx

omit hpq in
theorem blockOperator_mem_core {M : ℕ → Matrix (Fin 4) (Fin 4) ℝ} {C : ℝ}
    (hM : ∀ e i j, |M e i j| ≤ C) {x : DiagonalL2 (ℕ × Fin 4)}
    (hx : x ∈ finiteSupportCore (ℕ × Fin 4)) :
    depthBlockOperator M hM x ∈ finiteSupportCore (ℕ × Fin 4) :=
  depthBlockOperator_mem_core hM hx

/-- **(TCPSS.4).**  On the finitely supported core, `S B S = Θ`. -/
theorem formationSandwich_eq (x : DiagonalL2 (ℕ × Fin 4))
    (hx : x ∈ finiteSupportCore (ℕ × Fin 4)) :
    formationHalfDensityOperator p q
        ⟨physicalPluckerOperator hpq
            (formationHalfDensityOperator p q ⟨x, finiteSupportCore_le_domain _ hx⟩),
          finiteSupportCore_le_domain _ (blockOperator_mem_core _
            (formationHalfDensityOperator_mem_core (p := p) (q := q) hx))⟩ =
      thetaCompletedPluckerOperator hpq x := by
  apply lp.ext
  funext z
  obtain ⟨e, i⟩ := z
  change (formationHalfDensity p q e : ℂ) *
      (∑ j, (weightedPluckerBlock p q (pluckerDepthLaw p q) e i j : ℂ) *
        ((formationHalfDensity p q e : ℂ) * x (e, j))) =
    ∑ j, (weightedPluckerBlock p q thetaCuspMellinSixFlux e i j : ℂ) * x (e, j)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : ((formationHalfDensity p q e : ℂ)) ^ 2 * (pluckerDepthLaw p q e : ℂ) =
      (thetaCuspMellinSixFlux e : ℂ) := by
    exact_mod_cast formationHalfDensity_sq_mul hpq e
  simp only [weightedPluckerBlock, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  linear_combination ((normalizedPluckerBlock p q e i j : ℂ) * x (e, j)) * hw

/-- **(TCPSS, 3).**  The core sandwich operator `Θ|_core` is closable and its closure is the
bounded operator `Θ`. -/
theorem formationSandwich_closure :
    (((thetaCompletedPluckerOperator hpq :
          DiagonalL2 (ℕ × Fin 4) →ₗ[ℂ] DiagonalL2 (ℕ × Fin 4)).toPMap
        (finiteSupportCore (ℕ × Fin 4))).IsClosable) ∧
      ((thetaCompletedPluckerOperator hpq :
          DiagonalL2 (ℕ × Fin 4) →ₗ[ℂ] DiagonalL2 (ℕ × Fin 4)).toPMap
          (finiteSupportCore (ℕ × Fin 4))).closure =
        (thetaCompletedPluckerOperator hpq :
          DiagonalL2 (ℕ × Fin 4) →ₗ[ℂ] DiagonalL2 (ℕ × Fin 4)).toPMap ⊤ :=
  closure_toPMap_of_dense _ dense_finiteSupportCore

/-- **(TCPSS, 4).**  `S` is the unique nonnegative block-scalar operator implementing the sandwich
on the core. -/
theorem eq_formationHalfDensity_of_sandwich {r : ℕ → ℝ} (hr : ∀ e, 0 ≤ r e)
    (h : ∀ (x : DiagonalL2 (ℕ × Fin 4)) (hx : x ∈ finiteSupportCore (ℕ × Fin 4)),
      maximalRealDiagonal (fun z : ℕ × Fin 4 => r z.1)
          ⟨physicalPluckerOperator hpq
              (maximalRealDiagonal (fun z : ℕ × Fin 4 => r z.1)
                ⟨x, finiteSupportCore_le_domain _ hx⟩),
            finiteSupportCore_le_domain _ (blockOperator_mem_core _
              (maximalRealDiagonal_mem_core _ hx))⟩ =
        thetaCompletedPluckerOperator hpq x) (e : ℕ) :
    r e = formationHalfDensity p q e := by
  have htr := normalizedPluckerBlock_trace hpq e
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ k, normalizedPluckerBlock p q e k k ≠ 0 by
      rw [show ∑ k, normalizedPluckerBlock p q e k k = (normalizedPluckerBlock p q e).trace from
        rfl, htr]
      exact one_ne_zero)
  have hx : (lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)) ∈
      finiteSupportCore (ℕ × Fin 4) := by
    rw [mem_finiteSupportCore]
    refine (Set.finite_singleton (e, i)).subset fun z hz => ?_
    by_contra hzi
    exact hz (lp.single_apply_ne _ _ _ hzi)
  have hev := congrArg (fun y : DiagonalL2 (ℕ × Fin 4) => y (e, i)) (h _ hx)
  simp only at hev
  rw [maximalRealDiagonal_apply] at hev
  change (r e : ℂ) * physicalPluckerOperator hpq
      (maximalRealDiagonal (fun z : ℕ × Fin 4 => r z.1)
        ⟨lp.single 2 (e, i) 1, finiteSupportCore_le_domain _ hx⟩) (e, i) =
    thetaCompletedPluckerOperator hpq (lp.single 2 (e, i) 1) (e, i) at hev
  rw [maximalRealDiagonal_single, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    physicalPluckerOperator, thetaCompletedPluckerOperator, depthBlockOperator_single,
    depthBlockOperator_single, if_pos rfl, if_pos rfl] at hev
  simp only [weightedPluckerBlock, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul] at hev
  have hreal : r e ^ 2 * pluckerDepthLaw p q e * normalizedPluckerBlock p q e i i =
      thetaCuspMellinSixFlux e * normalizedPluckerBlock p q e i i := by
    have : ((r e ^ 2 * pluckerDepthLaw p q e * normalizedPluckerBlock p q e i i : ℝ) : ℂ) =
        ((thetaCuspMellinSixFlux e * normalizedPluckerBlock p q e i i : ℝ) : ℂ) := by
      push_cast
      linear_combination hev
    exact_mod_cast this
  have hsq : r e ^ 2 * pluckerDepthLaw p q e = thetaCuspMellinSixFlux e :=
    mul_right_cancel₀ hi hreal
  exact (sq_mul_pluckerDepthLaw_eq_iff hpq (hr e) e).1 hsq

/-- **(TCPSS, 5).**  The matrix of `Θ` is block diagonal with blocks `w_e A_e`. -/
theorem inner_single_thetaCompletedPluckerOperator_single (e : ℕ) (i : Fin 4) (e' : ℕ)
    (j : Fin 4) :
    ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
        thetaCompletedPluckerOperator hpq (lp.single 2 (e', j) 1)⟫_ℂ =
      if e = e' then ((thetaCuspMellinSixFlux e * normalizedPluckerBlock p q e i j : ℝ) : ℂ)
      else 0 := by
  rw [thetaCompletedPluckerOperator, inner_single_depthBlockOperator_single]
  simp only [weightedPluckerBlock, Matrix.smul_apply, smul_eq_mul]

/-- **(TCPSS.5) fails.**  `Θ` is not `diag(w) ⊗ A` for any fixed `4 × 4` matrix `A`. -/
theorem thetaCompletedPluckerOperator_not_separable :
    ¬ ∃ A : Matrix (Fin 4) (Fin 4) ℂ, ∀ (e : ℕ) (i j : Fin 4),
      ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
          thetaCompletedPluckerOperator hpq (lp.single 2 (e, j) 1)⟫_ℂ =
        (thetaCuspMellinSixFlux e : ℂ) * A i j := by
  rintro ⟨A, hA⟩
  have hblock : ∀ e i j, (normalizedPluckerBlock p q e i j : ℂ) = A i j := by
    intro e i j
    have h := hA e i j
    rw [inner_single_thetaCompletedPluckerOperator_single, if_pos rfl, Complex.ofReal_mul] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (thetaCuspMellinSixFlux_pos e).ne') h
  have heq : normalizedPluckerBlock p q 0 = normalizedPluckerBlock p q (0 + 1) := by
    ext i j
    exact_mod_cast (hblock 0 i j).trans (hblock (0 + 1) i j).symm
  exact normalizedPluckerBlock_ker_ne_succ hpq 0 (by rw [heq])

/-! ## The singular sandwich theorem -/

/-- **Theorem TCPSS.**  For primes `p < q`: `B` and `Θ` are positive Schatten-one with trace one;
`S` is self-adjoint, closed and unbounded with `Dom S = Dom(N+1)`; `S B S = Θ` on the finitely
supported core, whose sandwich operator has closure `Θ`; every block of `Θ` is `w_e A_e` with `A_e`
of rank three, kernel spanned by the moving Stokes-gap vector and nonzero off-diagonal coupling;
and `Θ` is not of the form `diag(w) ⊗ A`. -/
theorem theta_completed_plucker_singular_sandwich :
    ((physicalPluckerOperator hpq).IsPositive ∧ MemSchattenClass 1 (physicalPluckerOperator hpq) ∧
      (physicalPluckerOperator hpq).opTrace = 1) ∧
    ((thetaCompletedPluckerOperator hpq).IsPositive ∧
      MemSchattenClass 1 (thetaCompletedPluckerOperator hpq) ∧
      (thetaCompletedPluckerOperator hpq).opTrace = 1) ∧
    IsSelfAdjoint (formationHalfDensityOperator p q) ∧
    (formationHalfDensityOperator p q).IsClosed ∧
    (formationHalfDensityOperator p q).domain = depthNumberSuccOperator.domain ∧
    (¬ ∃ C : ℝ, ∀ x : (formationHalfDensityOperator p q).domain,
      ‖formationHalfDensityOperator p q x‖ ≤ C * ‖(x : DiagonalL2 (ℕ × Fin 4))‖) ∧
    (∀ (x : DiagonalL2 (ℕ × Fin 4)) (hx : x ∈ finiteSupportCore (ℕ × Fin 4)),
      formationHalfDensityOperator p q
          ⟨physicalPluckerOperator hpq
              (formationHalfDensityOperator p q ⟨x, finiteSupportCore_le_domain _ hx⟩),
            finiteSupportCore_le_domain _ (blockOperator_mem_core _
              (formationHalfDensityOperator_mem_core (p := p) (q := q) hx))⟩ =
        thetaCompletedPluckerOperator hpq x) ∧
    ((thetaCompletedPluckerOperator hpq :
          DiagonalL2 (ℕ × Fin 4) →ₗ[ℂ] DiagonalL2 (ℕ × Fin 4)).toPMap
          (finiteSupportCore (ℕ × Fin 4))).closure =
      (thetaCompletedPluckerOperator hpq :
        DiagonalL2 (ℕ × Fin 4) →ₗ[ℂ] DiagonalL2 (ℕ × Fin 4)).toPMap ⊤ ∧
    (∀ e : ℕ, (normalizedPluckerBlock p q e).rank = 3 ∧
      LinearMap.ker (normalizedPluckerBlock p q e).mulVecLin =
        ℝ ∙ gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q ∧
      (∃ i j : Fin 4, i ≠ j ∧ normalizedPluckerBlock p q e i j ≠ 0) ∧
      LinearMap.ker (normalizedPluckerBlock p q e).mulVecLin ≠
        LinearMap.ker (normalizedPluckerBlock p q (e + 1)).mulVecLin) ∧
    ¬ ∃ A : Matrix (Fin 4) (Fin 4) ℂ, ∀ (e : ℕ) (i j : Fin 4),
      ⟪(lp.single 2 (e, i) (1 : ℂ) : DiagonalL2 (ℕ × Fin 4)),
          thetaCompletedPluckerOperator hpq (lp.single 2 (e, j) 1)⟫_ℂ =
        (thetaCuspMellinSixFlux e : ℂ) * A i j := by
  obtain ⟨⟨hB1, hB2, hB3, -⟩, ⟨hT1, hT2, hT3, -⟩⟩ :=
    physical_and_theta_pluckerOperator_traceClass hpq
  obtain ⟨hS1, hS2, -, hS4, hS5, -⟩ := formationHalfDensityOperator_properties hpq
  exact ⟨⟨hB1, hB2, hB3⟩, ⟨hT1, hT2, hT3⟩, hS1, hS2, hS5, hS4, formationSandwich_eq hpq,
    (formationSandwich_closure hpq).2,
    fun e => ⟨normalizedPluckerBlock_rank hpq e, normalizedPluckerBlock_ker hpq e,
      exists_normalizedPluckerBlock_offDiagonal_ne_zero hpq e,
      normalizedPluckerBlock_ker_ne_succ hpq e⟩,
    thetaCompletedPluckerOperator_not_separable hpq⟩

end Sandwich

end GaloisForLFunctions.HTGeometry
