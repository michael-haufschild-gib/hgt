import Mathlib

/-!
# The unilateral shift: recurrent boundary, open defect history, index

On the Hardy space `ℓ²(ℕ₀)` the `n`-fold unilateral shift `Sⁿ` is an isometry with cokernel of
dimension `n`.  Its defect `Dₙ = 1 − Sⁿ S*ⁿ` is the coordinate truncation onto the first `n` slots,
it obeys an exact orthogonal cocycle law, and its rank grows linearly while every root-of-unity
boundary observer is periodic.

The `n`-fold shift is defined directly as a coordinate reindexing rather than as an `n`-th power, so
all identities are proved without induction on operator powers.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal InnerProductSpace

noncomputable section

/-- The Hardy space `ℓ²(ℕ₀)`. -/
abbrev ToeplitzSpace : Type := lp (fun _ : ℕ => ℂ) 2

/-! ## Sequence-level shifts -/

/-- The `n`-fold forward shift of a sequence. -/
def shiftFun (n : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := fun k => if k < n then 0 else f (k - n)

/-- The `n`-fold backward shift of a sequence. -/
def backFun (n : ℕ) (f : ℕ → ℂ) : ℕ → ℂ := fun k => f (k + n)

@[simp] theorem shiftFun_add (n : ℕ) (f : ℕ → ℂ) (m : ℕ) : shiftFun n f (m + n) = f m := by
  simp only [shiftFun]
  rw [if_neg (by omega), Nat.add_sub_cancel]

@[simp] theorem shiftFun_of_lt {n k : ℕ} (h : k < n) (f : ℕ → ℂ) : shiftFun n f k = 0 :=
  if_pos h

theorem shiftFun_of_le {n k : ℕ} (h : n ≤ k) (f : ℕ → ℂ) : shiftFun n f k = f (k - n) :=
  if_neg (by omega)

@[simp] theorem backFun_apply (n : ℕ) (f : ℕ → ℂ) (k : ℕ) : backFun n f k = f (k + n) := rfl

/-- The backward shift is a left inverse of the forward shift, at sequence level. -/
theorem backFun_shiftFun (n : ℕ) (f : ℕ → ℂ) : backFun n (shiftFun n f) = f := by
  funext k
  simp

/-- The forward shift of the backward shift is the truncation that kills the first `n` slots. -/
theorem shiftFun_backFun (n : ℕ) (f : ℕ → ℂ) :
    shiftFun n (backFun n f) = fun k => if k < n then 0 else f k := by
  funext k
  by_cases h : k < n
  · simp [shiftFun, h]
  · rw [shiftFun_of_le (by omega), backFun_apply, if_neg h]
    congr 1
    omega

/-- Composition of forward shifts. -/
theorem shiftFun_shiftFun (n r : ℕ) (f : ℕ → ℂ) :
    shiftFun n (shiftFun r f) = shiftFun (n + r) f := by
  funext k
  by_cases h : k < n + r
  · rw [shiftFun_of_lt h]
    by_cases h2 : k < n
    · rw [shiftFun_of_lt h2]
    · rw [shiftFun_of_le (by omega), shiftFun_of_lt (by omega)]
  · rw [shiftFun_of_le (by omega : n + r ≤ k), shiftFun_of_le (by omega : n ≤ k),
      shiftFun_of_le (by omega : r ≤ k - n)]
    congr 1
    omega

/-! ## Square-summability -/

theorem summable_sq_of_memℓp {f : ℕ → ℂ} (hf : Memℓp f 2) :
    Summable fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal :=
  hf.summable (by norm_num)

theorem memℓp_shiftFun {f : ℕ → ℂ} (hf : Memℓp f 2) (n : ℕ) : Memℓp (shiftFun n f) 2 := by
  refine memℓp_gen ?_
  refine (summable_nat_add_iff n).mp ?_
  refine (summable_sq_of_memℓp hf).congr ?_
  intro m
  rw [shiftFun_add]

theorem memℓp_backFun {f : ℕ → ℂ} (hf : Memℓp f 2) (n : ℕ) : Memℓp (backFun n f) 2 := by
  refine memℓp_gen ?_
  exact (summable_nat_add_iff n).mpr (summable_sq_of_memℓp hf)

theorem tsum_sq_shiftFun {f : ℕ → ℂ} (hf : Memℓp f 2) (n : ℕ) :
    ∑' k : ℕ, ‖shiftFun n f k‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' k : ℕ, ‖f k‖ ^ (2 : ℝ≥0∞).toReal := by
  have hsum : Summable fun k => ‖shiftFun n f k‖ ^ (2 : ℝ≥0∞).toReal :=
    summable_sq_of_memℓp (memℓp_shiftFun hf n)
  have hhead : ∑ i ∈ Finset.range n, ‖shiftFun n f i‖ ^ (2 : ℝ≥0∞).toReal = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [shiftFun_of_lt (Finset.mem_range.mp hi)]
    simp
  have htail : ∑' m : ℕ, ‖shiftFun n f (m + n)‖ ^ (2 : ℝ≥0∞).toReal
      = ∑' k : ℕ, ‖f k‖ ^ (2 : ℝ≥0∞).toReal := by
    refine tsum_congr ?_
    intro m
    rw [shiftFun_add]
  rw [← hsum.sum_add_tsum_nat_add n, hhead, htail, zero_add]

/-! ## The shift operators -/

/-- The `n`-fold unilateral shift, as a linear isometry of the Hardy space. -/
def shiftIsom (n : ℕ) : ToeplitzSpace →ₗᵢ[ℂ] ToeplitzSpace where
  toFun f := ⟨shiftFun n f, memℓp_shiftFun (lp.memℓp f) n⟩
  map_add' f g := by
    ext k
    by_cases h : k < n <;> simp [shiftFun, h]
  map_smul' c f := by
    ext k
    by_cases h : k < n <;> simp [shiftFun, h]
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact tsum_sq_shiftFun (lp.memℓp f) n

@[simp] theorem shiftIsom_apply (n : ℕ) (f : ToeplitzSpace) (k : ℕ) :
    (shiftIsom n f : ℕ → ℂ) k = shiftFun n (f : ℕ → ℂ) k := rfl

/-- The `n`-fold backward shift, as a linear map of the Hardy space. -/
def backLinear (n : ℕ) : ToeplitzSpace →ₗ[ℂ] ToeplitzSpace where
  toFun f := ⟨backFun n f, memℓp_backFun (lp.memℓp f) n⟩
  map_add' f g := by ext k; simp
  map_smul' c f := by ext k; simp

@[simp] theorem backLinear_apply (n : ℕ) (f : ToeplitzSpace) (k : ℕ) :
    (backLinear n f : ℕ → ℂ) k = (f : ℕ → ℂ) (k + n) := rfl

theorem norm_backLinear_le (n : ℕ) (f : ToeplitzSpace) : ‖backLinear n f‖ ≤ ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  have hsum : Summable fun k => ‖(f : ℕ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal :=
    summable_sq_of_memℓp (lp.memℓp f)
  have htail : ∑' k : ℕ, ‖(backLinear n f : ℕ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' k : ℕ, ‖(f : ℕ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal := by
    have hhead : 0 ≤ ∑ i ∈ Finset.range n, ‖(f : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
    have := hsum.sum_add_tsum_nat_add n
    have heq : ∑' m : ℕ, ‖(f : ℕ → ℂ) (m + n)‖ ^ (2 : ℝ≥0∞).toReal
        = ∑' k : ℕ, ‖(backLinear n f : ℕ → ℂ) k‖ ^ (2 : ℝ≥0∞).toReal := by
      refine tsum_congr ?_
      intro m
      rw [backLinear_apply]
    rw [heq] at this
    linarith
  refine Real.rpow_le_rpow ?_ htail (by norm_num)
  exact tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _

/-- The `n`-fold backward shift, as a bounded operator. -/
def backOp (n : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (backLinear n).mkContinuous 1 (fun f => by simpa using norm_backLinear_le n f)

@[simp] theorem backOp_apply (n : ℕ) (f : ToeplitzSpace) (k : ℕ) :
    (backOp n f : ℕ → ℂ) k = (f : ℕ → ℂ) (k + n) := rfl

/-- The `n`-fold unilateral shift, as a bounded operator. -/
def shiftOp (n : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  (shiftIsom n).toLinearMap.mkContinuous 1 (fun f => by
    rw [one_mul]
    exact le_of_eq ((shiftIsom n).norm_map f))

@[simp] theorem shiftOp_apply (n : ℕ) (f : ToeplitzSpace) (k : ℕ) :
    (shiftOp n f : ℕ → ℂ) k = shiftFun n (f : ℕ → ℂ) k := rfl

/-! ## The adjoint and the isometry relation -/

/-- **The backward shift is the adjoint of the forward shift.** -/
theorem adjoint_shiftOp (n : ℕ) :
    ContinuousLinearMap.adjoint (shiftOp n) = backOp n := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hsum : Summable fun k : ℕ => ⟪(x : ℕ → ℂ) k, (shiftOp n y : ℕ → ℂ) k⟫_ℂ :=
    lp.summable_inner x (shiftOp n y)
  have hhead : ∑ i ∈ Finset.range n, ⟪(x : ℕ → ℂ) i, (shiftOp n y : ℕ → ℂ) i⟫_ℂ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [shiftOp_apply, shiftFun_of_lt (Finset.mem_range.mp hi)]
    simp
  have htail : ∑' m : ℕ, ⟪(x : ℕ → ℂ) (m + n), (shiftOp n y : ℕ → ℂ) (m + n)⟫_ℂ
      = ∑' m : ℕ, ⟪(backOp n x : ℕ → ℂ) m, (y : ℕ → ℂ) m⟫_ℂ := by
    refine tsum_congr ?_
    intro m
    rw [shiftOp_apply, shiftFun_add, backOp_apply]
  rw [← hsum.sum_add_tsum_nat_add n, hhead, zero_add, htail]

/-- **Clause 1.**  The `n`-fold shift is an isometry: `S*ⁿ Sⁿ = 1`. -/
theorem backOp_comp_shiftOp (n : ℕ) :
    backOp n ∘L shiftOp n = ContinuousLinearMap.id ℂ ToeplitzSpace := by
  ext f k
  simp

theorem adjoint_comp_shiftOp (n : ℕ) :
    ContinuousLinearMap.adjoint (shiftOp n) ∘L shiftOp n
      = ContinuousLinearMap.id ℂ ToeplitzSpace := by
  rw [adjoint_shiftOp, backOp_comp_shiftOp]

/-! ## The defect projection -/

/-- The `n`-th defect `Dₙ = 1 − Sⁿ S*ⁿ`. -/
def defectOp (n : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  ContinuousLinearMap.id ℂ ToeplitzSpace - shiftOp n ∘L backOp n

/-- **Clause 2, description.**  The defect is the coordinate truncation onto the first `n` slots. -/
@[simp] theorem defectOp_apply (n : ℕ) (f : ToeplitzSpace) (k : ℕ) :
    (defectOp n f : ℕ → ℂ) k = if k < n then (f : ℕ → ℂ) k else 0 := by
  show (f : ℕ → ℂ) k - shiftFun n (fun j => (f : ℕ → ℂ) (j + n)) k = _
  by_cases h : k < n
  · rw [shiftFun_of_lt h, if_pos h, sub_zero]
  · rw [shiftFun_of_le (by omega), if_neg h]
    have : k - n + n = k := by omega
    rw [this, sub_self]

theorem defectOp_zero : defectOp 0 = 0 := by
  ext f k
  simp

/-- The defect is idempotent. -/
theorem defectOp_comp_self (n : ℕ) : defectOp n ∘L defectOp n = defectOp n := by
  ext f k
  by_cases h : k < n <;> simp [h]

/-- The defect is self-adjoint, hence an orthogonal projection. -/
theorem adjoint_defectOp (n : ℕ) :
    ContinuousLinearMap.adjoint (defectOp n) = defectOp n := by
  rw [defectOp, map_sub, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.adjoint_comp,
    adjoint_shiftOp]
  congr 1
  rw [← adjoint_shiftOp, ContinuousLinearMap.adjoint_adjoint]

/-! ## The exact cocycle law -/

/-- **Clause 3.**  `D_{n+r} = Dₙ + Sⁿ D_r S*ⁿ`. -/
theorem defectOp_add (n r : ℕ) :
    defectOp (n + r) = defectOp n + shiftOp n ∘L defectOp r ∘L backOp n := by
  ext f k
  have hleft : (defectOp (n + r) f : ℕ → ℂ) k = if k < n + r then (f : ℕ → ℂ) k else 0 :=
    defectOp_apply (n + r) f k
  have hright : ((shiftOp n ∘L defectOp r ∘L backOp n) f : ℕ → ℂ) k
      = if k < n then 0 else (if k - n < r then (f : ℕ → ℂ) k else 0) := by
    show shiftFun n (fun j => (defectOp r (backOp n f) : ℕ → ℂ) j) k = _
    by_cases h : k < n
    · rw [shiftFun_of_lt h, if_pos h]
    · rw [shiftFun_of_le (by omega), if_neg h, defectOp_apply, backOp_apply]
      have : k - n + n = k := by omega
      rw [this]
  rw [add_apply]
  show (defectOp (n + r) f : ℕ → ℂ) k
      = (defectOp n f : ℕ → ℂ) k + ((shiftOp n ∘L defectOp r ∘L backOp n) f : ℕ → ℂ) k
  rw [hleft, hright, defectOp_apply]
  by_cases h : k < n
  · rw [if_pos h, if_pos h, if_pos (by omega), add_zero]
  · rw [if_neg h, if_neg h, zero_add]
    by_cases h2 : k - n < r
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

/-- **Clause 3, orthogonality.**  The two summands of the cocycle law have orthogonal ranges: their
product in either order vanishes. -/
theorem defectOp_orthogonal (n r : ℕ) :
    defectOp n ∘L (shiftOp n ∘L defectOp r ∘L backOp n) = 0 ∧
      (shiftOp n ∘L defectOp r ∘L backOp n) ∘L defectOp n = 0 := by
  constructor
  · ext f k
    show (defectOp n (shiftOp n (defectOp r (backOp n f))) : ℕ → ℂ) k = 0
    rw [defectOp_apply]
    by_cases h : k < n
    · rw [if_pos h, shiftOp_apply, shiftFun_of_lt h]
    · rw [if_neg h]
  · ext f k
    show shiftFun n (fun j => (defectOp r (backOp n (defectOp n f)) : ℕ → ℂ) j) k = 0
    by_cases h : k < n
    · rw [shiftFun_of_lt h]
    · rw [shiftFun_of_le (by omega)]
      have hinner : (backOp n (defectOp n f) : ℕ → ℂ) (k - n) = 0 := by
        rw [backOp_apply, defectOp_apply, if_neg (by omega)]
      rw [defectOp_apply, hinner]
      simp

/-! ## The defect range and its dimension -/

/-- The coordinate subspace of sequences supported in the first `n` slots. -/
def defectSubmodule (n : ℕ) : Submodule ℂ ToeplitzSpace where
  carrier := {f : ToeplitzSpace | ∀ k, n ≤ k → (f : ℕ → ℂ) k = 0}
  add_mem' hf hg := by
    intro k hk
    simp [hf k hk, hg k hk]
  zero_mem' := by
    intro k _
    simp
  smul_mem' c f hf := by
    intro k hk
    simp [hf k hk]

theorem mem_defectSubmodule {n : ℕ} {f : ToeplitzSpace} :
    f ∈ defectSubmodule n ↔ ∀ k, n ≤ k → (f : ℕ → ℂ) k = 0 := Iff.rfl

theorem defectOp_mem (n : ℕ) (f : ToeplitzSpace) : defectOp n f ∈ defectSubmodule n := by
  intro k hk
  rw [defectOp_apply, if_neg (by omega)]

theorem defectOp_eq_self_of_mem {n : ℕ} {f : ToeplitzSpace} (hf : f ∈ defectSubmodule n) :
    defectOp n f = f := by
  ext k
  rw [defectOp_apply]
  by_cases h : k < n
  · rw [if_pos h]
  · rw [if_neg h]
    exact (hf k (by omega)).symm

/-- The finitely supported coordinate vector attached to `v ∈ ℂⁿ`. -/
def coordVec (n : ℕ) (v : Fin n → ℂ) : ToeplitzSpace :=
  ⟨fun k => if h : k < n then v ⟨k, h⟩ else 0, by
    refine memℓp_gen (summable_of_ne_finset_zero (s := Finset.range n) ?_)
    intro k hk
    rw [dif_neg (by simpa using hk)]
    simp⟩

@[simp] theorem coordVec_apply (n : ℕ) (v : Fin n → ℂ) (k : ℕ) :
    (coordVec n v : ℕ → ℂ) k = if h : k < n then v ⟨k, h⟩ else 0 := rfl

theorem coordVec_mem (n : ℕ) (v : Fin n → ℂ) : coordVec n v ∈ defectSubmodule n := by
  intro k hk
  rw [coordVec_apply, dif_neg (by omega)]

/-- **Clause 2, dimension.**  The defect subspace is `n`-dimensional: restriction to the first `n`
coordinates is a linear isomorphism onto `ℂⁿ`. -/
def defectCoordEquiv (n : ℕ) : (defectSubmodule n) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun f := fun i => ((f : ToeplitzSpace) : ℕ → ℂ) (i : ℕ)
  map_add' f g := by
    funext i
    simp
  map_smul' c f := by
    funext i
    simp
  invFun v := ⟨coordVec n v, coordVec_mem n v⟩
  left_inv f := by
    apply Subtype.ext
    ext k
    rw [coordVec_apply]
    by_cases h : k < n
    · rw [dif_pos h]
    · rw [dif_neg h]
      exact (f.2 k (by omega)).symm
  right_inv v := by
    funext i
    show (coordVec n v : ℕ → ℂ) (i : ℕ) = v i
    rw [coordVec_apply, dif_pos i.isLt]

theorem finrank_defectSubmodule (n : ℕ) : Module.finrank ℂ (defectSubmodule n) = n := by
  rw [(defectCoordEquiv n).finrank_eq, Module.finrank_pi ℂ]
  simp

/-- The defect, viewed as a surjection onto the `n`-dimensional coordinate subspace. -/
def defectMap (n : ℕ) : ToeplitzSpace →ₗ[ℂ] (defectSubmodule n) where
  toFun f := ⟨defectOp n f, defectOp_mem n f⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp

theorem defectMap_surjective (n : ℕ) : Function.Surjective (defectMap n) := by
  intro f
  refine ⟨(f : ToeplitzSpace), ?_⟩
  apply Subtype.ext
  exact defectOp_eq_self_of_mem f.2

/-! ## Kernel and cokernel of the shift -/

theorem ker_shiftOp (n : ℕ) :
    LinearMap.ker (shiftOp n).toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro f hf
  have h : ∀ k, (f : ℕ → ℂ) k = 0 := by
    intro k
    have := congrArg (fun g : ToeplitzSpace => (g : ℕ → ℂ) (k + n)) hf
    simpa using this
  exact lp.ext (funext h)

theorem range_shiftOp (n : ℕ) :
    LinearMap.range (shiftOp n).toLinearMap = LinearMap.ker (defectMap n) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    ext k
    show (defectOp n (shiftOp n g) : ℕ → ℂ) k = 0
    rw [defectOp_apply]
    by_cases h : k < n
    · rw [if_pos h, shiftOp_apply, shiftFun_of_lt h]
    · rw [if_neg h]
  · intro hf
    have hzero : ∀ k, k < n → (f : ℕ → ℂ) k = 0 := by
      intro k hk
      have := congrArg (fun g : defectSubmodule n => ((g : ToeplitzSpace) : ℕ → ℂ) k) hf
      simpa [defectMap, hk] using this
    refine ⟨backOp n f, ?_⟩
    ext k
    show shiftFun n (fun j => (f : ℕ → ℂ) (j + n)) k = (f : ℕ → ℂ) k
    by_cases h : k < n
    · rw [shiftFun_of_lt h, (hzero k h)]
    · rw [shiftFun_of_le (by omega)]
      have hk : k - n + n = k := by omega
      show (f : ℕ → ℂ) (k - n + n) = (f : ℕ → ℂ) k
      rw [hk]

/-- **Clause 6.**  The cokernel of `Sⁿ` is the `n`-dimensional defect subspace. -/
def cokerShiftEquiv (n : ℕ) :
    (ToeplitzSpace ⧸ LinearMap.range (shiftOp n).toLinearMap) ≃ₗ[ℂ] (defectSubmodule n) :=
  (Submodule.quotEquivOfEq _ _ (range_shiftOp n)).trans
    (LinearMap.quotKerEquivOfSurjective (defectMap n) (defectMap_surjective n))

theorem finrank_ker_shiftOp (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (shiftOp n).toLinearMap) = 0 := by
  rw [ker_shiftOp]
  simp

/-- **Clause 6.**  `dim coker Sⁿ = n`, so `Sⁿ` has index `−n`. -/
theorem finrank_coker_shiftOp (n : ℕ) :
    Module.finrank ℂ (ToeplitzSpace ⧸ LinearMap.range (shiftOp n).toLinearMap) = n := by
  rw [(cokerShiftEquiv n).finrank_eq, finrank_defectSubmodule]

/-- The Fredholm index of the `n`-fold shift. -/
def shiftIndex (n : ℕ) : ℤ :=
  (Module.finrank ℂ (LinearMap.ker (shiftOp n).toLinearMap) : ℤ)
    - (Module.finrank ℂ (ToeplitzSpace ⧸ LinearMap.range (shiftOp n).toLinearMap) : ℤ)

/-- **Clause 6, equation (6).**  `ind Sⁿ = −n`. -/
theorem shiftIndex_eq (n : ℕ) : shiftIndex n = -(n : ℤ) := by
  rw [shiftIndex, finrank_ker_shiftOp, finrank_coker_shiftOp]
  simp

/-! ## The finite boundary observer -/

/-- The boundary observer at a primitive `m`-th root of unity, equation (3). -/
noncomputable def boundaryObserver (m n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * n / m)

/-- **Clause 4.**  Every finite boundary observer is `m`-periodic. -/
theorem boundaryObserver_add (m n : ℕ) (hm : m ≠ 0) :
    boundaryObserver m (n + m) = boundaryObserver m n := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [boundaryObserver, boundaryObserver]
  have hsplit : 2 * (Real.pi : ℂ) * Complex.I * ((n + m : ℕ) : ℂ) / (m : ℂ)
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (m : ℂ)
        + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Clause 5.**  Along the return sequence `n = km` the observer is back at one. -/
theorem boundaryObserver_mul (m k : ℕ) (hm : m ≠ 0) :
    boundaryObserver m (k * m) = 1 := by
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [boundaryObserver]
  have hsplit : 2 * (Real.pi : ℂ) * Complex.I * ((k * m : ℕ) : ℂ) / (m : ℂ)
      = (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [hsplit, Complex.exp_int_mul_two_pi_mul_I]

/-- **Clause 5.**  The defect rank diverges along the observer return sequence. -/
theorem finrank_defect_return_tendsto (m : ℕ) (hm : m ≠ 0) :
    Filter.Tendsto (fun k : ℕ => Module.finrank ℂ (defectSubmodule (k * m)))
      Filter.atTop Filter.atTop := by
  have hfun : (fun k : ℕ => Module.finrank ℂ (defectSubmodule (k * m)))
      = fun k : ℕ => k * m := by
    funext k
    exact finrank_defectSubmodule (k * m)
  rw [hfun]
  exact Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha =>
    le_trans ha (Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hm))⟩

/-- **Clauses 4–6 together.**  The exact recurrence/divergence split of the shift: the boundary
observer has returned to one while the defect rank equals `km` and the index equals `−km`. -/
theorem recurrent_boundary_open_defect (m k : ℕ) (hm : m ≠ 0) :
    boundaryObserver m (k * m) = 1 ∧
      Module.finrank ℂ (defectSubmodule (k * m)) = k * m ∧
      shiftIndex (k * m) = -((k * m : ℕ) : ℤ) :=
  ⟨boundaryObserver_mul m k hm, finrank_defectSubmodule (k * m), shiftIndex_eq (k * m)⟩

/-! ## The boundary class -/

theorem range_defectOp (n : ℕ) :
    LinearMap.range (defectOp n).toLinearMap = defectSubmodule n := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact defectOp_mem n g
  · intro hf
    exact ⟨f, defectOp_eq_self_of_mem hf⟩

/-- The kernel defect `1 − S*ⁿSⁿ` vanishes: the shift is an isometry. -/
theorem coDefect_eq_zero (n : ℕ) :
    ContinuousLinearMap.id ℂ ToeplitzSpace - backOp n ∘L shiftOp n = 0 := by
  rw [backOp_comp_shiftOp, sub_self]

/-- The concrete boundary class of the winding unitary `zⁿ`, computed in `K₀(𝒦) ≅ ℤ` by rank:
`∂[zⁿ] = [1 − S*ⁿSⁿ] − [1 − SⁿS*ⁿ]`. -/
def toeplitzDefectBoundaryClass (n : ℕ) : ℤ :=
  (Module.finrank ℂ
      (LinearMap.range
        (ContinuousLinearMap.id ℂ ToeplitzSpace - backOp n ∘L shiftOp n).toLinearMap) : ℤ)
    - (Module.finrank ℂ (LinearMap.range (defectOp n).toLinearMap) : ℤ)

/-- **Clause 7, equation (7).**  The boundary class is minus the defect class. -/
theorem boundaryClass_eq_neg_defect (n : ℕ) :
    toeplitzDefectBoundaryClass n = -(Module.finrank ℂ (LinearMap.range (defectOp n).toLinearMap) : ℤ) := by
  rw [toeplitzDefectBoundaryClass, coDefect_eq_zero]
  have hbot : LinearMap.range (0 : ToeplitzSpace →L[ℂ] ToeplitzSpace).toLinearMap
      = (⊥ : Submodule ℂ ToeplitzSpace) := by simp
  rw [hbot]
  simp

theorem boundaryClass_eq (n : ℕ) : toeplitzDefectBoundaryClass n = -(n : ℤ) := by
  rw [boundaryClass_eq_neg_defect, range_defectOp, finrank_defectSubmodule]

/-- **The boundary class is the Fredholm index.** -/
theorem boundaryClass_eq_shiftIndex (n : ℕ) : toeplitzDefectBoundaryClass n = shiftIndex n := by
  rw [boundaryClass_eq, shiftIndex_eq]

theorem shiftOp_not_surjective {n : ℕ} (hn : 0 < n) :
    ¬ Function.Surjective (shiftOp n) := by
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj (lp.single 2 0 (1 : ℂ))
  have h0 := congrArg (fun f : ToeplitzSpace => (f : ℕ → ℂ) 0) hg
  rw [shiftOp_apply, shiftFun_of_lt hn] at h0
  rw [lp.single_apply] at h0
  simp at h0

/-! ## Clause 8 — nonliftability of the winding unitary -/

/-- **Clause 8, operator form.**  For `n > 0` no invertible operator differs from `Sⁿ` by a compact
operator. -/
theorem no_invertible_compact_perturbation {n : ℕ} (hn : 0 < n)
    (U : ToeplitzSpace →L[ℂ] ToeplitzSpace) (hU : Function.Bijective U)
    (hcomp : IsCompactOperator (U - shiftOp n)) : False := by
  obtain ⟨u, hu⟩ := (ContinuousLinearMap.isUnit_iff_bijective).mpr hU
  set V : ToeplitzSpace →L[ℂ] ToeplitzSpace := (↑u⁻¹ : ToeplitzSpace →L[ℂ] ToeplitzSpace) with hV
  have hVU : V * U = 1 := by rw [hV, ← hu]; exact u.inv_mul
  have hUV : U * V = 1 := by rw [hV, ← hu]; exact u.mul_inv
  have hVUapp : ∀ x, V (U x) = x := by
    intro x
    have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T x) hVU
    simpa using this
  have hUVapp : ∀ x, U (V x) = x := by
    intro x
    have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T x) hUV
    simpa using this
  set C : ToeplitzSpace →L[ℂ] ToeplitzSpace := V ∘L (U - shiftOp n) with hC
  have hCcomp : IsCompactOperator C := hcomp.clm_comp V
  have hkey : ∀ x, V (shiftOp n x) = x - C x := by
    intro x
    have hCx : C x = V (U x) - V (shiftOp n x) := by
      rw [hC]
      show V ((U - shiftOp n) x) = _
      rw [sub_apply, map_sub]
    rw [hCx, hVUapp]
    abel
  have hVinj : Function.Injective V := by
    intro a b hab
    have h1 : U (V a) = U (V b) := congrArg _ hab
    rwa [hUVapp, hUVapp] at h1
  have hinj : Function.Injective (fun x => x - C x) := by
    intro x y hxy
    simp only at hxy
    have h1 : V (shiftOp n x) = V (shiftOp n y) := by rw [hkey, hkey, hxy]
    exact (shiftIsom n).injective (hVinj h1)
  have hnoeig : ¬ Module.End.HasEigenvalue (C : Module.End ℂ ToeplitzSpace) 1 := by
    intro hev
    obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
    apply hx.2
    have hCx : C x = x := by
      have := hx.apply_eq_smul
      simpa using this
    have hz : (fun z => z - C z) x = (fun z => z - C z) 0 := by
      simp [hCx]
    exact hinj hz
  have hres : (1 : ℂ) ∈ resolventSet ℂ C := by
    rcases IsCompactOperator.hasEigenvalue_or_mem_resolventSet hCcomp one_ne_zero with h | h
    · exact absurd h hnoeig
    · exact h
  have hunit : IsUnit ((1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) - C) := by
    rw [spectrum.mem_resolventSet_iff] at hres
    simpa using hres
  have hbij : Function.Bijective ((1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) - C) :=
    (ContinuousLinearMap.isUnit_iff_bijective).mp hunit
  refine shiftOp_not_surjective hn ?_
  intro y
  obtain ⟨x, hx⟩ := hbij.2 (V y)
  refine ⟨x, ?_⟩
  have hxx : x - C x = V y := by
    have h2 := hx
    rw [sub_apply, one_apply_eq_self] at h2
    exact h2
  have h1 : V (shiftOp n x) = V y := by rw [hkey, hxx]
  exact hVinj h1

/-- **Clause 8.**  For `n > 0` the winding unitary `zⁿ` has no unitary lift: no unitary operator
differs from `Sⁿ` by a compact operator. -/
theorem no_unitary_compact_perturbation {n : ℕ} (hn : 0 < n)
    (U : ToeplitzSpace →L[ℂ] ToeplitzSpace)
    (hUU : ContinuousLinearMap.adjoint U ∘L U = 1)
    (hUU' : U ∘L ContinuousLinearMap.adjoint U = 1)
    (hcomp : IsCompactOperator (U - shiftOp n)) : False := by
  have h1 : ∀ x, ContinuousLinearMap.adjoint U (U x) = x := by
    intro x
    have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T x) hUU
    simpa using this
  have h2 : ∀ x, U (ContinuousLinearMap.adjoint U x) = x := by
    intro x
    have := congrArg (fun T : ToeplitzSpace →L[ℂ] ToeplitzSpace => T x) hUU'
    simpa using this
  refine no_invertible_compact_perturbation hn U ⟨?_, ?_⟩ hcomp
  · intro a b hab
    rw [← h1 a, ← h1 b, hab]
  · intro y
    exact ⟨ContinuousLinearMap.adjoint U y, h2 y⟩

/-- **The eight clauses of the law, on one producer.**  One one-sided isometry gives the positivity
relation, the exact defect projection with linearly growing rank, the orthogonal cocycle law, the
recurrent boundary observer, the divergent defect along observer returns, the index `−n`, the
boundary class `−[Dₙ]`, and the nonliftability of the winding unitary. -/
theorem toeplitz_recurrent_boundary_open_defect_index {n m k : ℕ} (hn : 0 < n) (hm : m ≠ 0) :
    backOp n ∘L shiftOp n = ContinuousLinearMap.id ℂ ToeplitzSpace ∧
      Module.finrank ℂ (defectSubmodule n) = n ∧
      (∀ r : ℕ, defectOp (n + r) = defectOp n + shiftOp n ∘L defectOp r ∘L backOp n) ∧
      boundaryObserver m (n + m) = boundaryObserver m n ∧
      (boundaryObserver m (k * m) = 1 ∧ Module.finrank ℂ (defectSubmodule (k * m)) = k * m) ∧
      shiftIndex n = -(n : ℤ) ∧
      toeplitzDefectBoundaryClass n = -(Module.finrank ℂ (LinearMap.range (defectOp n).toLinearMap) : ℤ) ∧
      (∀ U : ToeplitzSpace →L[ℂ] ToeplitzSpace,
        ContinuousLinearMap.adjoint U ∘L U = 1 → U ∘L ContinuousLinearMap.adjoint U = 1 →
        ¬ IsCompactOperator (U - shiftOp n)) :=
  ⟨backOp_comp_shiftOp n, finrank_defectSubmodule n, defectOp_add n,
    boundaryObserver_add m n hm,
    ⟨boundaryObserver_mul m k hm, finrank_defectSubmodule (k * m)⟩,
    shiftIndex_eq n, boundaryClass_eq_neg_defect n,
    fun U hUU hUU' hcomp => no_unitary_compact_perturbation hn U hUU hUU' hcomp⟩

end

end GaloisForLFunctions.HTGeometry
