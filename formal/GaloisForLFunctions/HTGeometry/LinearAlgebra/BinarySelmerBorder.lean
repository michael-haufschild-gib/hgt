import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerDictionary

/-!
# The exact bordered determinant test in descent coordinates

The two descent equations force `zᵀu=0` and `yᵀu=yᵀv`.
After the explicit kernel change of coordinates, the border `(y+z,0)`
pairs with a kernel vector as `yᵀu+zᵀv`. Thus its determinant is nonzero
exactly when the original kernel is a line detected by this functional.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binarySelmerShear_mulVec (y v : ι → ZMod 2) :
    binarySelmerShear y *ᵥ v = v + (y ⬝ᵥ v) • 1 := by
  rw [binarySelmerShear, add_mulVec, one_mulVec, vecMulVec_mulVec]
  funext i
  change v i + (1 : ZMod 2) * (y ⬝ᵥ v) = v i + (y ⬝ᵥ v) * 1
  rw [one_mul, mul_one]

theorem binarySelmerChange_inl (y : ι → ZMod 2) (v : ι ⊕ ι → ZMod 2) :
    (binarySelmerChange y *ᵥ v) ∘ Sum.inl =
      (v ∘ Sum.inl) + ((v ∘ Sum.inr) + (y ⬝ᵥ (v ∘ Sum.inr)) • 1) := by
  rw [binarySelmerChange, fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, one_mulVec, binarySelmerShear_mulVec]

/-- Membership in the nonsymmetric kernel is the pair of descent equations. -/
theorem binarySelmerSource_kernel_iff (A : Matrix ι ι (ZMod 2))
    (y z : ι → ZMod 2) (v : ι ⊕ ι → ZMod 2) :
    binarySelmerSource A y z *ᵥ v = 0 ↔
      A *ᵥ (v ∘ Sum.inl) + diagonal y *ᵥ (v ∘ Sum.inr) = 0 ∧
      diagonal z *ᵥ (v ∘ Sum.inl) + (A + diagonal y) *ᵥ (v ∘ Sum.inr) = 0 := by
  rw [binarySelmerSource, fromBlocks_mulVec]
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (Sum.inl i)),
      funext (fun i => congrFun h (Sum.inr i))⟩
  · rintro ⟨htop, hbottom⟩
    funext i
    cases i with
    | inl i => exact congrFun htop i
    | inr i => exact congrFun hbottom i

/-- The change of variables transports the kernel condition in both directions. -/
theorem binarySelmer_kernel_iff (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) (v : ι ⊕ ι → ZMod 2) :
    binarySelmerSource A y z *ᵥ v = 0 ↔
      binarySelmerSymmetric A z *ᵥ (binarySelmerChange y *ᵥ v) = 0 := by
  have h := congrArg (fun B : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) => B *ᵥ v)
    (binarySelmer_intertwining A y z hA hrec hy)
  rw [← mulVec_mulVec, ← mulVec_mulVec] at h
  constructor
  · intro hv
    rw [h, hv, mulVec_zero]
  · intro hv
    apply (binarySelmerRowEquiv (ι := ι)).injective
    change binarySelmerRowChange *ᵥ (binarySelmerSource A y z *ᵥ v) =
      binarySelmerRowChange *ᵥ 0
    rw [← h, hv, mulVec_zero]

private theorem diagonal_mulVec_one (y : ι → ZMod 2) : diagonal y *ᵥ 1 = y := by
  funext i
  simp only [mulVec_diagonal, Pi.one_apply, mul_one]

/-- The conditions at the even prime follow from the two finite descent
equations and quadratic reciprocity. -/
theorem binarySelmer_kernel_relations (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) {v : ι ⊕ ι → ZMod 2}
    (hv : binarySelmerSource A y z *ᵥ v = 0) :
    z ⬝ᵥ (v ∘ Sum.inl) = 0 ∧ y ⬝ᵥ (v ∘ Sum.inl) = y ⬝ᵥ (v ∘ Sum.inr) := by
  have hsumA (w : ι → ZMod 2) : 1 ⬝ᵥ (A *ᵥ w) = y ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, binarySelmer_transpose_one A y hA hrec hy]
  have hsumD (a w : ι → ZMod 2) : 1 ⬝ᵥ (diagonal a *ᵥ w) = a ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, diagonal_transpose, diagonal_mulVec_one]
  obtain ⟨htop, hbottom⟩ := (binarySelmerSource_kernel_iff A y z v).mp hv
  have htopSum := congrArg (fun w : ι → ZMod 2 => 1 ⬝ᵥ w) htop
  rw [dotProduct_add, hsumA, hsumD, dotProduct_zero] at htopSum
  have hbottomSum := congrArg (fun w : ι → ZMod 2 => 1 ⬝ᵥ w) hbottom
  rw [dotProduct_add, hsumD, add_mulVec, dotProduct_add, hsumA, hsumD,
    CharTwo.add_self_eq_zero, add_zero, dotProduct_zero] at hbottomSum
  refine ⟨hbottomSum, ?_⟩
  calc
    y ⬝ᵥ (v ∘ Sum.inl) = y ⬝ᵥ (v ∘ Sum.inl) +
        (y ⬝ᵥ (v ∘ Sum.inr) + y ⬝ᵥ (v ∘ Sum.inr)) := by
      rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (y ⬝ᵥ (v ∘ Sum.inl) + y ⬝ᵥ (v ∘ Sum.inr)) +
        y ⬝ᵥ (v ∘ Sum.inr) := by abel
    _ = y ⬝ᵥ (v ∘ Sum.inr) := by rw [htopSum, zero_add]

omit [DecidableEq ι] in
private theorem dot_sum_elim (a b : ι → ZMod 2) (v : ι ⊕ ι → ZMod 2) :
    Sum.elim a b ⬝ᵥ v = a ⬝ᵥ (v ∘ Sum.inl) + b ⬝ᵥ (v ∘ Sum.inr) := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply]

/-- The border pairing reduces to the descent functional on the source kernel. -/
theorem binarySelmer_border_pairing (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) (hz : z ⬝ᵥ 1 = 1) {v : ι ⊕ ι → ZMod 2}
    (hv : binarySelmerSource A y z *ᵥ v = 0) :
    Sum.elim (y + z) 0 ⬝ᵥ (binarySelmerChange y *ᵥ v) =
      y ⬝ᵥ (v ∘ Sum.inl) + z ⬝ᵥ (v ∘ Sum.inr) := by
  have hzu := (binarySelmer_kernel_relations A y z hA hrec hy hv).1
  rw [dot_sum_elim, zero_dotProduct, add_zero, binarySelmerChange_inl]
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_eq_mul,
    hy, hz, hzu, zero_add, add_zero, mul_one]
  calc
    _ = (y ⬝ᵥ (v ∘ Sum.inl) + z ⬝ᵥ (v ∘ Sum.inr)) +
        (y ⬝ᵥ (v ∘ Sum.inr) + y ⬝ᵥ (v ∘ Sum.inr)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem binarySelmerSymmetric_isSymm (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    (binarySelmerSymmetric A z).IsSymm := by
  change (binarySelmerSymmetric A z)ᵀ = binarySelmerSymmetric A z
  ext i j
  cases i <;> cases j <;>
    simp [binarySelmerSymmetric, fromBlocks, transpose_apply, diagonal, add_comm, eq_comm]

/-- Being generated by a specified kernel vector is preserved by the dictionary. -/
theorem binarySelmer_kernel_line_iff (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) (κ : ι ⊕ ι → ZMod 2) :
    (∀ v, binarySelmerSource A y z *ᵥ v = 0 → ∃ a : ZMod 2, v = a • κ) ↔
      (∀ w, binarySelmerSymmetric A z *ᵥ w = 0 →
        ∃ a : ZMod 2, w = a • (binarySelmerChange y *ᵥ κ)) := by
  let e := binarySelmerChangeEquiv y hy
  constructor
  · intro h w hw
    have hback : binarySelmerSource A y z *ᵥ e.symm w = 0 := by
      apply (binarySelmer_kernel_iff A y z hA hrec hy _).mpr
      change binarySelmerSymmetric A z *ᵥ e (e.symm w) = 0
      rw [e.apply_symm_apply]
      exact hw
    obtain ⟨a, ha⟩ := h (e.symm w) hback
    refine ⟨a, ?_⟩
    have heq := congrArg e ha
    simpa only [e.apply_symm_apply, map_smul] using heq
  · intro h v hv
    have hforward := (binarySelmer_kernel_iff A y z hA hrec hy v).mp hv
    obtain ⟨a, ha⟩ := h (e v) hforward
    refine ⟨a, e.injective ?_⟩
    rw [map_smul]
    exact ha

/-- Exact bordered determinant criterion expressed entirely in the
original descent coordinates. -/
theorem binarySelmer_border_det_ne_zero_iff (A : Matrix ι ι (ZMod 2)) (y z : ι → ZMod 2)
    (hA : A *ᵥ 1 = 0) (hrec : A + Aᵀ = vecMulVec y y + diagonal y)
    (hy : y ⬝ᵥ 1 = 0) (hz : z ⬝ᵥ 1 = 1)
    {κ : ι ⊕ ι → ZMod 2} (hκne : κ ≠ 0) (hκ : binarySelmerSource A y z *ᵥ κ = 0) :
    (symmetricBorder (binarySelmerSymmetric A z) (Sum.elim (y + z) 0)).det ≠ 0 ↔
      (∀ v, binarySelmerSource A y z *ᵥ v = 0 → ∃ a : ZMod 2, v = a • κ) ∧
        y ⬝ᵥ (κ ∘ Sum.inl) + z ⬝ᵥ (κ ∘ Sum.inr) ≠ 0 := by
  have hκ' := (binarySelmer_kernel_iff A y z hA hrec hy κ).mp hκ
  have hκne' : binarySelmerChange y *ᵥ κ ≠ 0 := by
    intro h
    apply hκne
    apply (binarySelmerChangeEquiv y hy).injective
    change binarySelmerChange y *ᵥ κ = binarySelmerChange y *ᵥ 0
    rw [h, mulVec_zero]
  rw [symmetricBorder_det_ne_zero_iff (binarySelmerSymmetric_isSymm A z) hκne' hκ',
    ← binarySelmer_kernel_line_iff A y z hA hrec hy κ,
    binarySelmer_border_pairing A y z hA hrec hy hz hκ]

#print axioms binarySelmer_kernel_relations
#print axioms binarySelmer_border_det_ne_zero_iff

end GaloisForLFunctions.HTGeometry.LinearAlgebra
