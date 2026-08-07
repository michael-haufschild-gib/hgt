import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraUnit

/-!
# The product of single-bidegree elements, and the two inclusions

A single-bidegree element multiplies with another by a one-term sum: only the splitting given by the
two bidegrees survives, the others killing one of the two factors.  With the units of the two
algebras this gives the two inclusions of a tensor product of algebras.

* `HTGeometry.tensorAlgMul_tensorSingle` : the product of two single-bidegree elements.
* `HTGeometry.tensorCDGAInclLeft`, `HTGeometry.tensorCDGAInclRight` : the two inclusions.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- **The product of two single-bidegree elements is a one-term sum.** -/
theorem tensorAlgMul_tensorSingle {a b n : ℕ} (h : a + b = n)
    (r : {ab : ℕ × ℕ // ab.1 + ab.2 = a}) (s : {ab : ℕ × ℕ // ab.1 + ab.2 = b})
    (z : TensorProduct R (X r.1.1) (Y r.1.2)) (w : TensorProduct R (X s.1.1) (Y s.1.2))
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (hp1 : r.1.1 + s.1.1 = p.1.1) (hp2 : r.1.2 + s.1.2 = p.1.2) :
    tensorAlgMul A B h (tensorSingle (M := X) (N := Y) r z)
        (tensorSingle (M := X) (N := Y) s w) p
      = tensorPairₗ A B hp1 hp2 z w := by
  classical
  show (∑ rs : Splitting a b p, splittingTerm A B (tensorSingle (M := X) (N := Y) r z)
    (tensorSingle (M := X) (N := Y) s w) rs) = _
  rw [Finset.sum_eq_single_of_mem (⟨(r, s), ⟨hp1, hp2⟩⟩ : Splitting a b p) (Finset.mem_univ _)
    (fun rs _ hne => ?_)]
  · show tensorPairₗ A B hp1 hp2 (tensorSingle (M := X) (N := Y) r z r)
      (tensorSingle (M := X) (N := Y) s w s) = _
    rw [tensorSingle_same, tensorSingle_same]
  · by_cases hr : rs.1.1 = r
    · exfalso
      apply hne
      subst hr
      have e1 : rs.1.1.1.1 + rs.1.2.1.1 = p.1.1 := rs.2.1
      have e2 : rs.1.1.1.2 + rs.1.2.1.2 = p.1.2 := rs.2.2
      have e3 : rs.1.1.1.1 + s.1.1 = p.1.1 := hp1
      have e4 : rs.1.1.1.2 + s.1.2 = p.1.2 := hp2
      exact Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext
        (Nat.add_left_cancel (e1.trans e3.symm)) (Nat.add_left_cancel (e2.trans e4.symm)))))
    · show tensorPairₗ A B rs.2.1 rs.2.2 (tensorSingle (M := X) (N := Y) r z rs.1.1)
        (tensorSingle (M := X) (N := Y) s w rs.1.2) = 0
      rw [tensorSingle_ne _ hr, map_zero, LinearMap.zero_apply]

/-- **Off the sum of the two bidegrees the product of two single-bidegree elements vanishes.** -/
theorem tensorAlgMul_tensorSingle_ne {a b n : ℕ} (h : a + b = n)
    (r : {ab : ℕ × ℕ // ab.1 + ab.2 = a}) (s : {ab : ℕ × ℕ // ab.1 + ab.2 = b})
    (z : TensorProduct R (X r.1.1) (Y r.1.2)) (w : TensorProduct R (X s.1.1) (Y s.1.2))
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (hne : ¬(r.1.1 + s.1.1 = p.1.1 ∧ r.1.2 + s.1.2 = p.1.2)) :
    tensorAlgMul A B h (tensorSingle (M := X) (N := Y) r z)
        (tensorSingle (M := X) (N := Y) s w) p = 0 := by
  show (∑ rs : Splitting a b p, splittingTerm A B (tensorSingle (M := X) (N := Y) r z)
    (tensorSingle (M := X) (N := Y) s w) rs) = 0
  refine Finset.sum_eq_zero fun rs _ => ?_
  by_cases hr : rs.1.1 = r
  · have e1 : rs.1.1.1.1 + rs.1.2.1.1 = p.1.1 := rs.2.1
    have e2 : rs.1.1.1.2 + rs.1.2.1.2 = p.1.2 := rs.2.2
    have h3 : rs.1.1.1.1 = r.1.1 := by rw [hr]
    have h4 : rs.1.1.1.2 = r.1.2 := by rw [hr]
    have hs : rs.1.2 ≠ s := by
      intro hs
      refine hne ⟨?_, ?_⟩
      · rw [← h3, ← show rs.1.2.1.1 = s.1.1 by rw [hs]]
        exact e1
      · rw [← h4, ← show rs.1.2.1.2 = s.1.2 by rw [hs]]
        exact e2
    show tensorPairₗ A B rs.2.1 rs.2.2 (tensorSingle (M := X) (N := Y) r z rs.1.1)
      (tensorSingle (M := X) (N := Y) s w rs.1.2) = 0
    rw [tensorSingle_ne _ hs, map_zero]
  · show tensorPairₗ A B rs.2.1 rs.2.2 (tensorSingle (M := X) (N := Y) r z rs.1.1)
      (tensorSingle (M := X) (N := Y) s w rs.1.2) = 0
    rw [tensorSingle_ne _ hr, map_zero, LinearMap.zero_apply]

section Inclusions

variable {A B}

/-- The value of `x ⊗ t`, placed in the bidegree `(n, 0)`, at a bidegree with second coordinate
zero. -/
theorem tensorSingleRight_apply (n : ℕ) (x : X n) (t : Y 0)
    (hn : (n, 0).1 + (n, 0).2 = n) :
    tensorSingle (M := X) (N := Y) (⟨(n, 0), hn⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
      (x ⊗ₜ[R] t) ⟨(n, 0), hn⟩ = x ⊗ₜ[R] t :=
  tensorSingle_same (M := X) (N := Y) _ _

/-- The same element vanishes at every other bidegree. -/
theorem tensorSingleRight_apply_ne (n : ℕ) (x : X n) (t : Y 0)
    (hn : (n, 0).1 + (n, 0).2 = n) {α β : ℕ} (hαβ : (α, β).1 + (α, β).2 = n) (hβ : β ≠ 0) :
    tensorSingle (M := X) (N := Y) (⟨(n, 0), hn⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
      (x ⊗ₜ[R] t) ⟨(α, β), hαβ⟩ = 0 :=
  tensorSingle_ne _ (by rw [Ne, tensorIndex_eq_iff]; omega)

/-- **The external differential of `x ⊗ 1`.** -/
theorem extTensorD_tensorSingleRight (A : CDGAStructure R X) (B : CDGAStructure R Y)
    (v : CDGAUnit B) (n : ℕ) (x : X n)
    (hn : (n, 0).1 + (n, 0).2 = n) (hn1 : (n + 1, 0).1 + (n + 1, 0).2 = n + 1) :
    extTensorD A B n (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one))
      = tensorSingle (M := X) (N := Y) ⟨(n + 1, 0), hn1⟩ (A.d n x ⊗ₜ[R] v.one) := by
  funext p
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
  show tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one)) ⟨(p₁, p₂), hp⟩
    + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one)) ⟨(p₁, p₂), hp⟩ = _
  cases p₂ with
  | zero =>
      rw [tensorDR_zero, add_zero]
      cases p₁ with
      | zero => exact absurd hp (by omega)
      | succ α =>
          obtain rfl : n = α := by simp only at hp; omega
          rw [tensorDL_succ]
          show TensorProduct.map (A.dₗ n) LinearMap.id
            (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one) ⟨(n, 0), hn⟩) = _
          rw [tensorSingleRight_apply n x v.one hn, TensorProduct.map_tmul,
            tensorSingleRight_apply (n + 1) (A.d n x) v.one hn1]
          rfl
  | succ β =>
      rw [tensorSingleRight_apply_ne (n + 1) (A.d n x) v.one hn1 hp (by omega)]
      cases p₁ with
      | zero =>
          rw [tensorDL_zero, zero_add, tensorDR_succ]
          show ((-1 : R)) ^ 0 • TensorProduct.map LinearMap.id (B.dₗ β)
            (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one)
              ⟨(0, β), by simp only at hp ⊢; omega⟩) = 0
          cases β with
          | zero =>
              obtain rfl : n = 0 := by simp only at hp; omega
              rw [tensorSingleRight_apply 0 x v.one hn, TensorProduct.map_tmul, pow_zero,
                one_smul]
              show (LinearMap.id x : X 0) ⊗ₜ[R] B.d 0 v.one = 0
              rw [v.d_one, TensorProduct.tmul_zero]
          | succ γ =>
              rw [tensorSingleRight_apply_ne n x v.one hn
                (by simp only at hp ⊢; omega) (by omega), map_zero, smul_zero]
      | succ α =>
          rw [tensorDL_succ, tensorDR_succ]
          show TensorProduct.map (A.dₗ α) LinearMap.id
              (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one)
                ⟨(α, β + 1), by simp only at hp ⊢; omega⟩)
            + ((-1 : R)) ^ (α + 1) • TensorProduct.map LinearMap.id (B.dₗ β)
              (tensorSingle (M := X) (N := Y) ⟨(n, 0), hn⟩ (x ⊗ₜ[R] v.one)
                ⟨(α + 1, β), by simp only at hp ⊢; omega⟩) = 0
          rw [tensorSingleRight_apply_ne n x v.one hn (by simp only at hp ⊢; omega) (by omega),
            map_zero, zero_add]
          cases β with
          | zero =>
              obtain rfl : n = α + 1 := by simp only at hp; omega
              rw [tensorSingleRight_apply (α + 1) x v.one hn, TensorProduct.map_tmul]
              show ((-1 : R)) ^ (α + 1) •
                ((LinearMap.id x : X (α + 1)) ⊗ₜ[R] B.d 0 v.one) = 0
              rw [v.d_one, TensorProduct.tmul_zero, smul_zero]
          | succ γ =>
              rw [tensorSingleRight_apply_ne n x v.one hn (by simp only at hp ⊢; omega)
                (by omega), map_zero, smul_zero]

/-- **The left inclusion** of a tensor product of algebras. -/
noncomputable def tensorCDGAInclLeft (A : CDGAStructure R X) (B : CDGAStructure R Y)
    (v : CDGAUnit B) : CDGAHom A (tensorCDGA A B) where
  toFun n x := tensorSingle (M := X) (N := Y)
    (⟨(n, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (x ⊗ₜ[R] v.one)
  map_add n x y := by rw [TensorProduct.add_tmul, tensorSingle_add]
  map_smul n c x := by rw [← TensorProduct.smul_tmul', tensorSingle_smul]
  map_mul := by
    intro a b m h x y
    funext p
    obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
    rw [tensorCDGA_mul]
    by_cases hcase : p₂ = 0
    · subst hcase
      obtain rfl : m = p₁ := by simp only at hp; omega
      rw [tensorAlgMul_tensorSingle A B h _ _ _ _ ⟨(m, 0), hp⟩ h rfl,
        tensorPairₗ_tmul, Nat.zero_mul, pow_zero, one_smul,
        show B.mul (show (0 : ℕ) + 0 = 0 by omega) v.one v.one = v.one from v.one_mul 0 v.one,
        tensorSingleRight_apply m (A.mul h x y) v.one hp]
    · rw [tensorAlgMul_tensorSingle_ne A B h _ _ _ _ ⟨(p₁, p₂), hp⟩ (by
        rintro ⟨-, h2⟩
        exact hcase h2.symm),
        tensorSingleRight_apply_ne m (A.mul h x y) v.one (by omega) hp hcase]
  map_d n x := (extTensorD_tensorSingleRight A B v n x (by omega) (by omega)).symm

/-- The value of `1 ⊗ y`, placed in the bidegree `(0, n)`, at that bidegree. -/
theorem tensorSingleLeft_apply (n : ℕ) (t : X 0) (y : Y n)
    (hn : (0, n).1 + (0, n).2 = n) :
    tensorSingle (M := X) (N := Y) (⟨(0, n), hn⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
      (t ⊗ₜ[R] y) ⟨(0, n), hn⟩ = t ⊗ₜ[R] y :=
  tensorSingle_same (M := X) (N := Y) _ _

/-- The same element vanishes at every other bidegree. -/
theorem tensorSingleLeft_apply_ne (n : ℕ) (t : X 0) (y : Y n)
    (hn : (0, n).1 + (0, n).2 = n) {α β : ℕ} (hαβ : (α, β).1 + (α, β).2 = n) (hα : α ≠ 0) :
    tensorSingle (M := X) (N := Y) (⟨(0, n), hn⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
      (t ⊗ₜ[R] y) ⟨(α, β), hαβ⟩ = 0 :=
  tensorSingle_ne _ (by rw [Ne, tensorIndex_eq_iff]; omega)

/-- **The external differential of `1 ⊗ y`.** -/
theorem extTensorD_tensorSingleLeft (A : CDGAStructure R X) (B : CDGAStructure R Y)
    (u : CDGAUnit A) (n : ℕ) (y : Y n)
    (hn : (0, n).1 + (0, n).2 = n) (hn1 : (0, n + 1).1 + (0, n + 1).2 = n + 1) :
    extTensorD A B n (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y))
      = tensorSingle (M := X) (N := Y) ⟨(0, n + 1), hn1⟩ (u.one ⊗ₜ[R] B.d n y) := by
  funext p
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
  show tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y)) ⟨(p₁, p₂), hp⟩
    + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y)) ⟨(p₁, p₂), hp⟩ = _
  cases p₁ with
  | zero =>
      rw [tensorDL_zero, zero_add]
      cases p₂ with
      | zero => exact absurd hp (by omega)
      | succ β =>
          obtain rfl : n = β := by simp only at hp; omega
          rw [tensorDR_succ]
          show ((-1 : R)) ^ 0 • TensorProduct.map LinearMap.id (B.dₗ n)
            (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y) ⟨(0, n), hn⟩) = _
          rw [tensorSingleLeft_apply n u.one y hn, pow_zero, one_smul, TensorProduct.map_tmul,
            tensorSingleLeft_apply (n + 1) u.one (B.d n y) hn1]
          rfl
  | succ α =>
      rw [tensorSingleLeft_apply_ne (n + 1) u.one (B.d n y) hn1 hp (by omega)]
      cases α with
      | zero =>
          cases p₂ with
          | zero =>
              rw [tensorDR_zero, add_zero, tensorDL_succ]
              obtain rfl : n = 0 := by simp only at hp; omega
              show TensorProduct.map (A.dₗ 0) LinearMap.id
                (tensorSingle (M := X) (N := Y) ⟨(0, 0), hn⟩ (u.one ⊗ₜ[R] y) ⟨(0, 0), hn⟩) = 0
              rw [tensorSingleLeft_apply 0 u.one y hn, TensorProduct.map_tmul]
              show A.d 0 u.one ⊗ₜ[R] (LinearMap.id y : Y 0) = 0
              rw [u.d_one, TensorProduct.zero_tmul]
          | succ β =>
              obtain rfl : n = β + 1 := by simp only at hp; omega
              rw [tensorDL_succ, tensorDR_succ]
              show TensorProduct.map (A.dₗ 0) LinearMap.id
                  (tensorSingle (M := X) (N := Y) ⟨(0, β + 1), hn⟩ (u.one ⊗ₜ[R] y)
                    ⟨(0, β + 1), hn⟩)
                + ((-1 : R)) ^ (0 + 1) • TensorProduct.map LinearMap.id (B.dₗ β)
                  (tensorSingle (M := X) (N := Y) ⟨(0, β + 1), hn⟩ (u.one ⊗ₜ[R] y)
                    ⟨(0 + 1, β), by simp only at hp ⊢; omega⟩) = 0
              have hi2 : (0 + 1, β).1 + (0 + 1, β).2 = β + 1 := by simp only; omega
              rw [tensorSingleLeft_apply_ne (β + 1) u.one y hn hi2 (by omega), map_zero,
                smul_zero, add_zero, tensorSingleLeft_apply (β + 1) u.one y hn,
                TensorProduct.map_tmul]
              show A.d 0 u.one ⊗ₜ[R] (LinearMap.id y : Y (β + 1)) = 0
              rw [u.d_one, TensorProduct.zero_tmul]
      | succ γ =>
          cases p₂ with
          | zero =>
              rw [tensorDR_zero, add_zero, tensorDL_succ]
              show TensorProduct.map (A.dₗ (γ + 1)) LinearMap.id
                (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y)
                  ⟨(γ + 1, 0), by simp only at hp ⊢; omega⟩) = 0
              rw [tensorSingleLeft_apply_ne n u.one y hn (by simp only at hp ⊢; omega)
                (by omega), map_zero]
          | succ β =>
              rw [tensorDL_succ, tensorDR_succ]
              show TensorProduct.map (A.dₗ (γ + 1)) LinearMap.id
                  (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y)
                    ⟨(γ + 1, β + 1), by simp only at hp ⊢; omega⟩)
                + ((-1 : R)) ^ (γ + 1 + 1) • TensorProduct.map LinearMap.id (B.dₗ β)
                  (tensorSingle (M := X) (N := Y) ⟨(0, n), hn⟩ (u.one ⊗ₜ[R] y)
                    ⟨(γ + 1 + 1, β), by simp only at hp ⊢; omega⟩) = 0
              rw [tensorSingleLeft_apply_ne n u.one y hn (by simp only at hp ⊢; omega)
                  (by omega),
                tensorSingleLeft_apply_ne n u.one y hn (by simp only at hp ⊢; omega)
                  (by omega), map_zero, map_zero, smul_zero, add_zero]

/-- **The right inclusion** of a tensor product of algebras. -/
noncomputable def tensorCDGAInclRight (A : CDGAStructure R X) (B : CDGAStructure R Y)
    (u : CDGAUnit A) : CDGAHom B (tensorCDGA A B) where
  toFun n y := tensorSingle (M := X) (N := Y)
    (⟨(0, n), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (u.one ⊗ₜ[R] y)
  map_add n y y' := by rw [TensorProduct.tmul_add, tensorSingle_add]
  map_smul n c y := by rw [TensorProduct.tmul_smul, tensorSingle_smul]
  map_mul := by
    intro a b m h y y'
    funext p
    obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
    rw [tensorCDGA_mul]
    by_cases hcase : p₁ = 0
    · subst hcase
      obtain rfl : m = p₂ := by simp only at hp; omega
      rw [tensorAlgMul_tensorSingle A B h _ _ _ _ ⟨(0, m), hp⟩ rfl h,
        tensorPairₗ_tmul, Nat.mul_zero, pow_zero, one_smul,
        show A.mul (show (0 : ℕ) + 0 = 0 by omega) u.one u.one = u.one from u.one_mul 0 u.one,
        tensorSingleLeft_apply m u.one (B.mul h y y') hp]
    · rw [tensorAlgMul_tensorSingle_ne A B h _ _ _ _ ⟨(p₁, p₂), hp⟩ (by
        rintro ⟨h1, -⟩
        exact hcase h1.symm),
        tensorSingleLeft_apply_ne m u.one (B.mul h y y') (by omega) hp hcase]
  map_d n y := (extTensorD_tensorSingleLeft A B u n y (by omega) (by omega)).symm

end Inclusions

end GaloisForLFunctions.HTGeometry
