import GaloisForLFunctions.HTGeometry.CDGATensor

/-!
# Elements of a tensor product concentrated in one bidegree

The carrier of a graded tensor product is a product over the finitely many decompositions of the
total degree, so it has a distinguished element for each bidegree: the one supported there.  The
three structure maps move such an element to a single other bidegree, which makes them the right
generators for describing subobjects of a tensor product.

* `HTGeometry.tensorSingle` : the element supported at one bidegree.
* `HTGeometry.tensorDL_tensorSingle`, `tensorDR_tensorSingle`, `tensorAct_tensorSingle` : each
  structure map sends it to another such element.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

open scoped Classical in
/-- The element of a graded tensor product supported at a single bidegree. -/
noncomputable def tensorSingle {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (M p.1.1) (N p.1.2)) : TensorCarrier (R := R) M N n :=
  Pi.single p z

open scoped Classical in
@[simp] theorem tensorSingle_same {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (M p.1.1) (N p.1.2)) : tensorSingle (N := N) p z p = z :=
  Pi.single_eq_same _ _

open scoped Classical in
theorem tensorSingle_ne {n : ℕ} {p q : {ab : ℕ × ℕ // ab.1 + ab.2 = n}}
    (z : TensorProduct R (M p.1.1) (N p.1.2)) (h : q ≠ p) : tensorSingle (N := N) p z q = 0 :=
  Pi.single_eq_of_ne h _

theorem tensorSingle_add {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z z' : TensorProduct R (M p.1.1) (N p.1.2)) :
    tensorSingle (N := N) p (z + z') = tensorSingle (N := N) p z + tensorSingle (N := N) p z' := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [tensorSingle_same, tensorCarrier_add_apply, tensorSingle_same, tensorSingle_same]
  · rw [tensorSingle_ne _ hq, tensorCarrier_add_apply, tensorSingle_ne _ hq,
      tensorSingle_ne _ hq, add_zero]

theorem tensorSingle_smul {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (r : R)
    (z : TensorProduct R (M p.1.1) (N p.1.2)) :
    tensorSingle (N := N) p (r • z) = r • tensorSingle (N := N) p z := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [tensorSingle_same, tensorCarrier_smul_apply, tensorSingle_same]
  · rw [tensorSingle_ne _ hq, tensorCarrier_smul_apply, tensorSingle_ne _ hq, smul_zero]

theorem tensorSingle_zero {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    tensorSingle (N := N) p (0 : TensorProduct R (M p.1.1) (N p.1.2)) = 0 := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [tensorSingle_same]
    rfl
  · rw [tensorSingle_ne _ hq]
    rfl

/-- Two indices of a graded tensor product agree exactly when their components do. -/
theorem tensorIndex_eq_iff {n : ℕ} {a b a' b' : ℕ} (h : (a, b).1 + (a, b).2 = n)
    (h' : (a', b').1 + (a', b').2 = n) :
    (⟨(a, b), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) = ⟨(a', b'), h'⟩ ↔ a = a' ∧ b = b' := by
  constructor
  · intro hEq
    have := congrArg Subtype.val hEq
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The decompositions of a total degree are finite**: they are indexed by the first component,
which ranges over `0, …, n`. -/
def tensorIndexEquiv (n : ℕ) : {ab : ℕ × ℕ // ab.1 + ab.2 = n} ≃ Fin (n + 1) where
  toFun p := ⟨p.1.1, by
    have h : p.1.1 + p.1.2 = n := p.2
    omega⟩
  invFun k := ⟨(k.1, n - k.1), by
    have h : k.1 < n + 1 := k.2
    show k.1 + (n - k.1) = n
    omega⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, h⟩ := p
    have h' : a + b = n := h
    refine Subtype.ext (Prod.ext rfl ?_)
    show n - a = b
    omega
  right_inv k := Fin.ext rfl

instance tensorIndexFintype (n : ℕ) : Fintype {ab : ℕ × ℕ // ab.1 + ab.2 = n} :=
  Fintype.ofEquiv _ (tensorIndexEquiv n).symm

/-- A finite sum of elements of a graded tensor product is computed bidegree by bidegree. -/
theorem tensorCarrier_sum_apply {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → TensorCarrier (R := R) M N n) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (∑ i ∈ s, g i) p = ∑ i ∈ s, g i p := by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, tensorCarrier_add_apply, ih]

/-- Every element of a graded tensor product is the sum of its bidegree components. -/
theorem tensorCarrier_eq_sum_single {n : ℕ} (f : TensorCarrier (R := R) M N n) :
    f = ∑ p, tensorSingle (N := N) p (f p) := by
  funext q
  rw [tensorCarrier_sum_apply]
  rw [Finset.sum_eq_single q (fun p _ hne => tensorSingle_ne _ (Ne.symm hne))
    (fun h => absurd (Finset.mem_univ q) h)]
  exact (tensorSingle_same q (f q)).symm

section Structure

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- The left half-differential of a single-bidegree element is a single-bidegree element. -/
theorem tensorDL_tensorSingle {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n)
    (z : TensorProduct R (M a) (N b)) :
    tensorDL P Q n (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) (⟨(a + 1, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
        (TensorProduct.map (P.dₗ a) LinearMap.id z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  cases a' with
  | zero =>
      rw [tensorDL_zero, tensorSingle_ne _ (by
        rw [Ne, tensorIndex_eq_iff]
        omega)]
  | succ a'' =>
      rw [tensorDL_succ]
      by_cases hab : a'' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [tensorSingle_same, tensorSingle_same]
      · rw [tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega), map_zero, tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega)]

/-- The right half-differential of a single-bidegree element is a single-bidegree element. -/
theorem tensorDR_tensorSingle {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n)
    (z : TensorProduct R (M a) (N b)) :
    tensorDR P Q n (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) (⟨(a, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
        (((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b) z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  cases b' with
  | zero =>
      rw [tensorDR_zero, tensorSingle_ne _ (by
        rw [Ne, tensorIndex_eq_iff]
        omega)]
  | succ b'' =>
      rw [tensorDR_succ]
      by_cases hab : a' = a ∧ b'' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [tensorSingle_same, tensorSingle_same]
      · rw [tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega), map_zero, smul_zero, tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega)]

/-- The action on a single-bidegree element is a single-bidegree element. -/
theorem tensorAct_tensorSingle {c n a b m : ℕ} (hcn : c + n = m) (x : X c)
    (h : (a, b).1 + (a, b).2 = n) (z : TensorProduct R (M a) (N b)) :
    tensorAct P Q hcn x (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) (⟨(c + a, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m})
        (TensorProduct.map (P.actₗ (rfl : c + a = c + a) x) LinearMap.id z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  by_cases hc : c ≤ a'
  · obtain ⟨i, hi⟩ : ∃ i, c + i = a' := Nat.le.dest hc
    rw [tensorAct_apply_eq P Q hcn x _ hi (show (i, b').1 + (i, b').2 = n by omega) h']
    by_cases hab : i = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := hab
      rw [tensorSingle_same]
      subst hi
      rw [tensorSingle_same]
    · rw [tensorSingle_ne _ (by
        rw [Ne, tensorIndex_eq_iff]
        omega), map_zero, tensorSingle_ne _ (by
        rw [Ne, tensorIndex_eq_iff]
        omega)]
  · rw [tensorAct_of_lt P Q hcn x _ h' hc, tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega)]

/-- The total differential of a single-bidegree element. -/
theorem tensorD_tensorSingle {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n)
    (z : TensorProduct R (M a) (N b)) :
    tensorD P Q n (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) (⟨(a + 1, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (TensorProduct.map (P.dₗ a) LinearMap.id z)
        + tensorSingle (N := N) (⟨(a, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b) z) := by
  show tensorDL P Q n _ + tensorDR P Q n _ = _
  rw [tensorDL_tensorSingle, tensorDR_tensorSingle]

end Structure

end GaloisForLFunctions.HTGeometry
