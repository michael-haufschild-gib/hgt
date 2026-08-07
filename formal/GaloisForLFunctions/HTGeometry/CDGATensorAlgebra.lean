import GaloisForLFunctions.HTGeometry.CDGATensorSingle
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Data.Fintype.Prod

/-!
# The Koszul product on a bidegree of a tensor product of algebras

The tensor product of two commutative differential graded algebras is graded by the total degree,
and its product pairs a bidegree with a bidegree.  On pure tensors it is
`(x₁ ⊗ y₁)(x₂ ⊗ y₂) = (−1)^{|y₁||x₂|}(x₁x₂) ⊗ (y₁y₂)`, and the whole of the sign bookkeeping of the
tensor product of algebras happens here, one bidegree at a time.

* `HTGeometry.tensorPairₗ` : the product of two bidegrees.
* `HTGeometry.tensorPair_comm` : graded commutativity.
* `HTGeometry.tensorPair_assoc` : associativity.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]

/-- Two powers of `−1` agree when their exponents differ by an even number. -/
theorem neg_one_pow_eq_of_even_add (m k : ℕ) (t : ℕ) (h : m + k = 2 * t) :
    ((-1 : R)) ^ m = ((-1 : R)) ^ k := by
  have h1 : ((-1 : R)) ^ m * ((-1 : R)) ^ k = 1 := by
    rw [← pow_add, h, pow_mul]
    norm_num
  have h2 : ((-1 : R)) ^ k * ((-1 : R)) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ((-1 : R)) ^ m = ((-1 : R)) ^ m * (((-1 : R)) ^ k * ((-1 : R)) ^ k) := by rw [h2, mul_one]
    _ = (((-1 : R)) ^ m * ((-1 : R)) ^ k) * ((-1 : R)) ^ k := by ring
    _ = ((-1 : R)) ^ k := by rw [h1, one_mul]

section Pair

variable (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- The Koszul product of two bidegrees, as a map out of the tensor product of the two bidegrees. -/
noncomputable def tensorPairMap {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂) :
    TensorProduct R (TensorProduct R (X a₁) (Y a₂)) (TensorProduct R (X b₁) (Y b₂)) →ₗ[R]
      TensorProduct R (X n₁) (Y n₂) :=
  ((-1 : R)) ^ (a₂ * b₁) •
    (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁)) (TensorProduct.lift (B.mulₗ h₂))).comp
      (TensorProduct.tensorTensorTensorComm R (X a₁) (Y a₂) (X b₁) (Y b₂)).toLinearMap

/-- The Koszul product of two bidegrees. -/
noncomputable def tensorPairₗ {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂) :
    TensorProduct R (X a₁) (Y a₂) →ₗ[R] TensorProduct R (X b₁) (Y b₂) →ₗ[R]
      TensorProduct R (X n₁) (Y n₂) :=
  TensorProduct.curry (tensorPairMap A B h₁ h₂)

@[simp] theorem tensorPairₗ_tmul {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (x₁ : X a₁) (y₁ : Y a₂) (x₂ : X b₁) (y₂ : Y b₂) :
    tensorPairₗ A B h₁ h₂ (x₁ ⊗ₜ[R] y₁) (x₂ ⊗ₜ[R] y₂)
      = ((-1 : R)) ^ (a₂ * b₁) • (A.mul h₁ x₁ x₂ ⊗ₜ[R] B.mul h₂ y₁ y₂) := by
  show (((-1 : R)) ^ (a₂ * b₁) •
    (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁)) (TensorProduct.lift (B.mulₗ h₂))).comp
      (TensorProduct.tensorTensorTensorComm R (X a₁) (Y a₂) (X b₁) (Y b₂)).toLinearMap)
        ((x₁ ⊗ₜ[R] y₁) ⊗ₜ[R] (x₂ ⊗ₜ[R] y₂)) = _
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  show ((-1 : R)) ^ (a₂ * b₁) • (TensorProduct.map (TensorProduct.lift (A.mulₗ h₁))
    (TensorProduct.lift (B.mulₗ h₂))) (TensorProduct.tensorTensorTensorComm R _ _ _ _
      ((x₁ ⊗ₜ[R] y₁) ⊗ₜ[R] (x₂ ⊗ₜ[R] y₂))) = _
  rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  rfl

/-- **Graded commutativity of the Koszul product**, bidegree by bidegree: the sign of the product
in the two algebras and the Koszul sign of the shuffle combine into the sign of the total degrees.
-/
theorem tensorPair_comm {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (h₁' : b₁ + a₁ = n₁) (h₂' : b₂ + a₂ = n₂)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂)) :
    tensorPairₗ A B h₁ h₂ z w
      = ((-1 : R)) ^ ((a₁ + a₂) * (b₁ + b₂)) • tensorPairₗ A B h₁' h₂' w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          rw [tensorPairₗ_tmul, tensorPairₗ_tmul, A.mul_comm h₁' h₁ x₂ x₁,
            B.mul_comm h₂' h₂ y₂ y₁]
          simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, ← pow_add]
          refine congrArg (fun r : R => r • (A.mul h₁ x₁ x₂ ⊗ₜ[R] B.mul h₂ y₁ y₂)) ?_
          refine neg_one_pow_eq_of_even_add _ _ (a₁ * b₁ + a₂ * b₂ + a₁ * b₂ + a₂ * b₁) ?_
          ring
      | add w w' hw hw' =>
          rw [map_add, map_add, LinearMap.add_apply, hw, hw', smul_add]
  | add z z' hz hz' =>
      rw [map_add, LinearMap.add_apply, hz, hz', map_add, smul_add]

/-- **Associativity of the Koszul product**, bidegree by bidegree.  The three Koszul signs on each
side are the same three products of degrees. -/
theorem tensorPair_assoc {a₁ a₂ b₁ b₂ c₁ c₂ m₁ m₂ n₁ n₂ p₁ p₂ : ℕ}
    (h₁ : a₁ + b₁ = m₁) (h₂ : a₂ + b₂ = m₂) (k₁ : m₁ + c₁ = n₁) (k₂ : m₂ + c₂ = n₂)
    (l₁ : b₁ + c₁ = p₁) (l₂ : b₂ + c₂ = p₂) (e₁ : a₁ + p₁ = n₁) (e₂ : a₂ + p₂ = n₂)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂))
    (v : TensorProduct R (X c₁) (Y c₂)) :
    tensorPairₗ A B k₁ k₂ (tensorPairₗ A B h₁ h₂ z w) v
      = tensorPairₗ A B e₁ e₂ z (tensorPairₗ A B l₁ l₂ w v) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          induction v using TensorProduct.induction_on with
          | zero => simp
          | tmul x₃ y₃ =>
              simp only [tensorPairₗ_tmul, map_smul, LinearMap.smul_apply, smul_smul, ← pow_add]
              rw [A.mul_assoc h₁ k₁ l₁ e₁ x₁ x₂ x₃, B.mul_assoc h₂ k₂ l₂ e₂ y₁ y₂ y₃]
              refine congrArg (fun r : R =>
                r • (A.mul e₁ x₁ (A.mul l₁ x₂ x₃) ⊗ₜ[R] B.mul e₂ y₁ (B.mul l₂ y₂ y₃))) ?_
              refine congrArg (fun t : ℕ => ((-1 : R)) ^ t) ?_
              subst h₁
              subst h₂
              subst l₁
              subst l₂
              ring
          | add v v' hv hv' =>
              simp only [map_add, hv, hv']
      | add w w' hw hw' =>
          simp only [map_add, LinearMap.add_apply, hw, hw']
  | add z z' hz hz' =>
      simp only [map_add, LinearMap.add_apply, hz, hz']

/-- **The Leibniz rule for the first differential**, bidegree by bidegree. -/
theorem tensorPair_dL {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (hl : a₁ + 1 + b₁ = n₁ + 1) (hr : a₁ + (b₁ + 1) = n₁ + 1)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂)) :
    TensorProduct.map (A.dₗ n₁) LinearMap.id (tensorPairₗ A B h₁ h₂ z w)
      = tensorPairₗ A B hl h₂ (TensorProduct.map (A.dₗ a₁) LinearMap.id z) w
        + ((-1 : R)) ^ (a₁ + a₂) •
          tensorPairₗ A B hr h₂ z (TensorProduct.map (A.dₗ b₁) LinearMap.id w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          simp only [tensorPairₗ_tmul, TensorProduct.map_tmul, map_smul, smul_smul, ← pow_add]
          show ((-1 : R)) ^ (a₂ * b₁) • (A.d n₁ (A.mul h₁ x₁ x₂) ⊗ₜ[R]
              (LinearMap.id (B.mul h₂ y₁ y₂) : Y n₂)) = _
          rw [A.d_mul h₁ x₁ x₂, TensorProduct.add_tmul, smul_add]
          refine congrArg₂ (· + ·) ?_ ?_
          · rfl
          · rw [TensorProduct.smul_tmul', smul_smul, ← pow_add]
            refine congrArg (fun r : R =>
              r • (A.mul (show a₁ + (b₁ + 1) = n₁ + 1 by omega) x₁ (A.d b₁ x₂) ⊗ₜ[R]
                B.mul h₂ y₁ y₂)) ?_
            refine neg_one_pow_eq_of_even_add _ _ (a₂ * b₁ + a₁ + a₂) ?_
            ring
      | add w w' hw hw' => simp only [map_add, hw, hw', smul_add]; abel
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]; abel

/-- **The Leibniz rule for the second differential**, bidegree by bidegree. -/
theorem tensorPair_dR {a₁ a₂ b₁ b₂ n₁ n₂ : ℕ} (h₁ : a₁ + b₁ = n₁) (h₂ : a₂ + b₂ = n₂)
    (hl : a₂ + 1 + b₂ = n₂ + 1) (hr : a₂ + (b₂ + 1) = n₂ + 1)
    (z : TensorProduct R (X a₁) (Y a₂)) (w : TensorProduct R (X b₁) (Y b₂)) :
    TensorProduct.map LinearMap.id (B.dₗ n₂) (tensorPairₗ A B h₁ h₂ z w)
      = ((-1 : R)) ^ b₁ •
          tensorPairₗ A B h₁ hl (TensorProduct.map LinearMap.id (B.dₗ a₂) z) w
        + ((-1 : R)) ^ a₂ •
          tensorPairₗ A B h₁ hr z (TensorProduct.map LinearMap.id (B.dₗ b₂) w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ y₁ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x₂ y₂ =>
          simp only [tensorPairₗ_tmul, TensorProduct.map_tmul, map_smul, smul_smul, ← pow_add]
          show ((-1 : R)) ^ (a₂ * b₁) • ((LinearMap.id (A.mul h₁ x₁ x₂) : X n₁) ⊗ₜ[R]
              B.d n₂ (B.mul h₂ y₁ y₂)) = _
          rw [B.d_mul h₂ y₁ y₂, TensorProduct.tmul_add, smul_add]
          refine congrArg₂ (· + ·) ?_ ?_
          · refine congrArg (fun r : R =>
              r • (A.mul h₁ x₁ x₂ ⊗ₜ[R]
                B.mul (show a₂ + 1 + b₂ = n₂ + 1 by omega) (B.d a₂ y₁) y₂)) ?_
            refine neg_one_pow_eq_of_even_add _ _ (a₂ * b₁ + b₁) ?_
            ring
          · rw [TensorProduct.tmul_smul, smul_smul, ← pow_add]
            refine congrArg (fun r : R =>
              r • (A.mul h₁ x₁ x₂ ⊗ₜ[R]
                B.mul (show a₂ + (b₂ + 1) = n₂ + 1 by omega) y₁ (B.d b₂ y₂))) ?_
            refine neg_one_pow_eq_of_even_add _ _ (a₂ * b₁ + a₂) ?_
            ring
      | add w w' hw hw' => simp only [map_add, hw, hw', smul_add]; abel
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', smul_add]; abel

end Pair

section Convolution

variable (A : CDGAStructure R X) (B : CDGAStructure R Y)

/-- **A splitting of an output bidegree**: a bidegree of each factor whose two coordinates add up
to the two coordinates of the output.  Indexing the product by splittings rather than by a bidegree
of one factor keeps truncated subtraction out of every dependent position, which is what makes the
three laws reindexing arguments rather than transport arguments. -/
abbrev Splitting (a b : ℕ) {n : ℕ} (p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) : Type :=
  {rs : {ab : ℕ × ℕ // ab.1 + ab.2 = a} × {ab : ℕ × ℕ // ab.1 + ab.2 = b} //
    rs.1.1.1 + rs.2.1.1 = p.1.1 ∧ rs.1.1.2 + rs.2.1.2 = p.1.2}

instance splittingDecidableEq (a b : ℕ) {n : ℕ} (p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    DecidableEq (Splitting a b p) :=
  inferInstanceAs (DecidableEq {_rs : _ × _ // _})

instance splittingFintype (a b : ℕ) {n : ℕ}
    (p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) : Fintype (Splitting a b p) :=
  Subtype.fintype _

/-- One summand of the product: the Koszul product of the two components a splitting names. -/
noncomputable def splittingTerm {a b n : ℕ} {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b)
    (rs : Splitting a b p) : TensorProduct R (X p.1.1) (Y p.1.2) :=
  tensorPairₗ A B rs.2.1 rs.2.2 (f rs.1.1) (g rs.1.2)

/-- **The product of two elements of a tensor product of algebras**: the sum over the splittings of
each output bidegree. -/
noncomputable def tensorAlgMul {a b n : ℕ} (_h : a + b = n)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    TensorCarrier (R := R) X Y n :=
  fun p => ∑ rs : Splitting a b p, splittingTerm A B f g rs

theorem tensorAlgMul_add_left {a b n : ℕ} (h : a + b = n)
    (f f' : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h (f + f') g = tensorAlgMul A B h f g + tensorAlgMul A B h f' g := by
  funext p
  show (∑ rs : Splitting a b p, splittingTerm A B (f + f') g rs) = _
  rw [tensorCarrier_add_apply]
  show (∑ rs : Splitting a b p, splittingTerm A B (f + f') g rs)
    = (∑ rs : Splitting a b p, splittingTerm A B f g rs)
      + ∑ rs : Splitting a b p, splittingTerm A B f' g rs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun rs _ => ?_
  show tensorPairₗ A B rs.2.1 rs.2.2 ((f + f') rs.1.1) (g rs.1.2) = _
  rw [tensorCarrier_add_apply, map_add, LinearMap.add_apply]
  rfl

theorem tensorAlgMul_add_right {a b n : ℕ} (h : a + b = n)
    (f : TensorCarrier (R := R) X Y a) (g g' : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h f (g + g') = tensorAlgMul A B h f g + tensorAlgMul A B h f g' := by
  funext p
  show (∑ rs : Splitting a b p, splittingTerm A B f (g + g') rs) = _
  rw [tensorCarrier_add_apply]
  show (∑ rs : Splitting a b p, splittingTerm A B f (g + g') rs)
    = (∑ rs : Splitting a b p, splittingTerm A B f g rs)
      + ∑ rs : Splitting a b p, splittingTerm A B f g' rs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun rs _ => ?_
  show tensorPairₗ A B rs.2.1 rs.2.2 (f rs.1.1) ((g + g') rs.1.2) = _
  rw [tensorCarrier_add_apply, map_add]
  rfl

theorem tensorAlgMul_smul_left {a b n : ℕ} (h : a + b = n) (c : R)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h (c • f) g = c • tensorAlgMul A B h f g := by
  funext p
  show (∑ rs : Splitting a b p, splittingTerm A B (c • f) g rs) = _
  rw [tensorCarrier_smul_apply]
  show (∑ rs : Splitting a b p, splittingTerm A B (c • f) g rs)
    = c • ∑ rs : Splitting a b p, splittingTerm A B f g rs
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun rs _ => ?_
  show tensorPairₗ A B rs.2.1 rs.2.2 ((c • f) rs.1.1) (g rs.1.2) = _
  rw [tensorCarrier_smul_apply, map_smul, LinearMap.smul_apply]
  rfl

theorem tensorAlgMul_smul_right {a b n : ℕ} (h : a + b = n) (c : R)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h f (c • g) = c • tensorAlgMul A B h f g := by
  funext p
  show (∑ rs : Splitting a b p, splittingTerm A B f (c • g) rs) = _
  rw [tensorCarrier_smul_apply]
  show (∑ rs : Splitting a b p, splittingTerm A B f (c • g) rs)
    = c • ∑ rs : Splitting a b p, splittingTerm A B f g rs
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun rs _ => ?_
  show tensorPairₗ A B rs.2.1 rs.2.2 (f rs.1.1) ((c • g) rs.1.2) = _
  rw [tensorCarrier_smul_apply, map_smul]
  rfl

/-- **The swap of a splitting**, an involution between the splittings for the two orders of the
factors. -/
def splittingSwap {a b n : ℕ} {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}} (rs : Splitting a b p) :
    Splitting b a p :=
  ⟨(rs.1.2, rs.1.1), by
    refine ⟨?_, ?_⟩
    · have h := rs.2.1
      show rs.1.2.1.1 + rs.1.1.1.1 = p.1.1
      omega
    · have h := rs.2.2
      show rs.1.2.1.2 + rs.1.1.1.2 = p.1.2
      omega⟩

theorem splittingSwap_swap {a b n : ℕ} {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (rs : Splitting a b p) : splittingSwap (splittingSwap rs) = rs := rfl

/-- **Graded commutativity of the product**: the swap of splittings matches the summands, and each
matching pair differs by the sign of the two total degrees. -/
theorem tensorAlgMul_comm {a b n : ℕ} (h : a + b = n) (h' : b + a = n)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h f g = ((-1 : R)) ^ (a * b) • tensorAlgMul A B h' g f := by
  funext p
  show (∑ rs : Splitting a b p, splittingTerm A B f g rs)
    = ((-1 : R)) ^ (a * b) • ∑ sr : Splitting b a p, splittingTerm A B g f sr
  rw [Finset.smul_sum]
  refine Finset.sum_nbij' (fun rs => splittingSwap rs) (fun sr => splittingSwap sr)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => splittingSwap_swap _) (fun _ _ => splittingSwap_swap _) ?_
  intro rs _
  show tensorPairₗ A B rs.2.1 rs.2.2 (f rs.1.1) (g rs.1.2)
    = ((-1 : R)) ^ (a * b) • tensorPairₗ A B (splittingSwap rs).2.1 (splittingSwap rs).2.2
      (g rs.1.2) (f rs.1.1)
  have hr : rs.1.1.1.1 + rs.1.1.1.2 = a := rs.1.1.2
  have hs : rs.1.2.1.1 + rs.1.2.1.2 = b := rs.1.2.2
  rw [tensorPair_comm A B rs.2.1 rs.2.2 (splittingSwap rs).2.1 (splittingSwap rs).2.2
    (f rs.1.1) (g rs.1.2), hr, hs]
  rfl

/-- **Reassociating a splitting of a splitting.**  Both sides of associativity are sums over triples
of bidegrees adding up to the output; this is the reassociation of such a triple. -/
def splitReassoc {a b c m q n : ℕ} (h₁ : a + b = m) (h₃ : b + c = q)
    {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (x : (ts : Splitting m c p) × Splitting a b ts.1.1) :
    (us : Splitting a q p) × Splitting b c us.1.2 :=
  ⟨⟨(x.2.1.1, ⟨(x.2.1.2.1.1 + x.1.1.2.1.1, x.2.1.2.1.2 + x.1.1.2.1.2), by
        have h4 := x.2.1.2.2
        have h5 := x.1.1.2.2
        simp only at h4 h5 ⊢
        omega⟩), by
      have h4 := x.2.2.1
      have h5 := x.2.2.2
      have h6 := x.1.2.1
      have h7 := x.1.2.2
      simp only at h4 h5 h6 h7 ⊢
      omega⟩,
    ⟨(x.2.1.2, x.1.1.2), ⟨rfl, rfl⟩⟩⟩

/-- The inverse reassociation. -/
def splitReassocInv {a b c m q n : ℕ} (h₁ : a + b = m) (h₃ : b + c = q)
    {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (y : (us : Splitting a q p) × Splitting b c us.1.2) :
    (ts : Splitting m c p) × Splitting a b ts.1.1 :=
  ⟨⟨(⟨(y.1.1.1.1.1 + y.2.1.1.1.1, y.1.1.1.1.2 + y.2.1.1.1.2), by
        have h4 := y.1.1.1.2
        have h5 := y.2.1.1.2
        simp only at h4 h5 ⊢
        omega⟩, y.2.1.2), by
      have h4 := y.1.2.1
      have h5 := y.1.2.2
      have h6 := y.2.2.1
      have h7 := y.2.2.2
      simp only at h4 h5 h6 h7 ⊢
      omega⟩,
    ⟨(y.1.1.1, y.2.1.1), ⟨rfl, rfl⟩⟩⟩

theorem splitReassoc_inv {a b c m q n : ℕ} (h₁ : a + b = m) (h₃ : b + c = q)
    {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (x : (ts : Splitting m c p) × Splitting a b ts.1.1) :
    splitReassocInv h₁ h₃ (splitReassoc h₁ h₃ x) = x := by
  obtain ⟨⟨⟨u, t⟩, hu1, hu2⟩, ⟨⟨r, s⟩, hr1, hr2⟩⟩ := x
  have hm : (r.1.1 + s.1.1) + (r.1.2 + s.1.2) = m := by
    clear hu1 hu2 hr1 hr2
    have hr : r.1.1 + r.1.2 = a := r.2
    have hs : s.1.1 + s.1.2 = b := s.2
    omega
  have hu : u = ⟨(r.1.1 + s.1.1, r.1.2 + s.1.2), hm⟩ := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> simp only at hr1 hr2 ⊢ <;> omega
  subst hu
  rfl

theorem splitReassocInv_inv {a b c m q n : ℕ} (h₁ : a + b = m) (h₃ : b + c = q)
    {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (y : (us : Splitting a q p) × Splitting b c us.1.2) :
    splitReassoc h₁ h₃ (splitReassocInv h₁ h₃ y) = y := by
  obtain ⟨⟨⟨r, v⟩, hu1, hu2⟩, ⟨⟨s, t⟩, hs1, hs2⟩⟩ := y
  have hq : (s.1.1 + t.1.1) + (s.1.2 + t.1.2) = q := by
    clear hu1 hu2 hs1 hs2
    have hs : s.1.1 + s.1.2 = b := s.2
    have ht : t.1.1 + t.1.2 = c := t.2
    omega
  have hv : v = ⟨(s.1.1 + t.1.1, s.1.2 + t.1.2), hq⟩ := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;> simp only at hs1 hs2 ⊢ <;> omega
  subst hv
  rfl

/-- **Associativity of the product**: both sides are sums over triples of bidegrees adding up to the
output, and reassociating a triple matches the summands. -/
theorem tensorAlgMul_assoc {a b c m q n : ℕ} (h₁ : a + b = m) (h₂ : m + c = n)
    (h₃ : b + c = q) (h₄ : a + q = n)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b)
    (k : TensorCarrier (R := R) X Y c) :
    tensorAlgMul A B h₂ (tensorAlgMul A B h₁ f g) k
      = tensorAlgMul A B h₄ f (tensorAlgMul A B h₃ g k) := by
  funext p
  have hL : (∑ ts : Splitting m c p, splittingTerm A B (tensorAlgMul A B h₁ f g) k ts)
      = ∑ ts : Splitting m c p, ∑ rs : Splitting a b ts.1.1,
          tensorPairₗ A B ts.2.1 ts.2.2 (splittingTerm A B f g rs) (k ts.1.2) := by
    refine Finset.sum_congr rfl fun ts _ => ?_
    show tensorPairₗ A B ts.2.1 ts.2.2
      (∑ rs : Splitting a b ts.1.1, splittingTerm A B f g rs) (k ts.1.2) = _
    rw [map_sum, LinearMap.sum_apply]
  have hR : (∑ us : Splitting a q p, splittingTerm A B f (tensorAlgMul A B h₃ g k) us)
      = ∑ us : Splitting a q p, ∑ vw : Splitting b c us.1.2,
          tensorPairₗ A B us.2.1 us.2.2 (f us.1.1) (splittingTerm A B g k vw) := by
    refine Finset.sum_congr rfl fun us _ => ?_
    show tensorPairₗ A B us.2.1 us.2.2 (f us.1.1)
      (∑ vw : Splitting b c us.1.2, splittingTerm A B g k vw) = _
    rw [map_sum]
  show (∑ ts : Splitting m c p, splittingTerm A B (tensorAlgMul A B h₁ f g) k ts)
    = ∑ us : Splitting a q p, splittingTerm A B f (tensorAlgMul A B h₃ g k) us
  rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => splitReassoc h₁ h₃ x) (fun y => splitReassocInv h₁ h₃ y)
    (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => splitReassoc_inv h₁ h₃ x) (fun y _ => splitReassocInv_inv h₁ h₃ y) ?_
  · exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · exact Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · intro x _
    exact tensorPair_assoc A B x.2.2.1 x.2.2.2 x.1.2.1 x.1.2.2
      (splitReassoc h₁ h₃ x).2.2.1 (splitReassoc h₁ h₃ x).2.2.2
      (splitReassoc h₁ h₃ x).1.2.1 (splitReassoc h₁ h₃ x).1.2.2
      (f x.2.1.1) (g x.2.1.2) (k x.1.1.2)

end Convolution

section External

variable {A : CDGAStructure R X}

/-- **A differential graded algebra as a module with zero action.**  Every axiom of a module is an
identity between zeros except the two for the differential, which are the algebra's own.  This is
what lets the external differential of a tensor product of algebras reuse the module-level
half-differentials: they refer to the two differentials only, but their signatures ask for two
modules over one algebra. -/
def zeroActModule (B : CDGAStructure R Y) : CDGAModuleStructure A Y where
  act _ _ _ := 0
  d := B.d
  act_add_left _ _ _ _ := (add_zero (0 : Y _)).symm
  act_add_right _ _ _ _ := (add_zero (0 : Y _)).symm
  act_smul_left _ _ _ _ := (smul_zero _).symm
  act_smul_right _ _ _ _ := (smul_zero _).symm
  act_assoc _ _ _ _ _ _ _ := rfl
  d_add := B.d_add
  d_smul := B.d_smul
  d_d := B.d_d
  d_act _ _ _ := by
    show B.d _ 0 = 0 + ((-1 : R)) ^ _ • 0
    rw [show B.d _ (0 : Y _) = 0 from (B.dₗ _).map_zero, smul_zero, add_zero]

@[simp] theorem zeroActModule_d (B : CDGAStructure R Y) (n : ℕ) (y : Y n) :
    (zeroActModule (A := A) B).d n y = B.d n y := rfl

/-- **The external differential of a tensor product of algebras.** -/
noncomputable def extTensorD (A : CDGAStructure R X) (B : CDGAStructure R Y) (n : ℕ)
    (f : TensorCarrier (R := R) X Y n) : TensorCarrier (R := R) X Y (n + 1) :=
  tensorD (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n f

theorem extTensorD_d (A : CDGAStructure R X) (B : CDGAStructure R Y) (n : ℕ)
    (f : TensorCarrier (R := R) X Y n) : extTensorD A B (n + 1) (extTensorD A B n f) = 0 :=
  (tensorModule (CDGAStructure.selfModule A) (zeroActModule (A := A) B)).d_d n f

section Shift

variable {a b n : ℕ} {q : {pq : ℕ × ℕ // pq.1 + pq.2 = n}} {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n + 1}}

/-- Raise the first coordinate of the left part of a splitting. -/
def shiftLeftFst (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2) (rs : Splitting a b q) :
    Splitting (a + 1) b p :=
  ⟨(⟨(rs.1.1.1.1 + 1, rs.1.1.1.2), by
      have h := rs.1.1.2
      simp only at h ⊢
      omega⟩, rs.1.2), by
    refine ⟨?_, ?_⟩
    · have h := rs.2.1
      simp only at h ⊢
      omega
    · have h := rs.2.2
      simp only at h ⊢
      omega⟩

/-- Raise the first coordinate of the right part of a splitting. -/
def shiftRightFst (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2) (rs : Splitting a b q) :
    Splitting a (b + 1) p :=
  ⟨(rs.1.1, ⟨(rs.1.2.1.1 + 1, rs.1.2.1.2), by
      have h := rs.1.2.2
      simp only at h ⊢
      omega⟩), by
    refine ⟨?_, ?_⟩
    · have h := rs.2.1
      simp only at h ⊢
      omega
    · have h := rs.2.2
      simp only at h ⊢
      omega⟩

theorem shiftLeftFst_injective (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2)
    (rs rs' : Splitting a b q) (he : shiftLeftFst hp1 hp2 rs = shiftLeftFst hp1 hp2 rs') :
    rs = rs' := by
  have h1 := congrArg (fun z : Splitting (a + 1) b p => z.1.1.1.1) he
  have h2 := congrArg (fun z : Splitting (a + 1) b p => z.1.1.1.2) he
  have h3 := congrArg (fun z : Splitting (a + 1) b p => z.1.2) he
  simp only [shiftLeftFst] at h1 h2 h3
  refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) h3) <;> omega

theorem shiftRightFst_injective (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2)
    (rs rs' : Splitting a b q) (he : shiftRightFst hp1 hp2 rs = shiftRightFst hp1 hp2 rs') :
    rs = rs' := by
  have h1 := congrArg (fun z : Splitting a (b + 1) p => z.1.2.1.1) he
  have h2 := congrArg (fun z : Splitting a (b + 1) p => z.1.2.1.2) he
  have h3 := congrArg (fun z : Splitting a (b + 1) p => z.1.1) he
  simp only [shiftRightFst] at h1 h2 h3
  refine Subtype.ext (Prod.ext h3 (Subtype.ext (Prod.ext ?_ ?_))) <;> omega

theorem shiftLeftFst_surjective (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2)
    (uv : Splitting (a + 1) b p) (hu : uv.1.1.1.1 ≠ 0) :
    ∃ rs : Splitting a b q, shiftLeftFst hp1 hp2 rs = uv := by
  obtain ⟨k, hk⟩ : ∃ k, uv.1.1.1.1 = k + 1 := ⟨uv.1.1.1.1 - 1, by omega⟩
  refine ⟨⟨(⟨(k, uv.1.1.1.2), by
      have h := uv.1.1.2
      simp only at h ⊢
      omega⟩, uv.1.2), ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · have h := uv.2.1
      simp only at h ⊢
      omega
    · have h := uv.2.2
      simp only at h ⊢
      omega
  · refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ rfl)) rfl)
    simp only [shiftLeftFst]
    omega

theorem shiftRightFst_surjective (hp1 : p.1.1 = q.1.1 + 1) (hp2 : p.1.2 = q.1.2)
    (uv : Splitting a (b + 1) p) (hv : uv.1.2.1.1 ≠ 0) :
    ∃ rs : Splitting a b q, shiftRightFst hp1 hp2 rs = uv := by
  obtain ⟨k, hk⟩ : ∃ k, uv.1.2.1.1 = k + 1 := ⟨uv.1.2.1.1 - 1, by omega⟩
  refine ⟨⟨(uv.1.1, ⟨(k, uv.1.2.1.2), by
      have h := uv.1.2.2
      simp only at h ⊢
      omega⟩), ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · have h := uv.2.1
      simp only at h ⊢
      omega
    · have h := uv.2.2
      simp only at h ⊢
      omega
  · refine Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext ?_ rfl)))
    simp only [shiftRightFst]
    omega

theorem sum_shiftLeftFst {M' : Type*} [AddCommGroup M'] (hp1 : p.1.1 = q.1.1 + 1)
    (hp2 : p.1.2 = q.1.2) (F : Splitting a b q → M') (G : Splitting (a + 1) b p → M')
    (hzero : ∀ uv : Splitting (a + 1) b p, uv.1.1.1.1 = 0 → G uv = 0)
    (hFG : ∀ rs : Splitting a b q, F rs = G (shiftLeftFst hp1 hp2 rs)) :
    (∑ rs : Splitting a b q, F rs) = ∑ uv : Splitting (a + 1) b p, G uv := by
  classical
  rw [← Finset.sum_filter_of_ne
    (p := fun uv : Splitting (a + 1) b p => uv.1.1.1.1 ≠ 0)
    (fun uv _ hne h0 => hne (hzero uv h0))]
  refine Finset.sum_bij (fun rs _ => shiftLeftFst hp1 hp2 rs) (fun rs _ => ?_)
    (fun rs _ rs' _ he => shiftLeftFst_injective hp1 hp2 rs rs' he) (fun uv huv => ?_)
    (fun rs _ => hFG rs)
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (shiftLeftFst hp1 hp2 rs).1.1.1.1 ≠ 0
    simp only [shiftLeftFst]
    omega
  · obtain ⟨rs, hrs⟩ := shiftLeftFst_surjective hp1 hp2 uv (Finset.mem_filter.1 huv).2
    exact ⟨rs, Finset.mem_univ _, hrs⟩

theorem sum_shiftRightFst {M' : Type*} [AddCommGroup M'] (hp1 : p.1.1 = q.1.1 + 1)
    (hp2 : p.1.2 = q.1.2) (F : Splitting a b q → M') (G : Splitting a (b + 1) p → M')
    (hzero : ∀ uv : Splitting a (b + 1) p, uv.1.2.1.1 = 0 → G uv = 0)
    (hFG : ∀ rs : Splitting a b q, F rs = G (shiftRightFst hp1 hp2 rs)) :
    (∑ rs : Splitting a b q, F rs) = ∑ uv : Splitting a (b + 1) p, G uv := by
  classical
  rw [← Finset.sum_filter_of_ne
    (p := fun uv : Splitting a (b + 1) p => uv.1.2.1.1 ≠ 0)
    (fun uv _ hne h0 => hne (hzero uv h0))]
  refine Finset.sum_bij (fun rs _ => shiftRightFst hp1 hp2 rs) (fun rs _ => ?_)
    (fun rs _ rs' _ he => shiftRightFst_injective hp1 hp2 rs rs' he) (fun uv huv => ?_)
    (fun rs _ => hFG rs)
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (shiftRightFst hp1 hp2 rs).1.2.1.1 ≠ 0
    simp only [shiftRightFst]
    omega
  · obtain ⟨rs, hrs⟩ := shiftRightFst_surjective hp1 hp2 uv (Finset.mem_filter.1 huv).2
    exact ⟨rs, Finset.mem_univ _, hrs⟩

/-- Raise the second coordinate of the left part of a splitting. -/
def shiftLeftSnd (hp1 : p.1.1 = q.1.1) (hp2 : p.1.2 = q.1.2 + 1) (rs : Splitting a b q) :
    Splitting (a + 1) b p :=
  ⟨(⟨(rs.1.1.1.1, rs.1.1.1.2 + 1), by
      have h := rs.1.1.2
      simp only at h ⊢
      omega⟩, rs.1.2), by
    refine ⟨?_, ?_⟩
    · have h := rs.2.1
      simp only at h ⊢
      omega
    · have h := rs.2.2
      simp only at h ⊢
      omega⟩

/-- Raise the second coordinate of the right part of a splitting. -/
def shiftRightSnd (hp1 : p.1.1 = q.1.1) (hp2 : p.1.2 = q.1.2 + 1) (rs : Splitting a b q) :
    Splitting a (b + 1) p :=
  ⟨(rs.1.1, ⟨(rs.1.2.1.1, rs.1.2.1.2 + 1), by
      have h := rs.1.2.2
      simp only at h ⊢
      omega⟩), by
    refine ⟨?_, ?_⟩
    · have h := rs.2.1
      simp only at h ⊢
      omega
    · have h := rs.2.2
      simp only at h ⊢
      omega⟩

theorem sum_shiftLeftSnd {M' : Type*} [AddCommGroup M'] (hp1 : p.1.1 = q.1.1)
    (hp2 : p.1.2 = q.1.2 + 1) (F : Splitting a b q → M') (G : Splitting (a + 1) b p → M')
    (hzero : ∀ uv : Splitting (a + 1) b p, uv.1.1.1.2 = 0 → G uv = 0)
    (hFG : ∀ rs : Splitting a b q, F rs = G (shiftLeftSnd hp1 hp2 rs)) :
    (∑ rs : Splitting a b q, F rs) = ∑ uv : Splitting (a + 1) b p, G uv := by
  classical
  rw [← Finset.sum_filter_of_ne
    (p := fun uv : Splitting (a + 1) b p => uv.1.1.1.2 ≠ 0)
    (fun uv _ hne h0 => hne (hzero uv h0))]
  refine Finset.sum_bij (fun rs _ => shiftLeftSnd hp1 hp2 rs) (fun rs _ => ?_)
    (fun rs _ rs' _ he => ?_) (fun uv huv => ?_) (fun rs _ => hFG rs)
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (shiftLeftSnd hp1 hp2 rs).1.1.1.2 ≠ 0
    simp only [shiftLeftSnd]
    omega
  · have h1 := congrArg (fun z : Splitting (a + 1) b p => z.1.1.1.1) he
    have h2 := congrArg (fun z : Splitting (a + 1) b p => z.1.1.1.2) he
    have h3 := congrArg (fun z : Splitting (a + 1) b p => z.1.2) he
    simp only [shiftLeftSnd] at h1 h2 h3
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) h3) <;> omega
  · have hu : uv.1.1.1.2 ≠ 0 := (Finset.mem_filter.1 huv).2
    obtain ⟨k, hk⟩ : ∃ k, uv.1.1.1.2 = k + 1 := ⟨uv.1.1.1.2 - 1, by omega⟩
    refine ⟨⟨(⟨(uv.1.1.1.1, k), by
        have h := uv.1.1.2
        simp only at h ⊢
        omega⟩, uv.1.2), ?_⟩, Finset.mem_univ _, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h := uv.2.1
        simp only at h ⊢
        omega
      · have h := uv.2.2
        simp only at h ⊢
        omega
    · refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl ?_)) rfl)
      simp only [shiftLeftSnd]
      omega

theorem sum_shiftRightSnd {M' : Type*} [AddCommGroup M'] (hp1 : p.1.1 = q.1.1)
    (hp2 : p.1.2 = q.1.2 + 1) (F : Splitting a b q → M') (G : Splitting a (b + 1) p → M')
    (hzero : ∀ uv : Splitting a (b + 1) p, uv.1.2.1.2 = 0 → G uv = 0)
    (hFG : ∀ rs : Splitting a b q, F rs = G (shiftRightSnd hp1 hp2 rs)) :
    (∑ rs : Splitting a b q, F rs) = ∑ uv : Splitting a (b + 1) p, G uv := by
  classical
  rw [← Finset.sum_filter_of_ne
    (p := fun uv : Splitting a (b + 1) p => uv.1.2.1.2 ≠ 0)
    (fun uv _ hne h0 => hne (hzero uv h0))]
  refine Finset.sum_bij (fun rs _ => shiftRightSnd hp1 hp2 rs) (fun rs _ => ?_)
    (fun rs _ rs' _ he => ?_) (fun uv huv => ?_) (fun rs _ => hFG rs)
  · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (shiftRightSnd hp1 hp2 rs).1.2.1.2 ≠ 0
    simp only [shiftRightSnd]
    omega
  · have h1 := congrArg (fun z : Splitting a (b + 1) p => z.1.2.1.1) he
    have h2 := congrArg (fun z : Splitting a (b + 1) p => z.1.2.1.2) he
    have h3 := congrArg (fun z : Splitting a (b + 1) p => z.1.1) he
    simp only [shiftRightSnd] at h1 h2 h3
    refine Subtype.ext (Prod.ext h3 (Subtype.ext (Prod.ext ?_ ?_))) <;> omega
  · have hv : uv.1.2.1.2 ≠ 0 := (Finset.mem_filter.1 huv).2
    obtain ⟨k, hk⟩ : ∃ k, uv.1.2.1.2 = k + 1 := ⟨uv.1.2.1.2 - 1, by omega⟩
    refine ⟨⟨(uv.1.1, ⟨(uv.1.2.1.1, k), by
        have h := uv.1.2.2
        simp only at h ⊢
        omega⟩), ?_⟩, Finset.mem_univ _, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h := uv.2.1
        simp only at h ⊢
        omega
      · have h := uv.2.2
        simp only at h ⊢
        omega
    · refine Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext rfl ?_)))
      simp only [shiftRightSnd]
      omega

end Shift

section Leibniz

variable (A : CDGAStructure R X) (B : CDGAStructure R Y)

theorem tensorDL_of_fst_zero {M N : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)] {A' : CDGAStructure R X}
    (P : CDGAModuleStructure A' M) (Q : CDGAModuleStructure A' N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (u : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
    (hu : u.1.1 = 0) : tensorDL P Q n f u = 0 := by
  obtain ⟨⟨u₁, u₂⟩, h2⟩ := u
  simp only at hu
  subst hu
  exact tensorDL_zero _ _ _ _ f h2

/-- **The Leibniz rule for the first half-differential.** -/
theorem tensorAlgMul_tensorDL {a b n : ℕ} (h : a + b = n) (hl : a + 1 + b = n + 1)
    (hr : a + (b + 1) = n + 1)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n (tensorAlgMul A B h f g)
      = tensorAlgMul A B hl
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f) g
        + ((-1 : R)) ^ a • tensorAlgMul A B hr f
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g) := by
  funext p
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
  rw [tensorCarrier_add_apply, tensorCarrier_smul_apply]
  cases p₁ with
  | zero =>
      rw [tensorDL_zero]
      have hL : (∑ uv : Splitting (a + 1) b ⟨(0, p₂), hp⟩,
          splittingTerm A B (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f)
            g uv) = 0 := by
        refine Finset.sum_eq_zero fun uv _ => ?_
        have hu : uv.1.1.1.1 = 0 := by
          have h1 := uv.2.1
          simp only at h1
          omega
        show tensorPairₗ A B uv.2.1 uv.2.2
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f uv.1.1)
          (g uv.1.2) = 0
        rw [tensorDL_of_fst_zero _ _ a f uv.1.1 hu, map_zero, LinearMap.zero_apply]
      have hR : (∑ uv : Splitting a (b + 1) ⟨(0, p₂), hp⟩,
          splittingTerm A B f
            (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g) uv) = 0 := by
        refine Finset.sum_eq_zero fun uv _ => ?_
        have hv : uv.1.2.1.1 = 0 := by
          have h1 := uv.2.1
          simp only at h1
          omega
        show tensorPairₗ A B uv.2.1 uv.2.2 (f uv.1.1)
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g uv.1.2) = 0
        rw [tensorDL_of_fst_zero _ _ b g uv.1.2 hv, map_zero]
      rw [show tensorAlgMul A B hl
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f) g
          ⟨(0, p₂), hp⟩ = 0 from hL,
        show tensorAlgMul A B hr f
          (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g)
          ⟨(0, p₂), hp⟩ = 0 from hR, smul_zero, add_zero]
  | succ α =>
      have hq : (α, p₂).1 + (α, p₂).2 = n := by simp only at hp ⊢; omega
      rw [tensorDL_succ]
      show TensorProduct.map ((CDGAStructure.selfModule A).dₗ α) LinearMap.id
          (∑ rs : Splitting a b ⟨(α, p₂), hq⟩, splittingTerm A B f g rs) = _
      rw [map_sum]
      have hsplit : ∀ rs : Splitting a b ⟨(α, p₂), hq⟩,
          TensorProduct.map ((CDGAStructure.selfModule A).dₗ α) LinearMap.id
            (splittingTerm A B f g rs)
          = tensorPairₗ A B (show rs.1.1.1.1 + 1 + rs.1.2.1.1 = α + 1 by
                have := rs.2.1; simp only at this ⊢; omega) rs.2.2
              (TensorProduct.map (A.dₗ rs.1.1.1.1) LinearMap.id (f rs.1.1)) (g rs.1.2)
            + ((-1 : R)) ^ a • tensorPairₗ A B (show rs.1.1.1.1 + (rs.1.2.1.1 + 1) = α + 1 by
                have := rs.2.1; simp only at this ⊢; omega) rs.2.2
              (f rs.1.1) (TensorProduct.map (A.dₗ rs.1.2.1.1) LinearMap.id (g rs.1.2)) := by
        intro rs
        have hra : rs.1.1.1.1 + rs.1.1.1.2 = a := rs.1.1.2
        rw [show ((-1 : R)) ^ a = ((-1 : R)) ^ (rs.1.1.1.1 + rs.1.1.1.2) by rw [hra]]
        exact tensorPair_dL A B rs.2.1 rs.2.2 _ _ (f rs.1.1) (g rs.1.2)
      rw [Finset.sum_congr rfl fun rs _ => hsplit rs, Finset.sum_add_distrib, ← Finset.smul_sum]
      refine congrArg₂ (· + ·) ?_ (congrArg (fun z => ((-1 : R)) ^ a • z) ?_)
      · refine sum_shiftLeftFst (a := a) (b := b) (q := ⟨(α, p₂), hq⟩) (p := ⟨(α + 1, p₂), hp⟩)
          rfl rfl _ _ (fun uv hu => ?_) (fun rs => ?_)
        · show tensorPairₗ A B uv.2.1 uv.2.2
            (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f uv.1.1)
            (g uv.1.2) = 0
          rw [tensorDL_of_fst_zero _ _ a f uv.1.1 hu, map_zero, LinearMap.zero_apply]
        · show tensorPairₗ A B _ _ (TensorProduct.map (A.dₗ rs.1.1.1.1) LinearMap.id (f rs.1.1))
            (g rs.1.2) = tensorPairₗ A B _ _
            (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f
              (shiftLeftFst rfl rfl rs).1.1) (g (shiftLeftFst rfl rfl rs).1.2)
          rfl
      · refine sum_shiftRightFst (a := a) (b := b) (q := ⟨(α, p₂), hq⟩) (p := ⟨(α + 1, p₂), hp⟩)
          rfl rfl _ _ (fun uv hv => ?_) (fun rs => ?_)
        · show tensorPairₗ A B uv.2.1 uv.2.2 (f uv.1.1)
            (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g uv.1.2) = 0
          rw [tensorDL_of_fst_zero _ _ b g uv.1.2 hv, map_zero]
        · rfl

theorem tensorDR_of_snd_zero {M N : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)] {A' : CDGAStructure R X}
    (P : CDGAModuleStructure A' M) (Q : CDGAModuleStructure A' N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (u : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
    (hu : u.1.2 = 0) : tensorDR P Q n f u = 0 := by
  obtain ⟨⟨u₁, u₂⟩, h2⟩ := u
  simp only at hu
  subst hu
  exact tensorDR_zero _ _ _ _ f h2

/-- **The Leibniz rule for the second half-differential.** -/
theorem tensorAlgMul_tensorDR {a b n : ℕ} (h : a + b = n) (hl : a + 1 + b = n + 1)
    (hr : a + (b + 1) = n + 1)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n (tensorAlgMul A B h f g)
      = tensorAlgMul A B hl
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f) g
        + ((-1 : R)) ^ a • tensorAlgMul A B hr f
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g) := by
  funext p
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
  rw [tensorCarrier_add_apply, tensorCarrier_smul_apply]
  cases p₂ with
  | zero =>
      rw [tensorDR_zero]
      have hL : (∑ uv : Splitting (a + 1) b ⟨(p₁, 0), hp⟩,
          splittingTerm A B (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f)
            g uv) = 0 := by
        refine Finset.sum_eq_zero fun uv _ => ?_
        have hu : uv.1.1.1.2 = 0 := by
          have h1 := uv.2.2
          simp only at h1
          omega
        show tensorPairₗ A B uv.2.1 uv.2.2
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f uv.1.1)
          (g uv.1.2) = 0
        rw [tensorDR_of_snd_zero _ _ a f uv.1.1 hu, map_zero, LinearMap.zero_apply]
      have hR : (∑ uv : Splitting a (b + 1) ⟨(p₁, 0), hp⟩,
          splittingTerm A B f
            (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g) uv) = 0 := by
        refine Finset.sum_eq_zero fun uv _ => ?_
        have hv : uv.1.2.1.2 = 0 := by
          have h1 := uv.2.2
          simp only at h1
          omega
        show tensorPairₗ A B uv.2.1 uv.2.2 (f uv.1.1)
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g uv.1.2) = 0
        rw [tensorDR_of_snd_zero _ _ b g uv.1.2 hv, map_zero]
      rw [show tensorAlgMul A B hl
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f) g
          ⟨(p₁, 0), hp⟩ = 0 from hL,
        show tensorAlgMul A B hr f
          (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g)
          ⟨(p₁, 0), hp⟩ = 0 from hR, smul_zero, add_zero]
  | succ β =>
      have hq : (p₁, β).1 + (p₁, β).2 = n := by simp only at hp ⊢; omega
      rw [tensorDR_succ]
      show ((-1 : R)) ^ p₁ • TensorProduct.map LinearMap.id
          ((zeroActModule (A := A) B).dₗ β)
          (∑ rs : Splitting a b ⟨(p₁, β), hq⟩, splittingTerm A B f g rs) = _
      rw [map_sum, Finset.smul_sum]
      have hsplit : ∀ rs : Splitting a b ⟨(p₁, β), hq⟩,
          ((-1 : R)) ^ p₁ • TensorProduct.map LinearMap.id
              ((zeroActModule (A := A) B).dₗ β) (splittingTerm A B f g rs)
          = ((-1 : R)) ^ rs.1.1.1.1 • tensorPairₗ A B rs.2.1
                (show rs.1.1.1.2 + 1 + rs.1.2.1.2 = β + 1 by
                  have := rs.2.2; simp only at this ⊢; omega)
                (TensorProduct.map LinearMap.id (B.dₗ rs.1.1.1.2) (f rs.1.1)) (g rs.1.2)
            + ((-1 : R)) ^ a • (((-1 : R)) ^ rs.1.2.1.1 • tensorPairₗ A B rs.2.1
                (show rs.1.1.1.2 + (rs.1.2.1.2 + 1) = β + 1 by
                  have := rs.2.2; simp only at this ⊢; omega)
                (f rs.1.1) (TensorProduct.map LinearMap.id (B.dₗ rs.1.2.1.2) (g rs.1.2))) := by
        intro rs
        have hp1 : rs.1.1.1.1 + rs.1.2.1.1 = p₁ := rs.2.1
        have hra : rs.1.1.1.1 + rs.1.1.1.2 = a := rs.1.1.2
        show ((-1 : R)) ^ p₁ • TensorProduct.map LinearMap.id (B.dₗ β)
            (tensorPairₗ A B rs.2.1 rs.2.2 (f rs.1.1) (g rs.1.2)) = _
        rw [tensorPair_dR A B rs.2.1 rs.2.2 _ _ (f rs.1.1) (g rs.1.2), smul_add, smul_smul,
          smul_smul, smul_smul, ← pow_add, ← pow_add, ← pow_add]
        refine congrArg₂ (· + ·) ?_ ?_
        · congr 1
          refine neg_one_pow_eq_of_even_add _ _ (rs.1.1.1.1 + rs.1.2.1.1) ?_
          omega
        · congr 1
          refine neg_one_pow_eq_of_even_add _ _ (rs.1.1.1.1 + rs.1.2.1.1 + rs.1.1.1.2) ?_
          omega
      rw [Finset.sum_congr rfl fun rs _ => hsplit rs, Finset.sum_add_distrib, ← Finset.smul_sum]
      refine congrArg₂ (· + ·) ?_ (congrArg (fun z => ((-1 : R)) ^ a • z) ?_)
      · refine sum_shiftLeftSnd (a := a) (b := b) (q := ⟨(p₁, β), hq⟩) (p := ⟨(p₁, β + 1), hp⟩)
          rfl rfl _ _ (fun uv hu => ?_) (fun rs => ?_)
        · show tensorPairₗ A B uv.2.1 uv.2.2
            (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f uv.1.1)
            (g uv.1.2) = 0
          rw [tensorDR_of_snd_zero _ _ a f uv.1.1 hu, map_zero, LinearMap.zero_apply]
        · show ((-1 : R)) ^ rs.1.1.1.1 • tensorPairₗ A B _ _ _ (g rs.1.2)
            = tensorPairₗ A B _ _
              (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f
                (shiftLeftSnd rfl rfl rs).1.1) (g (shiftLeftSnd rfl rfl rs).1.2)
          rw [show (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f
              (shiftLeftSnd rfl rfl rs).1.1)
            = ((-1 : R)) ^ rs.1.1.1.1 • TensorProduct.map LinearMap.id (B.dₗ rs.1.1.1.2)
              (f rs.1.1) from rfl, LinearMap.map_smul₂]
      · refine sum_shiftRightSnd (a := a) (b := b) (q := ⟨(p₁, β), hq⟩) (p := ⟨(p₁, β + 1), hp⟩)
          rfl rfl _ _ (fun uv hv => ?_) (fun rs => ?_)
        · show tensorPairₗ A B uv.2.1 uv.2.2 (f uv.1.1)
            (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g uv.1.2) = 0
          rw [tensorDR_of_snd_zero _ _ b g uv.1.2 hv, map_zero]
        · show ((-1 : R)) ^ rs.1.2.1.1 • tensorPairₗ A B _ _ (f rs.1.1) _
            = tensorPairₗ A B _ _ (f (shiftRightSnd rfl rfl rs).1.1)
              (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g
                (shiftRightSnd rfl rfl rs).1.2)
          rw [show (tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g
              (shiftRightSnd rfl rfl rs).1.2)
            = ((-1 : R)) ^ rs.1.2.1.1 • TensorProduct.map LinearMap.id (B.dₗ rs.1.2.1.2)
              (g rs.1.2) from rfl]
          exact ((tensorPairₗ A B rs.2.1 (show rs.1.1.1.2 + (rs.1.2.1.2 + 1) = β + 1 by
            have := rs.2.2; simp only at this ⊢; omega) (f rs.1.1)).map_smul _ _).symm

/-- **The Leibniz rule for the product on a tensor product of algebras.** -/
theorem tensorAlgMul_extTensorD {a b n : ℕ} (h : a + b = n) (hl : a + 1 + b = n + 1)
    (hr : a + (b + 1) = n + 1)
    (f : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    extTensorD A B n (tensorAlgMul A B h f g)
      = tensorAlgMul A B hl (extTensorD A B a f) g
        + ((-1 : R)) ^ a • tensorAlgMul A B hr f (extTensorD A B b g) := by
  show tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorAlgMul A B h f g)
    + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) n
      (tensorAlgMul A B h f g) = _
  rw [tensorAlgMul_tensorDL A B h hl hr f g, tensorAlgMul_tensorDR A B h hl hr f g]
  show _ = tensorAlgMul A B hl
      (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f
        + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) a f) g
    + ((-1 : R)) ^ a • tensorAlgMul A B hr f
      (tensorDL (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g
        + tensorDR (CDGAStructure.selfModule A) (zeroActModule (A := A) B) b g)
  rw [tensorAlgMul_add_left, tensorAlgMul_add_right, smul_add]
  abel

end Leibniz

end External

end GaloisForLFunctions.HTGeometry
