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
def Splitting (a b : ℕ) {n : ℕ} (p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) : Type :=
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
  match x with
  | ⟨⟨⟨_, t⟩, hu1, hu2⟩, ⟨⟨r, s⟩, hr1, hr2⟩⟩ =>
      ⟨⟨(r, ⟨(s.1.1 + t.1.1, s.1.2 + t.1.2), by
            have hs := s.2
            have ht := t.2
            simp only at hs ht ⊢
            omega⟩), by
          have hs := s.2
          have ht := t.2
          simp only at hs ht hu1 hu2 hr1 hr2 ⊢
          omega⟩,
        ⟨(s, t), ⟨rfl, rfl⟩⟩⟩

/-- The inverse reassociation. -/
def splitReassocInv {a b c m q n : ℕ} (h₁ : a + b = m) (h₃ : b + c = q)
    {p : {pq : ℕ × ℕ // pq.1 + pq.2 = n}}
    (y : (us : Splitting a q p) × Splitting b c us.1.2) :
    (ts : Splitting m c p) × Splitting a b ts.1.1 :=
  match y with
  | ⟨⟨⟨r, _⟩, hu1, hu2⟩, ⟨⟨s, t⟩, hs1, hs2⟩⟩ =>
      ⟨⟨(⟨(r.1.1 + s.1.1, r.1.2 + s.1.2), by
            have hr := r.2
            have hs := s.2
            simp only at hr hs ⊢
            omega⟩, t), by
          have hr := r.2
          have hs := s.2
          simp only at hr hs hu1 hu2 hs1 hs2 ⊢
          omega⟩,
        ⟨(r, s), ⟨rfl, rfl⟩⟩⟩

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
  simp only [splitReassoc, splitReassocInv]

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
  simp only [splitReassoc, splitReassocInv]

end Convolution

end GaloisForLFunctions.HTGeometry
