import GaloisForLFunctions.HTGeometry.CDGAModule
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The graded tensor product of two differential graded modules

The tensor product of two graded modules has, in degree `n`, the sum of `M^a ⊗ N^b` over the
decompositions `a + b = n`.  Indexing it by the subtype `{ab : ℕ × ℕ // ab.1 + ab.2 = n}` — a finite
type, over which the product and the direct sum agree — keeps the additive structure the one `Pi`
already carries, and keeps truncated subtraction out of the definition, exactly as for the free
cell.

The total differential is the sum of two half-differentials: one differentiating the left factor,
one the right with the Koszul sign of the left degree.  Each half squares to zero because the
corresponding differential does, and the two anticommute, which is the sign cancellation that makes
the total differential square to zero.

* `HTGeometry.TensorCarrier` : the underlying graded module.
* `HTGeometry.tensorDL`, `HTGeometry.tensorDR` : the two half-differentials.
* `HTGeometry.tensorDL_tensorDL`, `HTGeometry.tensorDR_tensorDR` : each half squares to zero.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- The underlying graded module of the tensor product. -/
def TensorCarrier (M N : ℕ → Type w) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)] (n : ℕ) : Type w :=
  ∀ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, TensorProduct R (M p.1.1) (N p.1.2)

instance (n : ℕ) : AddCommGroup (TensorCarrier (R := R) M N n) :=
  inferInstanceAs (AddCommGroup
    (∀ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, TensorProduct R (M p.1.1) (N p.1.2)))

instance (n : ℕ) : Module R (TensorCarrier (R := R) M N n) :=
  inferInstanceAs (Module R
    (∀ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, TensorProduct R (M p.1.1) (N p.1.2)))

@[simp] theorem tensorCarrier_add_apply {n : ℕ} (f g : TensorCarrier (R := R) M N n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) : (f + g) p = f p + g p := rfl

@[simp] theorem tensorCarrier_smul_apply {n : ℕ} (c : R) (f : TensorCarrier (R := R) M N n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) : (c • f) p = c • f p := rfl

@[simp] theorem tensorCarrier_zero_apply {n : ℕ} (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (0 : TensorCarrier (R := R) M N n) p = 0 := rfl

/-- The half of the total differential that differentiates the left factor. -/
def tensorDL (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) : TensorCarrier (R := R) M N (n + 1) :=
  fun p =>
    match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, b), h⟩ =>
        TensorProduct.map (P.dₗ a) LinearMap.id (f ⟨(a, b), by omega⟩)

/-- The half of the total differential that differentiates the right factor, with the Koszul sign
of the left degree. -/
def tensorDR (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) : TensorCarrier (R := R) M N (n + 1) :=
  fun p =>
    match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, b + 1), h⟩ =>
        ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b) (f ⟨(a, b), by omega⟩)

@[simp] theorem tensorDL_zero (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n b : ℕ)
    (f : TensorCarrier (R := R) M N n) (h : (0, b).1 + (0, b).2 = n + 1) :
    tensorDL P Q n f ⟨(0, b), h⟩ = 0 := rfl

@[simp] theorem tensorDL_succ (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (n a b : ℕ) (f : TensorCarrier (R := R) M N n) (h : (a + 1, b).1 + (a + 1, b).2 = n + 1) :
    tensorDL P Q n f ⟨(a + 1, b), h⟩
      = TensorProduct.map (P.dₗ a) LinearMap.id (f ⟨(a, b), by omega⟩) := rfl

@[simp] theorem tensorDR_zero (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n a : ℕ)
    (f : TensorCarrier (R := R) M N n) (h : (a, 0).1 + (a, 0).2 = n + 1) :
    tensorDR P Q n f ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem tensorDR_succ (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (n a b : ℕ) (f : TensorCarrier (R := R) M N n) (h : (a, b + 1).1 + (a, b + 1).2 = n + 1) :
    tensorDR P Q n f ⟨(a, b + 1), h⟩
      = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b) (f ⟨(a, b), by omega⟩) := rfl

theorem tensorDL_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f g : TensorCarrier (R := R) M N n) :
    tensorDL P Q n (f + g) = tensorDL P Q n f + tensorDL P Q n g := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rfl
  | succ a' =>
      show TensorProduct.map (P.dₗ a') LinearMap.id ((f + g) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add]
      rfl

theorem tensorDR_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f g : TensorCarrier (R := R) M N n) :
    tensorDR P Q n (f + g) = tensorDR P Q n f + tensorDR P Q n g := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b')
        ((f + g) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add, smul_add]
      rfl

theorem tensorDL_smul (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (c : R) (f : TensorCarrier (R := R) M N n) :
    tensorDL P Q n (c • f) = c • tensorDL P Q n f := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rfl
  | succ a' =>
      show TensorProduct.map (P.dₗ a') LinearMap.id ((c • f) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul]
      rfl

theorem tensorDR_smul (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (c : R) (f : TensorCarrier (R := R) M N n) :
    tensorDR P Q n (c • f) = c • tensorDR P Q n f := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ b')
        ((c • f) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul, smul_comm]
      rfl

/-- The composite of two left differentials vanishes as a map of tensor products. -/
theorem tensorMap_dL_comp (P : CDGAModuleStructure A M) (a b : ℕ) :
    (TensorProduct.map (P.dₗ (a + 1)) (LinearMap.id : N b →ₗ[R] N b)).comp
      (TensorProduct.map (P.dₗ a) (LinearMap.id : N b →ₗ[R] N b)) = 0 := by
  rw [← TensorProduct.map_comp]
  refine TensorProduct.ext' fun x y => ?_
  show TensorProduct.map ((P.dₗ (a + 1)).comp (P.dₗ a)) (LinearMap.id.comp LinearMap.id) (x ⊗ₜ y)
    = 0
  rw [TensorProduct.map_tmul]
  show P.d (a + 1) (P.d a x) ⊗ₜ y = 0
  rw [P.d_d a x, TensorProduct.zero_tmul]

/-- The composite of two right differentials vanishes as a map of tensor products. -/
theorem tensorMap_dR_comp (Q : CDGAModuleStructure A N) (a b : ℕ) :
    (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ (b + 1))).comp
      (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ b)) = 0 := by
  rw [← TensorProduct.map_comp]
  refine TensorProduct.ext' fun x y => ?_
  show TensorProduct.map (LinearMap.id.comp LinearMap.id) ((Q.dₗ (b + 1)).comp (Q.dₗ b)) (x ⊗ₜ y)
    = 0
  rw [TensorProduct.map_tmul]
  show x ⊗ₜ Q.d (b + 1) (Q.d b y) = 0
  rw [Q.d_d b y, TensorProduct.tmul_zero]

/-- **The left half-differential squares to zero.** -/
theorem tensorDL_tensorDL (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) :
    tensorDL P Q (n + 1) (tensorDL P Q n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rfl
  | succ a' =>
      cases a' with
      | zero =>
          show TensorProduct.map (P.dₗ 0) LinearMap.id (tensorDL P Q n f ⟨(0, b), by omega⟩) = 0
          rw [tensorDL_zero, map_zero]
      | succ a'' =>
          show TensorProduct.map (P.dₗ (a'' + 1)) LinearMap.id
            (tensorDL P Q n f ⟨(a'' + 1, b), by omega⟩) = 0
          rw [tensorDL_succ]
          exact congrArg (fun L : TensorProduct R (M a'') (N b) →ₗ[R]
            TensorProduct R (M (a'' + 1 + 1)) (N b) => L (f ⟨(a'', b), by omega⟩))
            (tensorMap_dL_comp P a'' b)

/-- **The right half-differential squares to zero.** -/
theorem tensorDR_tensorDR (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) :
    tensorDR P Q (n + 1) (tensorDR P Q n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      cases b' with
      | zero =>
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ 0)
            (tensorDR P Q n f ⟨(a, 0), by omega⟩) = 0
          rw [tensorDR_zero, map_zero, smul_zero]
      | succ b'' =>
          show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (Q.dₗ (b'' + 1))
            (tensorDR P Q n f ⟨(a, b'' + 1), by omega⟩) = 0
          rw [tensorDR_succ, map_smul, smul_smul]
          have hz := congrArg (fun L : TensorProduct R (M a) (N b'') →ₗ[R]
            TensorProduct R (M a) (N (b'' + 1 + 1)) => L (f ⟨(a, b''), by omega⟩))
            (tensorMap_dR_comp Q a b'')
          simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
          rw [hz, smul_zero]

/-- The two half-differentials commute as maps of tensor products. -/
theorem tensorMap_comm (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (a b : ℕ) :
    (TensorProduct.map (P.dₗ a) (LinearMap.id : N (b + 1) →ₗ[R] N (b + 1))).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ b))
      = (TensorProduct.map (LinearMap.id : M (a + 1) →ₗ[R] M (a + 1)) (Q.dₗ b)).comp
        (TensorProduct.map (P.dₗ a) (LinearMap.id : N b →ₗ[R] N b)) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id, LinearMap.id_comp]

/-- **The two half-differentials anticommute.**  This is the sign cancellation that makes the total
differential square to zero: the two ways of differentiating both factors carry opposite Koszul
signs. -/
theorem tensorDL_tensorDR_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) :
    tensorDL P Q (n + 1) (tensorDR P Q n f) + tensorDR P Q (n + 1) (tensorDL P Q n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero =>
      cases b with
      | zero => rfl
      | succ b' =>
          show tensorDL P Q (n + 1) (tensorDR P Q n f) ⟨(0, b' + 1), h⟩
            + ((-1 : R)) ^ 0 • TensorProduct.map LinearMap.id (Q.dₗ b')
                (tensorDL P Q n f ⟨(0, b'), by omega⟩) = 0
          simp only [tensorDL_zero, map_zero, smul_zero, add_zero, zero_add]
  | succ a' =>
      cases b with
      | zero =>
          show TensorProduct.map (P.dₗ a') LinearMap.id
              (tensorDR P Q n f ⟨(a', 0), by omega⟩)
            + tensorDR P Q (n + 1) (tensorDL P Q n f) ⟨(a' + 1, 0), h⟩ = 0
          simp only [tensorDR_zero, map_zero, add_zero, zero_add]
      | succ b' =>
          show TensorProduct.map (P.dₗ a') LinearMap.id
              (tensorDR P Q n f ⟨(a', b' + 1), by omega⟩)
            + ((-1 : R)) ^ (a' + 1) • TensorProduct.map LinearMap.id (Q.dₗ b')
                (tensorDL P Q n f ⟨(a' + 1, b'), by omega⟩) = 0
          rw [tensorDR_succ, tensorDL_succ, map_smul]
          have hcomm := congrArg
            (fun L : TensorProduct R (M a') (N b') →ₗ[R] TensorProduct R (M (a' + 1)) (N (b' + 1))
              => L (f ⟨(a', b'), by omega⟩)) (tensorMap_comm P Q a' b')
          simp only [LinearMap.comp_apply] at hcomm
          rw [hcomm, pow_succ, mul_comm, neg_one_mul, neg_smul, add_neg_cancel]

/-- **The total differential of the tensor product.** -/
def tensorD (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) : TensorCarrier (R := R) M N (n + 1) :=
  tensorDL P Q n f + tensorDR P Q n f

theorem tensorD_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f g : TensorCarrier (R := R) M N n) :
    tensorD P Q n (f + g) = tensorD P Q n f + tensorD P Q n g := by
  show tensorDL P Q n (f + g) + tensorDR P Q n (f + g) = _
  rw [tensorDL_add, tensorDR_add]
  show _ = tensorDL P Q n f + tensorDR P Q n f + (tensorDL P Q n g + tensorDR P Q n g)
  abel

theorem tensorD_smul (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (c : R) (f : TensorCarrier (R := R) M N n) :
    tensorD P Q n (c • f) = c • tensorD P Q n f := by
  show tensorDL P Q n (c • f) + tensorDR P Q n (c • f) = _
  rw [tensorDL_smul, tensorDR_smul]
  show _ = c • (tensorDL P Q n f + tensorDR P Q n f)
  rw [smul_add]

/-- **The total differential of the tensor product squares to zero.** -/
theorem tensorD_tensorD (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) :
    tensorD P Q (n + 1) (tensorD P Q n f) = 0 := by
  show tensorDL P Q (n + 1) (tensorDL P Q n f + tensorDR P Q n f)
    + tensorDR P Q (n + 1) (tensorDL P Q n f + tensorDR P Q n f) = 0
  rw [tensorDL_add, tensorDR_add, tensorDL_tensorDL, tensorDR_tensorDR]
  have hmid := tensorDL_tensorDR_add P Q n f
  show 0 + tensorDL P Q (n + 1) (tensorDR P Q n f)
    + (tensorDR P Q (n + 1) (tensorDL P Q n f) + 0) = 0
  rw [zero_add, add_zero, hmid]

/-- The action of the algebra on the tensor product: through the left factor. -/
def tensorAct (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {b n m : ℕ}
    (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) :
    TensorCarrier (R := R) M N m :=
  fun p =>
    match p with
    | ⟨(a, c), ha⟩ =>
      if hb : b ≤ a then
        TensorProduct.map (P.actₗ (show b + (a - b) = a by omega) x) LinearMap.id
          (f ⟨(a - b, c), by omega⟩)
      else 0

theorem tensorAct_of_le (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {b n m : ℕ}
    (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) {a c : ℕ}
    (ha : (a, c).1 + (a, c).2 = m) (hb : b ≤ a) :
    tensorAct P Q h x f ⟨(a, c), ha⟩
      = TensorProduct.map (P.actₗ (show b + (a - b) = a by omega) x) LinearMap.id
          (f ⟨(a - b, c), by omega⟩) := dif_pos hb

theorem tensorAct_of_lt (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) {b n m : ℕ}
    (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) {a c : ℕ}
    (ha : (a, c).1 + (a, c).2 = m) (hb : ¬ b ≤ a) :
    tensorAct P Q h x f ⟨(a, c), ha⟩ = 0 := dif_neg hb

/-- The action at a component that visibly decomposes: no subtraction survives. -/
theorem tensorAct_apply_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) {i c : ℕ}
    (hi : (i, c).1 + (i, c).2 = n) (hbi : (b + i, c).1 + (b + i, c).2 = m) :
    tensorAct P Q h x f ⟨(b + i, c), hbi⟩
      = TensorProduct.map (P.actₗ (rfl : b + i = b + i) x) LinearMap.id (f ⟨(i, c), hi⟩) := by
  rw [tensorAct_of_le P Q h x f hbi (Nat.le_add_right b i)]
  have gen : ∀ (j : ℕ) (hj : (j, c).1 + (j, c).2 = n) (e : b + j = b + i),
      TensorProduct.map (P.actₗ e x) LinearMap.id (f ⟨(j, c), hj⟩)
        = TensorProduct.map (P.actₗ (rfl : b + i = b + i) x) LinearMap.id (f ⟨(i, c), hi⟩) := by
    intro j hj e
    obtain rfl : j = i := by omega
    rfl
  exact gen (b + i - b) (by simpa using by omega) (by omega)

/-- The action at a component with an arbitrary witness of the decomposition. -/
theorem tensorAct_apply_eq (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) {i a c : ℕ}
    (e : b + i = a) (hi : (i, c).1 + (i, c).2 = n) (ha : (a, c).1 + (a, c).2 = m) :
    tensorAct P Q h x f ⟨(a, c), ha⟩
      = TensorProduct.map (P.actₗ e x) LinearMap.id (f ⟨(i, c), hi⟩) := by
  subst e
  exact tensorAct_apply_add P Q h x f hi ha

theorem tensorAct_add_left (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x x' : X b) (f : TensorCarrier (R := R) M N n) :
    tensorAct P Q h (x + x') f = tensorAct P Q h x f + tensorAct P Q h x' f := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [tensorCarrier_add_apply, tensorAct_of_le P Q h _ f ha hb,
      tensorAct_of_le P Q h x f ha hb, tensorAct_of_le P Q h x' f ha hb]
    have hl : (P.actₗ (show b + (a - b) = a by omega) (x + x') : M (a - b) →ₗ[R] M a)
        = P.actₗ (show b + (a - b) = a by omega) x
          + P.actₗ (show b + (a - b) = a by omega) x' :=
      LinearMap.ext fun z => P.act_add_left _ x x' z
    rw [hl, TensorProduct.map_add_left]
    rfl
  · rw [tensorCarrier_add_apply, tensorAct_of_lt P Q h _ f ha hb,
      tensorAct_of_lt P Q h x f ha hb, tensorAct_of_lt P Q h x' f ha hb, add_zero]

theorem tensorAct_add_right (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f g : TensorCarrier (R := R) M N n) :
    tensorAct P Q h x (f + g) = tensorAct P Q h x f + tensorAct P Q h x g := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [tensorCarrier_add_apply, tensorAct_of_le P Q h x _ ha hb,
      tensorAct_of_le P Q h x f ha hb, tensorAct_of_le P Q h x g ha hb,
      tensorCarrier_add_apply, map_add]
  · rw [tensorCarrier_add_apply, tensorAct_of_lt P Q h x _ ha hb,
      tensorAct_of_lt P Q h x f ha hb, tensorAct_of_lt P Q h x g ha hb, add_zero]

theorem tensorAct_smul_left (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (r : R) (x : X b) (f : TensorCarrier (R := R) M N n) :
    tensorAct P Q h (r • x) f = r • tensorAct P Q h x f := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [tensorCarrier_smul_apply, tensorAct_of_le P Q h _ f ha hb,
      tensorAct_of_le P Q h x f ha hb]
    have hl : (P.actₗ (show b + (a - b) = a by omega) (r • x) : M (a - b) →ₗ[R] M a)
        = r • P.actₗ (show b + (a - b) = a by omega) x :=
      LinearMap.ext fun z => P.act_smul_left _ r x z
    rw [hl, TensorProduct.map_smul_left]
    rfl
  · rw [tensorCarrier_smul_apply, tensorAct_of_lt P Q h _ f ha hb,
      tensorAct_of_lt P Q h x f ha hb, smul_zero]

theorem tensorAct_smul_right (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (r : R) (x : X b) (f : TensorCarrier (R := R) M N n) :
    tensorAct P Q h x (r • f) = r • tensorAct P Q h x f := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [tensorCarrier_smul_apply, tensorAct_of_le P Q h x _ ha hb,
      tensorAct_of_le P Q h x f ha hb, tensorCarrier_smul_apply, map_smul]
  · rw [tensorCarrier_smul_apply, tensorAct_of_lt P Q h x _ ha hb,
      tensorAct_of_lt P Q h x f ha hb, smul_zero]

/-- **The right half-differential commutes with the action up to the Koszul sign.** -/
theorem tensorDR_tensorAct (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) :
    tensorDR P Q m (tensorAct P Q h x f)
      = ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
          (tensorDR P Q n f) := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  cases c with
  | zero =>
      rw [tensorDR_zero, tensorCarrier_smul_apply]
      by_cases hb : b ≤ a
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
        rw [tensorAct_apply_eq P Q _ x _ hi (by omega) ha, tensorDR_zero, map_zero, smul_zero]
      · rw [tensorAct_of_lt P Q _ x _ ha hb, smul_zero]
  | succ c' =>
      by_cases hb : b ≤ a
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
        rw [tensorDR_succ, tensorAct_apply_eq P Q h x f hi (by omega) (by omega),
          tensorCarrier_smul_apply,
          tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x (tensorDR P Q n f) hi
            (by omega) ha,
          tensorDR_succ, map_smul, smul_smul]
        have hcomm := congrArg
          (fun L : TensorProduct R (M i) (N c') →ₗ[R] TensorProduct R (M a) (N (c' + 1))
            => L (f ⟨(i, c'), by omega⟩))
          (show (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N (c' + 1) →ₗ[R] N (c' + 1))).comp
              (TensorProduct.map (LinearMap.id : M i →ₗ[R] M i) (Q.dₗ c'))
            = (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ c')).comp
              (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N c' →ₗ[R] N c')) by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id,
              LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp])
        simp only [LinearMap.comp_apply] at hcomm
        rw [← hcomm, ← pow_add]
        congr 2
        omega
      · rw [tensorDR_succ, tensorAct_of_lt P Q h x f (by omega) hb, map_zero, smul_zero,
          tensorCarrier_smul_apply,
          tensorAct_of_lt P Q (show b + (n + 1) = m + 1 by omega) x (tensorDR P Q n f) ha hb,
          smul_zero]

/-- **The left half-differential satisfies the Leibniz rule for the action.** -/
theorem tensorDL_tensorAct (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) :
    tensorDL P Q m (tensorAct P Q h x f)
      = tensorAct P Q (show b + 1 + n = m + 1 by omega) (A.d b x) f
        + ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorDL P Q n f) := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  cases a with
  | zero =>
      rw [tensorDL_zero, tensorCarrier_add_apply, tensorCarrier_smul_apply,
        tensorAct_of_lt P Q _ (A.d b x) f ha (by omega)]
      by_cases hb : b ≤ 0
      · rw [tensorAct_apply_eq P Q _ x _ (show b + 0 = 0 by omega) (by omega) ha,
          tensorDL_zero, map_zero, smul_zero, add_zero]
      · rw [tensorAct_of_lt P Q _ x _ ha hb, smul_zero, add_zero]
  | succ a' =>
      by_cases hb : b ≤ a'
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a' := Nat.le.dest hb
        rw [tensorDL_succ, tensorAct_apply_eq P Q h x f hi (by omega) (by omega),
          tensorCarrier_add_apply, tensorCarrier_smul_apply,
          tensorAct_apply_eq P Q (show b + 1 + n = m + 1 by omega) (A.d b x) f
            (show b + 1 + i = a' + 1 by omega) (by omega) ha,
          tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x (tensorDL P Q n f)
            (show b + (i + 1) = a' + 1 by omega) (by omega) ha,
          tensorDL_succ]
        have hpt : (P.dₗ a').comp (P.actₗ hi x)
            = P.actₗ (show b + 1 + i = a' + 1 by omega) (A.d b x)
              + ((-1 : R)) ^ b • (P.actₗ (show b + (i + 1) = a' + 1 by omega) x).comp
                  (P.dₗ i) := by
          refine LinearMap.ext fun z => ?_
          exact P.d_act hi x z
        have hmaps : (TensorProduct.map (P.dₗ a') (LinearMap.id : N c →ₗ[R] N c)).comp
              (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N c →ₗ[R] N c))
            = TensorProduct.map (P.actₗ (show b + 1 + i = a' + 1 by omega) (A.d b x))
                (LinearMap.id : N c →ₗ[R] N c)
              + ((-1 : R)) ^ b • (TensorProduct.map
                  (P.actₗ (show b + (i + 1) = a' + 1 by omega) x)
                  (LinearMap.id : N c →ₗ[R] N c)).comp
                  (TensorProduct.map (P.dₗ i) (LinearMap.id : N c →ₗ[R] N c)) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hpt,
            TensorProduct.map_add_left, TensorProduct.map_smul_left, LinearMap.id_comp]
        exact congrArg (fun L : TensorProduct R (M i) (N c) →ₗ[R]
          TensorProduct R (M (a' + 1)) (N c) => L (f ⟨(i, c), by omega⟩)) hmaps
      · rw [tensorDL_succ, tensorAct_of_lt P Q h x f (by omega) hb, map_zero,
          tensorCarrier_add_apply, tensorCarrier_smul_apply,
          tensorAct_of_lt P Q (show b + 1 + n = m + 1 by omega) (A.d b x) f ha (by omega)]
        by_cases hb2 : b ≤ a' + 1
        · rw [tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x (tensorDL P Q n f)
            (show b + 0 = a' + 1 by omega) (by omega) ha, tensorDL_zero, map_zero, smul_zero,
            add_zero]
        · rw [tensorAct_of_lt P Q (show b + (n + 1) = m + 1 by omega) x (tensorDL P Q n f) ha hb2,
            smul_zero, add_zero]

/-- **The Leibniz rule for the tensor product.** -/
theorem tensorD_tensorAct (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) :
    tensorD P Q m (tensorAct P Q h x f)
      = tensorAct P Q (show b + 1 + n = m + 1 by omega) (A.d b x) f
        + ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorD P Q n f) := by
  show tensorDL P Q m (tensorAct P Q h x f) + tensorDR P Q m (tensorAct P Q h x f) = _
  rw [tensorDL_tensorAct, tensorDR_tensorAct]
  show _ = tensorAct P Q (show b + 1 + n = m + 1 by omega) (A.d b x) f
    + ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
        (tensorDL P Q n f + tensorDR P Q n f)
  rw [tensorAct_add_right, smul_add]
  abel

/-- **The action of the algebra on the tensor product is associative.** -/
theorem tensorAct_assoc (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {a b k' m' m'' n : ℕ} (h₁ : a + b = m') (h₂ : m' + k' = n) (h₃ : b + k' = m'')
    (h₄ : a + m'' = n) (x : X a) (y : X b) (f : TensorCarrier (R := R) M N k') :
    tensorAct P Q h₂ (A.mul h₁ x y) f = tensorAct P Q h₄ x (tensorAct P Q h₃ y f) := by
  funext p
  obtain ⟨⟨d, c⟩, hd⟩ := p
  by_cases hm : m' ≤ d
  · obtain ⟨i, hi⟩ : ∃ i, m' + i = d := Nat.le.dest hm
    rw [tensorAct_apply_eq P Q h₂ _ f hi (by omega) hd,
      tensorAct_apply_eq P Q h₄ x _ (show a + (b + i) = d by omega) (by omega) hd,
      tensorAct_apply_eq P Q h₃ y f (show b + i = b + i from rfl) (by omega) (by omega)]
    have hcomp : (P.actₗ hi (A.mul h₁ x y) : M i →ₗ[R] M d)
        = (P.actₗ (show a + (b + i) = d by omega) x).comp
          (P.actₗ (show b + i = b + i from rfl) y) :=
      LinearMap.ext fun z =>
        P.act_assoc h₁ hi rfl (show a + (b + i) = d by omega) x y z
    have hmaps : TensorProduct.map (P.actₗ hi (A.mul h₁ x y)) (LinearMap.id : N c →ₗ[R] N c)
        = (TensorProduct.map (P.actₗ (show a + (b + i) = d by omega) x)
            (LinearMap.id : N c →ₗ[R] N c)).comp
          (TensorProduct.map (P.actₗ (show b + i = b + i from rfl) y)
            (LinearMap.id : N c →ₗ[R] N c)) := by
      rw [← TensorProduct.map_comp, hcomp, LinearMap.id_comp]
    exact congrArg (fun L : TensorProduct R (M i) (N c) →ₗ[R] TensorProduct R (M d) (N c) =>
      L (f ⟨(i, c), by omega⟩)) hmaps
  · rw [tensorAct_of_lt P Q h₂ _ f hd (by omega)]
    by_cases hha : a ≤ d
    · obtain ⟨j, hj⟩ : ∃ j, a + j = d := Nat.le.dest hha
      rw [tensorAct_apply_eq P Q h₄ x _ hj (by omega) hd,
        tensorAct_of_lt P Q h₃ y f (by omega) (by omega), map_zero]
    · rw [tensorAct_of_lt P Q h₄ x _ hd (by omega)]

/-- **The tensor product of two differential graded modules.** -/
def tensorModule (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) :
    CDGAModuleStructure A (TensorCarrier (R := R) M N) where
  act h x f := tensorAct P Q h x f
  d n f := tensorD P Q n f
  act_add_left h x x' f := tensorAct_add_left P Q h x x' f
  act_add_right h x f g := tensorAct_add_right P Q h x f g
  act_smul_left h r x f := tensorAct_smul_left P Q h r x f
  act_smul_right h r x f := tensorAct_smul_right P Q h r x f
  act_assoc h₁ h₂ h₃ h₄ x y f := tensorAct_assoc P Q h₁ h₂ h₃ h₄ x y f
  d_add n f g := tensorD_add P Q n f g
  d_smul n r f := tensorD_smul P Q n r f
  d_d n f := tensorD_tensorD P Q n f
  d_act h x f := tensorD_tensorAct P Q h x f

@[simp] theorem tensorModule_d (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    (tensorModule P Q).d n f = tensorD P Q n f := rfl

@[simp] theorem tensorModule_act (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M N n) :
    (tensorModule P Q).act h x f = tensorAct P Q h x f := rfl

section Functoriality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- **The tensor product is functorial in the left variable.** -/
def tensorMapLeft {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
    (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) :
    CDGAModuleHom (tensorModule P Q) (tensorModule P' Q) where
  toFun n f := fun p => TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id (f p)
  map_add n f g := by
    funext p
    show TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id (f p + g p) = _
    rw [map_add]
    rfl
  map_smul n r f := by
    funext p
    show TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id (r • f p) = _
    rw [map_smul]
    rfl
  map_act := by
    intro bA nM nR h x f
    funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    by_cases hb : bA ≤ a
    · obtain ⟨i, hi⟩ : ∃ i, bA + i = a := Nat.le.dest hb
      show TensorProduct.map (φ.mapₗ a) LinearMap.id (tensorAct P Q h x f ⟨(a, c), ha⟩) = _
      rw [tensorModule_act, tensorAct_apply_eq P Q h x f hi (by omega) ha,
        tensorAct_apply_eq P' Q h x (fun q => TensorProduct.map (φ.mapₗ q.1.1) LinearMap.id (f q))
          hi (by omega) ha]
      have hcomm : (TensorProduct.map (φ.mapₗ a) (LinearMap.id : N c →ₗ[R] N c)).comp
            (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N c →ₗ[R] N c))
          = (TensorProduct.map (P'.actₗ hi x) (LinearMap.id : N c →ₗ[R] N c)).comp
            (TensorProduct.map (φ.mapₗ i) (LinearMap.id : N c →ₗ[R] N c)) := by
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
        congr 1
        exact LinearMap.ext fun z => φ.map_act hi x z
      exact congrArg (fun L : TensorProduct R (M i) (N c) →ₗ[R]
        TensorProduct R (M' a) (N c) => L (f ⟨(i, c), by omega⟩)) hcomm
    · show TensorProduct.map (φ.mapₗ a) LinearMap.id (tensorAct P Q h x f ⟨(a, c), ha⟩) = _
      rw [tensorModule_act, tensorAct_of_lt P Q h x f ha hb, map_zero,
        tensorAct_of_lt P' Q h x
          (fun q => TensorProduct.map (φ.mapₗ q.1.1) LinearMap.id (f q)) ha hb]
  map_d n f := by
    funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show TensorProduct.map (φ.mapₗ a) LinearMap.id
      (tensorDL P Q n f ⟨(a, c), ha⟩ + tensorDR P Q n f ⟨(a, c), ha⟩)
      = tensorDL P' Q n (fun q => TensorProduct.map (φ.mapₗ q.1.1) LinearMap.id (f q))
          ⟨(a, c), ha⟩
        + tensorDR P' Q n (fun q => TensorProduct.map (φ.mapₗ q.1.1) LinearMap.id (f q))
          ⟨(a, c), ha⟩
    rw [map_add]
    congr 1
    · cases a with
      | zero => rw [tensorDL_zero, tensorDL_zero, map_zero]
      | succ a' =>
          rw [tensorDL_succ, tensorDL_succ]
          have hcomm : (TensorProduct.map (φ.mapₗ (a' + 1)) (LinearMap.id : N c →ₗ[R] N c)).comp
                (TensorProduct.map (P.dₗ a') (LinearMap.id : N c →ₗ[R] N c))
              = (TensorProduct.map (P'.dₗ a') (LinearMap.id : N c →ₗ[R] N c)).comp
                (TensorProduct.map (φ.mapₗ a') (LinearMap.id : N c →ₗ[R] N c)) := by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
            congr 1
            exact LinearMap.ext fun z => φ.map_d a' z
          exact congrArg (fun L : TensorProduct R (M a') (N c) →ₗ[R]
            TensorProduct R (M' (a' + 1)) (N c) => L (f ⟨(a', c), by omega⟩)) hcomm
    · cases c with
      | zero => rw [tensorDR_zero, tensorDR_zero, map_zero]
      | succ c' =>
          rw [tensorDR_succ, tensorDR_succ, map_smul]
          congr 1
          have hcomm : (TensorProduct.map (φ.mapₗ a) (LinearMap.id : N (c' + 1) →ₗ[R] N (c' + 1))).comp
                (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ c'))
              = (TensorProduct.map (LinearMap.id : M' a →ₗ[R] M' a) (Q.dₗ c')).comp
                (TensorProduct.map (φ.mapₗ a) (LinearMap.id : N c' →ₗ[R] N c')) := by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id,
              LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp]
          exact congrArg (fun L : TensorProduct R (M a) (N c') →ₗ[R]
            TensorProduct R (M' a) (N (c' + 1)) => L (f ⟨(a, c'), by omega⟩)) hcomm

end Functoriality

section SigmaR

variable {C : ℕ → Type w} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

/-- A degree-one family of maps `C → N`, applied in the right factor of a tensor product with the
Koszul sign of the left degree.  With `σ` the differential this is `tensorDR`; with `σ` a twisting
cochain it is the twist induced on the tensor product. -/
def tensorSigmaR (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m : ℕ)
    (f : TensorCarrier (R := R) M C m) : TensorCarrier (R := R) M N (m + 1) :=
  fun p =>
    match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, b + 1), h⟩ =>
        ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (σ b) (f ⟨(a, b), by omega⟩)

@[simp] theorem tensorSigmaR_zero (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m a : ℕ)
    (f : TensorCarrier (R := R) M C m) (h : (a, 0).1 + (a, 0).2 = m + 1) :
    tensorSigmaR (M := M) σ m f ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem tensorSigmaR_succ (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m a b : ℕ)
    (f : TensorCarrier (R := R) M C m) (h : (a, b + 1).1 + (a, b + 1).2 = m + 1) :
    tensorSigmaR (M := M) σ m f ⟨(a, b + 1), h⟩
      = ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (σ b) (f ⟨(a, b), by omega⟩) := rfl

theorem tensorSigmaR_add (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m : ℕ)
    (f g : TensorCarrier (R := R) M C m) :
    tensorSigmaR (M := M) σ m (f + g)
      = tensorSigmaR (M := M) σ m f + tensorSigmaR (M := M) σ m g := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (σ b')
        ((f + g) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add, smul_add]
      rfl

theorem tensorSigmaR_smul (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m : ℕ) (r : R)
    (f : TensorCarrier (R := R) M C m) :
    tensorSigmaR (M := M) σ m (r • f) = r • tensorSigmaR (M := M) σ m f := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases b with
  | zero => rfl
  | succ b' =>
      show ((-1 : R)) ^ a • TensorProduct.map LinearMap.id (σ b')
        ((r • f) ⟨(a, b'), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul, smul_comm]
      rfl

/-- `tensorDR` is the case of `tensorSigmaR` where the family is the differential. -/
theorem tensorDR_eq_tensorSigmaR (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    tensorDR P Q n f = tensorSigmaR (M := M) (fun k => Q.dₗ k) n f := rfl

/-- The left differential and a right-factor family commute as maps of tensor products. -/
theorem tensorMap_sigma_comm (P : CDGAModuleStructure A M) (σ : ∀ n, C n →ₗ[R] N (n + 1))
    (a b : ℕ) :
    (TensorProduct.map (P.dₗ a) (LinearMap.id : N (b + 1) →ₗ[R] N (b + 1))).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (σ b))
      = (TensorProduct.map (LinearMap.id : M (a + 1) →ₗ[R] M (a + 1)) (σ b)).comp
        (TensorProduct.map (P.dₗ a) (LinearMap.id : C b →ₗ[R] C b)) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id, LinearMap.id_comp]

/-- **The left half-differential anticommutes with a right-factor family.**  No property of the
family is used: the sign is the one carried by the family itself. -/
theorem tensorDL_tensorSigmaR_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (Qc : CDGAModuleStructure A C) (σ : ∀ n, C n →ₗ[R] N (n + 1)) (n : ℕ)
    (f : TensorCarrier (R := R) M C n) :
    tensorDL P Q (n + 1) (tensorSigmaR (M := M) σ n f)
      + tensorSigmaR (M := M) σ (n + 1) (tensorDL P Qc n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  show tensorDL P Q (n + 1) (tensorSigmaR (M := M) σ n f) ⟨(a, b), h⟩
      + tensorSigmaR (M := M) σ (n + 1) (tensorDL P Qc n f) ⟨(a, b), h⟩ = 0
  cases a with
  | zero =>
      cases b with
      | zero => simp only [tensorDL_zero, tensorSigmaR_zero, add_zero]
      | succ b' =>
          rw [tensorDL_zero, tensorSigmaR_succ, tensorDL_zero, map_zero, smul_zero, add_zero]
  | succ a' =>
      cases b with
      | zero =>
          rw [tensorDL_succ, tensorSigmaR_zero, map_zero, tensorSigmaR_zero, add_zero]
      | succ b' =>
          rw [tensorDL_succ, tensorSigmaR_succ, tensorSigmaR_succ, tensorDL_succ, map_smul]
          have hcomm := congrArg
            (fun L : TensorProduct R (M a') (C b') →ₗ[R] TensorProduct R (M (a' + 1)) (N (b' + 1))
              => L (f ⟨(a', b'), by omega⟩)) (tensorMap_sigma_comm (N := N) P σ a' b')
          simp only [LinearMap.comp_apply] at hcomm
          rw [hcomm, pow_succ, mul_comm, neg_one_mul, neg_smul, add_neg_cancel]

/-- A right-factor family composed with the two differentials, in the right factor. -/
theorem tensorMap_sigma_d_apply (Q : CDGAModuleStructure A N) (Qc : CDGAModuleStructure A C)
    (σ : ∀ n, C n →ₗ[R] N (n + 1))
    (hσ : ∀ (k : ℕ) (c : C k), Q.d (k + 1) (σ k c) + σ (k + 1) (Qc.d k c) = 0)
    (a b : ℕ) (z : TensorProduct R (M a) (C b)) :
    TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ (b + 1))
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (σ b) z)
      + TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (σ (b + 1))
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Qc.dₗ b) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, ← TensorProduct.tmul_add]
      show (LinearMap.id (LinearMap.id x) : M a) ⊗ₜ[R]
        (Q.d (b + 1) (σ b y) + σ (b + 1) (Qc.d b y)) = 0
      rw [hσ b y, TensorProduct.tmul_zero]
  | add z w hz hw =>
      simp only [map_add]
      rw [add_add_add_comm, hz, hw, add_zero]

/-- **The right half-differential and a right-factor family anticommute** as soon as the family
anticommutes with the differentials of the two modules it connects. -/
theorem tensorDR_tensorSigmaR_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (Qc : CDGAModuleStructure A C) (σ : ∀ n, C n →ₗ[R] N (n + 1))
    (hσ : ∀ (k : ℕ) (c : C k), Q.d (k + 1) (σ k c) + σ (k + 1) (Qc.d k c) = 0) (n : ℕ)
    (f : TensorCarrier (R := R) M C n) :
    tensorDR P Q (n + 1) (tensorSigmaR (M := M) σ n f)
      + tensorSigmaR (M := M) σ (n + 1) (tensorDR P Qc n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  show tensorDR P Q (n + 1) (tensorSigmaR (M := M) σ n f) ⟨(a, b), h⟩
      + tensorSigmaR (M := M) σ (n + 1) (tensorDR P Qc n f) ⟨(a, b), h⟩ = 0
  cases b with
  | zero => simp only [tensorDR_zero, tensorSigmaR_zero, add_zero]
  | succ b' =>
      cases b' with
      | zero =>
          rw [tensorDR_succ, tensorSigmaR_zero, map_zero, smul_zero, tensorSigmaR_succ,
            tensorDR_zero, map_zero, smul_zero, add_zero]
      | succ b'' =>
          rw [tensorDR_succ, tensorSigmaR_succ, tensorSigmaR_succ, tensorDR_succ, map_smul,
            map_smul, smul_smul, smul_smul, ← smul_add,
            tensorMap_sigma_d_apply Q Qc σ hσ a b'' (f ⟨(a, b''), by omega⟩), smul_zero]

/-- **The right half-differential rule for a right-factor family under the action.** -/
theorem tensorSigmaR_tensorAct (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (Qc : CDGAModuleStructure A C) (σ : ∀ n, C n →ₗ[R] N (n + 1))
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) M C n) :
    tensorSigmaR (M := M) σ m (tensorAct P Qc h x f)
      = ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
          (tensorSigmaR (M := M) σ n f) := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  cases c with
  | zero =>
      rw [tensorSigmaR_zero, tensorCarrier_smul_apply]
      by_cases hb : b ≤ a
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
        rw [tensorAct_apply_eq P Q _ x _ hi (by omega) ha, tensorSigmaR_zero, map_zero, smul_zero]
      · rw [tensorAct_of_lt P Q _ x _ ha hb, smul_zero]
  | succ c' =>
      by_cases hb : b ≤ a
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
        rw [tensorSigmaR_succ, tensorAct_apply_eq P Qc h x f hi (by omega) (by omega),
          tensorCarrier_smul_apply,
          tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorSigmaR (M := M) σ n f) hi (by omega) ha,
          tensorSigmaR_succ, map_smul, smul_smul]
        have hcomm := congrArg
          (fun L : TensorProduct R (M i) (C c') →ₗ[R] TensorProduct R (M a) (N (c' + 1))
            => L (f ⟨(i, c'), by omega⟩))
          (show (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N (c' + 1) →ₗ[R] N (c' + 1))).comp
              (TensorProduct.map (LinearMap.id : M i →ₗ[R] M i) (σ c'))
            = (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (σ c')).comp
              (TensorProduct.map (P.actₗ hi x) (LinearMap.id : C c' →ₗ[R] C c')) by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id,
              LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp])
        simp only [LinearMap.comp_apply] at hcomm
        rw [← hcomm, ← pow_add]
        congr 2
        omega
      · rw [tensorSigmaR_succ, tensorAct_of_lt P Qc h x f (by omega) hb, map_zero, smul_zero,
          tensorCarrier_smul_apply,
          tensorAct_of_lt P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorSigmaR (M := M) σ n f) ha hb, smul_zero]

/-- **The total differential and a right-factor family anticommute.** -/
theorem tensorD_tensorSigmaR_add (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (Qc : CDGAModuleStructure A C) (σ : ∀ n, C n →ₗ[R] N (n + 1))
    (hσ : ∀ (k : ℕ) (c : C k), Q.d (k + 1) (σ k c) + σ (k + 1) (Qc.d k c) = 0) (n : ℕ)
    (f : TensorCarrier (R := R) M C n) :
    tensorD P Q (n + 1) (tensorSigmaR (M := M) σ n f)
      + tensorSigmaR (M := M) σ (n + 1) (tensorD P Qc n f) = 0 := by
  have hL := tensorDL_tensorSigmaR_add P Q Qc σ n f
  have hR := tensorDR_tensorSigmaR_add P Q Qc σ hσ n f
  show tensorDL P Q (n + 1) (tensorSigmaR (M := M) σ n f)
      + tensorDR P Q (n + 1) (tensorSigmaR (M := M) σ n f)
      + tensorSigmaR (M := M) σ (n + 1) (tensorDL P Qc n f + tensorDR P Qc n f) = 0
  rw [tensorSigmaR_add, add_add_add_comm, hL, hR, add_zero]

/-- **The twist induced on a tensor product.**  Attaching a cell to the right factor of `M ⊗ −`
attaches the tensored cell to `M ⊗ −`, twisted by the original cochain applied in the right factor
with the Koszul sign of the left degree. -/
def tensorTwistR (P : CDGAModuleStructure A M) {Q : CDGAModuleStructure A N}
    {Qc : CDGAModuleStructure A C} (t : CDGATwist Q Qc) :
    CDGATwist (tensorModule P Q) (tensorModule P Qc) where
  τ n v := tensorSigmaR (M := M) (fun k => t.τₗ k) n v
  τ_add n v v' := tensorSigmaR_add (M := M) (fun k => t.τₗ k) n v v'
  τ_smul n r v := tensorSigmaR_smul (M := M) (fun k => t.τₗ k) n r v
  τ_act h x v := by
    rw [tensorModule_act, tensorModule_act]
    exact tensorSigmaR_tensorAct P Q Qc (fun k => t.τₗ k) h x v
  τ_d n v := by
    rw [tensorModule_d, tensorModule_d]
    exact tensorD_tensorSigmaR_add P Q Qc (fun k => t.τₗ k) (fun k c => t.τ_d k c) n v

@[simp] theorem tensorTwistR_τ (P : CDGAModuleStructure A M) {Q : CDGAModuleStructure A N}
    {Qc : CDGAModuleStructure A C} (t : CDGATwist Q Qc) (n : ℕ)
    (v : TensorCarrier (R := R) M C n) :
    (tensorTwistR P t).τ n v = tensorSigmaR (M := M) (fun k => t.τₗ k) n v := rfl

end SigmaR

section Distributivity

variable {C : ℕ → Type w} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  {D : ℕ → Type w} [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]

/-- **The tensor product distributes over a direct sum in the second variable**, bidegree by
bidegree.  The two sides have different carriers — a family of tensor products with a product on the
right, against a product of two families — so the comparison can only ever be a degreewise
bijection, never an equality; `IsQuasiIso.of_bijective` is what carries a quasi-isomorphism across
it. -/
noncomputable def tensorProdRight (n : ℕ) :
    TensorCarrier (R := R) M (fun k => N k × C k) n
      ≃ₗ[R] TensorCarrier (R := R) M N n × TensorCarrier (R := R) M C n where
  toFun f :=
    (fun p => (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2) (f p)).1,
     fun p => (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2) (f p)).2)
  map_add' f g := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)) (f p + g p)).1 = _
      rw [map_add]
      rfl
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)) (f p + g p)).2 = _
      rw [map_add]
      rfl
  map_smul' r f := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)) (r • f p)).1 = _
      rw [map_smul]
      rfl
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)) (r • f p)).2 = _
      rw [map_smul]
      rfl
  invFun g := fun p =>
    (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)).symm (g.1 p, g.2 p)
  left_inv f := by
    funext p
    show (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)).symm
      ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)) (f p)) = f p
    rw [LinearEquiv.symm_apply_apply]
  right_inv g := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2))
        ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)).symm (g.1 p, g.2 p))).1 = _
      rw [LinearEquiv.apply_symm_apply]
    · funext p
      show ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2))
        ((TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2)).symm (g.1 p, g.2 p))).2 = _
      rw [LinearEquiv.apply_symm_apply]

theorem tensorProdRight_bijective (n : ℕ) :
    Function.Bijective (tensorProdRight (R := R) (M := M) (N := N) (C := C) n) :=
  (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).toEquiv.bijective

@[simp] theorem tensorProdRight_fst (n : ℕ)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1 p
      = (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2) (f p)).1 := rfl

@[simp] theorem tensorProdRight_snd (n : ℕ)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 p
      = (TensorProduct.prodRight R R (M p.1.1) (N p.1.2) (C p.1.2) (f p)).2 := rfl

/-- Distributivity commutes with a map applied in the left factor: first component. -/
theorem prodRight_map_left_fst {a a' b : ℕ} (φ : M a →ₗ[R] D a')
    (z : TensorProduct R (M a) (N b × C b)) :
    (TensorProduct.prodRight R R (D a') (N b) (C b)
        (TensorProduct.map φ (LinearMap.id : (N b × C b) →ₗ[R] (N b × C b)) z)).1
      = TensorProduct.map φ (LinearMap.id : N b →ₗ[R] N b)
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add z w hz hw => simp only [map_add, Prod.fst_add, hz, hw]

/-- Distributivity commutes with a map applied in the left factor: second component. -/
theorem prodRight_map_left_snd {a a' b : ℕ} (φ : M a →ₗ[R] D a')
    (z : TensorProduct R (M a) (N b × C b)) :
    (TensorProduct.prodRight R R (D a') (N b) (C b)
        (TensorProduct.map φ (LinearMap.id : (N b × C b) →ₗ[R] (N b × C b)) z)).2
      = TensorProduct.map φ (LinearMap.id : C b →ₗ[R] C b)
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add z w hz hw => simp only [map_add, Prod.snd_add, hz, hw]

/-- Distributivity turns a triangular map of the right factor into the two half-maps it is made
of.  This is the identity that transports a twist across the distributivity comparison. -/
theorem prodRight_map_right_fst {a b b' : ℕ} (ψ₁ : N b →ₗ[R] N b') (ψ₂ : C b →ₗ[R] N b')
    (g : (N b × C b) →ₗ[R] (N b' × C b')) (hg : ∀ w : N b × C b, (g w).1 = ψ₁ w.1 + ψ₂ w.2)
    (z : TensorProduct R (M a) (N b × C b)) :
    (TensorProduct.prodRight R R (M a) (N b') (C b')
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) g z)).1
      = TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) ψ₁
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).1
        + TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) ψ₂
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp [hg, TensorProduct.tmul_add]
  | add z w hz hw =>
      simp only [map_add, Prod.fst_add, Prod.snd_add, hz, hw]
      abel

/-- The second component of a triangular map of the right factor, after distributivity. -/
theorem prodRight_map_right_snd {a b b' : ℕ} (ψ₃ : C b →ₗ[R] C b')
    (g : (N b × C b) →ₗ[R] (N b' × C b')) (hg : ∀ w : N b × C b, (g w).2 = ψ₃ w.2)
    (z : TensorProduct R (M a) (N b × C b)) :
    (TensorProduct.prodRight R R (M a) (N b') (C b')
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) g z)).2
      = TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) ψ₃
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp [hg]
  | add z w hz hw => simp only [map_add, Prod.snd_add, hz, hw]

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
  (Qc : CDGAModuleStructure A C)

/-- Distributivity transports the left half-differential to the pair of left half-differentials. -/
theorem tensorProdRight_tensorDL (t : CDGATwist Q Qc) (n : ℕ)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    tensorProdRight (R := R) (M := M) (N := N) (C := C) (n + 1)
        (tensorDL P (CDGAModuleStructure.twisted Q Qc t) n f)
      = (tensorDL P Q n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1,
         tensorDL P Qc n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M a) (N b) (C b)
        (tensorDL P (CDGAModuleStructure.twisted Q Qc t) n f ⟨(a, b), h⟩)).1
      = tensorDL P Q n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1 ⟨(a, b), h⟩
    cases a with
    | zero => rw [tensorDL_zero, map_zero, Prod.fst_zero, tensorDL_zero]
    | succ a' =>
        rw [tensorDL_succ, prodRight_map_left_fst, tensorDL_succ, tensorProdRight_fst]
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M a) (N b) (C b)
        (tensorDL P (CDGAModuleStructure.twisted Q Qc t) n f ⟨(a, b), h⟩)).2
      = tensorDL P Qc n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 ⟨(a, b), h⟩
    cases a with
    | zero => rw [tensorDL_zero, map_zero, Prod.snd_zero, tensorDL_zero]
    | succ a' =>
        rw [tensorDL_succ, prodRight_map_left_snd, tensorDL_succ, tensorProdRight_snd]

/-- **Distributivity transports the right half-differential of a twisted right factor to the right
half-differential together with the induced twist.**  This is the identity that names the twist
`tensorTwistR`: the off-diagonal part of the differential of a cell attachment becomes, after
distributing, exactly the tensored twisting cochain. -/
theorem tensorProdRight_tensorDR (t : CDGATwist Q Qc) (n : ℕ)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    tensorProdRight (R := R) (M := M) (N := N) (C := C) (n + 1)
        (tensorDR P (CDGAModuleStructure.twisted Q Qc t) n f)
      = (tensorDR P Q n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1
            + tensorSigmaR (M := M) (fun k => t.τₗ k) n
              (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2,
         tensorDR P Qc n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M a) (N b) (C b)
        (tensorDR P (CDGAModuleStructure.twisted Q Qc t) n f ⟨(a, b), h⟩)).1
      = (tensorDR P Q n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1
          + tensorSigmaR (M := M) (fun k => t.τₗ k) n
            (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2) ⟨(a, b), h⟩
    cases b with
    | zero =>
        rw [tensorDR_zero, map_zero, Prod.fst_zero, tensorCarrier_add_apply, tensorDR_zero,
          tensorSigmaR_zero, add_zero]
    | succ b' =>
        rw [tensorDR_succ, map_smul, Prod.smul_fst,
          prodRight_map_right_fst (Q.dₗ b') (t.τₗ b')
            ((CDGAModuleStructure.twisted Q Qc t).dₗ b') (fun w => rfl),
          tensorCarrier_add_apply, tensorDR_succ, tensorSigmaR_succ, tensorProdRight_fst,
          tensorProdRight_snd, smul_add]
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodRight R R (M a) (N b) (C b)
        (tensorDR P (CDGAModuleStructure.twisted Q Qc t) n f ⟨(a, b), h⟩)).2
      = tensorDR P Qc n (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 ⟨(a, b), h⟩
    cases b with
    | zero => rw [tensorDR_zero, map_zero, Prod.snd_zero, tensorDR_zero]
    | succ b' =>
        rw [tensorDR_succ, map_smul, Prod.smul_snd,
          prodRight_map_right_snd (Qc.dₗ b') ((CDGAModuleStructure.twisted Q Qc t).dₗ b')
            (fun w => rfl),
          tensorDR_succ, tensorProdRight_snd]

/-- Distributivity transports the action to the componentwise action. -/
theorem tensorProdRight_tensorAct (t : CDGATwist Q Qc) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    tensorProdRight (R := R) (M := M) (N := N) (C := C) m
        (tensorAct P (CDGAModuleStructure.twisted Q Qc t) h x f)
      = (tensorAct P Q h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1,
         tensorAct P Qc h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show (TensorProduct.prodRight R R (M a) (N c) (C c)
        (tensorAct P (CDGAModuleStructure.twisted Q Qc t) h x f ⟨(a, c), ha⟩)).1
      = tensorAct P Q h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1 ⟨(a, c), ha⟩
    by_cases hb : b ≤ a
    · rw [tensorAct_of_le P (CDGAModuleStructure.twisted Q Qc t) h x f ha hb,
        prodRight_map_left_fst,
        tensorAct_of_le P Q h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1 ha hb,
        tensorProdRight_fst]
    · rw [tensorAct_of_lt P (CDGAModuleStructure.twisted Q Qc t) h x f ha hb, map_zero,
        Prod.fst_zero,
        tensorAct_of_lt P Q h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).1 ha hb]
  · funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show (TensorProduct.prodRight R R (M a) (N c) (C c)
        (tensorAct P (CDGAModuleStructure.twisted Q Qc t) h x f ⟨(a, c), ha⟩)).2
      = tensorAct P Qc h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 ⟨(a, c), ha⟩
    by_cases hb : b ≤ a
    · rw [tensorAct_of_le P (CDGAModuleStructure.twisted Q Qc t) h x f ha hb,
        prodRight_map_left_snd,
        tensorAct_of_le P Qc h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 ha hb,
        tensorProdRight_snd]
    · rw [tensorAct_of_lt P (CDGAModuleStructure.twisted Q Qc t) h x f ha hb, map_zero,
        Prod.snd_zero,
        tensorAct_of_lt P Qc h x (tensorProdRight (R := R) (M := M) (N := N) (C := C) n f).2 ha hb]

/-- **Tensoring commutes with attaching a cell.**  The distributivity comparison is a map of
differential graded modules from the tensor product with a cell attachment to the cell attachment,
along the induced twist, of the tensor products. -/
noncomputable def tensorProdRightHom (t : CDGATwist Q Qc) :
    CDGAModuleHom (tensorModule P (CDGAModuleStructure.twisted Q Qc t))
      (CDGAModuleStructure.twisted (tensorModule P Q) (tensorModule P Qc)
        (tensorTwistR P t)) where
  toFun n f := tensorProdRight (R := R) (M := M) (N := N) (C := C) n f
  map_add n f g := map_add (tensorProdRight (R := R) (M := M) (N := N) (C := C) n) f g
  map_smul n c f := map_smul (tensorProdRight (R := R) (M := M) (N := N) (C := C) n) c f
  map_act h x f := by
    show tensorProdRight (R := R) (M := M) (N := N) (C := C) _
      (tensorAct P (CDGAModuleStructure.twisted Q Qc t) h x f) = _
    rw [tensorProdRight_tensorAct]
    rfl
  map_d n f := by
    show tensorProdRight (R := R) (M := M) (N := N) (C := C) (n + 1)
      (tensorD P (CDGAModuleStructure.twisted Q Qc t) n f) = _
    rw [show tensorD P (CDGAModuleStructure.twisted Q Qc t) n f
          = tensorDL P (CDGAModuleStructure.twisted Q Qc t) n f
            + tensorDR P (CDGAModuleStructure.twisted Q Qc t) n f from rfl,
      map_add, tensorProdRight_tensorDL, tensorProdRight_tensorDR]
    exact Prod.ext (add_assoc _ _ _).symm rfl

theorem tensorProdRightHom_isQuasiIso (t : CDGATwist Q Qc) :
    (tensorProdRightHom P Q Qc t).IsQuasiIso :=
  CDGAModuleHom.IsQuasiIso.of_bijective (fun n => tensorProdRight_bijective n)

end Distributivity

section RightFunctoriality

variable {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

/-- **The tensor product is functorial in the right variable.**  No Koszul sign appears: a morphism
has degree zero, so the sign carried by the right half-differential is the same before and after. -/
def tensorMapRight (P : CDGAModuleStructure A M) {Q : CDGAModuleStructure A N}
    {Q' : CDGAModuleStructure A N'} (ψ : CDGAModuleHom Q Q') :
    CDGAModuleHom (tensorModule P Q) (tensorModule P Q') where
  toFun n f := fun p => TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (f p)
  map_add n f g := by
    funext p
    show TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (f p + g p) = _
    rw [map_add]
    rfl
  map_smul n r f := by
    funext p
    show TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (r • f p) = _
    rw [map_smul]
    rfl
  map_act := by
    intro bA nM nR h x f
    funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    by_cases hb : bA ≤ a
    · obtain ⟨i, hi⟩ : ∃ i, bA + i = a := Nat.le.dest hb
      show TensorProduct.map LinearMap.id (ψ.mapₗ c) (tensorAct P Q h x f ⟨(a, c), ha⟩) = _
      rw [tensorModule_act, tensorAct_apply_eq P Q h x f hi (by omega) ha,
        tensorAct_apply_eq P Q' h x (fun q => TensorProduct.map LinearMap.id (ψ.mapₗ q.1.2) (f q))
          hi (by omega) ha]
      have hcomm : (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (ψ.mapₗ c)).comp
            (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N c →ₗ[R] N c))
          = (TensorProduct.map (P.actₗ hi x) (LinearMap.id : N' c →ₗ[R] N' c)).comp
            (TensorProduct.map (LinearMap.id : M i →ₗ[R] M i) (ψ.mapₗ c)) := by
        rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
          LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
      exact congrArg (fun L : TensorProduct R (M i) (N c) →ₗ[R]
        TensorProduct R (M a) (N' c) => L (f ⟨(i, c), by omega⟩)) hcomm
    · show TensorProduct.map LinearMap.id (ψ.mapₗ c) (tensorAct P Q h x f ⟨(a, c), ha⟩) = _
      rw [tensorModule_act, tensorAct_of_lt P Q h x f ha hb, map_zero,
        tensorAct_of_lt P Q' h x
          (fun q => TensorProduct.map LinearMap.id (ψ.mapₗ q.1.2) (f q)) ha hb]
  map_d n f := by
    funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show TensorProduct.map LinearMap.id (ψ.mapₗ c)
      (tensorDL P Q n f ⟨(a, c), ha⟩ + tensorDR P Q n f ⟨(a, c), ha⟩)
      = tensorDL P Q' n (fun q => TensorProduct.map LinearMap.id (ψ.mapₗ q.1.2) (f q))
          ⟨(a, c), ha⟩
        + tensorDR P Q' n (fun q => TensorProduct.map LinearMap.id (ψ.mapₗ q.1.2) (f q))
          ⟨(a, c), ha⟩
    rw [map_add]
    congr 1
    · cases a with
      | zero => rw [tensorDL_zero, tensorDL_zero, map_zero]
      | succ a' =>
          rw [tensorDL_succ, tensorDL_succ]
          have hcomm : (TensorProduct.map (LinearMap.id : M (a' + 1) →ₗ[R] M (a' + 1))
                (ψ.mapₗ c)).comp
                (TensorProduct.map (P.dₗ a') (LinearMap.id : N c →ₗ[R] N c))
              = (TensorProduct.map (P.dₗ a') (LinearMap.id : N' c →ₗ[R] N' c)).comp
                (TensorProduct.map (LinearMap.id : M a' →ₗ[R] M a') (ψ.mapₗ c)) := by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
              LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
          exact congrArg (fun L : TensorProduct R (M a') (N c) →ₗ[R]
            TensorProduct R (M (a' + 1)) (N' c) => L (f ⟨(a', c), by omega⟩)) hcomm
    · cases c with
      | zero => rw [tensorDR_zero, tensorDR_zero, map_zero]
      | succ c' =>
          rw [tensorDR_succ, tensorDR_succ, map_smul]
          have hcomm : (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a)
                (ψ.mapₗ (c' + 1))).comp
                (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q.dₗ c'))
              = (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (Q'.dₗ c')).comp
                (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (ψ.mapₗ c')) := by
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
            congr 1
            exact LinearMap.ext fun z => ψ.map_d c' z
          exact congrArg (fun L : TensorProduct R (M a) (N c') →ₗ[R]
            TensorProduct R (M a) (N' (c' + 1)) => ((-1 : R)) ^ a • L (f ⟨(a, c'), by omega⟩))
            hcomm

@[simp] theorem tensorMapRight_toFun (P : CDGAModuleStructure A M) {Q : CDGAModuleStructure A N}
    {Q' : CDGAModuleStructure A N'} (ψ : CDGAModuleHom Q Q') (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorMapRight P ψ).toFun n f p
      = TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (f p) := rfl

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- **The two functorialities commute**, so the tensor product is a functor of two variables. -/
theorem tensorMapLeft_comp_tensorMapRight {P : CDGAModuleStructure A M}
    {P' : CDGAModuleStructure A M'} {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'}
    (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q') :
    (tensorMapLeft φ Q').comp (tensorMapRight P ψ)
      = (tensorMapRight P' ψ).comp (tensorMapLeft φ Q) := by
  refine CDGAModuleHom.hom_ext fun n f => ?_
  funext p
  show TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id
      (TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (f p))
    = TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2)
      (TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id (f p))
  have hcomm : (TensorProduct.map (φ.mapₗ p.1.1) (LinearMap.id : N' p.1.2 →ₗ[R] N' p.1.2)).comp
        (TensorProduct.map (LinearMap.id : M p.1.1 →ₗ[R] M p.1.1) (ψ.mapₗ p.1.2))
      = (TensorProduct.map (LinearMap.id : M' p.1.1 →ₗ[R] M' p.1.1) (ψ.mapₗ p.1.2)).comp
        (TensorProduct.map (φ.mapₗ p.1.1) (LinearMap.id : N p.1.2 →ₗ[R] N p.1.2)) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_id]
  exact congrArg (fun L : TensorProduct R (M p.1.1) (N p.1.2) →ₗ[R]
    TensorProduct R (M' p.1.1) (N' p.1.2) => L (f p)) hcomm

/-- **The tensor product of two morphisms.** -/
def tensorMap {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
    {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'}
    (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q') :
    CDGAModuleHom (tensorModule P Q) (tensorModule P' Q') :=
  (tensorMapLeft φ Q').comp (tensorMapRight P ψ)

@[simp] theorem tensorMap_toFun {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
    {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'}
    (φ : CDGAModuleHom P P') (ψ : CDGAModuleHom Q Q') (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorMap φ ψ).toFun n f p
      = TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) (f p) := by
  show TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id
      (TensorProduct.map LinearMap.id (ψ.mapₗ p.1.2) (f p)) = _
  have hcomp : (TensorProduct.map (φ.mapₗ p.1.1) (LinearMap.id : N' p.1.2 →ₗ[R] N' p.1.2)).comp
        (TensorProduct.map (LinearMap.id : M p.1.1 →ₗ[R] M p.1.1) (ψ.mapₗ p.1.2))
      = TensorProduct.map (φ.mapₗ p.1.1) (ψ.mapₗ p.1.2) := by
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  exact congrArg (fun L : TensorProduct R (M p.1.1) (N p.1.2) →ₗ[R]
    TensorProduct R (M' p.1.1) (N' p.1.2) => L (f p)) hcomp

end RightFunctoriality

section LeftNaturality

variable {C : ℕ → Type w} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- A map applied in the left factor commutes with a family applied in the right factor. -/
theorem tensorMap_left_sigma_comm {a a' b : ℕ} (θ : M a →ₗ[R] M' a')
    (σ : ∀ n, C n →ₗ[R] N (n + 1)) :
    (TensorProduct.map θ (LinearMap.id : N (b + 1) →ₗ[R] N (b + 1))).comp
        (TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) (σ b))
      = (TensorProduct.map (LinearMap.id : M' a' →ₗ[R] M' a') (σ b)).comp
        (TensorProduct.map θ (LinearMap.id : C b →ₗ[R] C b)) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id, LinearMap.id_comp]

@[simp] theorem tensorMapLeft_toFun {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
    (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorMapLeft φ Q).toFun n f p
      = TensorProduct.map (φ.mapₗ p.1.1) LinearMap.id (f p) := rfl

/-- **Tensoring in the left variable intertwines a right-factor family with itself.**  With the
family a twisting cochain this is the compatibility that makes the tensored comparison a comparison
of cell attachments. -/
theorem tensorMapLeft_tensorSigmaR {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}
    (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) (Qc : CDGAModuleStructure A C)
    (σ : ∀ n, C n →ₗ[R] N (n + 1)) (n : ℕ) (v : TensorCarrier (R := R) M C n) :
    (tensorMapLeft φ Q).toFun (n + 1) (tensorSigmaR (M := M) σ n v)
      = tensorSigmaR (M := M') σ n ((tensorMapLeft φ Qc).toFun n v) := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  rw [tensorMapLeft_toFun]
  cases b with
  | zero => rw [tensorSigmaR_zero, map_zero, tensorSigmaR_zero]
  | succ b' =>
      rw [tensorSigmaR_succ, map_smul, tensorSigmaR_succ, tensorMapLeft_toFun]
      have hcomm := congrArg
        (fun L : TensorProduct R (M a) (C b') →ₗ[R] TensorProduct R (M' a) (N (b' + 1))
          => L (v ⟨(a, b'), by omega⟩)) (tensorMap_left_sigma_comm (M' := M') (φ.mapₗ a) σ)
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm]

/-- The compatibility of the tensored comparison with the tensored twists. -/
theorem tensorTwistR_compat (P : CDGAModuleStructure A M) (P' : CDGAModuleStructure A M')
    {Q : CDGAModuleStructure A N} {Qc : CDGAModuleStructure A C} (φ : CDGAModuleHom P P')
    (t : CDGATwist Q Qc) (n : ℕ) (v : TensorCarrier (R := R) M C n) :
    (tensorMapLeft φ Q).toFun (n + 1) ((tensorTwistR P t).τ n v)
      = (tensorTwistR P' t).τ n ((tensorMapLeft φ Qc).toFun n v) :=
  tensorMapLeft_tensorSigmaR φ Q Qc (fun k => t.τₗ k) n v

@[simp] theorem tensorProdRightHom_toFun (P : CDGAModuleStructure A M)
    (Q : CDGAModuleStructure A N) (Qc : CDGAModuleStructure A C) (t : CDGATwist Q Qc) (n : ℕ)
    (f : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    (tensorProdRightHom P Q Qc t).toFun n f
      = tensorProdRight (R := R) (M := M) (N := N) (C := C) n f := rfl

end LeftNaturality

end GaloisForLFunctions.HTGeometry
