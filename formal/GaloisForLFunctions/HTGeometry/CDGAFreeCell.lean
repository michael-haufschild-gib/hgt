import GaloisForLFunctions.HTGeometry.CDGAModule
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The free graded module on a module placed in a single degree

The free module on a plain module `V` in degree `k` over a graded algebra `X` has, in degree `n`,
the tensor product `X^a ⊗ V` where `a + k = n` — and nothing when there is no such `a`.  Indexing it
by the subtype `{a // a + k = n}` rather than by `X (n - k)` is what makes this workable: truncated
subtraction on `ℕ` would force the degrees below `k` into a dependent `if`, whose two branches have
different types, and the additive structure would then have to be transported by hand.  Over the
subtype the index set is a subsingleton, so the dependent function type *is* the direct sum, and the
group and module structures are the ones `Pi` already carries.

The differential is the differential of the algebra on the left factor; `V` carries none.  It
squares to zero because the algebra's does, and the degree-`k` piece has nothing below it to
differentiate into.

* `HTGeometry.FreeCellCarrier` : the underlying graded module.
* `HTGeometry.freeCellD` : its differential, with `freeCellD_d` its square.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {V : Type w} [AddCommGroup V] [Module R V]

/-- The underlying graded module of the free module on `V` placed in degree `k`. -/
def FreeCellCarrier (X : ℕ → Type v) [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
    (V : Type w) [AddCommGroup V] [Module R V] (k n : ℕ) : Type (max v w) :=
  ∀ p : {a : ℕ // a + k = n}, TensorProduct R (X p.1) V

instance (k n : ℕ) : AddCommGroup (FreeCellCarrier (R := R) X V k n) :=
  inferInstanceAs (AddCommGroup (∀ p : {a : ℕ // a + k = n}, TensorProduct R (X p.1) V))

instance (k n : ℕ) : Module R (FreeCellCarrier (R := R) X V k n) :=
  inferInstanceAs (Module R (∀ p : {a : ℕ // a + k = n}, TensorProduct R (X p.1) V))

@[simp] theorem freeCellCarrier_add_apply {k n : ℕ} (f g : FreeCellCarrier (R := R) X V k n)
    (p : {a : ℕ // a + k = n}) : (f + g) p = f p + g p := rfl

@[simp] theorem freeCellCarrier_smul_apply {k n : ℕ} (c : R)
    (f : FreeCellCarrier (R := R) X V k n) (p : {a : ℕ // a + k = n}) : (c • f) p = c • f p := rfl

@[simp] theorem freeCellCarrier_zero_apply {k n : ℕ} (p : {a : ℕ // a + k = n}) :
    (0 : FreeCellCarrier (R := R) X V k n) p = 0 := rfl

/-- The differential of the free module: the differential of the algebra on the left factor.  There
is nothing below the bottom degree to differentiate into, which is the first branch. -/
def freeCellD (A : CDGAStructure R X) (k n : ℕ) (f : FreeCellCarrier (R := R) X V k n) :
    FreeCellCarrier (R := R) X V k (n + 1) :=
  fun p => match p with
    | ⟨0, _⟩ => 0
    | ⟨a + 1, h⟩ => TensorProduct.map (A.dₗ a) LinearMap.id (f ⟨a, by omega⟩)

@[simp] theorem freeCellD_zero (A : CDGAStructure R X) (k n : ℕ)
    (f : FreeCellCarrier (R := R) X V k n) (h : 0 + k = n + 1) :
    freeCellD A k n f ⟨0, h⟩ = 0 := rfl

@[simp] theorem freeCellD_succ (A : CDGAStructure R X) (k n a : ℕ)
    (f : FreeCellCarrier (R := R) X V k n) (h : a + 1 + k = n + 1) :
    freeCellD A k n f ⟨a + 1, h⟩
      = TensorProduct.map (A.dₗ a) LinearMap.id (f ⟨a, by omega⟩) := rfl

theorem freeCellD_add (A : CDGAStructure R X) (k n : ℕ)
    (f g : FreeCellCarrier (R := R) X V k n) :
    freeCellD A k n (f + g) = freeCellD A k n f + freeCellD A k n g := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => rfl
  | succ b =>
      show TensorProduct.map (A.dₗ b) LinearMap.id ((f + g) ⟨b, by omega⟩) = _
      rw [freeCellCarrier_add_apply, map_add]
      rfl

theorem freeCellD_smul (A : CDGAStructure R X) (k n : ℕ) (c : R)
    (f : FreeCellCarrier (R := R) X V k n) :
    freeCellD A k n (c • f) = c • freeCellD A k n f := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => rfl
  | succ b =>
      show TensorProduct.map (A.dₗ b) LinearMap.id ((c • f) ⟨b, by omega⟩) = _
      rw [freeCellCarrier_smul_apply, map_smul]
      rfl

/-- The composite of two differentials of the algebra vanishes as a map of tensor products. -/
theorem tensorMap_d_comp_d (A : CDGAStructure R X) (b : ℕ) :
    (TensorProduct.map (A.dₗ (b + 1)) (LinearMap.id : V →ₗ[R] V)).comp
      (TensorProduct.map (A.dₗ b) (LinearMap.id : V →ₗ[R] V)) = 0 := by
  rw [← TensorProduct.map_comp]
  refine TensorProduct.ext' fun x v => ?_
  show TensorProduct.map ((A.dₗ (b + 1)).comp (A.dₗ b)) (LinearMap.id.comp LinearMap.id) (x ⊗ₜ v)
    = 0
  rw [TensorProduct.map_tmul]
  show A.d (b + 1) (A.d b x) ⊗ₜ v = 0
  rw [A.d_d b x, TensorProduct.zero_tmul]

/-- **The differential of the free module squares to zero.** -/
theorem freeCellD_d (A : CDGAStructure R X) (k n : ℕ) (f : FreeCellCarrier (R := R) X V k n) :
    freeCellD A k (n + 1) (freeCellD A k n f) = 0 := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => rfl
  | succ b =>
      cases b with
      | zero =>
          show TensorProduct.map (A.dₗ 0) LinearMap.id (freeCellD A k n f ⟨0, by omega⟩) = 0
          rw [freeCellD_zero, map_zero]
      | succ c =>
          show TensorProduct.map (A.dₗ (c + 1)) LinearMap.id
            (freeCellD A k n f ⟨c + 1, by omega⟩) = 0
          rw [freeCellD_succ]
          have := congrArg (fun L : TensorProduct R (X c) V →ₗ[R] TensorProduct R (X (c + 1 + 1)) V
            => L (f ⟨c, by omega⟩)) (tensorMap_d_comp_d (V := V) A c)
          simpa using this

/-- The action of the algebra on the free module: multiply on the left factor.  Below the shift the
source has no component, so the value is zero. -/
def freeCellAct (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : FreeCellCarrier (R := R) X V k n) : FreeCellCarrier (R := R) X V k m :=
  fun p =>
    match p with
    | ⟨a, ha⟩ =>
      if hb : b ≤ a then
        TensorProduct.map (A.mulₗ (show b + (a - b) = a by omega) x) LinearMap.id
          (f ⟨a - b, by omega⟩)
      else 0

theorem freeCellAct_of_le (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : FreeCellCarrier (R := R) X V k n) {a : ℕ} (ha : a + k = m) (hb : b ≤ a) :
    freeCellAct A k h x f ⟨a, ha⟩
      = TensorProduct.map (A.mulₗ (show b + (a - b) = a by omega) x) LinearMap.id
          (f ⟨a - b, by omega⟩) := dif_pos hb

theorem freeCellAct_of_lt (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : FreeCellCarrier (R := R) X V k n) {a : ℕ} (ha : a + k = m) (hb : ¬ b ≤ a) :
    freeCellAct A k h x f ⟨a, ha⟩ = 0 := dif_neg hb

/-- The action at a component that visibly decomposes: no subtraction survives. -/
theorem freeCellAct_apply_add (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (x : X b) (f : FreeCellCarrier (R := R) X V k n) {i : ℕ} (hi : i + k = n)
    (hbi : b + i + k = m) :
    freeCellAct A k h x f ⟨b + i, hbi⟩
      = TensorProduct.map (A.mulₗ (rfl : b + i = b + i) x) LinearMap.id (f ⟨i, hi⟩) := by
  rw [freeCellAct_of_le A k h x f hbi (Nat.le_add_right b i)]
  have gen : ∀ (j : ℕ) (hj : j + k = n) (e : b + j = b + i),
      TensorProduct.map (A.mulₗ e x) LinearMap.id (f ⟨j, hj⟩)
        = TensorProduct.map (A.mulₗ (rfl : b + i = b + i) x) LinearMap.id (f ⟨i, hi⟩) := by
    intro j hj e
    obtain rfl : j = i := by omega
    rfl
  exact gen (b + i - b) (by omega) (by omega)

/-- The action at a component with an arbitrary witness of the decomposition. -/
theorem freeCellAct_apply_eq (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (x : X b) (f : FreeCellCarrier (R := R) X V k n) {i c : ℕ} (e : b + i = c) (hi : i + k = n)
    (hc : c + k = m) :
    freeCellAct A k h x f ⟨c, hc⟩
      = TensorProduct.map (A.mulₗ e x) LinearMap.id (f ⟨i, hi⟩) := by
  subst e
  exact freeCellAct_apply_add A k h x f hi hc

theorem freeCellAct_add_left (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (x x' : X b) (f : FreeCellCarrier (R := R) X V k n) :
    freeCellAct A k h (x + x') f = freeCellAct A k h x f + freeCellAct A k h x' f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [freeCellAct_of_le A k h _ f ha hb, freeCellCarrier_add_apply,
      freeCellAct_of_le A k h x f ha hb, freeCellAct_of_le A k h x' f ha hb, map_add,
      TensorProduct.map_add_left]
    rfl
  · rw [freeCellAct_of_lt A k h _ f ha hb, freeCellCarrier_add_apply,
      freeCellAct_of_lt A k h x f ha hb, freeCellAct_of_lt A k h x' f ha hb, add_zero]

theorem freeCellAct_add_right (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (x : X b) (f g : FreeCellCarrier (R := R) X V k n) :
    freeCellAct A k h x (f + g) = freeCellAct A k h x f + freeCellAct A k h x g := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [freeCellCarrier_add_apply, freeCellAct_of_le A k h x _ ha hb,
      freeCellAct_of_le A k h x f ha hb, freeCellAct_of_le A k h x g ha hb,
      freeCellCarrier_add_apply, map_add]
  · rw [freeCellAct_of_lt A k h x _ ha hb, freeCellCarrier_add_apply,
      freeCellAct_of_lt A k h x f ha hb, freeCellAct_of_lt A k h x g ha hb, add_zero]

theorem freeCellAct_smul_left (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (c : R) (x : X b) (f : FreeCellCarrier (R := R) X V k n) :
    freeCellAct A k h (c • x) f = c • freeCellAct A k h x f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [freeCellAct_of_le A k h _ f ha hb, freeCellCarrier_smul_apply,
      freeCellAct_of_le A k h x f ha hb, map_smul, TensorProduct.map_smul_left]
    rfl
  · rw [freeCellAct_of_lt A k h _ f ha hb, freeCellCarrier_smul_apply,
      freeCellAct_of_lt A k h x f ha hb, smul_zero]

theorem freeCellAct_smul_right (A : CDGAStructure R X) (k : ℕ) {b n m : ℕ} (h : b + n = m)
    (c : R) (x : X b) (f : FreeCellCarrier (R := R) X V k n) :
    freeCellAct A k h x (c • f) = c • freeCellAct A k h x f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [freeCellCarrier_smul_apply, freeCellAct_of_le A k h x _ ha hb,
      freeCellAct_of_le A k h x f ha hb, freeCellCarrier_smul_apply, map_smul]
  · rw [freeCellAct_of_lt A k h x _ ha hb, freeCellCarrier_smul_apply,
      freeCellAct_of_lt A k h x f ha hb, smul_zero]

/-- **The action of the algebra on the free module is associative.** -/
theorem freeCellAct_assoc (A : CDGAStructure R X) (k : ℕ) {a b k' m' m'' n : ℕ}
    (h₁ : a + b = m') (h₂ : m' + k' = n) (h₃ : b + k' = m'') (h₄ : a + m'' = n)
    (x : X a) (y : X b) (f : FreeCellCarrier (R := R) X V k k') :
    freeCellAct A k h₂ (A.mul h₁ x y) f
      = freeCellAct A k h₄ x (freeCellAct A k h₃ y f) := by
  funext p
  obtain ⟨c, hc⟩ := p
  by_cases hm : m' ≤ c
  · obtain ⟨i, hi⟩ : ∃ i, m' + i = c := Nat.le.dest hm
    have hik : i + k = k' := by omega
    have hbi : b + i + k = m'' := by omega
    rw [freeCellAct_apply_eq A k h₂ _ f hi hik hc,
      freeCellAct_apply_eq A k h₄ x _ (show a + (b + i) = c by omega) hbi hc,
      freeCellAct_apply_eq A k h₃ y f (show b + i = b + i from rfl) hik hbi]
    have hcomp : (A.mulₗ hi (A.mul h₁ x y) : X i →ₗ[R] X c)
        = (A.mulₗ (show a + (b + i) = c by omega) x).comp
          (A.mulₗ (show b + i = b + i from rfl) y) :=
      LinearMap.ext fun z =>
        A.mul_assoc h₁ hi rfl (show a + (b + i) = c by omega) x y z
    have hmaps : TensorProduct.map (A.mulₗ hi (A.mul h₁ x y)) (LinearMap.id : V →ₗ[R] V)
        = (TensorProduct.map (A.mulₗ (show a + (b + i) = c by omega) x)
            (LinearMap.id : V →ₗ[R] V)).comp
          (TensorProduct.map (A.mulₗ (show b + i = b + i from rfl) y)
            (LinearMap.id : V →ₗ[R] V)) := by
      rw [← TensorProduct.map_comp, hcomp, LinearMap.id_comp]
    exact congrArg (fun L : TensorProduct R (X i) V →ₗ[R] TensorProduct R (X c) V =>
      L (f ⟨i, hik⟩)) hmaps
  · have hL : freeCellAct A k h₂ (A.mul h₁ x y) f ⟨c, hc⟩ = 0 :=
      freeCellAct_of_lt A k h₂ _ f hc (by omega)
    rw [hL]
    by_cases ha : a ≤ c
    · obtain ⟨j, hj⟩ : ∃ j, a + j = c := Nat.le.dest ha
      have hjk : j + k = m'' := by omega
      rw [freeCellAct_apply_eq A k h₄ x _ hj hjk hc,
        freeCellAct_of_lt A k h₃ y f hjk (by omega), map_zero]
    · rw [freeCellAct_of_lt A k h₄ x _ hc (by omega)]

/-- **The Leibniz rule for the free module.** -/
theorem freeCellD_act (A : CDGAStructure R X) (k : ℕ) {a b n : ℕ} (h : a + b = n) (x : X a)
    (f : FreeCellCarrier (R := R) X V k b) :
    freeCellD A k n (freeCellAct A k h x f)
      = freeCellAct A k (show a + 1 + b = n + 1 by omega) (A.d a x) f
        + ((-1 : R)) ^ a • freeCellAct A k (show a + (b + 1) = n + 1 by omega) x
            (freeCellD A k b f) := by
  funext p
  obtain ⟨c, hc⟩ := p
  cases c with
  | zero =>
      have h1 : freeCellAct A k (show a + 1 + b = n + 1 by omega) (A.d a x) f ⟨0, hc⟩ = 0 :=
        freeCellAct_of_lt _ _ _ _ _ hc (by omega)
      have h2 : freeCellAct A k (show a + (b + 1) = n + 1 by omega) x
          (freeCellD A k b f) ⟨0, hc⟩ = 0 := by
        by_cases ha : a ≤ 0
        · have ha0 : a = 0 := by omega
          subst ha0
          rw [freeCellAct_apply_eq A k _ x _ (show 0 + 0 = 0 by omega) (by omega) hc,
            freeCellD_zero, map_zero]
        · exact freeCellAct_of_lt _ _ _ _ _ hc (by omega)
      rw [freeCellCarrier_add_apply, freeCellCarrier_smul_apply, h1, h2, smul_zero, add_zero,
        freeCellD_zero]
  | succ e =>
      by_cases hae : a ≤ e
      · obtain ⟨i, hi⟩ : ∃ i, a + i = e := Nat.le.dest hae
        have hik : i + k = b := by omega
        have hek : e + k = n := by omega
        rw [freeCellCarrier_add_apply, freeCellCarrier_smul_apply,
          freeCellD_succ A k n e (freeCellAct A k h x f) hc,
          freeCellAct_apply_eq A k h x f hi hik hek,
          freeCellAct_apply_eq A k (show a + 1 + b = n + 1 by omega) (A.d a x) f
            (show a + 1 + i = e + 1 by omega) hik hc,
          freeCellAct_apply_eq A k (show a + (b + 1) = n + 1 by omega) x (freeCellD A k b f)
            (show a + (i + 1) = e + 1 by omega) (by omega) hc,
          freeCellD_succ A k b i f (by omega)]
        have hpt : (A.dₗ e).comp (A.mulₗ hi x) =
            A.mulₗ (show a + 1 + i = e + 1 by omega) (A.d a x)
              + ((-1 : R)) ^ a • (A.mulₗ (show a + (i + 1) = e + 1 by omega) x).comp
                  (A.dₗ i) := by
          refine LinearMap.ext fun z => ?_
          exact A.d_mul hi x z
        have hmaps : (TensorProduct.map (A.dₗ e) (LinearMap.id : V →ₗ[R] V)).comp
              (TensorProduct.map (A.mulₗ hi x) (LinearMap.id : V →ₗ[R] V))
            = TensorProduct.map (A.mulₗ (show a + 1 + i = e + 1 by omega) (A.d a x))
                (LinearMap.id : V →ₗ[R] V)
              + ((-1 : R)) ^ a • (TensorProduct.map
                  (A.mulₗ (show a + (i + 1) = e + 1 by omega) x) (LinearMap.id : V →ₗ[R] V)).comp
                  (TensorProduct.map (A.dₗ i) (LinearMap.id : V →ₗ[R] V)) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hpt,
            TensorProduct.map_add_left, TensorProduct.map_smul_left, LinearMap.id_comp]
        exact congrArg (fun L : TensorProduct R (X i) V →ₗ[R] TensorProduct R (X (e + 1)) V
          => L (f ⟨i, hik⟩)) hmaps
      · have hL : freeCellAct A k h x f ⟨e, by omega⟩ = 0 :=
          freeCellAct_of_lt _ _ _ _ _ (by omega) (by omega)
        have h1 : freeCellAct A k (show a + 1 + b = n + 1 by omega) (A.d a x) f ⟨e + 1, hc⟩ = 0 :=
          freeCellAct_of_lt _ _ _ _ _ hc (by omega)
        have h2 : freeCellAct A k (show a + (b + 1) = n + 1 by omega) x
            (freeCellD A k b f) ⟨e + 1, hc⟩ = 0 := by
          by_cases ha : a ≤ e + 1
          · rw [freeCellAct_apply_eq A k _ x _ (show a + 0 = e + 1 by omega) (by omega) hc,
              freeCellD_zero, map_zero]
          · exact freeCellAct_of_lt _ _ _ _ _ hc (by omega)
        rw [freeCellCarrier_add_apply, freeCellCarrier_smul_apply, h1, h2, smul_zero, add_zero,
          freeCellD_succ A k n e (freeCellAct A k h x f) hc, hL, map_zero]

/-- **The free differential graded module on a module placed in a single degree.** -/
def freeCellModule (A : CDGAStructure R X) (V : Type w) [AddCommGroup V] [Module R V] (k : ℕ) :
    CDGAModuleStructure A (FreeCellCarrier (R := R) X V k) where
  act h x f := freeCellAct A k h x f
  d n f := freeCellD A k n f
  act_add_left h x x' f := freeCellAct_add_left A k h x x' f
  act_add_right h x f g := freeCellAct_add_right A k h x f g
  act_smul_left h c x f := freeCellAct_smul_left A k h c x f
  act_smul_right h c x f := freeCellAct_smul_right A k h c x f
  act_assoc h₁ h₂ h₃ h₄ x y f := freeCellAct_assoc A k h₁ h₂ h₃ h₄ x y f
  d_add n f g := freeCellD_add A k n f g
  d_smul n c f := freeCellD_smul A k n c f
  d_d n f := freeCellD_d A k n f
  d_act h x f := freeCellD_act A k h x f

@[simp] theorem freeCellModule_d (A : CDGAStructure R X) (V : Type w) [AddCommGroup V]
    [Module R V] (k n : ℕ) (f : FreeCellCarrier (R := R) X V k n) :
    (freeCellModule A V k).d n f = freeCellD A k n f := rfl

@[simp] theorem freeCellModule_act (A : CDGAStructure R X) (V : Type w) [AddCommGroup V]
    [Module R V] (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : FreeCellCarrier (R := R) X V k n) :
    (freeCellModule A V k).act h x f = freeCellAct A k h x f := rfl

end GaloisForLFunctions.HTGeometry
