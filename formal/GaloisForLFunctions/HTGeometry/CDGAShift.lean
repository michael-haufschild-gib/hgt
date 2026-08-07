import GaloisForLFunctions.HTGeometry.CDGAFreeCell

/-!
# The degree shift of a differential graded module

Shifting a module up by `k` places its degree `a` in degree `a + k` and puts nothing below `k`.
Indexing the degree by the subtype `{a // a + k = n}` keeps truncated subtraction out of every
dependent position: the component below the shift is an empty product, which is what makes the
bottom of the complex trivial without a separate case in the carrier.

* `HTGeometry.ShiftCarrier`, `HTGeometry.shiftModule` : the shifted module.
* `HTGeometry.shiftMap` : the shift of a morphism.
* `HTGeometry.shiftEval` : above the shift the module is the original one.
* `HTGeometry.freeCellCarrier_eq_shift` : the free cell is the shift of the algebra tensored with
  the coefficient module.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- The underlying graded module of a degree shift. -/
def ShiftCarrier (M : ℕ → Type w) (k n : ℕ) : Type w := ∀ p : {a : ℕ // a + k = n}, M p.1

instance (k n : ℕ) : AddCommGroup (ShiftCarrier M k n) :=
  inferInstanceAs (AddCommGroup (∀ p : {a : ℕ // a + k = n}, M p.1))

instance (k n : ℕ) : Module R (ShiftCarrier M k n) :=
  inferInstanceAs (Module R (∀ p : {a : ℕ // a + k = n}, M p.1))

@[simp] theorem shiftCarrier_add_apply {k n : ℕ} (f g : ShiftCarrier M k n)
    (p : {a : ℕ // a + k = n}) : (f + g) p = f p + g p := rfl

@[simp] theorem shiftCarrier_smul_apply {k n : ℕ} (c : R) (f : ShiftCarrier M k n)
    (p : {a : ℕ // a + k = n}) : (c • f) p = c • f p := rfl

@[simp] theorem shiftCarrier_zero_apply {k n : ℕ} (p : {a : ℕ // a + k = n}) :
    (0 : ShiftCarrier M k n) p = 0 := rfl

section Structure

variable (P : CDGAModuleStructure A M)

/-- The differential of the shift.  There is nothing below the bottom degree, which is the first
branch. -/
def shiftD (k n : ℕ) (f : ShiftCarrier M k n) : ShiftCarrier M k (n + 1) :=
  fun p => match p with
    | ⟨0, _⟩ => 0
    | ⟨a + 1, h⟩ => P.d a (f ⟨a, by omega⟩)

@[simp] theorem shiftD_zero (k n : ℕ) (f : ShiftCarrier M k n) (h : 0 + k = n + 1) :
    shiftD P k n f ⟨0, h⟩ = 0 := rfl

@[simp] theorem shiftD_succ (k n a : ℕ) (f : ShiftCarrier M k n) (h : a + 1 + k = n + 1) :
    shiftD P k n f ⟨a + 1, h⟩ = P.d a (f ⟨a, by omega⟩) := rfl

theorem shiftD_add (k n : ℕ) (f g : ShiftCarrier M k n) :
    shiftD P k n (f + g) = shiftD P k n f + shiftD P k n g := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => exact (add_zero (0 : M 0)).symm
  | succ b =>
      show P.d b ((f + g) ⟨b, by omega⟩) = _
      rw [shiftCarrier_add_apply, P.d_add]
      rfl

theorem shiftD_smul (k n : ℕ) (c : R) (f : ShiftCarrier M k n) :
    shiftD P k n (c • f) = c • shiftD P k n f := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => exact (smul_zero c).symm
  | succ b =>
      show P.d b ((c • f) ⟨b, by omega⟩) = _
      rw [shiftCarrier_smul_apply, P.d_smul]
      rfl

/-- **The differential of the shift squares to zero.** -/
theorem shiftD_d (k n : ℕ) (f : ShiftCarrier M k n) :
    shiftD P k (n + 1) (shiftD P k n f) = 0 := by
  funext p
  obtain ⟨a, h⟩ := p
  cases a with
  | zero => rfl
  | succ b =>
      cases b with
      | zero =>
          show P.d 0 (shiftD P k n f ⟨0, by omega⟩) = 0
          rw [shiftD_zero]
          exact (P.dₗ 0).map_zero
      | succ c =>
          show P.d (c + 1) (shiftD P k n f ⟨c + 1, by omega⟩) = 0
          rw [shiftD_succ, P.d_d]

/-- The action of the algebra on the shift.  Below the shift the source has no component. -/
def shiftAct (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b) (f : ShiftCarrier M k n) :
    ShiftCarrier M k m :=
  fun p =>
    match p with
    | ⟨a, ha⟩ =>
      if hb : b ≤ a then P.act (show b + (a - b) = a by omega) x (f ⟨a - b, by omega⟩)
      else 0

theorem shiftAct_of_le (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b) (f : ShiftCarrier M k n)
    {a : ℕ} (ha : a + k = m) (hb : b ≤ a) :
    shiftAct P k h x f ⟨a, ha⟩
      = P.act (show b + (a - b) = a by omega) x (f ⟨a - b, by omega⟩) := dif_pos hb

theorem shiftAct_of_lt (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b) (f : ShiftCarrier M k n)
    {a : ℕ} (ha : a + k = m) (hb : ¬ b ≤ a) : shiftAct P k h x f ⟨a, ha⟩ = 0 := dif_neg hb

/-- The action at a component that visibly decomposes: no subtraction survives. -/
theorem shiftAct_apply_add (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : ShiftCarrier M k n) {i : ℕ} (hi : i + k = n) (hbi : b + i + k = m) :
    shiftAct P k h x f ⟨b + i, hbi⟩ = P.act (rfl : b + i = b + i) x (f ⟨i, hi⟩) := by
  rw [shiftAct_of_le P k h x f hbi (Nat.le_add_right b i)]
  have gen : ∀ (j : ℕ) (hj : j + k = n) (e : b + j = b + i),
      P.act e x (f ⟨j, hj⟩) = P.act (rfl : b + i = b + i) x (f ⟨i, hi⟩) := by
    intro j hj e
    obtain rfl : j = i := by omega
    rfl
  exact gen (b + i - b) (by omega) (by omega)

/-- The action at a component with an arbitrary witness of the decomposition. -/
theorem shiftAct_apply_eq (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : ShiftCarrier M k n) {i c : ℕ} (e : b + i = c) (hi : i + k = n) (hc : c + k = m) :
    shiftAct P k h x f ⟨c, hc⟩ = P.act e x (f ⟨i, hi⟩) := by
  subst e
  exact shiftAct_apply_add P k h x f hi hc

theorem shiftAct_add_left (k : ℕ) {b n m : ℕ} (h : b + n = m) (x x' : X b)
    (f : ShiftCarrier M k n) :
    shiftAct P k h (x + x') f = shiftAct P k h x f + shiftAct P k h x' f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [shiftAct_of_le P k h _ f ha hb, shiftCarrier_add_apply, shiftAct_of_le P k h x f ha hb,
      shiftAct_of_le P k h x' f ha hb, P.act_add_left]
  · rw [shiftAct_of_lt P k h _ f ha hb, shiftCarrier_add_apply, shiftAct_of_lt P k h x f ha hb,
      shiftAct_of_lt P k h x' f ha hb, add_zero]

theorem shiftAct_add_right (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f g : ShiftCarrier M k n) :
    shiftAct P k h x (f + g) = shiftAct P k h x f + shiftAct P k h x g := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [shiftCarrier_add_apply, shiftAct_of_le P k h x _ ha hb, shiftAct_of_le P k h x f ha hb,
      shiftAct_of_le P k h x g ha hb, shiftCarrier_add_apply, P.act_add_right]
  · rw [shiftAct_of_lt P k h x _ ha hb, shiftCarrier_add_apply, shiftAct_of_lt P k h x f ha hb,
      shiftAct_of_lt P k h x g ha hb, add_zero]

theorem shiftAct_smul_left (k : ℕ) {b n m : ℕ} (h : b + n = m) (c : R) (x : X b)
    (f : ShiftCarrier M k n) :
    shiftAct P k h (c • x) f = c • shiftAct P k h x f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [shiftAct_of_le P k h _ f ha hb, shiftCarrier_smul_apply, shiftAct_of_le P k h x f ha hb,
      P.act_smul_left]
  · rw [shiftAct_of_lt P k h _ f ha hb, shiftCarrier_smul_apply, shiftAct_of_lt P k h x f ha hb,
      smul_zero]

theorem shiftAct_smul_right (k : ℕ) {b n m : ℕ} (h : b + n = m) (c : R) (x : X b)
    (f : ShiftCarrier M k n) :
    shiftAct P k h x (c • f) = c • shiftAct P k h x f := by
  funext p
  obtain ⟨a, ha⟩ := p
  by_cases hb : b ≤ a
  · rw [shiftCarrier_smul_apply, shiftAct_of_le P k h x _ ha hb, shiftAct_of_le P k h x f ha hb,
      shiftCarrier_smul_apply, P.act_smul_right]
  · rw [shiftAct_of_lt P k h x _ ha hb, shiftCarrier_smul_apply, shiftAct_of_lt P k h x f ha hb,
      smul_zero]

/-- **The action on the shift is associative.** -/
theorem shiftAct_assoc (k : ℕ) {a b k' m' m'' n : ℕ} (h₁ : a + b = m') (h₂ : m' + k' = n)
    (h₃ : b + k' = m'') (h₄ : a + m'' = n) (x : X a) (y : X b) (f : ShiftCarrier M k k') :
    shiftAct P k h₂ (A.mul h₁ x y) f = shiftAct P k h₄ x (shiftAct P k h₃ y f) := by
  funext p
  obtain ⟨c, hc⟩ := p
  by_cases hm : m' ≤ c
  · obtain ⟨i, hi⟩ : ∃ i, m' + i = c := Nat.le.dest hm
    have hik : i + k = k' := by omega
    have hbi : b + i + k = m'' := by omega
    rw [shiftAct_apply_eq P k h₂ _ f hi hik hc,
      shiftAct_apply_eq P k h₄ x _ (show a + (b + i) = c by omega) hbi hc,
      shiftAct_apply_eq P k h₃ y f (show b + i = b + i from rfl) hik hbi]
    exact P.act_assoc h₁ hi rfl (show a + (b + i) = c by omega) x y (f ⟨i, hik⟩)
  · rw [shiftAct_of_lt P k h₂ _ f hc (by omega)]
    by_cases ha : a ≤ c
    · obtain ⟨j, hj⟩ : ∃ j, a + j = c := Nat.le.dest ha
      have hjk : j + k = m'' := by omega
      rw [shiftAct_apply_eq P k h₄ x _ hj hjk hc, shiftAct_of_lt P k h₃ y f hjk (by omega)]
      have hz : P.act hj x (0 : M j) = 0 := (P.actₗ hj x).map_zero
      rw [hz]
    · rw [shiftAct_of_lt P k h₄ x _ hc (by omega)]

/-- **The Leibniz rule for the shift.** -/
theorem shiftD_act (k : ℕ) {a b n : ℕ} (h : a + b = n) (x : X a) (f : ShiftCarrier M k b) :
    shiftD P k n (shiftAct P k h x f)
      = shiftAct P k (show a + 1 + b = n + 1 by omega) (A.d a x) f
        + ((-1 : R)) ^ a • shiftAct P k (show a + (b + 1) = n + 1 by omega) x
            (shiftD P k b f) := by
  funext p
  obtain ⟨c, hc⟩ := p
  cases c with
  | zero =>
      have h1 : shiftAct P k (show a + 1 + b = n + 1 by omega) (A.d a x) f ⟨0, hc⟩ = 0 :=
        shiftAct_of_lt _ _ _ _ _ hc (by omega)
      have h2 : shiftAct P k (show a + (b + 1) = n + 1 by omega) x (shiftD P k b f) ⟨0, hc⟩
          = 0 := by
        by_cases ha : a ≤ 0
        · have ha0 : a = 0 := by omega
          subst ha0
          rw [shiftAct_apply_eq P k _ x _ (show 0 + 0 = 0 by omega) (by omega) hc, shiftD_zero]
          exact (P.actₗ (show 0 + 0 = 0 by omega) x).map_zero
        · exact shiftAct_of_lt _ _ _ _ _ hc (by omega)
      rw [shiftCarrier_add_apply, shiftCarrier_smul_apply, h1, h2, smul_zero, add_zero,
        shiftD_zero]
  | succ e =>
      by_cases hae : a ≤ e
      · obtain ⟨i, hi⟩ : ∃ i, a + i = e := Nat.le.dest hae
        have hik : i + k = b := by omega
        have hek : e + k = n := by omega
        rw [shiftCarrier_add_apply, shiftCarrier_smul_apply,
          shiftD_succ P k n e (shiftAct P k h x f) hc, shiftAct_apply_eq P k h x f hi hik hek,
          shiftAct_apply_eq P k (show a + 1 + b = n + 1 by omega) (A.d a x) f
            (show a + 1 + i = e + 1 by omega) hik hc,
          shiftAct_apply_eq P k (show a + (b + 1) = n + 1 by omega) x (shiftD P k b f)
            (show a + (i + 1) = e + 1 by omega) (by omega) hc,
          shiftD_succ P k b i f (by omega)]
        exact P.d_act hi x (f ⟨i, hik⟩)
      · have hL : shiftAct P k h x f ⟨e, by omega⟩ = 0 :=
          shiftAct_of_lt _ _ _ _ _ (by omega) (by omega)
        have h1 : shiftAct P k (show a + 1 + b = n + 1 by omega) (A.d a x) f ⟨e + 1, hc⟩ = 0 :=
          shiftAct_of_lt _ _ _ _ _ hc (by omega)
        have h2 : shiftAct P k (show a + (b + 1) = n + 1 by omega) x (shiftD P k b f)
            ⟨e + 1, hc⟩ = 0 := by
          by_cases ha : a ≤ e + 1
          · rw [shiftAct_apply_eq P k _ x _ (show a + 0 = e + 1 by omega) (by omega) hc,
              shiftD_zero]
            exact (P.actₗ (show a + 0 = e + 1 by omega) x).map_zero
          · exact shiftAct_of_lt _ _ _ _ _ hc (by omega)
        rw [shiftCarrier_add_apply, shiftCarrier_smul_apply, h1, h2, smul_zero, add_zero,
          shiftD_succ P k n e (shiftAct P k h x f) hc, hL]
        exact (P.dₗ e).map_zero

/-- **The degree shift of a differential graded module.** -/
def shiftModule (k : ℕ) : CDGAModuleStructure A (ShiftCarrier M k) where
  act h x f := shiftAct P k h x f
  d n f := shiftD P k n f
  act_add_left h x x' f := shiftAct_add_left P k h x x' f
  act_add_right h x f g := shiftAct_add_right P k h x f g
  act_smul_left h c x f := shiftAct_smul_left P k h c x f
  act_smul_right h c x f := shiftAct_smul_right P k h c x f
  act_assoc h₁ h₂ h₃ h₄ x y f := shiftAct_assoc P k h₁ h₂ h₃ h₄ x y f
  d_add n f g := shiftD_add P k n f g
  d_smul n c f := shiftD_smul P k n c f
  d_d n f := shiftD_d P k n f
  d_act h x f := shiftD_act P k h x f

@[simp] theorem shiftModule_d (k n : ℕ) (f : ShiftCarrier M k n) :
    (shiftModule P k).d n f = shiftD P k n f := rfl

@[simp] theorem shiftModule_act (k : ℕ) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : ShiftCarrier M k n) : (shiftModule P k).act h x f = shiftAct P k h x f := rfl

end Structure

section Index

/-- Above the shift the index of a degree is unique. -/
instance shiftIndexUnique (k j : ℕ) : Unique {a : ℕ // a + k = j + k} where
  default := ⟨j, rfl⟩
  uniq p := Subtype.ext (by
    have hp := p.2
    show p.1 = j
    omega)

/-- Below the shift there is no index at all, so the component is trivial. -/
theorem shiftIndex_isEmpty {k n : ℕ} (h : n < k) : IsEmpty {a : ℕ // a + k = n} :=
  ⟨fun p => absurd p.2 (by omega)⟩

/-- Below the shift the module is trivial. -/
theorem shiftCarrier_subsingleton {k n : ℕ} (h : n < k) : Subsingleton (ShiftCarrier M k n) := by
  refine ⟨fun f g => funext fun p => ?_⟩
  exact absurd p.2 (by omega)

/-- **Above the shift the module is the original one**, read off at the unique index. -/
def shiftEval (k j : ℕ) : ShiftCarrier M k (j + k) ≃ₗ[R] M j where
  toFun := Equiv.piUnique (fun p : {a : ℕ // a + k = j + k} => M p.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := (Equiv.piUnique (fun p : {a : ℕ // a + k = j + k} => M p.1)).symm
  left_inv := (Equiv.piUnique (fun p : {a : ℕ // a + k = j + k} => M p.1)).left_inv
  right_inv := (Equiv.piUnique (fun p : {a : ℕ // a + k = j + k} => M p.1)).right_inv

@[simp] theorem shiftEval_apply (k j : ℕ) (f : ShiftCarrier M k (j + k)) :
    shiftEval (R := R) (M := M) k j f = f ⟨j, rfl⟩ := rfl

end Index

section FreeCell

variable {V : Type w} [AddCommGroup V] [Module R V]

/-- **The free cell is the shift of the algebra tensored with the coefficient module.** -/
theorem freeCellCarrier_eq_shift (k : ℕ) :
    FreeCellCarrier (R := R) X V k
      = ShiftCarrier (fun a => TensorProduct R (X a) V) k := rfl

end FreeCell

section Functoriality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- **The shift of a morphism.** -/
def shiftMap (φ : CDGAModuleHom P P') (k : ℕ) :
    CDGAModuleHom (shiftModule P k) (shiftModule P' k) where
  toFun n f := fun p => φ.toFun p.1 (f p)
  map_add n f g := by
    funext p
    exact φ.map_add p.1 (f p) (g p)
  map_smul n c f := by
    funext p
    exact φ.map_smul p.1 c (f p)
  map_act := by
    intro bA nS mS h x f
    funext p
    obtain ⟨a, ha⟩ := p
    by_cases hb : bA ≤ a
    · rw [show (shiftModule P k).act h x f = shiftAct P k h x f from rfl,
        shiftAct_of_le P k h x f ha hb,
        show (shiftModule P' k).act h x (fun q => φ.toFun q.1 (f q))
          = shiftAct P' k h x (fun q => φ.toFun q.1 (f q)) from rfl,
        shiftAct_of_le P' k h x _ ha hb]
      exact φ.map_act (show bA + (a - bA) = a by omega) x (f ⟨a - bA, by omega⟩)
    · rw [show (shiftModule P k).act h x f = shiftAct P k h x f from rfl,
        shiftAct_of_lt P k h x f ha hb,
        show (shiftModule P' k).act h x (fun q => φ.toFun q.1 (f q))
          = shiftAct P' k h x (fun q => φ.toFun q.1 (f q)) from rfl,
        shiftAct_of_lt P' k h x _ ha hb]
      exact (φ.mapₗ a).map_zero
  map_d n f := by
    funext p
    obtain ⟨a, ha⟩ := p
    cases a with
    | zero =>
        rw [show (shiftModule P k).d n f = shiftD P k n f from rfl, shiftD_zero,
          show (shiftModule P' k).d n (fun q => φ.toFun q.1 (f q))
            = shiftD P' k n (fun q => φ.toFun q.1 (f q)) from rfl, shiftD_zero]
        exact (φ.mapₗ 0).map_zero
    | succ b =>
        rw [show (shiftModule P k).d n f = shiftD P k n f from rfl, shiftD_succ,
          show (shiftModule P' k).d n (fun q => φ.toFun q.1 (f q))
            = shiftD P' k n (fun q => φ.toFun q.1 (f q)) from rfl, shiftD_succ]
        exact φ.map_d b (f ⟨b, by omega⟩)

@[simp] theorem shiftMap_toFun (φ : CDGAModuleHom P P') (k n : ℕ) (f : ShiftCarrier M k n)
    (p : {a : ℕ // a + k = n}) : (shiftMap φ k).toFun n f p = φ.toFun p.1 (f p) := rfl

end Functoriality

end GaloisForLFunctions.HTGeometry
