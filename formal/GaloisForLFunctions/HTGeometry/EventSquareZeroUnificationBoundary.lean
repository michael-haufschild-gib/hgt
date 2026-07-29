import GaloisForLFunctions.HTGeometry.EventSecondOrderSoldering

/-!
# Square-zero coupling in an upper event algebra

An upper-triangular event endomorphism has two diagonal endpoint actions and one off-diagonal
channel.  This file proves that:

* the off-diagonal channels form a square-zero two-sided direction;
* the two diagonal sectors act on that direction from opposite sides;
* forgetting the off-diagonal channel gives an exact quotient equivalent to the product of the
  endpoint endomorphism algebras; and
* the off-diagonal commutator is the corresponding bimodule action.

These are unconditional block-algebra statements.  They do not identify an event channel with
actualization, a symmetry with a physical force, or a commutator with spacetime curvature.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R K I : Type*}
variable [CommRing R]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup I] [Module R I]

/-- Parameters of an upper-triangular endomorphism of `K × I`. -/
@[ext]
structure EventUpperBlock where
  left : Module.End R K
  bridge : I →ₗ[R] K
  right : Module.End R I

namespace EventUpperBlock

instance : Zero (EventUpperBlock (R := R) (K := K) (I := I)) :=
  ⟨⟨0, 0, 0⟩⟩

instance : Add (EventUpperBlock (R := R) (K := K) (I := I)) :=
  ⟨fun x y => ⟨x.left + y.left, x.bridge + y.bridge, x.right + y.right⟩⟩

instance : Neg (EventUpperBlock (R := R) (K := K) (I := I)) :=
  ⟨fun x => ⟨-x.left, -x.bridge, -x.right⟩⟩

instance : Sub (EventUpperBlock (R := R) (K := K) (I := I)) :=
  ⟨fun x y => ⟨x.left - y.left, x.bridge - y.bridge, x.right - y.right⟩⟩

@[simp] theorem zero_left :
    (0 : EventUpperBlock (R := R) (K := K) (I := I)).left = 0 := rfl

@[simp] theorem zero_bridge :
    (0 : EventUpperBlock (R := R) (K := K) (I := I)).bridge = 0 := rfl

@[simp] theorem zero_right :
    (0 : EventUpperBlock (R := R) (K := K) (I := I)).right = 0 := rfl

@[simp] theorem add_left
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x + y).left = x.left + y.left := rfl

@[simp] theorem add_bridge
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x + y).bridge = x.bridge + y.bridge := rfl

@[simp] theorem add_right
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x + y).right = x.right + y.right := rfl

@[simp] theorem sub_left
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x - y).left = x.left - y.left := rfl

@[simp] theorem sub_bridge
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x - y).bridge = x.bridge - y.bridge := rfl

@[simp] theorem sub_right
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    (x - y).right = x.right - y.right := rfl

/-- Upper-triangular block multiplication. -/
def mul
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    EventUpperBlock (R := R) (K := K) (I := I) :=
  ⟨x.left.comp y.left,
    x.left.comp y.bridge + x.bridge.comp y.right,
    x.right.comp y.right⟩

/-- Faithful realization as an upper-triangular endomorphism. -/
def toEnd (x : EventUpperBlock (R := R) (K := K) (I := I)) :
    Module.End R (K × I) where
  toFun v := (x.left v.1 + x.bridge v.2, x.right v.2)
  map_add' v w := by
    ext
    · simp
      abel
    · simp
  map_smul' r v := by ext <;> simp

@[simp] theorem toEnd_apply
    (x : EventUpperBlock (R := R) (K := K) (I := I)) (v : K × I) :
    x.toEnd v = (x.left v.1 + x.bridge v.2, x.right v.2) := rfl

/-- Upper-block parameters are recovered faithfully from their endomorphism. -/
theorem toEnd_injective :
    Function.Injective
      (toEnd : EventUpperBlock (R := R) (K := K) (I := I) →
        Module.End R (K × I)) := by
  intro x y h
  apply EventUpperBlock.ext
  · ext k
    have hv := LinearMap.congr_fun h (k, 0)
    simpa using congrArg Prod.fst hv
  · ext i
    have hv := LinearMap.congr_fun h (0, i)
    simpa using congrArg Prod.fst hv
  · ext i
    have hv := LinearMap.congr_fun h (0, i)
    simpa using congrArg Prod.snd hv

/-- Abstract upper-block multiplication is ordinary endomorphism composition. -/
theorem toEnd_mul
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    toEnd (mul x y) = toEnd x * toEnd y := by
  apply LinearMap.ext
  rintro ⟨k, i⟩
  ext
  · simp [toEnd, mul]
    abel
  · simp [toEnd, mul]

/-- Pure off-diagonal event channel. -/
def radical (b : I →ₗ[R] K) :
    EventUpperBlock (R := R) (K := K) (I := I) :=
  ⟨0, b, 0⟩

/-- Pure diagonal endpoint symmetry. -/
def diagonal (a : Module.End R K) (d : Module.End R I) :
    EventUpperBlock (R := R) (K := K) (I := I) :=
  ⟨a, 0, d⟩

/-- Any product of two pure event channels is zero. -/
@[simp] theorem radical_mul_radical (b c : I →ₗ[R] K) :
    mul (radical b) (radical c) = 0 := by
  ext <;> simp [mul, radical]

/-- The left endpoint acts on an event channel by postcomposition. -/
@[simp] theorem diagonal_mul_radical
    (a : Module.End R K) (d : Module.End R I) (b : I →ₗ[R] K) :
    mul (diagonal a d) (radical b) = radical (a.comp b) := by
  ext <;> simp [mul, diagonal, radical]

/-- The right endpoint acts on an event channel by precomposition. -/
@[simp] theorem radical_mul_diagonal
    (b : I →ₗ[R] K) (a : Module.End R K) (d : Module.End R I) :
    mul (radical b) (diagonal a d) = radical (b.comp d) := by
  ext <;> simp [mul, diagonal, radical]

/-- Reporter retaining only the two endpoint endomorphisms. -/
def diagonalReporter
    (x : EventUpperBlock (R := R) (K := K) (I := I)) :
    Module.End R K × Module.End R I :=
  (x.left, x.right)

/-- The diagonal of a product is the componentwise endpoint product. -/
theorem diagonalReporter_mul
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :
    diagonalReporter (mul x y) =
      (x.left.comp y.left, x.right.comp y.right) := rfl

/-- Every pair of endpoint endomorphisms has a diagonal upper-block representative. -/
theorem diagonalReporter_surjective :
    Function.Surjective
      (diagonalReporter :
        EventUpperBlock (R := R) (K := K) (I := I) →
          Module.End R K × Module.End R I) := by
  rintro ⟨a, d⟩
  exact ⟨diagonal a d, rfl⟩

/-- The diagonal reporter erases exactly the pure off-diagonal channels. -/
theorem diagonalReporter_eq_zero_iff
    (x : EventUpperBlock (R := R) (K := K) (I := I)) :
    diagonalReporter x = (0, 0) ↔
      ∃ b, x = radical b := by
  constructor
  · intro hx
    have hl : x.left = 0 := congrArg Prod.fst hx
    have hr : x.right = 0 := congrArg Prod.snd hx
    exact ⟨x.bridge, by ext <;> simp [radical, hl, hr]⟩
  · rintro ⟨b, rfl⟩
    rfl

/-- Equality modulo the square-zero event direction. -/
def diagonalSetoid :
    Setoid (EventUpperBlock (R := R) (K := K) (I := I)) where
  r x y := diagonalReporter x = diagonalReporter y
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

/-- Quotient that forgets irreversible off-diagonal event coupling. -/
abbrev SymmetryQuotient :=
  Quotient (diagonalSetoid (R := R) (K := K) (I := I))

/-- The event quotient is exactly the pair of endpoint symmetry algebras. -/
def symmetryQuotientEquiv :
    SymmetryQuotient (R := R) (K := K) (I := I) ≃
      Module.End R K × Module.End R I where
  toFun :=
    Quotient.lift diagonalReporter (fun _ _ h => h)
  invFun p :=
    Quotient.mk _ (diagonal p.1 p.2)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    rfl
  right_inv p := by
    rcases p with ⟨a, d⟩
    rfl

/-- Upper-block multiplication depends modulo the event direction only on both diagonals. -/
theorem mul_respects_diagonalSetoid
    {x x' y y' : EventUpperBlock (R := R) (K := K) (I := I)}
    (hx : diagonalReporter x = diagonalReporter x')
    (hy : diagonalReporter y = diagonalReporter y') :
    diagonalReporter (mul x y) = diagonalReporter (mul x' y') := by
  have hxl : x.left = x'.left := congrArg Prod.fst hx
  have hxr : x.right = x'.right := congrArg Prod.snd hx
  have hyl : y.left = y'.left := congrArg Prod.fst hy
  have hyr : y.right = y'.right := congrArg Prod.snd hy
  simp [diagonalReporter_mul, hxl, hxr, hyl, hyr]

/-- Upper-block addition depends modulo the event direction only on both diagonals. -/
theorem add_respects_diagonalSetoid
    {x x' y y' : EventUpperBlock (R := R) (K := K) (I := I)}
    (hx : diagonalReporter x = diagonalReporter x')
    (hy : diagonalReporter y = diagonalReporter y') :
    diagonalReporter (x + y) = diagonalReporter (x' + y') := by
  have hxl : x.left = x'.left := congrArg Prod.fst hx
  have hxr : x.right = x'.right := congrArg Prod.snd hx
  have hyl : y.left = y'.left := congrArg Prod.fst hy
  have hyr : y.right = y'.right := congrArg Prod.snd hy
  simp [diagonalReporter, hxl, hxr, hyl, hyr]

/-- Addition on the quotient induced by upper-block addition. -/
def quotientAdd
    (q₁ q₂ : SymmetryQuotient (R := R) (K := K) (I := I)) :
    SymmetryQuotient (R := R) (K := K) (I := I) :=
  Quotient.liftOn₂ q₁ q₂
    (fun x y => Quotient.mk _ (x + y))
    (by
      intro x x' y y' hx hy
      apply Quotient.sound
      exact add_respects_diagonalSetoid hx hy)

/-- Quotient addition is exactly componentwise endpoint addition. -/
theorem symmetryQuotientEquiv_add
    (q₁ q₂ : SymmetryQuotient (R := R) (K := K) (I := I)) :
    symmetryQuotientEquiv (quotientAdd q₁ q₂) =
      (symmetryQuotientEquiv q₁ + symmetryQuotientEquiv q₂) := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y
  rfl

/-- Multiplication on the quotient induced by upper-block composition. -/
def quotientMul
    (q₁ q₂ : SymmetryQuotient (R := R) (K := K) (I := I)) :
    SymmetryQuotient (R := R) (K := K) (I := I) :=
  Quotient.liftOn₂ q₁ q₂
    (fun x y => Quotient.mk _ (mul x y))
    (by
      intro x x' y y' hx hy
      apply Quotient.sound
      exact mul_respects_diagonalSetoid hx hy)

/-- Quotient multiplication is exactly componentwise endpoint composition. -/
theorem symmetryQuotientEquiv_mul
    (q₁ q₂ : SymmetryQuotient (R := R) (K := K) (I := I)) :
    symmetryQuotientEquiv (quotientMul q₁ q₂) =
      ((symmetryQuotientEquiv q₁).1.comp (symmetryQuotientEquiv q₂).1,
       (symmetryQuotientEquiv q₁).2.comp (symmetryQuotientEquiv q₂).2) := by
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y
  rfl

/-- Upper-block commutator. -/
def commutator
    (x y : EventUpperBlock (R := R) (K := K) (I := I)) :=
  mul x y - mul y x

/-- Exact diagonal and bimodule components of the upper-block commutator. -/
theorem commutator_eq
    (a a' : Module.End R K) (b b' : I →ₗ[R] K)
    (d d' : Module.End R I) :
    commutator ⟨a, b, d⟩ ⟨a', b', d'⟩ =
      ⟨a.comp a' - a'.comp a,
        a.comp b' + b.comp d' - (a'.comp b + b'.comp d),
        d.comp d' - d'.comp d⟩ := by
  rfl

/-- Pure event channels have zero mutual commutator. -/
@[simp] theorem radical_commutator (b c : I →ₗ[R] K) :
    commutator (radical b) (radical c) = 0 := by
  ext <;> simp [commutator, mul, radical]

/-- The commutator with a pure event channel is its endpoint bimodule action. -/
theorem commutator_radical
    (a : Module.End R K) (b c : I →ₗ[R] K) (d : Module.End R I) :
    commutator ⟨a, b, d⟩ (radical c) =
      radical (a.comp c - c.comp d) := by
  ext <;> simp [commutator, mul, radical]

end EventUpperBlock

end

end GaloisForLFunctions.HTGeometry
