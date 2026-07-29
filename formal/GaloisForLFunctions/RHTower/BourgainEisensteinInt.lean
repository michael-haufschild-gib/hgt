/-
# Eisenstein integers for the parabola-fiber divisor bound

This file supplies the arithmetic ring naturally attached to
`u² + 3v²`.  We represent `a + bω`, where `ω² + ω + 1 = 0`, by the pair
`(a,b)`.  Its norm is `a² - ab + b²`.

The Euclidean algorithm and divisor-counting consequences are developed in
subsequent modules.  Keeping this algebraic core separate makes the trusted
base of the quadratic-form reduction explicit.
-/
import GaloisForLFunctions.RHTower.BourgainParabolaQuadraticReduction

namespace RHTower

/-- Eisenstein integer `a + bω`, with `ω² + ω + 1 = 0`. -/
@[ext]
structure BourgainEisensteinInt where
  re : ℤ
  im : ℤ
  deriving DecidableEq

namespace BourgainEisensteinInt

/-- Integral scalar embedded in the Eisenstein integers. -/
def ofInt (n : ℤ) : BourgainEisensteinInt :=
  ⟨n, 0⟩

instance : Zero BourgainEisensteinInt :=
  ⟨ofInt 0⟩

instance : One BourgainEisensteinInt :=
  ⟨ofInt 1⟩

instance : Add BourgainEisensteinInt :=
  ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg BourgainEisensteinInt :=
  ⟨fun x => ⟨-x.re, -x.im⟩⟩

/-- Multiplication using `ω² = -ω - 1`. -/
instance : Mul BourgainEisensteinInt :=
  ⟨fun x y =>
    ⟨x.re * y.re - x.im * y.im,
      x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[simp] theorem re_zero : (0 : BourgainEisensteinInt).re = 0 := rfl
@[simp] theorem im_zero : (0 : BourgainEisensteinInt).im = 0 := rfl
@[simp] theorem re_one : (1 : BourgainEisensteinInt).re = 1 := rfl
@[simp] theorem im_one : (1 : BourgainEisensteinInt).im = 0 := rfl
@[simp] theorem re_add (x y : BourgainEisensteinInt) :
    (x + y).re = x.re + y.re := rfl
@[simp] theorem im_add (x y : BourgainEisensteinInt) :
    (x + y).im = x.im + y.im := rfl
@[simp] theorem re_neg (x : BourgainEisensteinInt) :
    (-x).re = -x.re := rfl
@[simp] theorem im_neg (x : BourgainEisensteinInt) :
    (-x).im = -x.im := rfl
@[simp] theorem re_mul (x y : BourgainEisensteinInt) :
    (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem im_mul (x y : BourgainEisensteinInt) :
    (x * y).im =
      x.re * y.im + x.im * y.re - x.im * y.im := rfl

instance instAddCommGroup : AddCommGroup BourgainEisensteinInt := by
  refine
    { sub := fun x y => x + -y
      nsmul := @nsmulRec BourgainEisensteinInt ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec BourgainEisensteinInt ⟨0⟩ ⟨(· + ·)⟩
        ⟨Neg.neg⟩ (@nsmulRec BourgainEisensteinInt ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp <;> omega

instance instAddGroupWithOne : AddGroupWithOne BourgainEisensteinInt :=
  { instAddCommGroup with
    natCast := fun n => ofInt n
    intCast := ofInt }

instance instCommRing : CommRing BourgainEisensteinInt := by
  refine
    { instAddGroupWithOne with
      npow := @npowRec BourgainEisensteinInt ⟨1⟩ ⟨(· * ·)⟩
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

instance : Nontrivial BourgainEisensteinInt :=
  ⟨⟨0, 1, by
    intro h
    have := congrArg BourgainEisensteinInt.re h
    norm_num at this⟩⟩

instance : CharZero BourgainEisensteinInt where
  cast_injective m n h := by
    have := congrArg BourgainEisensteinInt.re h
    change (m : ℤ) = (n : ℤ) at this
    exact_mod_cast this

@[simp] theorem re_natCast (n : ℕ) :
    (n : BourgainEisensteinInt).re = n := rfl

@[simp] theorem im_natCast (n : ℕ) :
    (n : BourgainEisensteinInt).im = 0 := rfl

@[simp] theorem re_intCast (n : ℤ) :
    (n : BourgainEisensteinInt).re = n := rfl

@[simp] theorem im_intCast (n : ℤ) :
    (n : BourgainEisensteinInt).im = 0 := rfl

/-- Eisenstein conjugation:
`conj(a + bω) = a + bω² = (a-b) - bω`. -/
def conj (x : BourgainEisensteinInt) : BourgainEisensteinInt :=
  ⟨x.re - x.im, -x.im⟩

@[simp] theorem re_conj (x : BourgainEisensteinInt) :
    (conj x).re = x.re - x.im := rfl

@[simp] theorem im_conj (x : BourgainEisensteinInt) :
    (conj x).im = -x.im := rfl

@[simp] theorem conj_conj (x : BourgainEisensteinInt) :
    conj (conj x) = x := by
  ext <;> simp [conj]

@[simp] theorem conj_add (x y : BourgainEisensteinInt) :
    conj (x + y) = conj x + conj y := by
  ext <;> simp [conj] <;> ring

@[simp] theorem conj_mul (x y : BourgainEisensteinInt) :
    conj (x * y) = conj x * conj y := by
  ext <;> simp [conj] <;> ring

/-- Multiplicative norm `a² - ab + b²`. -/
def norm (x : BourgainEisensteinInt) : ℤ :=
  x.re ^ (2 : ℕ) - x.re * x.im + x.im ^ (2 : ℕ)

theorem norm_def (x : BourgainEisensteinInt) :
    norm x = x.re ^ (2 : ℕ) - x.re * x.im + x.im ^ (2 : ℕ) :=
  rfl

@[simp] theorem norm_zero : norm 0 = 0 := by
  simp [norm]

@[simp] theorem norm_one : norm 1 = 1 := by
  simp [norm]

@[simp] theorem norm_intCast (n : ℤ) :
    norm (n : BourgainEisensteinInt) = n ^ (2 : ℕ) := by
  simp [norm]

@[simp] theorem norm_natCast (n : ℕ) :
    norm (n : BourgainEisensteinInt) = (n : ℤ) ^ (2 : ℕ) := by
  simp [norm]

/-- Norm is the scalar product with the conjugate. -/
theorem mul_conj (x : BourgainEisensteinInt) :
    x * conj x = (norm x : BourgainEisensteinInt) := by
  apply BourgainEisensteinInt.ext
  · change
      x.re * (x.re - x.im) - x.im * (-x.im) = norm x
    simp only [norm]
    ring
  · change
      x.re * (-x.im) + x.im * (x.re - x.im) -
          x.im * (-x.im) = 0
    ring

/-- Eisenstein norm is multiplicative. -/
theorem norm_mul (x y : BourgainEisensteinInt) :
    norm (x * y) = norm x * norm y := by
  simp only [norm, re_mul, im_mul]
  ring

/-- Eisenstein norm as a monoid homomorphism. -/
def normMonoidHom : BourgainEisensteinInt →* ℤ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

/-- Positive-definite identity `4N(a+bω)=(2a-b)²+3b²`. -/
theorem four_mul_norm (x : BourgainEisensteinInt) :
    4 * norm x =
      (2 * x.re - x.im) ^ (2 : ℕ) +
        3 * x.im ^ (2 : ℕ) := by
  simp only [norm]
  ring

theorem norm_nonneg (x : BourgainEisensteinInt) :
    0 ≤ norm x := by
  nlinarith [four_mul_norm x, sq_nonneg (2 * x.re - x.im),
    sq_nonneg x.im]

@[simp] theorem norm_eq_zero {x : BourgainEisensteinInt} :
    norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsum :
        (2 * x.re - x.im) ^ (2 : ℕ) +
            3 * x.im ^ (2 : ℕ) = 0 := by
      nlinarith [four_mul_norm x]
    have him : x.im = 0 := by
      nlinarith [sq_nonneg (2 * x.re - x.im), sq_nonneg x.im]
    have hre : x.re = 0 := by
      rw [him] at hsum
      nlinarith [sq_nonneg x.re]
    exact BourgainEisensteinInt.ext hre him
  · rintro rfl
    exact norm_zero

theorem norm_pos {x : BourgainEisensteinInt} :
    0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm, norm_eq_zero]
  simp [norm_nonneg]

/-- `u²+3v²` is the Eisenstein norm of `(u+v)+2vω`. -/
def ofQuadraticPair (u v : ℤ) : BourgainEisensteinInt :=
  ⟨u + v, 2 * v⟩

theorem norm_ofQuadraticPair (u v : ℤ) :
    norm (ofQuadraticPair u v) =
      u ^ (2 : ℕ) + 3 * v ^ (2 : ℕ) := by
  simp [ofQuadraticPair, norm]
  ring

/-- The quadratic-pair embedding is injective. -/
theorem ofQuadraticPair_injective :
    Function.Injective (fun uv : ℤ × ℤ =>
      ofQuadraticPair uv.1 uv.2) := by
  intro uv xy h
  have him := congrArg BourgainEisensteinInt.im h
  have hre := congrArg BourgainEisensteinInt.re h
  simp only [ofQuadraticPair] at him hre
  apply Prod.ext
  · omega
  · omega

end BourgainEisensteinInt

end RHTower
