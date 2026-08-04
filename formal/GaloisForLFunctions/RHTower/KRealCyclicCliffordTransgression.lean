import GaloisForLFunctions.RHTower.KRealCyclicModule

/-!
# Clifford transgression of Real-even cyclic morphisms

A cyclic morphism commuting with conjugate-linear Real structures becomes anti-Real after
multiplication by `i`.  This elementary parity shift is the degree-zero cyclic-module form of
Clifford suspension.  It is the correct type for comparing an anti-Real Real-corona character with
a Real-even Lefschetz correspondence.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions
namespace RHTower
namespace CyclicModule

/-- Scalar endomorphism of a cyclic module. -/
def Hom.scalar (X : CyclicModule ℂ) (z : ℂ) : Hom X X where
  simplicial :=
    { app := fun j => ModuleCat.ofHom
        { toFun := fun x => z • x
          map_add' := fun x y => by simp
          map_smul' := fun c x => by
            simp only [smul_smul]
            rw [mul_comm]
            simp only [RingHom.id_apply] }
      naturality := by
        intro j k f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp }
  cyclic_naturality n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp

@[simp]
theorem Hom.scalar_degree_apply
    (X : CyclicModule ℂ) (z : ℂ) (n : ℕ)
    (x : X.simplicial.degree n) :
    (Hom.scalar X z).simplicial.app (.op (.mk n)) x = z • x :=
  rfl

/-- Scalar multiple of a cyclic morphism, implemented by scalar postcomposition. -/
def Hom.smul {X Y : CyclicModule ℂ} (z : ℂ) (f : Hom X Y) : Hom X Y :=
  f.comp (Hom.scalar Y z)

@[simp]
theorem Hom.smul_degree_apply
    {X Y : CyclicModule ℂ} (z : ℂ) (f : Hom X Y) (n : ℕ)
    (x : X.simplicial.degree n) :
    (f.smul z).simplicial.app (.op (.mk n)) x =
      z • f.simplicial.app (.op (.mk n)) x :=
  rfl

/-- Anti-equivariant cyclic morphism between even Real cyclic modules. -/
structure KRealAntiHom {X Y : CyclicModule ℂ}
    (KX : KReal false X) (KY : KReal false Y) extends Hom X Y where
  real_antinaturality : ∀ n (x : X.simplicial.degree n),
    (KY.real n).sigma (toHom.simplicial.app (.op (.mk n)) x) =
      -toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma x)

/-- A morphism cannot be simultaneously Real-even and anti-Real unless every degree map is zero. -/
theorem KRealHom.degree_eq_zero_of_anti
    {X Y : CyclicModule ℂ} {KX : KReal false X} {KY : KReal false Y}
    (f : KRealHom KX KY)
    (hanti : ∀ n (x : X.simplicial.degree n),
      (KY.real n).sigma (f.toHom.simplicial.app (.op (.mk n)) x) =
        -f.toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma x))
    (n : ℕ) (x : X.simplicial.degree n) :
    f.toHom.simplicial.app (.op (.mk n)) x = 0 := by
  let sx := (KX.real n).sigma x
  have heven := f.real_naturality n sx
  have hodd := hanti n sx
  have hneg :
      f.toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma sx) =
        -f.toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma sx) := by
    exact heven.symm.trans hodd
  have hzero :
      f.toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma sx) = 0 := by
    have htwo :
        (2 : ℂ) •
            f.toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma sx) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hneg
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [sx, (KX.real n).sq x, kRealParityAction] using hzero

/-- Exact scalar classification for the Real-parity shift.  For a nonzero Real-even cyclic
morphism, a scalar multiple is anti-Real precisely when the scalar is purely imaginary, expressed
intrinsically as `conj z = -z`.  Thus Clifford transgression is canonical after choosing the
positive unit imaginary scalar, but Real parity alone does not falsely make that choice unique. -/
theorem KRealHom.smul_isAnti_iff_star_eq_neg
    {X Y : CyclicModule ℂ} {KX : KReal false X} {KY : KReal false Y}
    (f : KRealHom KX KY)
    (hf : ∃ n, ∃ x : X.simplicial.degree n,
      f.toHom.simplicial.app (.op (.mk n)) x ≠ 0)
    (z : ℂ) :
    (∀ n (x : X.simplicial.degree n),
      (KY.real n).sigma
          ((f.toHom.smul z).simplicial.app (.op (.mk n)) x) =
        -(f.toHom.smul z).simplicial.app
          (.op (.mk n)) ((KX.real n).sigma x)) ↔
      (starRingEnd ℂ) z = -z := by
  constructor
  · intro hanti
    obtain ⟨n, x, hx⟩ := hf
    have h := hanti n ((KX.real n).sigma x)
    rw [Hom.smul_degree_apply, map_smulₛₗ, f.real_naturality,
      Hom.smul_degree_apply, (KX.real n).sq] at h
    simp only [kRealParityAction, Bool.false_eq_true, ↓reduceIte] at h
    have hzsmul : ((starRingEnd ℂ) z + z) •
        f.toHom.simplicial.app (.op (.mk n)) x = 0 := by
      rw [add_smul, h]
      simp
    have hz : (starRingEnd ℂ) z + z = 0 :=
      (smul_eq_zero.mp hzsmul).resolve_right hx
    linear_combination hz
  · intro hz n x
    rw [Hom.smul_degree_apply, map_smulₛₗ, f.real_naturality,
      Hom.smul_degree_apply, hz]
    simp

/-- **Clifford transgression.** Multiplication by `i` changes Real-even cyclic naturality into
anti-Real cyclic naturality. -/
def KRealHom.cliffordTransgression
    {X Y : CyclicModule ℂ} {KX : KReal false X} {KY : KReal false Y}
    (f : KRealHom KX KY) : KRealAntiHom KX KY where
  toHom := f.toHom.smul Complex.I
  real_antinaturality n x := by
    rw [Hom.smul_degree_apply, map_smulₛₗ, f.real_naturality]
    simp

@[simp]
theorem KRealHom.cliffordTransgression_degree_apply
    {X Y : CyclicModule ℂ} {KX : KReal false X} {KY : KReal false Y}
    (f : KRealHom KX KY) (n : ℕ) (x : X.simplicial.degree n) :
    f.cliffordTransgression.toHom.simplicial.app (.op (.mk n)) x =
      Complex.I • f.toHom.simplicial.app (.op (.mk n)) x :=
  rfl

/-- Clifford transgression of the identity squares to minus the identity in every cyclic degree. -/
theorem KRealHom.cliffordTransgression_identity_sq
    {X : CyclicModule ℂ} {KX : KReal false X}
    (f : KRealHom KX KX)
    (hid : ∀ n (x : X.simplicial.degree n),
      f.toHom.simplicial.app (.op (.mk n)) x = x)
    (n : ℕ) (x : X.simplicial.degree n) :
    f.cliffordTransgression.toHom.simplicial.app (.op (.mk n))
        (f.cliffordTransgression.toHom.simplicial.app (.op (.mk n)) x) = -x := by
  rw [KRealHom.cliffordTransgression_degree_apply,
    KRealHom.cliffordTransgression_degree_apply, hid]
  simpa [smul_smul] using hid n x

end CyclicModule
end RHTower
end GaloisForLFunctions
