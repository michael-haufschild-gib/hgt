import Mathlib.Analysis.Quaternion
import Mathlib.Tactic.NoncommRing
import GaloisForLFunctions.HTGeometry.Octonion.Alternative

open scoped Quaternion

namespace GaloisForLFunctions.HTGeometry.Octonion

/-- Concrete real Cayley octonions, obtained by doubling Hamilton's quaternions.

The doubling parameter is fixed so that the new unit has square `-1`; this is the compact
division algebra used in arXiv:2605.07183, not the split Cayley algebra. -/
def RealOctonion : Type := ℍ[ℝ] × ℍ[ℝ]

namespace RealOctonion

noncomputable section

instance : AddCommGroup RealOctonion :=
  (inferInstance : AddCommGroup (ℍ[ℝ] × ℍ[ℝ]))
instance : Module ℝ RealOctonion :=
  (inferInstance : Module ℝ (ℍ[ℝ] × ℍ[ℝ]))
instance : Module.Free ℝ RealOctonion :=
  (inferInstance : Module.Free ℝ (ℍ[ℝ] × ℍ[ℝ]))

@[ext]
theorem ext {x y : RealOctonion} (hfst : x.1 = y.1) (hsnd : x.2 = y.2) : x = y :=
  Prod.ext hfst hsnd

@[simp] theorem add_fst (x y : RealOctonion) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem add_snd (x y : RealOctonion) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem zero_fst : (0 : RealOctonion).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : RealOctonion).2 = 0 := rfl
@[simp] theorem neg_fst (x : RealOctonion) : (-x).1 = -x.1 := rfl
@[simp] theorem neg_snd (x : RealOctonion) : (-x).2 = -x.2 := rfl
@[simp] theorem smul_fst (r : ℝ) (x : RealOctonion) : (r • x).1 = r • x.1 := rfl
@[simp] theorem smul_snd (r : ℝ) (x : RealOctonion) : (r • x).2 = r • x.2 := rfl

def mk (p q : ℍ[ℝ]) : RealOctonion := (p, q)

@[simp] theorem mk_fst (p q : ℍ[ℝ]) : (mk p q : RealOctonion).1 = p := rfl
@[simp] theorem mk_snd (p q : ℍ[ℝ]) : (mk p q : RealOctonion).2 = q := rfl

/-- Cayley--Dickson multiplication with the division-algebra sign. -/
instance : Mul RealOctonion where
  mul x y := mk (x.1 * y.1 - star y.2 * x.2) (y.2 * x.1 + x.2 * star y.1)

@[simp] theorem mul_fst (x y : RealOctonion) :
    (x * y).1 = x.1 * y.1 - star y.2 * x.2 := rfl
@[simp] theorem mul_snd (x y : RealOctonion) :
    (x * y).2 = y.2 * x.1 + x.2 * star y.1 := rfl

instance : One RealOctonion := ⟨mk 1 0⟩

@[simp] theorem one_fst : (1 : RealOctonion).1 = 1 := rfl
@[simp] theorem one_snd : (1 : RealOctonion).2 = 0 := rfl

instance : NonAssocRing RealOctonion where
  left_distrib x y z := by ext <;> simp [mul_add] <;> ring
  right_distrib x y z := by ext <;> simp [add_mul] <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

/-- Cayley--Dickson conjugation. -/
instance : Star RealOctonion where
  star x := mk (star x.1) (-x.2)

@[simp] theorem star_fst (x : RealOctonion) : (star x).1 = star x.1 := rfl
@[simp] theorem star_snd (x : RealOctonion) : (star x).2 = -x.2 := rfl

instance : StarRing RealOctonion where
  star_involutive x := by ext <;> simp
  star_add x y := by ext <;> simp [add_comm]
  star_mul x y := by ext <;> simp

instance : IsScalarTower ℝ RealOctonion RealOctonion where
  smul_assoc r x y := by
    apply ext
    · simp only [smul_eq_mul, smul_fst, mul_fst, smul_snd]
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    · simp only [smul_eq_mul, smul_snd, mul_snd, smul_fst]
      rw [mul_smul_comm, smul_mul_assoc, ← smul_add]

instance : SMulCommClass ℝ RealOctonion RealOctonion where
  smul_comm r x y := by
    apply ext
    · simp only [smul_eq_mul, mul_fst, smul_fst, smul_snd]
      rw [mul_smul_comm, Quaternion.star_smul, smul_mul_assoc, ← smul_sub]
    · simp only [smul_eq_mul, mul_snd, smul_snd, smul_fst]
      rw [smul_mul_assoc, Quaternion.star_smul, mul_smul_comm, ← smul_add]

private theorem add_star_eq_coe (p : ℍ[ℝ]) :
    p + star p = ((2 * p.re : ℝ) : ℍ[ℝ]) := by
  calc
    p + star p = (2 : ℍ[ℝ]) * (p.re : ℍ[ℝ]) := Quaternion.self_add_star p
    _ = ((2 * p.re : ℝ) : ℍ[ℝ]) := (Quaternion.coe_mul 2 p.re).symm

private theorem add_star_mul_comm (p q : ℍ[ℝ]) :
    (p + star p) * q = q * (p + star p) := by
  rw [add_star_eq_coe]
  exact Quaternion.coe_commutes _ q

private theorem star_mul_self_eq_coe (q : ℍ[ℝ]) :
    star q * q = ((star q * q).re : ℍ[ℝ]) :=
  Quaternion.star_mul_eq_coe q

private theorem star_mul_self_mul_comm (p q : ℍ[ℝ]) :
    (star q * q) * p = p * (star q * q) := by
  rw [star_mul_self_eq_coe]
  exact Quaternion.coe_commutes _ p

private theorem mul_star_self_eq_star_mul_self (q : ℍ[ℝ]) :
    q * star q = star q * q :=
  (star_comm_self' q).symm

private theorem alternative_left (x y : RealOctonion) : x * (x * y) = (x * x) * y := by
  apply ext
  · show x.1 * (x * y).1 - star (x * y).2 * x.2 =
      (x * x).1 * y.1 - star y.2 * (x * x).2
    simp only [mul_fst, mul_snd, star_add, star_mul, star_star, mul_sub,
      sub_mul, mul_add, add_mul]
    rw [← mul_assoc x.1 x.1 y.1]
    have key : x.1 * (star y.2 * x.2) +
        (star x.1 * star y.2 * x.2 + y.1 * star x.2 * x.2) =
        star x.2 * x.2 * y.1 +
          (star y.2 * (x.2 * x.1) + star y.2 * (x.2 * star x.1)) := by
      have h1 : (x.1 + star x.1) * (star y.2 * x.2) =
          (star y.2 * x.2) * (x.1 + star x.1) :=
        add_star_mul_comm x.1 (star y.2 * x.2)
      have h2 : y.1 * (star x.2 * x.2) = (star x.2 * x.2) * y.1 :=
        (star_mul_self_mul_comm y.1 x.2).symm
      calc
        x.1 * (star y.2 * x.2) +
            (star x.1 * star y.2 * x.2 + y.1 * star x.2 * x.2) =
          (x.1 + star x.1) * (star y.2 * x.2) + y.1 * (star x.2 * x.2) := by
            noncomm_ring
        _ = (star y.2 * x.2) * (x.1 + star x.1) + (star x.2 * x.2) * y.1 := by
            rw [h1, h2]
        _ = star x.2 * x.2 * y.1 +
            (star y.2 * (x.2 * x.1) + star y.2 * (x.2 * star x.1)) := by
            noncomm_ring
    linear_combination (norm := abel) -key
  · show (x * y).2 * x.1 + x.2 * star (x * y).1 =
      y.2 * (x * x).1 + (x * x).2 * star y.1
    simp only [mul_fst, mul_snd, star_sub, star_mul, star_star, mul_sub,
      add_mul]
    rw [mul_assoc y.2 x.1 x.1]
    have key : x.2 * star y.1 * x.1 + x.2 * (star y.1 * star x.1) -
        x.2 * (star x.2 * y.2) =
        x.2 * x.1 * star y.1 + x.2 * star x.1 * star y.1 -
          y.2 * (star x.2 * x.2) := by
      have h1 : star y.1 * (x.1 + star x.1) = (x.1 + star x.1) * star y.1 :=
        (add_star_mul_comm x.1 (star y.1)).symm
      have h2 : x.2 * star x.2 * y.2 = y.2 * (star x.2 * x.2) := by
        rw [mul_star_self_eq_star_mul_self, star_mul_self_mul_comm]
      calc
        x.2 * star y.1 * x.1 + x.2 * (star y.1 * star x.1) -
            x.2 * (star x.2 * y.2) =
          x.2 * (star y.1 * (x.1 + star x.1)) - x.2 * star x.2 * y.2 := by
            noncomm_ring
        _ = x.2 * ((x.1 + star x.1) * star y.1) - y.2 * (star x.2 * x.2) := by
            rw [h1, h2]
        _ = x.2 * x.1 * star y.1 + x.2 * star x.1 * star y.1 -
            y.2 * (star x.2 * x.2) := by
            noncomm_ring
    linear_combination (norm := noncomm_ring) key

private theorem alternative_right (x y : RealOctonion) : (y * x) * x = y * (x * x) := by
  have h := congrArg star (alternative_left (star x) (star y))
  simpa [star_mul, star_star] using h

instance : IsAlternative RealOctonion where
  mul_alternative_left := alternative_left
  mul_alternative_right := alternative_right

/-- Scalar copy of the real numbers inside the Cayley octonions. -/
def scalarEmbed : ℝ →+* RealOctonion where
  toFun r := mk (r : ℍ[ℝ]) 0
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

@[simp] theorem scalarEmbed_fst (r : ℝ) : (scalarEmbed r : RealOctonion).1 = r := rfl
@[simp] theorem scalarEmbed_snd (r : ℝ) : (scalarEmbed r : RealOctonion).2 = 0 := rfl

theorem scalarEmbed_mul (r : ℝ) (x : RealOctonion) : scalarEmbed r * x = r • x := by
  apply ext
  · simp [mul_fst, Algebra.smul_def]
  · simp [mul_snd, Algebra.smul_def, Quaternion.coe_commutes]

theorem mul_scalarEmbed (x : RealOctonion) (r : ℝ) : x * scalarEmbed r = r • x := by
  apply ext
  · simp [mul_fst, Algebra.smul_def, Quaternion.coe_commutes]
  · simp [mul_snd, Algebra.smul_def, Quaternion.coe_commutes]

theorem scalarEmbed_associates (r : ℝ) (x y : RealOctonion) :
    (scalarEmbed r * x) * y = scalarEmbed r * (x * y) := by
  rw [scalarEmbed_mul, scalarEmbed_mul]
  exact smul_mul_assoc r x y

theorem mul_scalarEmbed_associates (x : RealOctonion) (r : ℝ) (y : RealOctonion) :
    (x * scalarEmbed r) * y = x * (scalarEmbed r * y) := by
  rw [mul_scalarEmbed, scalarEmbed_mul, smul_mul_assoc, mul_smul_comm]

/-- Euclidean norm squared of the concrete Cayley octonion. -/
def normSq (x : RealOctonion) : ℝ :=
  (star x.1 * x.1).re + (star x.2 * x.2).re

theorem normSq_eq_quaternion_normSq (x : RealOctonion) :
    normSq x = Quaternion.normSq x.1 + Quaternion.normSq x.2 := by
  unfold normSq
  rw [Quaternion.star_mul_self, Quaternion.star_mul_self]
  simp

theorem normSq_nonneg (x : RealOctonion) : 0 ≤ normSq x := by
  rw [normSq_eq_quaternion_normSq]
  exact add_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg

theorem normSq_eq_zero (x : RealOctonion) : normSq x = 0 ↔ x = 0 := by
  rw [normSq_eq_quaternion_normSq]
  constructor
  · intro h
    rw [add_eq_zero_iff_of_nonneg Quaternion.normSq_nonneg Quaternion.normSq_nonneg] at h
    apply ext
    · exact Quaternion.normSq_eq_zero.mp h.1
    · exact Quaternion.normSq_eq_zero.mp h.2
  · intro h
    subst x
    simp

theorem mul_star_self_eq_scalarEmbed (x : RealOctonion) :
    x * star x = scalarEmbed (normSq x) := by
  apply ext
  · show x.1 * (star x).1 - star (star x).2 * x.2 = (scalarEmbed (normSq x)).1
    rw [star_fst, star_snd, star_neg, neg_mul, sub_neg_eq_add,
      mul_star_self_eq_star_mul_self, star_mul_self_eq_coe x.1,
      star_mul_self_eq_coe x.2, scalarEmbed_fst]
    exact (Quaternion.coe_add _ _).symm
  · show (star x).2 * x.1 + x.2 * star (star x).1 = (scalarEmbed (normSq x)).2
    rw [star_snd, star_fst, star_star, neg_mul, scalarEmbed_snd]
    abel

theorem star_mul_self_eq_scalarEmbed (x : RealOctonion) :
    star x * x = scalarEmbed (normSq x) := by
  have h := mul_star_self_eq_scalarEmbed (star x)
  calc
    star x * x = scalarEmbed (normSq (star x)) := by simpa using h
    _ = scalarEmbed (normSq x) := by
      congr 1
      simp only [normSq, star_fst, star_snd, star_star, star_neg, neg_mul,
        mul_neg, neg_neg]
      rw [mul_star_self_eq_star_mul_self]

/-- The algebraic inverse in the real division octonions. -/
def inverse (x : RealOctonion) : RealOctonion :=
  scalarEmbed (normSq x)⁻¹ * star x

theorem mul_inverse (x : RealOctonion) (hx : x ≠ 0) : x * inverse x = 1 := by
  have hn : normSq x ≠ 0 := mt (normSq_eq_zero x).mp hx
  rw [inverse, ← mul_scalarEmbed_associates, mul_scalarEmbed,
    smul_mul_assoc, mul_star_self_eq_scalarEmbed]
  rw [show (normSq x)⁻¹ • scalarEmbed (normSq x) =
      scalarEmbed ((normSq x)⁻¹ * normSq x) by rw [← scalarEmbed_mul, map_mul]]
  calc
    scalarEmbed ((normSq x)⁻¹ * normSq x) = scalarEmbed 1 :=
      congrArg scalarEmbed (inv_mul_cancel₀ hn)
    _ = 1 := map_one scalarEmbed

theorem inverse_mul (x : RealOctonion) (hx : x ≠ 0) : inverse x * x = 1 := by
  have hn : normSq x ≠ 0 := mt (normSq_eq_zero x).mp hx
  rw [inverse, scalarEmbed_associates, star_mul_self_eq_scalarEmbed]
  calc
    scalarEmbed (normSq x)⁻¹ * scalarEmbed (normSq x) =
      scalarEmbed ((normSq x)⁻¹ * normSq x) := (map_mul scalarEmbed _ _).symm
    _ = scalarEmbed 1 := congrArg scalarEmbed (inv_mul_cancel₀ hn)
    _ = 1 := map_one scalarEmbed

theorem add_star_eq_scalarEmbed (x : RealOctonion) :
    x + star x = scalarEmbed (2 * x.1.re) := by
  apply ext
  · simpa [scalarEmbed] using add_star_eq_coe x.1
  · simp

theorem star_eq_scalarEmbed_sub (x : RealOctonion) :
    star x = scalarEmbed (2 * x.1.re) - x := by
  rw [← add_star_eq_scalarEmbed]
  abel

/-- Conjugate factors associate on the right. -/
theorem mul_star_associates (x s : RealOctonion) :
    (x * star s) * s = x * (star s * s) := by
  rw [star_eq_scalarEmbed_sub]
  simp only [mul_sub, sub_mul]
  rw [mul_scalarEmbed, scalarEmbed_mul, smul_mul_assoc, mul_smul_comm,
    IsAlternative.mul_alternative_right]

end
end RealOctonion
end GaloisForLFunctions.HTGeometry.Octonion
