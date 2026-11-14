import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Tactic.NoncommRing

/-!
# The integral algebra of Raynaud operators

The operators satisfy `FV = VF = p`, `d² = 0`, and `FdV = d`. We construct
their algebra as a quotient, so every identity below holds in an actual ring.
This is the integral operator algebra, before adjoining Witt scalars and their
semilinearity relations. It isolates the operator calculations used in the
finite-torsion comparisons of Yuan Yang, *Finite torsion in Hodge--Witt
cohomology groups*, §§1--4, arXiv:2611.11269.
-/

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

inductive RaynaudGenerator
  | frobenius | verschiebung | differential

open RaynaudGenerator

private abbrev generator := FreeAlgebra.ι ℤ (X := RaynaudGenerator)

/-- The integral Raynaud relations. -/
inductive RaynaudRelation (p : ℕ) :
    FreeAlgebra ℤ RaynaudGenerator → FreeAlgebra ℤ RaynaudGenerator → Prop
  | fv : RaynaudRelation p (generator frobenius * generator verschiebung) p
  | vf : RaynaudRelation p (generator verschiebung * generator frobenius) p
  | dd : RaynaudRelation p (generator differential * generator differential) 0
  | fdv : RaynaudRelation p
      (generator frobenius * generator differential * generator verschiebung)
      (generator differential)

/-- Universal integral algebra of Frobenius, Verschiebung and differential. -/
abbrev RaynaudAlgebra (p : ℕ) := RingQuot (RaynaudRelation p)

namespace RaynaudAlgebra

variable (p : ℕ)

def F : RaynaudAlgebra p := RingQuot.mkAlgHom ℤ _ (generator frobenius)
def V : RaynaudAlgebra p := RingQuot.mkAlgHom ℤ _ (generator verschiebung)
def d : RaynaudAlgebra p := RingQuot.mkAlgHom ℤ _ (generator differential)

theorem F_mul_V : F p * V p = p := by
  simpa only [F, V, map_mul, map_natCast] using
    RingQuot.mkAlgHom_rel ℤ (RaynaudRelation.fv (p := p))

theorem V_mul_F : V p * F p = p := by
  simpa only [F, V, map_mul, map_natCast] using
    RingQuot.mkAlgHom_rel ℤ (RaynaudRelation.vf (p := p))

theorem d_mul_d : d p * d p = 0 := by
  simpa only [d, map_mul, map_zero] using
    RingQuot.mkAlgHom_rel ℤ (RaynaudRelation.dd (p := p))

theorem F_mul_d_mul_V : F p * d p * V p = d p := by
  simpa only [F, V, d, map_mul] using
    RingQuot.mkAlgHom_rel ℤ (RaynaudRelation.fdv (p := p))

theorem commute_F_V : Commute (F p) (V p) := by
  show F p * V p = V p * F p
  rw [F_mul_V, V_mul_F]

/-- Iterating the Raynaud identity moves every power of `V` past the differential. -/
theorem F_pow_mul_d_mul_V_pow (n : ℕ) : F p ^ n * d p * V p ^ n = d p := by
  induction n with
  | zero => simp only [pow_zero, one_mul, mul_one]
  | succ n ih =>
      calc
        F p ^ (n + 1) * d p * V p ^ (n + 1) =
            F p * (F p ^ n * d p * V p ^ n) * V p := by
          rw [pow_succ' (F p), pow_succ (V p)]
          simp only [mul_assoc]
        _ = d p := by rw [ih, F_mul_d_mul_V]

theorem F_pow_mul_V_pow (n : ℕ) : F p ^ n * V p ^ n = (p : RaynaudAlgebra p) ^ n := by
  rw [← (commute_F_V p).mul_pow, F_mul_V]

theorem V_pow_mul_F_pow (n : ℕ) : V p ^ n * F p ^ n = (p : RaynaudAlgebra p) ^ n := by
  rw [← (commute_F_V p).symm.mul_pow, V_mul_F]

/-- `dF = pFd` follows from `FdV = d` and `VF = p`. -/
theorem d_mul_F : d p * F p = (p : RaynaudAlgebra p) * F p * d p := by
  calc
    d p * F p = (F p * d p * V p) * F p := by rw [F_mul_d_mul_V]
    _ = F p * d p * (p : RaynaudAlgebra p) := by
      rw [mul_assoc, mul_assoc, V_mul_F, mul_assoc]
    _ = (p : RaynaudAlgebra p) * F p * d p := by
      rw [← (Nat.cast_commute p (F p * d p)).eq, mul_assoc]

theorem V_mul_d : V p * d p = (p : RaynaudAlgebra p) * d p * V p := by
  calc
    V p * d p = V p * (F p * d p * V p) := by rw [F_mul_d_mul_V]
    _ = (p : RaynaudAlgebra p) * d p * V p := by
      rw [← mul_assoc, ← mul_assoc, V_mul_F]

theorem d_mul_F_pow (n : ℕ) :
    d p * F p ^ n = (p : RaynaudAlgebra p) ^ n * F p ^ n * d p := by
  induction n with
  | zero => simp only [pow_zero, mul_one, one_mul]
  | succ n ih =>
      rw [pow_succ (F p), ← mul_assoc, ih, mul_assoc _ _ (F p), d_mul_F]
      calc
        (p : RaynaudAlgebra p) ^ n * F p ^ n * ((p : RaynaudAlgebra p) * F p * d p) =
            (p : RaynaudAlgebra p) ^ n * (F p ^ n * (p : RaynaudAlgebra p)) *
              F p * d p := by simp only [mul_assoc]
        _ = (p : RaynaudAlgebra p) ^ n * ((p : RaynaudAlgebra p) * F p ^ n) *
              F p * d p := by rw [← (Nat.cast_commute p (F p ^ n)).eq]
        _ = (p : RaynaudAlgebra p) ^ (n + 1) * (F p ^ n * F p) * d p := by
          rw [pow_succ]
          simp only [mul_assoc]

theorem V_pow_mul_d (n : ℕ) :
    V p ^ n * d p = (p : RaynaudAlgebra p) ^ n * d p * V p ^ n := by
  induction n with
  | zero => simp only [pow_zero, one_mul, mul_one]
  | succ n ih =>
      calc
        V p ^ (n + 1) * d p = V p ^ n * ((p : RaynaudAlgebra p) * d p * V p) := by
          rw [pow_succ, mul_assoc, V_mul_d]
        _ = (p : RaynaudAlgebra p) * (V p ^ n * d p) * V p := by
          rw [← mul_assoc, ← mul_assoc, ← (Nat.cast_commute p (V p ^ n)).eq]
          simp only [mul_assoc]
        _ = (p : RaynaudAlgebra p) ^ (n + 1) * d p * V p ^ (n + 1) := by
          rw [ih, pow_succ' (p : RaynaudAlgebra p), pow_succ (V p)]
          simp only [mul_assoc]

/-- Frobenius-saturated boundaries remain cycles after every Verschiebung iterate. -/
theorem d_mul_V_pow_mul_F_pow_mul_d (r s : ℕ) :
    d p * V p ^ r * F p ^ s * d p = 0 := by
  have hfv := ((commute_F_V p).pow_pow s r).eq
  calc
    d p * V p ^ r * F p ^ s * d p = d p * F p ^ s * (V p ^ r * d p) := by
      simp only [mul_assoc]
      rw [← mul_assoc (V p ^ r), ← hfv]
      simp only [mul_assoc]
    _ = ((p : RaynaudAlgebra p) ^ s * F p ^ s) *
        (d p * (p : RaynaudAlgebra p) ^ r) * d p * V p ^ r := by
      rw [d_mul_F_pow, V_pow_mul_d]
      simp only [mul_assoc]
    _ = ((p : RaynaudAlgebra p) ^ s * F p ^ s) *
        ((p : RaynaudAlgebra p) ^ r * (d p * d p)) * V p ^ r := by
      rw [← ((Nat.cast_commute p (d p)).pow_left r).eq]
      simp only [mul_assoc]
    _ = 0 := by rw [d_mul_d, mul_zero, mul_zero, zero_mul]

/-- The ordinary rank-one module `F = 1`, `V = p`, `d = 0` realizes the relations. -/
def augmentation : RaynaudAlgebra p →ₐ[ℤ] ℤ :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (fun
    | frobenius => 1
    | verschiebung => (p : ℤ)
    | differential => 0), by
      intro x y h
      cases h <;> simp only [map_mul, map_natCast, map_zero, generator,
        FreeAlgebra.lift_ι_apply, one_mul, mul_one, mul_zero, zero_mul]⟩

/-- The quotient is nonzero: its augmentation preserves integer scalars. -/
instance : Nontrivial (RaynaudAlgebra p) :=
  (augmentation p).toRingHom.domain_nontrivial

#print axioms d_mul_V_pow_mul_F_pow_mul_d
#print axioms F_pow_mul_d_mul_V_pow
#print axioms augmentation

end RaynaudAlgebra
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
