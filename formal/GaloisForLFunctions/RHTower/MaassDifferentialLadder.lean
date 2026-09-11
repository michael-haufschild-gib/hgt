import GaloisForLFunctions.RHTower.MaassSmoothDifferentialOperators
import GaloisForLFunctions.RHTower.SelbergExceptionalSphericalModel

/-! The actual Maass differential ladders and their nonvanishing. -/

namespace GaloisForLFunctions.RHTower.MaassSmooth
noncomputable section
open UpperHalfPlane

/-- Repeated raising, with its actual changing weight. -/
def raised (f : FunctionSpace) : ℕ → FunctionSpace
  | 0 => f
  | n+1 => raise (n : ℤ) (raised f n)

/-- Repeated lowering, with its actual changing weight. -/
def lowered (f : FunctionSpace) : ℕ → FunctionSpace
  | 0 => f
  | n+1 => lower (-(n : ℤ)) (lowered f n)

@[simp] theorem raised_zero (f : FunctionSpace) : raised f 0 = f := rfl
@[simp] theorem raised_succ (f : FunctionSpace) (n : ℕ) :
    raised f (n+1) = raise (n : ℤ) (raised f n) := rfl
@[simp] theorem lowered_zero (f : FunctionSpace) : lowered f 0 = f := rfl
@[simp] theorem lowered_succ (f : FunctionSpace) (n : ℕ) :
    lowered f (n+1) = lower (-(n : ℤ)) (lowered f n) := rfl

/-- The opposite spherical factorization follows from the actual zero-weight commutator. -/
theorem raise_lower_zero (f : FunctionSpace) : raise (-1) (lower 0 f) = -laplacian f := by
  have h := raise_lower_comm 0 f
  simp only [Int.cast_zero, mul_zero, zero_smul, zero_sub, zero_add] at h
  rw [sub_eq_zero] at h
  exact h.trans (lower_raise_zero f)

/-- Lowering an actual raised Maass form has the coefficient forced by its Laplace eigenvalue. -/
theorem lower_raised {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    lower ((n : ℤ)+1) (raised (ofMaass f) (n+1)) =
      -((lam : ℂ) + (n : ℂ) * ((n : ℂ)+1)) • raised (ofMaass f) n := by
  induction n with
  | zero => simpa using lower_raise_ofMaass f
  | succ n ih =>
      have hc := raise_lower_comm ((n : ℤ)+1) (raised (ofMaass f) (n+1))
      have hi : (n : ℤ)+1-1 = n := by omega
      rw [hi] at hc
      have hstep :
          lower (((n+1 : ℕ) : ℤ)+1) (raised (ofMaass f) (n+1+1)) =
            raise (n : ℤ) (lower ((n : ℤ)+1) (raised (ofMaass f) (n+1))) -
              (2 * (((n : ℤ)+1 : ℤ) : ℂ)) • raised (ofMaass f) (n+1) := by
        apply (eq_sub_iff_add_eq).mpr
        simpa only [raised_succ, Nat.cast_add, Nat.cast_one] using
          (add_comm _ _).trans (sub_eq_iff_eq_add.mp hc).symm
      rw [hstep, ih, map_smul, ← raised_succ]
      push_cast
      module

/-- Raising an actual lowered Maass form has the same forced coefficient. -/
theorem raise_lowered {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    raise (-((n : ℤ)+1)) (lowered (ofMaass f) (n+1)) =
      -((lam : ℂ) + (n : ℂ) * ((n : ℂ)+1)) • lowered (ofMaass f) n := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_add, neg_zero, lowered_succ, lowered_zero,
        zero_mul, add_zero, raise_lower_zero, laplacian_ofMaass]
      module
  | succ n ih =>
      have hc := raise_lower_comm (-((n : ℤ)+1)) (lowered (ofMaass f) (n+1))
      have hi : -((n : ℤ)+1)+1 = -(n : ℤ) := by omega
      rw [hi, ih, map_smul] at hc
      have hstep :
          raise (-(((n+1 : ℕ) : ℤ)+1)) (lowered (ofMaass f) (n+1+1)) =
            (2 * (-((n : ℤ)+1) : ℤ) : ℂ) • lowered (ofMaass f) (n+1) +
              (-((lam : ℂ) + (n : ℂ) * ((n : ℂ)+1))) • lowered (ofMaass f) (n+1) := by
        have hidx : -((n : ℤ)+1)-1 = -(((n+1 : ℕ) : ℤ)+1) := by omega
        rw [hidx] at hc
        simpa only [lowered_succ, Nat.cast_add, Nat.cast_one, Int.cast_mul, Int.cast_ofNat] using
          sub_eq_iff_eq_add.mp hc
      rw [hstep]
      push_cast
      module

private theorem ladderCoefficient_ne_zero (lam : SelbergExceptionalEigenvalue) (n : ℕ) :
    -((lam.1 : ℂ) + (n : ℂ) * ((n : ℂ)+1)) ≠ 0 := by
  have hp : 0 < lam.1 + (n : ℝ) * ((n : ℝ)+1) :=
    add_pos_of_pos_of_nonneg lam.2.1 (mul_nonneg (Nat.cast_nonneg n) (by positivity))
  apply neg_ne_zero.mpr
  exact_mod_cast ne_of_gt hp

/-- No positive-direction Maass derivative in the complementary interval vanishes. -/
theorem raised_ne_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : raised (ofMaass f) n ≠ 0 := by
  induction n with
  | zero => exact ofMaass_ne_zero f
  | succ n ih =>
      intro hz
      have h := lower_raised f n
      rw [hz, map_zero] at h
      exact ih ((smul_eq_zero.mp h.symm).resolve_left (ladderCoefficient_ne_zero lam n))

/-- No negative-direction Maass derivative in the complementary interval vanishes. -/
theorem lowered_ne_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : lowered (ofMaass f) n ≠ 0 := by
  induction n with
  | zero => exact ofMaass_ne_zero f
  | succ n ih =>
      intro hz
      have h := raise_lowered f n
      rw [hz, map_zero] at h
      exact ih ((smul_eq_zero.mp h.symm).resolve_left (ladderCoefficient_ne_zero lam n))

/-- Lower a weight `2n` function back to weight zero using the actual differential operators. -/
def lowerToZero : ℕ → Module.End ℂ FunctionSpace
  | 0 => 1
  | n+1 => lowerToZero n * lower ((n : ℤ)+1)

/-- Raise a weight `-2n` function back to weight zero using the actual differential operators. -/
def raiseToZero : ℕ → Module.End ℂ FunctionSpace
  | 0 => 1
  | n+1 => raiseToZero n * raise (-((n : ℤ)+1))

/-- The exact return scalar for every positive Maass ladder. -/
theorem lowerToZero_raised {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    lowerToZero n (raised (ofMaass f) n) =
      (∏ j ∈ Finset.range n, -((lam : ℂ) + (j : ℂ)*((j : ℂ)+1))) • ofMaass f := by
  induction n with
  | zero => simp only [lowerToZero, raised_zero, Finset.range_zero, Finset.prod_empty,
      one_smul, Module.End.one_apply]
  | succ n ih =>
      rw [lowerToZero, Module.End.mul_apply, lower_raised, map_smul, ih,
        Finset.prod_range_succ, smul_smul]
      congr 1
      exact mul_comm _ _

/-- The exact return scalar for every negative Maass ladder. -/
theorem raiseToZero_lowered {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    raiseToZero n (lowered (ofMaass f) n) =
      (∏ j ∈ Finset.range n, -((lam : ℂ) + (j : ℂ)*((j : ℂ)+1))) • ofMaass f := by
  induction n with
  | zero => simp only [raiseToZero, lowered_zero, Finset.range_zero, Finset.prod_empty,
      one_smul, Module.End.one_apply]
  | succ n ih =>
      rw [raiseToZero, Module.End.mul_apply, raise_lowered, map_smul, ih,
        Finset.prod_range_succ, smul_smul]
      congr 1
      exact mul_comm _ _


end
end GaloisForLFunctions.RHTower.MaassSmooth
