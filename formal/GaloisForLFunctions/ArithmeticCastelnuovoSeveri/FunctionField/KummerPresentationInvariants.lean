import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExponentReduction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RegularDifferentialEquivalence
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerAffineNormalizationDefect

/-!
# Intrinsic genus and presentation-dependent normalization defect

Adding a multiple of the covering degree to the branch exponent preserves the
function field and its regular differential space. The affine normalization
defect nevertheless grows by an explicit positive amount. Consequently one
function field has plane presentations with arbitrarily large affine defect.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial

/-- Removing full covering-degree powers preserves actual global regular differentials. -/
def kummerExponentReductionRegularEquiv {K : Type*} [Field K]
    (c : Kˣ) (b R n : ℕ) :
    globalRegularDifferentials K (KummerBranchField c b R n) ≃ₗ[K]
      globalRegularDifferentials K (KummerBranchField c b (R % (n + 1)) n) :=
  globalRegularDifferentialEquiv ((kummerExponentReductionEquiv c b R n).restrictScalars K)

/-- Shifting the branch exponent by a covering-degree multiple preserves intrinsic genus. -/
theorem kummerExponentShift_genus_eq {K : Type*} [Field K]
    (c : Kˣ) (b R n k : ℕ) :
    Module.finrank K (globalRegularDifferentials K (KummerBranchField c b (R + k * (n + 1)) n)) =
      Module.finrank K (globalRegularDifferentials K (KummerBranchField c b R n)) :=
  globalRegularDifferential_finrank_eq ((kummerExponentShiftEquiv c b R n k).restrictScalars K)

variable (p : ℕ) [Fact p.Prime] (s d : ℕ) (c : (SquareConstantField p s)ˣ) (R k : ℕ)

private abbrev affineDefectModule (t : ℕ) :
    Module (SquareConstantField p s) (SquareKummerAffineDefect p s d c t) := inferInstance

attribute [local instance] affineDefectModule

/-- The affine normalization defect grows linearly along isomorphic Kummer presentations. -/
theorem squareKummerAffineDefect_shift_twice :
    2 * Module.finrank (SquareConstantField p s)
      (SquareKummerAffineDefect p s d c (R + k * (p ^ (s + 1) + 1))) =
    2 * Module.finrank (SquareConstantField p s) (SquareKummerAffineDefect p s d c R) +
      (p ^ (d + 1) - 1) * k * (p ^ (s + 1) + 1) * p ^ (s + 1) := by
  have hg : Nat.gcd (p ^ (s + 1) + 1) (R + k * (p ^ (s + 1) + 1)) =
      Nat.gcd (p ^ (s + 1) + 1) R := by
    rw [Nat.gcd_rec (p ^ (s + 1) + 1) (R + k * (p ^ (s + 1) + 1)),
      Nat.gcd_rec (p ^ (s + 1) + 1) R]
    congr 1
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, add_zero, Nat.mod_mod]
  have hnew := squareKummerAffineDefect_finrank_twice p s d c (R + k * (p ^ (s + 1) + 1))
  have hold := squareKummerAffineDefect_finrank_twice p s d c R
  rw [hg] at hnew
  have he : (p ^ (d + 1) - 1) *
      ((R + k * (p ^ (s + 1) + 1)) * p ^ (s + 1) + Nat.gcd (p ^ (s + 1) + 1) R) =
      (p ^ (d + 1) - 1) * (R * p ^ (s + 1) + Nat.gcd (p ^ (s + 1) + 1) R) +
      (p ^ (d + 1) - 1) * k * (p ^ (s + 1) + 1) * p ^ (s + 1) := by ring
  rw [he] at hnew
  omega

/-- One fixed Kummer function field has affine presentations of arbitrarily large defect. -/
theorem squareKummerAffineDefect_unbounded_same_field (M : ℕ) :
    ∃ R' : ℕ,
      Nonempty (SquareKummerField p s c (p ^ (d + 1) - 2) R' ≃ₐ[FractionRing (SquareConstantField p s)[X]]
        SquareKummerField p s c (p ^ (d + 1) - 2) R) ∧
      M < Module.finrank (SquareConstantField p s) (SquareKummerAffineDefect p s d c R') := by
  refine ⟨R + (2 * M + 1) * (p ^ (s + 1) + 1),
    ⟨kummerExponentShiftEquiv c (p ^ (d + 1) - 2) R (p ^ (s + 1)) (2 * M + 1)⟩, ?_⟩
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hQ : 0 < p ^ (s + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hpos : 0 < (p ^ (d + 1) - 1) * (p ^ (s + 1) + 1) * p ^ (s + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos _)) hQ
  have hinc : 2 * M + 1 ≤
      (p ^ (d + 1) - 1) * (2 * M + 1) * (p ^ (s + 1) + 1) * p ^ (s + 1) := by
    calc
      _ = 1 * (2 * M + 1) := (one_mul _).symm
      _ ≤ ((p ^ (d + 1) - 1) * (p ^ (s + 1) + 1) * p ^ (s + 1)) * (2 * M + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpos)
      _ = _ := by ring
  have h := squareKummerAffineDefect_shift_twice p s d c R (2 * M + 1)
  omega

#print axioms kummerExponentShift_genus_eq
#print axioms squareKummerAffineDefect_unbounded_same_field
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
