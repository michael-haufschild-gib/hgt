import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierIterates
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RegularDifferentialEquivalence

/-!
# Cartier iterates on intrinsic regular differentials

Every Cartier iterate restricts to the actual global regular space.
The restrictions retain their Frobenius scalar law and naturality
under constant-field automorphisms.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "G" => globalRegularDifferentials K L
local notation "I" => squareKummerCartierIterate p s c (p ^ (d + 1) - 2)
  (kummerExponent (p ^ (d + 1)) r)

/-- Each Cartier iterate restricts to an additive endomorphism of intrinsic regular differentials. -/
def squareKummerRegularCartierIterate (e : ℕ) : G →+ G where
  toFun ω := ⟨I e ω.val, squareKummerCartierIterate_global_regular p s c d r e ω.val ω.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' ω η := Subtype.ext (map_add _ _ _)

/-- The restricted iterate extracts `p^e`th powers of constants. -/
theorem squareKummerRegularCartierIterate_frobenius_smul (e : ℕ) (a : K) (ω : G) :
    squareKummerRegularCartierIterate p s c d r e (a ^ (p ^ e) • ω) =
      a • squareKummerRegularCartierIterate p s c d r e ω := by
  apply Subtype.ext
  change I e ((a ^ (p ^ e)) • ω.val) = a • I e ω.val
  rw [← IsScalarTower.algebraMap_smul L (a ^ (p ^ e)), map_pow,
    squareKummerCartierIterate_frobenius_smul, IsScalarTower.algebraMap_smul]

/-- The restricted iterate preserves scalar lines over the full constant field. -/
theorem squareKummerRegularCartierIterate_scalar_line (e : ℕ) (a : K) (ω : G) :
    ∃ a' : K, squareKummerRegularCartierIterate p s c d r e (a • ω) =
      a' • squareKummerRegularCartierIterate p s c d r e ω := by
  obtain ⟨a', ha'⟩ := squareKummerCartierIterate_scalar_line p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) e a ω.val
  exact ⟨a', Subtype.ext ha'⟩

/-- Restricted Cartier iterates commute with all constant-field automorphisms. -/
theorem squareKummerRegularCartierIterate_aut (e : ℕ) (σ : L ≃ₐ[K] L) (ω : G) :
    globalRegularDifferentialEquiv σ (squareKummerRegularCartierIterate p s c d r e ω) =
      squareKummerRegularCartierIterate p s c d r e (globalRegularDifferentialEquiv σ ω) := by
  apply Subtype.ext
  exact squareKummerCartierIterate_map p s c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) e σ.toAlgHom ω.val

/-- Repeating a restricted Cartier block agrees with the corresponding ambient Cartier iterate. -/
theorem squareKummerRegularCartierIterate_iterate (e n : ℕ) (ω : G) :
    (((squareKummerRegularCartierIterate p s c d r e : G → G)^[n]) ω).val = I (e * n) ω.val := by
  rw [squareKummerCartierIterate_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change I e (((squareKummerRegularCartierIterate p s c d r e : G → G)^[n]) ω).val =
      I e ((I e : _ → _)^[n] ω.val)
    rw [ih]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
