import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierNilpotence

/-!
# Logarithmic differentials and Cartier fixed forms

Cartier fixes every logarithmic differential `df/f`. On the actual
regular differential space its nilpotence leaves no nonzero fixed
forms. Hence `df/f` is everywhere regular exactly when `f` is a
Frobenius power in the same function field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis

/-- Cartier fixes the logarithmic differential of every function. -/
theorem squareKummerCoordinateCartier_logarithmic
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (f : SquareKummerField p s c b R) :
    squareKummerCoordinateCartier p s c b R
      (f⁻¹ • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) f) =
      f⁻¹ • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) f := by
  by_cases hf : f = 0
  · subst f
    rw [inv_zero, zero_smul, map_zero]
  · have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
    have hpow : f ^ p = f ^ (p - 1) * f :=
      (congrArg (fun j : ℕ => f ^ j) hp).symm.trans (pow_succ f (p - 1))
    have hmul : (f⁻¹) ^ p * f ^ (p - 1) = f⁻¹ := by
      rw [inv_pow, hpow, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hf), mul_one]
    calc
      _ = squareKummerCoordinateCartier p s c b R
          ((f⁻¹) ^ p • (f ^ (p - 1) •
            KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) f)) := by
        rw [smul_smul, hmul]
      _ = _ := by rw [squareKummerCoordinateCartier_frobenius_smul,
        squareKummerCoordinateCartier_normalization]

variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "G" => globalRegularDifferentials K L

/-- The only Cartier-fixed intrinsic regular differential is zero. -/
theorem primePowerKummerRegularCartier_fixed_iff (ω : G) :
    squareKummerRegularCartier p s c d r ω = ω ↔ ω = 0 := by
  constructor
  · intro hω
    have hfixed (j : ℕ) : (squareKummerRegularCartier p s c d r : G → G)^[j] ω = ω := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, hω]
    exact (hfixed _).symm.trans (primePowerKummerRegularCartier_nilpotent p d n r c ω)
  · rintro rfl
    exact map_zero _

/-- A logarithmic differential is globally regular exactly when its function is an actual Frobenius power. -/
theorem primePowerKummer_logarithmic_regular_iff (f : L) :
    f⁻¹ • KaehlerDifferential.D K L f ∈ globalRegularDifferentials K L ↔
      ∃ a : L, a ^ p = f := by
  rw [← squareKummer_differential_eq_zero_iff]
  constructor
  · intro hreg
    let ω : G := ⟨f⁻¹ • KaehlerDifferential.D K L f, hreg⟩
    have hfix : squareKummerRegularCartier p s c d r ω = ω :=
      Subtype.ext (squareKummerCoordinateCartier_logarithmic p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) f)
    have hz := congrArg Subtype.val
      ((primePowerKummerRegularCartier_fixed_iff p d n r c ω).mp hfix)
    by_cases hf : f = 0
    · rw [hf, map_zero]
    · exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hf)
  · intro hf
    rw [hf, smul_zero]
    exact Submodule.zero_mem _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
