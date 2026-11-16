import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GroupAction.HermitianTranslationAction
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldTraceFibers

/-!
# Noncommuting automorphisms of the Hermitian function field

Every first coordinate occurs in a rational Hermitian point, using a
trace-one constant. A Frobenius-nonfixed first coordinate then gives
two noncommuting translations. Faithfulness transfers this obstruction
to actual constant-field automorphisms, including in characteristic two.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s
local notation "H" => HermitianKummerField p s
local notation "HK" => HermitianAffinePoint p s K

/-- Multiplying a trace-one element by a norm constructs a rational point with any prescribed first coordinate. -/
def hermitianAffinePointWithFirst (a : K) : HK := by
  refine ⟨(a, a ^ (Q + 1) * squareTraceOne p s), ?_⟩
  change (a ^ (Q + 1) * squareTraceOne p s) ^ Q +
    a ^ (Q + 1) * squareTraceOne p s = a ^ (Q + 1)
  rw [mul_pow, squareConstantField_norm_fixed, ← mul_add,
    ← squareFieldTrace_apply, squareTraceOne_trace, mul_one]

/-- The rational Hermitian translation group contains two noncommuting elements in every characteristic. -/
theorem hermitianTranslationGroup_exists_noncommuting : ∃ P U : HK, P * U ≠ U * P := by
  obtain ⟨t, ht⟩ := squareConstantField_exists_not_fixed p s
  let P := hermitianAffinePointWithFirst p s 1
  let U := hermitianAffinePointWithFirst p s t
  refine ⟨P, U, ?_⟩
  intro h
  have he := congrArg (fun T : HK => T.val.2) h
  change P.val.2 + U.val.2 + (1 : K) ^ Q * t =
    U.val.2 + P.val.2 + t ^ Q * 1 at he
  rw [one_pow, one_mul, mul_one, add_comm U.val.2 P.val.2] at he
  exact ht (add_left_cancel he).symm

/-- The actual Hermitian function field has noncommuting constant-field automorphisms. -/
theorem hermitianFieldAut_exists_noncommuting :
    ∃ σ τ : H ≃ₐ[K] H, σ * τ ≠ τ * σ := by
  obtain ⟨P, U, hPU⟩ := hermitianTranslationGroup_exists_noncommuting p s
  let F := hermitianTranslationFieldAutHom p s
  refine ⟨F P, F U, ?_⟩
  intro h
  apply hPU
  apply hermitianTranslationFieldAutHom_injective p s
  rw [map_mul, map_mul]
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
