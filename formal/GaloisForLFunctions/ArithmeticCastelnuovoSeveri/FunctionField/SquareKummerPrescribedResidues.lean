import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionRamification

/-!
# Normalized valuations with prescribed radical residue

The residue of a nonzero radical is a constant root of its defining value.
Multiplying the radical by a constant root of unity changes that residue
to any prescribed root. Transporting the normalized adic valuation by this
actual field automorphism preserves its normalization and its rational base.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (b R : ℕ)
local notation "N" => p ^ (s + 1) + 1
local notation "L" => SquareKummerExtensionField p s E c b R
local notation "B" => SquareKummerExtensionNormalization p s E c b R
local notation "F" => FractionRing E[X]
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))

/-- A radical automorphism moves the residue at an actual prime to any specified nonzero root. -/
theorem squareKummerExtension_exists_aut_radical_residue
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c b R).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    ∃ σ : L ≃ₐ[F] L, w.valuation L (σ z - algebraMap E L β) < 1 := by
  obtain ⟨γ, hγpow, hγclose⟩ :=
    squareKummerExtension_exists_radical_residue p s E c b R x β hβ hpow w
  have hγ : γ ≠ 0 := by
    intro h0
    have hz := hγpow.symm.trans (by rw [h0, zero_pow (Nat.succ_ne_zero _)])
    exact pow_ne_zero N hβ (hpow.trans hz)
  let ξ : Eˣ := Units.mk0 (β / γ) (div_ne_zero hβ hγ)
  have hξ : ξ ∈ rootsOfUnity N E := by
    rw [mem_rootsOfUnity]
    apply Units.ext
    change (β / γ) ^ N = 1
    rw [div_pow, hpow, hγpow, div_self (by rw [← hpow]; exact pow_ne_zero N hβ)]
  let ζ : rootsOfUnity N E := ⟨ξ, hξ⟩
  let σ := squareKummerExtensionAutEquiv p s E c b R ζ
  refine ⟨σ, ?_⟩
  have hid : σ z - algebraMap E L β =
      algebraMap E L (β / γ) * (z - algebraMap E L γ) := by
    rw [squareKummerExtensionAutEquiv_root]
    change algebraMap E L (β / γ) * z - algebraMap E L β = _
    rw [mul_sub, ← map_mul, div_mul_cancel₀ β hγ]
  rw [hid, map_mul, heightOne_valuation_constant w (β / γ) (div_ne_zero hβ hγ), one_mul]
  exact hγclose

/-- Every soluble nonzero fiber admits a normalized valuation with the specified radical residue. -/
theorem squareKummerExtension_exists_prescribed_valuation
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c b R).eval x) :
    ∃ (w : HeightOneSpectrum B) (V : Valuation L (WithZero (Multiplicative ℤ))),
      w.asIdeal.LiesOver (Ideal.span {X - C x}) ∧ Function.Surjective V ∧
      (∀ f : E[X], V (algebraMap E[X] L f) = w.valuation L (algebraMap E[X] L f)) ∧
      V (z - algebraMap E L β) < 1 := by
  obtain ⟨w, hw⟩ := squareKummerExtension_exists_primeAbove p s E c b R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x))
  change w.asIdeal.LiesOver (Ideal.span {X - C x}) at hw
  letI := hw
  obtain ⟨σ, hσ⟩ := squareKummerExtension_exists_aut_radical_residue p s E c b R x β hβ hpow w
  let V := (w.valuation L).comap σ.toRingHom
  refine ⟨w, V, hw, (w.valuation_surjective L).comp σ.surjective, ?_, ?_⟩
  · intro f
    change w.valuation L (σ (algebraMap E[X] L f)) = _
    rw [IsScalarTower.algebraMap_apply E[X] F L, σ.commutes]
  · change w.valuation L (σ (z - algebraMap E L β)) < 1
    rw [map_sub, IsScalarTower.algebraMap_apply E F L, σ.commutes,
      ← IsScalarTower.algebraMap_apply E F L]
    exact hσ

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
