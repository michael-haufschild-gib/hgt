import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularPhaseIdeals
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.KernelSectorArithmetic

/-!
# Separation of angular phases in reflected rows

The ideal of a reflected denominator is the product of the fixed conductor, row ideal
and slot ideal. Its angular character therefore separates into three bounded factors.
The opposite angular frequency character supplies a bounded column factor.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection CanonicalQuadraticSieve
open GaloisForLFunctions.FamilyContinuationTheory
namespace InverseReflectedPhase
noncomputable section
local notation "Eis" => Eisenstein.O

def angularIdealPhase (ℓ : ℕ) (I : Ideal Eis) : ℂ := idealPsiSix I ^ (2 * ℓ)

lemma angularIdealPhase_norm_le_one (ℓ : ℕ) (I : Ideal Eis) : ‖angularIdealPhase ℓ I‖ ≤ 1 := by
  rw [angularIdealPhase, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one I)

/-- Angular reflection changes the fixed conductor, row and slot by separate ideal phases. -/
theorem angular_reflected_denominator_phase (ℓ : ℕ)
    {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    angularCuspDenominatorPhase ℓ (c * ∏ i, (F.reflected K hK S).generator i) =
      angularIdealPhase ℓ (Ideal.span {c} * ∏ i, F.ideal i) *
        angularIdealPhase ℓ K * angularIdealPhase ℓ (∏ i, S.ideal i) := by
  rw [angularCuspDenominatorPhase_eq_idealPsiSix,
    ← Ideal.span_singleton_mul_span_singleton, PrimeFamily.product_span, F.reflected_product]
  simp only [angularIdealPhase, idealPsiSix_mul, mul_pow]
  ring

def angularCuspColumnPhase (ℓ : ℕ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  conj (elemPsiSix (fixedCuspArrayIndex u m n b)) ^ ℓ

lemma angularCuspColumnPhase_norm_le_one (ℓ : ℕ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖angularCuspColumnPhase ℓ u m n b‖ ≤ 1 := by
  rw [angularCuspColumnPhase, norm_pow, Complex.norm_conj]
  exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one _)

lemma angularCuspColumnPhase_full_index (ℓ : ℕ) (p : ThetaFullIndex) :
    angularCuspColumnPhase ℓ p.1 p.2.1 p.2.2.1.val p.2.2.2.val =
      conj (elemPsiSix (thetaFullFrequency p)) ^ ℓ := by
  rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
  rfl

end
end InverseReflectedPhase
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
