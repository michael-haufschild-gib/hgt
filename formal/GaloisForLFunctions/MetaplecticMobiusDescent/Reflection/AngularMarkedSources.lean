import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularFiniteReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.PoolPrimeFamilies

/-!
# Angular twists of marked arithmetic sources

Angular twisting commutes with row characters and fixed-factor extraction. The actual
marked completed source consequently joins the same free prime family, with its angular
character outside the finite coefficient that undergoes Fourier inversion.
-/

open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection CanonicalQuadraticSieve
open InverseMoment
noncomputable section
local notation "Eis" => Eisenstein.O

lemma angularSourceTwist_mul (k : ℕ) (Ψ χ : Eis →* ℂ) :
    angularSourceTwist k (Ψ*χ) = angularSourceTwist k Ψ*χ := by
  unfold angularSourceTwist
  ac_rfl

lemma angularSourceTwist_mul_left (k : ℕ) (Ψ χ : Eis →* ℂ) :
    χ*angularSourceTwist k Ψ = angularSourceTwist k (χ*Ψ) := by
  unfold angularSourceTwist
  ac_rfl

namespace CanonicalRowCompletion
lemma rowTwist_angularSourceTwist (k : ℕ) (Ψ : Eis →* ℂ) (m f z : Eis) :
    rowTwist (angularSourceTwist k Ψ) m f z = angularSourceTwist k (rowTwist Ψ m f z) := by
  unfold rowTwist angularSourceTwist
  ac_rfl

lemma GoodMaskRowData.fixedFactor_angularSourceTwist (k : ℕ) {m f z : Eis}
    (D : GoodMaskRowData m f z) (Ψ : Eis →* ℂ) (Q : Ideal Eis) :
    D.fixedFactor (angularSourceTwist k Ψ) Q = angularSourceTwist k (D.fixedFactor Ψ Q) := by
  unfold GoodMaskRowData.fixedFactor angularSourceTwist
  ac_rfl
end CanonicalRowCompletion

namespace InverseReflectedPhase
/-- Joining the actual marked row keeps angular twisting outside its finite fixed factor. -/
theorem angular_actual_marked_row_eq_joined (k : ℕ) {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : lambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) :
    let Q₀ := Q*Ideal.span {(72:Eis)}
    let G := (freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S
    let j := Sum.elim
      (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ => 0)
    markedCompletedT (angularSourceTwist k (rowTwist Ψ m f z)) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
      markedCompletedT (angularSourceTwist k
        (D.fixedFactor Ψ Q*unmarkedSexticTwist G.generator G.generator_good j markedSumSlots))
        W X (fun A => ∏ i∈markedSumSlots, if Ideal.span {G.generator i}∣A then (1:ℂ) else 0) := by
  simpa only [rowTwist_angularSourceTwist,GoodMaskRowData.fixedFactor_angularSourceTwist,
    angularSourceTwist_mul] using
    actual_marked_row_eq_joined D S (angularSourceTwist k Ψ) Q hmLam hm2 W X
end InverseReflectedPhase

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
