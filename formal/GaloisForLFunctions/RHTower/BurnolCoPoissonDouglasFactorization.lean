import GaloisForLFunctions.RHTower.BurnolCoPoissonDilationChannels
import GaloisForLFunctions.RHTower.HilbertDouglasFactorization

/-!
# Douglas factorization of Burnol's quotient dilation channels

The quotient-compressed bilateral holonomy is nonpositive exactly when the forward channel factors
contractively through the inverse channel.  This is the full infinite-dimensional Douglas theorem,
specialized to the actual extended-Sonine/co-Poisson channels.
-/

open Complex Real
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

/-- Negative compressed holonomy is exactly the Douglas Gram difference of the inverse and forward
co-Poisson quotient channels. -/
theorem neg_burnolCoPoissonCompressedHolonomy_eq_douglasGram
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    -burnolCoPoissonCompressedHolonomy b hb a ha r hr =
      burnolCoPoissonFullInverseChannel b hb a r hr ∘L
          burnolCoPoissonFullInverseChannelAdjoint b hb a ha r hr -
        burnolCoPoissonFullForwardChannel b hb a r hr ∘L
          burnolCoPoissonFullForwardChannelAdjoint b hb a ha r hr := by
  rw [burnolCoPoissonCompressedHolonomy_eq_fullChannel_gram_sub]
  exact neg_sub _ _

set_option maxHeartbeats 1000000 in
/-- **Exact reverse Douglas implication.**  Nonpositive compressed holonomy supplies the
contractive right factor between the actual forward and inverse co-Poisson quotient channels. -/
theorem exists_burnolCoPoisson_contractive_factorization_of_neg_isPositive
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r)
    (hneg : (-burnolCoPoissonCompressedHolonomy b hb a ha r hr).IsPositive) :
    ∃ C : soninExtendedSpace a →L[ℂ] soninExtendedSpace a,
      ‖C‖ ≤ 1 ∧
        burnolCoPoissonFullForwardChannel b hb a r hr =
          burnolCoPoissonFullInverseChannel b hb a r hr ∘L C := by
  letI : Fact (0 < a) := ⟨ha⟩
  let hComplete : CompleteSpace (soninExtendedSpace a) :=
    (isClosed_soninExtendedSpace ha).completeSpace_coe
  letI : CompleteSpace (soninExtendedSpace a) := hComplete
  let A : soninExtendedSpace a →L[ℂ] evenSubspace :=
    burnolCoPoissonFullForwardChannel b hb a r hr
  let B : soninExtendedSpace a →L[ℂ] evenSubspace :=
    burnolCoPoissonFullInverseChannel b hb a r hr
  let Astar : evenSubspace →L[ℂ] soninExtendedSpace a :=
    burnolCoPoissonFullForwardChannelAdjoint b hb a ha r hr
  let Bstar : evenSubspace →L[ℂ] soninExtendedSpace a :=
    burnolCoPoissonFullInverseChannelAdjoint b hb a ha r hr
  have hgram : (B ∘L Bstar - A ∘L Astar).IsPositive := by
    have heq := neg_burnolCoPoissonCompressedHolonomy_eq_douglasGram
      b hb a ha r hr
    change -burnolCoPoissonCompressedHolonomy b hb a ha r hr =
      B ∘L Bstar - A ∘L Astar at heq
    exact heq ▸ hneg
  have hAstar : ContinuousLinearMap.adjoint (𝕜 := ℂ)
      (E := soninExtendedSpace a) (F := evenSubspace) A = Astar := by
    exact adjoint_burnolCoPoissonFullForwardChannel b hb a ha r hr
  have hBstar : ContinuousLinearMap.adjoint (𝕜 := ℂ)
      (E := soninExtendedSpace a) (F := evenSubspace) B = Bstar := by
    exact adjoint_burnolCoPoissonFullInverseChannel b hb a ha r hr
  exact @exists_contractive_rightFactor_of_explicitAdjoint_gram_isPositive
    (soninExtendedSpace a) evenSubspace
    (inferInstance : NormedAddCommGroup (soninExtendedSpace a))
    (inferInstance : InnerProductSpace ℂ (soninExtendedSpace a)) hComplete
    (inferInstance : NormedAddCommGroup evenSubspace)
    (inferInstance : InnerProductSpace ℂ evenSubspace)
    (inferInstance : CompleteSpace evenSubspace)
    A B Astar Bstar hAstar hBstar hgram

/-- **Douglas equivalence for the actual quotient channels.** -/
theorem burnolCoPoissonCompressedHolonomy_neg_isPositive_iff_contractive_factorization
    (b : ℝ) (hb : 0 < b) (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    (-burnolCoPoissonCompressedHolonomy b hb a ha r hr).IsPositive ↔
      ∃ C : soninExtendedSpace a →L[ℂ] soninExtendedSpace a,
        ‖C‖ ≤ 1 ∧
          burnolCoPoissonFullForwardChannel b hb a r hr =
            burnolCoPoissonFullInverseChannel b hb a r hr ∘L C := by
  constructor
  · exact exists_burnolCoPoisson_contractive_factorization_of_neg_isPositive
      b hb a ha r hr
  · rintro ⟨C, hC, hfactor⟩
    exact burnolCoPoissonCompressedHolonomy_neg_isPositive_of_contractive_factorization
      b hb a ha r hr C hC hfactor

end RHTower
