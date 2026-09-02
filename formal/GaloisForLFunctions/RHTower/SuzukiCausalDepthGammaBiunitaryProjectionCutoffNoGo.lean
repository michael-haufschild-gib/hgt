import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaProjectionCutoffAnomalyNoGo
import GaloisForLFunctions.RHTower.SoninApertureAreaRigidity

/-!
# Biunitary source-motion no-go for the causal-depth Gamma feature

The projection-cutoff capacity law forces every successful Suzuki transition-core reporter to
carry Hilbert--Schmidt source energy growing at least linearly on the cofinal mesh.  Arbitrary
left and right unitary motion cannot create that energy: it preserves the complete singular-value
profile, hence the squared Hilbert--Schmidt norm, exactly.

Consequently no moving source in the full biunitary orbit of one fixed Hilbert--Schmidt feature,
combined with any moving orthogonal cutoff, can supply the lower-semibounded rectangular Ward
premise that implies RH.  Specializing to the actual causal-depth Gamma feature kills all
source-faithful unitary, phase, basis, and shared-plane reorientations before cutoff.  No
regularity, convergence, rank, nesting, or relation between the two unitary families is assumed.

All statements are unconditional and use no RH premise, zero-location information, computation,
or added axiom.
-/

open Complex Filter ContinuousLinearMap
open scoped Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Independent unitary motion on the target and source legs of one Hilbert--Schmidt feature. -/
def suzukiBiunitarySourceTransport
    (F : H →L[ℂ] H) (u v : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (u : H →L[ℂ] H) ∘L F ∘L (v.symm : H →L[ℂ] H)

/-- Biunitary motion preserves the Hilbert--Schmidt class. -/
theorem suzukiBiunitarySourceTransport_isHilbertSchmidt
    {F : H →L[ℂ] H} (hF : IsHilbertSchmidt F)
    (u v : H ≃ₗᵢ[ℂ] H) :
    IsHilbertSchmidt (suzukiBiunitarySourceTransport F u v) := by
  exact (hF.comp_right (v.symm : H →L[ℂ] H)).comp_left
    (u : H →L[ℂ] H)

/-- **Singular-value rigidity.** Independent unitary motion on both legs preserves the complete
squared Hilbert--Schmidt energy. -/
theorem hsNormSq_suzukiBiunitarySourceTransport_eq
    {F : H →L[ℂ] H} (hF : IsHilbertSchmidt F)
    (u v : H ≃ₗᵢ[ℂ] H) :
    hsNormSq (suzukiBiunitarySourceTransport F u v) = hsNormSq F := by
  unfold suzukiBiunitarySourceTransport
  rw [hsNormSq_comp_left_eq_of_norm_map
    (hF.comp_right (v.symm : H →L[ℂ] H))
    (u : H →L[ℂ] H) (fun x => u.norm_map x)]
  exact hsNormSq_comp_right_linearIsometryEquiv_symm hF v

/-- Every arbitrarily moving biunitary orbit of one fixed Hilbert--Schmidt source has sublinear
energy on the transition-core mesh. -/
theorem suzukiBiunitarySourceTransport_projectionCutoffSourceHSEnergySublinear
    {F : H →L[ℂ] H} (hF : IsHilbertSchmidt F)
    (u v : ℕ → H ≃ₗᵢ[ℂ] H) :
    SuzukiProjectionCutoffSourceHSEnergySublinear
      (fun N => suzukiBiunitarySourceTransport F (u N) (v N)) := by
  rw [SuzukiProjectionCutoffSourceHSEnergySublinear]
  have heq :
      (fun n : ℕ =>
        hsNormSq
            (suzukiBiunitarySourceTransport F (u (8 * n)) (v (8 * n))) /
          (n : ℝ)) =
      fun n : ℕ => hsNormSq F / (n : ℝ) := by
    funext n
    rw [hsNormSq_suzukiBiunitarySourceTransport_eq hF]
  rw [heq]
  exact Tendsto.div_atTop tendsto_const_nhds
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- **Biunitary projection-cutoff route kill.** No moving source with fixed singular values,
followed by arbitrary moving orthogonal cutoffs, can supply the semibounded rectangular Ward
premise for the positive Suzuki transition core. -/
theorem no_fixedBiunitaryOrbit_projectionCutoff_rectangularWardProducer :
    ¬ ∃ (L : ℝ) (F : H →L[ℂ] H)
      (u v : ℕ → H ≃ₗᵢ[ℂ] H) (Q : ℕ → H →L[ℂ] H) (lower : ℝ),
      IsHilbertSchmidt F ∧
      (∀ N, adjoint (Q N) = Q N) ∧
      (∀ N, Q N * Q N = Q N) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiProjectionCutoffCommutatorAnomaly
              (fun M => suzukiBiunitarySourceTransport F (u M) (v M)) Q N)
          (8 * n) := by
  rintro ⟨L, F, u, v, Q, lower, hF, hQ, hQ2, hlower⟩
  apply no_sublinear_hilbertSchmidt_projectionCutoff_rectangularWardProducer
    (H := H)
  exact ⟨L, (fun N => suzukiBiunitarySourceTransport F (u N) (v N)), Q, lower,
    (fun N => suzukiBiunitarySourceTransport_isHilbertSchmidt hF (u N) (v N)),
    hQ, hQ2,
    suzukiBiunitarySourceTransport_projectionCutoffSourceHSEnergySublinear hF u v,
    hlower⟩

/-- **Actual-source specialization.** Arbitrary biunitary motion of the canonical causal-depth
Gamma feature, even before an arbitrary moving orthogonal cutoff, cannot be a Suzuki Ward
producer. -/
theorem no_canonicalCausalDepthGamma_biunitary_projectionCutoff_rectangularWardProducer :
    ¬ ∃ (L : ℝ)
      (u v : ℕ → SuzukiCausalDepthGammaTraceL2 ≃ₗᵢ[ℂ]
        SuzukiCausalDepthGammaTraceL2)
      (Q : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2) (lower : ℝ),
      (∀ N, adjoint (Q N) = Q N) ∧
      (∀ N, Q N * Q N = Q N) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiProjectionCutoffCommutatorAnomaly
              (fun M => suzukiBiunitarySourceTransport
                suzukiCanonicalCausalDepthGammaFeatureOperator (u M) (v M)) Q N)
          (8 * n) := by
  rintro ⟨L, u, v, Q, lower, hQ, hQ2, hlower⟩
  apply no_fixedBiunitaryOrbit_projectionCutoff_rectangularWardProducer
    (H := SuzukiCausalDepthGammaTraceL2)
  exact ⟨L, suzukiCanonicalCausalDepthGammaFeatureOperator, u, v, Q, lower,
    suzukiCanonicalCausalDepthGammaFeatureOperator_isHilbertSchmidt,
    hQ, hQ2, hlower⟩

end

end RHTower
