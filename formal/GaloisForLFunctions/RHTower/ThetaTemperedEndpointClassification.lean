import GaloisForLFunctions.RHTower.ThetaTemperedGlobalJets

/-!
The original theta derivative annihilator, with its exact globally tempered
signed-jet classification. All carriers retain the original Schwartz topology.
-/

noncomputable section

open scoped SchwartzMap

namespace RHTower

/-- Canonical real-divisor coefficients of the actual inverse physical Fourier transform. -/
def thetaUnscaledTemperedLocalCoefficients (T : 𝓢'(ℝ, ℂ))
    (hT : T ∈ thetaUnscaledTemperedDerivativeAnnihilator) :
    ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ :=
  thetaXiTemperedLocalCoefficients (thetaPhysicalTemperedInversePullback T)
    ((thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T).mp hT)

/-- Every actual compact test recovers the canonical signed-jet functional. -/
theorem thetaUnscaledTemperedLocalCoefficients_compact_value (T : 𝓢'(ℝ, ℂ))
    (hT : T ∈ thetaUnscaledTemperedDerivativeAnnihilator) (φ : thetaSchwartzCompactCore) :
    thetaPhysicalTemperedInversePullback T (φ : 𝓢(ℝ, ℂ)) =
      thetaXiRawCompactJetFunctional (thetaUnscaledTemperedLocalCoefficients T hT) φ := by
  exact (thetaXiRawCompactJetFunctional_of_tempered
    (thetaPhysicalTemperedInversePullback T)
    ((thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T).mp hT)
    φ).symm

/-- The literal double finite derivative sum, using actual multiplicities and closed support. -/
theorem thetaUnscaledTemperedLocalCoefficients_compact_derivatives (T : 𝓢'(ℝ, ℂ))
    (hT : T ∈ thetaUnscaledTemperedDerivativeAnnihilator) (φ : thetaSchwartzCompactCore) :
    thetaPhysicalTemperedInversePullback T (φ : 𝓢(ℝ, ℂ)) =
      ∑ t ∈ thetaXiCompactTestZeros (φ : 𝓢(ℝ, ℂ)) φ.property,
        ∑ r : Fin (thetaRealXiMultiplicity t),
          thetaUnscaledTemperedLocalCoefficients T hT t r *
            ((-1 : ℂ) ^ (r : ℕ) * iteratedDeriv (r : ℕ) (φ : 𝓢(ℝ, ℂ)) t) := by
  rw [thetaUnscaledTemperedLocalCoefficients_compact_value T hT φ]
  exact thetaXiRawCompactJetFunctional_apply _ φ

/-- The canonical family obeys one joint bound in the original Schwartz seminorms. -/
theorem thetaUnscaledTemperedLocalCoefficients_jointBound (T : 𝓢'(ℝ, ℂ))
    (hT : T ∈ thetaUnscaledTemperedDerivativeAnnihilator) :
    thetaXiRawJetJointBound (thetaUnscaledTemperedLocalCoefficients T hT) := by
  exact thetaSchwartzCompactCoreJointBound_of_tempered _
    (thetaPhysicalTemperedInversePullback T)
    (thetaUnscaledTemperedLocalCoefficients_compact_value T hT)

/-- Exact all-source-derivative annihilation iff a unique globally tempered real jet family. -/
theorem thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_existsUnique_globalJets
    (T : 𝓢'(ℝ, ℂ)) :
    T ∈ thetaUnscaledTemperedDerivativeAnnihilator ↔
      ∃! a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ,
        thetaXiRawJetJointBound a ∧
          ∀ φ : thetaSchwartzCompactCore,
            thetaPhysicalTemperedInversePullback T (φ : 𝓢(ℝ, ℂ)) =
              thetaXiRawCompactJetFunctional a φ := by
  constructor
  · intro hT
    refine ⟨thetaUnscaledTemperedLocalCoefficients T hT,
      ⟨thetaUnscaledTemperedLocalCoefficients_jointBound T hT,
        thetaUnscaledTemperedLocalCoefficients_compact_value T hT⟩, ?_⟩
    intro a ha
    apply funext
    intro t
    exact (thetaXiRawCompactJetFunctional_extension_coefficients a
      (thetaPhysicalTemperedInversePullback T) ha.2 t).symm
  · rintro ⟨a, ⟨_, hL⟩, _⟩
    exact (thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T).mpr
      (thetaXiRawCompactJetFunctional_extension_mem_kernel a
        (thetaPhysicalTemperedInversePullback T) hL)

/-- Every admitted raw jet family has exactly one original source-annihilating extension. -/
theorem thetaXiRawJetJointBound_iff_existsUnique_sourceAnn_extension
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiRawJetJointBound a ↔ ∃! T : 𝓢'(ℝ, ℂ),
      T ∈ thetaUnscaledTemperedDerivativeAnnihilator ∧
        ∀ φ : thetaSchwartzCompactCore,
          thetaPhysicalTemperedInversePullback T (φ : 𝓢(ℝ, ℂ)) =
            thetaXiRawCompactJetFunctional a φ := by
  constructor
  · intro ha
    obtain ⟨Q, ⟨hQ, hL⟩, h_unique⟩ :=
      (thetaXiRawJetJointBound_iff_existsUnique_kernel_extension a).mp ha
    refine ⟨thetaPhysicalTemperedPullback Q,
      ⟨(thetaPhysicalTemperedPullback_mem_annihilator_iff_Xi_kernel Q).mpr hQ, ?_⟩, ?_⟩
    · intro φ
      simpa only [thetaPhysicalTemperedInversePullback_pullback] using hL φ
    · intro T hT
      have h_inverse : thetaPhysicalTemperedInversePullback T = Q :=
        h_unique (thetaPhysicalTemperedInversePullback T)
          ⟨(thetaUnscaledTemperedDerivativeAnnihilator_mem_iff_Xi_inverseFourier_kernel T).mp
            hT.1, hT.2⟩
      calc
        T = thetaPhysicalTemperedPullback (thetaPhysicalTemperedInversePullback T) :=
          (thetaPhysicalTemperedPullback_inversePullback T).symm
        _ = thetaPhysicalTemperedPullback Q := congrArg thetaPhysicalTemperedPullback h_inverse
  · rintro ⟨T, ⟨_, hL⟩, _⟩
    exact thetaSchwartzCompactCoreJointBound_of_tempered _
      (thetaPhysicalTemperedInversePullback T) hL

/-- The same raw coefficients characterize exactly one original source annihilator. -/
theorem thetaXiRawJetJointBound_iff_existsUnique_sourceAnn_coefficients
    (a : ∀ t : ℝ, Fin (thetaRealXiMultiplicity t) → ℂ) :
    thetaXiRawJetJointBound a ↔ ∃! T : 𝓢'(ℝ, ℂ),
      ∃ hT : T ∈ thetaUnscaledTemperedDerivativeAnnihilator,
        ∀ t : ℝ, thetaUnscaledTemperedLocalCoefficients T hT t = a t := by
  constructor
  · intro ha
    obtain ⟨T, ⟨hT, hL⟩, h_unique⟩ :=
      (thetaXiRawJetJointBound_iff_existsUnique_sourceAnn_extension a).mp ha
    refine ⟨T, ⟨hT, ?_⟩, ?_⟩
    · intro t
      exact thetaXiRawCompactJetFunctional_extension_coefficients a
        (thetaPhysicalTemperedInversePullback T) hL t
    · rintro S ⟨hS, h_coefficients⟩
      apply h_unique S
      refine ⟨hS, ?_⟩
      intro φ
      rw [thetaUnscaledTemperedLocalCoefficients_compact_value S hS φ]
      have h_family : thetaUnscaledTemperedLocalCoefficients S hS = a := funext h_coefficients
      rw [h_family]
  · rintro ⟨T, ⟨hT, h_coefficients⟩, _⟩
    have h_family : thetaUnscaledTemperedLocalCoefficients T hT = a := funext h_coefficients
    rw [← h_family]
    exact thetaUnscaledTemperedLocalCoefficients_jointBound T hT

end RHTower
