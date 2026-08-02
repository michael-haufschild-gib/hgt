import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaUnitPeriod
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDifference

/-!
# The pointed incidence phase of the elliptic-gamma source boundary

Fix an order-one elliptic gamma source whose two periods are rationally independent together with
the unit period, and let `F` be its logarithmic derivative.  Consider the germs solving the same
structural boundary: the unit period together with the two structural difference equations of `F`.

Every solution differs from `F` by a germ fixed by all three translations, hence by a constant, so
the solution set is exactly the coset `F + ℂ` — an affine line over the constants.  None of its
members is differentially algebraic, because a differentially algebraic solution would make `F`
itself differentially algebraic.

Thus the differentially algebraic incidence fibre is empty while the ambient meromorphic one is a
constant torsor, singled out to `F` by any pointing.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ## The structural boundary problem -/

/-- Germs with the same unit period and the same structural differences as the source. -/
def ellipticGammaBoundarySolutions (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    Set (meroField (Set.univ : Set ℂ)) :=
  {G | addTranslationMeroEquiv 1 G = G ∧
    ∀ i, meroShiftDiff (τ i) G =
      meroShiftDiff (τ i) (multipleEllipticGammaLogDerivMero τ hτ)}

theorem multipleEllipticGammaLogDerivMero_mem_boundarySolutions
    (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivMero τ hτ ∈ ellipticGammaBoundarySolutions τ hτ :=
  ⟨addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero τ hτ, fun _ => rfl⟩

/-- The three source generators of the boundary problem. -/
def ellipticGammaSourceGenerators (τ : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ellipticGammaSourcePeriods (τ 0) (τ 1)

theorem ellipticGammaSourceGenerators_apply (τ : Fin 2 → ℂ) :
    ellipticGammaSourceGenerators τ 0 = 1 ∧
      ellipticGammaSourceGenerators τ 1 = τ 0 ∧
      ellipticGammaSourceGenerators τ 2 = τ 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## The solution set is a constant torsor -/

/-- **Solutions differ from the source by a constant.** -/
theorem exists_constant_of_mem_boundarySolutions
    (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ 0) (τ 1)))
    {G : meroField (Set.univ : Set ℂ)} (hG : G ∈ ellipticGammaBoundarySolutions τ hτ) :
    ∃ c : ℂ, G = multipleEllipticGammaLogDerivMero τ hτ +
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  classical
  set F := multipleEllipticGammaLogDerivMero τ hτ with hF
  obtain ⟨hone, hdiff⟩ := hG
  have hfixed : JointFixed
      (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods (τ 0) (τ 1))) (G - F) := by
    intro i
    show addTranslationMeroEquiv (ellipticGammaSourcePeriods (τ 0) (τ 1) i) (G - F) = G - F
    fin_cases i
    · show addTranslationMeroEquiv (1 : ℂ) (G - F) = G - F
      rw [map_sub, hone, hF, addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero]
    · show addTranslationMeroEquiv (τ 0) (G - F) = G - F
      have h0 := hdiff 0
      rw [meroShiftDiff, meroShiftDiff] at h0
      rw [map_sub]
      have : addTranslationMeroEquiv (τ 0) G - G =
          addTranslationMeroEquiv (τ 0) F - F := h0
      have hcalc : addTranslationMeroEquiv (τ 0) G - addTranslationMeroEquiv (τ 0) F =
          G - F := by
        have := sub_eq_sub_iff_sub_eq_sub.mp this
        linear_combination (norm := abel) this
      exact hcalc
    · show addTranslationMeroEquiv (τ 1) (G - F) = G - F
      have h1 := hdiff 1
      rw [meroShiftDiff, meroShiftDiff] at h1
      rw [map_sub]
      have : addTranslationMeroEquiv (τ 1) G - G =
          addTranslationMeroEquiv (τ 1) F - F := h1
      have hcalc : addTranslationMeroEquiv (τ 1) G - addTranslationMeroEquiv (τ 1) F =
          G - F := by
        have := sub_eq_sub_iff_sub_eq_sub.mp this
        linear_combination (norm := abel) this
      exact hcalc
  obtain ⟨c, hc⟩ :=
    (rankThree_generator_jointFixed_iff_constant _ hindep (G - F)).mp hfixed
  refine ⟨c, ?_⟩
  have hcc : algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = G - F := hc
  rw [hcc]
  abel

/-- **The solution set is exactly the constant coset of the source.** -/
theorem boundarySolutions_eq_constantCoset
    (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ 0) (τ 1))) :
    ellipticGammaBoundarySolutions τ hτ =
      {G | ∃ c : ℂ, G = multipleEllipticGammaLogDerivMero τ hτ +
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) c} := by
  ext G
  constructor
  · exact fun hG => exists_constant_of_mem_boundarySolutions τ hτ hindep hG
  · rintro ⟨c, rfl⟩
    refine ⟨?_, fun i => ?_⟩
    · rw [map_add, addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero,
        addTranslationMeroEquiv_algebraMap_complex]
    · rw [meroShiftDiff, meroShiftDiff, map_add,
        addTranslationMeroEquiv_algebraMap_complex]
      abel

/-! ## The two incidence fibres -/

/-- **The differentially algebraic incidence fibre is empty.**  No solution of the structural
boundary problem is differentially algebraic. -/
theorem not_differentialAlgebraicOver_of_mem_boundarySolutions
    (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ 0) (τ 1)))
    {G : meroField (Set.univ : Set ℂ)} (hG : G ∈ ellipticGammaBoundarySolutions τ hτ) :
    ¬ DifferentialAlgebraicOver (RatFunc ℂ) G := by
  intro hDA
  obtain ⟨c, rfl⟩ := exists_constant_of_mem_boundarySolutions τ hτ hindep hG
  have hconst : DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) :=
    differentialAlgebraicOver_algebraMap_complex c
  have hF : DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivMero τ hτ) := by
    have := differentialAlgebraicOver_sub hDA hconst
    simpa using this
  have hminor : MultipleEllipticGammaHasRankThreeMinor τ :=
    ⟨0, 1, by decide, hindep⟩
  exact (hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor
    τ hτ).mpr hminor hF

/-- **The ambient incidence fibre is a constant torsor.**  Adding a constant is a bijection from
the constants onto the solution set, so any pointing singles out the source. -/
theorem boundarySolutions_constantTorsor
    (τ : Fin 2 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods (τ 0) (τ 1))) :
    Function.Bijective
      (fun c : ℂ => (⟨multipleEllipticGammaLogDerivMero τ hτ +
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) c,
        by
          rw [boundarySolutions_eq_constantCoset τ hτ hindep]
          exact ⟨c, rfl⟩⟩ : ellipticGammaBoundarySolutions τ hτ)) := by
  constructor
  · intro a b hab
    have h := congrArg Subtype.val hab
    have hcast : algebraMap ℂ (meroField (Set.univ : Set ℂ)) a =
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) b := by
      have := add_left_cancel h
      exact this
    exact (algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective hcast
  · rintro ⟨G, hG⟩
    obtain ⟨c, hc⟩ := exists_constant_of_mem_boundarySolutions τ hτ hindep hG
    exact ⟨c, Subtype.ext hc.symm⟩

end

end GaloisForLFunctions
