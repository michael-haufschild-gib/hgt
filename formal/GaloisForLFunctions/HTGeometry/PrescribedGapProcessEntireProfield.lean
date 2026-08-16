import GaloisForLFunctions.HTGeometry.MovingDivisorQuartetSurgery
import GaloisForLFunctions.HTGeometry.PrescribedGapProcessFreeness

/-!
# The order-one maximal-HT profield of a prescribed gap process

Every shift-ergodic positive gap law of mean one is realized by the positive zeros of an even real
entire function of exact order one, whose full complex translation family is differentially
algebraically independent at *every* positive power, and whose positive-power translation profields
also contain a representative with an off-real quartet and exactly the same real zeros.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- The complete order-one maximal-HT profield conclusion for the symmetric canonical product of a
moving divisor at a fixed location parameter: an even Schwarz-real entire function with an
order-one envelope and the exact simple divisor `{±Λ_j(θ)}`, whose full complex translation family
is relation-free at every positive power, together with an off-real quartet representative that has
the same real zeros, the same freeness, and literally the same positive-power translation
profields. -/
def OrderOneMaximalHTProfield (Dv : MovingDivisor) (θ : BoundedRealSequence) : Prop :=
  OrderOneEnvelope (Dv.evenCanonicalProduct (θ : ℕ → ℝ)) ∧
  (∀ z : ℂ, Dv.evenCanonicalProduct (θ : ℕ → ℝ) (-z) = Dv.evenCanonicalProduct (θ : ℕ → ℝ) z) ∧
  (∀ z : ℂ, Dv.evenCanonicalProduct (θ : ℕ → ℝ) ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (Dv.evenCanonicalProduct (θ : ℕ → ℝ) z)) ∧
  (∀ z : ℂ, Dv.evenCanonicalProduct (θ : ℕ → ℝ) z = 0 ↔
      ∃ n, z = (Dv.zero (θ : ℕ → ℝ) n : ℂ) ∨ z = -(Dv.zero (θ : ℕ → ℝ) n : ℂ)) ∧
  (∀ n, analyticOrderAt (Dv.evenCanonicalProduct (θ : ℕ → ℝ))
      (Dv.zero (θ : ℕ → ℝ) n : ℂ) = 1) ∧
  (∀ n, analyticOrderAt (Dv.evenCanonicalProduct (θ : ℕ → ℝ))
      (-(Dv.zero (θ : ℕ → ℝ) n : ℂ)) = 1) ∧
  (∀ N : ℕ, N ≠ 0 → ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
      ¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => (Dv.evenCanonicalProduct (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
        (commonUpperTranslationDomain shift)) ∧
  ∀ τ : ℂ, τ.re * τ.im ≠ 0 →
    OrderOneEnvelope (Dv.quartetProduct τ (θ : ℕ → ℝ)) ∧
    (∀ z : ℂ, Dv.quartetProduct τ (θ : ℕ → ℝ) (-z) = Dv.quartetProduct τ (θ : ℕ → ℝ) z) ∧
    (∀ z : ℂ, Dv.quartetProduct τ (θ : ℕ → ℝ) ((starRingEnd ℂ) z)
        = (starRingEnd ℂ) (Dv.quartetProduct τ (θ : ℕ → ℝ) z)) ∧
    (Dv.quartetProduct τ (θ : ℕ → ℝ) τ = 0 ∧ Dv.quartetProduct τ (θ : ℕ → ℝ) (-τ) = 0 ∧
      Dv.quartetProduct τ (θ : ℕ → ℝ) ((starRingEnd ℂ) τ) = 0 ∧
      Dv.quartetProduct τ (θ : ℕ → ℝ) (-((starRingEnd ℂ) τ)) = 0) ∧
    (∀ z : ℂ, z.im = 0 →
      (Dv.quartetProduct τ (θ : ℕ → ℝ) z = 0 ↔ Dv.evenCanonicalProduct (θ : ℕ → ℝ) z = 0)) ∧
    (∀ N : ℕ, N ≠ 0 → ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
      ¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => (Dv.quartetProduct τ (θ : ℕ → ℝ) (z + shift.1 i)) ^ N)
        (commonUpperTranslationDomain shift)) ∧
    ∀ (N : ℕ) (hF : AnalyticOnNhd ℂ (Dv.quartetProduct τ (θ : ℕ → ℝ)) Set.univ)
      (hE : AnalyticOnNhd ℂ (Dv.evenCanonicalProduct (θ : ℕ → ℝ)) Set.univ),
      translationPowerProfield (Dv.quartetProduct τ (θ : ℕ → ℝ)) hF N
        = translationPowerProfield (Dv.evenCanonicalProduct (θ : ℕ → ℝ)) hE N

/-- **Carrier freeness gives the complete order-one maximal-HT profield conclusion.** -/
theorem orderOneMaximalHTProfield_of_carrierFree (Dv : MovingDivisor) (θ : BoundedRealSequence)
    (hcar : ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
      ¬ FamilyDifferentiallyAlgebraicOn
        (fun i z => Dv.evenCarrierB θ (z + shift.1 i)) (commonUpperTranslationDomain shift)) :
    OrderOneMaximalHTProfield Dv θ := by
  refine ⟨Dv.evenCanonicalProduct_orderOneEnvelope _, Dv.evenCanonicalProduct_even _,
    Dv.evenCanonicalProduct_conj _, Dv.evenCanonicalProduct_eq_zero_iff _,
    Dv.evenCanonicalProduct_pos_zero_analyticOrderAt _,
    Dv.evenCanonicalProduct_neg_zero_analyticOrderAt _,
    fun N hN m shift => not_familyDifferentiallyAlgebraicOn_evenCanonicalProduct_translates_pow
      Dv θ shift hN (hcar m shift), fun τ hτ => ?_⟩
  have hτim : τ.im ≠ 0 := fun hcon => hτ (by rw [hcon, mul_zero])
  exact ⟨Dv.quartetProduct_orderOneEnvelope τ _, Dv.quartetProduct_even τ _,
    Dv.quartetProduct_conj τ _, Dv.quartetProduct_quartet_zeros τ _,
    fun z hz => Dv.quartetProduct_real_eq_zero_iff hτim _ hz,
    fun N hN m shift => not_familyDifferentiallyAlgebraicOn_quartetProduct_translates_pow
      Dv τ θ shift hN (hcar m shift),
    fun N hF hE => translationPowerProfield_quartetProduct Dv τ _ N hF hE⟩

/-- **Every stationary ergodic positive gap law of mean one is realized by the positive zeros of an
even real order-one function with maximal translation HT at every power, inside a profield that also
contains an off-real-quartet representative with exactly the same real zeros.** -/
theorem exists_prescribedGapProcess_orderOneMaximalHTProfield
    {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]
    (hErg : Ergodic shiftSeq P) (hint : Integrable (fun ω => ω 0) P)
    (hmean : ∫ ω, ω 0 ∂P = 1) (hpos : ∀ᵐ ω ∂P, ∀ n, 0 < ω n) :
    ∃ (g : ℕ → ℝ) (hgpos : ∀ j, 0 < g j)
      (hgmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)),
      ∃ Θ : Set BoundedRealSequence,
        Dense Θ ∧ Θ ∈ residual BoundedRealSequence ∧
        ∀ θ ∈ Θ,
          StrictMono (gapLocation g (θ : ℕ → ℝ)) ∧
          (∀ j, 0 < gapLocation g (θ : ℕ → ℝ) j) ∧
          Tendsto (fun j : ℕ => gapLocation g (θ : ℕ → ℝ) j / j) atTop (𝓝 1) ∧
          (∀ (k : ℕ) (Φ : (Fin k → ℝ) → ℝ) (C : ℝ≥0), LipschitzWith C Φ →
            (∃ M : ℝ, ∀ x, |Φ x| ≤ M) →
            Tendsto
              (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
                Φ (fun i : Fin k => gapLocationGap g (θ : ℕ → ℝ) (j + i)))
              atTop (𝓝 (∫ ω, Φ (blockMap k ω) ∂P))) ∧
          OrderOneMaximalHTProfield (gapMovingDivisor g hgpos hgmean) θ := by
  classical
  obtain ⟨g, hgpos, hgmean, hgblock⟩ :=
    exists_prescribedGapProcess_locations hErg hint hmean hpos
  refine ⟨g, hgpos, hgmean, ?_⟩
  set Dv : MovingDivisor := gapMovingDivisor g hgpos hgmean with hDv
  obtain ⟨hdense, hres, hnoRel⟩ := Dv.movingDivisor_fullTranslationFreeness_denseResidual
  refine ⟨_, hdense, hres, fun θ hθ => ?_⟩
  obtain ⟨hmono, hposθ, hdens, hblock⟩ := hgblock (θ : ℕ → ℝ)
  exact ⟨hmono, hposθ, hdens, hblock,
    orderOneMaximalHTProfield_of_carrierFree Dv θ (hnoRel θ hθ)⟩

end

end GaloisForLFunctions.HTGeometry
