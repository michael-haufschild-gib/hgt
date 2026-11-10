import GaloisForLFunctions.SelectiveArithmetic.CancellationInTheContactsBuysTheLadder
import GaloisForLFunctions.SelectiveArithmetic.AnIsolatedPairShowsAtTheRungOfItsDepth
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoSidedThetaMollifierTrap
import GaloisForLFunctions.BezoutValuationIncidence.UnconditionalEscapedMoebiusDecayAndCrossRouteBridge

/-!
# The cancellation and depth ladder

Cancellation with exponent `γ` pays the sign on bounded shapes at every rung
`2γκ < 1`. Full window positivity at a rung forces companions of zeros of depth
`2δκ > 1`. These are different test domains. A bounded dyadic moment for the
Möbius mollifier of length `T^θ` confines all sufficiently high zeros to depth
less than `1/(2θ)+ε`. The seven power-saving formulations of quasi-RH complete
the dictionary.
-/

open Complex Filter Topology MeasureTheory Set
open Zeta23
open _root_.RHTower
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

/-- Cancellation gives the sign on packets whose derivative energy is at most their mass. -/
theorem cancellation_gives_boundedShape_sign {C γ κ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hγκ : 2 * γ * κ < 1) :
    ∃ M : ℝ, ∀ q : ℝ, M ≤ Real.log q → ∀ a : ℝ,
      0 ≤ a → a ≤ κ * Real.log (Real.log q) →
      ∀ {w : ℕ → ℝ}, HasCancellation w C γ → ∀ {f : ℝ → ℝ},
      ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
      (∫ u, deriv f u ^ 2) ≤ (∫ u, f u ^ 2) →
      0 ≤ systemForm w q a (fun u => (f u : ℂ)) := by
  obtain ⟨M, hM⟩ := exists_cancellation_margin hC hγ hκ hγκ
  refine ⟨max M 0, fun q hq a ha har w hw f hf hs hshape => ?_⟩
  have hq0 : 0 ≤ Real.log q := (le_max_right _ _).trans hq
  exact (mul_nonneg (div_nonneg hq0 zero_le_two) (sub_nonneg.mpr hshape)).trans
    (hM q ((le_max_left _ _).trans hq) a ha har hw hf hs)

/-- The finite exceptional set supplied by a long Möbius moment has bounded height. -/
theorem eventual_depth_bound_of_dyadic_moebius_moment {θ C ε : ℝ}
    (hθ : 1 / 2 < θ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ᶠ T in atTop,
      (∫ t in T..(2 * T),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C * T) :
    ∃ H : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      H ≤ |ρ.im| → |ρ.re - 1 / 2| < 1 / (2 * θ) + ε := by
  have hfin := finite_offLineZeros_beyond_of_dyadic_moebius_mollifier hθ hC hε hbound
  obtain ⟨H, hH⟩ := (hfin.image fun ρ => |ρ.im|).bddAbove
  refine ⟨H + 1, fun ρ hρ h0 h1 hheight => ?_⟩
  by_contra hdepth
  have hmem : ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      1 / (2 * θ) + ε ≤ |ρ.re - 1 / 2|} := ⟨hρ, h0, h1, le_of_not_gt hdepth⟩
  have hh := hH (Set.mem_image_of_mem (fun ρ : ℂ => |ρ.im|) hmem)
  linarith only [hh, hheight]

/-- The ladder in one statement, retaining the bounded-shape and full-window domains. -/
theorem cancellation_and_depth_ladder {C γ κ δ θ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hγκ : 2 * γ * κ < 1)
    (hδ : 0 < δ) (hδκ : 1 < 2 * δ * κ) (hθ : 1 < θ) :
    ∃ M A M' : ℝ, 1 ≤ A ∧
      (∀ q : ℝ, M ≤ Real.log q → ∀ a : ℝ,
        0 ≤ a → a ≤ κ * Real.log (Real.log q) →
        ∀ {w : ℕ → ℝ}, HasCancellation w C γ → ∀ {f : ℝ → ℝ},
        ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
        (∫ u, deriv f u ^ 2) ≤ (∫ u, f u ^ 2) →
        0 ≤ systemForm w q a (fun u => (f u : ℂ))) ∧
      (∀ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re = 1 / 2 + δ →
        M' ≤ Real.log (A * Real.log (|ρ₀.im| + 3)) →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
          tsupport f ⊆ Icc (-(κ * Real.log (A * Real.log (|ρ₀.im| + 3))))
            (κ * Real.log (A * Real.log (|ρ₀.im| + 3))) →
          0 ≤ (zetaZeroConfig.W f f).re) →
        ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧
          ρ ≠ ArithmeticCastelnuovoSeveri.reflect ρ₀ ∧
          |ρ.im - ρ₀.im| ≤ Real.exp (κ * Real.log (A * Real.log (|ρ₀.im| + 3))) ∧
          ρ.re ≠ 1 / 2) ∧
      (∀ C' ε : ℝ, 0 ≤ C' → 0 < ε →
        (∀ᶠ T in atTop,
          (∫ t in T..(2 * T),
            ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
              edPoly moebiusMollifierCoeff (Finset.Icc 1 ⌊T ^ θ⌋₊)
                (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ C' * T) →
        ∃ H : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
          H ≤ |ρ.im| → |ρ.re - 1 / 2| < 1 / (2 * θ) + ε) ∧
      List.TFAE [∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ GrowingEndpointEscapedMoebiusLaw s,
        ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ DyadicEscapedMoebiusLaw s,
        CentredPrimeBandPowerSaving, PrimePowerWindowSaving, MoebiusPowerWindowSaving,
        receiverDampingRate < 1 / 2, zetaZeroAbscissa < 1] := by
  obtain ⟨M, hM⟩ := cancellation_gives_boundedShape_sign hC hγ hκ hγκ
  obtain ⟨A, M', hA, hcomp⟩ := zeta_companion_of_rung hδ hδκ
  exact ⟨M, A, M', hA, hM, hcomp,
    fun _ _ hC' hε => eventual_depth_bound_of_dyadic_moebius_moment
      (by linarith only [hθ]) hC' hε,
    quasiRH_crossRoute_seven_way_tfae⟩

#print axioms cancellation_and_depth_ladder

end GaloisForLFunctions.SelectiveArithmetic
