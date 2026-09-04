import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroScheduleCriterion
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroDiagonalNoGo

/-!
# Fast scheduled Cesàro no-go

This module extracts the exact rate condition behind the diagonal Cesàro obstruction. If certified
boundary amplification `5^(κ(N)-24)` eventually dominates cutoff `N` up to one fixed constant,
local boundedness of the scheduled pole-cleared Cesàro family would make `N C_N` bounded. The
discrete derivative identity would then make raw convolution-half partial sums eventually bounded,
contradicting their unconditional arithmetic unboundedness at `6/11`.

Thus any live Cesàro schedule must be cofinal but sublogarithmic in this precise base-five sense.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- Pole degree grows fast enough that its certified boundary amplification dominates cutoff. -/
def CesaroPoleScheduleFast (kappa : ℕ → ℕ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    24 ≤ kappa N ∧ (N : ℝ) ≤ B * (5 : ℝ) ^ (kappa N - 24)

/-- **Fast-schedule no-go.** Every pole schedule whose certified amplification dominates cutoff
is incompatible with local boundedness of canonical Cesàro source approximants. -/
theorem no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_fast
    {kappa : ℕ → ℕ} (hfast : CesaroPoleScheduleFast kappa) :
    ¬ PoleClearedFirstTraceCesaroScheduledLocallyBounded kappa := by
  rintro hloc
  obtain ⟨B, hB, N₀, hfast⟩ := hfast
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCesaroScheduledApprox kappa N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hC0 : 0 ≤ C :=
    (norm_nonneg
      (poleClearedFirstTraceCesaroScheduledApprox kappa 0 boundaryExteriorPoint)).trans (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hweighted : ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ B * K := by
    intro N hN
    obtain ⟨hk24, hscale⟩ := hfast N hN
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow hk24
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hbound N
    have hprod :
        ‖poleFactorSqrtApprox (kappa N) boundaryExteriorPoint‖ *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K := by
      rw [poleClearedFirstTraceCesaroScheduledApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hpowprod :
        (5 : ℝ) ^ (kappa N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K :=
      (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hprod
    calc
      (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          (B * (5 : ℝ) ^ (kappa N - 24)) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
      _ = B * ((5 : ℝ) ^ (kappa N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖) := by ring
      _ ≤ B * K := mul_le_mul_of_nonneg_left hpowprod hB
  have hpartial : ∀ N : ℕ, N₀ ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ 2 * (B * K) := by
    intro N hN
    rw [squarefreeHalfDirichletPartialSum_eq_cesaro_discreteDerivative]
    calc
      ‖((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint -
          (N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          ‖((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint‖ +
            ‖(N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint‖ := norm_sub_le _ _
      _ = ((N + 1 : ℕ) : ℝ) *
            ‖squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint‖ +
          (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ := by
        simp only [norm_mul, norm_natCast]
      _ ≤ B * K + B * K := add_le_add
        (hweighted (N + 1) (by omega)) (hweighted N hN)
      _ = 2 * (B * K) := by ring
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨2 * (B * K), N₀, hpartial⟩

end

end RHTower
