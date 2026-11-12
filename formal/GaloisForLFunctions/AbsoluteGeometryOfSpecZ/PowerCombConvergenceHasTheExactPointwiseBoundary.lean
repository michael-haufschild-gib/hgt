import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRightZeroConvolutionHasItsLimit
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactsSplitIntoRightTraceAndRemainder
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ConvergentPowerCombsExcludeBoundaryZeros
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive

/-!
# The exact pointwise boundary of ordinary power-comb convergence

For every subcritical positive power, the literal comb converges exactly
when every zeta zero lies strictly left of its power boundary. No common
gap is required: density supplies summable contact amplitudes in a narrow
right band, and the complete harmonic zero convolution has its limit.
-/

noncomputable section

open Complex Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open SquareRootThreshold

/-- An empty bounding line suffices for convergence when every zero copy
lies below it; the density moment supplies all trace summability. -/
theorem powerCombTailConverges_of_forall_copy_re_lt {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re < 1 - a) :
    PowerCombTailConverges a := by
  obtain ⟨σ, hσ, hσβ, hs⟩ := exists_summable_powerTailRightZeroAmplitude ha ha2
  apply (powerCombTailConverges_iff_rightZeroConvolution_converges ha ha2 hσ hσβ
    (fun q => (hβ q).le)).mpr
  have hlim := tendsto_powerTailRightZeroConvolution ha.le
    (by linarith only [ha2] : a ≤ 1) hσ hs hβ
  refine ⟨(∑' q, powerTailRightZeroConstant a σ q).re, ?_⟩
  exact (Complex.continuous_re.tendsto _).comp hlim

/-- Strict pointwise exclusion, rather than a gap below the supremum,
is sufficient for ordinary convergence of every subcritical power comb. -/
theorem powerCombTailConverges_of_forall_zero_re_lt {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2)
    (hzero : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 - a) :
    PowerCombTailConverges a :=
  powerCombTailConverges_of_forall_copy_re_lt ha ha2
    (fun q => hzero (q.1 : ℂ) (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q))

/-- Ordinary subcritical power-comb convergence is exactly strict
pointwise exclusion of every zeta zero from its bounding line and right half-plane. -/
theorem powerCombTailConverges_iff_forall_zero_re_lt {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) :
    PowerCombTailConverges a ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 - a := by
  constructor
  · intro hc ρ hρ
    have hw := add_zeroWidth_le_half_of_powerCombTailConverges ha ha2 hc
    have hne := powerCombTailConverges_excludes_boundary_zeros ha ha2 hc ρ hρ
    apply lt_of_le_of_ne _ hne
    by_cases hlo : ρ.re ≤ 1 / 2
    · linarith only [hlo, ha2]
    · have hr0 : 0 < ρ.re := by linarith only [not_le.mp hlo]
      have hr1 : ρ.re < 1 := lt_of_not_ge fun hh => riemannZeta_ne_zero_of_one_le_re hh hρ
      have hmem : ρ ∈ zetaZeroConfig.carrier := show IsNontrivialZero ρ from ⟨hρ, hr0, hr1⟩
      have hd := abs_re_sub_half_le_zetaZeroWidth hmem
      have hlow := le_abs_self (ρ.re - 1 / 2)
      linarith only [hw, hd, hlow]
  · exact powerCombTailConverges_of_forall_zero_re_lt ha ha2

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
