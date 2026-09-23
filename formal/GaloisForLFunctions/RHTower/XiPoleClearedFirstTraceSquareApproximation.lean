import GaloisForLFunctions.RHTower.LocallyUniformSquareMultiplicityClosure
import GaloisForLFunctions.RHTower.XiPoleClearedFirstTraceRootReduction

/-!
# Compact-open square approximation is exactly the first RH rung

Suppose the pole-cleared valuation-one continuation is a compact-open limit on `rightHalf` of
functions which are holomorphic squares there.  The argument principle makes every finite local
order even, so this hypothesis already proves `RHLadder 1`.  Conversely, a right-half square root
gives a constant approximating sequence.

Thus normal-family or Vitali proposals based on square approximants do not weaken the missing
arithmetic step: convergence itself is equivalent to the first multiplicity-parity rung.  This
module is a receiver theorem and does not construct the approximants.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The pole-cleared first-prime-trace field is a compact-open limit of holomorphic squares on the
strict right half-plane iff every right-half Xi zero has even order. -/
theorem rhLadder_one_iff_poleClearedFirstTrace_locallyUniform_square_approximants :
    RHLadder 1 ↔
      ∃ G F : ℕ → ℂ → ℂ,
        (∀ n, AnalyticOnNhd ℂ (G n) rightHalf) ∧
        (∀ n, F n = fun z => G n z ^ (2 : ℕ)) ∧
        TendstoLocallyUniformlyOn F poleClearedFirstTraceExponentialContinuation
          atTop rightHalf := by
  constructor
  · rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
    rintro ⟨e, he, hesq⟩
    refine ⟨fun _ => e, fun _ z => e z ^ (2 : ℕ), fun _ => he, fun _ => rfl, ?_⟩
    intro u hu x hx
    refine ⟨rightHalf, self_mem_nhdsWithin, Eventually.of_forall fun _ y hy => ?_⟩
    change (poleClearedFirstTraceExponentialContinuation y, e y ^ (2 : ℕ)) ∈ u
    rw [hesq y hy]
    exact refl_mem_uniformity hu
  · rintro ⟨G, F, hG, hF, hconv⟩
    rw [rhLadder_iff_toNat_dvd]
    intro ρ hρ _hzero
    let d := (analyticOrderAt xi ρ).toNat
    have hxiOrder : analyticOrderAt xi ρ = (d : ℕ∞) :=
      (ENat.coe_toNat (xi_order_ne_top ρ)).symm
    have hfirstOrder :
        analyticOrderAt poleClearedFirstTraceExponentialContinuation ρ = (d : ℕ∞) := by
      rw [analyticOrderAt_poleClearedFirstTraceExponentialContinuation_eq_xi hρ]
      exact hxiOrder
    have heven : Even d :=
      even_analyticOrderAt_of_tendstoLocallyUniformlyOn_squares_of_order
        isOpen_rightHalf hG hF
        analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
        hconv hρ hfirstOrder
    obtain ⟨k, hk⟩ := heven
    refine ⟨k, ?_⟩
    norm_num
    omega

end

end RHTower
