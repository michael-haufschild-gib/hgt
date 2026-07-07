/-
# Charge tomography: the off-line divisor and RH reconstructed from circle averages of `log‖ξ‖`

The two-circle modulus slope `modulusSlope ρ r₁ r₂` — the discrete radial derivative of the circle
average `r ↦ ⨍_{|z-ρ|=r} log‖ξ(z)‖` — recovers the local vanishing order of `ξ` at `ρ`
(`ModulusHolography.xi_circleAverage_slope_eq_order`).  This file welds that holographic readoff to the
census/valuation side (`DiscJump`, `ValuationProfile`, `ValMeasure`), which is otherwise stated in terms
of `analyticOrderAt xi` and never connected to the modulus data.  The result is a genuine tomography:
the whole off-line divisor is a functional of countably many circle averages of `log‖ξ‖`.

* `rh_iff_forall_modulusSlope_eq_zero` — **the crisp criterion**: RH holds iff the modulus-slope order
  field vanishes on the open right half-plane (the two-circle slope of `log‖ξ‖` is `0` at every
  right-half point, for small radii).  A single real-valued vanishing condition, not a per-level
  root-of-unity condition.
* `exists_radii_discJump_eq_sum_modulusSlope` — **the reconstruction**: the integer census jump
  `discJump t` (the total off-line order at height `t`, the atom feeding `valProfile`/`valMeasure`) is a
  finite sum of modulus circle-average slopes.  The census — hence the valuation profile, hence the
  off-line locus, hence RH — is a functional of the modulus data alone.
* `rh_iff_forall_height_sum_modulusSlope_zero` — RH iff every height's reconstructed order sum vanishes:
  the off-line locus is the support of the modulus-reconstructed order field.

The order field is fixed by the modulus constraint (a boundary datum on shrinking circles), not
propagated by any flow — holography in the literal sense: the bulk divisor read off its circle-average
boundary values.
-/
import GaloisForLFunctions.RHTower.ModulusHolography
import GaloisForLFunctions.RHTower.ValMeasure

open Complex Metric MeasureTheory
open scoped ENNReal

namespace RHTower

noncomputable section

/-- The two-circle modulus slope of `log‖ξ‖` at `ρ`: the discrete radial derivative of the circle
average between radii `r₁ < r₂`.  For small radii it equals the local vanishing order of `ξ` at `ρ`. -/
def modulusSlope (ρ : ℂ) (r₁ r₂ : ℝ) : ℝ :=
  (Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₂ -
      Real.circleAverage (fun z => Real.log ‖xi z‖) ρ r₁) /
    (Real.log r₂ - Real.log r₁)

/-- **The modulus slope recovers the vanishing order.**  For small enough radii the two-circle slope
of `log‖ξ‖` at `ρ` equals `(analyticOrderAt xi ρ).toNat` — the holographic readoff of the local order
from circle averages. -/
theorem modulusSlope_eq_order (ρ : ℂ) :
    ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
      modulusSlope ρ r₁ r₂ = ((analyticOrderAt xi ρ).toNat : ℝ) :=
  xi_circleAverage_slope_eq_order ρ

/-- The recovered order at `ρ` is zero iff `ξ` does not vanish at `ρ`. -/
theorem xi_orderToNat_eq_zero_iff (ρ : ℂ) : (analyticOrderAt xi ρ).toNat = 0 ↔ xi ρ ≠ 0 := by
  rw [ENat.toNat_eq_zero]
  constructor
  · rintro (h | h)
    · exact analyticOrderAt_eq_zero.mp h |>.resolve_left
        (not_not.mpr ((xi_analyticOnNhd_univ) ρ (by trivial)))
    · exact absurd h (xi_orderAt_ne_top ρ)
  · intro h; exact Or.inl (analyticOrderAt_eq_zero.mpr (Or.inr h))

/-- **Crisp tomography criterion for RH.**  The Riemann Hypothesis holds iff the modulus-slope order
field vanishes on the open right half-plane: at every right-half point the two-circle slope of
`log‖ξ‖` is `0` for small radii.  A zero slope means a zero recovered order, i.e. `ξ ≠ 0`; RH is exactly
the absence of right-half zeros. -/
theorem rh_iff_forall_modulusSlope_eq_zero :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
        modulusSlope ρ r₁ r₂ = 0 := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro hRH ρ hρ
    obtain ⟨R₀, hR₀, hrec⟩ := modulusSlope_eq_order ρ
    refine ⟨R₀, hR₀, ?_⟩
    intro R r₁ r₂ hr₁ hr₁₂ hr₂R hRle
    rw [hrec hr₁ hr₁₂ hr₂R hRle, (xi_orderToNat_eq_zero_iff ρ).mpr (hRH ρ hρ)]
    norm_num
  · intro hmod ρ hρ
    obtain ⟨R₁, hR₁, hrec⟩ := modulusSlope_eq_order ρ
    obtain ⟨R₂, hR₂, hzero⟩ := hmod ρ hρ
    set Rm : ℝ := min R₁ R₂ with hRm
    have hRmpos : 0 < Rm := lt_min hR₁ hR₂
    have hr₁ : (0 : ℝ) < Rm / 4 := by linarith
    have hr₁₂ : Rm / 4 < Rm / 2 := by linarith
    have hr₂R : Rm / 2 < Rm := by linarith
    have hval := hrec (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R (min_le_left _ _)
    have hz := hzero (R := Rm) (r₁ := Rm / 4) (r₂ := Rm / 2) hr₁ hr₁₂ hr₂R (min_le_right _ _)
    rw [hval] at hz
    have : (analyticOrderAt xi ρ).toNat = 0 := by exact_mod_cast hz
    exact (xi_orderToNat_eq_zero_iff ρ).mp this

/-- **The census jump is reconstructed from modulus circle averages.**  For every height `t` there is
a choice of radii for which the integer census jump `discJump t` (the total off-line order at height
`t`) equals the finite sum of modulus circle-average slopes over the box zeros at that height.  The
census — hence `valProfile`, `valMeasure`, and RH — is a functional of the modulus data. -/
theorem exists_radii_discJump_eq_sum_modulusSlope (t : ℝ) :
    ∃ r₁ r₂ : ℂ → ℝ,
      (discJump t : ℝ) =
        ∑ z ∈ (boxHeightZeros_finite t).toFinset, modulusSlope z (r₁ z) (r₂ z) := by
  choose R₀ hR₀ hrec using fun z : ℂ => modulusSlope_eq_order z
  refine ⟨fun z => R₀ z / 4, fun z => R₀ z / 2, ?_⟩
  rw [discJump, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have hpos := hR₀ z
  exact (hrec z (R := 3 * R₀ z / 4) (r₁ := R₀ z / 4) (r₂ := R₀ z / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)).symm

/-- **RH is the vanishing of the modulus-reconstructed order field.**  RH holds iff at every height
the reconstructed sum of modulus circle-average slopes is zero — i.e. the off-line locus is the
support of the modulus order field.  Combines the census reconstruction with
`ValMeasure.rh_iff_offLineHeights_empty`. -/
theorem rh_iff_forall_height_sum_modulusSlope_zero :
    RiemannHypothesis ↔
      ∀ t : ℝ, ∀ r₁ r₂ : ℂ → ℝ,
        (discJump t : ℝ) =
          ∑ z ∈ (boxHeightZeros_finite t).toFinset, modulusSlope z (r₁ z) (r₂ z) →
        (∑ z ∈ (boxHeightZeros_finite t).toFinset, modulusSlope z (r₁ z) (r₂ z)) = 0 := by
  rw [rh_iff_offLineHeights_empty, offLineHeights, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h t r₁ r₂ hrecon
    have hz : discJump t = 0 := by
      by_contra hne
      exact h t (by rw [Set.mem_setOf_eq]; exact hne)
    rw [← hrecon, hz, Nat.cast_zero]
  · intro h t ht
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨r₁, r₂, hrecon⟩ := exists_radii_discJump_eq_sum_modulusSlope t
    have := h t r₁ r₂ hrecon
    rw [this] at hrecon
    exact ht (by exact_mod_cast hrecon)

end

end RHTower
