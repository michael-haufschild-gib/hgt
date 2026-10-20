import GaloisForLFunctions.ArithmeticCriticalityTheory.MeanZeroProfileVariationInequalityPastPrimeTwo
import GaloisForLFunctions.RHTower.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.SuzukiFirstContactBoundaryRoughness

/-!
# An explicit small-aperture floor for the restricted Weil operator

The restricted Weil operator of Connes–Consani–Moscovici at the aperture `A` has the ground energy
`μ(A)`, the greatest lower bound of the Rayleigh quotients of smooth sources compactly supported in
`(−A, A)` (Suzuki's characterisation), including the pole directions. Small-aperture positivity is
known in the form `∃ δ > 0, ∀ A < δ, 0 < μ(A)`, with `δ` produced by an asymptotic expansion and not
explicit.

The Markov window of the full zero form gives it explicitly. On a complex smooth source `u` the
restricted quadratic is `Re W_ζ(u, u)`, and on tests supported in `[−21/200, 21/200]` the Markov-window
theorem gives `Re W_ζ(u, u) ≥ (1/30) ∫ |u|²` (`zetaZeroConfig_re_W_ge_of_support_le`). Hence:

* **Explicit floor** (`one_thirtieth_le_ccmRestrictedWeilGroundEnergy`): `μ(A) ≥ 1/30` for every
  aperture `A ≤ 21/200`.
* **Coercivity on the whole form domain** (`ccmRestrictedWeilSourceQuadratic_ge_of_le`): every vector
  of the completed CCM form domain at such an aperture, pole directions included, has
  `Q_A(u) ≥ (1/30) ‖u‖²`.
* **Contact apertures** (`lt_of_ccmRestrictedWeilGroundEnergy_nonpos`): every aperture with
  `μ(A) ≤ 0`, in particular the first contact aperture that a failure of RH would produce, exceeds
  `21/200`.
-/

open MeasureTheory Set Filter Topology
open RHTower
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The aperture norm of a smooth interior source is its `L²` norm. -/
theorem norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) :
    ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  change ‖(ccmArchimedeanFormToAperture A u.toCCMFormVector : SoninL2)‖ ^ 2 = _
  rw [soninL2_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
  rw [hx]

/-- **The explicit floor**: `μ(A) ≥ 1/30` for every aperture `A ≤ 21/200`. -/
theorem one_thirtieth_le_ccmRestrictedWeilGroundEnergy {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 21 / 200) : 1 / 30 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hsupp : tsupport (u : ℝ → ℂ) ⊆ Icc (-(21 / 200)) (21 / 200) :=
    u.tsupport_subset.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact zetaZeroConfig_re_W_ge_of_support_le (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsupp

/-- **Coercivity on the completed form domain** at every aperture `A ≤ 21/200`. -/
theorem ccmRestrictedWeilSourceQuadratic_ge_of_le {A : SuzukiPositiveAperture}
    (hA : A.1 ≤ 21 / 200) (u : CCMArchimedeanFormDomain A) :
    1 / 30 * ‖ccmArchimedeanFormToAperture A u‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic A u :=
  (mul_le_mul_of_nonneg_right (one_thirtieth_le_ccmRestrictedWeilGroundEnergy hA)
    (sq_nonneg _)).trans (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source A u)

/-- **Contact apertures exceed `21/200`.** -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonpos {A : SuzukiPositiveAperture}
    (h : ccmRestrictedWeilGroundEnergy A ≤ 0) : 21 / 200 < A.1 := by
  by_contra hA
  have := one_thirtieth_le_ccmRestrictedWeilGroundEnergy (not_lt.mp hA)
  linarith

/-- The first contact of a boundary-rough failure of RH lies beyond `21/200`. -/
theorem ccmFirstContactBoundaryRoughness_aperture_gt :
    CCMFirstContactBoundaryRoughness →
      ∃ (A : SuzukiPositiveAperture) (q : CCMArchimedeanFormDomain A), 21 / 200 < A.1 ∧
        ccmRestrictedWeilGroundEnergy A = 0 ∧ ccmArchimedeanFormToAperture A q ≠ 0 ∧
          ccmRestrictedWeilSourceQuadratic A q = 0 := by
  rintro ⟨A, q, h0, -, hq, hQ, -⟩
  exact ⟨A, q, lt_of_ccmRestrictedWeilGroundEnergy_nonpos h0.le, h0, hq, hQ⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
