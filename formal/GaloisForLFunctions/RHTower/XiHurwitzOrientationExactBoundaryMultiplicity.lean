import GaloisForLFunctions.RHTower.XiHurwitzOrientationSharpNonnegativeConeDistance

/-!
# Exact-boundary multiplicity of Xi--Hurwitz orientation

The sharp nonnegative-cone radius is attained by far more than one vector. For any
reflection-even vector of the same norm as the reflection-odd orientation vector, their balanced
half-sum is a zero-energy closest boundary point. In particular, sign-forgetting the orientation
coordinates and its negative give two distinct exact boundary points whenever orientation energy
is positive.

Thus uniqueness of the closest zero-energy boundary point is equivalent to RH. Abstract cone
projection cannot select the missing Route-Q source packet: away from RH its equality locus already
contains a reflection-even sphere, and arithmetic incidence must choose a phase on that sphere.
-/

open Complex

namespace CliffordWeil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every equally long fixed vector produces an explicit closest zero-energy point to an
anti-fixed vector. -/
theorem balanced_fixed_antiFixed_boundary
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J)
    {w e : H} (hw : J w = -w) (he : J e = e) (hnorm : ‖e‖ = ‖w‖) :
    let v : H := (1 / 2 : ℂ) • (w + e)
    quadratic J v = 0 ∧ ‖w‖ ^ 2 = 2 * ‖v - w‖ ^ 2 := by
  let v : H := (1 / 2 : ℂ) • (w + e)
  have hvplus : v + J v = e := by
    dsimp [v]
    rw [map_smul, map_add, hw, he]
    module
  have hvminus : v - J v = w := by
    dsimp [v]
    rw [map_smul, map_add, hw, he]
    module
  have hbalanceV := four_mul_quadratic_eq_even_sub_odd J hJ v
  have hq : quadratic J v = 0 := by
    rw [hvplus, hvminus, hnorm] at hbalanceV
    linarith
  let d : H := v - w
  have hdplus : d + J d = e := by
    dsimp [d]
    rw [map_sub, hw]
    calc
      v - w + (J v - -w) = v + J v := by module
      _ = e := hvplus
  have hdminus : d - J d = -w := by
    dsimp [d]
    rw [map_sub, hw]
    calc
      v - w - (J v - -w) = (v - J v) - (w + w) := by module
      _ = -w := by rw [hvminus]; module
  have hplusEnergy := plus_channel_energy_eq J hJ d
  have hminusEnergy := minus_channel_energy_eq J hJ d
  have hparallelogram :
      ‖d + J d‖ ^ 2 + ‖d - J d‖ ^ 2 = 4 * ‖d‖ ^ 2 := by
    nlinarith
  rw [hdplus, hdminus, norm_neg, hnorm] at hparallelogram
  refine ⟨hq, ?_⟩
  dsimp [d] at hparallelogram
  nlinarith

end CliffordWeil

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Exact closest points on the zero-Weil-energy boundary. -/
def xiHurwitzOrientationExactConeBoundary (v : XiWeilCarrier) : Prop :=
  xiWeilHilbertQuadratic v = 0 ∧
    xiHurwitzOrientationEnergy =
      2 * dist v xiHurwitzOrientationVector ^ 2

/-- Closest boundary point using the canonical sign-forgetting even companion. -/
def xiHurwitzOrientationBoundaryPlus : XiWeilCarrier :=
  (1 / 2 : ℂ) •
    (xiHurwitzOrientationVector + xiHurwitzOrientationAbsoluteVector)

/-- Antipodal closest boundary point using the negative even companion. -/
def xiHurwitzOrientationBoundaryMinus : XiWeilCarrier :=
  (1 / 2 : ℂ) •
    (xiHurwitzOrientationVector - xiHurwitzOrientationAbsoluteVector)

theorem xiHurwitzOrientationBoundaryPlus_exact :
    xiHurwitzOrientationExactConeBoundary xiHurwitzOrientationBoundaryPlus := by
  have h := CliffordWeil.balanced_fixed_antiFixed_boundary
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
    xiWeilLineConjLp_xiHurwitzOrientationVector
    xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector
    norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector
  unfold xiHurwitzOrientationExactConeBoundary
  rw [← norm_sq_xiHurwitzOrientationVector, dist_eq_norm]
  simpa only [xiHurwitzOrientationBoundaryPlus, xiWeilHilbertQuadratic,
    CliffordWeil.quadratic] using h

theorem xiHurwitzOrientationBoundaryMinus_exact :
    xiHurwitzOrientationExactConeBoundary xiHurwitzOrientationBoundaryMinus := by
  have he : xiWeilLineConjLinearIsometry (-xiHurwitzOrientationAbsoluteVector) =
      -xiHurwitzOrientationAbsoluteVector := by
    rw [map_neg, xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
  have hnorm : ‖-xiHurwitzOrientationAbsoluteVector‖ =
      ‖xiHurwitzOrientationVector‖ := by
    rw [norm_neg, norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector]
  have h := CliffordWeil.balanced_fixed_antiFixed_boundary
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
    xiWeilLineConjLp_xiHurwitzOrientationVector he hnorm
  unfold xiHurwitzOrientationExactConeBoundary
  rw [← norm_sq_xiHurwitzOrientationVector, dist_eq_norm]
  simpa only [xiHurwitzOrientationBoundaryMinus, sub_eq_add_neg,
    xiWeilHilbertQuadratic, CliffordWeil.quadratic] using h

/-- Positive orientation energy splits the exact closest boundary into at least two points. -/
theorem xiHurwitzOrientationBoundaryPlus_ne_minus_of_energy_pos
    (hE : 0 < xiHurwitzOrientationEnergy) :
    xiHurwitzOrientationBoundaryPlus ≠ xiHurwitzOrientationBoundaryMinus := by
  intro heq
  have hdiff :
      xiHurwitzOrientationBoundaryPlus - xiHurwitzOrientationBoundaryMinus =
        xiHurwitzOrientationAbsoluteVector := by
    unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
    module
  rw [heq, sub_self] at hdiff
  have hnorm := norm_sq_xiHurwitzOrientationAbsoluteVector
  rw [← hdiff, norm_zero] at hnorm
  norm_num at hnorm
  linarith

/-- Exact Route-Q multiplicity law: the closest zero-energy cone boundary is unique exactly under
RH. If RH fails, the two explicit antipodal-even balances are distinct equality witnesses. -/
theorem xiHurwitzOrientation_exactConeBoundary_unique_iff_rh :
    (∃! v : XiWeilCarrier, xiHurwitzOrientationExactConeBoundary v) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨v, hv, hunique⟩
    by_contra hnot
    have hE : 0 < xiHurwitzOrientationEnergy :=
      xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
    have heq := (hunique xiHurwitzOrientationBoundaryPlus
      xiHurwitzOrientationBoundaryPlus_exact).trans
        (hunique xiHurwitzOrientationBoundaryMinus
          xiHurwitzOrientationBoundaryMinus_exact).symm
    exact xiHurwitzOrientationBoundaryPlus_ne_minus_of_energy_pos hE heq
  · intro hRH
    have hE : xiHurwitzOrientationEnergy = 0 :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.1 hRH
    have hw : xiHurwitzOrientationVector = 0 :=
      xiHurwitzOrientationVector_eq_zero_iff_energy_eq_zero.2 hE
    refine ⟨0, ?_, fun v hv => ?_⟩
    · unfold xiHurwitzOrientationExactConeBoundary xiWeilHilbertQuadratic
      simp [hE, hw]
    · unfold xiHurwitzOrientationExactConeBoundary at hv
      rw [hE, hw, dist_zero_right] at hv
      have hvnorm : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.mp hvnorm

end

end RHTower
