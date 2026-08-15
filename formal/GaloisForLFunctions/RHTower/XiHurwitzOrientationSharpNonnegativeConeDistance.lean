import GaloisForLFunctions.RHTower.CCMClosedXiConformalKreinLaw
import GaloisForLFunctions.RHTower.XiHurwitzOrientationCofinalSourceSignGate

/-!
# Sharp nonnegative-cone distance from Xi--Hurwitz orientation

The preceding cofinal-sign theorem shows qualitatively that source-nonnegative separated packets
cannot converge to a nonzero Hurwitz orientation vector.  Here the involutive Weil geometry gives
the exact quantitative obstruction.  Every vector with nonnegative Weil quadratic stays outside
the squared-radius ball

`orientationEnergy / 2`.

The constant is attained on the zero-energy boundary.  A canonical reflection-even vector is
obtained by forgetting the signs of the orientation coordinates; its norm equals that of the
reflection-odd orientation vector.  Balancing the two vectors produces the equality witness.

For separated continued-Cauchy packets this yields the literal finite prime--Gamma inequality

`orientationEnergy <= 2 * dist(packet.evaluation, orientationVector)^2`.

No RH premise, computation, or nonstandard assumption is used.  The equality witness is target-defined, so it
classifies the obstruction but does not manufacture the missing source-first packet.
-/

open Complex

namespace CliffordWeil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A reflection-nonnegative vector stays at least `‖w‖ / sqrt 2` away from every
reflection-odd vector `w`, in division-free squared form. -/
theorem antiFixed_norm_sq_le_two_mul_norm_sub_sq_of_quadratic_nonneg
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J)
    {w v : H} (hw : J w = -w) (hv : 0 ≤ quadratic J v) :
    ‖w‖ ^ 2 ≤ 2 * ‖v - w‖ ^ 2 := by
  have hbalanceV := four_mul_quadratic_eq_even_sub_odd J hJ v
  have hchannels : ‖v - J v‖ ^ 2 ≤ ‖v + J v‖ ^ 2 := by
    nlinarith
  let a : H := v - w
  have hplus : a + J a = v + J v := by
    dsimp [a]
    rw [map_sub, hw]
    module
  have hminus : a - J a = (v - J v) - (w + w) := by
    dsimp [a]
    rw [map_sub, hw]
    module
  have hplusEnergy := plus_channel_energy_eq J hJ a
  have hminusEnergy := minus_channel_energy_eq J hJ a
  have hparallelogram :
      ‖a + J a‖ ^ 2 + ‖a - J a‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
    nlinarith
  have htriangle : ‖w + w‖ ≤ ‖v - J v‖ + ‖(v - J v) - (w + w)‖ := by
    calc
      ‖w + w‖ = ‖(v - J v) - ((v - J v) - (w + w))‖ := by
        congr 1
        module
      _ ≤ ‖v - J v‖ + ‖(v - J v) - (w + w)‖ := norm_sub_le _ _
  have haddnorm : ‖w + w‖ = 2 * ‖w‖ := by
    rw [← two_smul ℂ w, norm_smul]
    norm_num
  have hmidpoint :
      2 * ‖w‖ ^ 2 ≤
        ‖v - J v‖ ^ 2 + ‖(v - J v) - (w + w)‖ ^ 2 := by
    rw [haddnorm] at htriangle
    nlinarith [sq_nonneg
      (‖v - J v‖ - ‖(v - J v) - (w + w)‖),
      norm_nonneg w, norm_nonneg (v - J v),
      norm_nonneg ((v - J v) - (w + w))]
  rw [hplus, hminus] at hparallelogram
  dsimp [a] at hparallelogram
  nlinarith

/-- The constant in the anti-fixed exclusion radius is attained whenever an equally long fixed
vector exists. -/
theorem exists_quadratic_zero_with_antiFixed_distance_eq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J)
    {w e : H} (hw : J w = -w) (he : J e = e) (hnorm : ‖e‖ = ‖w‖) :
    ∃ v : H, quadratic J v = 0 ∧ ‖w‖ ^ 2 = 2 * ‖v - w‖ ^ 2 := by
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
  let a : H := v - w
  have haplus : a + J a = e := by
    dsimp [a]
    rw [map_sub, hw]
    calc
      v - w + (J v - -w) = v + J v := by module
      _ = e := hvplus
  have haminus : a - J a = -w := by
    dsimp [a]
    rw [map_sub, hw]
    calc
      v - w - (J v - -w) = (v - J v) - (w + w) := by module
      _ = -w := by rw [hvminus]; module
  have hplusEnergy := plus_channel_energy_eq J hJ a
  have hminusEnergy := minus_channel_energy_eq J hJ a
  have hparallelogram :
      ‖a + J a‖ ^ 2 + ‖a - J a‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
    nlinarith
  rw [haplus, haminus, norm_neg, hnorm] at hparallelogram
  refine ⟨v, hq, ?_⟩
  dsimp [a] at hparallelogram
  nlinarith

end CliffordWeil

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Phase-forgetting reflection-even companion of the signed orientation vector. -/
def xiHurwitzOrientationAbsoluteVector : XiWeilCarrier :=
  ⟨fun q => ((‖xiHurwitzOrientationCoordinate q‖ : ℝ) : ℂ),
    HilbertSchmidt.memℓp_of_sq <| by
      simpa using summable_norm_sq_xiHurwitzOrientationCoordinate⟩

@[simp] theorem xiHurwitzOrientationAbsoluteVector_apply (q : XiZeroCopy) :
    xiHurwitzOrientationAbsoluteVector q =
      ((‖xiHurwitzOrientationCoordinate q‖ : ℝ) : ℂ) := rfl

/-- Forgetting orientation signs moves the vector to the reflection-even sector. -/
theorem xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector :
    xiWeilLineConjLp xiHurwitzOrientationAbsoluteVector =
      xiHurwitzOrientationAbsoluteVector := by
  apply Subtype.ext
  funext q
  rw [xiWeilLineConjLp_apply]
  simp only [xiHurwitzOrientationAbsoluteVector_apply,
    xiHurwitzOrientationCoordinate_lineConj, norm_neg]

/-- Sign-forgetting preserves exactly the full orientation energy. -/
theorem norm_sq_xiHurwitzOrientationAbsoluteVector :
    ‖xiHurwitzOrientationAbsoluteVector‖ ^ 2 =
      xiHurwitzOrientationEnergy := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' q : XiZeroCopy,
    ‖((‖xiHurwitzOrientationCoordinate q‖ : ℝ) : ℂ)‖ ^ 2) = _
  rw [← norm_sq_xiHurwitzOrientationVector,
    HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro q
  simp

theorem norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector :
    ‖xiHurwitzOrientationAbsoluteVector‖ = ‖xiHurwitzOrientationVector‖ := by
  have hsq : ‖xiHurwitzOrientationAbsoluteVector‖ ^ 2 =
      ‖xiHurwitzOrientationVector‖ ^ 2 := by
    rw [norm_sq_xiHurwitzOrientationAbsoluteVector,
      norm_sq_xiHurwitzOrientationVector]
  nlinarith [norm_nonneg xiHurwitzOrientationAbsoluteVector,
    norm_nonneg xiHurwitzOrientationVector]

/-- Every Weil-nonnegative vector lies outside the exact orientation exclusion ball. -/
theorem orientation_norm_sq_le_two_mul_dist_sq_of_weil_nonnegative
    (v : XiWeilCarrier) (hv : 0 ≤ xiWeilHilbertQuadratic v) :
    ‖xiHurwitzOrientationVector‖ ^ 2 ≤
      2 * dist v xiHurwitzOrientationVector ^ 2 := by
  rw [dist_eq_norm]
  exact CliffordWeil.antiFixed_norm_sq_le_two_mul_norm_sub_sq_of_quadratic_nonneg
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
    xiWeilLineConjLp_xiHurwitzOrientationVector hv

/-- Literal finite-source form: every source-nonnegative separated packet obeys the sharp
orientation-distance obstruction. -/
theorem orientationEnergy_le_two_mul_packet_dist_sq_of_sourceEnergy_nonnegative
    (P : XiSeparatedContinuedCauchyPacket) (hP : 0 ≤ P.sourceEnergy) :
    xiHurwitzOrientationEnergy ≤
      2 * dist P.evaluation xiHurwitzOrientationVector ^ 2 := by
  rw [← norm_sq_xiHurwitzOrientationVector]
  apply orientation_norm_sq_le_two_mul_dist_sq_of_weil_nonnegative
  rwa [← P.sourceEnergy_eq_hilbertQuadratic]

/-- The exclusion radius is attained by a zero-Weil-energy boundary vector. -/
theorem exists_weilBoundaryVector_at_exact_orientationRadius :
    ∃ v : XiWeilCarrier,
      xiWeilHilbertQuadratic v = 0 ∧
      xiHurwitzOrientationEnergy =
        2 * dist v xiHurwitzOrientationVector ^ 2 := by
  obtain ⟨v, hvq, hvdist⟩ :=
    CliffordWeil.exists_quadratic_zero_with_antiFixed_distance_eq
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
      xiWeilLineConjLp_xiHurwitzOrientationVector
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector
      norm_xiHurwitzOrientationAbsoluteVector_eq_orientationVector
  refine ⟨v, hvq, ?_⟩
  rw [← norm_sq_xiHurwitzOrientationVector, dist_eq_norm]
  exact hvdist

/-- **Exact Route-Q cone geometry.**  The Hurwitz orientation vector has squared distance
`orientationEnergy / 2` from the nonnegative Weil cone, expressed without an infimum or division:
every cone point satisfies the lower bound and one zero-energy boundary point attains it. -/
theorem xiHurwitzOrientation_exact_nonnegativeCone_radius :
    (∀ v : XiWeilCarrier, 0 ≤ xiWeilHilbertQuadratic v →
      xiHurwitzOrientationEnergy ≤
        2 * dist v xiHurwitzOrientationVector ^ 2) ∧
    (∃ v : XiWeilCarrier, xiWeilHilbertQuadratic v = 0 ∧
      xiHurwitzOrientationEnergy =
        2 * dist v xiHurwitzOrientationVector ^ 2) := by
  refine ⟨?_, exists_weilBoundaryVector_at_exact_orientationRadius⟩
  intro v hv
  rw [← norm_sq_xiHurwitzOrientationVector]
  exact orientation_norm_sq_le_two_mul_dist_sq_of_weil_nonnegative v hv

end


end RHTower
