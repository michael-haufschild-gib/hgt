import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.PhaseExtraction.MinimumTargetWeights
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheNonprincipalFilterRecoversTheTarget

/-!
# Minimum-cost extraction of the completed arithmetic row

The unique minimum-energy homogeneous sextic filter extracts the inverse-phase
target of `rowLocalSum`. Its exact cost controls perturbations of these actual
rows after removal of the explicit completion denominator.
-/

noncomputable section
open Complex Finset
open scoped Classical ComplexConjugate InnerProductSpace
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-- Every phase weight satisfying the four extraction tests recovers the
reciprocal target mode of the actual completed local row. -/
theorem sexticReadout_rowLocalSum_of_tests {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (w : Fin 6 → ℂ) (Q R η X Y V : ℂ)
    (h0 : sexticCoefficients ζ w 0 = 0) (h1 : sexticCoefficients ζ w 1 = 1)
    (h5 : sexticCoefficients ζ w 5 = 0)
    (hg : sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) = 0) :
    sexticReadout w (fun i => rowLocalSum Q R η X Y V (ζ ^ i.val)) =
      -(1 - R)⁻¹ * η * X := by
  have hm : sexticReadout w (fun i => ζ ^ i.val) = 0 := by
    have h := sexticReadout_monomial hζ w (k := 1) (by norm_num) (by norm_num)
    simpa only [pow_one, h5] using h
  have hc : sexticReadout w (fun _ => 1) = 0 := by rw [sexticReadout_one ζ w, h0]
  have hi : sexticReadout w (fun i => (ζ ^ i.val)⁻¹) = 1 := by
    rw [sexticReadout_inverse, h1]
  have he (ρ : ℂ) : rowLocalSum Q R η X Y V ρ =
      ((1 - V)⁻¹ + (1 - R)⁻¹ * (R * (1 - Q⁻¹) * (1 - V)⁻¹ -
        η * (Q - 1) * X * Y * V * (1 - V)⁻¹)) * 1 +
      ((1 - R)⁻¹ * Y * R) * ρ - ((1 - R)⁻¹ * η * X) * ρ⁻¹ +
      ρ * Y * (1 - ρ * Y)⁻¹ := by
    unfold rowLocalSum
    ring
  simp_rw [he]
  rw [sexticReadout_add, sexticReadout_sub, sexticReadout_add,
    sexticReadout_mul, sexticReadout_mul, sexticReadout_mul, hc, hm, hi, hg]
  ring

/-- The minimum-energy phase readout on the canonical six phases. -/
def minimumPhaseReadout (Y : ℂ) (f : ℂ → ℂ) : ℂ :=
  sexticReadout (fun i => minimumTargetWeight Y (targetSixthRoot ^ i.val))
    (fun i => f (targetSixthRoot ^ i.val))

private theorem minimum_phase_root : IsPrimitiveRoot targetSixthRoot 6 :=
  Complex.isPrimitiveRoot_exp 6 (by norm_num)

/-- The minimizing filter retains the literal target without subtracting a
geometric correction from the observed rows. -/
theorem minimumPhaseReadout_rowLocalSum (Q R η X Y V : ℂ) (hY : Y ^ 6 ≠ 1) :
    minimumPhaseReadout Y (rowLocalSum Q R η X Y V) = -(1 - R)⁻¹ * η * X := by
  obtain ⟨h0, h1, h5, hg⟩ := minimumTargetWeight_admissible minimum_phase_root Y hY
  exact sexticReadout_rowLocalSum_of_tests minimum_phase_root _ Q R η X Y V h0 h1 h5 hg

/-- Removing the explicit completion denominator recovers the arithmetic coefficient. -/
theorem minimumPhaseReadout_recovers_target (Q R η X Y V : ℂ)
    (hY : Y ^ 6 ≠ 1) (hR : 1 - R ≠ 0) :
    -(1 - R) * minimumPhaseReadout Y (rowLocalSum Q R η X Y V) = η * X := by
  rw [minimumPhaseReadout_rowLocalSum Q R η X Y V hY]
  field_simp

/-- The optimal mean-square cost applies to every observed phase input. -/
theorem norm_minimumPhaseReadout_sq_le (Y : ℂ) (f : ℂ → ℂ) :
    6 * ‖minimumPhaseReadout Y f‖ ^ 2 ≤
      (1 + ‖Y‖ ^ 6 / targetGram Y) *
        ∑ i : Fin 6, ‖f (targetSixthRoot ^ i.val)‖ ^ 2 := by
  have h := norm_sexticReadout_sq_le
    (fun i => minimumTargetWeight Y (targetSixthRoot ^ i.val))
    (fun i => f (targetSixthRoot ^ i.val))
  rw [minimumTargetWeight_energy minimum_phase_root Y] at h
  change 6 * ‖minimumPhaseReadout Y f‖ ^ 2 ≤ _
  change 36 * ‖minimumPhaseReadout Y f‖ ^ 2 ≤ _ at h
  nlinarith only [h]

/-- Perturbations of the actual rows have the optimal squared extraction cost;
the explicit completion multiplier introduces no pole as `R` approaches one. -/
theorem minimumPhaseReadout_target_error (Q R η X Y V : ℂ)
    (hY : Y ^ 6 ≠ 1) (hR : 1 - R ≠ 0) (f : ℂ → ℂ) :
    6 * ‖-(1 - R) * minimumPhaseReadout Y f - η * X‖ ^ 2 ≤
      ‖1 - R‖ ^ 2 * (1 + ‖Y‖ ^ 6 / targetGram Y) *
        ∑ i : Fin 6, ‖f (targetSixthRoot ^ i.val) -
          rowLocalSum Q R η X Y V (targetSixthRoot ^ i.val)‖ ^ 2 := by
  have he : -(1 - R) * minimumPhaseReadout Y f - η * X =
      -(1 - R) * minimumPhaseReadout Y (fun ρ => f ρ - rowLocalSum Q R η X Y V ρ) := by
    rw [minimumPhaseReadout, sexticReadout_sub]
    have ht := minimumPhaseReadout_recovers_target Q R η X Y V hY hR
    change -(1 - R) * minimumPhaseReadout Y f - η * X =
      -(1 - R) * (minimumPhaseReadout Y f - minimumPhaseReadout Y (rowLocalSum Q R η X Y V))
    linear_combination -ht
  have hn := norm_minimumPhaseReadout_sq_le Y (fun ρ => f ρ - rowLocalSum Q R η X Y V ρ)
  rw [he, norm_mul, norm_neg, mul_pow]
  calc
    _ = ‖1 - R‖ ^ 2 * (6 * ‖minimumPhaseReadout Y
      (fun ρ => f ρ - rowLocalSum Q R η X Y V ρ)‖ ^ 2) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (sq_nonneg ‖1 - R‖)

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
