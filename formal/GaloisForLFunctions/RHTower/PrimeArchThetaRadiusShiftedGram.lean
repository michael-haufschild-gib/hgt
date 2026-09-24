import GaloisForLFunctions.HTGeometry.MonotoneRadiusShiftedGram
import GaloisForLFunctions.RHTower.PrimeArchThetaMonotoneGramRatio

/-!
# A second shifted Gram cone from the decreasing theta density

The derivative of `x^3 (x^4 + α*x^2 + β)^2` is nonnegative after integration
against any decreasing density.  For the completed theta source this yields
the shifted radius-mixing Gram form in its first five normalized moments.
-/

open MeasureTheory Set
namespace RHTower
noncomputable section

private theorem integrableOn_thetaCuspRadiusQuadratic (α β : ℝ) :
    IntegrableOn
      (fun x : ℝ => thetaCuspFullSource x *
        GaloisForLFunctions.HTGeometry.radiusQuadraticDerivative α β x)
      (Ioi 0) := by
  have h10 := (integrableOn_thetaCuspRawMoment 10).const_mul (11 : ℝ)
  have h8 := (integrableOn_thetaCuspRawMoment 8).const_mul (18 * α)
  have h6 := (integrableOn_thetaCuspRawMoment 6).const_mul
    (7 * α ^ (2 : ℕ) + 14 * β)
  have h4 := (integrableOn_thetaCuspRawMoment 4).const_mul (10 * α * β)
  have h2 := (integrableOn_thetaCuspRawMoment 2).const_mul (3 * β ^ (2 : ℕ))
  have hsum : IntegrableOn _ (Ioi (0 : ℝ)) :=
    ((((h10.add h8).add h6).add h4).add h2)
  apply hsum.congr_fun
  · intro x _
    simp only [Pi.add_apply]
    dsimp [GaloisForLFunctions.HTGeometry.radiusQuadraticDerivative]
    ring
  · exact measurableSet_Ioi

/-- The positive shifted radius-mixing form in raw completed theta moments. -/
theorem thetaCuspRawEvenMoment_radiusQuadratic_nonneg (α β : ℝ) :
    0 ≤ 11 * thetaCuspRawEvenMoment 5 +
      (18 * α) * thetaCuspRawEvenMoment 4 +
      (7 * α ^ (2 : ℕ) + 14 * β) * thetaCuspRawEvenMoment 3 +
      (10 * α * β) * thetaCuspRawEvenMoment 2 +
      (3 * β ^ (2 : ℕ)) * thetaCuspRawEvenMoment 1 := by
  have hanti0 : AntitoneOn thetaCuspFullSource (Ici (0 : ℝ)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    · have hprod := strictAntiOn_thetaCuspFullSource_mul_reflect 0 hs ht hst
      simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at hprod
      nlinarith [thetaCuspFullSource_pos_all s, thetaCuspFullSource_pos_all t]
  have hanti : AntitoneOn thetaCuspFullSource (Ioi (0 : ℝ)) :=
    hanti0.mono Ioi_subset_Ici_self
  have hder (x : ℝ) (hx : 0 < x) : deriv thetaCuspFullSource x ≤ 0 := by
    rw [← derivWithin_of_isOpen isOpen_Ioi hx]
    exact hanti.derivWithin_nonpos
  have h := GaloisForLFunctions.HTGeometry.antitone_density_radiusQuadratic_Ioi
    thetaCuspFullSource
    (contDiff_thetaCuspFullSource.differentiable (by simp))
    (contDiff_thetaCuspFullSource.continuous_deriv (by simp))
    (fun x _ => (thetaCuspFullSource_pos_all x).le)
    hder α β (integrableOn_thetaCuspRadiusQuadratic α β)
  have h10 := (integrableOn_thetaCuspRawMoment 10).const_mul (11 : ℝ)
  have h8 := (integrableOn_thetaCuspRawMoment 8).const_mul (18 * α)
  have h6 := (integrableOn_thetaCuspRawMoment 6).const_mul
    (7 * α ^ (2 : ℕ) + 14 * β)
  have h4 := (integrableOn_thetaCuspRawMoment 4).const_mul (10 * α * β)
  have h2 := (integrableOn_thetaCuspRawMoment 2).const_mul (3 * β ^ (2 : ℕ))
  have hsum : IntegrableOn _ (Ioi (0 : ℝ)) :=
    (((h10.add h8).add h6).add h4)
  have heq :
      (∫ x : ℝ in Ioi 0, thetaCuspFullSource x *
        GaloisForLFunctions.HTGeometry.radiusQuadraticDerivative α β x) =
      11 * (∫ x : ℝ in Ioi 0, x ^ (10 : ℕ) * thetaCuspFullSource x) +
        (18 * α) * (∫ x : ℝ in Ioi 0, x ^ (8 : ℕ) * thetaCuspFullSource x) +
        (7 * α ^ (2 : ℕ) + 14 * β) *
          (∫ x : ℝ in Ioi 0, x ^ (6 : ℕ) * thetaCuspFullSource x) +
        (10 * α * β) *
          (∫ x : ℝ in Ioi 0, x ^ (4 : ℕ) * thetaCuspFullSource x) +
        (3 * β ^ (2 : ℕ)) *
          (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspFullSource x) := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (((((fun x : ℝ => 11 * (x ^ (10 : ℕ) * thetaCuspFullSource x)) +
            (fun x => (18 * α) * (x ^ (8 : ℕ) * thetaCuspFullSource x))) +
            (fun x => (7 * α ^ (2 : ℕ) + 14 * β) *
              (x ^ (6 : ℕ) * thetaCuspFullSource x))) +
            (fun x => (10 * α * β) * (x ^ (4 : ℕ) * thetaCuspFullSource x))) +
            (fun x => (3 * β ^ (2 : ℕ)) *
              (x ^ (2 : ℕ) * thetaCuspFullSource x))) x := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [Pi.add_apply]
              dsimp [GaloisForLFunctions.HTGeometry.radiusQuadraticDerivative]
              ring
      _ = _ := by
        have hsplit1 := integral_add hsum h2
        have hsplit2 := integral_add ((h10.add h8).add h6) h4
        have hsplit3 := integral_add (h10.add h8) h6
        have hsplit4 := integral_add h10 h8
        simp only [Pi.add_apply, integral_const_mul] at hsplit1 hsplit2 hsplit3 hsplit4
        simp only [Pi.add_apply]
        linear_combination hsplit1 + hsplit2 + hsplit3 + hsplit4
  rw [heq] at h
  simp only [thetaCuspRawEvenMoment, Nat.reduceMul] at ⊢
  nlinarith [h]

/-- The decreasing source's extra radius-moment cone after normalization. -/
theorem thetaCuspNormalizedEvenMoment_radiusQuadratic_nonneg (α β : ℝ) :
    0 ≤ 11 * thetaCuspNormalizedEvenMoment 5 +
      (18 * α) * thetaCuspNormalizedEvenMoment 4 +
      (7 * α ^ (2 : ℕ) + 14 * β) * thetaCuspNormalizedEvenMoment 3 +
      (10 * α * β) * thetaCuspNormalizedEvenMoment 2 +
      (3 * β ^ (2 : ℕ)) * thetaCuspNormalizedEvenMoment 1 := by
  have hraw := thetaCuspRawEvenMoment_radiusQuadratic_nonneg α β
  have hscaled := mul_nonneg hraw
    (inv_nonneg.mpr thetaCuspRawEvenMoment_zero_pos.le)
  simp only [thetaCuspNormalizedEvenMoment, div_eq_mul_inv]
  ring_nf at hscaled ⊢
  exact hscaled

end
end RHTower
