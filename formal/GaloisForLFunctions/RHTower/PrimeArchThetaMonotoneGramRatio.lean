import GaloisForLFunctions.HTGeometry.MonotoneWeightedMonicQuadratic
import GaloisForLFunctions.HTGeometry.MonotoneQuadraticResidualAlgebra
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.ThetaCuspNormalizedShiftedGramStrict

/-!
# Relative weighted-Gram floor for the literal theta source

The completed theta source decreases on the positive half-line.  The sharp
monic-quadratic floor for decreasing densities therefore applies to every
quadratic test polynomial, with a fraction of the fifth source moment on the
right.  This is scale invariant and does not depend on a chosen flat window.
-/

open MeasureTheory Set
namespace RHTower
noncomputable section

private theorem integrableOn_thetaCuspMonicQuadraticNorm (α β : ℝ) :
    IntegrableOn
      (fun x : ℝ => x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) *
          thetaCuspFullSource x) (Ioi 0) := by
  have h10 := integrableOn_thetaCuspRawMoment 10
  have h8 := integrableOn_thetaCuspRawMoment 8
  have h6 := integrableOn_thetaCuspRawMoment 6
  have h4 := integrableOn_thetaCuspRawMoment 4
  have h2 := integrableOn_thetaCuspRawMoment 2
  have hsum := (((h10.add (h8.const_mul (2 * α))).add
    (h6.const_mul (α ^ (2 : ℕ) + 2 * β))).add
    (h4.const_mul (2 * α * β))).add
    (h2.const_mul (β ^ (2 : ℕ)))
  apply hsum.congr_fun
  · intro x _
    simp only [Pi.add_apply]
    ring
  · exact measurableSet_Ioi

/-- Sharp scale-invariant residual floor for every monic quadratic tested
against the actual completed theta density. -/
theorem thetaCuspFullSource_monicQuadratic_relative_floor (α β : ℝ) :
    (64 / 3969 : ℝ) *
      (∫ x : ℝ in Ioi 0, x ^ (10 : ℕ) * thetaCuspFullSource x) ≤
      ∫ x : ℝ in Ioi 0,
        x ^ (2 : ℕ) *
          (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) *
            thetaCuspFullSource x := by
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
  exact GaloisForLFunctions.HTGeometry.weighted_monic_quadratic_antitone_floor_Ioi
    thetaCuspFullSource
    (contDiff_thetaCuspFullSource.differentiable (by simp))
    (contDiff_thetaCuspFullSource.continuous_deriv (by simp))
    (fun x _ => (thetaCuspFullSource_pos_all x).le)
    hder α β
    (integrableOn_thetaCuspRawMoment 10)
    (integrableOn_thetaCuspMonicQuadraticNorm α β)

/-- The same relative floor in raw theta moments. -/
theorem thetaCuspRawEvenMoment_monicQuadratic_relative_floor (α β : ℝ) :
    (64 / 3969 : ℝ) * thetaCuspRawEvenMoment 5 ≤
      thetaCuspRawEvenMoment 5 + 2 * α * thetaCuspRawEvenMoment 4 +
        (α ^ (2 : ℕ) + 2 * β) * thetaCuspRawEvenMoment 3 +
        2 * α * β * thetaCuspRawEvenMoment 2 +
        β ^ (2 : ℕ) * thetaCuspRawEvenMoment 1 := by
  have h := thetaCuspFullSource_monicQuadratic_relative_floor α β
  have hsum := (((integrableOn_thetaCuspRawMoment 10).add
    ((integrableOn_thetaCuspRawMoment 8).const_mul (2 * α))).add
    ((integrableOn_thetaCuspRawMoment 6).const_mul (α ^ (2 : ℕ) + 2 * β))).add
    ((integrableOn_thetaCuspRawMoment 4).const_mul (2 * α * β))
  have heq :
      (∫ x : ℝ in Ioi 0,
        x ^ (2 : ℕ) *
          (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) *
            thetaCuspFullSource x) =
      (∫ x : ℝ in Ioi 0, x ^ (10 : ℕ) * thetaCuspFullSource x) +
        (2 * α) * (∫ x : ℝ in Ioi 0, x ^ (8 : ℕ) * thetaCuspFullSource x) +
        (α ^ (2 : ℕ) + 2 * β) *
          (∫ x : ℝ in Ioi 0, x ^ (6 : ℕ) * thetaCuspFullSource x) +
        (2 * α * β) *
          (∫ x : ℝ in Ioi 0, x ^ (4 : ℕ) * thetaCuspFullSource x) +
        β ^ (2 : ℕ) *
          (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspFullSource x) := by
    calc
      _ = ∫ x : ℝ in Ioi 0,
          (((((fun x : ℝ => x ^ (10 : ℕ) * thetaCuspFullSource x) +
            (fun x => (2 * α) * (x ^ (8 : ℕ) * thetaCuspFullSource x))) +
            (fun x => (α ^ (2 : ℕ) + 2 * β) *
              (x ^ (6 : ℕ) * thetaCuspFullSource x))) +
            (fun x => (2 * α * β) * (x ^ (4 : ℕ) * thetaCuspFullSource x))) +
            (fun x => β ^ (2 : ℕ) * (x ^ (2 : ℕ) * thetaCuspFullSource x))) x := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [Pi.add_apply]
              ring
      _ = _ := by
        have h1 := integral_add hsum
          ((integrableOn_thetaCuspRawMoment 2).const_mul (β ^ (2 : ℕ)))
        have h2 := integral_add
          (((integrableOn_thetaCuspRawMoment 10).add
            ((integrableOn_thetaCuspRawMoment 8).const_mul (2 * α))).add
            ((integrableOn_thetaCuspRawMoment 6).const_mul (α ^ (2 : ℕ) + 2 * β)))
          ((integrableOn_thetaCuspRawMoment 4).const_mul (2 * α * β))
        have h3 := integral_add
          ((integrableOn_thetaCuspRawMoment 10).add
            ((integrableOn_thetaCuspRawMoment 8).const_mul (2 * α)))
          ((integrableOn_thetaCuspRawMoment 6).const_mul (α ^ (2 : ℕ) + 2 * β))
        have h4 := integral_add (integrableOn_thetaCuspRawMoment 10)
          ((integrableOn_thetaCuspRawMoment 8).const_mul (2 * α))
        simp only [Pi.add_apply, integral_const_mul] at h1 h2 h3 h4
        simp only [Pi.add_apply]
        linear_combination h1 + h2 + h3 + h4
  rw [heq] at h
  simp only [thetaCuspRawEvenMoment, Nat.reduceMul] at ⊢
  nlinarith [h]

/-- The relative floor holds after normalizing by the theta source mass. -/
theorem thetaCuspNormalizedEvenMoment_monicQuadratic_relative_floor (α β : ℝ) :
    (64 / 3969 : ℝ) * thetaCuspNormalizedEvenMoment 5 ≤
      thetaCuspNormalizedEvenMoment 5 +
        2 * α * thetaCuspNormalizedEvenMoment 4 +
        (α ^ (2 : ℕ) + 2 * β) * thetaCuspNormalizedEvenMoment 3 +
        2 * α * β * thetaCuspNormalizedEvenMoment 2 +
        β ^ (2 : ℕ) * thetaCuspNormalizedEvenMoment 1 := by
  have hraw := thetaCuspRawEvenMoment_monicQuadratic_relative_floor α β
  have hscaled := mul_le_mul_of_nonneg_right hraw
    (inv_nonneg.mpr thetaCuspRawEvenMoment_zero_pos.le)
  simp only [thetaCuspNormalizedEvenMoment, div_eq_mul_inv]
  ring_nf at hscaled ⊢
  exact hscaled

/-- The literal theta source has a scale-invariant gap above the shifted
three-by-three Gram boundary. -/
theorem thetaCuspNormalizedEvenMoment_shiftedGram_relative_floor :
    (64 / 3969 : ℝ) *
        (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
          thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ)) *
        thetaCuspNormalizedEvenMoment 5 ≤
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 3 -
        thetaCuspNormalizedEvenMoment 2 ^ (2 : ℕ)) *
        thetaCuspNormalizedEvenMoment 5 -
      (thetaCuspNormalizedEvenMoment 1 * thetaCuspNormalizedEvenMoment 4 ^ (2 : ℕ) -
        2 * thetaCuspNormalizedEvenMoment 2 * thetaCuspNormalizedEvenMoment 3 *
          thetaCuspNormalizedEvenMoment 4 +
        thetaCuspNormalizedEvenMoment 3 ^ (3 : ℕ)) := by
  exact GaloisForLFunctions.HTGeometry.relative_monicQuadratic_floor_implies_shiftedGram_ratio
    _ _ _ _ _ thetaCuspNormalizedEvenMoment_shifted_q_pos
    thetaCuspNormalizedEvenMoment_monicQuadratic_relative_floor

end
end RHTower
