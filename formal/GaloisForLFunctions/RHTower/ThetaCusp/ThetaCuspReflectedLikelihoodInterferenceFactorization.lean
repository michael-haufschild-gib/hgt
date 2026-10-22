import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodModularSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSingleAtomReflectedRiccatiContraction

/-!
# Reflected likelihood-interference factorization

On a single modular half-line, the normalized reflected completed theta source splits exactly
into the normalized first-atom model and one positive likelihood-partition cocycle.  This confines
all unequal-index interference to the latter factor.
-/

namespace RHTower

noncomputable section

/-- Positive likelihood cocycle carrying every higher-atom interference contribution to the
normalized reflected completed source. -/
def thetaCuspReflectedLikelihoodInterference (u t : ℝ) : ℝ :=
  thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u + t)) *
      thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u - t)) /
    thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate u) ^ (2 : ℕ)

/-- Negative logarithmic action of the reflected likelihood-interference cocycle. -/
def thetaCuspReflectedLikelihoodInterferenceAction (u t : ℝ) : ℝ :=
  -Real.log (thetaCuspReflectedLikelihoodInterference u t)

/-- The existing positive likelihood representation rewritten as a literal partition
factorization of the completed theta source. -/
theorem thetaCuspFullSource_eq_first_mul_likelihoodPartition
    {x : ℝ} (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspFullSource x =
      thetaCuspSourceTerm x 1 *
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) := by
  calc
    thetaCuspFullSource x =
        thetaCuspSourceTerm x 1 *
          (1 + ∫ s : ℝ, Real.exp (-thetaCuspLikelihoodCoordinate x * s)
            ∂thetaCuspHigherLikelihoodSpectralMeasure) :=
      thetaCuspFullSource_eq_first_mul_one_add_spectralIntegral_of_coordinate_pos hB
    _ = _ := by
      rw [integral_exp_neg_mul_thetaCuspHigherLikelihoodSpectralMeasure hB]
      rfl

/-- Unnormalized reflected source product: exact first-atom model times the two likelihood
partitions. -/
theorem thetaCuspFullSource_reflected_mul_eq_singleAtomModel_mul_likelihoodPartitions
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) =
      thetaCuspSourceTerm u 1 ^ (2 : ℕ) *
          thetaCuspSingleAtomReflectedNormalizedModel
            (thetaCuspSingleAtomReflectionScale 1 u)
            (thetaCuspSingleAtomReflectionDefect t) *
        (thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u + t)) *
          thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u - t))) := by
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hatom :=
    thetaCuspSourceTerm_reflected_mul_eq_singleAtomModel
      (n := 1) (by norm_num) ht htu
  rw [thetaCuspFullSource_eq_first_mul_likelihoodPartition hplus,
    thetaCuspFullSource_eq_first_mul_likelihoodPartition hminus]
  calc
    _ = (thetaCuspSourceTerm (u + t) 1 * thetaCuspSourceTerm (u - t) 1) *
        (thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u + t)) *
          thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (u - t))) := by ring
    _ = _ := by rw [hatom]

/-- **Exact interference factorization.**  The normalized completed reflected source is the
strictly contracting first-atom profile times one positive likelihood cocycle. -/
theorem thetaCuspFullSource_reflected_normalized_eq_singleAtomModel_mul_interference
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
        thetaCuspFullSource u ^ (2 : ℕ) =
      thetaCuspSingleAtomReflectedNormalizedModel
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) *
        thetaCuspReflectedLikelihoodInterference u t := by
  have hu : 0 ≤ u := le_trans ht htu
  have hBu : 0 < thetaCuspLikelihoodCoordinate u :=
    thetaCuspLikelihoodCoordinate_pos hu
  have hfirst := thetaCuspSourceTerm_one_pos_of_likelihoodCoordinate_pos hBu
  have hpart := thetaCuspLikelihoodPartition_pos hBu
  rw [thetaCuspFullSource_reflected_mul_eq_singleAtomModel_mul_likelihoodPartitions ht htu,
    thetaCuspFullSource_eq_first_mul_likelihoodPartition hBu]
  unfold thetaCuspReflectedLikelihoodInterference
  field_simp [hfirst.ne', hpart.ne']

/-- The interference cocycle is strictly positive throughout the same-half-line chamber. -/
theorem thetaCuspReflectedLikelihoodInterference_pos
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    0 < thetaCuspReflectedLikelihoodInterference u t := by
  have hplus : 0 < thetaCuspLikelihoodCoordinate (u + t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hminus : 0 < thetaCuspLikelihoodCoordinate (u - t) :=
    thetaCuspLikelihoodCoordinate_pos (by linarith)
  have hu : 0 ≤ u := le_trans ht htu
  have hcenter : 0 < thetaCuspLikelihoodCoordinate u :=
    thetaCuspLikelihoodCoordinate_pos hu
  unfold thetaCuspReflectedLikelihoodInterference
  exact div_pos
    (mul_pos (thetaCuspLikelihoodPartition_pos hplus)
      (thetaCuspLikelihoodPartition_pos hminus))
    (sq_pos_of_pos (thetaCuspLikelihoodPartition_pos hcenter))

/-- The likelihood-interference cocycle is normalized at the reflection center. -/
theorem thetaCuspReflectedLikelihoodInterference_zero
    {u : ℝ} (hu : 0 ≤ u) :
    thetaCuspReflectedLikelihoodInterference u 0 = 1 := by
  have hB : 0 < thetaCuspLikelihoodCoordinate u :=
    thetaCuspLikelihoodCoordinate_pos hu
  unfold thetaCuspReflectedLikelihoodInterference
  simp only [add_zero, sub_zero]
  field_simp [(thetaCuspLikelihoodPartition_pos hB).ne']

/-- The likelihood-interference cocycle is even in displacement. -/
theorem thetaCuspReflectedLikelihoodInterference_neg (u t : ℝ) :
    thetaCuspReflectedLikelihoodInterference u (-t) =
      thetaCuspReflectedLikelihoodInterference u t := by
  unfold thetaCuspReflectedLikelihoodInterference
  congr 1
  ring

/-- Exact additive action law behind the interference classification. -/
theorem thetaCuspFullSource_reflected_action_eq_singleAtom_add_interference
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    -Real.log
        (thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) /
          thetaCuspFullSource u ^ (2 : ℕ)) =
      thetaCuspSingleAtomReflectedAction
          (thetaCuspSingleAtomReflectionScale 1 u) t +
        thetaCuspReflectedLikelihoodInterferenceAction u t := by
  have hfactor :=
    thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
      (n := 1) (by norm_num) ht htu
  have hmodel : 0 <
      thetaCuspSingleAtomReflectedNormalizedModel
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) := by
    unfold thetaCuspSingleAtomReflectedNormalizedModel
    exact mul_pos hfactor (Real.exp_pos _)
  have hinterference := thetaCuspReflectedLikelihoodInterference_pos ht htu
  rw [thetaCuspFullSource_reflected_normalized_eq_singleAtomModel_mul_interference ht htu,
    Real.log_mul hmodel.ne' hinterference.ne',
    thetaCuspSingleAtomReflectedAction_eq_neg_log_model hfactor.ne']
  unfold thetaCuspReflectedLikelihoodInterferenceAction
  ring

end

end RHTower
