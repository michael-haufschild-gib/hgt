import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectMoments
/-!
# A complete spectral reserve for nonlinear curvature-defect terms

Exact coupled point-and-ray moments retain a fixed positive portion of the
sixth-moment scale. Countable additivity transports that reserve to the
complete spectral source and its normalized likelihood state.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
noncomputable section

theorem hasSum_atomMoment {q : ℝ} (hq : 0 < q) (j : ℕ) :
    HasSum (fun n : ℕ => atomMoment (n+2) q j)
      (thetaCuspHigherLikelihoodSpectralMoment q j) := by
  have hm : Integrable (fun t : ℝ => t^j*Real.exp (-(q*t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [neg_mul] using
      integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure j hq
  have hi : (∫ t : ℝ, t^j*Real.exp (-(q*t))
      ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      thetaCuspHigherLikelihoodSpectralMoment q j := by
    simpa only [neg_mul] using
      (thetaCuspHigherLikelihoodSpectralMoment_eq_integral q j).symm
  change Integrable (fun t : ℝ => t^j*Real.exp (-(q*t)))
    (Measure.sum fun n : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (n+2)) at hm
  rw [← hi]
  simpa only [atomMoment,thetaCuspHigherLikelihoodSpectralMeasure] using
    hasSum_integral_measure hm

theorem hasSum_atomCooling {q : ℝ} (hq : 0 < q) :
    HasSum (fun n : ℕ => coolingFunctional q (atomMoment (n+2) q))
      (coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)) := by
  unfold coolingFunctional
  have h (j : ℕ) : HasSum
      (fun n : ℕ => coolingCoefficient q (j+2)*atomMoment (n+2) q (j+2))
      (coolingCoefficient q (j+2)*thetaCuspHigherLikelihoodSpectralMoment q (j+2)) :=
    (hasSum_atomMoment hq (j+2)).mul_left _
  exact hasSum_sum (fun j _ => h j)
private theorem atomMoment_six_closed {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    atomMoment n q 6 = Real.exp (-(3/2)*thetaCuspLikelihoodGap n) *
      Real.exp (-q*thetaCuspLikelihoodGap n) * (thetaCuspLikelihoodGap n+1) *
      thetaCuspLikelihoodGap n * momentNumeratorSix q (thetaCuspLikelihoodGap n) / q^7 := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn 6 hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold momentNumeratorSix
  field_simp [hq.ne']
  ring

private theorem kernel_reserve_shift (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    coolingCoefficient (3/2+y) 6*momentNumeratorSix (3/2+y) (3+v) ≤
      1000*(3/2+y)*normalizedDefectCoolingKernel (3/2+y) (3+v) := by
  apply sub_nonneg.mp
  simp only [coolingCoefficient]
  unfold normalizedDefectCoolingKernel momentNumeratorTwo momentNumeratorThree
    momentNumeratorFour momentNumeratorFive momentNumeratorSix
  ring_nf
  positivity

theorem kernel_reserve {q d : ℝ} (hq : 3/2 ≤ q) (hd : 3 ≤ d) :
    coolingCoefficient q 6*momentNumeratorSix q d ≤
      1000*q*normalizedDefectCoolingKernel q d := by
  have h := kernel_reserve_shift (q-3/2) (d-3) (by linarith) (by linarith)
  simpa only [show 3/2+(q-3/2)=q by ring,show 3+(d-3)=d by ring] using h

theorem atom_cooling_reserve {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 3/2 ≤ q) :
    coolingCoefficient q 6*atomMoment n q 6 ≤ 1000*coolingFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith
  have hd : 3 ≤ thetaCuspLikelihoodGap n := by
    unfold thetaCuspLikelihoodGap
    have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  let F := Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
    (thetaCuspLikelihoodGap n+1)*thetaCuspLikelihoodGap n/q^7
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h := mul_le_mul_of_nonneg_left (kernel_reserve hq hd) hF
  rw [atom_coolingFunctional_eq hn hq0,atomMoment_six_closed hn hq0]
  calc
    _ = F*(coolingCoefficient q 6*momentNumeratorSix q (thetaCuspLikelihoodGap n)) := by
      dsimp only [F]
      ring
    _ ≤ F*(1000*q*normalizedDefectCoolingKernel q (thetaCuspLikelihoodGap n)) := h
    _ = _ := by
      dsimp only [F]
      field_simp [hq0.ne'] <;> ring

theorem full_cooling_reserve {q : ℝ} (hq : 3/2 ≤ q) :
    coolingCoefficient q 6*thetaCuspHigherLikelihoodSpectralMoment q 6 ≤
      1000*coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
  have hq0 : 0 < q := by linarith
  exact hasSum_le (fun n => atom_cooling_reserve (by omega) hq)
    ((hasSum_atomMoment hq0 6).mul_left _) ((hasSum_atomCooling hq0).mul_left _)

theorem cooling_normalized_eq {q : ℝ} :
    coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q) =
      coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)/thetaCuspLikelihoodPartition q := by
  simp only [coolingFunctional,thetaCuspLikelihoodNormalizedMoment,Finset.sum_div,mul_div_assoc]

theorem normalized_cooling_reserve {q : ℝ} (hq : 3/2 ≤ q) :
    coolingCoefficient q 6*thetaCuspLikelihoodNormalizedMoment q 6 ≤
      1000*coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q) := by
  have hq0 : 0 < q := by linarith
  rw [cooling_normalized_eq,thetaCuspLikelihoodNormalizedMoment,←mul_div_assoc,←mul_div_assoc]
  exact (div_le_div_iff_of_pos_right (thetaCuspLikelihoodPartition_pos hq0)).2
    (full_cooling_reserve hq)
end
end RHTower.ThetaCuspDefect
