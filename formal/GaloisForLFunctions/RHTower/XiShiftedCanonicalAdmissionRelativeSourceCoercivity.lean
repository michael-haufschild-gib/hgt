import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionSourceRecession

/-!
# Relative coercivity of canonical shifted-Xi source admission

The absolute arcsine source margin of the monic degree-`n` admission decays exponentially because
the monic Chebyshev norm does.  Dividing by that intrinsic admitted norm removes the coordinate
collapse: the source-to-norm ratio is exactly `n + 3/8` in every positive degree.

For the actual shifted-Xi inverse-Hankel admission, the mass-scaled literal rational--Gamma minus
von Mangoldt source divided by the normalized admitted norm converges to the same linearly growing
ratio.  This identifies the precise remaining obstruction: fixed-degree source recession is
relatively coercive, so only absence of a degree-uniform diagonal convergence rate can permit
cofinal face escape.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower

noncomputable section

namespace XiShiftedArcsineAdmission

/-- Exact squared norm of the monic shifted-Chebyshev admission on the arcsine face. -/
theorem momentFunctional_amplitude_sq
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((amplitude n) ^ 2) =
      monicScale n ^ 2 / 2 := by
  have hsq :
      (amplitude n) ^ 2 =
        monicScale n ^ 2 •
          ((Polynomial.Chebyshev.T ℝ n) ^ 2).comp affine := by
    simp only [amplitude, Polynomial.smul_eq_C_mul, Polynomial.pow_comp]
    rw [Polynomial.C_pow]
    ring
  rw [hsq, HTGeometry.momentFunctional_smul]
  change monicScale n ^ 2 * L ((Polynomial.Chebyshev.T ℝ n) ^ 2) = _
  rw [show (Polynomial.Chebyshev.T ℝ n) ^ 2 =
      Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ n by ring,
    L_T_mul_self_of_ne_zero hn]
  ring

/-- **Scale-free arcsine source law.**  Exponential decay of the absolute monic source margin is
exactly the decay of the admitted orthogonal norm; their ratio grows linearly with degree. -/
theorem momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) =
      ((n : ℝ) + 3 / 8) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((amplitude n) ^ 2) := by
  by_cases hn1 : n = 1
  · subst n
    rw [momentFunctional_adaptiveShear_amplitude_one,
      momentFunctional_amplitude_sq (by omega)]
    norm_num [monicScale]
  · have hn2 : 2 ≤ n := by omega
    rw [momentFunctional_adaptiveShear_amplitude_of_two_le hn2,
      momentFunctional_amplitude_sq hn]
    ring

/-- The admitted arcsine norm is strictly positive in every positive degree. -/
theorem momentFunctional_amplitude_sq_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((amplitude n) ^ 2) := by
  rw [momentFunctional_amplitude_sq hn]
  have hs : 0 < monicScale n := by
    unfold monicScale
    exact inv_pos.mpr (pow_pos (by norm_num) _)
  positivity

/-- The scale-free source margin strictly dominates degree times admitted norm. -/
theorem degree_mul_momentFunctional_amplitude_sq_lt_adaptiveShear
    {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) *
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((amplitude n) ^ 2) <
      HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        (xiShiftedBoundaryAdaptiveShearPolynomial (amplitude n)) := by
  rw [momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear hn]
  have hnorm := momentFunctional_amplitude_sq_pos hn
  nlinarith

end XiShiftedArcsineAdmission

namespace XiShiftedCanonicalAdmission

/-- Normalized squared norm of the actual dimensionless inverse-Hankel admission. -/
def normalizedAdmissionNorm (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
    ((dimensionlessAdmission w n) ^ 2)

/-- Normalized adaptive source of the same admission, formed before any reporting map. -/
def normalizedAdmissionSource (w : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
    (xiShiftedBoundaryAdaptiveShearPolynomial (dimensionlessAdmission w n))

/-- Coefficientwise convergence of a finite polynomial curve passes to its square. -/
theorem tendsto_sq_coeff
    {α : Type*} {l : Filter α} {F : α → Polynomial ℝ} {P : Polynomial ℝ}
    (hcoeff : ∀ k, Tendsto (fun x => (F x).coeff k) l (nhds (P.coeff k)))
    (k : ℕ) :
    Tendsto (fun x => ((F x) ^ 2).coeff k) l (nhds ((P ^ 2).coeff k)) := by
  simp only [pow_two, Polynomial.coeff_mul]
  apply tendsto_finsetSum
  intro ij _
  exact (hcoeff ij.1).mul (hcoeff ij.2)

/-- The normalized admitted norm converges to the exact arcsine admitted norm. -/
theorem tendsto_normalizedAdmissionNorm
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => normalizedAdmissionNorm w n) atTop
      (nhds (HTGeometry.momentFunctional
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom
        ((Arc.amplitude n) ^ 2))) := by
  let N := 2 * n
  have hterms : ∀ k ∈ Finset.range (N + 1),
      Tendsto
        (fun w : ℝ => ((dimensionlessAdmission w n) ^ 2).coeff k *
          xiShiftedFarRightNormalizedMoment w k)
        atTop
        (nhds (((Arc.amplitude n) ^ 2).coeff k *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom k)) := by
    intro k _
    exact (tendsto_sq_coeff
      (fun j => tendsto_dimensionlessAdmission_coeff hn j) k).mul
        (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k)
  have hsum := tendsto_finsetSum (Finset.range (N + 1)) hterms
  have hdegXi : ∀ w : ℝ, ((dimensionlessAdmission w n) ^ 2).natDegree ≤ N := by
    intro w
    rw [Polynomial.natDegree_pow, dimensionlessAdmission_natDegree]
  have hdegArc : ((Arc.amplitude n) ^ 2).natDegree ≤ N := by
    rw [Polynomial.natDegree_pow, amplitude_natDegree hn]
  simpa only [normalizedAdmissionNorm,
      momentFunctional_eq_sum_range_of_natDegree_le
        (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom) hdegArc] using
    hsum.congr' (Filter.Eventually.of_forall fun w => by
      rw [momentFunctional_eq_sum_range_of_natDegree_le
        (s := xiShiftedFarRightNormalizedMoment w) (hdegXi w)])

/-- The normalized adaptive source-to-admitted-norm ratio converges to `n + 3/8`. -/
theorem tendsto_normalizedAdmissionSource_div_norm
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto
      (fun w : ℝ => normalizedAdmissionSource w n / normalizedAdmissionNorm w n)
      atTop (nhds ((n : ℝ) + 3 / 8)) := by
  have hsource := tendsto_dimensionlessAdmission_adaptiveShearMoment hn
  have hnorm := tendsto_normalizedAdmissionNorm hn
  have hnormPos := XiShiftedArcsineAdmission.momentFunctional_amplitude_sq_pos hn
  have hdiv := hsource.div hnorm (ne_of_gt hnormPos)
  have hlimit :
      HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          (xiShiftedBoundaryAdaptiveShearPolynomial (Arc.amplitude n)) /
        HTGeometry.momentFunctional
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom
          ((Arc.amplitude n) ^ 2) =
        (n : ℝ) + 3 / 8 := by
    rw [XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear hn]
    field_simp [ne_of_gt hnormPos]
  rw [hlimit] at hdiv
  apply hdiv.congr'
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Literal mass-scaled rational--Gamma minus von Mangoldt source, divided by intrinsic normalized
admitted norm. -/
def relativeArithmeticSource (w : ℝ) (n : ℕ) : ℝ :=
  (w ^ (4 * n + 5) / Real.log w *
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (sourceCoordinateAdmission w n)) /
    normalizedAdmissionNorm w n

/-- Before taking any limit, the relative arithmetic source is exactly the normalized adaptive
source quotient. -/
theorem relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm
    {w : ℝ} (hw : 1 < w) (n : ℕ) :
    relativeArithmeticSource w n =
      normalizedAdmissionSource w n / normalizedAdmissionNorm w n := by
  rw [relativeArithmeticSource, normalizedAdmissionSource,
    sourceCoordinateAdmission,
    scaled_arithmeticSource_sourceCoordinateDilation hw n (dimensionlessAdmission w n)]

/-- **Relative canonical arithmetic-source recession.**  The literal completed source has a
linearly growing, not exponentially collapsing, source-to-admitted-norm limit. -/
theorem tendsto_relativeArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ => relativeArithmeticSource w n) atTop
      (nhds ((n : ℝ) + 3 / 8)) := by
  apply (tendsto_normalizedAdmissionSource_div_norm hn).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  exact (relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm hw n).symm

/-- Every fixed positive degree eventually has relative arithmetic-source margin strictly larger
than the degree itself. -/
theorem relativeArithmeticSource_eventually_gt_degree
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w : ℝ in atTop, (n : ℝ) < relativeArithmeticSource w n := by
  have htarget : (n : ℝ) < (n : ℝ) + 3 / 8 := by norm_num
  exact (tendsto_relativeArithmeticSource hn).eventually (Ioi_mem_nhds htarget)

end XiShiftedCanonicalAdmission

end

end RHTower
