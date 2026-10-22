import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectKernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodEighthAtomPairTrace
/-!
# Complete spectral positivity for curvature-defect cooling

Each literal theta component retains its point mass together with its ray.
Its exact cooling functional is positive; integrability and countable additivity
then give strict positivity for the complete higher-theta spectral measure.
This is an ordinary-moment theorem. The logarithmic cumulant correction remains
a separate mathematical obligation.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
open scoped BigOperators
noncomputable section
def atomMoment (n : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  ∫ t : ℝ, t^j * Real.exp (-(q*t)) ∂thetaCuspAtomLikelihoodSpectralMeasure n

private theorem atomMoment_Two_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    atomMoment n q 2 = Real.exp (-(3/2)*thetaCuspLikelihoodGap n) *
      Real.exp (-q*thetaCuspLikelihoodGap n) * (thetaCuspLikelihoodGap n+1) *
      thetaCuspLikelihoodGap n * momentNumeratorTwo q (thetaCuspLikelihoodGap n) / q^3 := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn 2 hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold momentNumeratorTwo
  field_simp [hq.ne']

private theorem atomMoment_Three_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    atomMoment n q 3 = Real.exp (-(3/2)*thetaCuspLikelihoodGap n) *
      Real.exp (-q*thetaCuspLikelihoodGap n) * (thetaCuspLikelihoodGap n+1) *
      thetaCuspLikelihoodGap n * momentNumeratorThree q (thetaCuspLikelihoodGap n) / q^4 := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn 3 hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold momentNumeratorThree
  field_simp [hq.ne']
  ring

private theorem atomMoment_Four_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    atomMoment n q 4 = Real.exp (-(3/2)*thetaCuspLikelihoodGap n) *
      Real.exp (-q*thetaCuspLikelihoodGap n) * (thetaCuspLikelihoodGap n+1) *
      thetaCuspLikelihoodGap n * momentNumeratorFour q (thetaCuspLikelihoodGap n) / q^5 := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn 4 hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold momentNumeratorFour
  field_simp [hq.ne']
  ring

private theorem atomMoment_Five_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    atomMoment n q 5 = Real.exp (-(3/2)*thetaCuspLikelihoodGap n) *
      Real.exp (-q*thetaCuspLikelihoodGap n) * (thetaCuspLikelihoodGap n+1) *
      thetaCuspLikelihoodGap n * momentNumeratorFive q (thetaCuspLikelihoodGap n) / q^6 := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn 5 hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  norm_num [Finset.sum_range_succ, Nat.choose]
  unfold momentNumeratorFive
  field_simp [hq.ne']
  ring

private theorem atomMoment_Six_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
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

def coolingCoefficient (q : ℝ) : ℕ → ℝ
  | 2 => 12*(4*q+15)
  | 3 => -36*q*(q+3)-24*(4*q+15)*(q+3/2)
  | 4 => 44*q*(q+3)*(q+3/2)+10*(4*q+15)*(q+3/2)^2
  | 5 => -13*q*(q+3)*(q+3/2)^2-(4*q+15)*(q+3/2)^3
  | 6 => q*(q+3)*(q+3/2)^3
  | _ => 0

def coolingFunctional (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, coolingCoefficient q (j+2)*m (j+2)

theorem atom_coolingFunctional_eq {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    coolingFunctional q (atomMoment n q) =
      Real.exp (-(3/2)*thetaCuspLikelihoodGap n) * Real.exp (-q*thetaCuspLikelihoodGap n) *
        (thetaCuspLikelihoodGap n+1)*thetaCuspLikelihoodGap n /
          q^6 * normalizedDefectCoolingKernel q (thetaCuspLikelihoodGap n) := by
  simp only [coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,coolingCoefficient]
  rw [atomMoment_Two_eq hn hq,atomMoment_Three_eq hn hq,atomMoment_Four_eq hn hq,
    atomMoment_Five_eq hn hq,atomMoment_Six_eq hn hq]
  unfold normalizedDefectCoolingKernel
  field_simp [hq.ne']
  ring

theorem atom_coolingFunctional_pos {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 3/2 ≤ q) :
    0 < coolingFunctional q (atomMoment n q) := by
  have hq0 : 0 < q := by linarith
  have hd : 3 ≤ thetaCuspLikelihoodGap n := by
    unfold thetaCuspLikelihoodGap
    have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [atom_coolingFunctional_eq hn hq0]
  have hk := normalizedDefectCoolingKernel_pos hq hd
  positivity
def coolingIntegrand (q t : ℝ) : ℝ :=
  coolingFunctional q (fun j => t^j*Real.exp (-(q*t)))

private theorem integrable_coolingIntegrand (q : ℝ) (μ : Measure ℝ)
    (hm : ∀ j, Integrable (fun t : ℝ => t^j*Real.exp (-(q*t))) μ) :
    Integrable (coolingIntegrand q) μ := by
  unfold coolingIntegrand coolingFunctional
  apply integrable_finsetSum
  intro j _
  exact (hm (j+2)).const_mul _

private theorem integral_coolingIntegrand_eq (q : ℝ) (μ : Measure ℝ)
    (hm : ∀ j, Integrable (fun t : ℝ => t^j*Real.exp (-(q*t))) μ) :
    (∫ t, coolingIntegrand q t ∂μ) =
      coolingFunctional q (fun j => ∫ t : ℝ, t^j*Real.exp (-(q*t)) ∂μ) := by
  unfold coolingIntegrand coolingFunctional
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_const_mul _ _
  · intro j _
    exact (hm (j+2)).const_mul _

theorem full_coolingFunctional_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
  have hq0 : 0 < q := by linarith
  have hm (j : ℕ) : Integrable (fun t : ℝ => t^j*Real.exp (-(q*t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [neg_mul] using
      integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure j hq0
  have hg := integrable_coolingIntegrand q thetaCuspHigherLikelihoodSpectralMeasure hm
  have hi := integral_coolingIntegrand_eq q thetaCuspHigherLikelihoodSpectralMeasure hm
  simp_rw [← neg_mul, ← thetaCuspHigherLikelihoodSpectralMoment_eq_integral] at hi
  have hatom (n : ℕ) :
      (∫ t, coolingIntegrand q t ∂thetaCuspAtomLikelihoodSpectralMeasure (n+2)) =
        coolingFunctional q (atomMoment (n+2) q) := by
    apply integral_coolingIntegrand_eq
    intro j
    exact (hm j).mono_measure (Measure.le_sum _ n)
  change Integrable (coolingIntegrand q)
    (Measure.sum fun n : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (n+2)) at hg
  have hs := hasSum_integral_measure hg
  have hs' : HasSum (fun n : ℕ => coolingFunctional q (atomMoment (n+2) q))
      (coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)) := by
    rw [← hi]
    simpa only [hatom, thetaCuspHigherLikelihoodSpectralMeasure] using hs
  have hp (n : ℕ) : 0 < coolingFunctional q (atomMoment (n+2) q) :=
    atom_coolingFunctional_pos (by omega) hq
  rw [← hs'.tsum_eq]
  exact hs'.summable.tsum_pos (fun n => (hp n).le) 0 (hp 0)
end
end RHTower.ThetaCuspDefect
