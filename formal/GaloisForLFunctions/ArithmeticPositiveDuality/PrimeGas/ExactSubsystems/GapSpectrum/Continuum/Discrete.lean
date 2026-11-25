import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.ScaleConvergence
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Instances.PNat

/-! # Gibbs probabilities on integer labels and reduced energy gaps -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open MeasureTheory

/-- Occupation labels carry the Borel sets of their discrete metric topology. -/
scoped instance labelMeasurableSpace : MeasurableSpace ℕ+ := borel ℕ+
scoped instance labelBorelSpace : BorelSpace ℕ+ := ⟨rfl⟩

abbrev ReducedDirection := {q : ℕ+ × ℕ+ // q.1.Coprime q.2}

/-- The real partition in the trace half-plane is positive. -/
private theorem zeta_norm_real {u : ℝ} (hu : 1 < u) :
    (‖riemannZeta (u:ℂ)‖:ℂ) = riemannZeta (u:ℂ) := by
  rw [← thermalWeight_partition (⟨u,hu⟩ : TraceTemperature)]
  rw [Complex.norm_of_nonneg (tsum_nonneg (fun k => (thermalWeight_pos _ k).le))]

/-- The pair amplitude equals the product of the individual normalized Gibbs weights. -/
theorem gapAmplitude_product {x : ℝ} (hx : 1/2 < x) (q : ℕ+ × ℕ+) :
    gapAmplitude x q = commonScaleWeight (x/2) q.1 * commonScaleWeight (x/2) q.2 := by
  simp only [gapAmplitude,commonScaleWeight,show 4*(x/2) = x+x by ring,heat_mul]
  rw [zeta_norm_real (by linarith : 1 < x+x)]
  simp only [div_eq_mul_inv,pow_two,mul_inv_rev]
  ring

theorem primitive_line_positive {x : ℝ} (hx : 1/2 < x) (d : ReducedDirection) :
    ∃ r : ℝ, 0 < r ∧ (r:ℂ) = overlapCoefficient x (gapFrequency d.val) := by
  rcases d with ⟨⟨a,b⟩,hc⟩
  have h := gapAmplitude_disintegrates hx hc 1
  rw [mul_one,mul_one,gapAmplitude_product hx] at h
  obtain ⟨u,hu,heu⟩ := commonScaleWeight_positive (by linarith : 1/4 < x/2) a
  obtain ⟨v,hv,hev⟩ := commonScaleWeight_positive (by linarith : 1/4 < x/2) b
  obtain ⟨w,hw,hew⟩ := commonScaleWeight_positive (by linarith : 1/4 < x) 1
  change commonScaleWeight (x/2) a * commonScaleWeight (x/2) b =
    overlapCoefficient x (gapFrequency (a,b)) * commonScaleWeight x 1 at h
  refine ⟨u*v/w,div_pos (mul_pos hu hv) hw,?_⟩
  rw [Complex.ofReal_div,Complex.ofReal_mul,heu,hev]
  exact (div_eq_iff (Complex.ofReal_ne_zero.mpr hw.ne')).mpr (by simpa only [hew] using h)

private def realMassPMF {ι : Type*} (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) : PMF ι := by
  refine ⟨fun i => ENNReal.ofReal (p i),?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← ENNReal.toNNReal_one]
  simpa using hs.toNNReal hp

/-- The common-scale weight is a probability whenever its own partition is finite. -/
def scalePMF (x : ℝ) (hx : 1/4 < x) : PMF ℕ+ :=
  realMassPMF (fun k => (commonScaleWeight x k).re) (fun k => by
    obtain ⟨r,hr,he⟩ := commonScaleWeight_positive hx k
    rw [← he,Complex.ofReal_re]
    exact hr.le) (commonScaleReal_hasSum hx)

def scaleLaw (x : ℝ) (hx : 1/4 < x) : ProbabilityMeasure ℕ+ :=
  ⟨(scalePMF x hx).toMeasure,inferInstance⟩

theorem scaleLaw_atom {x : ℝ} (hx : 1/4 < x) (k : ℕ+) :
    (scaleLaw x hx : Measure ℕ+) {k} = ENNReal.ofReal (commonScaleWeight x k).re :=
  (scalePMF x hx).toMeasure_apply_singleton k (measurableSet_singleton k)

/-- Probability of a primitive direction from its measured Fourier line. -/
def directionPMF (x : ℝ) (hx : 1/2 < x) : PMF ReducedDirection :=
  realMassPMF (fun d : ReducedDirection => (overlapCoefficient x (gapFrequency d.val)).re) (fun d => by
    obtain ⟨r,hr,he⟩ := primitive_line_positive hx d
    rw [← he,Complex.ofReal_re]
    exact hr.le) (by
      have ht := primitive_lines_total hx
      have hs : Summable (fun d : ReducedDirection => overlapCoefficient x (gapFrequency d.val)) := by
        by_contra hn
        exact one_ne_zero (ht.symm.trans (tsum_eq_zero_of_not_summable hn))
      have h : HasSum (fun d : ReducedDirection => overlapCoefficient x (gapFrequency d.val)) 1 := by
        rw [← ht]
        exact hs.hasSum
      exact Complex.reCLM.hasSum h)

def directionLaw (x : ℝ) (hx : 1/2 < x) : ProbabilityMeasure ReducedDirection :=
  ⟨(directionPMF x hx).toMeasure,inferInstance⟩

theorem directionLaw_atom {x : ℝ} (hx : 1/2 < x) (d : ReducedDirection) :
    (directionLaw x hx : Measure ReducedDirection) {d} = ENNReal.ofReal (overlapCoefficient x (gapFrequency d.val)).re :=
  (directionPMF x hx).toMeasure_apply_singleton d (measurableSet_singleton d)

/-- The full energy-basis samples are two independent labels at inverse temperature 2x. -/
def gibbsPairLaw (x : ℝ) (hx : 1/2 < x) : ProbabilityMeasure (ℕ+ × ℕ+) :=
  (scaleLaw (x/2) (by linarith)).prod (scaleLaw (x/2) (by linarith))

theorem gibbsPairLaw_atom {x : ℝ} (hx : 1/2 < x) (q : ℕ+ × ℕ+) :
    (gibbsPairLaw x hx : Measure (ℕ+ × ℕ+)) {q} = ENNReal.ofReal (gapAmplitude x q).re := by
  rcases q with ⟨a,b⟩
  have hh : 1/4 < x/2 := by linarith
  obtain ⟨u,hu,heu⟩ := commonScaleWeight_positive hh a
  obtain ⟨v,hv,hev⟩ := commonScaleWeight_positive hh b
  rw [gibbsPairLaw,ProbabilityMeasure.toMeasure_prod,← Set.singleton_prod_singleton,Measure.prod_prod,
    scaleLaw_atom,scaleLaw_atom,gapAmplitude_product hx]
  change ENNReal.ofReal (commonScaleWeight (x/2) a).re * ENNReal.ofReal (commonScaleWeight (x/2) b).re =
    ENNReal.ofReal (commonScaleWeight (x/2) a * commonScaleWeight (x/2) b).re
  simp only [← heu,← hev,← Complex.ofReal_mul,Complex.ofReal_re,ENNReal.ofReal_mul hu.le]

#print axioms gapAmplitude_product
#print axioms primitive_line_positive
#print axioms scaleLaw_atom
#print axioms directionLaw_atom
#print axioms gibbsPairLaw_atom

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
