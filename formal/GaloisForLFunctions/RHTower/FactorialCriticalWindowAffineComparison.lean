import GaloisForLFunctions.RHTower.FactorialCriticalWindowHarmonicBounds

/-! Affine comparison of harmonic correlations in critical physical measure.
The error is small in operator norm as the least source scale tends to infinity. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem window_abs_integral_mul_le {f g : ℝ → ℝ} {A B E : ℝ}
    (hfm : AEStronglyMeasurable f criticalWindowMeasure)
    (hgm : AEStronglyMeasurable g criticalWindowMeasure)
    (hfi : Integrable (fun v => f v ^ 2) criticalWindowMeasure)
    (hgi : Integrable (fun v => g v ^ 2) criticalWindowMeasure)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hf : (∫ v, f v ^ 2 ∂criticalWindowMeasure) ≤ A * E)
    (hg : (∫ v, g v ^ 2 ∂criticalWindowMeasure) ≤ B * E) :
    |∫ v, f v * g v ∂criticalWindowMeasure| ≤ Real.sqrt (A * B) * E := by
  have hs := sq_integral_mul_le hfm hgm hfi hgi
  have hm := mul_le_mul hf hg (integral_nonneg fun v => sq_nonneg (g v))
    (mul_nonneg hA hE)
  have hroot := Real.sq_sqrt (mul_nonneg hA hB)
  have hpos := mul_nonneg (Real.sqrt_nonneg (A * B)) hE
  have hsq : (∫ v, f v * g v ∂criticalWindowMeasure) ^ 2 ≤
      (Real.sqrt (A * B) * E) ^ 2 := by
    calc _ ≤ (A * E) * (B * E) := hs.trans hm
      _ = (Real.sqrt (A * B) * E) ^ 2 := by rw [mul_pow, hroot]; ring
  nlinarith [sq_abs (∫ v, f v * g v ∂criticalWindowMeasure),
    abs_nonneg (∫ v, f v * g v ∂criticalWindowMeasure)]

/-- Error coefficient for two affine-compared harmonic layers. -/
def criticalWindowAffineCorrelationError (k l : ℕ) (N : ℝ) : ℝ :=
  Real.sqrt ((Real.pi ^ 2 * k / (140 * N)) * criticalWindowHarmonicBound) +
    Real.sqrt (criticalWindowHarmonicBound * (Real.pi ^ 2 * l / (140 * N))) +
    Real.sqrt ((Real.pi ^ 2 * k / (140 * N)) * (Real.pi ^ 2 * l / (140 * N)))

/-- The actual and affine critical correlations differ by a coefficient-square bound
that tends to zero independently of the support size. -/
theorem abs_integral_criticalWindow_harmonics_sub_affine_le
    {S : Finset ℕ} (b : ℕ → ℝ) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    {N : ℝ} (hN : 0 < N) (hS : ∀ n ∈ S, N ≤ ((n+1 : ℕ) : ℝ)) :
    |(∫ v, realHarmonicLayer S b k v * realHarmonicLayer S b l v ∂criticalWindowMeasure) -
      ∫ v, realAffineHarmonicLayer S b k v * realAffineHarmonicLayer S b l v
        ∂criticalWindowMeasure| ≤
      criticalWindowAffineCorrelationError k l N * ∑ n ∈ S, b n ^ 2 := by
  let H := realHarmonicLayer S b
  let A := realAffineHarmonicLayer S b
  let d := fun j v => H j v - A j v
  let E := ∑ n ∈ S, b n ^ 2
  let ak := Real.pi ^ 2 * k / (140 * N)
  let al := Real.pi ^ 2 * l / (140 * N)
  have hE : 0 ≤ E := Finset.sum_nonneg fun n hn => sq_nonneg (b n)
  have hak : 0 ≤ ak := by dsimp [ak]; positivity
  have hal : 0 ≤ al := by dsimp [al]; positivity
  have hU := criticalWindowHarmonicBound_nonneg
  have hHm (j : ℕ) : AEStronglyMeasurable (H j) criticalWindowMeasure := by
    apply Continuous.aestronglyMeasurable
    dsimp [H, realHarmonicLayer]
    fun_prop
  have hAm (j : ℕ) : AEStronglyMeasurable (A j) criticalWindowMeasure :=
    (continuous_realAffineHarmonicLayer S b j).aestronglyMeasurable
  have hdm (j : ℕ) : AEStronglyMeasurable (d j) criticalWindowMeasure :=
    (hHm j).sub (hAm j)
  have hHi (j : ℕ) : Integrable (fun v => H j v ^ 2) criticalWindowMeasure :=
    integrable_criticalWindow_harmonic_sq S b j
  have hAi (j : ℕ) : Integrable (fun v => A j v ^ 2) criticalWindowMeasure :=
    integrable_criticalWindow_affine_sq S b j
  have hdi (j : ℕ) : Integrable (fun v => d j v ^ 2) criticalWindowMeasure :=
    integrable_criticalWindow_affine_error_sq S b j
  have hH (j : ℕ) (hj : 1 ≤ j) :
      (∫ v, H j v ^ 2 ∂criticalWindowMeasure) ≤ criticalWindowHarmonicBound * E := by
    rw [integral_criticalWindowMeasure_eq_weight]
    exact integral_criticalWindowWeight_harmonic_sq_le S b hj
  have hdk : (∫ v, d k v ^ 2 ∂criticalWindowMeasure) ≤ ak * E :=
    integral_criticalWindow_affine_error_sq_le b k hN hS
  have hdl : (∫ v, d l v ^ 2 ∂criticalWindowMeasure) ≤ al * E :=
    integral_criticalWindow_affine_error_sq_le b l hN hS
  have h1 := window_abs_integral_mul_le (hdm k) (hHm l) (hdi k) (hHi l)
    hak hU hE hdk (hH l hl)
  have h2 := window_abs_integral_mul_le (hHm k) (hdm l) (hHi k) (hdi l)
    hU hal hE (hH k hk) hdl
  have h3 := window_abs_integral_mul_le (hdm k) (hdm l) (hdi k) (hdi l)
    hak hal hE hdk hdl
  have hi1 := integrable_mul_of_sq_integrable (hdm k) (hHm l) (hdi k) (hHi l)
  have hi2 := integrable_mul_of_sq_integrable (hHm k) (hdm l) (hHi k) (hdi l)
  have hi3 := integrable_mul_of_sq_integrable (hdm k) (hdm l) (hdi k) (hdi l)
  have heq : (∫ v, H k v * H l v ∂criticalWindowMeasure) -
      (∫ v, A k v * A l v ∂criticalWindowMeasure) =
      ((∫ v, d k v * H l v ∂criticalWindowMeasure) +
        ∫ v, H k v * d l v ∂criticalWindowMeasure) -
        ∫ v, d k v * d l v ∂criticalWindowMeasure := by
    rw [← integral_sub (integrable_mul_of_sq_integrable (hHm k) (hHm l) (hHi k) (hHi l))
      (integrable_mul_of_sq_integrable (hAm k) (hAm l) (hAi k) (hAi l))]
    rw [← integral_add hi1 hi2, ← integral_sub (hi1.add hi2) hi3]
    apply integral_congr_ae
    exact Eventually.of_forall fun v => by dsimp [d]; ring
  change |_ - _| ≤ criticalWindowAffineCorrelationError k l N * E
  rw [heq]
  refine (abs_sub _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add h1 h2)) h3).trans_eq ?_)
  unfold criticalWindowAffineCorrelationError
  dsimp only [ak, al]
  ring

end GaloisForLFunctions.ArithmeticPositivityTheory
