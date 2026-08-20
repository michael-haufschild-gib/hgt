import GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency
import GaloisForLFunctions.HTGeometry.PositiveJumpFormationChirality

/-!
# Esscher formation chirality

The two directed relative entropies of an exponentially tilted pair are read off from the
normalizations and the first responses:

`D(P_s ‖ P_t) = log Z(t) − log Z(s) + (t − s) · E_s[Q]`.

Their difference is therefore `2(F(t) − F(s)) + (t − s)(m(s) + m(t))`, the exact expression which
the positive-jump kernel evaluates.  Combining with the chronology of a positive-jump datum, a
measurable involution exchanging two admitted formation laws forces the two parameters to agree,
and a finite-order formation symmetry acts as the identity.
-/

open MeasureTheory InformationTheory

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The directed Esscher relative entropies -/

/-- The log-likelihood ratio of two members of an exponential family is affine in the tilting
statistic. -/
theorem llr_esscherLaw (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 < cs) (hct : 0 < ct) (s t : ℝ)
    [SigmaFinite (esscherLaw μ Q ct t)] :
    llr (esscherLaw μ Q cs s) (esscherLaw μ Q ct t)
      =ᵐ[esscherLaw μ Q ct t] fun ω => Real.log (cs / ct) + (t - s) * Q ω := by
  have hfac := esscherLaw_eq_withDensity_comp μ hQ hcs.le hct s t
  have hrn : (esscherLaw μ Q cs s).rnDeriv (esscherLaw μ Q ct t)
      =ᵐ[esscherLaw μ Q ct t]
        (fun y => ENNReal.ofReal (cs / ct * Real.exp ((t - s) * y))) ∘ Q := by
    rw [hfac]
    exact Measure.rnDeriv_withDensity _ (by fun_prop)
  filter_upwards [hrn] with ω hω
  rw [llr, hω]
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (by positivity), Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp]

/-- **(FCRM.9)**  The directed Esscher relative entropy. -/
theorem klDiv_esscherLaw (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 < cs) (hct : 0 < ct) (s t : ℝ)
    [IsProbabilityMeasure (esscherLaw μ Q cs s)] [IsProbabilityMeasure (esscherLaw μ Q ct t)]
    (hQint : Integrable Q (esscherLaw μ Q cs s)) :
    klDiv (esscherLaw μ Q cs s) (esscherLaw μ Q ct t)
      = ENNReal.ofReal
          (Real.log (cs / ct) + (t - s) * ∫ ω, Q ω ∂(esscherLaw μ Q cs s)) := by
  have hfac := esscherLaw_eq_withDensity_comp μ hQ hcs.le hct s t
  have hac : esscherLaw μ Q cs s ≪ esscherLaw μ Q ct t := by
    rw [hfac]; exact withDensity_absolutelyContinuous _ _
  have hllr := (llr_esscherLaw μ hQ hcs hct s t).filter_mono hac.ae_le
  have hint : Integrable (llr (esscherLaw μ Q cs s) (esscherLaw μ Q ct t))
      (esscherLaw μ Q cs s) := by
    refine Integrable.congr ?_ hllr.symm
    exact (integrable_const _).add (hQint.const_mul (t - s))
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr]
  rw [integral_add (integrable_const _) (hQint.const_mul (t - s))]
  simp [integral_const_mul, probReal_univ]

/-- **Gibbs positivity in Esscher coordinates.**  The argument of the directed relative entropy is
nonnegative. -/
theorem esscherDirected_nonneg (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 < cs) (hct : 0 < ct) (s t : ℝ)
    [IsProbabilityMeasure (esscherLaw μ Q cs s)] [IsProbabilityMeasure (esscherLaw μ Q ct t)]
    (hQint : Integrable Q (esscherLaw μ Q cs s)) :
    0 ≤ Real.log (cs / ct) + (t - s) * ∫ ω, Q ω ∂(esscherLaw μ Q cs s) := by
  have hfac := esscherLaw_eq_withDensity_comp μ hQ hcs.le hct s t
  have hac : esscherLaw μ Q cs s ≪ esscherLaw μ Q ct t := by
    rw [hfac]; exact withDensity_absolutelyContinuous _ _
  have hllr := (llr_esscherLaw μ hQ hcs hct s t).filter_mono hac.ae_le
  have hint : Integrable (llr (esscherLaw μ Q cs s) (esscherLaw μ Q ct t))
      (esscherLaw μ Q cs s) := by
    refine Integrable.congr ?_ hllr.symm
    exact (integrable_const _).add (hQint.const_mul (t - s))
  have hgibbs := integral_llr_add_sub_measure_univ_nonneg hac hint
  rw [integral_congr_ae hllr,
    integral_add (integrable_const _) (hQint.const_mul (t - s))] at hgibbs
  simp only [integral_const, integral_const_mul, probReal_univ, smul_eq_mul, mul_one] at hgibbs
  linarith

/-- The directed information commutator of two members of an exponential family. -/
theorem klChirality_esscherLaw (μ : Measure Ω) {Q : Ω → ℝ} (hQ : Measurable Q)
    {cs ct : ℝ} (hcs : 0 < cs) (hct : 0 < ct) (s t : ℝ)
    [IsProbabilityMeasure (esscherLaw μ Q cs s)] [IsProbabilityMeasure (esscherLaw μ Q ct t)]
    (hQs : Integrable Q (esscherLaw μ Q cs s)) (hQt : Integrable Q (esscherLaw μ Q ct t))
    (hs : 0 ≤ Real.log (cs / ct) + (t - s) * ∫ ω, Q ω ∂(esscherLaw μ Q cs s))
    (ht : 0 ≤ Real.log (ct / cs) + (s - t) * ∫ ω, Q ω ∂(esscherLaw μ Q ct t)) :
    klChirality (esscherLaw μ Q cs s) (esscherLaw μ Q ct t)
      = 2 * Real.log (cs / ct)
        + (t - s) * ((∫ ω, Q ω ∂(esscherLaw μ Q cs s)) + ∫ ω, Q ω ∂(esscherLaw μ Q ct t)) := by
  rw [klChirality, klDiv_esscherLaw μ hQ hcs hct s t hQs,
    klDiv_esscherLaw μ hQ hct hcs t s hQt, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal ht]
  have hlog : Real.log (ct / cs) = -Real.log (cs / ct) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog]
  ring

/-! ## Involutive and finite-order selection -/

/-- **Theorem 7.2 order core.**  A strictly increasing self-map of finite order on any set of reals
is the identity. -/
theorem eq_id_of_strictMonoOn_of_iterate_id {I : Set ℝ} {φ : ℝ → ℝ}
    (hmap : ∀ t ∈ I, φ t ∈ I)
    (hmono : ∀ s ∈ I, ∀ t ∈ I, s < t → φ s < φ t)
    {N : ℕ} (hN : 0 < N) (hiter : ∀ t ∈ I, φ^[N] t = t) :
    ∀ t ∈ I, φ t = t := by
  have hiterMem : ∀ (k : ℕ), ∀ t ∈ I, φ^[k] t ∈ I := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
        intro t ht
        rw [Function.iterate_succ_apply]
        exact ih _ (hmap t ht)
  have hchain : ∀ (k : ℕ), ∀ t ∈ I, t < φ t → t < φ^[k + 1] t := by
    intro k
    induction k with
    | zero => intro t ht h; simpa using h
    | succ k ih =>
        intro t ht h
        have h1 : t < φ^[k + 1] t := ih t ht h
        have h2 : φ^[k + 1] t ∈ I := hiterMem (k + 1) t ht
        have h3 : φ t < φ (φ^[k + 1] t) := hmono t ht _ h2 h1
        have : φ^[k + 2] t = φ (φ^[k + 1] t) := by
          rw [Function.iterate_succ_apply']
        rw [this]
        exact lt_trans h h3
  have hchain' : ∀ (k : ℕ), ∀ t ∈ I, φ t < t → φ^[k + 1] t < t := by
    intro k
    induction k with
    | zero => intro t ht h; simpa using h
    | succ k ih =>
        intro t ht h
        have h1 : φ^[k + 1] t < t := ih t ht h
        have h2 : φ^[k + 1] t ∈ I := hiterMem (k + 1) t ht
        have h3 : φ (φ^[k + 1] t) < φ t := hmono _ h2 t ht h1
        have : φ^[k + 2] t = φ (φ^[k + 1] t) := by
          rw [Function.iterate_succ_apply']
        rw [this]
        exact lt_trans h3 h
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  rcases lt_trichotomy (φ t) t with h | h | h
  · have := hchain' k t ht h
    rw [hiter t ht] at this
    exact absurd this (lt_irrefl t)
  · exact h
  · have := hchain k t ht h
    rw [hiter t ht] at this
    exact absurd this (lt_irrefl t)

end GaloisForLFunctions.HTGeometry
