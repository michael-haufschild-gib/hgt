import GaloisForLFunctions.HTGeometry.LaurentAnnulus
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.RHTower.FiniteHermiteCRT

/-!
# Compact-open density of centered real-even polynomials

Taylor truncation gives polynomial approximation of an arbitrary entire function. Averaging over
the sign and Schwarz involutions preserves compact-open convergence, so a centered real-even,
Schwarz-real entire function is approximated by polynomials with exactly those two symmetries.
-/

open Complex Filter Set Topology Polynomial
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical Taylor polynomial of an entire function at the origin. -/
def entireTaylorPolynomial (f : ℂ → ℂ) (n : ℕ) : Polynomial ℂ :=
  Finset.sum (Finset.range n) fun k => C (outerCoeff f 1 k) * X ^ k

theorem entireTaylorPolynomial_eval (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (entireTaylorPolynomial f n).eval z =
      (cauchyPowerSeries f 0 1).partialSum n z := by
  rw [entireTaylorPolynomial, Polynomial.eval_finsetSum,
    FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, cauchyPowerSeries_diag f (by norm_num : (0 : ℝ) < 1)]
  simp only [smul_eq_mul]
  ring

/-- Taylor polynomials of an entire function converge compact-open on the whole plane. -/
theorem entireTaylorPolynomial_tendstoLocallyUniformly
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    TendstoLocallyUniformly
      (fun n z => (entireTaylorPolynomial f n).eval z) f atTop := by
  have hpow := hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have hconv := hpow.tendstoLocallyUniformlyOn'
  rw [Metric.eball_top] at hconv
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa only [entireTaylorPolynomial_eval, sub_zero] using! hconv

/-- Pullback by the sign involution on functions. -/
def functionNegPullback (f : ℂ → ℂ) (z : ℂ) : ℂ := f (-z)

/-- Schwarz reflection on functions. -/
def functionSchwarzReflect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

/-- Compact-open convergence is preserved by pullback under `z ↦ -z`. -/
theorem tendstoLocallyUniformly_functionNegPullback
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f atTop) :
    TendstoLocallyUniformly (fun n => functionNegPullback (F n))
      (functionNegPullback f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  let K' : Set ℂ := (fun z : ℂ => -z) '' K
  have hK' : IsCompact K' := hK.image continuous_neg
  have hU := h K' hK'
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro epsilon hepsilon
  filter_upwards [hU epsilon hepsilon] with n hn z hz
  exact hn (-z) ⟨z, hz, rfl⟩

/-- Compact-open convergence is preserved by Schwarz reflection. -/
theorem tendstoLocallyUniformly_functionSchwarzReflect
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f atTop) :
    TendstoLocallyUniformly (fun n => functionSchwarzReflect (F n))
      (functionSchwarzReflect f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  let K' : Set ℂ := (starRingEnd ℂ) '' K
  have hK' : IsCompact K' := hK.image Complex.continuous_conj
  have hU := h K' hK'
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro epsilon hepsilon
  filter_upwards [hU epsilon hepsilon] with n hn z hz
  have hdist := hn ((starRingEnd ℂ) z) ⟨z, hz, rfl⟩
  rw [dist_eq_norm] at hdist ⊢
  simpa [functionSchwarzReflect, ← map_sub] using hdist

theorem tendstoLocallyUniformly_const_index (c : ℂ) :
    TendstoLocallyUniformly (fun _ : ℕ => fun _ : ℂ => c) (fun _ => c) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  exact Filter.Eventually.of_forall (fun n z hz => by simpa using hepsilon)

/-- Real-even averaging preserves compact-open convergence to a real-even target. -/
theorem polynomialRealEvenAverage_tendstoLocallyUniformly
    {P : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly (fun n z => (P n).eval z) f atTop)
    (hf : Continuous f) (heven : ∀ z, f (-z) = f z)
    (hschwarz : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    TendstoLocallyUniformly
      (fun n z => (polynomialRealEvenAverage (P n)).eval z) f atTop := by
  have hneg := tendstoLocallyUniformly_functionNegPullback h
  have hconj := tendstoLocallyUniformly_functionSchwarzReflect h
  have hnegconj := tendstoLocallyUniformly_functionSchwarzReflect hneg
  have hsum := ((h.add hneg).add hconj).add hnegconj
  have hc := tendstoLocallyUniformly_const_index (1 / 4 : ℂ)
  have hmul := tendstoLocallyUniformly_mul hc hsum continuous_const
    (((hf.add (hf.comp continuous_neg)).add
      (Complex.continuous_conj.comp (hf.comp Complex.continuous_conj))).add
      (Complex.continuous_conj.comp
        ((hf.comp continuous_neg).comp Complex.continuous_conj)))
  convert hmul using 1
  · funext n z
    rw [eval_polynomialRealEvenAverage]
    simp [functionNegPullback, functionSchwarzReflect]
    ring
  · funext z
    simp only [Pi.add_apply, functionNegPullback, functionSchwarzReflect]
    rw [heven, hschwarz]
    rw [heven ((starRingEnd ℂ) z), hschwarz]
    simp
    ring

/-- Every centered real-even, Schwarz-real entire function has real-even polynomial approximants. -/
theorem exists_realEvenPolynomial_compactOpen_approximation
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z)
    (hschwarz : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ n z, (P n).eval (-z) = (P n).eval z) ∧
      (∀ n z, (P n).eval ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) ((P n).eval z)) ∧
      TendstoLocallyUniformly (fun n z => (P n).eval z) f atTop := by
  refine ⟨fun n => polynomialRealEvenAverage (entireTaylorPolynomial f n), ?_, ?_, ?_⟩
  · exact fun n => polynomialRealEvenAverage_eval_neg _
  · exact fun n => polynomialRealEvenAverage_eval_conj _
  · exact polynomialRealEvenAverage_tendstoLocallyUniformly
      (entireTaylorPolynomial_tendstoLocallyUniformly hf) hf.continuous heven hschwarz

end

end RHTower
