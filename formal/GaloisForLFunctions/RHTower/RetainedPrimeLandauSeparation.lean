import GaloisForLFunctions.RHTower.RetainedPrimeLandauCarrier
import GaloisForLFunctions.RHTower.FiniteDirichletMellinContinuationObstruction

/-!
# Unconditional directional separation of finite retained sources

A one-sided actual retained functional gives a finite positive integral carrier.
Landau transfer reconstructs its Mellin transform analytically on `Re s > 3/4`.
The exact source germ and surviving simple critical poles force every retained
coordinate of that functional to vanish. Every nonzero retained direction
therefore has actual integer cutoffs with both strict signs. No source-sign,
RH or zero-location assumption is added to the resulting witness theorems.
-/

noncomputable section
open Complex MeasureTheory Filter Set ProbabilityTheory Topology
open scoped NNReal
namespace RHTower

/-- The closed low-height balls force every exponential moment they reach for
a one-sided retained functional. -/
lemma retainedPrimeLandau_integrable_transfer
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) {R : NNReal} (hR : (R : ℝ) < 7 / 2)
    {t : ℝ} (ht0 : 0 ≤ t) (htR : t < (R : ℝ)) :
    Integrable (fun x => Real.exp (t * Real.log x)) (retainedPrimeLandauMeasure Q y) := by
  apply landau_complexMGF_integrable_transfer
    (log_nonneg_ae_retainedPrimeLandauMeasure Q y)
    (zero_mem_interior_integrableExpSet_retainedPrimeLandauMeasure Q y)
    (G := retainedPrimeLandauContinuation Q y) (R := R) _
    (retainedPrimeLandauContinuation_eventuallyEq_complexMGF h) ht0 htR
  exact differentiableOn_finiteDirichletDivisorMellin_landau_ball _
    (retainedPrimeDirichletCoefficients_zero _ _) Q _ hR

lemma Iio_subset_interior_integrableExpSet_retainedPrimeLandauMeasure
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) {R : NNReal} (hR : (R : ℝ) < 7 / 2) :
    Iio (R : ℝ) ⊆ interior (integrableExpSet Real.log (retainedPrimeLandauMeasure Q y)) := by
  have hset : Iio (R : ℝ) ⊆ integrableExpSet Real.log (retainedPrimeLandauMeasure Q y) := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · exact retainedPrimeLandau_integrable_transfer h hR ht0 ht
    · exact integrable_exp_log_retainedPrimeLandauMeasure Q y (by linarith)
  intro t ht
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset (Iio_mem_nhds ht) hset

/-- A one-sided functional reconstructs an analytic source Mellin transform
past the real part of every surviving critical pole. -/
lemma analyticOnNhd_retainedPrimeLandauReconstruction
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) :
    AnalyticOnNhd ℂ
      (fun s : ℂ => complexMGF Real.log (retainedPrimeLandauMeasure Q y) (4 - s))
      {s : ℂ | 3 / 4 < s.re} := by
  let R : NNReal := ⟨13 / 4, by norm_num⟩
  have hinter := Iio_subset_interior_integrableExpSet_retainedPrimeLandauMeasure
    h (R := R) (by change (13 / 4 : ℝ) < 7 / 2; norm_num)
  intro s hs
  change 3 / 4 < s.re at hs
  have hz : (4 - s).re ∈ interior (integrableExpSet Real.log (retainedPrimeLandauMeasure Q y)) := by
    apply hinter
    change (4 - s).re < 13 / 4
    simp only [sub_re]
    norm_num
    linarith [hs]
  have houter := analyticOnNhd_complexMGF (X := Real.log) (μ := retainedPrimeLandauMeasure Q y)
    (4 - s) hz
  have hshift : AnalyticAt ℂ (fun z : ℂ => 4 - z) s := by fun_prop
  simpa only [Function.comp_def] using houter.comp hshift

/-- Every nonnegative complete retained-source functional vanishes on every
retained coordinate. The conclusion is unconditional and uses actual source values. -/
theorem retainedPrimeSourceNonnegative_coordinates_zero
    {Q : Finset Nat.Primes} {y : Finset ℕ → ℝ}
    (h : RetainedPrimeSourceNonnegative Q y) :
    ∀ R : Finset ℕ, R ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) → y R = 0 := by
  intro R hR
  by_contra hyR
  let P := Q.image (fun p : Nat.Primes => (p : ℕ))
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  let a := retainedPrimeDirichletCoefficients P (fun S => (y S : ℂ))
  have ha : a 0 = 0 := retainedPrimeDirichletCoefficients_zero _ _
  have hane : a ≠ 0 := retainedPrimeDirichletCoefficients_ne_zero P hP _
    ⟨R, hR, Complex.ofReal_ne_zero.mpr hyR⟩
  apply no_analytic_finiteDirichletDivisorMellin_continuation a ha hane Q
    (2 * Real.eulerMascheroniConstant : ℂ) (by norm_num : (3 / 4 : ℝ) < 1)
    (analyticOnNhd_retainedPrimeLandauReconstruction h)
  have hn : ∀ᶠ s : ℂ in 𝓝 (4 : ℂ), 2 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hn] with s hs
  have he := retainedPrimeLandauContinuation_eq_complexMGF h
    (z := 4 - s) (by simp only [sub_re]; norm_num; linarith)
  simpa only [retainedPrimeLandauContinuation, sub_sub_cancel, a, P] using he.symm

/-- Every nonzero retained direction has an actual integer cutoff with a
strictly negative complete source pairing. -/
theorem exists_negative_retainedPrimeSourceMean
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ)
    (hy : ∃ R : Finset ℕ, R ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) ∧ y R ≠ 0) :
    ∃ M : ℕ, (retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
      (fun R => (y R : ℂ)) M).re < 0 := by
  by_contra hn
  have hnonneg : RetainedPrimeSourceNonnegative Q y := by
    intro M
    exact le_of_not_gt (fun hM => hn ⟨M, hM⟩)
  obtain ⟨R, hR, hyR⟩ := hy
  exact hyR (retainedPrimeSourceNonnegative_coordinates_zero hnonneg R hR)

/-- Every nonzero retained direction also has a strictly positive actual
integer source pairing; no fixed finite retained field admits one-sided separation. -/
theorem exists_positive_retainedPrimeSourceMean
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℝ)
    (hy : ∃ R : Finset ℕ, R ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) ∧ y R ≠ 0) :
    ∃ M : ℕ, 0 < (retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
      (fun R => (y R : ℂ)) M).re := by
  have hneg : ∃ R : Finset ℕ, R ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) ∧ (-y R) ≠ 0 := by
    obtain ⟨R, hR, hyR⟩ := hy
    exact ⟨R, hR, neg_ne_zero.mpr hyR⟩
  obtain ⟨M, hM⟩ := exists_negative_retainedPrimeSourceMean Q (fun R => -y R) hneg
  refine ⟨M, ?_⟩
  have he : retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
      (fun R => ((-y R : ℝ) : ℂ)) M =
      -retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
        (fun R => (y R : ℂ)) M := by
    simp [retainedPrimeSourceMean, Finset.sum_neg_distrib]
  rw [he, Complex.neg_re] at hM
  linarith

end RHTower
