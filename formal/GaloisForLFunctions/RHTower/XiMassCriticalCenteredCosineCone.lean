import GaloisForLFunctions.RHTower.XiMassCriticalCenteredDirichletCone

/-!
# One-sided cosine face of the finite critical mass cone

The mass propagator is even in real source frequency, while the moving centered Dirichlet
polynomial has conjugate frequencies.  Folding its exact full-line pairing therefore produces a
half-line integral against one real finite cosine polynomial.  This removes the artificial pair of
complex source-frequency faces without taking norms or discarding phase.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Real centered cosine polynomial at the rounded mass-cone cutoff. -/
noncomputable def xiMassCriticalCenteredCosineConePolynomial (d u x : ℝ) : ℝ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    (ArithmeticFunction.vonMangoldt (k + 2) - 1) *
      Real.exp (-Real.log ((k : ℝ) + 2) / 2) *
      Real.cos (Real.log ((k : ℝ) + 2) * x)

/-- The positive- and negative-frequency Dirichlet faces combine exactly into twice the real
cosine polynomial. -/
theorem xiMassCriticalCenteredDirichletConePolynomial_add_neg_eq_cosine
    (d u x : ℝ) :
    xiMassCriticalCenteredDirichletConePolynomial d u x +
        xiMassCriticalCenteredDirichletConePolynomial d u (-x) =
      (2 : ℂ) * (xiMassCriticalCenteredCosineConePolynomial d u x : ℂ) := by
  simp only [xiMassCriticalCenteredDirichletConePolynomial,
    xiMassCriticalCenteredCosineConePolynomial]
  rw [← Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  let h : ℝ := Real.log ((k : ℝ) + 2)
  have hp : -(I * (h : ℂ) * (x : ℂ)) = ((-(h * x) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hn : -(I * (h : ℂ) * ((-x : ℝ) : ℂ)) = (((h * x) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hpair :
      Complex.exp (-(I * (h : ℂ) * (x : ℂ))) +
          Complex.exp (-(I * (h : ℂ) * ((-x : ℝ) : ℂ))) =
        2 * Complex.cos ((h : ℂ) * (x : ℂ)) := by
    rw [hp, hn, Complex.exp_mul_I, Complex.exp_mul_I]
    have harg : (h : ℂ) * (x : ℂ) = ((h * x : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [show ((-(h * x) : ℝ) : ℂ) = -((h : ℂ) * (x : ℂ)) by push_cast; ring,
      Complex.cos_neg, Complex.sin_neg, harg]
    ring
  dsimp only [h] at hpair
  have hxcast : -((x : ℂ)) = ((-x : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hxcast]
  calc
    _ = (((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) - 1) *
        Complex.exp (-(Real.log ((k : ℝ) + 2) : ℂ) / 2) *
        (Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ))) +
          Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * ((-x : ℝ) : ℂ)))) := by
      ring
    _ = (((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) - 1) *
        Complex.exp (-(Real.log ((k : ℝ) + 2) : ℂ) / 2) *
        (2 * Complex.cos ((Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ))) := by
      rw [hpair]
    _ = _ := by ring

/-- The exact mass/finite-Dirichlet pairing is genuinely integrable as a finite sum of the
integrable critical atoms. -/
theorem integrable_xiMassAnalyticTest_mul_centeredDirichletConePolynomial
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        xiMassCriticalCenteredDirichletConePolynomial d u x) := by
  simp only [xiMassCriticalCenteredDirichletConePolynomial]
  simp_rw [Finset.mul_sum]
  exact MeasureTheory.integrable_finsetSum _ fun k _ =>
    integrable_xiMassAnalyticTest_mul_centeredCriticalAtom ha hsigma k

/-- One-sided exact cosine pairing.  Factor two accounts for folding the full source line. -/
noncomputable def xiMassCriticalCenteredCosineConePairing
    (a sigma d u : ℝ) : ℂ :=
  (2 : ℂ) * ∫ x : ℝ in Ioi 0,
    xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
      (xiMassCriticalCenteredCosineConePolynomial d u x : ℂ)

/-- **Exact one-sided cosine face.**  The finite centered-atom cone sum equals the folded
half-line pairing against one real cosine polynomial. -/
theorem xiMassCriticalCenteredAtomConeSum_eq_cosineConePairing
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalCenteredAtomConeSum a sigma d u =
      xiMassCriticalCenteredCosineConePairing a sigma d u := by
  rw [xiMassCriticalCenteredAtomConeSum_eq_integral_dirichletConePolynomial ha hsigma]
  let f : ℝ → ℂ := fun x =>
    xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
      xiMassCriticalCenteredDirichletConePolynomial d u x
  have hf : Integrable f := by
    simpa only [f] using
      integrable_xiMassAnalyticTest_mul_centeredDirichletConePolynomial ha hsigma
  rw [show (∫ x : ℝ,
      xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        xiMassCriticalCenteredDirichletConePolynomial d u x) = ∫ x : ℝ, f x by rfl]
  rw [integral_eq_integral_Ioi_add_reflect hf]
  rw [xiMassCriticalCenteredCosineConePairing, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  have hxcast : ((-x : ℝ) : ℂ) = -(x : ℂ) := by
    push_cast
    rfl
  rw [hxcast, xiMassAnalyticTest_neg, ← mul_add,
    xiMassCriticalCenteredDirichletConePolynomial_add_neg_eq_cosine]
  ring

/-- Uniform bound for the exact one-sided centered cosine cone pairing. -/
def XiMassCriticalCenteredCosineConePairingLineBound
    (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalCenteredCosineConePairing a sigma d u‖ ≤ C

/-- Replacing paired complex frequencies by the one-sided real cosine face loses no information. -/
theorem xiMassCriticalCenteredAtomConeLineBound_iff_cosineConePairing
    {a sigma d : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    XiMassCriticalCenteredAtomConeLineBound a sigma d ↔
      XiMassCriticalCenteredCosineConePairingLineBound a sigma d := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun u hu => ?_⟩
  · rw [← xiMassCriticalCenteredAtomConeSum_eq_cosineConePairing ha hsigma]
    exact hC u hu
  · rw [xiMassCriticalCenteredAtomConeSum_eq_cosineConePairing ha hsigma]
    exact hC u hu

/-- **One-sided cosine exact open core.**  RH is equivalent to a uniform half-line mass pairing
against one real finite centered cosine polynomial. -/
theorem riemannHypothesis_iff_xiMassCriticalCenteredCosineConePairingLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassCriticalCenteredCosineConePairingLineBound a sigma d := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  exact (riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalCenteredAtomConeLineBound_iff_cosineConePairing ha hsigma)

end

end RHTower
