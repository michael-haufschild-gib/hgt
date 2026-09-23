import GaloisForLFunctions.RHTower.XiMassCriticalCenteredAtomCone

/-!
# Dirichlet-polynomial face of the finite critical mass cone

The canonical finite centered-atom cone sum is exactly one genuine real integral pairing.  Its
first factor is the actual analytic mass propagator; its second factor is a finite critical
Dirichlet polynomial with coefficients `Lambda(n)-1`.  This puts the remaining RH-strength source
obligation in the same exact interface as the corpus mean-square, Perron, and oscillatory-integral
machinery.  No series continuation, limit exchange, or numerical computation occurs.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Moving finite critical Dirichlet polynomial cut off at the rounded mass-cone edge. -/
noncomputable def xiMassCriticalCenteredDirichletConePolynomial (d u x : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    (((ArithmeticFunction.vonMangoldt (k + 2) - 1) *
      Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) *
      Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ)))

/-- Each centered critical atom times the analytic mass propagator is genuinely integrable. -/
theorem integrable_xiMassAnalyticTest_mul_centeredCriticalAtom
    {a sigma u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (n : ℕ) :
    Integrable (fun x : ℝ =>
      xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        ((((ArithmeticFunction.vonMangoldt (n + 2) - 1) *
          Real.exp (-Real.log ((n : ℝ) + 2) / 2) : ℝ) : ℂ) *
          Complex.exp (-(I * (Real.log ((n : ℝ) + 2) : ℂ) * (x : ℂ))))) := by
  let C : ℝ := |ArithmeticFunction.vonMangoldt (n + 2) - 1| *
    Real.exp (-Real.log ((n : ℝ) + 2) / 2)
  apply Integrable.mono' ((integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hsigma).const_mul C)
  · have hg : Continuous (fun x : ℝ =>
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        change HasDerivAt (⇑Complex.ofRealCLM) 1 x
        exact Complex.ofRealCLM.hasDerivAt
      have hmem : (x : ℂ) ∈ xiMassStrip a := by
        change |((x : ℂ)).im| < a
        simpa using ha
      exact ((hasDerivAt_xiMassAnalyticTest ha _ hmem).comp x hz).continuousAt
    exact (hg.mul (continuous_const.mul
      (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    have hmem : (x : ℂ) ∈ xiMassStrip a := by
      change |((x : ℂ)).im| < a
      simpa using ha
    have hg := norm_xiMassAnalyticTest_le
      (τ := ((sigma : ℂ) + u * I)) ha (by simpa using hsigma.le) hmem
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    have hphase :
        (-(I * (Real.log ((n : ℝ) + 2) : ℂ) * (x : ℂ))).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one]
    have hg' : ‖xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ)‖ ≤
        Real.exp (-(sigma * |x|)) := by
      simpa using hg
    dsimp only [C]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(sigma * |x|)) *
          (|ArithmeticFunction.vonMangoldt (n + 2) - 1| *
            Real.exp (-Real.log ((n : ℝ) + 2) / 2)) :=
        mul_le_mul_of_nonneg_right hg'
          (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ = _ := by ring

/-- **Exact Dirichlet face.**  The finite centered-atom cone sum is the integral pairing of the
mass propagator with its moving finite critical Dirichlet polynomial. -/
theorem xiMassCriticalCenteredAtomConeSum_eq_integral_dirichletConePolynomial
    {a sigma d u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    xiMassCriticalCenteredAtomConeSum a sigma d u =
      ∫ x : ℝ, xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
        xiMassCriticalCenteredDirichletConePolynomial d u x := by
  simp only [xiMassCriticalCenteredAtomConeSum,
    xiMassCriticalCenteredDirichletConePolynomial]
  simp only [xiMassCriticalDampedFourierProfile, stripFourier]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfun : (fun x : ℝ =>
        xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
          ((((ArithmeticFunction.vonMangoldt (k + 2) - 1) *
            Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℝ) : ℂ) *
            Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ))))) =
        fun x : ℝ =>
          ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
            (Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℂ) *
            (xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
              Complex.exp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * (x : ℂ)))) := by
      funext x
      push_cast
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
    ring
  · intro k hk
    exact integrable_xiMassAnalyticTest_mul_centeredCriticalAtom ha hsigma k

/-- Uniform bound on the exact mass/Dirichlet-polynomial cone pairing. -/
def XiMassCriticalCenteredDirichletConePairingLineBound
    (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖∫ x : ℝ, xiMassAnalyticTest a ((sigma : ℂ) + u * I) (x : ℂ) *
      xiMassCriticalCenteredDirichletConePolynomial d u x‖ ≤ C

/-- Atom-sum and Dirichlet-pairing line bounds are definitionally connected by the exact integral
identity; no estimate is spent in either direction. -/
theorem xiMassCriticalCenteredAtomConeLineBound_iff_dirichletConePairing
    {a sigma d : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) :
    XiMassCriticalCenteredAtomConeLineBound a sigma d ↔
      XiMassCriticalCenteredDirichletConePairingLineBound a sigma d := by
  constructor <;> rintro ⟨C, hC⟩ <;> refine ⟨C, fun u hu => ?_⟩
  · rw [← xiMassCriticalCenteredAtomConeSum_eq_integral_dirichletConePolynomial
      ha hsigma]
    exact hC u hu
  · rw [xiMassCriticalCenteredAtomConeSum_eq_integral_dirichletConePolynomial
      ha hsigma]
    exact hC u hu

/-- **Dirichlet-polynomial exact open core.**  RH is equivalent to uniform boundedness of the exact
finite mass/centered-Dirichlet pairing on one nonnegative vertical cone. -/
theorem riemannHypothesis_iff_xiMassCriticalCenteredDirichletConePairingLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassCriticalCenteredDirichletConePairingLineBound a sigma d := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hdhalf hda)
  exact (riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalCenteredAtomConeLineBound_iff_dirichletConePairing ha hsigma)

end

end RHTower
