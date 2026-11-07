import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellin
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.EisensteinProductDetection

/-!
# Meromorphic continuation of the actual scalar Narain Mellin transform

The completed Poincare series and its canonical Fourier model identify the
scalar Mellin transform with the normalized product of Eisenstein numerators.
The elementary normalization is nonzero at every arithmetic resonance.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The continued scalar heat Mellin transform, with `s = 1/2 + u`. -/
def narainMellinContinuation (ρ σ : D4BMUpperHalfPlaneCoordinate) (u : ℂ) : ℂ :=
  2 * productQuotient ⟨ρ.y, ρ.y_pos⟩ ⟨σ.y, σ.y_pos⟩ ρ.x σ.x u /
    (u * (1 + 2 * u))

/-- The explicit mean of the continued transform over both target horocycles. -/
def narainMellinMean (Y Z : Height) (u : ℂ) : ℂ :=
  2 * meanQuotient Y Z u / (u * (1 + 2 * u))

theorem integral_narainMellinContinuation (Y Z : Height) (u : ℂ) :
    (∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
      narainMellinContinuation ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩ u) =
        narainMellinMean Y Z u := by
  simp only [narainMellinContinuation, integral_div, integral_const_mul,
    narainMellinMean]
  change (2 * (∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
    productQuotient Y Z x w u)) / (u * (1 + 2 * u)) = _
  rw [integral_productQuotient]

private theorem xi_eq_completed_positive {s : ℂ} (hs : 1 < s.re) :
    xi s = s * (s - 1) / 2 * reflectedCompletedLambda s := by
  have h0 : s ≠ 0 := by
    intro h
    have hs0 := lt_trans zero_lt_one hs
    simp [h] at hs0
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  rw [xi_eq_half_mul h0 h1, reflectedCompletedLambda,
    riemannZeta_def_of_ne_zero h0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)]

private theorem numerator_eq_completed_model {u : ℂ} (hu : 1 / 2 < u.re)
    (x Y : ℝ) :
    eisensteinNumerator u x Y = u * (1 + 2 * u) * lineModel u x Y := by
  have h1 : 1 < (1 + 2 * u).re := by simp only [add_re, mul_re]; norm_num; linarith
  have h2 : 1 < (2 * u).re := by simp; linarith
  have hne : 2 * u - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hu, hr]
  rw [eisensteinNumerator, lineModel_eq, xi_eq_completed_positive h1,
    xi_eq_completed_positive h2]
  field_simp [hne]
  ring

private theorem numeratorMean_eq_completed {u : ℂ} (hu : 1 / 2 < u.re) (Y : Height) :
    numeratorMean u Y = u * (1 + 2 * u) *
      (reflectedCompletedLambda (1 + 2 * u) * (Y.val : ℂ) ^ (1 / 2 + u) +
        reflectedCompletedLambda (2 * u) * (Y.val : ℂ) ^ (1 / 2 - u)) := by
  have h1 : 1 < (1 + 2 * u).re := by simp; linarith only [hu]
  have h2 : 1 < (2 * u).re := by simp; linarith only [hu]
  have hne : 2 * u - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hu, hr]
  rw [numeratorMean, xi_eq_completed_positive h1, xi_eq_completed_positive h2]
  field_simp [hne]
  ring

/-- At unit target heights, the average has no Whittaker terms: it is a
three-term expression in completed zeta functions. -/
theorem narainMellinMean_one_eq {u : ℂ} (hu : 1 / 2 < u.re) :
    narainMellinMean ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ u =
      2 * reflectedCompletedLambda (1 + 2 * u) +
        4 * reflectedCompletedLambda (2 * u) +
        2 * reflectedCompletedLambda (2 * u) ^ 2 / reflectedCompletedLambda (1 + 2 * u) := by
  have h1 : 1 < (1 + 2 * u).re := by simp; linarith only [hu]
  have hD : xi (1 + 2 * u) ≠ 0 := xi_ne_zero_of_one_le_re h1.le
  have hx : xi (1 + 2 * u) =
      (u * (1 + 2 * u)) * reflectedCompletedLambda (1 + 2 * u) := by
    rw [xi_eq_completed_positive h1]
    ring
  have hc : u * (1 + 2 * u) ≠ 0 := by
    intro h
    exact hD (by rw [hx, h, zero_mul])
  have hL : reflectedCompletedLambda (1 + 2 * u) ≠ 0 := by
    intro h
    exact hD (by rw [hx, h, mul_zero])
  rw [narainMellinMean, meanQuotient, numeratorMean_eq_completed hu,
    numeratorMean_eq_completed hu, hx]
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one]
  generalize u * (1 + 2 * u) = c at hc ⊢
  field_simp [hc, hL]
  ring

private theorem completed_model_eq_poincare (z : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    lineModel (s - 1 / 2) z.x z.y =
      reflectedCompletedLambda (2 * s) * d4BMRawEisensteinPoincareSeries z ⟨s, hs⟩ := by
  rw [lineModel_eq_cuspLeg]
  exact (d4BM_actualCompletedPoincare_eq_canonicalCuspLeg z ⟨s, hs⟩ z.x).symm

private theorem reflectedCompletedLambda_two_mul (s : ℂ) :
    reflectedCompletedLambda (2 * s) =
      (Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s) := by
  simp only [reflectedCompletedLambda, Complex.Gammaℝ_def]
  rw [show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring]

private theorem numerator_eq_xi_mul_poincare (z : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    eisensteinNumerator (s - 1 / 2) z.x z.y =
      xi (2 * s) * d4BMRawEisensteinPoincareSeries z ⟨s, hs⟩ := by
  have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith only [hs]
  have hs2 : 1 < (2 * s).re := by simp; linarith only [hs]
  rw [numerator_eq_completed_model hu, completed_model_eq_poincare z hs,
    xi_eq_completed_positive hs2]
  ring

/-- On the absolute-convergence half-plane, the quotient is the Mellin
transform of the literal nonvacuum scalar heat sum. -/
theorem narainMellinContinuation_eq_mellin (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    narainMellinContinuation ρ σ (s - 1 / 2) = mellin (narainScalarHeat ρ σ) s := by
  have hs2 : 1 < (2 * s).re := by simp; linarith only [hs]
  have hD : xi (2 * s) ≠ 0 := xi_ne_zero_of_one_le_re hs2.le
  have hx : xi (2 * s) = s * (2 * s - 1) * reflectedCompletedLambda (2 * s) := by
    rw [xi_eq_completed_positive hs2]
    ring
  have hc : s * (2 * s - 1) ≠ 0 := by
    intro h
    exact hD (by rw [hx, h, zero_mul])
  have hL : reflectedCompletedLambda (2 * s) ≠ 0 := by
    intro h
    exact hD (by rw [hx, h, mul_zero])
  rw [narainMellinContinuation, productQuotient,
    numerator_eq_xi_mul_poincare ρ hs, numerator_eq_xi_mul_poincare σ hs,
    show 1 + 2 * (s - 1 / 2) = 2 * s by ring,
    show (s - 1 / 2) * (2 * s) = s * (2 * s - 1) by ring,
    mellin_narainScalarHeat_eq_eisenstein_product ρ σ hs,
    ← reflectedCompletedLambda_two_mul, hx]
  generalize s * (2 * s - 1) = c at hc ⊢
  field_simp [hc, hL]
  ring

/-- The same continuation starts directly from the scalar projection of the
actual partition function, divided by height and with the vacuum removed. -/
theorem narainMellinContinuation_eq_projection (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    narainMellinContinuation ρ σ (s - 1 / 2) =
      mellin (fun y : ℝ =>
        (∫ x in Ioc (0 : ℝ) 1, narainPartition ρ σ x y) / (y : ℂ) - 1) s := by
  rw [narainMellinContinuation_eq_mellin ρ σ hs,
    mellin_narainScalarProjection ρ σ hs,
    mellin_narainScalarHeat_eq_eisenstein_product ρ σ hs]

/-- Averaging the actual scalar Mellin transforms gives the explicit
horocycle-mean continuation on their common convergence half-plane. -/
theorem integral_mellin_narainScalarHeat (Y Z : Height) {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
      mellin (narainScalarHeat ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩) s) =
        narainMellinMean Y Z (s - 1 / 2) := by
  rw [← integral_narainMellinContinuation]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro w _
  exact (narainMellinContinuation_eq_mellin _ _ hs).symm

private theorem meromorphic_eisensteinNumerator (x : ℝ) (Y : Height) :
    Meromorphic (fun u => eisensteinNumerator u x Y.val) := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hplus : Differentiable ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 + u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + u) u).const_cpow
      (Or.inl hY)
  have hminus : Differentiable ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 - u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 - u) u).const_cpow
      (Or.inl hY)
  have hxi : Differentiable ℂ (fun u : ℂ => xi (2 * u)) :=
    xi_differentiable.comp (by fun_prop)
  have htail : Differentiable ℂ (fun u => eisTail u x Y.val) :=
    fun u => differentiableAt_eisTail x Y.property u
  intro u
  have ha : AnalyticAt ℂ (fun u : ℂ => 1 + 2 * u) u := by fun_prop
  have hb : AnalyticAt ℂ (fun u : ℂ => 2 * u - 1) u := by fun_prop
  have hc : AnalyticAt ℂ (fun u : ℂ => (1 + 2 * u) * (2 * u)) u := by fun_prop
  exact (((hplus.analyticAt u).meromorphicAt.mul
      (differentiable_xi_shift.analyticAt u).meromorphicAt).add
      (((ha.meromorphicAt.div hb.meromorphicAt).mul
        (hxi.analyticAt u).meromorphicAt).mul (hminus.analyticAt u).meromorphicAt)).add
    (hc.meromorphicAt.mul (htail.analyticAt u).meromorphicAt)

/-- The continued transform is meromorphic on the whole parameter plane. -/
theorem meromorphic_narainMellinContinuation (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    Meromorphic (narainMellinContinuation ρ σ) := by
  intro u
  have h2 : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) u := analyticAt_const
  have hc : AnalyticAt ℂ (fun u : ℂ => u * (1 + 2 * u)) u := by fun_prop
  exact (h2.meromorphicAt.mul
    (((meromorphic_eisensteinNumerator ρ.x ⟨ρ.y, ρ.y_pos⟩ u).mul
      (meromorphic_eisensteinNumerator σ.x ⟨σ.y, σ.y_pos⟩ u)).div
        (differentiable_xi_shift.analyticAt u).meromorphicAt)).div hc.meromorphicAt

private theorem resonance_normalization_ne_zero (p : Resonance) :
    p.val * (1 + 2 * p.val) ≠ 0 := by
  have hr := re_neg_of_xi_shift_eq_zero p.property
  have hl := re_gt_of_xi_shift_eq_zero p.property
  apply mul_ne_zero
  · intro h
    simp [h] at hr
  · intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith only [hl, hh]

private theorem normalized_order (p : Resonance) (f : ℂ → ℂ) :
    meromorphicOrderAt (fun u => 2 * f u / (u * (1 + 2 * u))) p.val =
      meromorphicOrderAt f p.val := by
  have hc : AnalyticAt ℂ (fun u : ℂ => u * (1 + 2 * u)) p.val := by fun_prop
  have hg : AnalyticAt ℂ (fun u : ℂ => 2 / (u * (1 + 2 * u))) p.val :=
    analyticAt_const.div hc (resonance_normalization_ne_zero p)
  have heq : (fun u => 2 * f u / (u * (1 + 2 * u))) =
      (fun u : ℂ => 2 / (u * (1 + 2 * u))) * f := by
    funext u
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  rw [heq, meromorphicOrderAt_mul_of_ne_zero hg
    (div_ne_zero two_ne_zero (resonance_normalization_ne_zero p))]

/-- Every arithmetic resonance occurs with full multiplicity in actual scalar
Mellin continuations, for some target pair on any prescribed horocycles. -/
theorem exists_narainMellinContinuation_full_order (p : Resonance) (Y Z : Height) :
    ∃ x ∈ Ioc (0 : ℝ) 1, ∃ w ∈ Ioc (0 : ℝ) 1,
      meromorphicOrderAt
        (narainMellinContinuation ⟨x, Y.val, Y.property⟩ ⟨w, Z.val, Z.property⟩) p.val =
          -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  obtain ⟨x, hx, w, hw, horder⟩ := exists_product_full_order p Y Z
  refine ⟨x, hx, w, hw, ?_⟩
  change meromorphicOrderAt (fun u =>
    2 * productQuotient Y Z x w u / (u * (1 + 2 * u))) p.val = _
  rw [normalized_order]
  exact horder

/-- Double target-horocycle averaging preserves every arithmetic pole order. -/
theorem narainMellinMean_full_order (p : Resonance) (Y Z : Height) :
    meromorphicOrderAt (narainMellinMean Y Z) p.val =
      -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  change meromorphicOrderAt (fun u =>
    2 * meanQuotient Y Z u / (u * (1 + 2 * u))) p.val = _
  rw [normalized_order, meanQuotient_full_order]

/-- The averaged continuation has a genuine pole, of finite positive multiplicity. -/
theorem narainMellinMean_pole (p : Resonance) (Y Z : Height) :
    ∃ n : ℕ, meromorphicOrderAt (narainMellinMean Y Z) p.val = -((n + 1 : ℕ) : ℤ) := by
  obtain ⟨n, hn⟩ := meanQuotient_pole p Y Z
  refine ⟨n, ?_⟩
  rw [narainMellinMean_full_order, ← meanQuotient_full_order p Y Z]
  exact hn

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMellinContinuation_eq_projection
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.integral_mellin_narainScalarHeat
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMellinMean_one_eq
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.meromorphic_narainMellinContinuation
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.exists_narainMellinContinuation_full_order
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.narainMellinMean_pole
