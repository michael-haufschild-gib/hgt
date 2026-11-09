import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.LaplaceBounds
import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.GridGeometry
import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.PolynomialPulses

/-! Strict positivity of the real Laplace transform permits finite positive translation
repair of a Lipschitz source with positive tails and all exponential moments.
A lower grid preserves all Laplace signs: fixed outer bands handle large tilts,
while weighted approximation handles a compact interval of tilts. Polynomial
coefficient repair then converts that lower grid into a positive source average. -/

open MeasureTheory Set Filter Topology Polynomial
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

/-- Every strictly positive real Laplace transform admits arbitrarily fine positive
polynomial lower pulses, provided the source is Lipschitz and positive at both ends. -/
theorem exists_positive_lower_grid {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hmoment : ∀ c : ℝ, Integrable fun x => Real.exp (c * |x|) * |f x|)
    (htail : ∃ A : ℝ, ∀ x, A < |x| → 0 < f x)
    (hlap : ∀ s : ℝ, 0 < ∫ x, f x * Real.exp (s * x))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R h : ℝ) (M : ℕ), 0 < h ∧ h < δ ∧ 0 < M ∧
      (∀ x, lowerGridStep f L (-R) h M x ≤ f x) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < (gridPolynomial (fun y => f y - L * h) (-R) h M).eval x) := by
  obtain ⟨A₀, hA₀⟩ := htail
  let A := max A₀ 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA : 0 ≤ A := zero_le_one.trans hA1
  have htailA : ∀ x, A < |x| → 0 < f x :=
    fun x hx => hA₀ x ((le_max_left _ _).trans_lt hx)
  obtain ⟨y₀, hy₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by linarith : -A - 1 ≤ A + 1)) hf.abs.continuousOn
  let B := |f y₀|
  have hB : 0 ≤ B := abs_nonneg _
  have hinner : ∀ y, |y| ≤ A + 1 → |f y| ≤ B := by
    intro y hy
    apply hmax
    have hy' := abs_le.mp hy
    exact ⟨by linarith only [hy'.1], hy'.2⟩
  obtain ⟨m, hm, hmband⟩ := exists_pos_annulus_margin hf
    (by linarith : 0 ≤ A + 2) (by linarith : A + 2 ≤ A + 5)
    (fun x hx _ => htailA x (by linarith only [hx]))
  -- Fix the outer bands before truncation; their tilt threshold is independent of the mesh.
  have hSlarge : ∀ᶠ s : ℝ in atTop, 2 * (A + 2) * (B + 1) < (m / 2) * Real.exp s :=
    (Real.tendsto_exp_atTop.const_mul_atTop (by positivity : 0 < m / 2)).eventually_gt_atTop _
  obtain ⟨S, hS, hgap⟩ := ((eventually_ge_atTop (1 : ℝ)).and hSlarge).exists
  obtain ⟨η, hη, hmargin⟩ := exists_laplace_margin hf.measurable (by linarith : 0 ≤ S)
    (hmoment S) hlap
  have htailSmall : Tendsto
      (fun R : ℝ => Real.exp (-R) * ∫ x, Real.exp ((S + 1) * |x|) * |f x|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const
        (∫ x, Real.exp ((S + 1) * |x|) * |f x|)
  obtain ⟨R, hR, htailR⟩ := ((eventually_gt_atTop (A + 6)).and
    (htailSmall.eventually (gt_mem_nhds (by positivity : 0 < η / 4)))).exists
  have hR0 : 0 < R := by linarith only [hA, hR]
  obtain ⟨u, hu, huband⟩ := exists_pos_annulus_margin hf
    (by linarith : 0 ≤ A + 1) (by linarith : A + 1 ≤ R)
    (fun x hx _ => htailA x (by linarith only [hx]))
  -- One mesh preserves the positive bands, the first cell, and the compact Laplace margin.
  let ε := min δ (min 1 (min (1 / L) (min (u / (2 * L))
    (min (m / (2 * L)) (η / (16 * R * L * Real.exp (S * R)))))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨M, hM, hh, hmesh, hend⟩ := exists_symmetric_mesh hR0 hε
  let h := 2 * R / M
  change 0 < h at hh
  change h < ε at hmesh
  change -R + M * h = R at hend
  have hδ' : h < δ := hmesh.trans_le (min_le_left _ _)
  have hh1 : h ≤ 1 := (hmesh.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hhL : L * h ≤ 1 := by
    have ht : h < 1 / L := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have ht' := (lt_div_iff₀ hL).mp ht
    linarith only [ht']
  have hhu : L * h < u / 2 := by
    have ht : h < u / (2 * L) := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
    have ht' := (lt_div_iff₀ (mul_pos two_pos hL)).mp ht
    nlinarith only [ht']
  have hhm : L * h ≤ m / 2 := by
    have ht : h < m / (2 * L) := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    have ht' := (lt_div_iff₀ (mul_pos two_pos hL)).mp ht
    nlinarith only [ht']
  have hhη : 4 * R * L * h * Real.exp (S * R) < η / 4 := by
    have ht : h < η / (16 * R * L * Real.exp (S * R)) := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    have ht' := (lt_div_iff₀ (by positivity : 0 < 16 * R * L * Real.exp (S * R))).mp ht
    nlinarith only [ht']
  let g := lowerGridStep f L (-R) h M
  have hgi (s : ℝ) : Integrable fun x => g x * Real.exp (s * x) := by
    change Integrable (fun x => gridStep (fun y => f y - L * h) (-R) h M x * Real.exp (s * x))
    rw [← polynomialAverage_gridPolynomial]
    simp only [polynomialAverage_apply, Finset.sum_mul, mul_assoc]
    exact integrable_finsetSum _ fun (i : ℕ) _ =>
      (integrable_translate_exp (integrable_gridPulse_exp (-R) h s) ((i : ℝ) * h)).const_mul _
  -- Compact error controls bounded tilts; the two positive bands control the remaining tails.
  have hgp (s : ℝ) : 0 < ∫ x, g x * Real.exp (s * x) := by
    by_cases hs : |s| ≤ S
    · have he := laplace_sub_le_of_compact_error hf.measurable (by linarith : 0 ≤ S) hs
        hR0.le (by positivity : 0 ≤ 2 * L * h) (hmoment (S + 1)) (hgi s)
        (fun x hx => (lowerGridStep_bounds (a := -R) (M := M) (x := x)
          hL.le hh hlip (by simpa only [hend] using hx)).2)
        (fun x hx => gridStep_eq_zero (f := fun y => f y - L * h) (a := -R)
          (M := M) (x := x) hh.le (by simpa only [hend] using hx))
      have hl := hmargin s hs
      change (∫ x, f x * Real.exp (s * x)) - (∫ x, g x * Real.exp (s * x)) ≤ _ at he
      nlinarith only [he, hl, hhη, htailR, hη]
    · apply laplace_pos_of_outer_bands (g := g) (by linarith : 0 ≤ A + 2)
        (by positivity : 0 < m / 2) (by linarith : 0 ≤ B + 1) hgi
        (lowerGridStep_lower_bound hB hh hend (by linarith only [hhu, hu]) hhL huband hinner)
        (fun x hx => lowerGridStep_nonneg_outside hh hh1 hend (by linarith only [hhu, hu]) huband hx)
        (fun x hl hu => lowerGridStep_pos_on_outer_bands hh hh1 hend
          (by linarith only [hR]) hhm hmband ⟨by linarith only [hl], by linarith only [hu]⟩)
        hgap s (lt_of_not_ge hs).le
  refine ⟨R, h, M, hh, hδ', hM, ?_, ?_⟩
  · intro x
    apply lowerGridStep_le hL.le hh hlip _ x
    intro y hy
    apply (htailA y ?_).le
    rw [hend] at hy
    by_contra hn
    have hy' := abs_le.mp (le_of_not_gt hn)
    exact hy ⟨by linarith only [hy'.1, hR], by linarith only [hy'.2, hR]⟩
  · apply gridPolynomial_eval_pos_of_laplace_pos hh _ hM hgp
    have hleft := huband (-R) (by rw [abs_neg, abs_of_pos hR0]; linarith only [hR])
      (by rw [abs_neg, abs_of_pos hR0])
    linarith only [hleft, hhu, hu]

/-- Positive real Laplace values and positive tails suffice for repair by a finite
positive translation average, at an arbitrarily small mesh. -/
theorem exists_positive_average_of_laplace_positive {f : ℝ → ℝ} (hf : Continuous f)
    {L : ℝ} (hL : 0 < L) (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hmoment : ∀ c : ℝ, Integrable fun x => Real.exp (c * |x|) * |f x|)
    (htail : ∃ A : ℝ, ∀ x, A < |x| → 0 < f x)
    (hlap : ∀ s : ℝ, 0 < ∫ x, f x * Real.exp (s * x)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (h : ℝ) (r : List ℝ), 0 < h ∧ h < δ ∧ (∀ a ∈ r, 0 < a) ∧
      ∀ x, 0 ≤ polynomialAverage (negativeRootMultiplier r) h f x := by
  obtain ⟨R, h, M, hh, hhδ, _, hlower, hp⟩ :=
    exists_positive_lower_grid hf hL hlip hmoment htail hlap hδ
  obtain ⟨r, hr, hpos⟩ := exists_positive_average_of_polynomial_lower_bound
    (gridPolynomial (fun y => f y - L * h) (-R) h M) hp h
    (b := gridPulse (-R) h) (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (by simpa only [polynomialAverage_gridPolynomial, lowerGridStep] using hlower)
  exact ⟨h, r, hh, hhδ, hr, hpos⟩

#print axioms exists_positive_lower_grid
#print axioms exists_positive_average_of_laplace_positive
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
