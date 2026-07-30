import GaloisForLFunctions.RHTower.CCMRectangularScrewCurvature

/-!
# One rectangular carrier recovers transverse Xi growth

The logarithmically sampled fixed-width rectangular Weil sequence has a sharp
power-growth exponent.  If the right Xi divisor is nonempty, its exponent is
the supremal horizontal displacement from the critical line.  Under RH the
same family is uniformly bounded.  Thus one scalar cofinal carrier measures,
and does not merely detect, transverse divisor escape.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- No polynomial exponent strictly below the transverse Xi supremum can
eventually bound the absolute rectangular dominant coefficients. -/
theorem no_eventual_power_bound_xiRectangularRightDirichletCoefficientReal
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < xiRightTransverseSup) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |xiRectangularRightDirichletCoefficientReal L n| ≤ C * (n : ℝ) ^ α := by
  rintro ⟨C, hC, N, hbound⟩
  let β : ℝ := (α + xiRightTransverseSup) / 2
  have hαβ : α < β := by
    dsimp only [β]
    linarith
  have hβsup : β < xiRightTransverseSup := by
    dsimp only [β]
    linarith
  have hβ0 : 0 ≤ β := hα0.trans hαβ.le
  have hsum : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L 0 N n : ℝ) : ℂ))
      ((1 + β : ℝ) : ℂ) := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + α)
    · simp only [ofReal_add, ofReal_one, add_re, one_re, ofReal_re]
      linarith
    · refine ⟨C, fun n hn => ?_⟩
      rw [xiRectangularLandauCoefficient]
      split_ifs with hN
      · rw [add_zero, Complex.norm_real, Real.norm_eq_abs]
        simpa only [add_sub_cancel_left] using hbound n hN
      · simp only [ofReal_zero, norm_zero]
        positivity
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ 1 + β :=
    xiRightShiftedPole_re_le_of_landau_summable hL 0 N
      (by linarith) (xiRightTransverseSup_pos hne).le
      (fun q => xiRightCenteredZero_re_le_sup q) hsum
  have hcenterBound : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ β := by
    intro q
    have hq := hpoleBound q
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hq
    linarith
  have hsupBound : xiRightTransverseSup ≤ β := by
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact hcenterBound q
  linarith

/-- Positive sharpness form: every subcritical power scale is exceeded
cofinally by the dominant coefficient sequence. -/
theorem xiRectangularRightDirichletCoefficientReal_cofinally_exceeds_power
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ) ^ α <
        |xiRectangularRightDirichletCoefficientReal L n| := by
  intro C hC N
  by_contra hnot
  push Not at hnot
  apply no_eventual_power_bound_xiRectangularRightDirichletCoefficientReal
    hL hne hα0 hα
  exact ⟨C, hC, N, hnot⟩

/-- Under RH every aperture beyond the fixed width has one uniform
reciprocal-square bound. -/
theorem norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis
    {L a : ℝ} (hRH : RiemannHypothesis) (hLa : L ≤ a) :
    ‖xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a)‖ ≤
      rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  have hdom : (∑' q : XiZeroCopy,
      xiRectangularTwoEdgeDominant L a (xiSpectralPoint q)) = 0 := by
    have hzero : ∀ q : XiZeroCopy,
        xiRectangularTwoEdgeDominant L a (xiSpectralPoint q) = 0 := by
      intro q
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [xiRectangularTwoEdgeDominant, ht]
      apply rectangularTwoEdgeDominant_of_re_eq_zero
      simp
    simp only [hzero, tsum_zero]
  have hrem := norm_xiWeilPolarization_rectangular_sub_dominant_le hLa
  rw [hdom, sub_zero] at hrem
  exact hrem

/-- If RH fails, the transverse supremum is an upper power exponent for the
actual fixed-width logarithmic Weil sequence. -/
theorem norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
    {L : ℝ} (hne : Nonempty XiRightZeroCopy) {n : ℕ}
    (hn : 1 ≤ n) (hLa : L ≤ Real.log n / 2) :
    ‖xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
      (2 * xiRectangularRightCoefficientNormSum L +
        rectangularTwoEdgeRemainderBound L *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
        (n : ℝ) ^ xiRightTransverseSup := by
  let K : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by unfold rectangularTwoEdgeRemainderBound; positivity)
      (tsum_nonneg fun q => by positivity)
  have hpow : 1 ≤ (n : ℝ) ^ xiRightTransverseSup := by
    exact Real.one_le_rpow (by exact_mod_cast hn)
      (xiRightTransverseSup_pos hne).le
  have hcoeff := abs_xiRectangularRightDirichletCoefficientReal_le L
    (fun q => xiRightCenteredZero_re_le_sup q) hn
  have hrem := norm_xiWeilPolarization_rectangular_sub_dominant_le hLa
  rw [tsum_xiRectangularTwoEdgeDominant_logSample_eq_ofReal_rightCoefficient
    L hn hLa] at hrem
  have htri := norm_add_le
    (xiWeilPolarization
      (xiRectangularTwoEdgeTransform L (Real.log n / 2))
      (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
        (xiRectangularRightDirichletCoefficientReal L n : ℂ))
    (xiRectangularRightDirichletCoefficientReal L n : ℂ)
  have hQ :
      ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
        K + |xiRectangularRightDirichletCoefficientReal L n| := by
    calc
      ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ =
          ‖(xiWeilPolarization
              (xiRectangularTwoEdgeTransform L (Real.log n / 2))
              (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
                (xiRectangularRightDirichletCoefficientReal L n : ℂ)) +
              (xiRectangularRightDirichletCoefficientReal L n : ℂ)‖ := by
            congr 1
            ring
      _ ≤ ‖xiWeilPolarization
              (xiRectangularTwoEdgeTransform L (Real.log n / 2))
              (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
                (xiRectangularRightDirichletCoefficientReal L n : ℂ)‖ +
            ‖(xiRectangularRightDirichletCoefficientReal L n : ℂ)‖ := htri
      _ ≤ K + |xiRectangularRightDirichletCoefficientReal L n| := by
            simpa only [Complex.norm_real, Real.norm_eq_abs] using
              add_le_add hrem (le_refl
                |xiRectangularRightDirichletCoefficientReal L n|)
  dsimp only [K] at hK ⊢
  calc
    ‖xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
      K + |xiRectangularRightDirichletCoefficientReal L n| := hQ
    _ ≤ K + 2 * xiRectangularRightCoefficientNormSum L *
        (n : ℝ) ^ xiRightTransverseSup := by gcongr
    _ ≤ K * (n : ℝ) ^ xiRightTransverseSup +
        2 * xiRectangularRightCoefficientNormSum L *
          (n : ℝ) ^ xiRightTransverseSup := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hK
    _ = (2 * xiRectangularRightCoefficientNormSum L + K) *
        (n : ℝ) ^ xiRightTransverseSup := by ring

/-- Sharp lower power law for the actual Weil values: every exponent below
the transverse Xi supremum is exceeded cofinally. -/
theorem xiWeilPolarization_rectangular_logSample_cofinally_exceeds_power
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < xiRightTransverseSup) :
    ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      C * (n : ℝ) ^ α <
        ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ := by
  intro C hC N0
  let K : ℝ := rectangularTwoEdgeRemainderBound L *
    ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by unfold rectangularTwoEdgeRemainderBound; positivity)
      (tsum_nonneg fun q => by positivity)
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt
    (max (N0 : ℝ) (Real.exp (2 * L)))
  have hN0 : N0 ≤ N := by
    exact_mod_cast (le_max_left (N0 : ℝ) (Real.exp (2 * L))).trans hN.le
  have hNexp : Real.exp (2 * L) < (N : ℝ) :=
    (le_max_right (N0 : ℝ) (Real.exp (2 * L))).trans_lt hN
  obtain ⟨n, hnN, hcoeff⟩ :=
    xiRectangularRightDirichletCoefficientReal_cofinally_exceeds_power
      hL hne hα0 hα (C + K) (add_nonneg hC hK) N
  have hn0 : N0 ≤ n := hN0.trans hnN
  have hnexp : Real.exp (2 * L) < (n : ℝ) :=
    hNexp.trans_le (by exact_mod_cast hnN)
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hnexp
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  have hlog : 2 * L < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  have hLa : L ≤ Real.log n / 2 := by linarith
  refine ⟨n, hn0, hLa, ?_⟩
  have hpow : 1 ≤ (n : ℝ) ^ α :=
    Real.one_le_rpow (by exact_mod_cast hn1) hα0
  have hrem := norm_xiWeilPolarization_rectangular_sub_dominant_le hLa
  rw [tsum_xiRectangularTwoEdgeDominant_logSample_eq_ofReal_rightCoefficient
    L hn1 hLa] at hrem
  have hcoeffLe : |xiRectangularRightDirichletCoefficientReal L n| ≤
      ‖xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ + K := by
    have htri := norm_sub_le
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2)))
      (xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
          (xiRectangularRightDirichletCoefficientReal L n : ℂ))
    have := htri.trans (add_le_add (le_refl _) hrem)
    have hcancel :
        xiWeilPolarization
            (xiRectangularTwoEdgeTransform L (Real.log n / 2))
            (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
          (xiWeilPolarization
              (xiRectangularTwoEdgeTransform L (Real.log n / 2))
              (xiRectangularTwoEdgeTransform L (Real.log n / 2)) -
            (xiRectangularRightDirichletCoefficientReal L n : ℂ)) =
          (xiRectangularRightDirichletCoefficientReal L n : ℂ) := by ring
    rw [hcancel, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hKpow : K ≤ K * (n : ℝ) ^ α := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hK
  nlinarith

/-- The transverse Xi supremum is the sharp power exponent of the one
fixed-width logarithmic rectangular Weil sequence. -/
theorem xiRightTransverseSup_is_sharp_rectangular_power_exponent
    {L : ℝ} (hL : 0 < L) (hne : Nonempty XiRightZeroCopy) :
    (∀ n : ℕ, 1 ≤ n → L ≤ Real.log n / 2 →
      ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤
        (2 * xiRectangularRightCoefficientNormSum L +
          rectangularTwoEdgeRemainderBound L *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) *
          (n : ℝ) ^ xiRightTransverseSup) ∧
    (∀ α : ℝ, 0 ≤ α → α < xiRightTransverseSup →
      ∀ C : ℝ, 0 ≤ C → ∀ N0 : ℕ, ∃ n : ℕ,
        N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
        C * (n : ℝ) ^ α <
          ‖xiWeilPolarization
            (xiRectangularTwoEdgeTransform L (Real.log n / 2))
            (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖) := by
  constructor
  · intro n hn hLa
    exact norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
      hne hn hLa
  · intro α hα0 hα C hC N0
    exact xiWeilPolarization_rectangular_logSample_cofinally_exceeds_power
      hL hne hα0 hα C hC N0

/-- Boundedness of the one fixed-width logarithmic rectangular sequence is
itself exactly RH. -/
theorem riemannHypothesis_iff_rectangular_logSample_weil_norm_bdd
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n : ℕ, L ≤ Real.log n / 2 →
        ‖xiWeilPolarization
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))
          (xiRectangularTwoEdgeTransform L (Real.log n / 2))‖ ≤ C := by
  constructor
  · intro hRH
    refine ⟨rectangularTwoEdgeRemainderBound L *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2, ?_⟩
    intro n hLa
    exact norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis hRH hLa
  · rintro ⟨C, hbound⟩
    by_contra hRH
    have hne := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have hsup := xiRightTransverseSup_pos hne
    obtain ⟨n, hn0, hLa, hexceed⟩ :=
      xiWeilPolarization_rectangular_logSample_cofinally_exceeds_power
        hL hne (le_refl 0) hsup (max C 0 + 1) (by positivity) 0
    have hC : C < max C 0 + 1 := by linarith [le_max_left C 0]
    have hpow : (n : ℝ) ^ (0 : ℝ) = 1 := by simp
    rw [hpow, mul_one] at hexceed
    exact (not_lt_of_ge (hbound n hLa)) (hC.trans hexceed)

end

end RHTower
