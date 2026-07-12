import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.LandauSummabilityTransfer
import GaloisForLFunctions.RHTower.XiThreeHalvesSummability
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound

/-!
# Logarithmically sampled rectangular CCM carrier

This module isolates the Dirichlet-series layer of the explicit rectangular
two-edge route.  A positive-transverse Xi copy contributes the nonzero weight
`A_L(w)^2`; at aperture `(log n)/2` its growing edge is exactly `A_L(w)^2 n^w`.

The results below establish the unconditional coefficient summability and the
shifted-zeta series on a safe right half-plane.  They do not assert its local
continuation to the Landau boundary or any RH implication.
-/

open Complex

namespace RHTower

noncomputable section

/-- Multiplicity copies of Xi zeros strictly to the right of the critical
line, expressed in the literal centered-zero coordinate. -/
abbrev XiRightZeroCopy :=
  {q : XiZeroCopy // 0 < (I * xiSpectralPoint q).re}

/-- The literal centered Xi zero `rho-1/2` attached to a right-half copy. -/
def xiRightCenteredZero (q : XiRightZeroCopy) : ℂ :=
  I * xiSpectralPoint q.1

theorem xiRightCenteredZero_re_pos (q : XiRightZeroCopy) :
    0 < (xiRightCenteredZero q).re := q.2

theorem xiRightCenteredZero_ne_zero (q : XiRightZeroCopy) :
    xiRightCenteredZero q ≠ 0 := by
  exact mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q.1)

theorem abs_xiRightCenteredZero_re_lt_half (q : XiRightZeroCopy) :
    |(xiRightCenteredZero q).re| < (1 / 2 : ℝ) :=
  abs_re_I_mul_xiSpectralPoint_le_half q.1

/-- The set of positive transverse displacements of the actual Xi divisor. -/
def xiRightTransverseSet : Set ℝ :=
  Set.range (fun q : XiRightZeroCopy => (xiRightCenteredZero q).re)

/-- The rightmost transverse displacement of the actual Xi divisor. -/
noncomputable def xiRightTransverseSup : ℝ :=
  sSup xiRightTransverseSet

theorem xiRightTransverseSet_bddAbove : BddAbove xiRightTransverseSet := by
  refine ⟨1 / 2, ?_⟩
  rintro x ⟨q, rfl⟩
  exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

theorem xiRightCenteredZero_re_le_sup
    (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re ≤ xiRightTransverseSup := by
  exact le_csSup xiRightTransverseSet_bddAbove ⟨q, rfl⟩

theorem xiRightTransverseSup_le_half (hne : Nonempty XiRightZeroCopy) :
    xiRightTransverseSup ≤ 1 / 2 := by
  apply csSup_le (Set.range_nonempty _)
  intro x hx
  rcases hx with ⟨q, rfl⟩
  exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

theorem xiRightTransverseSup_pos (hne : Nonempty XiRightZeroCopy) :
    0 < xiRightTransverseSup := by
  obtain ⟨q⟩ := hne
  exact (xiRightCenteredZero_re_pos q).trans_le
    (xiRightCenteredZero_re_le_sup q)

/-- Failure of RH supplies an actual multiplicity copy in the positive
transverse half of the centered Xi divisor. -/
theorem nonempty_xiRightZeroCopy_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) : Nonempty XiRightZeroCopy := by
  have hnotfree : ¬∀ s ∈ rightHalf, xi s ≠ 0 := by
    intro hfree
    exact hRH (rh_iff_xi_ne_zero_right.mpr hfree)
  push Not at hnotfree
  obtain ⟨s, hs, hzero⟩ := hnotfree
  let ρ : XiDivisorSupport :=
    ⟨s, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  refine ⟨⟨q, ?_⟩⟩
  rw [I_mul_xiSpectralPoint]
  dsimp only [q, ρ]
  have hsre := mem_rightHalf.mp hs
  simpa [Complex.sub_re] using hsre

/-- The unconditional Xi ordinate gap restricted to positive transverse
multiplicity copies. -/
theorem exists_xiRightCenteredZero_abs_im_lower_bound :
    ∃ η : ℝ, 0 < η ∧
      ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im| := by
  obtain ⟨η, hη, hbound⟩ := exists_xiZeroCopy_abs_im_lower_bound
  refine ⟨η, hη, fun q => ?_⟩
  simpa [xiRightCenteredZero, I_mul_xiSpectralPoint] using hbound q.1

/-- The fixed rectangular coefficient carried by a right-half Xi copy. -/
def xiRectangularRightCoefficient (L : ℝ) (q : XiRightZeroCopy) : ℂ :=
  rectangularWindowAmplitude L (xiRightCenteredZero q) ^ 2

/-- Positive window width makes every right-half rectangular coefficient
nonzero. -/
theorem xiRectangularRightCoefficient_ne_zero
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    xiRectangularRightCoefficient L q ≠ 0 := by
  exact pow_ne_zero 2
    (rectangularWindowAmplitude_ne_zero hL (xiRightCenteredZero_re_pos q))

/-- The coefficient norm is controlled by the canonical reciprocal-square Xi
majorant. -/
theorem norm_xiRectangularRightCoefficient_le
    (L : ℝ) (q : XiRightZeroCopy) :
    ‖xiRectangularRightCoefficient L q‖ ≤
      (1 + Real.exp (|L| / 2)) ^ 2 /
        ‖xiSpectralPoint q.1‖ ^ 2 := by
  rw [xiRectangularRightCoefficient, norm_pow]
  have hA := norm_rectangularWindowAmplitude_le L
    (xiRightCenteredZero_ne_zero q)
    (le_of_lt (abs_xiRightCenteredZero_re_lt_half q))
  have hA2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  rw [xiRightCenteredZero, norm_mul, norm_I, one_mul] at hA2
  calc
    ‖rectangularWindowAmplitude L (xiRightCenteredZero q)‖ ^ 2 ≤
        ((1 + Real.exp (|L| / 2)) / ‖xiSpectralPoint q.1‖) ^ 2 := hA2
    _ = (1 + Real.exp (|L| / 2)) ^ 2 /
        ‖xiSpectralPoint q.1‖ ^ 2 := by ring

/-- The right-half rectangular coefficient family is absolutely summable with
analytic multiplicity. -/
theorem xiRectangularRightCoefficient_summable (L : ℝ) :
    Summable (xiRectangularRightCoefficient L) := by
  have hbase : Summable (fun q : XiRightZeroCopy =>
      1 / ‖xiSpectralPoint q.1‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.subtype _
  apply Summable.of_norm_bounded
    (hbase.mul_left ((1 + Real.exp (|L| / 2)) ^ 2))
  intro q
  calc
    ‖xiRectangularRightCoefficient L q‖ ≤
        (1 + Real.exp (|L| / 2)) ^ 2 /
          ‖xiSpectralPoint q.1‖ ^ 2 :=
      norm_xiRectangularRightCoefficient_le L q
    _ = (1 + Real.exp (|L| / 2)) ^ 2 *
        (1 / ‖xiSpectralPoint q.1‖ ^ 2) := by ring

/-- Schwarz conjugation restricted to the positive transverse Xi copies. -/
def xiRightZeroCopyConjEquiv : XiRightZeroCopy ≃ XiRightZeroCopy :=
  Equiv.subtypeEquiv xiZeroCopyConjEquiv (fun q => by
    rw [I_mul_xiSpectralPoint_copyConj]
    simp)

theorem xiRightCenteredZero_conj (q : XiRightZeroCopy) :
    xiRightCenteredZero (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiRightCenteredZero q) := by
  exact I_mul_xiSpectralPoint_copyConj q.1

theorem xiRectangularRightCoefficient_conj (L : ℝ) (q : XiRightZeroCopy) :
    xiRectangularRightCoefficient L (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiRectangularRightCoefficient L q) := by
  rw [xiRectangularRightCoefficient, xiRectangularRightCoefficient,
    xiRightCenteredZero_conj, ← rectangularWindowAmplitude_conj, map_pow]

/-- One positive-transverse exponential coefficient at the logarithmic
sample `n`. -/
def xiRectangularRightDirichletTerm
    (L : ℝ) (n : ℕ) (q : XiRightZeroCopy) : ℂ :=
  xiRectangularRightCoefficient L q *
    (n : ℂ) ^ (xiRightCenteredZero q)

theorem xiRectangularRightDirichletTerm_summable
    (L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Summable (xiRectangularRightDirichletTerm L n) := by
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Summable.of_norm_bounded
    ((xiRectangularRightCoefficient_summable L).norm.mul_right
      ((n : ℝ) ^ (1 / 2 : ℝ)))
  intro q
  rw [xiRectangularRightDirichletTerm, norm_mul,
    Complex.norm_natCast_cpow_of_pos hnpos]
  gcongr
  exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

lemma natCast_cpow_conj_rectangular (n : ℕ) (w : ℂ) :
    ((n : ℂ)) ^ ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (((n : ℂ)) ^ w) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Ne.symm Real.pi_ne_zero
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem xiRectangularRightDirichletTerm_conj
    (L : ℝ) (n : ℕ) (q : XiRightZeroCopy) :
    xiRectangularRightDirichletTerm L n (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiRectangularRightDirichletTerm L n q) := by
  rw [xiRectangularRightDirichletTerm, xiRectangularRightDirichletTerm,
    xiRectangularRightCoefficient_conj, xiRightCenteredZero_conj,
    natCast_cpow_conj_rectangular, map_mul]

/-- Twice the complete right-half exponential sum.  This is the logarithmic
sample of the full FE-paired dominant carrier. -/
def xiRectangularRightDirichletComplex (L : ℝ) (n : ℕ) : ℂ :=
  2 * ∑' q : XiRightZeroCopy, xiRectangularRightDirichletTerm L n q

theorem star_xiRectangularRightDirichletComplex (L : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (xiRectangularRightDirichletComplex L n) =
      xiRectangularRightDirichletComplex L n := by
  rw [xiRectangularRightDirichletComplex, map_mul, map_ofNat]
  congr 1
  calc
    (starRingEnd ℂ)
        (∑' q : XiRightZeroCopy, xiRectangularRightDirichletTerm L n q) =
      ∑' q : XiRightZeroCopy,
        (starRingEnd ℂ) (xiRectangularRightDirichletTerm L n q) := by
          exact Complex.conj_tsum _
    _ = ∑' q : XiRightZeroCopy,
        xiRectangularRightDirichletTerm L n (xiRightZeroCopyConjEquiv q) := by
      apply tsum_congr
      intro q
      exact (xiRectangularRightDirichletTerm_conj L n q).symm
    _ = ∑' q : XiRightZeroCopy,
        xiRectangularRightDirichletTerm L n q := by
      simpa only using xiRightZeroCopyConjEquiv.tsum_eq
        (xiRectangularRightDirichletTerm L n)

/-- The real ordinary Dirichlet coefficient carried by the positive
transverse Xi divisor. -/
def xiRectangularRightDirichletCoefficientReal (L : ℝ) (n : ℕ) : ℝ :=
  (xiRectangularRightDirichletComplex L n).re

theorem xiRectangularRightDirichletComplex_im_eq_zero (L : ℝ) (n : ℕ) :
    (xiRectangularRightDirichletComplex L n).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_xiRectangularRightDirichletComplex L n)

theorem ofReal_xiRectangularRightDirichletCoefficientReal
    (L : ℝ) (n : ℕ) :
    ((xiRectangularRightDirichletCoefficientReal L n : ℝ) : ℂ) =
      xiRectangularRightDirichletComplex L n := by
  apply Complex.ext
  · rfl
  · simp [xiRectangularRightDirichletComplex_im_eq_zero L n]

/-- The total absolute mass of the fixed right-half rectangular weights. -/
def xiRectangularRightCoefficientNormSum (L : ℝ) : ℝ :=
  ∑' q : XiRightZeroCopy, ‖xiRectangularRightCoefficient L q‖

theorem norm_xiRectangularRightDirichletComplex_le
    (L : ℝ) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖xiRectangularRightDirichletComplex L n‖ ≤
      2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ δ := by
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterm := xiRectangularRightDirichletTerm_summable L hn
  have hmajor : Summable (fun q : XiRightZeroCopy =>
      ‖xiRectangularRightCoefficient L q‖ * (n : ℝ) ^ δ) :=
    (xiRectangularRightCoefficient_summable L).norm.mul_right ((n : ℝ) ^ δ)
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [xiRectangularRightDirichletComplex, norm_mul, hnorm2]
  calc
    (2 : ℝ) * ‖∑' q : XiRightZeroCopy,
        xiRectangularRightDirichletTerm L n q‖ ≤
      2 * ∑' q : XiRightZeroCopy,
        ‖xiRectangularRightDirichletTerm L n q‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm hterm.norm
    _ ≤ 2 * ∑' q : XiRightZeroCopy,
        (‖xiRectangularRightCoefficient L q‖ * (n : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hterm.norm.tsum_le_tsum (fun q => by
          rw [xiRectangularRightDirichletTerm, norm_mul,
            Complex.norm_natCast_cpow_of_pos hnpos]
          gcongr
          exact hupper q) hmajor
    _ = 2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ δ := by
      rw [xiRectangularRightCoefficientNormSum, tsum_mul_right]
      ring

theorem abs_xiRectangularRightDirichletCoefficientReal_le
    (L : ℝ) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {n : ℕ} (hn : 1 ≤ n) :
    |xiRectangularRightDirichletCoefficientReal L n| ≤
      2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ δ := by
  exact (Complex.abs_re_le_norm
    (xiRectangularRightDirichletComplex L n)).trans
      (norm_xiRectangularRightDirichletComplex_le L hupper hn)

/-- A tail-shifted real coefficient sequence.  Under a lower-bound hypothesis
it is coefficientwise nonnegative and is the sequence consumed by Landau. -/
def xiRectangularLandauCoefficient
    (L C : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then xiRectangularRightDirichletCoefficientReal L n + C else 0

theorem xiRectangularLandauCoefficient_nonneg
    {L C : ℝ} {N : ℕ}
    (hlower : ∀ n, N ≤ n →
      0 ≤ xiRectangularRightDirichletCoefficientReal L n + C) :
    ∀ n, 0 ≤ xiRectangularLandauCoefficient L C N n := by
  intro n
  rw [xiRectangularLandauCoefficient]
  split_ifs with hn
  · exact hlower n hn
  · exact le_rfl

theorem norm_xiRectangularLandauCoefficient_le
    (L C : ℝ) (N : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (n : ℕ) (hn : n ≠ 0) :
    ‖((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ)‖ ≤
      (2 * xiRectangularRightCoefficientNormSum L + |C|) *
        (n : ℝ) ^ δ := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ δ :=
    Real.one_le_rpow hnR hδ0
  rw [Complex.norm_real, Real.norm_eq_abs, xiRectangularLandauCoefficient]
  split_ifs with hN
  · calc
      |xiRectangularRightDirichletCoefficientReal L n + C| ≤
          |xiRectangularRightDirichletCoefficientReal L n| + |C| := abs_add_le _ _
      _ ≤ 2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ δ + |C| := by
        gcongr
        exact abs_xiRectangularRightDirichletCoefficientReal_le L hupper hn1
      _ ≤ 2 * xiRectangularRightCoefficientNormSum L * (n : ℝ) ^ δ +
          |C| * (n : ℝ) ^ δ := by
        gcongr
      _ = (2 * xiRectangularRightCoefficientNormSum L + |C|) *
          (n : ℝ) ^ δ := by ring
  · simp only [abs_zero]
    have hmass0 : 0 ≤ xiRectangularRightCoefficientNormSum L :=
      tsum_nonneg fun q => norm_nonneg _
    positivity

theorem xiRectangularLandauCoefficient_LSeriesSummable
    (L C : ℝ) (N : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    LSeries.LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ)) s := by
  apply LSeries.LSeriesSummable_of_le_const_mul_rpow (x := 1 + δ) hs
  refine ⟨2 * xiRectangularRightCoefficientNormSum L + |C|, fun n hn => ?_⟩
  convert norm_xiRectangularLandauCoefficient_le
    L C N hδ0 hupper n hn using 1 <;> ring

/-- The right-half shifted-zeta series attached to the rectangular window. -/
def xiRectangularShiftedZetaSeries (L : ℝ) (s : ℂ) : ℂ :=
  ∑' q : XiRightZeroCopy,
    xiRectangularRightCoefficient L q *
      riemannZeta (s - xiRightCenteredZero q)

/-- On `Re s >= 3/2+eps`, every shifted zeta factor has the uniform elementary
bound `1+1/eps`. -/
theorem norm_riemannZeta_sub_xiRightCenteredZero_le
    {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 3 / 2 + ε ≤ s.re)
    (q : XiRightZeroCopy) :
    ‖riemannZeta (s - xiRightCenteredZero q)‖ ≤ 1 + 1 / ε := by
  apply norm_riemannZeta_le hε
  rw [Complex.sub_re]
  have hright := abs_xiRightCenteredZero_re_lt_half q
  have hrelt : (xiRightCenteredZero q).re < 1 / 2 := (abs_lt.mp hright).2
  linarith

/-- Absolute summability of the shifted-zeta series on a safe right
half-plane. -/
theorem xiRectangularShiftedZetaSeries_summable
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 3 / 2 + ε ≤ s.re) :
    Summable (fun q : XiRightZeroCopy =>
      xiRectangularRightCoefficient L q *
        riemannZeta (s - xiRightCenteredZero q)) := by
  apply Summable.of_norm_bounded
    ((xiRectangularRightCoefficient_summable L).norm.mul_right (1 + 1 / ε))
  intro q
  rw [norm_mul]
  calc
    ‖xiRectangularRightCoefficient L q‖ *
        ‖riemannZeta (s - xiRightCenteredZero q)‖ ≤
      ‖xiRectangularRightCoefficient L q‖ * (1 + 1 / ε) := by
        gcongr
        exact norm_riemannZeta_sub_xiRightCenteredZero_le hε hs q

lemma sqrt_add_four_le_sqrt_add_two {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x + 4) ≤ Real.sqrt x + 2 := by
  have hxa : 0 ≤ x + 4 := by linarith
  have hsx := Real.sqrt_nonneg x
  have hsxa := Real.sqrt_nonneg (x + 4)
  have hsx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsxa_sq : (Real.sqrt (x + 4)) ^ 2 = x + 4 := Real.sq_sqrt hxa
  nlinarith

lemma inv_sq_mul_sqrt_add_two
    {x : ℝ} (hx : 0 < x) :
    (1 / x ^ 2) * (Real.sqrt x + 2) =
      1 / (x * Real.sqrt x) + 2 * (1 / x ^ 2) := by
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  field_simp
  nlinarith

/-- Uniform normal convergence of the shifted-zeta Xi series on a real ball
whose centre is one unit to the right of a common transverse upper bound.
The Xi ordinate gap keeps the ball away from every shifted zeta pole, while
the reciprocal-`3/2` divisor law absorbs the square-root vertical growth. -/
theorem summableLocallyUniformlyOn_xiRectangularShiftedZeta_ball
    (L : ℝ) {δ η r : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    SummableLocallyUniformlyOn
      (fun q : XiRightZeroCopy => fun s : ℂ =>
        xiRectangularRightCoefficient L q *
          riemannZeta (s - xiRightCenteredZero q))
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) := by
  let C0 : ℝ := (1 + Real.exp (|L| / 2)) ^ 2
  let Dz : ℝ := 2 + 1 / (η / 2) + 4 / 3
  have hthree : Summable (fun q : XiRightZeroCopy =>
      1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) :=
    xiSpectralPoint_inv_three_halves_summable.subtype _
  have htwo : Summable (fun q : XiRightZeroCopy =>
      1 / ‖xiSpectralPoint q.1‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.subtype _
  have hmajor : Summable (fun q : XiRightZeroCopy =>
      C0 * Dz *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖) +
          2 * (1 / ‖xiSpectralPoint q.1‖ ^ 2))) := by
    exact (hthree.add (htwo.mul_left 2)).mul_left (C0 * Dz)
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro s hs
  refine ⟨Metric.ball (((1 + δ : ℝ) : ℂ)) r,
    mem_nhdsWithin_of_mem_nhds ?_, ?_⟩
  · exact Metric.isOpen_ball.mem_nhds hs
  · apply HasSumUniformlyOn.of_norm_le_summable hmajor
    intro q x hx
    have hxball : ‖x - (((1 + δ : ℝ) : ℂ))‖ < r := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hx)
    have hxim : |x.im| < r := by
      have himnorm : |(x - (((1 + δ : ℝ) : ℂ))).im| ≤
          ‖x - (((1 + δ : ℝ) : ℂ))‖ := Complex.abs_im_le_norm _
      have himzero : (x - (((1 + δ : ℝ) : ℂ))).im = x.im := by simp
      rw [himzero] at himnorm
      exact lt_of_le_of_lt himnorm hxball
    have hxre : 1 + δ - r < x.re := by
      have hrenorm : |(x - (((1 + δ : ℝ) : ℂ))).re| ≤
          ‖x - (((1 + δ : ℝ) : ℂ))‖ := Complex.abs_re_le_norm _
      have hre : |x.re - (1 + δ)| < r := by
        exact lt_of_le_of_lt (by simpa [Complex.sub_re] using hrenorm) hxball
      rw [abs_lt] at hre
      linarith
    have hxnorm : ‖x‖ ≤ 2 := by
      have htri : ‖x‖ ≤ ‖x - (((1 + δ : ℝ) : ℂ))‖ +
          ‖(((1 + δ : ℝ) : ℂ))‖ := by
        calc
          ‖x‖ = ‖(x - (((1 + δ : ℝ) : ℂ))) + (((1 + δ : ℝ) : ℂ))‖ := by
            ring_nf
          _ ≤ ‖x - (((1 + δ : ℝ) : ℂ))‖ +
              ‖(((1 + δ : ℝ) : ℂ))‖ := norm_add_le _ _
      have hcenter : ‖(((1 + δ : ℝ) : ℂ))‖ = 1 + δ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        linarith
      rw [hcenter] at htri
      linarith
    let w : ℂ := xiRightCenteredZero q
    have hwre : w.re ≤ δ := hupper q
    have hwim : η ≤ |w.im| := hordinate q
    have hreal : 3 / 4 ≤ (x - w).re := by
      rw [Complex.sub_re]
      linarith
    have hpole : η / 2 ≤ ‖(x - w) - 1‖ := by
      have htriim : |w.im| ≤ |x.im - w.im| + |x.im| := by
        calc
          |w.im| = |(w.im - x.im) + x.im| := by ring_nf
          _ ≤ |w.im - x.im| + |x.im| := abs_add_le _ _
          _ = |x.im - w.im| + |x.im| := by rw [abs_sub_comm]
      have himlower : η / 2 ≤ |x.im - w.im| := by
        linarith
      have himnorm : |((x - w) - 1).im| ≤ ‖(x - w) - 1‖ :=
        Complex.abs_im_le_norm _
      have himid : ((x - w) - 1).im = x.im - w.im := by simp [Complex.sub_im]
      rw [himid] at himnorm
      exact le_trans himlower himnorm
    have hzeta : ‖riemannZeta (x - w)‖ ≤
        Dz * Real.sqrt (‖x - w‖ + 2) := by
      exact norm_riemannZeta_le_sqrt_norm_add_two hreal
        (half_pos hη) hpole
    have hwne : w ≠ 0 := xiRightCenteredZero_ne_zero q
    have hnpos : 0 < ‖xiSpectralPoint q.1‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
    have hwnorm : ‖w‖ = ‖xiSpectralPoint q.1‖ := by
      simp [w, xiRightCenteredZero]
    have harg : ‖x - w‖ + 2 ≤ ‖w‖ + 4 := by
      have hsub := norm_sub_le x w
      linarith
    have hsqrtarg : Real.sqrt (‖x - w‖ + 2) ≤
        Real.sqrt ‖w‖ + 2 := by
      calc
        Real.sqrt (‖x - w‖ + 2) ≤ Real.sqrt (‖w‖ + 4) :=
          Real.sqrt_le_sqrt harg
        _ ≤ Real.sqrt ‖w‖ + 2 :=
          sqrt_add_four_le_sqrt_add_two (norm_nonneg w)
    have hcoeff := norm_xiRectangularRightCoefficient_le L q
    have hprod :
        ‖xiRectangularRightCoefficient L q‖ * ‖riemannZeta (x - w)‖ ≤
          (C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := by
      apply mul_le_mul
      · simpa only [C0] using hcoeff
      · calc
          ‖riemannZeta (x - w)‖ ≤
              Dz * Real.sqrt (‖x - w‖ + 2) := hzeta
          _ ≤ Dz * (Real.sqrt ‖w‖ + 2) := by
            exact mul_le_mul_of_nonneg_left hsqrtarg (by
              dsimp only [Dz]
              positivity)
          _ = Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2) := by
            rw [hwnorm]
      · positivity
      · positivity
    rw [norm_mul]
    calc
      ‖xiRectangularRightCoefficient L q‖ * ‖riemannZeta (x - w)‖ ≤
          (C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := hprod
      _ = C0 * Dz *
          ((1 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := by ring
      _ = C0 * Dz *
          (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖) +
            2 * (1 / ‖xiSpectralPoint q.1‖ ^ 2)) := by
        rw [inv_sq_mul_sqrt_add_two hnpos]

theorem xiRight_shift_ne_one_of_mem_landauBall
    {δ η r : ℝ} (hη : 0 < η) (hrη : r ≤ η / 2)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|)
    {s : ℂ} (hs : s ∈ Metric.ball (((1 + δ : ℝ) : ℂ)) r)
    (q : XiRightZeroCopy) :
    s - xiRightCenteredZero q ≠ 1 := by
  have hsball : ‖s - (((1 + δ : ℝ) : ℂ))‖ < r := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hs)
  have hsim : |s.im| < r := by
    have himnorm : |(s - (((1 + δ : ℝ) : ℂ))).im| ≤
        ‖s - (((1 + δ : ℝ) : ℂ))‖ := Complex.abs_im_le_norm _
    have himzero : (s - (((1 + δ : ℝ) : ℂ))).im = s.im := by simp
    rw [himzero] at himnorm
    exact lt_of_le_of_lt himnorm hsball
  intro heq
  have himeq : s.im = (xiRightCenteredZero q).im := by
    have h := congrArg Complex.im heq
    simp only [Complex.sub_im, Complex.one_im] at h
    linarith
  rw [himeq] at hsim
  have hq := hordinate q
  linarith

/-- The locally normal shifted-zeta sum is holomorphic on the Landau ball. -/
theorem differentiableOn_xiRectangularShiftedZetaSeries_landauBall
    (L : ℝ) {δ η r : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    DifferentiableOn ℂ (xiRectangularShiftedZetaSeries L)
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) := by
  apply SummableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball
    (summableLocallyUniformlyOn_xiRectangularShiftedZeta_ball L
      hδ0 hδhalf hη hr hrquarter hrη hupper hordinate)
  intro q s hs
  have hne := xiRight_shift_ne_one_of_mem_landauBall
    hη hrη hordinate hs q
  exact ((differentiableAt_riemannZeta hne).comp s
    (differentiableAt_id.sub_const (xiRightCenteredZero q))).const_mul
      (xiRectangularRightCoefficient L q)

theorem analyticOnNhd_xiRectangularShiftedZetaSeries_landauBall
    (L : ℝ) {δ η r : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    AnalyticOnNhd ℂ (xiRectangularShiftedZetaSeries L)
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) :=
  (differentiableOn_xiRectangularShiftedZetaSeries_landauBall L
    hδ0 hδhalf hη hr hrquarter hrη hupper hordinate).analyticOnNhd
      Metric.isOpen_ball

/-- The actual right-half Xi divisor has a nontrivial pole-free ball at its
real transverse boundary on which the rectangular shifted-zeta carrier is
holomorphic. -/
theorem exists_analyticOnNhd_xiRectangularShiftedZetaSeries_actualLandauBall
    (L : ℝ) (hne : Nonempty XiRightZeroCopy) :
    ∃ η r : ℝ, 0 < η ∧ 0 < r ∧ r ≤ 1 / 4 ∧ r ≤ η / 2 ∧
      AnalyticOnNhd ℂ (xiRectangularShiftedZetaSeries L)
        (Metric.ball (((1 + xiRightTransverseSup : ℝ) : ℂ)) r) := by
  obtain ⟨η, hη, hordinate⟩ :=
    exists_xiRightCenteredZero_abs_im_lower_bound
  let r : ℝ := min (1 / 8) (η / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (by norm_num) (div_pos hη (by norm_num))
  have hrquarter : r ≤ 1 / 4 := by
    exact (min_le_left _ _).trans (by norm_num)
  have hrη : r ≤ η / 2 := by
    exact (min_le_right _ _).trans (by linarith)
  refine ⟨η, r, hη, hr, hrquarter, hrη, ?_⟩
  exact analyticOnNhd_xiRectangularShiftedZetaSeries_landauBall L
    (xiRightTransverseSup_pos hne).le
    (xiRightTransverseSup_le_half hne)
    hη hr hrquarter hrη
    (fun q => xiRightCenteredZero_re_le_sup q) hordinate

/-- At logarithmic aperture, a right-half Xi dominant edge is exactly its
rectangular coefficient times the Dirichlet monomial `n^w`. -/
theorem xiRectangularTwoEdgeDominant_logSample_of_right
    {L : ℝ} {n : ℕ} (hn : 1 ≤ n) (q : XiRightZeroCopy) :
    xiRectangularTwoEdgeDominant L (Real.log n / 2)
        (xiSpectralPoint q.1) =
      xiRectangularRightCoefficient L q *
        (n : ℂ) ^ (xiRightCenteredZero q) := by
  exact rectangularTwoEdgeDominant_logSample_of_pos hn q.2

end

end RHTower
