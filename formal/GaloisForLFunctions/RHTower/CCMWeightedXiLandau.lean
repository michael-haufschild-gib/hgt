import GaloisForLFunctions.RHTower.CCMSmoothProfileDecay
import GaloisForLFunctions.RHTower.CCMShiftedXiGlobalOrder

/-!
# Coefficient-generic Xi shifted-zeta Landau carrier

This module factors the rectangular Landau proof through the exact properties
of its right-Xi coefficient family.  The abstraction is instantiated below by
the squared Laplace amplitudes of a fixed smooth boundary profile.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- Exact data needed from a coefficient on positive-transverse Xi copies. -/
structure XiRightCoefficientSystem where
  coefficient : XiRightZeroCopy → ℂ
  normBound : ℝ
  normBound_nonneg : 0 ≤ normBound
  norm_le : ∀ q, ‖coefficient q‖ ≤ normBound / ‖xiSpectralPoint q.1‖ ^ 2
  conjugate : ∀ q, coefficient (xiRightZeroCopyConjEquiv q) =
    (starRingEnd ℂ) (coefficient q)
  support_eq : ∀ {q r}, q.1.1 = r.1.1 → coefficient q = coefficient r
  nonzero : ∀ q, coefficient q ≠ 0

/-- Squared Laplace amplitudes of a generic smooth profile form an exact
right-Xi coefficient system. -/
def smoothProfileXiRightCoefficientSystem
    {eta L : ℝ} (heta : 0 < eta) (hwindow : eta < L - eta)
    (f : SmoothBoundaryProfile eta L) (hf : f ∈ xiSmoothProfileGenericSet eta L) :
    XiRightCoefficientSystem where
  coefficient q := smoothProfileLaplaceAmplitude f (xiRightCenteredZero q) ^ 2
  normBound := (Real.exp (L / 2) * smoothProfileDerivativeMass f) ^ 2
  normBound_nonneg := sq_nonneg _
  norm_le q := norm_smoothProfileLaplaceAmplitude_sq_xiRight_le
    heta hwindow f q
  conjugate q := by
    rw [xiRightCenteredZero_conj, ← smoothProfileLaplaceAmplitude_conj, map_pow]
  support_eq {q r} hqr := by
    rw [xiRightCenteredZero_eq_of_support_eq hqr]
  nonzero q := pow_ne_zero 2 (hf q)

theorem xiRightCoefficientSystem_summable (D : XiRightCoefficientSystem) :
    Summable D.coefficient := by
  have hbase : Summable (fun q : XiRightZeroCopy =>
      1 / ‖xiSpectralPoint q.1‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.subtype _
  apply Summable.of_norm_bounded (hbase.mul_left D.normBound)
  intro q
  calc
    ‖D.coefficient q‖ ≤ D.normBound / ‖xiSpectralPoint q.1‖ ^ 2 := D.norm_le q
    _ = D.normBound * (1 / ‖xiSpectralPoint q.1‖ ^ 2) := by ring

/-- One weighted positive-transverse Dirichlet monomial. -/
def xiWeightedRightDirichletTerm
    (D : XiRightCoefficientSystem) (n : ℕ) (q : XiRightZeroCopy) : ℂ :=
  D.coefficient q * (n : ℂ) ^ xiRightCenteredZero q

theorem xiWeightedRightDirichletTerm_summable
    (D : XiRightCoefficientSystem) {n : ℕ} (hn : 1 ≤ n) :
    Summable (xiWeightedRightDirichletTerm D n) := by
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Summable.of_norm_bounded
    ((xiRightCoefficientSystem_summable D).norm.mul_right
      ((n : ℝ) ^ (1 / 2 : ℝ)))
  intro q
  rw [xiWeightedRightDirichletTerm, norm_mul,
    Complex.norm_natCast_cpow_of_pos hnpos]
  gcongr
  exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2

theorem xiWeightedRightDirichletTerm_conj
    (D : XiRightCoefficientSystem) (n : ℕ) (q : XiRightZeroCopy) :
    xiWeightedRightDirichletTerm D n (xiRightZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiWeightedRightDirichletTerm D n q) := by
  rw [xiWeightedRightDirichletTerm, xiWeightedRightDirichletTerm,
    D.conjugate, xiRightCenteredZero_conj,
    natCast_cpow_conj_rectangular, map_mul]

/-- Twice the complete positive-transverse weighted exponential sum. -/
def xiWeightedRightDirichletComplex
    (D : XiRightCoefficientSystem) (n : ℕ) : ℂ :=
  2 * ∑' q : XiRightZeroCopy, xiWeightedRightDirichletTerm D n q

theorem star_xiWeightedRightDirichletComplex
    (D : XiRightCoefficientSystem) (n : ℕ) :
    (starRingEnd ℂ) (xiWeightedRightDirichletComplex D n) =
      xiWeightedRightDirichletComplex D n := by
  rw [xiWeightedRightDirichletComplex, map_mul, map_ofNat]
  congr 1
  calc
    (starRingEnd ℂ) (∑' q : XiRightZeroCopy,
        xiWeightedRightDirichletTerm D n q) =
      ∑' q : XiRightZeroCopy,
        (starRingEnd ℂ) (xiWeightedRightDirichletTerm D n q) := by
          exact Complex.conj_tsum _
    _ = ∑' q : XiRightZeroCopy,
        xiWeightedRightDirichletTerm D n (xiRightZeroCopyConjEquiv q) := by
      apply tsum_congr
      intro q
      exact (xiWeightedRightDirichletTerm_conj D n q).symm
    _ = ∑' q : XiRightZeroCopy,
        xiWeightedRightDirichletTerm D n q := by
      simpa only using xiRightZeroCopyConjEquiv.tsum_eq
        (xiWeightedRightDirichletTerm D n)

/-- The associated real ordinary Dirichlet coefficient. -/
def xiWeightedRightDirichletCoefficientReal
    (D : XiRightCoefficientSystem) (n : ℕ) : ℝ :=
  (xiWeightedRightDirichletComplex D n).re

theorem xiWeightedRightDirichletComplex_im_eq_zero
    (D : XiRightCoefficientSystem) (n : ℕ) :
    (xiWeightedRightDirichletComplex D n).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_xiWeightedRightDirichletComplex D n)

theorem ofReal_xiWeightedRightDirichletCoefficientReal
    (D : XiRightCoefficientSystem) (n : ℕ) :
    ((xiWeightedRightDirichletCoefficientReal D n : ℝ) : ℂ) =
      xiWeightedRightDirichletComplex D n := by
  apply Complex.ext
  · rfl
  · simp [xiWeightedRightDirichletComplex_im_eq_zero D n]

def xiRightCoefficientNormSum (D : XiRightCoefficientSystem) : ℝ :=
  ∑' q : XiRightZeroCopy, ‖D.coefficient q‖

theorem norm_xiWeightedRightDirichletComplex_le
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖xiWeightedRightDirichletComplex D n‖ ≤
      2 * xiRightCoefficientNormSum D * (n : ℝ) ^ δ := by
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hterm := xiWeightedRightDirichletTerm_summable D hn
  have hmajor : Summable (fun q : XiRightZeroCopy =>
      ‖D.coefficient q‖ * (n : ℝ) ^ δ) :=
    (xiRightCoefficientSystem_summable D).norm.mul_right ((n : ℝ) ^ δ)
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [xiWeightedRightDirichletComplex, norm_mul, hnorm2]
  calc
    (2 : ℝ) * ‖∑' q : XiRightZeroCopy,
        xiWeightedRightDirichletTerm D n q‖ ≤
      2 * ∑' q : XiRightZeroCopy,
        ‖xiWeightedRightDirichletTerm D n q‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm hterm.norm
    _ ≤ 2 * ∑' q : XiRightZeroCopy,
        (‖D.coefficient q‖ * (n : ℝ) ^ δ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hterm.norm.tsum_le_tsum (fun q => by
          rw [xiWeightedRightDirichletTerm, norm_mul,
            Complex.norm_natCast_cpow_of_pos hnpos]
          gcongr
          exact hupper q) hmajor
    _ = 2 * xiRightCoefficientNormSum D * (n : ℝ) ^ δ := by
      rw [xiRightCoefficientNormSum, tsum_mul_right]
      ring

theorem abs_xiWeightedRightDirichletCoefficientReal_le
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {n : ℕ} (hn : 1 ≤ n) :
    |xiWeightedRightDirichletCoefficientReal D n| ≤
      2 * xiRightCoefficientNormSum D * (n : ℝ) ^ δ :=
  (Complex.abs_re_le_norm (xiWeightedRightDirichletComplex D n)).trans
    (norm_xiWeightedRightDirichletComplex_le D hupper hn)

/-- Tail shift used by the nonnegative Landau argument. -/
def xiWeightedLandauCoefficient
    (D : XiRightCoefficientSystem) (C : ℝ) (N n : ℕ) : ℝ :=
  if N ≤ n then xiWeightedRightDirichletCoefficientReal D n + C else 0

theorem xiWeightedLandauCoefficient_nonneg
    {D : XiRightCoefficientSystem} {C : ℝ} {N : ℕ}
    (hlower : ∀ n, N ≤ n →
      0 ≤ xiWeightedRightDirichletCoefficientReal D n + C) :
    ∀ n, 0 ≤ xiWeightedLandauCoefficient D C N n := by
  intro n
  rw [xiWeightedLandauCoefficient]
  split_ifs with hn
  · exact hlower n hn
  · exact le_rfl

theorem norm_xiWeightedLandauCoefficient_le
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (n : ℕ) (hn : n ≠ 0) :
    ‖((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)‖ ≤
      (2 * xiRightCoefficientNormSum D + |C|) * (n : ℝ) ^ δ := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow hnR hδ0
  rw [Complex.norm_real, Real.norm_eq_abs, xiWeightedLandauCoefficient]
  split_ifs with hN
  · calc
      |xiWeightedRightDirichletCoefficientReal D n + C| ≤
          |xiWeightedRightDirichletCoefficientReal D n| + |C| := abs_add_le _ _
      _ ≤ 2 * xiRightCoefficientNormSum D * (n : ℝ) ^ δ + |C| := by
        gcongr
        exact abs_xiWeightedRightDirichletCoefficientReal_le D hupper hn1
      _ ≤ 2 * xiRightCoefficientNormSum D * (n : ℝ) ^ δ +
          |C| * (n : ℝ) ^ δ := by
        gcongr
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hpow1 (abs_nonneg C))
      _ = (2 * xiRightCoefficientNormSum D + |C|) * (n : ℝ) ^ δ := by ring
  · simp only [abs_zero]
    have hmass0 : 0 ≤ xiRightCoefficientNormSum D :=
      tsum_nonneg fun q => norm_nonneg _
    positivity

theorem xiWeightedLandauCoefficient_LSeriesSummable
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    LSeriesSummable
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + δ) hs
  refine ⟨2 * xiRightCoefficientNormSum D + |C|, fun n hn => ?_⟩
  simpa only [add_sub_cancel_left] using
    norm_xiWeightedLandauCoefficient_le D C N hδ0 hupper n hn

theorem LSeries_xiWeightedRightDirichletTerm_eq
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) {s : ℂ}
    (hs : 1 + (xiRightCenteredZero q).re < s.re) :
    LSeries (fun n => 2 * xiWeightedRightDirichletTerm D n q) s =
      2 * D.coefficient q * riemannZeta (s - xiRightCenteredZero q) := by
  have hsw : 1 < (s - xiRightCenteredZero q).re := by
    rw [Complex.sub_re]
    linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hsw, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [LSeries.term_zero]
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re] at this
      linarith)]
    simp
  · rw [LSeries.term_of_ne_zero hn.ne']
    simp only [xiWeightedRightDirichletTerm]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hpow : (n : ℂ) ^ xiRightCenteredZero q / (n : ℂ) ^ s =
        1 / (n : ℂ) ^ (s - xiRightCenteredZero q) := by
      rw [← Complex.cpow_sub _ _ hn0]
      have hneg : xiRightCenteredZero q - s =
          -(s - xiRightCenteredZero q) := by ring
      rw [hneg, Complex.cpow_neg]
      ring
    calc
      2 * (D.coefficient q * (n : ℂ) ^ xiRightCenteredZero q) /
          (n : ℂ) ^ s =
        2 * D.coefficient q *
          ((n : ℂ) ^ xiRightCenteredZero q / (n : ℂ) ^ s) := by ring
      _ = 2 * D.coefficient q *
          (1 / (n : ℂ) ^ (s - xiRightCenteredZero q)) := by rw [hpow]

theorem summable_prod_LSeriesTerm_xiWeightedRightDirichletTerm
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    Summable (fun qn : XiRightZeroCopy × ℕ =>
      LSeries.term (fun n => 2 * xiWeightedRightDirichletTerm D n qn.1)
        s qn.2) := by
  let p : ℝ := s.re - δ
  have hp : 1 < p := by dsimp only [p]; linarith
  let g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ p
  have hg : Summable g := Real.summable_one_div_nat_rpow.mpr hp
  have hcoeff : Summable (fun q : XiRightZeroCopy =>
      2 * ‖D.coefficient q‖) :=
    (xiRightCoefficientSystem_summable D).norm.mul_left 2
  have hcoeffNorm : Summable (fun q : XiRightZeroCopy =>
      ‖2 * ‖D.coefficient q‖‖) := by
    refine hcoeff.congr fun q => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hgNorm : Summable (fun n => ‖g n‖) := by
    refine hg.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp only [g]
    positivity
  have hmajor : Summable (fun qn : XiRightZeroCopy × ℕ =>
      (2 * ‖D.coefficient qn.1‖) * g qn.2) :=
    summable_mul_of_summable_norm hcoeffNorm hgNorm
  apply Summable.of_norm_bounded hmajor
  rintro ⟨q, n⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [LSeries.term_zero, norm_zero]
    dsimp only [g]
    norm_num only [Nat.cast_zero]
    rw [Real.zero_rpow (by linarith : p ≠ 0), div_zero, mul_zero]
  · have hnRpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnRone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_mul,
      norm_ofNat, xiWeightedRightDirichletTerm, norm_mul,
      Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_natCast_cpow_of_pos hn]
    dsimp only [g, p]
    calc
      2 * (‖D.coefficient q‖ *
          (n : ℝ) ^ (xiRightCenteredZero q).re) / (n : ℝ) ^ s.re =
        2 * ‖D.coefficient q‖ *
          (n : ℝ) ^ ((xiRightCenteredZero q).re - s.re) := by
            rw [Real.rpow_sub hnRpos]
            ring
      _ ≤ 2 * ‖D.coefficient q‖ * (n : ℝ) ^ (δ - s.re) := by
        gcongr
        exact hupper q
      _ = (2 * ‖D.coefficient q‖) *
          (1 / (n : ℝ) ^ (s.re - δ)) := by
        rw [show δ - s.re = -(s.re - δ) by ring,
          Real.rpow_neg hnRpos.le]
        ring

/-- The coefficient-generic shifted-zeta series. -/
def xiWeightedShiftedZetaSeries
    (D : XiRightCoefficientSystem) (s : ℂ) : ℂ :=
  ∑' q : XiRightZeroCopy,
    D.coefficient q * riemannZeta (s - xiRightCenteredZero q)

set_option maxHeartbeats 800000 in
theorem LSeries_xiWeightedRightDirichletComplex_eq_shiftedZeta
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    LSeries (fun n => xiWeightedRightDirichletComplex D n) s =
      2 * xiWeightedShiftedZetaSeries D s := by
  have hdouble :=
    summable_prod_LSeriesTerm_xiWeightedRightDirichletTerm D hupper hs
  have hterm (n : ℕ) :
      LSeries.term (fun n => xiWeightedRightDirichletComplex D n) s n =
        ∑' q : XiRightZeroCopy,
          LSeries.term (fun n => 2 * xiWeightedRightDirichletTerm D n q) s n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
      rw [tsum_zero]
    · rw [LSeries.term_of_ne_zero hn.ne']
      simp only [xiWeightedRightDirichletComplex]
      calc
        (2 * ∑' q : XiRightZeroCopy,
            xiWeightedRightDirichletTerm D n q) / (n : ℂ) ^ s =
          (∑' q : XiRightZeroCopy,
            2 * xiWeightedRightDirichletTerm D n q) / (n : ℂ) ^ s := by
              rw [tsum_mul_left]
        _ = ∑' q : XiRightZeroCopy,
            (2 * xiWeightedRightDirichletTerm D n q) / (n : ℂ) ^ s := by
              rw [tsum_div_const]
        _ = ∑' q : XiRightZeroCopy,
            LSeries.term (fun n => 2 * xiWeightedRightDirichletTerm D n q) s n := by
          apply tsum_congr
          intro q
          rw [LSeries.term_of_ne_zero hn.ne']
  rw [LSeries]
  calc
    (∑' n, LSeries.term
        (fun n => xiWeightedRightDirichletComplex D n) s n) =
      ∑' n, ∑' q : XiRightZeroCopy,
        LSeries.term (fun n => 2 * xiWeightedRightDirichletTerm D n q) s n :=
      tsum_congr hterm
    _ = ∑' q : XiRightZeroCopy, ∑' n,
        LSeries.term (fun n => 2 * xiWeightedRightDirichletTerm D n q) s n :=
      hdouble.tsum_comm
    _ = ∑' q : XiRightZeroCopy,
        (2 * D.coefficient q * riemannZeta (s - xiRightCenteredZero q)) := by
      apply tsum_congr
      intro q
      exact LSeries_xiWeightedRightDirichletTerm_eq D q (by
        have := hupper q
        linarith)
    _ = 2 * xiWeightedShiftedZetaSeries D s := by
      rw [xiWeightedShiftedZetaSeries, ← tsum_mul_left]
      apply tsum_congr
      intro q
      ring

theorem xiWeightedRightDirichletComplex_zero
    (D : XiRightCoefficientSystem) :
    xiWeightedRightDirichletComplex D 0 = 0 := by
  rw [xiWeightedRightDirichletComplex]
  have hterm : ∀ q : XiRightZeroCopy,
      xiWeightedRightDirichletTerm D 0 q = 0 := by
    intro q
    rw [xiWeightedRightDirichletTerm]
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow (xiRightCenteredZero_ne_zero q), mul_zero]
  rw [tsum_congr hterm, tsum_zero, mul_zero]

def xiWeightedLandauPrefixCoefficient
    (D : XiRightCoefficientSystem) (C : ℝ) (N n : ℕ) : ℂ :=
  if n < N then xiWeightedRightDirichletComplex D n + C else 0

theorem ofReal_xiWeightedLandauCoefficient_eq_full_sub_prefix
    (D : XiRightCoefficientSystem) (C : ℝ) (N n : ℕ) :
    ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ) =
      xiWeightedRightDirichletComplex D n + C -
        xiWeightedLandauPrefixCoefficient D C N n := by
  rw [xiWeightedLandauCoefficient, xiWeightedLandauPrefixCoefficient]
  by_cases hN : N ≤ n
  · rw [if_pos hN, if_neg (not_lt.mpr hN), ofReal_add,
      ofReal_xiWeightedRightDirichletCoefficientReal]
    ring
  · have hnN : n < N := Nat.lt_of_not_ge hN
    rw [if_neg hN, if_pos hnN]
    push_cast
    ring

theorem xiWeightedRightDirichletComplex_LSeriesSummable
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    LSeriesSummable (fun n => xiWeightedRightDirichletComplex D n) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1 + δ) hs
  refine ⟨2 * xiRightCoefficientNormSum D, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  simpa only [add_sub_cancel_left] using
    norm_xiWeightedRightDirichletComplex_le D hupper hn1

theorem xiWeightedLandauPrefixCoefficient_LSeriesSummable
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) (s : ℂ) :
    LSeriesSummable (xiWeightedLandauPrefixCoefficient D C N) s := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hNn : N ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hnpos.ne',
      xiWeightedLandauPrefixCoefficient, if_neg (not_lt.mpr hNn), zero_div]

def xiWeightedLandauPrefixSeries
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    LSeries.term (xiWeightedLandauPrefixCoefficient D C N) s n

theorem LSeries_xiWeightedLandauPrefixCoefficient_eq
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) (s : ℂ) :
    LSeries (xiWeightedLandauPrefixCoefficient D C N) s =
      xiWeightedLandauPrefixSeries D C N s := by
  rw [LSeries, xiWeightedLandauPrefixSeries]
  apply tsum_eq_sum
  intro n hn
  have hNn : N ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hnpos.ne',
      xiWeightedLandauPrefixCoefficient, if_neg (not_lt.mpr hNn), zero_div]

theorem differentiable_xiWeightedLandauPrefixSeries
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) :
    Differentiable ℂ (xiWeightedLandauPrefixSeries D C N) := by
  intro s
  change DifferentiableAt ℂ
    (fun z => ∑ n ∈ Finset.range N,
      LSeries.term (xiWeightedLandauPrefixCoefficient D C N) z n) s
  apply DifferentiableAt.fun_sum
  intro n hn
  rcases n.eq_zero_or_pos with rfl | hnpos
  · simpa only [LSeries.term_zero] using
      (differentiableAt_const (c := (0 : ℂ)))
  · simp only [LSeries.term_of_ne_zero hnpos.ne']
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    exact (differentiableAt_const
      (c := xiWeightedLandauPrefixCoefficient D C N n)).div
      (differentiableAt_id.const_cpow (Or.inl hn0))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

def xiWeightedLandauContinuation
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  2 * xiWeightedShiftedZetaSeries D s + C * riemannZeta s -
    xiWeightedLandauPrefixSeries D C N s

set_option maxHeartbeats 800000 in
theorem LSeries_xiWeightedLandauCoefficient_eq_continuation
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    LSeries (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) s =
      xiWeightedLandauContinuation D C N s := by
  have hcomplex := xiWeightedRightDirichletComplex_LSeriesSummable D hupper hs
  have hsone : 1 < s.re := by linarith
  have hconst : LSeriesSummable (fun _n : ℕ => (C : ℂ)) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re
      (m := |C|) (fun n hn => ?_) hsone
    rw [norm_real, Real.norm_eq_abs]
  have hprefix := xiWeightedLandauPrefixCoefficient_LSeriesSummable D C N s
  have hcoeffEq : LSeries
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) s =
      LSeries ((fun n => xiWeightedRightDirichletComplex D n + C) -
        xiWeightedLandauPrefixCoefficient D C N) s := by
    apply LSeries_congr
    intro n hn
    exact ofReal_xiWeightedLandauCoefficient_eq_full_sub_prefix D C N n
  have hfun : (fun n => xiWeightedRightDirichletComplex D n + (C : ℂ)) =
      (fun n => xiWeightedRightDirichletComplex D n) +
        (fun _n : ℕ => (C : ℂ)) := by
    funext n
    rfl
  rw [hcoeffEq, hfun, LSeries_sub (hcomplex.add hconst) hprefix,
    LSeries_add hcomplex hconst,
    LSeries_xiWeightedRightDirichletComplex_eq_shiftedZeta D hupper hs]
  have hconstEq : LSeries (fun _n : ℕ => (C : ℂ)) s =
      C * riemannZeta s := by
    calc
      LSeries (fun _n : ℕ => (C : ℂ)) s =
          LSeries ((C : ℂ) • (1 : ℕ → ℂ)) s := by
        apply LSeries_congr
        intro n hn
        simp
      _ = C * LSeries (1 : ℕ → ℂ) s := LSeries_smul _ _ _
      _ = C * riemannZeta s := by rw [LSeries_one_eq_riemannZeta hsone]
  rw [hconstEq, xiWeightedLandauContinuation,
    LSeries_xiWeightedLandauPrefixCoefficient_eq]

end

end RHTower
