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

/-- Uniform normal convergence of a weighted shifted-zeta series on a
pole-free real ball at a common transverse upper bound. -/
theorem summableLocallyUniformlyOn_xiWeightedShiftedZeta_ball
    (D : XiRightCoefficientSystem) {δ η r : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    SummableLocallyUniformlyOn
      (fun q : XiRightZeroCopy => fun s : ℂ =>
        D.coefficient q * riemannZeta (s - xiRightCenteredZero q))
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) := by
  let C0 : ℝ := D.normBound
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
          ‖x‖ = ‖(x - (((1 + δ : ℝ) : ℂ))) +
              (((1 + δ : ℝ) : ℂ))‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
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
      have himlower : η / 2 ≤ |x.im - w.im| := by linarith
      have himnorm : |((x - w) - 1).im| ≤ ‖(x - w) - 1‖ :=
        Complex.abs_im_le_norm _
      have himid : ((x - w) - 1).im = x.im - w.im := by
        simp [Complex.sub_im]
      rw [himid] at himnorm
      exact le_trans himlower himnorm
    have hzeta : ‖riemannZeta (x - w)‖ ≤
        Dz * Real.sqrt (‖x - w‖ + 2) :=
      norm_riemannZeta_le_sqrt_norm_add_two hreal (half_pos hη) hpole
    have hnpos : 0 < ‖xiSpectralPoint q.1‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
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
    have hcoeff := D.norm_le q
    have hprod :
        ‖D.coefficient q‖ * ‖riemannZeta (x - w)‖ ≤
          (C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := by
      apply mul_le_mul
      · simpa only [C0] using hcoeff
      · calc
          ‖riemannZeta (x - w)‖ ≤ Dz * Real.sqrt (‖x - w‖ + 2) := hzeta
          _ ≤ Dz * (Real.sqrt ‖w‖ + 2) := by
            exact mul_le_mul_of_nonneg_left hsqrtarg (by
              dsimp only [Dz]
              positivity)
          _ = Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2) := by rw [hwnorm]
      · positivity
      · dsimp only [C0]
        exact div_nonneg D.normBound_nonneg (sq_nonneg _)
    rw [norm_mul]
    calc
      ‖D.coefficient q‖ * ‖riemannZeta (x - w)‖ ≤
          (C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Dz * (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := hprod
      _ = C0 * Dz *
          ((1 / ‖xiSpectralPoint q.1‖ ^ 2) *
            (Real.sqrt ‖xiSpectralPoint q.1‖ + 2)) := by ring
      _ = C0 * Dz *
          (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖) +
            2 * (1 / ‖xiSpectralPoint q.1‖ ^ 2)) := by
        rw [inv_sq_mul_sqrt_add_two hnpos]

theorem differentiableOn_xiWeightedShiftedZetaSeries_landauBall
    (D : XiRightCoefficientSystem) {δ η r : ℝ}
    (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    DifferentiableOn ℂ (xiWeightedShiftedZetaSeries D)
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) := by
  apply SummableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball
    (summableLocallyUniformlyOn_xiWeightedShiftedZeta_ball D
      hδ0 hδhalf hη hr hrquarter hrη hupper hordinate)
  intro q s hs
  have hne := xiRight_shift_ne_one_of_mem_landauBall
    hη hrη hordinate hs q
  exact ((differentiableAt_riemannZeta hne).comp s
    (differentiableAt_id.sub_const (xiRightCenteredZero q))).const_mul
      (D.coefficient q)

theorem differentiableOn_xiWeightedLandauContinuation_landauBall
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) {δ η r : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hη : 0 < η) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hrη : r ≤ η / 2)
    (hrδ : r ≤ δ / 2)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hordinate : ∀ q : XiRightZeroCopy, η ≤ |(xiRightCenteredZero q).im|) :
    DifferentiableOn ℂ (xiWeightedLandauContinuation D C N)
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) := by
  have hshift := differentiableOn_xiWeightedShiftedZetaSeries_landauBall D
    hδ.le hδhalf hη hr hrquarter hrη hupper hordinate
  intro s hs
  have hsne : s ≠ 1 := by
    intro heq
    subst s
    have hball : ‖(1 : ℂ) - (((1 + δ : ℝ) : ℂ))‖ < r := by
      simpa [dist_eq_norm] using (Metric.mem_ball.mp hs)
    have hnorm : ‖(1 : ℂ) - (((1 + δ : ℝ) : ℂ))‖ = δ := by
      rw [show (1 : ℂ) - (((1 + δ : ℝ) : ℂ)) = ((-δ : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
    rw [hnorm] at hball
    linarith
  have hzeta : DifferentiableWithinAt ℂ riemannZeta
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) s :=
    (differentiableAt_riemannZeta hsne).differentiableWithinAt
  have hprefix : DifferentiableWithinAt ℂ
      (xiWeightedLandauPrefixSeries D C N)
      (Metric.ball (((1 + δ : ℝ) : ℂ)) r) s :=
    (differentiable_xiWeightedLandauPrefixSeries D C N s).differentiableWithinAt
  simpa only [xiWeightedLandauContinuation] using
    (((hshift s hs).const_mul (2 : ℂ)).add
      (hzeta.const_mul (C : ℂ))).sub hprefix

/-- An eventual lower bound forces convergence strictly left of the actual
transverse boundary for every admissible coefficient system. -/
theorem exists_xiWeightedLandauCoefficient_summable_left_of_boundary
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    (hne : Nonempty XiRightZeroCopy)
    (hlower : ∀ n, N ≤ n →
      0 ≤ xiWeightedRightDirichletCoefficientReal D n + C) :
    ∃ σ : ℝ, 1 < σ ∧ σ < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ))
        (σ : ℂ) := by
  let δ : ℝ := xiRightTransverseSup
  have hδ : 0 < δ := xiRightTransverseSup_pos hne
  have hδhalf : δ ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ δ :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨η, hη, hordinate⟩ := exists_xiRightCenteredZero_abs_im_lower_bound
  let r : ℝ := min (min (1 / 8) (η / 4)) (δ / 2)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (lt_min (by norm_num) (div_pos hη (by norm_num)))
      (div_pos hδ (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hrη : r ≤ η / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrδ : r ≤ δ / 2 := min_le_right _ _
  have hcont := differentiableOn_xiWeightedLandauContinuation_landauBall
    D C N hδ hδhalf hη hr hrquarter hrη hrδ hupper hordinate
  let σ₁ : ℝ := 1 + δ + r / 8
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  let σ : ℝ := 1 + δ - r / 8
  have hh : 0 < h := by dsimp only [h]; positivity
  have hsum : LSeriesSummable
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ))
      (σ₁ : ℂ) := by
    apply xiWeightedLandauCoefficient_LSeriesSummable D C N hδ.le hupper
    dsimp only [σ₁]
    simp only [Complex.ofReal_re]
    linarith
  have hGd : DifferentiableOn ℂ (xiWeightedLandauContinuation D C N)
      (Metric.closedBall ((σ₁ + h : ℝ) : ℂ) (R : ℝ)) := by
    apply hcont.mono
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hcenter :
        ‖(((σ₁ + h : ℝ) : ℂ) - (((1 + δ : ℝ) : ℂ)))‖ = r / 4 := by
      have heq : (((σ₁ + h : ℝ) : ℂ) - (((1 + δ : ℝ) : ℂ))) =
          ((r / 4 : ℝ) : ℂ) := by
        dsimp only [σ₁, h]
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      positivity
    calc
      ‖z - (((1 + δ : ℝ) : ℂ))‖ ≤
          ‖z - (((σ₁ + h : ℝ) : ℂ))‖ +
            ‖(((σ₁ + h : ℝ) : ℂ) - (((1 + δ : ℝ) : ℂ)))‖ := by
        have := norm_add_le
          (z - (((σ₁ + h : ℝ) : ℂ)))
          ((((σ₁ + h : ℝ) : ℂ)) - (((1 + δ : ℝ) : ℂ)))
        simpa only [sub_add_sub_cancel] using this
      _ ≤ r / 2 + r / 4 := by
        rw [hcenter]
        exact add_le_add hz le_rfl
      _ < r := by linarith
  have hagree : ∀ s : ℂ, σ₁ < s.re →
      xiWeightedLandauContinuation D C N s =
        LSeries (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) s := by
    intro s hsright
    symm
    apply LSeries_xiWeightedLandauCoefficient_eq_continuation
      D C N hδ.le hupper
    dsimp only [σ₁] at hsright
    linarith
  have hnonneg := xiWeightedLandauCoefficient_nonneg hlower
  have hineq : σ₁ + h - (R : ℝ) < σ := by
    change σ₁ + h - r / 2 < σ
    dsimp only [σ₁, h, σ]
    linarith
  have htransfer := landau_local_summability_transfer
    (a := xiWeightedLandauCoefficient D C N)
    hnonneg hh hsum (R := R) (G := xiWeightedLandauContinuation D C N)
    hGd hagree hineq
  refine ⟨σ, ?_, ?_, htransfer⟩
  · dsimp only [σ]
    linarith
  · dsimp only [σ, δ]
    linarith

/-- One coefficient-weighted Xi-cancelled shifted-zeta term. -/
def xiWeightedCancelledTerm
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  D.coefficient q * xiShiftedZetaCancelledTerm q s

def xiWeightedCancelledSeries
    (D : XiRightCoefficientSystem) (s : ℂ) : ℂ :=
  ∑' q : XiRightZeroCopy, xiWeightedCancelledTerm D q s

/-- Reciprocal-square coefficient control makes the Xi-cancelled carrier
locally normally convergent on `Re s > 1`. -/
theorem summableLocallyUniformlyOn_xiWeightedCancelledTerm_rightOne
    (D : XiRightCoefficientSystem) :
    SummableLocallyUniformlyOn
      (fun q : XiRightZeroCopy => xiWeightedCancelledTerm D q)
      {s : ℂ | 1 < s.re} := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (xi_differentiable.continuous.comp
      (continuous_id.sub continuous_const)).continuousOn
  let C0 : ℝ := D.normBound
  let R0 : ℝ := max R 0
  let M0 : ℝ := max M 0
  let S : ℝ := 2 * (R0 + 2)
  have hR0 : 0 ≤ R0 := le_max_right _ _
  have hM0 : 0 ≤ M0 := le_max_right _ _
  have hS : 0 < S := by dsimp only [S]; positivity
  have hthree : Summable (fun q : XiRightZeroCopy =>
      1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) :=
    xiSpectralPoint_inv_three_halves_summable.subtype _
  refine ⟨fun q : XiRightZeroCopy =>
      (10 * C0 * M0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)),
    hthree.mul_left (10 * C0 * M0), ?_⟩
  have hbase : Summable (fun q : XiRightZeroCopy =>
      1 / ‖xiSpectralPoint q.1‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.subtype _
  have hlarge : ∀ᶠ q : XiRightZeroCopy in Filter.cofinite,
      S ≤ ‖xiSpectralPoint q.1‖ := by
    have htend := hbase.tendsto_cofinite_zero
    have hlt : ∀ᶠ q : XiRightZeroCopy in Filter.cofinite,
        1 / ‖xiSpectralPoint q.1‖ ^ 2 < 1 / S ^ 2 :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with q hq
    have hqpos : 0 < ‖xiSpectralPoint q.1‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
    have hsq : S ^ 2 < ‖xiSpectralPoint q.1‖ ^ 2 :=
      lt_of_one_div_lt_one_div (pow_pos hqpos 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  filter_upwards [hlarge] with q hqLarge
  intro s hs
  have hsright : 1 < s.re := hKsub hs
  have hsNorm : ‖s‖ ≤ R0 := (hR s hs).trans (le_max_left _ _)
  have hxiNorm : ‖xi (s - 1 / 2)‖ ≤ M0 :=
    (hM s hs).trans (le_max_left _ _)
  let w : ℂ := xiRightCenteredZero q
  have hwNorm : ‖w‖ = ‖xiSpectralPoint q.1‖ := by
    simp [w, xiRightCenteredZero]
  have hwLarge : S ≤ ‖w‖ := by simpa only [hwNorm] using hqLarge
  have hshiftRe : 1 / 2 ≤ (s - w).re := by
    rw [Complex.sub_re]
    have hwre := abs_xiRightCenteredZero_re_lt_half q
    dsimp only [w]
    linarith [abs_lt.mp hwre]
  have hsOneNorm : ‖s - 1‖ ≤ R0 + 1 := by
    calc
      ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ + 1 := by norm_num
      _ ≤ R0 + 1 := by linarith
  have hsep : 1 ≤ ‖(s - w) - 1‖ := by
    have hrev : ‖w‖ - ‖s - 1‖ ≤ ‖w - (s - 1)‖ := norm_sub_norm_le _ _
    have hcoord : ‖w - (s - 1)‖ = ‖(s - w) - 1‖ := by
      rw [show w - (s - 1) = -((s - w) - 1) by ring, norm_neg]
    rw [hcoord] at hrev
    dsimp only [S] at hwLarge
    linarith
  have hnotPole : s ≠ xiRightShiftedPole q := by
    intro heq
    have : (s - w) - 1 = 0 := by
      rw [heq, xiRightShiftedPole]
      dsimp only [w]
      ring
    rw [this, norm_zero] at hsep
    norm_num at hsep
  have hzeta := norm_riemannZeta_le_sqrt_norm_add_two_half
    hshiftRe (by norm_num : (0 : ℝ) < 1) hsep
  have harg : ‖s - w‖ + 2 ≤ 4 * ‖w‖ := by
    have hsub : ‖s - w‖ ≤ ‖s‖ + ‖w‖ := norm_sub_le _ _
    dsimp only [S] at hwLarge
    linarith
  have hsqrt : Real.sqrt (‖s - w‖ + 2) ≤ 2 * Real.sqrt ‖w‖ :=
    sqrt_le_two_mul_sqrt_rectangular (norm_nonneg w) (by positivity) harg
  have hcoeff := D.norm_le q
  rw [xiWeightedCancelledTerm, xiShiftedZetaCancelledTerm,
    Function.update_of_ne hnotPole, norm_mul, norm_mul]
  have hzeta' : ‖riemannZeta (s - w)‖ ≤ 10 * Real.sqrt ‖w‖ := by
    calc
      ‖riemannZeta (s - w)‖ ≤
          (2 + 1 / (1 : ℝ) + 2) * Real.sqrt (‖s - w‖ + 2) := hzeta
      _ ≤ 5 * (2 * Real.sqrt ‖w‖) := by
        norm_num only [div_one, OfNat.ofNat]
        gcongr
      _ = 10 * Real.sqrt ‖w‖ := by ring
  calc
    ‖D.coefficient q‖ *
        (‖xi (s - 1 / 2)‖ * ‖riemannZeta (s - w)‖) ≤
      ((C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
        (10 * Real.sqrt ‖w‖)) * ‖xi (s - 1 / 2)‖ := by
          calc
            ‖D.coefficient q‖ *
                (‖xi (s - 1 / 2)‖ * ‖riemannZeta (s - w)‖) =
              (‖D.coefficient q‖ * ‖riemannZeta (s - w)‖) *
                ‖xi (s - 1 / 2)‖ := by ring
            _ ≤ ((C0 / ‖xiSpectralPoint q.1‖ ^ 2) *
                (10 * Real.sqrt ‖w‖)) * ‖xi (s - 1 / 2)‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              apply mul_le_mul hcoeff hzeta' (norm_nonneg _)
              exact div_nonneg D.normBound_nonneg (sq_nonneg _)
    _ = (10 * C0) *
        ((1 / ‖xiSpectralPoint q.1‖ ^ 2) *
          Real.sqrt ‖xiSpectralPoint q.1‖) * ‖xi (s - 1 / 2)‖ := by
      rw [hwNorm]
      ring
    _ = (10 * C0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) *
          ‖xi (s - 1 / 2)‖ := by
      rw [inv_sq_mul_sqrt_rectangular
        (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1))]
    _ ≤ (10 * C0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) * M0 := by
      apply mul_le_mul_of_nonneg_left hxiNorm
      dsimp only [C0]
      exact mul_nonneg
        (mul_nonneg (by norm_num) D.normBound_nonneg)
        (by positivity)
    _ = (10 * C0 * M0) *
        (1 / (‖xiSpectralPoint q.1‖ * Real.sqrt ‖xiSpectralPoint q.1‖)) := by ring

theorem differentiableOn_xiWeightedCancelledSeries_rightOne
    (D : XiRightCoefficientSystem) :
    DifferentiableOn ℂ (xiWeightedCancelledSeries D) {s : ℂ | 1 < s.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re)
    (summableLocallyUniformlyOn_xiWeightedCancelledTerm_rightOne D)
  intro q s hs
  exact (differentiable_xiShiftedZetaCancelledTerm q s).const_mul
    (D.coefficient q)

theorem xiWeightedShiftedZetaSeries_summable_of_re_gt_transverse
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    Summable (fun q : XiRightZeroCopy =>
      D.coefficient q * riemannZeta (s - xiRightCenteredZero q)) := by
  let ε : ℝ := s.re - (1 + δ)
  have hε : 0 < ε := by dsimp only [ε]; linarith
  apply Summable.of_norm_bounded
    ((xiRightCoefficientSystem_summable D).norm.mul_right (1 + 1 / ε))
  intro q
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply norm_riemannZeta_le hε
  rw [Complex.sub_re]
  have := hupper q
  dsimp only [ε]
  linarith

theorem xiWeightedCancelledSeries_eq_xi_mul_shiftedZeta
    (D : XiRightCoefficientSystem) {δ : ℝ}
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    xiWeightedCancelledSeries D s =
      xi (s - 1 / 2) * xiWeightedShiftedZetaSeries D s := by
  have hsum := xiWeightedShiftedZetaSeries_summable_of_re_gt_transverse
    D hupper hs
  rw [xiWeightedCancelledSeries, xiWeightedShiftedZetaSeries, ← tsum_mul_left]
  apply tsum_congr
  intro q
  have hne : s ≠ xiRightShiftedPole q := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [xiRightShiftedPole, Complex.add_re] at hre
    have := hupper q
    simp only [Complex.one_re] at hre
    linarith
  rw [xiWeightedCancelledTerm, xiShiftedZetaCancelledTerm,
    Function.update_of_ne hne]
  ring

def xiWeightedSameSupportSeries
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  ∑' r : XiRightSupportFiber q, xiWeightedCancelledTerm D r.1 s

def xiWeightedOtherSupportSeries
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  ∑' r : XiRightOtherSupport q, xiWeightedCancelledTerm D r.1 s

theorem xiWeightedCancelledTerm_order
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    analyticOrderAt (xiWeightedCancelledTerm D q) (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => D.coefficient q)
      (xiRightShiftedPole q) := analyticAt_const
  have ht : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q)
      (xiRightShiftedPole q) :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _
  rw [show xiWeightedCancelledTerm D q =
      (fun _ : ℂ => D.coefficient q) * xiShiftedZetaCancelledTerm q by rfl,
    analyticOrderAt_mul hc ht,
    hc.analyticOrderAt_eq_zero.mpr (D.nonzero q),
    xiShiftedZetaCancelledTerm_order, zero_add]

theorem xiWeightedSameSupportSeries_eq_card_mul
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    xiWeightedSameSupportSeries D q =
      fun s => (Fintype.card (XiRightSupportFiber q) : ℂ) *
        xiWeightedCancelledTerm D q s := by
  funext s
  rw [xiWeightedSameSupportSeries, tsum_fintype]
  calc
    ∑ r : XiRightSupportFiber q, xiWeightedCancelledTerm D r.1 s =
        ∑ _r : XiRightSupportFiber q, xiWeightedCancelledTerm D q s := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [xiWeightedCancelledTerm,
        D.support_eq r.2,
        xiShiftedZetaCancelledTerm_eq_of_support_eq r.2]
      rfl
    _ = (Fintype.card (XiRightSupportFiber q) : ℂ) *
        xiWeightedCancelledTerm D q s := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem xiWeightedSameSupportSeries_order
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    analyticOrderAt (xiWeightedSameSupportSeries D q)
        (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  rw [xiWeightedSameSupportSeries_eq_card_mul]
  letI : Nonempty (XiRightSupportFiber q) := ⟨⟨q, rfl⟩⟩
  have hcard : (Fintype.card (XiRightSupportFiber q) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : AnalyticAt ℂ
      (fun _ : ℂ => (Fintype.card (XiRightSupportFiber q) : ℂ))
      (xiRightShiftedPole q) := analyticAt_const
  have ht : AnalyticAt ℂ (xiWeightedCancelledTerm D q)
      (xiRightShiftedPole q) :=
    analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _)
  rw [show (fun s => (Fintype.card (XiRightSupportFiber q) : ℂ) *
      xiWeightedCancelledTerm D q s) =
      (fun _ : ℂ => (Fintype.card (XiRightSupportFiber q) : ℂ)) *
        xiWeightedCancelledTerm D q by rfl,
    analyticOrderAt_mul hc ht,
    hc.analyticOrderAt_eq_zero.mpr hcard,
    xiWeightedCancelledTerm_order D q, zero_add]

theorem xiWeightedOtherSupportSeries_order_ge
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    (xiRightMultiplicity q : ℕ∞) ≤
      analyticOrderAt (xiWeightedOtherSupportSeries D q)
        (xiRightShiftedPole q) := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := by
    change 1 < (xiRightShiftedPole q).re
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hnormal : SummableLocallyUniformlyOn
      (fun r : XiRightOtherSupport q => xiWeightedCancelledTerm D r.1) U :=
    SummableLocallyUniformlyOn.comp_injective_local hU
      (summableLocallyUniformlyOn_xiWeightedCancelledTerm_rightOne D)
      Subtype.val_injective
  apply natCast_le_analyticOrderAt_tsum_of_summableLocallyUniformlyOn
    hU hpoleU hnormal
  · intro r s hs
    exact analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm r.1 |>.analyticAt s)
  · intro r
    have hterm : AnalyticAt ℂ (xiWeightedCancelledTerm D r.1)
        (xiRightShiftedPole q) := analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm r.1 |>.analyticAt _)
    rw [natCast_le_analyticOrderAt hterm]
    obtain ⟨u, hu, hev⟩ :=
      exists_xiShiftedZetaCancelledTerm_off_support_factorization
        q r.1 r.2.symm
    refine ⟨fun s => D.coefficient r.1 * u s,
      analyticAt_const.mul hu, ?_⟩
    filter_upwards [hev] with s hs
    rw [xiWeightedCancelledTerm, hs]
    simp only [smul_eq_mul]
    ring

theorem xiWeightedCancelledSeries_eventuallyEq_same_add_other
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    xiWeightedCancelledSeries D =ᶠ[nhds (xiRightShiftedPole q)]
      xiWeightedSameSupportSeries D q + xiWeightedOtherSupportSeries D q := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := by
    change 1 < (xiRightShiftedPole q).re
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  filter_upwards [hU.mem_nhds hpoleU] with s hs
  have hsum : Summable (fun r : XiRightZeroCopy =>
      xiWeightedCancelledTerm D r s) :=
    (summableLocallyUniformlyOn_xiWeightedCancelledTerm_rightOne D).summable hs
  let P : Set XiRightZeroCopy := {r | r.1.1 = q.1.1}
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl P
  change (∑' r : XiRightZeroCopy, xiWeightedCancelledTerm D r s) =
    (∑' r : XiRightSupportFiber q, xiWeightedCancelledTerm D r.1 s) +
      ∑' r : XiRightOtherSupport q, xiWeightedCancelledTerm D r.1 s
  simpa only [P, Set.mem_setOf_eq, Set.mem_compl_iff] using hsplit.symm

theorem xiWeightedCancelledSeries_order
    (D : XiRightCoefficientSystem) (q : XiRightZeroCopy) :
    analyticOrderAt (xiWeightedCancelledSeries D) (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  have heq := xiWeightedCancelledSeries_eventuallyEq_same_add_other D q
  rw [analyticOrderAt_congr heq]
  have hsame := xiWeightedSameSupportSeries_order D q
  have hother := xiWeightedOtherSupportSeries_order_ge D q
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  have hnat : xiRightMultiplicity q - 1 < xiRightMultiplicity q :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have henat : (xiRightMultiplicity q - 1 : ℕ∞) <
      (xiRightMultiplicity q : ℕ∞) := by exact_mod_cast hnat
  have hlt : analyticOrderAt (xiWeightedSameSupportSeries D q)
      (xiRightShiftedPole q) <
        analyticOrderAt (xiWeightedOtherSupportSeries D q)
          (xiRightShiftedPole q) := by
    rw [hsame]
    exact henat.trans_le hother
  rw [analyticOrderAt_add_eq_left_of_lt hlt, hsame]

/-- Analytic shifted-zeta continuation reconstructed from the Landau tail. -/
def xiWeightedLandauAnalyticShiftedSeries
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  (LSeries (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) s -
    C * riemannZeta s + xiWeightedLandauPrefixSeries D C N s) / 2

theorem differentiableOn_xiWeightedLandauAnalyticShiftedSeries
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {σ : ℝ} (hσ : 1 < σ)
    (hsum : LSeriesSummable
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) (σ : ℂ)) :
    DifferentiableOn ℂ (xiWeightedLandauAnalyticShiftedSeries D C N)
      {s : ℂ | σ < s.re} := by
  intro s hs
  change σ < s.re at hs
  have habs := hsum.abscissaOfAbsConv_le
  have habslt : LSeries.abscissaOfAbsConv
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) < s.re :=
    lt_of_le_of_lt habs (by exact_mod_cast hs)
  have hL := (LSeries_hasDerivAt habslt).differentiableAt
  have hsone : s ≠ 1 := by
    intro heq
    subst s
    simp only [Complex.one_re] at hs
    linarith
  have hzeta := differentiableAt_riemannZeta hsone
  have hprefix := differentiable_xiWeightedLandauPrefixSeries D C N s
  simpa only [xiWeightedLandauAnalyticShiftedSeries] using
    (((hL.sub (hzeta.const_mul (C : ℂ))).add hprefix).div_const (2 : ℂ)).differentiableWithinAt

theorem xiWeightedLandauAnalyticShiftedSeries_eq_shiftedZeta
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    {s : ℂ} (hs : 1 + δ < s.re) :
    xiWeightedLandauAnalyticShiftedSeries D C N s =
      xiWeightedShiftedZetaSeries D s := by
  have hL := LSeries_xiWeightedLandauCoefficient_eq_continuation
    D C N hδ0 hupper hs
  rw [xiWeightedLandauAnalyticShiftedSeries, hL,
    xiWeightedLandauContinuation]
  ring

theorem xiWeightedCancelledSeries_eq_xi_mul_landauContinuation
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ σ : ℝ} (hσ : 1 < σ) (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hsum : LSeriesSummable
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) (σ : ℂ)) :
    Set.EqOn (xiWeightedCancelledSeries D)
      (fun s => xi (s - 1 / 2) *
        xiWeightedLandauAnalyticShiftedSeries D C N s)
      {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
  have hcancelDiff : DifferentiableOn ℂ (xiWeightedCancelledSeries D) U :=
    (differentiableOn_xiWeightedCancelledSeries_rightOne D).mono (by
      intro s hs
      change σ < s.re at hs
      change 1 < s.re
      linarith)
  have hlandauDiff := differentiableOn_xiWeightedLandauAnalyticShiftedSeries
    D C N hσ hsum
  have hprodDiff : DifferentiableOn ℂ
      (fun s => xi (s - 1 / 2) *
        xiWeightedLandauAnalyticShiftedSeries D C N s) U := by
    intro s hs
    exact ((xi_differentiable (s - 1 / 2)).comp s
      (differentiableAt_id.sub_const (1 / 2))).differentiableWithinAt.mul
        (hlandauDiff s hs)
  let x0 : ℝ := max σ (1 + δ) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change σ < x0
    dsimp only [x0]
    linarith [le_max_left σ (1 + δ)]
  have hz0right : 1 + δ < z0.re := by
    change 1 + δ < x0
    dsimp only [x0]
    linarith [le_max_right σ (1 + δ)]
  have hrightOpen : IsOpen {s : ℂ | 1 + δ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hevent : xiWeightedCancelledSeries D =ᶠ[nhds z0]
      fun s => xi (s - 1 / 2) *
        xiWeightedLandauAnalyticShiftedSeries D C N s := by
    filter_upwards [hrightOpen.mem_nhds hz0right] with s hsright
    rw [xiWeightedCancelledSeries_eq_xi_mul_shiftedZeta D hupper hsright,
      xiWeightedLandauAnalyticShiftedSeries_eq_shiftedZeta
        D C N hδ0 hupper hsright]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hcancelDiff.analyticOnNhd hUopen)
    (hprodDiff.analyticOnNhd hUopen) hUpre hz0U hevent

/-- Any Landau summability boundary lies to the right of every genuine
weighted Xi pole. -/
theorem xiRightShiftedPole_re_le_of_weighted_landau_summable
    (D : XiRightCoefficientSystem) (C : ℝ) (N : ℕ)
    {δ σ : ℝ} (hσ : 1 < σ) (hδ0 : 0 ≤ δ)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ δ)
    (hsum : LSeriesSummable
      (fun n => ((xiWeightedLandauCoefficient D C N n : ℝ) : ℂ)) (σ : ℂ))
    (q : XiRightZeroCopy) :
    (xiRightShiftedPole q).re ≤ σ := by
  by_contra hnot
  have hpole : σ < (xiRightShiftedPole q).re := lt_of_not_ge hnot
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := hpole
  have heqOn := xiWeightedCancelledSeries_eq_xi_mul_landauContinuation
    D C N hσ hδ0 hupper hsum
  have hevent : xiWeightedCancelledSeries D =ᶠ[nhds (xiRightShiftedPole q)]
      fun s => xi (s - 1 / 2) *
        xiWeightedLandauAnalyticShiftedSeries D C N s := by
    filter_upwards [hU.mem_nhds hpoleU] with s hs
    exact heqOn hs
  have horders := analyticOrderAt_congr hevent
  have hlandauDiff := differentiableOn_xiWeightedLandauAnalyticShiftedSeries
    D C N hσ hsum
  have hlandauAn : AnalyticAt ℂ
      (xiWeightedLandauAnalyticShiftedSeries D C N)
      (xiRightShiftedPole q) :=
    (hlandauDiff.analyticOnNhd hU) _ hpoleU
  have hxiAn : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2))
      (xiRightShiftedPole q) :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hprod : (xiRightMultiplicity q : ℕ∞) ≤
      analyticOrderAt
        (fun s => xi (s - 1 / 2) *
          xiWeightedLandauAnalyticShiftedSeries D C N s)
        (xiRightShiftedPole q) := by
    rw [show (fun s => xi (s - 1 / 2) *
        xiWeightedLandauAnalyticShiftedSeries D C N s) =
      (fun s => xi (s - 1 / 2)) *
        xiWeightedLandauAnalyticShiftedSeries D C N by rfl,
      analyticOrderAt_mul hxiAn hlandauAn, xi_shifted_half_order]
    exact le_add_right le_rfl
  rw [xiWeightedCancelledSeries_order D q] at horders
  rw [← horders] at hprod
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  have hltNat : xiRightMultiplicity q - 1 < xiRightMultiplicity q :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have hlt : (xiRightMultiplicity q - 1 : ℕ∞) <
      (xiRightMultiplicity q : ℕ∞) := by exact_mod_cast hltNat
  exact (not_lt_of_ge hprod) hlt

theorem no_eventual_lower_bound_xiWeightedRightDirichletCoefficientReal
    (D : XiRightCoefficientSystem) (hne : Nonempty XiRightZeroCopy) :
    ¬ ∃ C : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      0 ≤ xiWeightedRightDirichletCoefficientReal D n + C := by
  rintro ⟨C, N, hlower⟩
  obtain ⟨σ, hσ, hσSup, hsum⟩ :=
    exists_xiWeightedLandauCoefficient_summable_left_of_boundary
      D C N hne hlower
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ σ :=
    xiRightShiftedPole_re_le_of_weighted_landau_summable D C N hσ
      (xiRightTransverseSup_pos hne).le
      (fun q => xiRightCenteredZero_re_le_sup q) hsum
  have hsupBound : xiRightTransverseSup ≤ σ - 1 :=
    xiRightTransverseSup_le_of_shiftedPole_re_le hne hpoleBound
  linarith

theorem xiWeightedRightDirichletCoefficientReal_cofinally_unbounded_below
    (D : XiRightCoefficientSystem) (hne : Nonempty XiRightZeroCopy) :
    ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      xiWeightedRightDirichletCoefficientReal D n < B := by
  intro B N
  by_contra hnot
  push Not at hnot
  apply no_eventual_lower_bound_xiWeightedRightDirichletCoefficientReal D hne
  refine ⟨-B, N, ?_⟩
  intro n hn
  have hBn := hnot n hn
  linarith

end

end RHTower
