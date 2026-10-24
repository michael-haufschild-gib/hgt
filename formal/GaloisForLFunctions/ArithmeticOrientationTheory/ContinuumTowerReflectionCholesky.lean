import GaloisForLFunctions.ArithmeticOrientationTheory.TheTowerOddSideIsACholeskyEnergyMinusTheMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Reflected Cholesky modes of a continuum prime tower

A half-line profile decomposes into cells of length `L`. Its same-side
correlations have a Cholesky decomposition on each cell. Reflected
correlations pair the zeroth mode at `θ` with the mode at `L - θ`.
Keeping that reflection gives a positive decomposition of the complete
ratio-minus-product tower after adding one diagonal mass.
-/

open Finset MeasureTheory Set Polynomial

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-- Weighted tails along the logarithmic fibre through `θ`. -/
def continuumTowerTail (F : ℝ → ℝ) (r L : ℝ) (N j : ℕ) (θ : ℝ) : ℝ :=
  kmsTail r (fun i => F (θ + (i : ℝ) * L)) N j

/-- Diagonal half-line mass through the last occupied cell. -/
def continuumTowerMass (F : ℝ → ℝ) (L : ℝ) (N : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * L, F x ^ 2

/-- Same-side correlations at all lags meeting the support. -/
def continuumTowerRatio (F : ℝ → ℝ) (r L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, r ^ k *
    ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * L, F x * F (x + (k : ℝ) * L)

/-- Reflected correlations at all lags meeting both positive half-line supports. -/
def continuumTowerCrossing (F : ℝ → ℝ) (r L : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (2 * N + 1), r ^ k *
    ∫ x in (0 : ℝ)..(k : ℝ) * L, F x * F ((k : ℝ) * L - x)

/-- A finite interval splits exactly into translated cells. -/
theorem integral_eq_sum_translated_cells {f : ℝ → ℝ} (hf : Continuous f)
    (L : ℝ) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ) * L, f x) =
      ∑ i ∈ range N, ∫ θ in (0 : ℝ)..L, f (θ + (i : ℝ) * L) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← ih]
    have hshift := intervalIntegral.integral_comp_add_right f ((N : ℝ) * L)
      (a := 0) (b := L)
    have he : L + (N : ℝ) * L = ((N + 1 : ℕ) : ℝ) * L := by
      push_cast
      ring
    rw [zero_add, he] at hshift
    rw [hshift]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm

private theorem sum_Icc_one_eq (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range N, f (k + 1) := by
  have h : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

/-- The finite mixed Cauchy product keeps the two reflected fibres separate. -/
theorem sum_mul_eq_sum_cauchy {u v : ℕ → ℝ} {N : ℕ}
    (hu : ∀ i, N < i → u i = 0) (hv : ∀ i, N < i → v i = 0) :
    (∑ i ∈ range (N + 1), u i) * (∑ i ∈ range (N + 1), v i) =
      ∑ k ∈ range (2 * N + 1), ∑ i ∈ range (k + 1), u i * v (k - i) := by
  have hdeg : (genPoly u N * genPoly v N).natDegree < 2 * N + 1 :=
    Nat.lt_succ_of_le (natDegree_mul_le.trans
      (by have hu' := natDegree_genPoly_le u N
          have hv' := natDegree_genPoly_le v N
          omega))
  rw [← eval_one_genPoly, ← eval_one_genPoly, ← eval_mul, eval_eq_sum_range' hdeg]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_congr rfl fun i _ => by rw [coeff_genPoly hu, coeff_genPoly hv]

private theorem cell_vanishes {F : ℝ → ℝ} {L θ : ℝ} {N i : ℕ}
    (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (hF : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0)
    (hi : N < i) : F (θ + (i : ℝ) * L) = 0 := by
  apply hF
  have hn : ((N + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_right hn hL
  linarith

theorem continuous_continuumTowerTail {F : ℝ → ℝ} (hF : Continuous F)
    (r L : ℝ) (N j : ℕ) : Continuous (continuumTowerTail F r L N j) := by
  unfold continuumTowerTail kmsTail
  fun_prop

theorem continuumTowerMass_eq_cells {F : ℝ → ℝ} (hF : Continuous F) (L : ℝ) (N : ℕ) :
    continuumTowerMass F L N =
      ∫ θ in (0 : ℝ)..L, ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) ^ 2 := by
  rw [continuumTowerMass, integral_eq_sum_translated_cells
    (f := fun x => F x ^ 2) (hF.pow 2) L (N + 1)]
  exact (intervalIntegral.integral_finsetSum fun i _ =>
    ((hF.comp (continuous_id.add continuous_const)).pow 2).intervalIntegrable _ _).symm

theorem continuumTowerRatio_eq_cells {F : ℝ → ℝ} (hF : Continuous F)
    (r L : ℝ) (N : ℕ) :
    continuumTowerRatio F r L N =
      ∫ θ in (0 : ℝ)..L, ∑ k ∈ Icc 1 N, r ^ k *
        ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L) := by
  have hc (k : ℕ) : Continuous (fun θ => r ^ k *
      ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L)) := by
    fun_prop
  rw [continuumTowerRatio, intervalIntegral.integral_finsetSum
    (fun k _ => (hc k).intervalIntegrable _ _)]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [integral_eq_sum_translated_cells
    (f := fun x => F x * F (x + (k : ℝ) * L)) (by fun_prop) L (N + 1),
    intervalIntegral.integral_finsetSum
      (f := fun (i : ℕ) (θ : ℝ) => F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L))
      (fun i _ => (show Continuous (fun θ =>
        F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L)) by fun_prop).intervalIntegrable _ _)]
  refine sum_congr rfl fun i _ => intervalIntegral.integral_congr fun θ _ => ?_
  congr 2
  push_cast
  ring

theorem continuumTowerCrossing_eq_cells {F : ℝ → ℝ} (hF : Continuous F)
    (r L : ℝ) (N : ℕ) :
    continuumTowerCrossing F r L N =
      ∫ θ in (0 : ℝ)..L, ∑ k ∈ range (2 * N + 1), r ^ (k + 1) *
        ∑ i ∈ range (k + 1), F (θ + (i : ℝ) * L) *
          F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L)) := by
  have hc (k : ℕ) : Continuous (fun θ => r ^ (k + 1) *
      ∑ i ∈ range (k + 1), F (θ + (i : ℝ) * L) *
        F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L))) := by
    fun_prop
  rw [continuumTowerCrossing, sum_Icc_one_eq,
    intervalIntegral.integral_finsetSum (fun k _ => (hc k).intervalIntegrable _ _)]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [integral_eq_sum_translated_cells
    (f := fun x => F x * F (((k + 1 : ℕ) : ℝ) * L - x)) (by fun_prop) L (k + 1),
    intervalIntegral.integral_finsetSum
      (f := fun (i : ℕ) (θ : ℝ) => F (θ + (i : ℝ) * L) *
        F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L)))
      (fun i _ => (show Continuous (fun θ => F (θ + (i : ℝ) * L) *
        F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L))) by fun_prop).intervalIntegrable _ _)]

/-- The reflected crossing pairs the two complementary fibres, before integration. -/
theorem reflected_cell_cauchy {F : ℝ → ℝ} {r L θ : ℝ} {N : ℕ}
    (hL : 0 ≤ L) (hθ : θ ∈ Icc (0 : ℝ) L)
    (hF : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0) :
    (∑ k ∈ range (2 * N + 1), r ^ (k + 1) *
      ∑ i ∈ range (k + 1),
        F (θ + (i : ℝ) * L) * F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L))) =
      r * continuumTowerTail F r L N 0 θ * continuumTowerTail F r L N 0 (L - θ) := by
  have hu : ∀ i, N < i → r ^ i * F (θ + (i : ℝ) * L) = 0 := by
    intro i hi
    rw [cell_vanishes hL hθ.1 hF hi, mul_zero]
  have hv : ∀ i, N < i → r ^ i * F (L - θ + (i : ℝ) * L) = 0 := by
    intro i hi
    rw [cell_vanishes hL (sub_nonneg.mpr hθ.2) hF hi, mul_zero]
  have hprod := sum_mul_eq_sum_cauchy hu hv
  have hterm (k : ℕ) (i : ℕ) (hi : i ∈ range (k + 1)) :
      r ^ (k + 1) *
          (F (θ + (i : ℝ) * L) * F (((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L))) =
        r * ((r ^ i * F (θ + (i : ℝ) * L)) *
          (r ^ (k - i) * F (L - θ + ((k - i : ℕ) : ℝ) * L))) := by
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hx : ((k + 1 : ℕ) : ℝ) * L - (θ + (i : ℝ) * L) =
        L - θ + ((k - i : ℕ) : ℝ) * L := by
      rw [Nat.cast_sub hik, Nat.cast_add, Nat.cast_one]
      ring
    have hp : r ^ k = r ^ i * r ^ (k - i) := by
      rw [← pow_add, show i + (k - i) = k by omega]
    rw [hx, pow_succ', hp]
    ring
  calc
    _ = r * ∑ k ∈ range (2 * N + 1), ∑ i ∈ range (k + 1),
          (r ^ i * F (θ + (i : ℝ) * L)) *
            (r ^ (k - i) * F (L - θ + ((k - i : ℕ) : ℝ) * L)) := by
      simp only [mul_sum]
      exact sum_congr rfl fun k _ => sum_congr rfl fun i hi => hterm k i hi
    _ = r * ((∑ i ∈ range (N + 1), r ^ i * F (θ + (i : ℝ) * L)) *
          ∑ i ∈ range (N + 1), r ^ i * F (L - θ + (i : ℝ) * L)) := by rw [hprod]
    _ = _ := by
      simp only [continuumTowerTail, kmsTail, Nat.sub_zero, ← range_eq_Ico]
      ring

/-- The full continuum tower crossing is a reflected pairing of the zeroth tail. -/
theorem continuumTowerCrossing_eq_reflected_pairing {F : ℝ → ℝ} (hF : Continuous F)
    {r L : ℝ} {N : ℕ} (hL : 0 ≤ L)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0) :
    continuumTowerCrossing F r L N = r *
      ∫ θ in (0 : ℝ)..L,
        continuumTowerTail F r L N 0 θ * continuumTowerTail F r L N 0 (L - θ) := by
  rw [continuumTowerCrossing_eq_cells hF, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le hL] at hθ
  simpa only [mul_assoc] using reflected_cell_cauchy hL hθ hsupport

/-- The same-side tower is the integral of the fibrewise Cholesky identity. -/
theorem continuumTowerMass_add_twice_ratio {F : ℝ → ℝ} (hF : Continuous F)
    {r L : ℝ} {N : ℕ} (hL : 0 ≤ L)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0) :
    continuumTowerMass F L N + 2 * continuumTowerRatio F r L N =
      (∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 θ ^ 2) +
        (1 - r ^ 2) * ∑ j ∈ range N,
          ∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N (j + 1) θ ^ 2 := by
  have hm : Continuous (fun θ => ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) ^ 2) := by
    fun_prop
  have hr : Continuous (fun θ => ∑ k ∈ Icc 1 N, r ^ k *
      ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L)) := by
    fun_prop
  have h2r : Continuous (fun θ => 2 * ∑ k ∈ Icc 1 N, r ^ k *
      ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L)) :=
    continuous_const.mul hr
  have ht (j : ℕ) : Continuous (fun θ => continuumTowerTail F r L N j θ ^ 2) :=
    (continuous_continuumTowerTail hF r L N j).pow 2
  have hsum : Continuous (fun θ => ∑ j ∈ range N, continuumTowerTail F r L N (j + 1) θ ^ 2) :=
    continuous_finsetSum (range N) (fun j _ => ht (j + 1))
  have hweight : Continuous (fun θ => (1 - r ^ 2) *
      ∑ j ∈ range N, continuumTowerTail F r L N (j + 1) θ ^ 2) :=
    continuous_const.mul hsum
  calc
    _ = ∫ θ in (0 : ℝ)..L,
        (∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) ^ 2) +
          2 * ∑ k ∈ Icc 1 N, r ^ k *
            ∑ i ∈ range (N + 1), F (θ + (i : ℝ) * L) * F (θ + ((i + k : ℕ) : ℝ) * L) := by
      rw [intervalIntegral.integral_add (hm.intervalIntegrable _ _)
        (h2r.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
        ← continuumTowerMass_eq_cells hF, ← continuumTowerRatio_eq_cells hF]
    _ = ∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 θ ^ 2 +
        (1 - r ^ 2) * ∑ j ∈ range N, continuumTowerTail F r L N (j + 1) θ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le hL] at hθ
      exact kms_cholesky r (fun i hi => cell_vanishes hL hθ.1 hsupport hi) le_rfl
    _ = _ := by
      rw [intervalIntegral.integral_add ((ht 0).intervalIntegrable _ _)
        (hweight.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun j _ => (ht (j + 1)).intervalIntegrable _ _)]

/-- The complete continuum tower retains a reflected zeroth mode and positive higher tails. -/
theorem continuumTower_reflection_cholesky {F : ℝ → ℝ} (hF : Continuous F)
    {r L : ℝ} {N : ℕ} (hL : 0 ≤ L)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0) :
    continuumTowerMass F L N + 2 * continuumTowerRatio F r L N -
        continuumTowerCrossing F r L N =
      (1 - r) * (∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 θ ^ 2) +
        (r / 2) * (∫ θ in (0 : ℝ)..L,
          (continuumTowerTail F r L N 0 θ - continuumTowerTail F r L N 0 (L - θ)) ^ 2) +
        (1 - r ^ 2) * ∑ j ∈ range N,
          ∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N (j + 1) θ ^ 2 := by
  have hu := continuous_continuumTowerTail hF r L N 0
  have hv : Continuous (fun θ => continuumTowerTail F r L N 0 (L - θ)) :=
    hu.comp (continuous_const.sub continuous_id)
  have hu2 : Continuous (fun θ => continuumTowerTail F r L N 0 θ ^ 2) := hu.pow 2
  have hv2 : Continuous (fun θ => continuumTowerTail F r L N 0 (L - θ) ^ 2) := hv.pow 2
  have hs : Continuous (fun θ => continuumTowerTail F r L N 0 θ ^ 2 +
      continuumTowerTail F r L N 0 (L - θ) ^ 2) := hu2.add hv2
  have hp : Continuous (fun θ => 2 *
      (continuumTowerTail F r L N 0 θ * continuumTowerTail F r L N 0 (L - θ))) :=
    continuous_const.mul (hu.mul hv)
  have href : (∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 (L - θ) ^ 2) =
      ∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 θ ^ 2 := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left (fun θ => continuumTowerTail F r L N 0 θ ^ 2)
        L (a := 0) (b := L)
  have hexpand : (∫ θ in (0 : ℝ)..L,
      (continuumTowerTail F r L N 0 θ - continuumTowerTail F r L N 0 (L - θ)) ^ 2) =
      2 * (∫ θ in (0 : ℝ)..L, continuumTowerTail F r L N 0 θ ^ 2) -
        2 * ∫ θ in (0 : ℝ)..L,
          continuumTowerTail F r L N 0 θ * continuumTowerTail F r L N 0 (L - θ) := by
    calc
      _ = ∫ θ in (0 : ℝ)..L,
          (continuumTowerTail F r L N 0 θ ^ 2 + continuumTowerTail F r L N 0 (L - θ) ^ 2) -
            2 * (continuumTowerTail F r L N 0 θ * continuumTowerTail F r L N 0 (L - θ)) :=
        intervalIntegral.integral_congr fun θ _ => by ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hs.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
          intervalIntegral.integral_add (hu2.intervalIntegrable _ _) (hv2.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, href]
        ring
  rw [continuumTowerMass_add_twice_ratio hF hL hsupport,
    continuumTowerCrossing_eq_reflected_pairing hF hL hsupport, hexpand]
  ring

/-- Adding one diagonal mass pays the entire reflected tower for `0 ≤ r ≤ 1`. -/
theorem continuumTower_compensated_nonneg {F : ℝ → ℝ} (hF : Continuous F)
    {r L : ℝ} {N : ℕ} (hL : 0 ≤ L) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * L ≤ x → F x = 0) :
    0 ≤ continuumTowerMass F L N + 2 * continuumTowerRatio F r L N -
      continuumTowerCrossing F r L N := by
  rw [continuumTower_reflection_cholesky hF hL hsupport]
  have hcoef : 0 ≤ 1 - r ^ 2 := by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (sub_nonneg.mpr hr1) (intervalIntegral.integral_nonneg hL fun θ _ => sq_nonneg _))
      (mul_nonneg (div_nonneg hr0 (by norm_num))
        (intervalIntegral.integral_nonneg hL fun θ _ => sq_nonneg _)))
    (mul_nonneg hcoef (sum_nonneg fun j _ =>
      intervalIntegral.integral_nonneg hL fun θ _ => sq_nonneg _))

/-- The literal von Mangoldt tower of the odd half-line correlation `2R - H`. -/
def continuumPrimeTower (F : ℝ → ℝ) (p N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (2 * N + 1),
    ArithmeticFunction.vonMangoldt (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 * (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
        F x * F (x + (k : ℝ) * Real.log p)) -
        ∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
          F x * F ((k : ℝ) * Real.log p - x))

/-- The prime-power weights and physical correlations identify the continuum tower exactly. -/
theorem continuumPrimeTower_eq {F : ℝ → ℝ} {p N : ℕ} (hp : p.Prime)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * Real.log p ≤ x → F x = 0) :
    continuumPrimeTower F p N = Real.log p *
      (2 * continuumTowerRatio F ((p : ℝ) ^ (-(1 / 2 : ℝ))) (Real.log p) N -
        continuumTowerCrossing F ((p : ℝ) ^ (-(1 / 2 : ℝ))) (Real.log p) N) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hw (k : ℕ) (hk : 1 ≤ k) :
      ArithmeticFunction.vonMangoldt (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
        Real.log p * ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      show (k : ℝ) * -(1 / 2 : ℝ) = -(k : ℝ) / 2 by ring,
      rpow_neg_half_pow hp]
  have hratio : (∑ k ∈ Icc 1 (2 * N + 1), ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k *
      ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
        F x * F (x + (k : ℝ) * Real.log p)) =
      continuumTowerRatio F ((p : ℝ) ^ (-(1 / 2 : ℝ))) (Real.log p) N := by
    unfold continuumTowerRatio
    symm
    apply sum_subset
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hkn
      have hkN : N < k := by
        simp only [Finset.mem_Icc] at hk hkn
        omega
      have hz : (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
          F x * F (x + (k : ℝ) * Real.log p)) = 0 := by
        calc
          _ = ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (mul_nonneg (Nat.cast_nonneg _) hL)] at hx
            change F x * F (x + (k : ℝ) * Real.log p) = 0
            rw [cell_vanishes hL hx.1 hsupport hkN, mul_zero]
          _ = 0 := by simp
      rw [hz, mul_zero]
  calc
    continuumPrimeTower F p N = Real.log p *
        ∑ k ∈ Icc 1 (2 * N + 1),
          (2 * (((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k *
            ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
              F x * F (x + (k : ℝ) * Real.log p)) -
            ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k *
              ∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
                F x * F ((k : ℝ) * Real.log p - x)) := by
      rw [continuumPrimeTower, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [hw k (Finset.mem_Icc.mp hk).1]
      ring
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, hratio]
      rfl

/-- One diagonal mass pays every power of one prime for an arbitrary real profile. -/
theorem continuumPrimeTower_compensated_nonneg {F : ℝ → ℝ} (hF : Continuous F)
    {p N : ℕ} (hp : p.Prime)
    (hsupport : ∀ x, ((N + 1 : ℕ) : ℝ) * Real.log p ≤ x → F x = 0) :
    0 ≤ Real.log p * continuumTowerMass F (Real.log p) N + continuumPrimeTower F p N := by
  have hL : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hr0 : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hr1 : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le) (by norm_num)
  rw [continuumPrimeTower_eq hp hsupport]
  have h := mul_nonneg hL (continuumTower_compensated_nonneg hF hL hr0 hr1 hsupport)
  nlinarith only [h]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
