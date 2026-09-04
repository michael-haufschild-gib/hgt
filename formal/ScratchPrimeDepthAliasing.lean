import GaloisForLFunctions.RHTower.TwoPrimeKummerClockSeparation
import GaloisForLFunctions.HTGeometry.ModularCubicProjectionTransgression
import Mathlib.LinearAlgebra.Matrix.Kronecker

open Complex Matrix
open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev TwoSiteChannelIndex := Fin 2 × Fin 2

def twoSiteBlockDiagonal {K : Type*} [Zero K] [DecidableEq (Fin 2)]
    (P Q : Matrix (Fin 2) (Fin 2) K) :
    Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  fun i j => if h : i.1 = j.1 then if i.1 = 0 then P i.2 j.2 else Q i.2 j.2 else 0

def twoSiteScalarDensity {K : Type*} [CommRing K]
    (d g e : K) : Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  modularTwoBlockDensity d g g e ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

def twoSiteScalarDensityInv {K : Type*} [Field K]
    (d g e : K) : Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  modularTwoBlockDensityInv d g g e ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

theorem twoSite_modularHolonomy_retained_block
    {K : Type*} [Field K]
    (d g e : K) (hdet : d * e - g ^ 2 ≠ 0)
    (P Q Pi Qi : Matrix (Fin 2) (Fin 2) K)
    (hPPi : P * Pi = 1) (r s : Fin 2) :
    (twoSiteScalarDensityInv d g e * twoSiteBlockDiagonal P Q *
        twoSiteScalarDensity d g e * twoSiteBlockDiagonal Pi Qi)
        ((0, r) : TwoSiteChannelIndex) ((0, s) : TwoSiteChannelIndex) =
      ((d * e) • (1 : Matrix (Fin 2) (Fin 2) K) - g ^ 2 • (Q * Pi)) r s /
        (d * e - g ^ 2) := by
  have hPPi_rs := congrArg (fun M => M r s) hPPi
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hPPi_rs
  have hdet' : e * d - g * g ≠ 0 := by
    simpa [pow_two, mul_comm] using hdet
  fin_cases r <;> fin_cases s <;>
    simp [twoSiteScalarDensityInv, twoSiteScalarDensity, twoSiteBlockDiagonal,
      modularTwoBlockDensityInv, modularTwoBlockDensity, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] at hPPi_rs ⊢ <;>
    ring_nf at hPPi_rs ⊢ <;>
    linear_combination (e * d * (e * d - g ^ 2)⁻¹) * hPPi_rs

theorem twoSite_modularHolonomy_retained_block_eq_one_add
    {K : Type*} [Field K]
    (d g e : K) (hdet : d * e - g ^ 2 ≠ 0)
    (P Q Pi Qi : Matrix (Fin 2) (Fin 2) K)
    (hPPi : P * Pi = 1) (r s : Fin 2) :
    (twoSiteScalarDensityInv d g e * twoSiteBlockDiagonal P Q *
        twoSiteScalarDensity d g e * twoSiteBlockDiagonal Pi Qi)
        ((0, r) : TwoSiteChannelIndex) ((0, s) : TwoSiteChannelIndex) =
      ((1 : Matrix (Fin 2) (Fin 2) K) +
        (g ^ 2 / (d * e - g ^ 2)) •
          ((1 : Matrix (Fin 2) (Fin 2) K) - Q * Pi)) r s := by
  rw [twoSite_modularHolonomy_retained_block d g e hdet P Q Pi Qi hPPi r s]
  have hden : d * e - g ^ 2 ≠ 0 := hdet
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hden] <;>
    ring

theorem cubicCauchyDenominator_factor (x y : ℝ) :
    (x + y) ^ 6 - 64 * x ^ 3 * y ^ 3 =
      (x - y) ^ 2 *
        ((x + y) ^ 4 + 4 * x * y * (x + y) ^ 2 + 16 * x ^ 2 * y ^ 2) := by
  ring

theorem cubicCauchyDenominator_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < (x + y) ^ 6 - 64 * x ^ 3 * y ^ 3 := by
  rw [cubicCauchyDenominator_factor]
  have hdiff : 0 < (x - y) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hsum : 0 < x + y := by positivity
  have hQ : 0 < (x + y) ^ 4 + 4 * x * y * (x + y) ^ 2 + 16 * x ^ 2 * y ^ 2 := by
    positivity
  positivity

theorem cubicCauchyGramCapacity_eq
    {A B x y : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    let d := A ^ 2 * 2 / (2 * x) ^ 3
    let e := B ^ 2 * 2 / (2 * y) ^ 3
    let g := A * B * 2 / (x + y) ^ 3
    g ^ 2 / (d * e - g ^ 2) =
      64 * x ^ 3 * y ^ 3 /
        ((x + y) ^ 6 - 64 * x ^ 3 * y ^ 3) := by
  dsimp
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  have hsum0 : x + y ≠ 0 := (add_pos hx hy).ne'
  have hden0 : (x + y) ^ 6 - 64 * x ^ 3 * y ^ 3 ≠ 0 :=
    (cubicCauchyDenominator_pos hx hy hxy).ne'
  field_simp [hA, hB, hx0, hy0, hsum0, hden0]
  ring

def cubicCauchyRelativeCapacity (u : ℝ) : ℝ :=
  (1 - u ^ 2) ^ 3 / (1 - (1 - u ^ 2) ^ 3)

theorem cubicCauchyRelativeCapacity_gt
    {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (husmall : u < 1 / (8 * (M + 1))) :
    M < cubicCauchyRelativeCapacity u := by
  have hM1 : 1 ≤ M + 1 := by linarith
  have hdenM : 0 < 8 * (M + 1) := by positivity
  have hscaled : u * (8 * (M + 1)) < 1 :=
    (lt_div_iff₀ hdenM).mp (by simpa using husmall)
  have hu_lt : u < 1 := by nlinarith
  have hu2pos : 0 < u ^ 2 := sq_pos_of_pos hu
  have hu2lt : u ^ 2 < 1 := by nlinarith
  have hbasepos : 0 < 1 - u ^ 2 := by linarith
  have hbaselt : 1 - u ^ 2 < 1 := by linarith
  have hdenpos : 0 < 1 - (1 - u ^ 2) ^ 3 := by
    nlinarith [mul_self_lt_mul_self (by linarith : 0 ≤ 1 - u ^ 2) hbaselt,
      mul_pos hbasepos hbasepos]
  have hnum : 1 / 2 < (1 - u ^ 2) ^ 3 := by
    have hu_eighth : u < 1 / 8 := by nlinarith
    nlinarith [sq_nonneg (u ^ 2), sq_nonneg (1 - u ^ 2)]
  have hden_le : 1 - (1 - u ^ 2) ^ 3 ≤ 3 * u ^ 2 := by
    nlinarith [sq_nonneg (u ^ 2), mul_nonneg hu2pos.le (by nlinarith : 0 ≤ 3 - u ^ 2)]
  have hMu : 6 * M * u ^ 2 < 1 := by
    have hscaled0 : 0 ≤ u * (8 * (M + 1)) := by positivity
    have hsquare : (u * (8 * (M + 1))) ^ 2 < 1 := by
      nlinarith [mul_self_lt_mul_self hscaled0 hscaled]
    nlinarith [sq_nonneg M]
  have hMfrac : M < (1 / 2) / (3 * u ^ 2) := by
    rw [lt_div_iff₀ (by positivity : 0 < 3 * u ^ 2)]
    nlinarith
  rw [cubicCauchyRelativeCapacity]
  refine lt_of_lt_of_le hMfrac ?_
  exact div_le_div₀ (by positivity) hnum.le hdenpos hden_le

theorem cubicCauchyRelativeCapacity_abs_sub_div_add_eq
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    cubicCauchyRelativeCapacity (|x - y| / (x + y)) =
      64 * x ^ 3 * y ^ 3 /
        ((x + y) ^ 6 - 64 * x ^ 3 * y ^ 3) := by
  have hsum0 : x + y ≠ 0 := (add_pos hx hy).ne'
  have hden0 : (x + y) ^ 6 - 64 * x ^ 3 * y ^ 3 ≠ 0 :=
    (cubicCauchyDenominator_pos hx hy hxy).ne'
  rw [cubicCauchyRelativeCapacity]
  rw [div_pow, sq_abs]
  field_simp [hsum0, hden0]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

theorem log_two_le_kummerFreq_of_coordinates_nonneg
    (z : ℤ × ℤ) (hz : z ≠ (0, 0)) (h1 : 0 ≤ z.1) (h2 : 0 ≤ z.2) :
    Real.log 2 ≤ kummerFreq z := by
  have hL3pos : 0 < Real.log 3 := lt_of_lt_of_le log_two_pos log_two_lt_log_three
  rcases eq_or_lt_of_le h1 with h10 | h1pos
  · have h2pos : 1 ≤ z.2 := by
      rcases eq_or_lt_of_le h2 with h20 | h2pos
      · exact absurd (Prod.ext h10.symm h20.symm) hz
      · omega
    have h2R : (1 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast h2pos
    rw [kummerFreq, ← h10]
    have hm : Real.log 2 ≤ (z.2 : ℝ) * Real.log 3 := by
      calc
        Real.log 2 ≤ Real.log 3 := log_two_lt_log_three
        _ = 1 * Real.log 3 := (one_mul _).symm
        _ ≤ (z.2 : ℝ) * Real.log 3 :=
          mul_le_mul_of_nonneg_right h2R hL3pos.le
    simpa using hm
  · have h1R : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1pos
    rw [kummerFreq]
    have ha : Real.log 2 ≤ (z.1 : ℝ) * Real.log 2 := by
      calc
        Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
        _ ≤ (z.1 : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1R log_two_pos.le
    have hb : 0 ≤ (z.2 : ℝ) * Real.log 3 :=
      mul_nonneg (by exact_mod_cast h2) hL3pos.le
    linarith

theorem log_two_le_abs_kummerFreq_of_mul_nonneg
    (z : ℤ × ℤ) (hz : z ≠ (0, 0)) (hsign : 0 ≤ z.1 * z.2) :
    Real.log 2 ≤ |kummerFreq z| := by
  rcases Int.mul_nonneg_iff.mp hsign with h | h
  · rcases h with ⟨h1, h2⟩
    have hfreq := log_two_le_kummerFreq_of_coordinates_nonneg z hz h1 h2
    rw [abs_of_nonneg (le_trans log_two_pos.le hfreq)]
    exact hfreq
  · rcases h with ⟨h1, h2⟩
    have hzneg : (-z.1, -z.2) ≠ (0, 0) := by
      intro hc
      apply hz
      have hc1 := congrArg Prod.fst hc
      have hc2 := congrArg Prod.snd hc
      simp only at hc1 hc2
      exact Prod.ext (by omega) (by omega)
    have hrec := log_two_le_kummerFreq_of_coordinates_nonneg
      (-z.1, -z.2) hzneg (by omega) (by omega)
    have hfreqneg : kummerFreq (-z.1, -z.2) = -kummerFreq z := by
      simp [kummerFreq]
      ring
    rw [hfreqneg] at hrec
    rw [abs_of_nonpos (by linarith [log_two_pos])]
    linarith

theorem exists_two_three_positive_depth_collision {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      0 < |(m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3| ∧
      |(m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3| < epsilon := by
  let delta := min epsilon (Real.log 2)
  have hdelta : 0 < delta := lt_min hepsilon log_two_pos
  obtain ⟨z, hz, hpos, hsmall⟩ := exists_small_kummerFreq hdelta
  have hltlog : |kummerFreq z| < Real.log 2 :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hsign : z.1 * z.2 < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ z.1 * z.2 := le_of_not_gt hnot
    exact (not_lt_of_ge (log_two_le_abs_kummerFreq_of_mul_nonneg z hz hnonneg)) hltlog
  have heps : |kummerFreq z| < epsilon :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  rcases Int.mul_neg_iff.mp hsign with h | h
  · rcases h with ⟨h1, h2⟩
    let m := z.1.toNat
    let n := (-z.2).toNat
    have hm : 0 < m := by omega
    have hn : 0 < n := by omega
    have hmcast : (m : ℝ) = (z.1 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h1.le
    have hncast : (n : ℝ) = -(z.2 : ℝ) := by
      have hz2 : ((n : ℕ) : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz2
    refine ⟨m, n, hm, hn, ?_, ?_⟩
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq]
      exact hpos
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq]
      exact heps
  · rcases h with ⟨h1, h2⟩
    let m := (-z.1).toNat
    let n := z.2.toNat
    have hm : 0 < m := by omega
    have hn : 0 < n := by omega
    have hmcast : (m : ℝ) = -(z.1 : ℝ) := by
      have hz1 : ((m : ℕ) : ℤ) = -z.1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz1
    have hncast : (n : ℝ) = (z.2 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h2.le
    refine ⟨m, n, hm, hn, ?_, ?_⟩
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = -kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq, abs_neg]
      exact hpos
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = -kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq, abs_neg]
      exact heps

/-- The normalized two-site cubic-Cauchy Gram capacity of literal 2/3 prime-depth pairs is
unbounded. The producer is scale aliasing between distinct prime labels, not positivity. -/
theorem exists_two_three_primeDepth_cubicCauchyCapacity_gt
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      M < 64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3 /
        ((((m : ℝ) * Real.log 2) + ((n : ℝ) * Real.log 3)) ^ 6 -
          64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3) := by
  let epsilon := Real.log 2 / (4 * (M + 1))
  have hM1 : 0 < M + 1 := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨m, n, hm, hn, hdiffpos, hdiffsmall⟩ :=
    exists_two_three_positive_depth_collision hepsilon
  let x := (m : ℝ) * Real.log 2
  let y := (n : ℝ) * Real.log 3
  let u := |x - y| / (x + y)
  change 0 < |x - y| at hdiffpos
  change |x - y| < epsilon at hdiffsmall
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < x := mul_pos (by exact_mod_cast hm) log_two_pos
  have hlog3 : 0 < Real.log 3 := lt_of_lt_of_le log_two_pos log_two_lt_log_three
  have hy : 0 < y := mul_pos (by exact_mod_cast hn) hlog3
  have hsum : 0 < x + y := add_pos hx hy
  have hsumlower : 2 * Real.log 2 ≤ x + y := by
    dsimp [x, y]
    have hxlow : Real.log 2 ≤ (m : ℝ) * Real.log 2 := by
      nlinarith
    have hylow : Real.log 2 ≤ (n : ℝ) * Real.log 3 := by
      have : Real.log 3 ≤ (n : ℝ) * Real.log 3 := by nlinarith
      exact log_two_lt_log_three.trans this
    linarith
  have hxy : x ≠ y := by
    intro h
    simp [h] at hdiffpos
  have hu : 0 < u := div_pos hdiffpos hsum
  have hcoeffpos : 0 < 8 * (M + 1) := by positivity
  have htarget : epsilon ≤ (1 / (8 * (M + 1))) * (x + y) := by
    dsimp [epsilon]
    rw [div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    field_simp [hM1.ne']
    nlinarith
  have husmall : u < 1 / (8 * (M + 1)) := by
    change |x - y| / (x + y) < 1 / (8 * (M + 1))
    rw [div_lt_iff₀ hsum]
    exact hdiffsmall.trans_le htarget
  have hcap := cubicCauchyRelativeCapacity_gt hM hu husmall
  refine ⟨m, n, hm, hn, ?_⟩
  change M < 64 * x ^ 3 * y ^ 3 / ((x + y) ^ 6 - 64 * x ^ 3 * y ^ 3)
  rwa [← cubicCauchyRelativeCapacity_abs_sub_div_add_eq hx hy hxy]

end GaloisForLFunctions.RHTower
