import GaloisForLFunctions.HTGeometry.PrimeDirichletAnalyticTransfer
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Field.GeomSum

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ComplexConjugate
open Filter Set

noncomputable section

/-- Standard finite-matrix positive definiteness for a complex function on the additive real line. -/
def PositiveDefiniteOnReal (f : ℝ → ℂ) : Prop :=
  ∀ (N : ℕ) (t : Fin N → ℝ) (c : Fin N → ℂ),
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ i, ∑ j, star (c i) * f (t j - t i) * c j = (r : ℂ)

/-- The additive character of the real line with a prescribed frequency. -/
def realFourierCharacter (a t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((a * t : ℝ) : ℝ) : ℂ))

theorem realFourierCharacter_sub (a x y : ℝ) :
    realFourierCharacter a (y - x) =
      star (realFourierCharacter a x) * realFourierCharacter a y := by
  change Complex.exp (Complex.I * (((a * (y - x) : ℝ) : ℝ) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * (((a * x : ℝ) : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (((a * y : ℝ) : ℝ) : ℂ))
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring

@[simp]
theorem norm_realFourierCharacter (a t : ℝ) :
    ‖realFourierCharacter a t‖ = 1 := by
  rw [realFourierCharacter]
  have h : Complex.I * ((((a * t : ℝ) : ℝ) : ℂ)) =
      (((a * t : ℝ) : ℂ)) * Complex.I := by ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem realFourierCharacter_freq_sub (a b t : ℝ) :
    star (realFourierCharacter b t) * realFourierCharacter a t =
      realFourierCharacter (a - b) t := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I * (((b * t : ℝ) : ℝ) : ℂ))) *
      Complex.exp (Complex.I * (((a * t : ℝ) : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((((a - b) * t : ℝ) : ℝ) : ℂ))
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  ring

theorem realFourierCharacter_nat_mul (a t : ℝ) (n : ℕ) :
    realFourierCharacter a ((n : ℝ) * t) = realFourierCharacter a t ^ n := by
  rw [realFourierCharacter, realFourierCharacter, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- An absolutely summable atomic Fourier transform. -/
def atomicFourierSeries (w freq : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' n, (w n : ℂ) * realFourierCharacter (freq n) t

private theorem atomicFourierSeries_summable
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|) (t : ℝ) :
    Summable (fun n => (w n : ℂ) * realFourierCharacter (freq n) t) := by
  rw [← summable_norm_iff]
  simpa [realFourierCharacter, norm_mul, Complex.norm_exp, Real.norm_eq_abs] using hw

private def atomicFourierVector {N : ℕ} (freq : ℕ → ℝ)
    (t : Fin N → ℝ) (c : Fin N → ℂ) (n : ℕ) : ℂ :=
  ∑ i, c i * realFourierCharacter (freq n) (t i)

private theorem atomicFourier_quadraticForm
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) :
    (∑ i, ∑ j, star (c i) * atomicFourierSeries w freq (t j - t i) * c j) =
      ∑' n, (w n : ℂ) * star (atomicFourierVector freq t c n) *
        atomicFourierVector freq t c n := by
  let g : Fin N → Fin N → ℕ → ℂ := fun i j n =>
    star (c i) *
      ((w n : ℂ) * realFourierCharacter (freq n) (t j - t i)) * c j
  have hg : ∀ i j, Summable (g i j) := by
    intro i j
    have hs := atomicFourierSeries_summable (freq := freq) hw (t j - t i)
    have hsl := hs.mul_left (star (c i))
    have hslr := hsl.mul_right (c j)
    simpa only [g] using hslr
  calc
    (∑ i, ∑ j, star (c i) * atomicFourierSeries w freq (t j - t i) * c j) =
        ∑ i, ∑ j, ∑' n, g i j n := by
      simp only [atomicFourierSeries, g, tsum_mul_left, tsum_mul_right]
    _ = ∑ i, ∑' n, ∑ j, g i j n := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hg i j)]
    _ = ∑' n, ∑ i, ∑ j, g i j n := by
      have hgi : ∀ i, Summable (fun n => ∑ j, g i j n) := by
        intro i
        exact summable_sum (s := Finset.univ) (fun j _ => hg i j)
      rw [Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hgi i)]
    _ = ∑' n, (w n : ℂ) * star (atomicFourierVector freq t c n) *
        atomicFourierVector freq t c n := by
      apply tsum_congr
      intro n
      simp only [atomicFourierVector, g]
      simp_rw [realFourierCharacter_sub]
      have hstar :
          star (∑ i, c i * realFourierCharacter (freq n) (t i)) =
            ∑ i, star (c i * realFourierCharacter (freq n) (t i)) := by
        change (starRingEnd ℂ) (∑ i, c i * realFourierCharacter (freq n) (t i)) = _
        simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte, starRingEnd_apply] using
          (map_sum (starRingEnd ℂ)
            (fun i => c i * realFourierCharacter (freq n) (t i)) Finset.univ)
      rw [hstar]
      simp only [star_mul, Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem positiveDefinite_atomicFourierSeries_of_nonnegative
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    (hw0 : ∀ n, 0 ≤ w n) :
    PositiveDefiniteOnReal (atomicFourierSeries w freq) := by
  intro N t c
  let C : ℝ := ∑ i, ‖c i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hvec (n : ℕ) : ‖atomicFourierVector freq t c n‖ ≤ C := by
    calc
      ‖atomicFourierVector freq t c n‖ ≤
          ∑ i, ‖c i * realFourierCharacter (freq n) (t i)‖ := by
        exact norm_sum_le Finset.univ _
      _ = C := by
        apply Finset.sum_congr rfl
        intro i _
        simp [realFourierCharacter, Complex.norm_exp]
  let q : ℕ → ℝ := fun n => w n * Complex.normSq (atomicFourierVector freq t c n)
  have hq0 (n : ℕ) : 0 ≤ q n :=
    mul_nonneg (hw0 n) (Complex.normSq_nonneg _)
  have hqle (n : ℕ) : q n ≤ C ^ 2 * |w n| := by
    have hsquare : Complex.normSq (atomicFourierVector freq t c n) ≤ C ^ 2 := by
      rw [← Complex.sq_norm]
      exact (sq_le_sq₀ (norm_nonneg _) hC0).2 (hvec n)
    rw [abs_of_nonneg (hw0 n)]
    exact mul_le_mul_of_nonneg_left hsquare (hw0 n) |>.trans_eq (mul_comm _ _)
  have hqsum : Summable q := by
    apply Summable.of_nonneg_of_le hq0 hqle
    simpa [mul_comm] using hw.mul_right (C ^ 2)
  refine ⟨∑' n, q n, tsum_nonneg hq0, ?_⟩
  rw [atomicFourier_quadraticForm hw]
  have hmap : ((∑' n, q n : ℝ) : ℂ) = ∑' n, (q n : ℂ) := by
    exact Complex.ofRealCLM.map_tsum hqsum
  rw [hmap]
  apply tsum_congr
  intro n
  rw [mul_assoc]
  change (w n : ℂ) *
      ((starRingEnd ℂ) (atomicFourierVector freq t c n) *
        atomicFourierVector freq t c n) = (q n : ℂ)
  rw [← Complex.normSq_eq_conj_mul_self]
  simp only [q, Complex.ofReal_mul]


/-- Cesàro average of the first `N+1` powers of a complex number. -/
def geometricAverage (z : ℂ) (N : ℕ) : ℂ :=
  (((N + 1 : ℕ) : ℂ)⁻¹) * ∑ j ∈ Finset.range (N + 1), z ^ j

@[simp]
theorem geometricAverage_one (N : ℕ) : geometricAverage 1 N = 1 := by
  unfold geometricAverage
  simp only [one_pow]
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N)

theorem geometricAverage_tendsto_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (geometricAverage z) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let bound : ℕ → ℝ := fun N =>
    (2 / ‖z - 1‖) * (((N + 1 : ℕ) : ℝ)⁻¹)
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hbound (N : ℕ) : ‖geometricAverage z N‖ ≤ bound N := by
    rw [geometricAverage, norm_mul, geom_sum_eq hz1]
    rw [norm_inv, norm_natCast, norm_div]
    have hnum : ‖z ^ (N + 1) - 1‖ ≤ 2 := by
      calc
        ‖z ^ (N + 1) - 1‖ ≤ ‖z ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hz]; norm_num
    change (((N + 1 : ℕ) : ℝ)⁻¹) *
        (‖z ^ (N + 1) - 1‖ / ‖z - 1‖) ≤
      (2 / ‖z - 1‖) * (((N + 1 : ℕ) : ℝ)⁻¹)
    have hcast : 0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹) := by positivity
    have hdiv : ‖z ^ (N + 1) - 1‖ / ‖z - 1‖ ≤ 2 / ‖z - 1‖ :=
      div_le_div_of_nonneg_right hnum hden.le
    nlinarith
  have hcastTop : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro b
    obtain ⟨M, hM⟩ := exists_nat_ge b
    exact Filter.eventually_atTop.mpr ⟨M, fun N hN => by
      exact hM.trans (by exact_mod_cast Nat.le_succ_of_le hN)⟩
  have hinv : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcastTop
  have hbound0 : Tendsto bound atTop (nhds 0) := by
    simpa [bound] using hinv.const_mul (2 / ‖z - 1‖)
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hbound0

theorem norm_geometricAverage_le_one {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖geometricAverage z N‖ ≤ 1 := by
  rw [geometricAverage, norm_mul, norm_inv, norm_natCast]
  calc
    (((N + 1 : ℕ) : ℝ)⁻¹) * ‖∑ j ∈ Finset.range (N + 1), z ^ j‖ ≤
        (((N + 1 : ℕ) : ℝ)⁻¹) *
          (∑ j ∈ Finset.range (N + 1), ‖z ^ j‖) := by
      gcongr
      exact norm_sum_le _ _
    _ = 1 := by
      simp only [norm_pow, hz, one_pow, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero N)

private def finiteFrequencyStep (freq : ℕ → ℝ) (q K : ℕ) : ℝ :=
  (1 + ∑ n ∈ Finset.range K, |freq n - freq q|)⁻¹

private theorem realFourierCharacter_finiteFrequencyStep_ne_one
    (freq : ℕ → ℝ) (q K n : ℕ) (hnK : n < K)
    (hne : freq n ≠ freq q) :
    realFourierCharacter (freq n - freq q) (finiteFrequencyStep freq q K) ≠ 1 := by
  let S : ℝ := ∑ m ∈ Finset.range K, |freq m - freq q|
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnmem : n ∈ Finset.range K := Finset.mem_range.mpr hnK
  have hterm : |freq n - freq q| ≤ S := by
    exact Finset.single_le_sum (fun m _ => abs_nonneg (freq m - freq q)) hnmem
  have hden : 0 < 1 + S := by linarith
  have htau : finiteFrequencyStep freq q K = (1 + S)⁻¹ := rfl
  have htau0 : 0 < finiteFrequencyStep freq q K := by
    rw [htau]
    positivity
  let x : ℝ := (freq n - freq q) * finiteFrequencyStep freq q K
  have hxne : x ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hne) (ne_of_gt htau0)
  have hxabs : |x| < 1 := by
    rw [show |x| = |freq n - freq q| * finiteFrequencyStep freq q K by
      simp [x, abs_mul, abs_of_pos htau0]]
    rw [htau, inv_eq_one_div]
    calc
      |freq n - freq q| * (1 / (1 + S)) ≤ S * (1 / (1 + S)) := by
        gcongr
      _ = S / (1 + S) := by ring
      _ < 1 := (div_lt_one hden).2 (by linarith)
  have hxpi : -Real.pi < x ∧ x < Real.pi := by
    have hxone := abs_lt.mp hxabs
    constructor <;> linarith [Real.pi_gt_three]
  intro hchar
  have him := congrArg Complex.im hchar
  have hsin : Real.sin x = 0 := by
    change (Complex.exp (Complex.I * (x : ℂ))).im = 0 at him
    rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I_im] at him
    exact him
  exact hxne ((Real.sin_eq_zero_iff_of_lt_of_lt hxpi.1 hxpi.2).mp hsin)

private theorem geometricAverage_normSq_tendsto_zero {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun N => Complex.normSq (geometricAverage z N)) atTop (nhds 0) := by
  have hnorm := (geometricAverage_tendsto_zero hz hz1).norm
  have hsquare := hnorm.pow 2
  simpa [Complex.sq_norm, Complex.normSq_apply] using hsquare

private theorem atomicFourier_recovery_head_tendsto
    {w freq : ℕ → ℝ} {q K : ℕ} (hqK : q < K)
    (hfreq : ∀ n, n ≠ q → w n ≠ 0 → freq n ≠ freq q) :
    Tendsto (fun N => ∑ n ∈ Finset.range K,
        w n * Complex.normSq
          (geometricAverage
            (realFourierCharacter (freq n - freq q) (finiteFrequencyStep freq q K)) N))
      atTop (nhds (w q)) := by
  let tau := finiteFrequencyStep freq q K
  have hterm : ∀ n ∈ Finset.range K,
      Tendsto (fun N => w n * Complex.normSq
          (geometricAverage (realFourierCharacter (freq n - freq q) tau) N))
        atTop (nhds (if n = q then w q else 0)) := by
    intro n hn
    by_cases hnq : n = q
    · subst n
      simp [tau, realFourierCharacter]
    · by_cases hwn : w n = 0
      · simp [hwn, hnq]
      · have hz : ‖realFourierCharacter (freq n - freq q) tau‖ = 1 :=
          norm_realFourierCharacter _ _
        have hz1 : realFourierCharacter (freq n - freq q) tau ≠ 1 :=
          realFourierCharacter_finiteFrequencyStep_ne_one freq q K n
            (Finset.mem_range.mp hn) (hfreq n hnq hwn)
        have hzero := geometricAverage_normSq_tendsto_zero hz hz1
        simpa [hnq] using hzero.const_mul (w n)
  have hsum := tendsto_finsetSum (Finset.range K) hterm
  convert hsum using 1
  simp only [Finset.sum_ite_eq', Finset.mem_range, hqK, if_pos]

private def fourierRecoveryTime (tau : ℝ) (N : ℕ) : Fin (N + 1) → ℝ :=
  fun j => (j : ℝ) * tau

private def fourierRecoveryCoefficient (freq : ℕ → ℝ) (q N : ℕ) (tau : ℝ) :
    Fin (N + 1) → ℂ :=
  fun j => (((N + 1 : ℕ) : ℂ)⁻¹) *
    star (realFourierCharacter (freq q) (fourierRecoveryTime tau N j))

private theorem atomicFourierVector_recovery
    (freq : ℕ → ℝ) (q n N : ℕ) (tau : ℝ) :
    atomicFourierVector freq (fourierRecoveryTime tau N)
        (fourierRecoveryCoefficient freq q N tau) n =
      geometricAverage (realFourierCharacter (freq n - freq q) tau) N := by
  unfold atomicFourierVector fourierRecoveryCoefficient fourierRecoveryTime geometricAverage
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (((N + 1 : ℕ) : ℂ)⁻¹) *
      star (realFourierCharacter (freq q) ((j : ℝ) * tau)) *
        realFourierCharacter (freq n) ((j : ℝ) * tau)) (N + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, realFourierCharacter_freq_sub]
  rw [realFourierCharacter_nat_mul]

private theorem atomicFourier_quadraticReal_summable
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) :
    Summable (fun n => w n * Complex.normSq (atomicFourierVector freq t c n)) := by
  let C : ℝ := ∑ i, ‖c i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hvec (n : ℕ) : ‖atomicFourierVector freq t c n‖ ≤ C := by
    calc
      ‖atomicFourierVector freq t c n‖ ≤
          ∑ i, ‖c i * realFourierCharacter (freq n) (t i)‖ :=
        norm_sum_le Finset.univ _
      _ = C := by
        apply Finset.sum_congr rfl
        intro i _
        simp [norm_realFourierCharacter]
  have habs : Summable (fun n => |w n *
      Complex.normSq (atomicFourierVector freq t c n)|) := by
    apply Summable.of_nonneg_of_le (f := fun n => C ^ 2 * |w n|)
      (fun _ => abs_nonneg _)
    · intro n
      rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
      have hsquare : Complex.normSq (atomicFourierVector freq t c n) ≤ C ^ 2 := by
        rw [← Complex.sq_norm]
        exact (sq_le_sq₀ (norm_nonneg _) hC0).2 (hvec n)
      calc
        |w n| * Complex.normSq (atomicFourierVector freq t c n) ≤ |w n| * C ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (abs_nonneg _)
        _ = C ^ 2 * |w n| := mul_comm _ _
    · exact hw.mul_left (C ^ 2)
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using habs

private theorem atomicFourier_quadratic_nonnegative_of_positiveDefinite
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    (hpd : PositiveDefiniteOnReal (atomicFourierSeries w freq))
    {N : ℕ} (t : Fin N → ℝ) (c : Fin N → ℂ) :
    0 ≤ ∑' n, w n * Complex.normSq (atomicFourierVector freq t c n) := by
  obtain ⟨r, hr, hform⟩ := hpd N t c
  rw [atomicFourier_quadraticForm hw] at hform
  let q : ℕ → ℝ := fun n =>
    w n * Complex.normSq (atomicFourierVector freq t c n)
  have hqsum : Summable q := atomicFourier_quadraticReal_summable hw t c
  have hmap : ((∑' n, q n : ℝ) : ℂ) = ∑' n, (q n : ℂ) :=
    Complex.ofRealCLM.map_tsum hqsum
  have hterms :
      (∑' n, (w n : ℂ) * star (atomicFourierVector freq t c n) *
        atomicFourierVector freq t c n) = ∑' n, (q n : ℂ) := by
    apply tsum_congr
    intro n
    rw [mul_assoc]
    change (w n : ℂ) *
        ((starRingEnd ℂ) (atomicFourierVector freq t c n) *
          atomicFourierVector freq t c n) = (q n : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [q, Complex.ofReal_mul]
  rw [hterms, ← hmap] at hform
  have hre : (∑' n, q n) = r := Complex.ofReal_injective hform
  simpa only [q, hre] using hr
private theorem atomicFourier_recovery_summable
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    (q N : ℕ) (tau : ℝ) :
    Summable (fun n => w n * Complex.normSq
      (geometricAverage (realFourierCharacter (freq n - freq q) tau) N)) := by
  have habs : Summable (fun n => |w n * Complex.normSq
      (geometricAverage (realFourierCharacter (freq n - freq q) tau) N)|) := by
    apply Summable.of_nonneg_of_le (f := fun n => |w n|) (fun _ => abs_nonneg _)
    · intro n
      rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
      have havg := norm_geometricAverage_le_one
        (norm_realFourierCharacter (freq n - freq q) tau) N
      have hsq : Complex.normSq
          (geometricAverage (realFourierCharacter (freq n - freq q) tau) N) ≤ 1 := by
        rw [← Complex.sq_norm]
        nlinarith [norm_nonneg
          (geometricAverage (realFourierCharacter (freq n - freq q) tau) N)]
      exact mul_le_of_le_one_right (abs_nonneg _) hsq
    · exact hw
  rw [← summable_norm_iff]
  simpa [Real.norm_eq_abs] using habs

private theorem atomicFourier_recovery_tail_bound
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    (q K N : ℕ) (tau : ℝ) :
    |∑' n, w (n + K) * Complex.normSq
        (geometricAverage
          (realFourierCharacter (freq (n + K) - freq q) tau) N)| ≤
      ∑' n, |w (n + K)| := by
  let f : ℕ → ℝ := fun n => w (n + K) * Complex.normSq
    (geometricAverage (realFourierCharacter (freq (n + K) - freq q) tau) N)
  have hfsum : Summable f := by
    exact (summable_nat_add_iff K).2 (atomicFourier_recovery_summable hw q N tau)
  calc
    |∑' n, f n| = ‖∑' n, f n‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hfsum.norm
    _ ≤ ∑' n, |w (n + K)| := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [Real.norm_eq_abs]
        change |w (n + K) * Complex.normSq
            (geometricAverage
              (realFourierCharacter (freq (n + K) - freq q) tau) N)| ≤ |w (n + K)|
        rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
        have havg := norm_geometricAverage_le_one
          (norm_realFourierCharacter (freq (n + K) - freq q) tau) N
        have hsq : Complex.normSq
            (geometricAverage
              (realFourierCharacter (freq (n + K) - freq q) tau) N) ≤ 1 := by
          rw [← Complex.sq_norm]
          nlinarith [norm_nonneg
            (geometricAverage
              (realFourierCharacter (freq (n + K) - freq q) tau) N)]
        exact mul_le_of_le_one_right (abs_nonneg _) hsq
      · exact hfsum.norm
      · exact (summable_nat_add_iff K).2 hw

/-- **Atomic Bochner coefficient recovery.** For an absolutely summable real atomic Fourier
series with distinct active frequencies, positive definiteness forces every atomic weight to be
nonnegative. The proof uses only finite positive-definite matrices and Cesàro character averages. -/
theorem atomicFourierSeries_weight_nonnegative_of_positiveDefinite
    {w freq : ℕ → ℝ} (hw : Summable fun n => |w n|)
    (hfreq : ∀ q n, n ≠ q → w n ≠ 0 → freq n ≠ freq q)
    (hpd : PositiveDefiniteOnReal (atomicFourierSeries w freq))
    (q : ℕ) : 0 ≤ w q := by
  by_contra hq0
  have hqneg : w q < 0 := lt_of_not_ge hq0
  let eps : ℝ := -w q / 4
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hpartial := hw.hasSum.tendsto_sum_nat
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp hpartial) eps heps
  let K := max K₀ (q + 1)
  have hK₀K : K₀ ≤ K := le_max_left _ _
  have hqK : q < K := by
    have : q + 1 ≤ K := le_max_right _ _
    omega
  have hclose :
      dist (∑ n ∈ Finset.range K, |w n|) (∑' n, |w n|) < eps :=
    hK₀ K hK₀K
  let tailAbs : ℝ := ∑' n, |w (n + K)|
  have htailAbs0 : 0 ≤ tailAbs := tsum_nonneg fun _ => abs_nonneg _
  have hsplitAbs :
      (∑ n ∈ Finset.range K, |w n|) + tailAbs = ∑' n, |w n| := by
    exact hw.sum_add_tsum_nat_add K
  have htailSmall : tailAbs < eps := by
    have hdistEq :
        dist (∑ n ∈ Finset.range K, |w n|) (∑' n, |w n|) = tailAbs := by
      rw [← hsplitAbs]
      simp [abs_of_nonneg htailAbs0]
    rwa [hdistEq] at hclose
  let tau := finiteFrequencyStep freq q K
  let head : ℕ → ℝ := fun N => ∑ n ∈ Finset.range K,
    w n * Complex.normSq
      (geometricAverage (realFourierCharacter (freq n - freq q) tau) N)
  have hhead : Tendsto head atTop (nhds (w q)) := by
    exact atomicFourier_recovery_head_tendsto hqK (hfreq q)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hhead) eps heps
  have hheadClose : dist (head N₀) (w q) < eps := hN₀ N₀ le_rfl
  let full : ℝ := ∑' n, w n * Complex.normSq
    (geometricAverage (realFourierCharacter (freq n - freq q) tau) N₀)
  let tail : ℝ := ∑' n, w (n + K) * Complex.normSq
    (geometricAverage
      (realFourierCharacter (freq (n + K) - freq q) tau) N₀)
  have hfull0 : 0 ≤ full := by
    have hnonneg := atomicFourier_quadratic_nonnegative_of_positiveDefinite hw hpd
      (fourierRecoveryTime tau N₀) (fourierRecoveryCoefficient freq q N₀ tau)
    simpa only [atomicFourierVector_recovery, full] using hnonneg
  have hfullsum : Summable (fun n => w n * Complex.normSq
      (geometricAverage (realFourierCharacter (freq n - freq q) tau) N₀)) :=
    atomicFourier_recovery_summable hw q N₀ tau
  have hsplit : head N₀ + tail = full := by
    exact hfullsum.sum_add_tsum_nat_add K
  have htailBound : |tail| ≤ tailAbs := by
    exact atomicFourier_recovery_tail_bound hw q K N₀ tau
  have hheadUpper : head N₀ < w q + eps := by
    rw [Real.dist_eq] at hheadClose
    have habs := (abs_lt.mp hheadClose).2
    linarith
  have htailUpper : tail < eps :=
    (le_abs_self tail).trans_lt (htailBound.trans_lt htailSmall)
  have hfullNeg : full < 0 := by
    rw [← hsplit]
    dsimp [eps] at hheadUpper htailUpper
    linarith
  linarith

/-- Real atomic weight of the signed prime carrier on the vertical line `Re s = sigma`. -/
def signedPrimeVerticalWeight (epsilon : Nat.Primes → Bool) (sigma : ℝ) (n : ℕ) : ℝ :=
  if hn : n.Prime then
    primeDirichletRealSign (epsilon ⟨n, hn⟩) * (n : ℝ) ^ (-sigma)
  else 0

/-- Frequency convention for `P_epsilon(sigma + I t)`: the atom at `n` has frequency `-log n`. -/
def primeVerticalFrequency (n : ℕ) : ℝ := -Real.log n

/-- The absolutely convergent vertical trace of a signed prime Dirichlet carrier. -/
def signedPrimeVerticalTrace (epsilon : Nat.Primes → Bool) (sigma : ℝ) : ℝ → ℂ :=
  atomicFourierSeries (signedPrimeVerticalWeight epsilon sigma) primeVerticalFrequency

theorem signedPrimeVerticalTrace_eq_LSeries
    (epsilon : Nat.Primes → Bool) (sigma t : ℝ) :
    signedPrimeVerticalTrace epsilon sigma t =
      LSeries (signedPrimeArithmeticFunction epsilon)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
  unfold signedPrimeVerticalTrace atomicFourierSeries LSeries
  apply tsum_congr
  intro n
  by_cases hn : n.Prime
  · rw [LSeries.term_of_ne_zero hn.ne_zero]
    rw [show signedPrimeArithmeticFunction epsilon n = primeDirichletSign (epsilon ⟨n, hn⟩) by
      exact arithmeticOfPrimeColumn_apply_prime
        (fun p => primeDirichletSign (epsilon p)) ⟨n, hn⟩]
    simp only [signedPrimeVerticalWeight, hn, dif_pos, primeVerticalFrequency]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn.pos
    have hscalar :
        (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
            realFourierCharacter (-Real.log n) t =
          1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
      rw [Real.rpow_def_of_pos hnpos]
      rw [Complex.ofReal_exp]
      rw [realFourierCharacter]
      rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne_zero)]
      rw [one_div, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
        (Complex.ofReal_log hnpos.le).symm
      rw [hlog]
      push_cast
      ring
    cases epsilon ⟨n, hn⟩ <;>
      simp [primeDirichletRealSign, primeDirichletSign, hscalar, div_eq_mul_inv]
  · simp [signedPrimeVerticalWeight, signedPrimeArithmeticFunction,
      arithmeticOfPrimeColumn, hn, LSeries.term]

theorem signedPrimeVerticalWeight_abs_summable
    (epsilon : Nat.Primes → Bool) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable fun n => |signedPrimeVerticalWeight epsilon sigma n| := by
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => (n : ℝ) ^ (-sigma))
    (fun _ => abs_nonneg _)
  · intro n
    by_cases hn : n.Prime
    · simp only [signedPrimeVerticalWeight, hn, dif_pos, abs_mul]
      cases epsilon ⟨n, hn⟩ <;>
        simp [primeDirichletRealSign, abs_of_nonneg (Real.rpow_nonneg _ _)]
    · simp [signedPrimeVerticalWeight, hn, Real.rpow_nonneg]
  · exact Real.summable_nat_rpow.mpr (by linarith)

private theorem primeVerticalFrequency_ne_of_weight_ne
    (epsilon : Nat.Primes → Bool) (sigma : ℝ) (q n : ℕ)
    (hnq : n ≠ q) (hnw : signedPrimeVerticalWeight epsilon sigma n ≠ 0) :
    primeVerticalFrequency n ≠ primeVerticalFrequency q := by
  have hnprime : n.Prime := by
    by_contra hn
    exact hnw (by simp [signedPrimeVerticalWeight, hn])
  unfold primeVerticalFrequency
  intro hlog
  have hlog' : Real.log n = Real.log q := neg_injective hlog
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.cast_zero, Real.log_zero] at hlog'
    have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hnprime.one_lt)
    linarith
  · have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnprime.pos
    have hncast : (n : ℝ) = (q : ℝ) :=
      Real.strictMonoOn_log.injOn hnpos hqpos hlog'
    exact hnq (by exact_mod_cast hncast)

/-- **Unique positive-definite pointing of the signed prime cube.** On every convergence line
`sigma > 1`, the vertical trace is positive definite exactly for the all-positive orientation. -/
theorem signedPrimeVerticalTrace_positiveDefinite_iff_allPositive
    (epsilon : Nat.Primes → Bool) {sigma : ℝ} (hsigma : 1 < sigma) :
    PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon sigma) ↔
      PrimeOrientationAllPositive epsilon := by
  let w := signedPrimeVerticalWeight epsilon sigma
  have hwsum : Summable fun n => |w n| :=
    signedPrimeVerticalWeight_abs_summable epsilon hsigma
  constructor
  · intro hpd
    have hnonneg (n : ℕ) : 0 ≤ w n :=
      atomicFourierSeries_weight_nonnegative_of_positiveDefinite hwsum
        (fun q n hnq hnw => primeVerticalFrequency_ne_of_weight_ne
          epsilon sigma q n hnq hnw) hpd n
    intro p
    have hpweight : 0 < (p : ℝ) ^ (-sigma) :=
      Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
    have hp := hnonneg p
    have hp' : 0 ≤ primeDirichletRealSign (epsilon p) * (p : ℝ) ^ (-sigma) := by
      simpa [w, signedPrimeVerticalWeight, p.2] using hp
    cases he : epsilon p
    · rfl
    · simp [primeDirichletRealSign, he] at hp'
      linarith
  · intro hall
    unfold signedPrimeVerticalTrace
    apply positiveDefinite_atomicFourierSeries_of_nonnegative hwsum
    intro n
    by_cases hn : n.Prime
    · rw [show w n = primeDirichletRealSign (epsilon ⟨n, hn⟩) *
          (n : ℝ) ^ (-sigma) by simp [w, signedPrimeVerticalWeight, hn]]
      rw [hall ⟨n, hn⟩]
      simp [primeDirichletRealSign, Real.rpow_nonneg]
    · simp [w, signedPrimeVerticalWeight, hn]
end
end GaloisForLFunctions.HTGeometry
