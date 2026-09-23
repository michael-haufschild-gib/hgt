import GaloisForLFunctions.RHTower.SoninSemilocalJacobiOrthonormal
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiResidueCorollaries

/-!
# The one-prime semilocal grading coefficient

This file specializes the literal finite-prime Euler-weighted Gamma integral to one prime, reindexes
the `Fin 1 → ℤ` Poisson lattice by the integers, folds its even nonzero frequencies to the positive
integers, and proves the exact positive-series formula for every even Jacobi coefficient.  It is the
analytic input for the quantitative unbounded grading-deformation theorem.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

def semilocalOnePrimeFamily (p : ℕ) : Fin 1 → ℕ := fun _ => p

@[simp]
theorem semilocalOnePrimeFamily_apply (p : ℕ) (i : Fin 1) :
    semilocalOnePrimeFamily p i = p := rfl

theorem semilocalOnePrimePoissonWeight (p : ℕ) (m : Fin 1 → ℤ) :
    semilocalFinitePrimePoissonWeight (semilocalOnePrimeFamily p) m =
      semilocalPrimePoissonRatio p ^ (m 0).natAbs := by
  simp [semilocalFinitePrimePoissonWeight, semilocalOnePrimeFamily]

theorem semilocalOnePrimeLogFrequency (p : ℕ) (m : Fin 1 → ℤ) :
    semilocalFinitePrimeLogFrequency (semilocalOnePrimeFamily p) m =
      (m 0 : ℝ) * Real.log p := by
  simp [semilocalFinitePrimeLogFrequency, semilocalOnePrimeFamily]

theorem semilocalOnePrimePoissonPrefactor (p : ℕ) :
    semilocalFinitePrimePoissonPrefactor (semilocalOnePrimeFamily p) =
      (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ := by
  simp [semilocalFinitePrimePoissonPrefactor, semilocalOnePrimeFamily]

theorem semilocalArchimedeanEvenJacobiKernel_neg (k : ℕ) (t : ℝ) :
    semilocalArchimedeanEvenJacobiKernel k (-t) =
      semilocalArchimedeanEvenJacobiKernel k t := by
  unfold semilocalArchimedeanEvenJacobiKernel
    semilocalArchimedeanCharacteristic
  rw [Real.cosh_neg, Real.tanh_neg, neg_pow]
  have heven : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  have htanh : (-Real.tanh t) ^ (2 * k) = Real.tanh t ^ (2 * k) := by
    rw [neg_pow, heven, one_mul]
  rw [htanh]

def semilocalOnePrimeEvenJacobiTerm (k p : ℕ) (m : ℤ) : ℝ :=
  semilocalPrimePoissonRatio p ^ m.natAbs *
    semilocalArchimedeanEvenJacobiKernel k
      ((m : ℝ) * Real.log p)

theorem semilocalOnePrimeEvenJacobiTerm_even (k p : ℕ) :
    Function.Even (semilocalOnePrimeEvenJacobiTerm k p) := by
  intro m
  unfold semilocalOnePrimeEvenJacobiTerm
  rw [Int.natAbs_neg]
  push_cast
  rw [neg_mul, semilocalArchimedeanEvenJacobiKernel_neg]

theorem summable_semilocalOnePrimeEvenJacobiTerm
    {k p : ℕ} (hp : p.Prime) :
    Summable (semilocalOnePrimeEvenJacobiTerm k p) := by
  have hfull := summable_semilocalFinitePrimeEvenJacobiFullTerm
    (k := k) (semilocalOnePrimeFamily p) (fun _ => hp)
  have hcomp := hfull.comp_injective
    (Equiv.funUnique (Fin 1) ℤ).symm.injective
  simpa [semilocalOnePrimeEvenJacobiTerm,
    semilocalOnePrimePoissonWeight,
    semilocalOnePrimeLogFrequency,
    Equiv.funUnique_symm_apply] using! hcomp

def semilocalOnePrimePositiveEvenJacobiSeries (k p : ℕ) : ℝ :=
  ∑' m : ℕ, semilocalOnePrimeEvenJacobiTerm k p ((m : ℤ) + 1)

def semilocalOnePrimeEvenJacobiMagnitudeTerm (k p m : ℕ) : ℝ :=
  semilocalPrimePoissonRatio p ^ (m + 1) *
    semilocalArchimedeanJacobiNormalization (2 * k) *
      semilocalArchimedeanCharacteristic
        (((m + 1 : ℕ) : ℝ) * Real.log p) *
        Real.tanh (((m + 1 : ℕ) : ℝ) * Real.log p) ^ (2 * k)

def semilocalOnePrimeEvenJacobiMagnitudeSeries (k p : ℕ) : ℝ :=
  ∑' m : ℕ, semilocalOnePrimeEvenJacobiMagnitudeTerm k p m

theorem semilocalOnePrimeEvenJacobiTerm_succ_signed
    (k p m : ℕ) :
    (-1 : ℝ) ^ k * semilocalOnePrimeEvenJacobiTerm k p ((m : ℤ) + 1) =
      semilocalOnePrimeEvenJacobiMagnitudeTerm k p m := by
  unfold semilocalOnePrimeEvenJacobiTerm
    semilocalOnePrimeEvenJacobiMagnitudeTerm
    semilocalArchimedeanEvenJacobiKernel
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have habs : ((m : ℤ) + 1).natAbs = m + 1 := by
    have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (m : ℤ) + 1 by omega)
    exact_mod_cast h
  rw [habs]
  push_cast
  calc
    (-1 : ℝ) ^ k *
        (semilocalPrimePoissonRatio p ^ (m + 1) *
          ((-1 : ℝ) ^ k *
            semilocalArchimedeanJacobiNormalization (2 * k) *
            semilocalArchimedeanCharacteristic
              (((m : ℝ) + 1) * Real.log p) *
            Real.tanh (((m : ℝ) + 1) * Real.log p) ^ (2 * k))) =
        ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          (semilocalPrimePoissonRatio p ^ (m + 1) *
            semilocalArchimedeanJacobiNormalization (2 * k) *
            semilocalArchimedeanCharacteristic
              (((m : ℝ) + 1) * Real.log p) *
            Real.tanh (((m : ℝ) + 1) * Real.log p) ^ (2 * k)) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem summable_semilocalOnePrimeEvenJacobiMagnitudeTerm
    {k p : ℕ} (hp : p.Prime) :
    Summable (semilocalOnePrimeEvenJacobiMagnitudeTerm k p) := by
  have hs := (summable_semilocalOnePrimeEvenJacobiTerm (k := k) hp).comp_injective
    (show Function.Injective (fun m : ℕ => (m : ℤ) + 1) by
      intro m n h
      change (m : ℤ) + 1 = (n : ℤ) + 1 at h
      have hc : (m : ℤ) = n := add_right_cancel h
      exact_mod_cast hc)
  have hscaled := hs.mul_left ((-1 : ℝ) ^ k)
  exact hscaled.congr (semilocalOnePrimeEvenJacobiTerm_succ_signed k p)

theorem semilocalOnePrimePositiveEvenJacobiSeries_eq_signed_magnitudeSeries
    {k p : ℕ} :
    semilocalOnePrimePositiveEvenJacobiSeries k p =
      (-1 : ℝ) ^ k * semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
  unfold semilocalOnePrimePositiveEvenJacobiSeries
    semilocalOnePrimeEvenJacobiMagnitudeSeries
  rw [← tsum_mul_left]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  apply tsum_congr
  intro m
  have h := semilocalOnePrimeEvenJacobiTerm_succ_signed k p m
  calc
    semilocalOnePrimeEvenJacobiTerm k p ((m : ℤ) + 1) =
        ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          semilocalOnePrimeEvenJacobiTerm k p ((m : ℤ) + 1) := by rw [hsign, one_mul]
    _ = (-1 : ℝ) ^ k * semilocalOnePrimeEvenJacobiMagnitudeTerm k p m := by
      rw [← h]
      ring

theorem semilocalOnePrimeEvenJacobiMagnitudeTerm_pos
    {k p : ℕ} (hp : p.Prime) (m : ℕ) :
    0 < semilocalOnePrimeEvenJacobiMagnitudeTerm k p m := by
  unfold semilocalOnePrimeEvenJacobiMagnitudeTerm
  have hfreq : (((m + 1 : ℕ) : ℝ) * Real.log p) ≠ 0 := by
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    exact mul_ne_zero (by positivity) hlog.ne'
  exact mul_pos
    (mul_pos
      (mul_pos (pow_pos (semilocalPrimePoissonRatio_pos hp) _)
        (semilocalArchimedeanJacobiNormalization_pos (2 * k)))
      (semilocalArchimedeanCharacteristic_pos _))
    (tanh_even_pow_pos hfreq)

theorem semilocalOnePrimeEvenJacobiMagnitudeSeries_pos
    {k p : ℕ} (hp : p.Prime) :
    0 < semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
  have hs := summable_semilocalOnePrimeEvenJacobiMagnitudeTerm (k := k) hp
  exact (semilocalOnePrimeEvenJacobiMagnitudeTerm_pos hp 0).trans_le
    (by
      unfold semilocalOnePrimeEvenJacobiMagnitudeSeries
      exact hs.le_tsum 0 (fun m _ =>
        (semilocalOnePrimeEvenJacobiMagnitudeTerm_pos hp m).le))

theorem tsum_semilocalOnePrimeEvenJacobiTerm_eq_two_mul_positiveSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (∑' m : ℤ, semilocalOnePrimeEvenJacobiTerm k p m) =
      2 * semilocalOnePrimePositiveEvenJacobiSeries k p := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (semilocalOnePrimeEvenJacobiTerm_even k p)
    (summable_semilocalOnePrimeEvenJacobiTerm hp)]
  have hzero : semilocalOnePrimeEvenJacobiTerm k p 0 = 0 := by
    unfold semilocalOnePrimeEvenJacobiTerm
    norm_num [semilocalArchimedeanEvenJacobiKernel_zero hk]
  rw [hzero, zero_add]
  rw [show (∑' n : ℕ+, semilocalOnePrimeEvenJacobiTerm k p (n : ℕ)) =
      ∑' n : ℕ, semilocalOnePrimeEvenJacobiTerm k p (n + 1) by
    exact tsum_pnat_eq_tsum_succ
      (M := ℝ) (f := fun n : ℕ => semilocalOnePrimeEvenJacobiTerm k p n)]
  simp [semilocalOnePrimePositiveEvenJacobiSeries]

theorem semilocalOnePrimeEvenJacobiNumerator_eq_two_mul_positiveSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    semilocalFinitePrimeEvenJacobiNumerator k (semilocalOnePrimeFamily p) =
      2 * semilocalOnePrimePositiveEvenJacobiSeries k p := by
  rw [← tsum_semilocalFinitePrimeEvenJacobiFullTerm_eq_numerator
    hk (semilocalOnePrimeFamily p) (fun _ => hp)]
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  simpa [semilocalOnePrimeEvenJacobiTerm,
    semilocalFinitePrimePoissonWeight,
    semilocalFinitePrimeLogFrequency,
    semilocalOnePrimeFamily,
    Equiv.funUnique_symm_apply] using
      (tsum_semilocalOnePrimeEvenJacobiTerm_eq_two_mul_positiveSeries hk hp)

def semilocalOnePrimeEvenJacobiCoefficient (k p : ℕ) : ℝ :=
  ∫ s : ℝ,
    (semilocalArchimedeanJacobiPolynomial (2 * k)).eval s *
      semilocalFinitePrimeEulerDensity (semilocalOnePrimeFamily p) s
      ∂semilocalArchimedeanGammaMeasure

theorem semilocalOnePrimeEvenJacobiCoefficient_eq_numerator
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    semilocalOnePrimeEvenJacobiCoefficient k p =
      (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
        semilocalFinitePrimeEvenJacobiNumerator k
          (semilocalOnePrimeFamily p) := by
  unfold semilocalOnePrimeEvenJacobiCoefficient
  rw [integral_semilocalFinitePrimeEulerDensity_mul_evenJacobi_eq_numerator
    hk (semilocalOnePrimeFamily p) (fun _ => hp)]
  rw [semilocalOnePrimePoissonPrefactor]

theorem semilocalOnePrimeEvenJacobiCoefficient_signed_eq_magnitudeSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    (-1 : ℝ) ^ k * semilocalOnePrimeEvenJacobiCoefficient k p =
      2 * (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
        semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
  rw [semilocalOnePrimeEvenJacobiCoefficient_eq_numerator hk hp,
    semilocalOnePrimeEvenJacobiNumerator_eq_two_mul_positiveSeries hk hp,
    semilocalOnePrimePositiveEvenJacobiSeries_eq_signed_magnitudeSeries]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ k *
        ((1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
          (2 * ((-1 : ℝ) ^ k *
            semilocalOnePrimeEvenJacobiMagnitudeSeries k p))) =
        ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          (2 * (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
            semilocalOnePrimeEvenJacobiMagnitudeSeries k p) := by ring
    _ = _ := by rw [hsign, one_mul]

/-- The exact one-prime coefficient formula (card equation (3)). -/
theorem abs_semilocalOnePrimeEvenJacobiCoefficient_eq_magnitudeSeries
    {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    |semilocalOnePrimeEvenJacobiCoefficient k p| =
      2 * (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
        semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by
  have h := semilocalOnePrimeEvenJacobiCoefficient_signed_eq_magnitudeSeries hk hp
  have hden : 0 < (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ := by
    apply inv_pos.mpr
    have hr0 := semilocalPrimePoissonRatio_pos hp
    have hr1 := semilocalPrimePoissonRatio_lt_one hp
    nlinarith [sq_nonneg (semilocalPrimePoissonRatio p)]
  have hseries := semilocalOnePrimeEvenJacobiMagnitudeSeries_pos (k := k) hp
  have hright : 0 < 2 * (1 - semilocalPrimePoissonRatio p ^ (2 : ℕ))⁻¹ *
      semilocalOnePrimeEvenJacobiMagnitudeSeries k p := by positivity
  have habs := congrArg abs h
  simpa [abs_mul, abs_of_pos hright] using habs

end RHTower
