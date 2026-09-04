import GaloisForLFunctions.RHTower.SemilocalBoostDiagonalClosedForm
import GaloisForLFunctions.RHTower.ScaledTerminatingHypergeometricLimit

/-!
# The large-rapidity bound for the boost matrix elements

`M_{mn}(t) = ∫ p_m p_n e^{its} dμ` (archimedean orthonormal Jacobi polynomials, Gamma measure).
With `σ = sech t`, `τ = tanh t`, the boost kernel factorizes,
`1 − wz − iτ(w+z) = (1−iτw)(1−iτz) − σ² wz`, and row `m` of the generating function is

`C_m (z + iτ)^m (1 − iτz)^{-m-1/2} = C_m Σ_{k≤m} binom(m,k) σ^{2k} (iτ)^{m−k} z^k (1 − iτz)^{-k-1/2}`

(binomial theorem for `z + iτ = σ²z + iτ(1 − iτz)`).  Reading off the `z^n` coefficient gives the
**separable expansion**

`c_m c_n M_{mn}(t) = (cosh t)^{-1/2} C_m Σ_{k ≤ min(m,n)} binom(m,k) σ^{2k} (iτ)^{m+n−2k} (k+½)_{n−k}/(n−k)!`

and, since every term has modulus `C_m C_n τ^{m+n} binom(m,k) binom(n,k) (σ/τ)^{2k}/C_k`, the
**boost bound**

`|M_{mn}(t)| ≤ (cosh t)^{-1/2} c_m c_n τ^{m+n} exp(2mn/sinh² t)`   (`t > 0`).

For `t = log p` the exponential is `exp(8mn/(p − 1/p)²) ≈ 1` when `√(mn) ≪ p`: the boost by a large
rapidity has entries of size `p^{-1/2} c_m c_n`, uniformly in the block `m, n ≪ p`.
-/

open Complex Finset
open scoped BigOperators

namespace RHTower
namespace MeixnerPollaczek

open ScaledHypergeometric PowerSeriesUniqueness

/-! ## `z + iτ = σ² z + iτ(1 − iτz)` -/

theorem sech_sq_add_tanh_sq (t : ℝ) : (1 / Real.cosh t) ^ 2 + Real.tanh t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos t).ne'
  have hsq := Real.cosh_sq t
  field_simp
  linear_combination (-1 : ℝ) * hsq

theorem add_I_tanh_eq (t : ℝ) (z : ℂ) :
    z + I * (Real.tanh t : ℂ) =
      (((1 / Real.cosh t) ^ 2 : ℝ) : ℂ) * z + I * (Real.tanh t : ℂ) * (1 - I * (Real.tanh t : ℂ) * z) := by
  have h := sech_sq_add_tanh_sq t
  have h' : ((((1 / Real.cosh t) ^ 2 : ℝ) : ℂ) + ((Real.tanh t : ℝ) : ℂ) ^ 2) = 1 := by
    exact_mod_cast h
  linear_combination (-z) * h' + (z * (Real.tanh t : ℂ) ^ 2) * I_sq

/-- The separable coefficient `binom(m,k) σ^{2k} (iτ)^{m−k}`. -/
noncomputable def sepCoeff (t : ℝ) (m k : ℕ) : ℂ :=
  (m.choose k : ℂ) * (((1 / Real.cosh t) ^ 2 : ℝ) : ℂ) ^ k * (I * (Real.tanh t : ℂ)) ^ (m - k)

/-- **The row polynomial factor is a binomial sum.** -/
theorem rowPolyFactor_eq_sum (t : ℝ) (m : ℕ) (z : ℂ) :
    rowPolyFactor t m z =
      ∑ k ∈ range (m + 1), sepCoeff t m k * z ^ k * (1 - I * (Real.tanh t : ℂ) * z) ^ (m - k) := by
  unfold rowPolyFactor
  rw [add_I_tanh_eq, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sepCoeff
  rw [mul_pow, mul_pow]
  ring

/-- The one-minus factor is nonzero on the unit disc. -/
theorem one_sub_I_tanh_mul_ne_zero' (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - I * (Real.tanh t : ℂ) * z ≠ 0 := by
  intro h
  have := re_one_sub_I_tanh_mul_pos t hz
  rw [h] at this
  simp at this

/-- **The row function as a finite sum of shifted binomial functions.** -/
theorem boostRowClosed_eq_sum (t : ℝ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    boostRowClosed t m z =
      rowConstant t m * ∑ k ∈ range (m + 1),
        sepCoeff t m k * (z ^ k * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((k : ℂ) + 1 / 2))) := by
  rw [boostRowClosed_eq_factors]
  simp only []
  rw [rowPolyFactor_eq_sum]
  unfold rowPowerFactor
  rw [Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by rw [Finset.mem_range] at hk; omega
  have hne := one_sub_I_tanh_mul_ne_zero' t hz
  have hpow : (1 - I * (Real.tanh t : ℂ) * z) ^ (m - k) * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((m : ℂ) + 1 / 2)) =
      (1 - I * (Real.tanh t : ℂ) * z) ^ (-((k : ℂ) + 1 / 2)) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    congr 1
    rw [Nat.cast_sub hk']
    ring
  rw [← hpow]
  ring

/-! ## Taylor coefficients of the shifted binomial functions -/

/-- The coefficient sequence of `z^k (1 − iτz)^{-k-1/2}`. -/
noncomputable def shiftedBinomialCoeff (t : ℝ) (k n : ℕ) : ℂ :=
  if k ≤ n then ((rising ((k : ℝ) + 1 / 2) (n - k) / (n - k).factorial : ℝ) : ℂ) *
    (I * (Real.tanh t : ℂ)) ^ (n - k) else 0

theorem hasSum_shiftedBinomial (t : ℝ) (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => shiftedBinomialCoeff t k n * z ^ n)
      (z ^ k * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((k : ℂ) + 1 / 2))) := by
  have hu : ‖I * (Real.tanh t : ℂ) * z‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := Real.abs_tanh_lt_one t
    have h2 := norm_nonneg z
    nlinarith [abs_nonneg (Real.tanh t)]
  have h := hasSum_one_sub_cpow_neg ((k : ℂ) + 1 / 2) hu
  have hcoef : ∀ j : ℕ, Ring.choose (-((k : ℂ) + 1 / 2)) j * (-(I * (Real.tanh t : ℂ) * z)) ^ j =
      (((rising ((k : ℝ) + 1 / 2) j / j.factorial : ℝ) : ℂ) * (I * (Real.tanh t : ℂ)) ^ j) * z ^ j := by
    intro j
    have hR : Ring.choose (-((k : ℂ) + 1 / 2)) j =
        (((-1) ^ j * rising ((k : ℝ) + 1 / 2) j / j.factorial : ℝ) : ℂ) := by
      rw [← ringChoose_neg_eq_rising, Complex.ofReal_choose]
      push_cast
      ring_nf
    rw [hR, neg_pow, mul_pow]
    push_cast [-Complex.ofReal_tanh]
    have h1 : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by rw [← mul_pow]; simp
    linear_combination ((rising ((k : ℝ) + 1 / 2) j : ℂ) / (j.factorial : ℂ) * (I * (Real.tanh t : ℂ)) ^ j * z ^ j) * h1
  have h' : HasSum (fun j : ℕ => ((((rising ((k : ℝ) + 1 / 2) j / j.factorial : ℝ) : ℂ) *
      (I * (Real.tanh t : ℂ)) ^ j) * z ^ (j + k))) (z ^ k * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((k : ℂ) + 1 / 2))) := by
    have := h.mul_left (z ^ k)
    refine this.congr_fun fun j => ?_
    rw [hcoef j, pow_add]
    ring
  rw [← hasSum_nat_add_iff' k]
  have hzero : ∑ i ∈ range k, shiftedBinomialCoeff t k i * z ^ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp [shiftedBinomialCoeff, Nat.not_le.mpr hi]
  rw [hzero, sub_zero]
  refine h'.congr_fun fun j => ?_
  simp [shiftedBinomialCoeff, Nat.add_sub_cancel]

/-- The separable row coefficient `Σ_k binom(m,k) σ^{2k} (iτ)^{m−k} · [z^n](z^k (1−iτz)^{-k-1/2})`. -/
noncomputable def sepRowCoeff (t : ℝ) (m n : ℕ) : ℂ :=
  ∑ k ∈ range (m + 1), sepCoeff t m k * shiftedBinomialCoeff t k n

theorem hasSum_sepRow (t : ℝ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => rowConstant t m * sepRowCoeff t m n * z ^ n) (boostRowClosed t m z) := by
  rw [boostRowClosed_eq_sum t m hz]
  have h := hasSum_sum (s := range (m + 1))
    (f := fun k n => sepCoeff t m k * (shiftedBinomialCoeff t k n * z ^ n))
    (a := fun k => sepCoeff t m k * (z ^ k * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((k : ℂ) + 1 / 2))))
    (fun k _ => (hasSum_shiftedBinomial t k hz).mul_left (sepCoeff t m k))
  have h2 := h.mul_left (rowConstant t m)
  refine h2.congr_fun fun n => ?_
  unfold sepRowCoeff
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The separable expansion of the boost matrix entries.** -/
theorem normalization_mul_boostMatrixEntry_eq_sepRow (t : ℝ) (m n : ℕ) :
    (semilocalArchimedeanJacobiNormalization n : ℂ) * boostMatrixEntry t m n =
      rowConstant t m * sepRowCoeff t m n := by
  rw [normalization_mul_boostMatrixEntry_eq]
  exact coeff_eq_of_hasSum_mul_pow_eq (r := 1 / 4) (by norm_num)
    (fun z hz => hasSum_taylor_boostRowClosed t m hz)
    (fun z hz => hasSum_sepRow t m (hz.trans (by norm_num))) n

/-! ## Norm bounds -/

theorem normalization_pos' (m : ℕ) : 0 < semilocalArchimedeanJacobiNormalization m := by
  unfold semilocalArchimedeanJacobiNormalization
  positivity

theorem norm_rowConstant (t : ℝ) (m : ℕ) :
    ‖rowConstant t m‖ = Real.cosh t ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization m := by
  unfold rowConstant
  rw [ringChoose_neg_half_mul_neg_one_pow]
  have hc : (semilocalArchimedeanJacobiNormalization m : ℂ) ≠ 0 := by
    exact_mod_cast (normalization_pos' m).ne'
  rw [show (semilocalArchimedeanJacobiNormalization m : ℂ) ^ 2 /
      (semilocalArchimedeanJacobiNormalization m : ℂ) = (semilocalArchimedeanJacobiNormalization m : ℂ) by
    field_simp]
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (Real.rpow_nonneg (Real.cosh_pos t).le _) (normalization_pos' m).le

theorem tanh_nonneg' {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.cosh_pos t).le

theorem norm_I_mul_tanh_pow {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    ‖(I * (Real.tanh t : ℂ)) ^ j‖ = Real.tanh t ^ j := by
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tanh_nonneg' ht)]

theorem norm_sepCoeff {t : ℝ} (ht : 0 ≤ t) (m k : ℕ) :
    ‖sepCoeff t m k‖ = (m.choose k : ℝ) * ((1 / Real.cosh t) ^ 2) ^ k * Real.tanh t ^ (m - k) := by
  unfold sepCoeff
  rw [norm_mul, norm_mul, norm_I_mul_tanh_pow ht, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem rising_nonneg_of_nonneg {a : ℝ} (ha : 0 ≤ a) (l : ℕ) : 0 ≤ rising a l := by
  unfold rising
  exact Finset.prod_nonneg fun i _ => by positivity

theorem norm_shiftedBinomialCoeff {t : ℝ} (ht : 0 ≤ t) (k n : ℕ) :
    ‖shiftedBinomialCoeff t k n‖ =
      if k ≤ n then rising ((k : ℝ) + 1 / 2) (n - k) / (n - k).factorial * Real.tanh t ^ (n - k) else 0 := by
  unfold shiftedBinomialCoeff
  split_ifs with h
  · rw [norm_mul, norm_I_mul_tanh_pow ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (rising_nonneg_of_nonneg (by positivity) _) (by positivity)
  · simp

/-- `C_j = binom(2j, j)/4^j`. -/
noncomputable def cbin (j : ℕ) : ℝ := (Nat.centralBinom j : ℝ) / 4 ^ j

theorem cbin_pos (j : ℕ) : 0 < cbin j := by
  unfold cbin
  have := Nat.centralBinom_pos j
  positivity

theorem cbin_eq_normalization_sq (j : ℕ) : cbin j = semilocalArchimedeanJacobiNormalization j ^ 2 :=
  centralBinom_div_four_pow_eq_normalization_sq j

theorem cbin_eq_rising (j : ℕ) : cbin j = rising (1 / 2) j / j.factorial :=
  normalizedCentralBinom_eq_rising_half_div j

/-- `(k+½)_{n−k}/(n−k)! = C_n binom(n,k) / C_k`. -/
theorem rising_shift_eq {k n : ℕ} (hk : k ≤ n) :
    rising ((k : ℝ) + 1 / 2) (n - k) / (n - k).factorial = cbin n * (n.choose k : ℝ) / cbin k := by
  have hadd := rising_add (1 / 2) k (n - k)
  rw [Nat.add_sub_cancel' hk] at hadd
  have hfac := Nat.choose_mul_factorial_mul_factorial hk
  have hfacR : ((n.choose k : ℕ) : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast hfac
  have hrk : 0 < rising (1 / 2) k := by
    unfold rising
    exact Finset.prod_pos fun i _ => by positivity
  have hkf : (0 : ℝ) < k.factorial := by positivity
  have hnkf : (0 : ℝ) < (n - k).factorial := by positivity
  have hch : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  set R := rising ((k : ℝ) + 1 / 2) (n - k) with hR
  have hadd' : rising (1 / 2) n = rising (1 / 2) k * R := by
    rw [hR, add_comm]
    exact hadd
  rw [cbin_eq_rising, cbin_eq_rising, hadd', ← hfacR]
  field_simp

theorem cbin_inv_eq (k : ℕ) : 1 / cbin k = 4 ^ k * (k.factorial : ℝ) ^ 2 / (2 * k).factorial := by
  unfold cbin
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  rw [show 2 * k - k = k by omega] at h
  have hR : (((2 * k).choose k : ℕ) : ℝ) * k.factorial * k.factorial = (2 * k).factorial := by
    exact_mod_cast h
  have h1 : (0 : ℝ) < (2 * k).choose k := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0 : ℝ) < k.factorial := by positivity
  have h3 : (0 : ℝ) < (2 * k).factorial := by positivity
  field_simp
  linear_combination (-1 : ℝ) * hR

/-- `binom(m,k) binom(n,k)/C_k ≤ (2mn)^k/k!`. -/
theorem choose_mul_choose_div_cbin_le (m n k : ℕ) :
    (m.choose k : ℝ) * (n.choose k : ℝ) / cbin k ≤ (2 * (m : ℝ) * n) ^ k / k.factorial := by
  rw [div_eq_mul_one_div, cbin_inv_eq]
  have hm := Nat.choose_le_pow_div (α := ℝ) k m
  have hn := Nat.choose_le_pow_div (α := ℝ) k n
  have h2 : (2 : ℝ) ^ k * k.factorial ≤ (2 * k).factorial := by
    exact_mod_cast Nat.two_pow_mul_factorial_le_factorial_two_mul k
  have hkf : (0 : ℝ) < k.factorial := by positivity
  have h2kf : (0 : ℝ) < (2 * k).factorial := by positivity
  have hcm : (0 : ℝ) ≤ m.choose k := by positivity
  have hcn : (0 : ℝ) ≤ n.choose k := by positivity
  calc (m.choose k : ℝ) * (n.choose k : ℝ) * (4 ^ k * (k.factorial : ℝ) ^ 2 / (2 * k).factorial)
      ≤ ((m : ℝ) ^ k / k.factorial) * ((n : ℝ) ^ k / k.factorial) *
        (4 ^ k * (k.factorial : ℝ) ^ 2 / (2 * k).factorial) := by
        gcongr
    _ = (m : ℝ) ^ k * (n : ℝ) ^ k * 4 ^ k / (2 * k).factorial := by
        field_simp
    _ ≤ (m : ℝ) ^ k * (n : ℝ) ^ k * 4 ^ k / (2 ^ k * k.factorial) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    _ = (2 * (m : ℝ) * n) ^ k / k.factorial := by
        rw [mul_pow, mul_pow, show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
        field_simp

/-! ## The bound -/

theorem sech_sq_div_tanh_sq {t : ℝ} (ht : 0 < t) :
    (1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2 = 1 / Real.sinh t ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hs := (Real.sinh_pos_iff.mpr ht).ne'
  have hc := (Real.cosh_pos t).ne'
  field_simp

theorem norm_sepRowCoeff_le {t : ℝ} (ht : 0 < t) (m n : ℕ) :
    ‖sepRowCoeff t m n‖ ≤ cbin n * Real.tanh t ^ (m + n) * Real.exp (2 * m * n / Real.sinh t ^ 2) := by
  have hτ : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)
  have hσ : 0 < (1 / Real.cosh t) ^ 2 := by positivity
  set x : ℝ := 2 * m * n / Real.sinh t ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxeq : x = 2 * (m : ℝ) * n * ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) := by
    rw [hx, sech_sq_div_tanh_sq ht]
    ring
  -- termwise bound
  have hterm : ∀ k ∈ range (m + 1), ‖sepCoeff t m k * shiftedBinomialCoeff t k n‖ ≤
      cbin n * Real.tanh t ^ (m + n) * (x ^ k / k.factorial) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [norm_mul, norm_sepCoeff ht.le, norm_shiftedBinomialCoeff ht.le]
    split_ifs with hkn
    · rw [rising_shift_eq hkn]
      have hkm : k ≤ m := by omega
      have hb := choose_mul_choose_div_cbin_le m n k
      have hcb := cbin_pos n
      have hck := cbin_pos k
      -- rearrange: choose(m,k) σ^{2k} τ^{m−k} · (C_n choose(n,k)/C_k) τ^{n−k}
      --   = C_n τ^{m+n} · (choose(m,k) choose(n,k)/C_k) · (σ²/τ²)^k
      have hτpow : Real.tanh t ^ (m - k) * Real.tanh t ^ (n - k) =
          Real.tanh t ^ (m + n) / Real.tanh t ^ (2 * k) := by
        rw [eq_div_iff (by positivity), ← pow_add, ← pow_add]
        congr 1
        omega
      have hrew : (m.choose k : ℝ) * ((1 / Real.cosh t) ^ 2) ^ k * Real.tanh t ^ (m - k) *
          (cbin n * (n.choose k : ℝ) / cbin k * Real.tanh t ^ (n - k)) =
          cbin n * Real.tanh t ^ (m + n) *
            (((m.choose k : ℝ) * (n.choose k : ℝ) / cbin k) *
              ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) ^ k) := by
        calc (m.choose k : ℝ) * ((1 / Real.cosh t) ^ 2) ^ k * Real.tanh t ^ (m - k) *
              (cbin n * (n.choose k : ℝ) / cbin k * Real.tanh t ^ (n - k))
            = (m.choose k : ℝ) * ((1 / Real.cosh t) ^ 2) ^ k * (cbin n * (n.choose k : ℝ) / cbin k) *
              (Real.tanh t ^ (m - k) * Real.tanh t ^ (n - k)) := by ring
          _ = (m.choose k : ℝ) * ((1 / Real.cosh t) ^ 2) ^ k * (cbin n * (n.choose k : ℝ) / cbin k) *
              (Real.tanh t ^ (m + n) / Real.tanh t ^ (2 * k)) := by rw [hτpow]
          _ = cbin n * Real.tanh t ^ (m + n) *
              (((m.choose k : ℝ) * (n.choose k : ℝ) / cbin k) *
                ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) ^ k) := by
              rw [div_pow ((1 / Real.cosh t) ^ 2) (Real.tanh t ^ 2) k, ← pow_mul (Real.tanh t) 2 k]
              have h2k : Real.tanh t ^ (2 * k) ≠ 0 := by positivity
              field_simp
      rw [hrew, hxeq, mul_pow, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hsq : 0 ≤ ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) := by positivity
      calc (m.choose k : ℝ) * (n.choose k : ℝ) / cbin k * ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) ^ k
          ≤ (2 * (m : ℝ) * n) ^ k / k.factorial * ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) ^ k :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = (2 * (m : ℝ)) ^ k * (n : ℝ) ^ k * ((1 / Real.cosh t) ^ 2 / Real.tanh t ^ 2) ^ k /
            k.factorial := by
            rw [mul_pow]
            ring
    · simp only [mul_zero]
      have := cbin_pos n
      positivity
  calc ‖sepRowCoeff t m n‖ ≤ ∑ k ∈ range (m + 1), ‖sepCoeff t m k * shiftedBinomialCoeff t k n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ range (m + 1), cbin n * Real.tanh t ^ (m + n) * (x ^ k / k.factorial) :=
        Finset.sum_le_sum hterm
    _ = cbin n * Real.tanh t ^ (m + n) * ∑ k ∈ range (m + 1), x ^ k / k.factorial := by
        rw [Finset.mul_sum]
    _ ≤ cbin n * Real.tanh t ^ (m + n) * Real.exp x := by
        have := cbin_pos n
        exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx0 (m + 1)) (by positivity)

/-- **The large-rapidity boost bound:**
`|M_{mn}(t)| ≤ (cosh t)^{-1/2} c_m c_n (tanh t)^{m+n} exp(2mn/sinh² t)` for `t > 0`. -/
theorem norm_boostMatrixEntry_le {t : ℝ} (ht : 0 < t) (m n : ℕ) :
    ‖boostMatrixEntry t m n‖ ≤
      Real.cosh t ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization m *
        semilocalArchimedeanJacobiNormalization n * Real.tanh t ^ (m + n) *
        Real.exp (2 * m * n / Real.sinh t ^ 2) := by
  have hcn := normalization_pos' n
  have h := normalization_mul_boostMatrixEntry_eq_sepRow t m n
  have hnorm : semilocalArchimedeanJacobiNormalization n * ‖boostMatrixEntry t m n‖ =
      ‖rowConstant t m‖ * ‖sepRowCoeff t m n‖ := by
    rw [← norm_mul, ← h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  rw [norm_rowConstant] at hnorm
  have hb := norm_sepRowCoeff_le ht m n
  rw [cbin_eq_normalization_sq] at hb
  have hcosh : 0 ≤ Real.cosh t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Real.cosh_pos t).le _
  have hcm := normalization_pos' m
  have hmain : semilocalArchimedeanJacobiNormalization n * ‖boostMatrixEntry t m n‖ ≤
      semilocalArchimedeanJacobiNormalization n *
        (Real.cosh t ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization m *
          semilocalArchimedeanJacobiNormalization n * Real.tanh t ^ (m + n) *
          Real.exp (2 * m * n / Real.sinh t ^ 2)) := by
    rw [hnorm]
    calc Real.cosh t ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization m * ‖sepRowCoeff t m n‖
        ≤ Real.cosh t ^ (-(1 / 2 : ℝ)) * semilocalArchimedeanJacobiNormalization m *
          (semilocalArchimedeanJacobiNormalization n ^ 2 * Real.tanh t ^ (m + n) *
            Real.exp (2 * m * n / Real.sinh t ^ 2)) := by
          gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_left hmain hcn

end MeixnerPollaczek
end RHTower
