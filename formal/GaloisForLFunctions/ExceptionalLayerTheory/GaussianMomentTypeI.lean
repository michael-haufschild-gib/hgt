import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanTypeI
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentInfiniteTypeII

/-!
# Type-I estimates for first Gaussian moments

Positive logarithmic curvature controls every dyadic prefix. Half the
Gaussian absorbs the moment, leaving a summable envelope. Dilation
retains the reciprocal-divisor saving needed by Vaughan's identity.
-/

open Complex Finset Filter Topology RHTower RHTower.Sieve
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory


private theorem gaussianLogCurvature_double_le {ξ t x : ℝ}
    (hξ : 0 ≤ ξ) (hx : 0 < x) :
    gaussianLogCurvature ξ t x ≤ 4 * gaussianLogCurvature ξ t (2 * x) := by
  have he : 4 * gaussianLogCurvature ξ t (2 * x) - gaussianLogCurvature ξ t x =
      3 * ξ / Real.pi := by
    unfold gaussianLogCurvature
    field_simp [hx.ne', Real.pi_ne_zero]
    ring
  have hh : 0 ≤ 3 * ξ / Real.pi := by positivity
  linarith only [he, hh]

private theorem gaussianLogCurvature_double_sqrt_le {ξ t x : ℝ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) (hx : 0 < x) :
    Real.sqrt (gaussianLogCurvature ξ t (2 * x)) ≤ Real.sqrt ξ + Real.sqrt t / x := by
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have hξπ : ξ / Real.pi ≤ ξ := (div_le_iff₀ Real.pi_pos).mpr (by nlinarith only [hξ, hπ])
  have htπ : t / (8 * Real.pi) ≤ t := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [ht, hπ])
  have he : gaussianLogCurvature ξ t (2 * x) = ξ / Real.pi + (t / (8 * Real.pi)) / x ^ 2 := by
    unfold gaussianLogCurvature
    field_simp [hx.ne', Real.pi_ne_zero]
    ring
  have hupper : gaussianLogCurvature ξ t (2 * x) ≤ ξ + t / x ^ 2 := by
    rw [he]
    exact add_le_add hξπ (div_le_div_of_nonneg_right htπ (sq_nonneg _))
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hsξ := Real.sq_sqrt hξ
  have hst : (Real.sqrt t / x) ^ 2 = t / x ^ 2 := by rw [div_pow, Real.sq_sqrt ht.le]
  have hcross := mul_nonneg (Real.sqrt_nonneg ξ) (div_nonneg (Real.sqrt_nonneg t) hx.le)
  exact hupper.trans (by nlinarith only [hsξ, hst, hcross])

private theorem gaussianLogCurvature_double_inv_sqrt_le {ξ t x : ℝ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) (hx : 0 < x) :
    12 / Real.sqrt (gaussianLogCurvature ξ t (2 * x)) ≤ 72 * x / Real.sqrt t := by
  have hcurv : 0 < gaussianLogCurvature ξ t (2 * x) := by unfold gaussianLogCurvature; positivity
  have hrootcurv : 0 < Real.sqrt (gaussianLogCurvature ξ t (2 * x)) := Real.sqrt_pos.mpr hcurv
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have he : gaussianLogCurvature ξ t (2 * x) = ξ / Real.pi + (t / (8 * Real.pi)) / x ^ 2 := by
    unfold gaussianLogCurvature
    field_simp [hx.ne', Real.pi_ne_zero]
    ring
  have hcoef : t / 36 ≤ t / (8 * Real.pi) :=
    div_le_div_of_nonneg_left ht.le (by positivity) (by linarith only [Real.pi_lt_four])
  have hlower : t / (36 * x ^ 2) ≤ gaussianLogCurvature ξ t (2 * x) := by
    rw [he]
    calc
      _ = (t / 36) / x ^ 2 := by ring
      _ ≤ (t / (8 * Real.pi)) / x ^ 2 := div_le_div_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hclear := (div_le_iff₀ (by positivity : 0 < 36 * x ^ 2)).mp hlower
  have hsq : (6 * x * Real.sqrt (gaussianLogCurvature ξ t (2 * x))) ^ 2 =
      36 * x ^ 2 * gaussianLogCurvature ξ t (2 * x) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hcurv.le]
    ring
  have hroot : Real.sqrt t ≤ 6 * x * Real.sqrt (gaussianLogCurvature ξ t (2 * x)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [hsq]
    nlinarith only [hclear]
  apply (div_le_iff₀ hrootcurv).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hst).mpr
  nlinarith only [hroot]

/-- Positive curvature gives a uniform dyadic prefix bound in elementary scales. -/
theorem gaussianTypeIBound_dyadic_le {ξ t : ℝ}
    (hξ : 0 ≤ ξ) (ht : 0 < t) {P : ℕ} (hP : 1 ≤ P) :
    gaussianTypeIBound ξ t P (2 * P) ≤
      100 * ((P : ℝ) * Real.sqrt ξ + Real.sqrt t + (P : ℝ) / Real.sqrt t) := by
  have hx : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hcurv : 0 < gaussianLogCurvature ξ t (2 * (P : ℝ)) := by unfold gaussianLogCurvature; positivity
  have hr : gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t (2 * (P : ℝ)) ≤ 4 :=
    (div_le_iff₀ hcurv).mpr (gaussianLogCurvature_double_le hξ hx)
  have hs := gaussianLogCurvature_double_sqrt_le hξ ht hx
  have hi := gaussianLogCurvature_double_inv_sqrt_le hξ ht hx
  simp only [gaussianTypeIBound, show 2 * P - P = P by omega, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ 8 * (P : ℝ) * (gaussianLogCurvature ξ t P / gaussianLogCurvature ξ t (2 * (P : ℝ))) *
        Real.sqrt (gaussianLogCurvature ξ t (2 * (P : ℝ))) +
          12 / Real.sqrt (gaussianLogCurvature ξ t (2 * (P : ℝ))) := min_le_right _ _
    _ ≤ 8 * (P : ℝ) * 4 * (Real.sqrt ξ + Real.sqrt t / P) + 72 * P / Real.sqrt t := by gcongr
    _ = 32 * ((P : ℝ) * Real.sqrt ξ + Real.sqrt t) + 72 * P / Real.sqrt t := by
      field_simp [hx.ne']
      ring
    _ ≤ _ := by
      have h₁ : 0 ≤ (P : ℝ) * Real.sqrt ξ := by positivity
      have h₂ := Real.sqrt_nonneg t
      have h₃ : 0 ≤ (P : ℝ) / Real.sqrt t := by positivity
      simp only [div_eq_mul_inv] at h₃ ⊢
      nlinarith only [h₁, h₂, h₃]



private theorem gaussian_linear_absorption (y : ℝ) :
    y * Real.exp (-y / 2) ≤ 2 := by
  have he : y ≤ 2 * Real.exp (y / 2) := by
    have hh := Real.add_one_le_exp (y / 2)
    linarith only [hh]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-y / 2)).le
  have hcancel : Real.exp (y / 2) * Real.exp (-y / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show y / 2 + -y / 2 = 0 by ring, Real.exp_zero]
  nlinarith only [hh, hcancel]

private theorem gaussian_root_absorption (z : ℝ) :
    z * Real.exp (-(z ^ 2) / 2) ≤ 1 := by
  have he : z ≤ Real.exp (z ^ 2 / 2) := by
    have hh := Real.add_one_le_exp (z ^ 2 / 2)
    nlinarith only [hh, sq_nonneg (z - 1)]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(z ^ 2) / 2)).le
  have hcancel : Real.exp (z ^ 2 / 2) * Real.exp (-(z ^ 2) / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show z ^ 2 / 2 + -(z ^ 2) / 2 = 0 by ring, Real.exp_zero]
  exact hh.trans_eq hcancel

/-- Half the Gaussian absorbs the moment and both curvature scales. -/
theorem gaussian_moment_curvature_absorption {α ξ t x : ℝ}
    (hα : 0 ≤ α) (ht : 0 < t) (hx : 0 ≤ x)
    (hsector : ξ ≤ 2 * α * t) :
    α * x ^ 2 * Real.exp (-α * x ^ 2) *
        (x * Real.sqrt ξ + Real.sqrt t + x / Real.sqrt t) ≤
      5 * (Real.sqrt (α * t) + 1 / Real.sqrt t) * x *
        Real.exp (-α * x ^ 2 / 2) := by
  have hsq : (Real.sqrt α * x) ^ 2 = α * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hα]
  have hl := gaussian_linear_absorption (α * x ^ 2)
  have hr := gaussian_root_absorption (Real.sqrt α * x)
  rw [hsq] at hr
  have hξ' : Real.sqrt ξ ≤ 2 * Real.sqrt (α * t) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hα ht.le)]
    nlinarith only [hsector, mul_nonneg hα ht.le]
  have he : Real.exp (-α * x ^ 2) =
      Real.exp (-α * x ^ 2 / 2) * Real.exp (-α * x ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit : α * x ^ 2 * Real.exp (-α * x ^ 2) *
      (x * Real.sqrt ξ + Real.sqrt t + x / Real.sqrt t) =
      x * Real.exp (-α * x ^ 2 / 2) *
        (Real.sqrt ξ * (α * x ^ 2 * Real.exp (-α * x ^ 2 / 2)) +
         Real.sqrt (α * t) * (Real.sqrt α * x * Real.exp (-α * x ^ 2 / 2)) +
         (1 / Real.sqrt t) * (α * x ^ 2 * Real.exp (-α * x ^ 2 / 2))) := by
    rw [he, Real.sqrt_mul hα]
    ring_nf
    rw [Real.sq_sqrt hα]
    ring
  rw [hsplit]
  have hfirst := mul_le_mul hξ' hl (by positivity) (by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg (α * t))
  have hthird := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1 / Real.sqrt t)
  have hbound : Real.sqrt ξ * (α * x ^ 2 * Real.exp (-α * x ^ 2 / 2)) +
      Real.sqrt (α * t) * (Real.sqrt α * x * Real.exp (-α * x ^ 2 / 2)) +
      (1 / Real.sqrt t) * (α * x ^ 2 * Real.exp (-α * x ^ 2 / 2)) ≤
        5 * (Real.sqrt (α * t) + 1 / Real.sqrt t) := by
    simp only [neg_mul] at hfirst hsecond hthird ⊢
    nlinarith only [hfirst, hsecond, hthird, (by positivity : 0 ≤ 1 / Real.sqrt t)]
  convert mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ x * Real.exp (-α * x ^ 2 / 2)) using 1 <;> (first | rfl | ring_nf)

/-- The first Gaussian moment at an integer, normalized by height. -/
def gaussianPrimeMomentWeight (σ α ξ t : ℝ) (n : ℕ) : ℂ :=
  ((((α : ℂ) - ξ * I) / t) * (n : ℂ) ^ 2) * gaussianPrimeWeight σ α ξ t n

/-- On positive integers the first moment is the abscissa shift by two. -/
theorem gaussianPrimeMomentWeight_eq_shift (σ α ξ t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    gaussianPrimeMomentWeight σ α ξ t n =
      (((α : ℂ) - ξ * I) / t) * gaussianPrimeWeight (σ - 2) α ξ t n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : (n : ℝ) ^ (-(σ - 2)) = (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-σ) := by
    rw [show -(σ - 2) = ((2 : ℕ) : ℝ) + (-σ) by push_cast; ring,
      Real.rpow_add hn0, Real.rpow_natCast]
  unfold gaussianPrimeMomentWeight gaussianPrimeWeight
  rw [hr]
  push_cast
  ring

private theorem gaussian_moment_prefactor_le {α ξ t : ℝ}
    (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t) (hsector : ξ ≤ 2 * α * t) :
    ‖((α : ℂ) - ξ * I) / t‖ ≤ 4 * α := by
  have hξ : 0 ≤ ξ := hα.trans hαξ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply (div_le_iff₀ ht).mpr
  calc
    _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
    _ = α + ξ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hξ, Complex.norm_I, mul_one]
    _ ≤ _ := by linarith only [hαξ, hsector]

/-- Pointwise absolute bound for the first moment, retaining the abscissa power. -/
theorem norm_gaussianPrimeMomentWeight_le (σ : ℝ) {α ξ t : ℝ}
    (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t) (hsector : ξ ≤ 2 * α * t)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      4 * α * (n : ℝ) ^ (2 - σ) * Real.exp (-α * (n : ℝ) ^ 2) := by
  rw [gaussianPrimeMomentWeight_eq_shift σ α ξ t hn, norm_mul, norm_gaussianPrimeWeight_exact]
  have hh := mul_le_mul_of_nonneg_right (gaussian_moment_prefactor_le hα hαξ ht hsector)
    (by positivity : 0 ≤ (n : ℝ) ^ (-(σ - 2)) * Real.exp (-α * (n : ℝ) ^ 2))
  rw [show -(σ - 2) = 2 - σ by ring] at hh ⊢
  exact hh.trans_eq (by ring)

/-- Every dyadic prefix of the first moment retains half its Gaussian.
The estimate is uniform through the stationary point of the phase. -/
theorem norm_sum_gaussianPrimeMomentWeight_prefix_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) {P R : ℕ}
    (hP : 1 ≤ P) (hPR : P ≤ R) (hR : R ≤ 2 * P) :
    ‖∑ n ∈ Ico P R, gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      16000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (P : ℝ) ^ (1 - σ) * Real.exp (-α * (P : ℝ) ^ 2 / 2) := by
  have hξ : 0 ≤ ξ := hα.trans hαξ
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hBd : 0 ≤ gaussianWeightedTypeIBound σ α ξ t P (2 * P) := by
    simpa only [Ico_self, sum_empty, norm_zero] using
      norm_sum_gaussianPrimeWeight_prefix_le hσ hα hξ ht hP le_rfl (by omega : P ≤ 2 * P)
  have hsum : ‖∑ n ∈ Ico P R, (((n : ℝ) ^ 2 : ℝ) : ℂ) * gaussianPrimeWeight σ α ξ t n‖ ≤
      8 * (P : ℝ) ^ 2 * gaussianWeightedTypeIBound σ α ξ t P (2 * P) := by
    by_cases hlt : P < R
    · have hh := norm_sum_Ico_mul_le_of_bounded_partial_mono hlt
        (fun n => (n : ℝ) ^ 2) (gaussianPrimeWeight σ α ξ t) (sq_nonneg _)
        (fun n _ => by exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ n) 2)
        (fun k hk => norm_sum_gaussianPrimeWeight_prefix_le hσ hα hξ ht hP
          (by omega) (by omega : P + k ≤ 2 * P))
      have hsq : (((R - 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (P : ℝ) ^ 2 := by
        have hh : (((R - 1 : ℕ) : ℝ)) ^ 2 ≤ (2 * (P : ℝ)) ^ 2 := by
          exact_mod_cast Nat.pow_le_pow_left (by omega : R - 1 ≤ 2 * P) 2
        nlinarith only [hh]
      exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hsq hBd])
    · rw [Ico_eq_empty_of_le (by omega), sum_empty, norm_zero]
      positivity
  have hweight := mul_le_mul_of_nonneg_right (gaussianTypeIBound_dyadic_le hξ ht hP)
    (by positivity : 0 ≤ (P : ℝ) ^ (-σ) * Real.exp (-α * (P : ℝ) ^ 2))
  have hm := mul_le_mul (gaussian_moment_prefactor_le hα hαξ ht hsector) hsum
    (norm_nonneg _) (by positivity : 0 ≤ 4 * α)
  have hsum_eq : (∑ n ∈ Ico P R, gaussianPrimeMomentWeight σ α ξ t n) =
      (((α : ℂ) - ξ * I) / t) *
        ∑ n ∈ Ico P R, (((n : ℝ) ^ 2 : ℝ) : ℂ) * gaussianPrimeWeight σ α ξ t n := by
    simp only [gaussianPrimeMomentWeight, mul_sum, Complex.ofReal_pow, Complex.ofReal_natCast, mul_assoc]
  rw [hsum_eq, norm_mul]
  apply hm.trans
  have hpoly := mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 4 * α * (8 * (P : ℝ) ^ 2))
  change gaussianTypeIBound ξ t P (2 * P) * _ ≤ _ at hweight
  have habs := mul_le_mul_of_nonneg_left
    (gaussian_moment_curvature_absorption hα ht hP0.le hsector)
    (by positivity : 0 ≤ 3200 * (P : ℝ) ^ (-σ))
  have hp : (P : ℝ) ^ (1 - σ) = (P : ℝ) * (P : ℝ) ^ (-σ) := by
    rw [sub_eq_add_neg, Real.rpow_add hP0, Real.rpow_one]
  rw [hp]
  calc
    4 * α * (8 * (P : ℝ) ^ 2 * gaussianWeightedTypeIBound σ α ξ t P (2 * P)) ≤
        3200 * (P : ℝ) ^ (-σ) *
          (α * (P : ℝ) ^ 2 * Real.exp (-α * (P : ℝ) ^ 2) *
            ((P : ℝ) * Real.sqrt ξ + Real.sqrt t + (P : ℝ) / Real.sqrt t)) := by
      unfold gaussianWeightedTypeIBound
      convert hpoly using 1 <;> (first | rfl | ring_nf)
    _ ≤ _ := by convert habs using 1 <;> (first | rfl | ring_nf)

/-- The logarithmic coefficient costs only the endpoint logarithm. -/
theorem norm_sum_log_gaussianPrimeMomentWeight_prefix_le {σ α ξ t : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) {P R : ℕ}
    (hP : 1 ≤ P) (hPR : P ≤ R) (hR : R ≤ 2 * P) :
    ‖∑ n ∈ Ico P R, (Real.log n : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      32000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (P : ℝ) ^ (1 - σ) * Real.exp (-α * (P : ℝ) ^ 2 / 2) * Real.log (2 * (P : ℝ)) := by
  by_cases hlt : P < R
  · have hh := norm_sum_Ico_mul_le_of_bounded_partial_mono hlt (fun n => Real.log n)
      (gaussianPrimeMomentWeight σ α ξ t) (Real.log_nonneg (by exact_mod_cast hP))
      (fun n hn => Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast Nat.le_succ n))
      (fun k hk => norm_sum_gaussianPrimeMomentWeight_prefix_le hσ hα hαξ ht hsector hP
        (by omega) (by omega : P + k ≤ 2 * P))
    have hlog : Real.log ((R - 1 : ℕ) : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < R - 1 by omega)
      · exact_mod_cast (show R - 1 ≤ 2 * P by omega)
    apply hh.trans
    convert mul_le_mul_of_nonneg_left hlog
      (by positivity : 0 ≤ 2 * (16000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (P : ℝ) ^ (1 - σ) * Real.exp (-α * (P : ℝ) ^ 2 / 2))) using 1
    ring_nf
  · rw [Ico_eq_empty_of_le (by omega), sum_empty, norm_zero]
    have hlog : 0 ≤ Real.log (2 * (P : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * P by omega))
    positivity


private theorem norm_sum_Ico_one_le_of_dyadic_prefix (f : ℕ → ℂ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j)
    (hb : ∀ j R, 2 ^ j ≤ R → R ≤ 2 * 2 ^ j → ‖∑ n ∈ Ico (2 ^ j) R, f n‖ ≤ E j)
    {B K : ℕ} (hB : 1 ≤ B) (hBK : B ≤ 2 ^ K) :
    ‖∑ n ∈ Ico 1 B, f n‖ ≤ ∑ j ∈ range K, E j := by
  have hpartial : ∀ K, ‖∑ n ∈ Ico 1 (min B (2 ^ K)), f n‖ ≤ ∑ j ∈ range K, E j := by
    intro K
    induction K with
    | zero => simp [min_eq_right hB]
    | succ K ih =>
        rw [Finset.sum_range_succ]
        have hp : 2 ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        by_cases h : B ≤ 2 ^ K
        · rw [min_eq_left (h.trans hp)]
          rw [min_eq_left h] at ih
          exact ih.trans (le_add_of_nonneg_right (hE K))
        · have hK : 2 ^ K ≤ B := by omega
          rw [min_eq_right hK] at ih
          have hm : 2 ^ K ≤ min B (2 ^ (K + 1)) := le_min hK hp
          rw [← sum_Ico_consecutive f Nat.one_le_two_pow hm]
          refine (norm_add_le _ _).trans (add_le_add ih ?_)
          apply hb K _ hm
          exact (min_le_right _ _).trans_eq (by ring)
  simpa only [min_eq_left hBK] using hpartial K

private theorem gaussianMoment_dyadic_scale (σ α : ℝ) (j : ℕ) :
    ((2 ^ j : ℕ) : ℝ) ^ (1 - σ) * Real.exp (-α * (((2 ^ j : ℕ) : ℝ)) ^ 2 / 2) =
      ((2 : ℝ) ^ (1 - σ)) ^ j * Real.exp (-α * (4 : ℝ) ^ j / 2) := by
  have hp : (((2 ^ j : ℕ) : ℝ)) ^ 2 = (4 : ℝ) ^ j := by
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [hp, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
    mul_comm (j : ℝ), Real.rpow_mul_natCast (by norm_num)]

private theorem gaussianMoment_dyadic_log_le (j : ℕ) :
    Real.log (2 * (((2 ^ j : ℕ) : ℝ))) ≤ ((j : ℝ) + 1) ^ 4 := by
  have hl : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hp : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 4 := by nlinarith only [hj, sq_nonneg (((j : ℝ) + 1) ^ 2 - 1)]
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (j : ℝ) + 1)
  exact (by nlinarith only [hh] : Real.log 2 + (j : ℝ) * Real.log 2 ≤ (j : ℝ) + 1).trans hp

private theorem norm_sum_initial_le_of_gaussian_dyadic_prefix {σ α X C : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hX : 1 ≤ X) (hscale : 2 ≤ α * X ^ 2) (f : ℕ → ℂ)
    (hb : ∀ (j R : ℕ), 2 ^ j ≤ R → R ≤ 2 * 2 ^ j →
      ‖∑ n ∈ Ico (2 ^ j) R, f n‖ ≤
        C * (((2 : ℝ) ^ (1 - σ)) ^ j * ((j : ℝ) + 1) ^ 4 *
          Real.exp (-α * (4 : ℝ) ^ j / 2)))
    {B : ℕ} (hB : 1 ≤ B) :
    ‖∑ n ∈ Ico 1 B, f n‖ ≤
      2 * C * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
        (2 + Real.log X / Real.log 2) ^ 4 := by
  obtain ⟨R, hR, hp⟩ := exists_gaussianMoment_physical_scale hσ hσ1 hα hX hscale
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hq2 : (2 : ℝ) ^ (1 - σ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith only [hσ] : 1 - σ ≤ 1)
  have hs := norm_sum_Ico_one_le_of_dyadic_prefix f _
    (fun j => by positivity) hb hB (Nat.lt_two_pow_self (n := B)).le
  have hseries := sum_dyadic_gaussian_fourth_le hq hq2 hα R B hR
  have hp' := mul_le_mul_of_nonneg_left hp
    (by positivity : 0 ≤ C * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12))
  apply hs.trans
  rw [← mul_sum]
  calc
    _ ≤ C * ((1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
          ((2 : ℝ) ^ (1 - σ)) ^ R * ((R : ℝ) + 1) ^ 4) :=
      mul_le_mul_of_nonneg_left hseries hC
    _ ≤ _ := by convert hp' using 1 <;> (first | rfl | ring)

/-- Uniform bound for an arbitrary initial segment of the first moment. -/
theorem norm_sum_gaussianPrimeMomentWeight_initial_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hX : 1 ≤ X) (hscale : 2 ≤ α * X ^ 2)
    {B : ℕ} (hB : 1 ≤ B) :
    ‖∑ n ∈ Ico 1 B, gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      32000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
          (2 + Real.log X / Real.log 2) ^ 4 := by
  have hb (j R : ℕ) (hj : 2 ^ j ≤ R) (hR : R ≤ 2 * 2 ^ j) :
      ‖∑ n ∈ Ico (2 ^ j) R, gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        (16000 * (Real.sqrt (α * t) + 1 / Real.sqrt t)) *
          (((2 : ℝ) ^ (1 - σ)) ^ j * ((j : ℝ) + 1) ^ 4 * Real.exp (-α * (4 : ℝ) ^ j / 2)) := by
    apply (norm_sum_gaussianPrimeMomentWeight_prefix_le hσ hα hαξ ht hsector Nat.one_le_two_pow hj hR).trans
    have hi : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)] : (1 : ℝ) ≤ (j : ℝ) + 1)
    have hh := mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ 16000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (((2 : ℝ) ^ (1 - σ)) ^ j * Real.exp (-α * (4 : ℝ) ^ j / 2)))
    rw [mul_assoc (16000 * _) _ _, gaussianMoment_dyadic_scale]
    convert hh using 1 <;> (first | rfl | ring)
  convert norm_sum_initial_le_of_gaussian_dyadic_prefix hσ hσ1 hα
    (by positivity) hX hscale _ hb hB using 1
  ring

/-- A logarithmic coefficient has the same truncation-uniform Gaussian envelope. -/
theorem norm_sum_log_gaussianPrimeMomentWeight_initial_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hX : 1 ≤ X) (hscale : 2 ≤ α * X ^ 2)
    {B : ℕ} (hB : 1 ≤ B) :
    ‖∑ n ∈ Ico 1 B, (Real.log n : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
      64000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) * X ^ (1 - σ) *
          (2 + Real.log X / Real.log 2) ^ 4 := by
  have hb (j R : ℕ) (hj : 2 ^ j ≤ R) (hR : R ≤ 2 * 2 ^ j) :
      ‖∑ n ∈ Ico (2 ^ j) R, (Real.log n : ℂ) * gaussianPrimeMomentWeight σ α ξ t n‖ ≤
        (32000 * (Real.sqrt (α * t) + 1 / Real.sqrt t)) *
          (((2 : ℝ) ^ (1 - σ)) ^ j * ((j : ℝ) + 1) ^ 4 * Real.exp (-α * (4 : ℝ) ^ j / 2)) := by
    apply (norm_sum_log_gaussianPrimeMomentWeight_prefix_le hσ hα hαξ ht hsector Nat.one_le_two_pow hj hR).trans
    have hh := mul_le_mul_of_nonneg_left (gaussianMoment_dyadic_log_le j)
      (by positivity : 0 ≤ 32000 * (Real.sqrt (α * t) + 1 / Real.sqrt t) *
        (((2 : ℝ) ^ (1 - σ)) ^ j * Real.exp (-α * (4 : ℝ) ^ j / 2)))
    rw [mul_assoc (32000 * _) _ _, gaussianMoment_dyadic_scale]
    convert hh using 1
    ring
  convert norm_sum_initial_le_of_gaussian_dyadic_prefix hσ hσ1 hα
    (by positivity) hX hscale _ hb hB using 1
  ring

private theorem norm_sum_Ico_le_of_initial_bound (f : ℕ → ℂ) {L : ℝ}
    (hb : ∀ B, 1 ≤ B → ‖∑ n ∈ Ico 1 B, f n‖ ≤ L)
    {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) : ‖∑ n ∈ Ico A B, f n‖ ≤ 2 * L := by
  by_cases hAB : A ≤ B
  · have he : (∑ n ∈ Ico A B, f n) = (∑ n ∈ Ico 1 B, f n) - ∑ n ∈ Ico 1 A, f n := by
      rw [← sum_Ico_consecutive f hA hAB]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith only [hb B hB, hb A hA])
  · rw [Ico_eq_empty_of_le (by omega), sum_empty, norm_zero]
    have hL : 0 ≤ L := by simpa only [Ico_self, sum_empty, norm_zero] using hb 1 le_rfl
    positivity

/-- Dilation rescales damping and rotation together; its scalar has modulus `b⁻σ`. -/
theorem gaussianPrimeMomentWeight_dilate (σ α ξ t : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gaussianPrimeMomentWeight σ α ξ t (a * b) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        gaussianPrimeMomentWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
  unfold gaussianPrimeMomentWeight
  rw [gaussianPrimeWeight_dilate σ α ξ t ha hb]
  push_cast
  ring

private theorem gaussianMoment_dilation_scalar_norm (σ t : ℝ) (b : ℕ) :
    ‖((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I))‖ =
      (b : ℝ) ^ (-σ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b) _)]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    Real.exp_zero, mul_one]

private theorem gaussianMoment_dilated_scale_bound {σ α t X b : ℝ}
    (ht : 0 < t)
    (hb : 1 ≤ b) (hbX : b ≤ X) :
    b ^ (-σ) * (Real.sqrt (α * b ^ 2 * t) + 1 / Real.sqrt t) *
      (X / b) ^ (1 - σ) * (2 + Real.log (X / b) / Real.log 2) ^ 4 ≤
    (Real.sqrt (α * t) + 1 / (b * Real.sqrt t)) *
      X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hX0 : 0 < X := hb0.trans_le hbX
  have hscale : 1 ≤ X / b := (le_div_iff₀ hb0).mpr (by simpa using hbX)
  have hp : b ^ (-σ) * (X / b) ^ (1 - σ) = X ^ (1 - σ) / b := by
    have he : b ^ (1 - σ) = b * b ^ (-σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hb0, Real.rpow_one]
    rw [Real.div_rpow hX0.le hb0.le, he]
    field_simp [hb0.ne', (Real.rpow_pos_of_pos hb0 (-σ)).ne']
  have hs : Real.sqrt (α * b ^ 2 * t) = b * Real.sqrt (α * t) := by
    rw [show α * b ^ 2 * t = b ^ 2 * (α * t) by ring,
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hb0]
  have he : b ^ (-σ) * (Real.sqrt (α * b ^ 2 * t) + 1 / Real.sqrt t) *
      (X / b) ^ (1 - σ) =
      (Real.sqrt (α * t) + 1 / (b * Real.sqrt t)) * X ^ (1 - σ) := by
    calc
      _ = (b ^ (-σ) * (X / b) ^ (1 - σ)) *
          (Real.sqrt (α * b ^ 2 * t) + 1 / Real.sqrt t) := by ring
      _ = _ := by rw [hp, hs]; field_simp [hb0.ne', (Real.sqrt_pos.mpr ht).ne']
  have hlog : 2 + Real.log (X / b) / Real.log 2 ≤ 2 + Real.log X / Real.log 2 := by
    apply _root_.add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    apply Real.log_le_log (by positivity)
    exact (div_le_iff₀ hb0).mpr (by nlinarith only [hb, hX0])
  have hlog0 : 0 ≤ 2 + Real.log (X / b) / Real.log 2 := by
    have hh := Real.log_nonneg hscale
    positivity
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 4) (by positivity)

/-- Every divisor fibre has a uniform bound with its reciprocal-divisor saving retained. -/
theorem norm_sum_gaussianPrimeMomentWeight_dilate_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hscale : 2 ≤ α * X ^ 2)
    {A B b : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hb : 1 ≤ b) (hbX : (b : ℝ) ≤ X) :
    ‖∑ a ∈ Ico A B, gaussianPrimeMomentWeight σ α ξ t (a * b)‖ ≤
      64000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
        (Real.sqrt (α * t) + 1 / ((b : ℝ) * Real.sqrt t)) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hX : 1 ≤ X / b := (le_div_iff₀ hb0).mpr (by simpa using hbX)
  have hscale' : 2 ≤ (α * (b : ℝ) ^ 2) * (X / b) ^ 2 := by
    convert hscale using 1
    field_simp [hb0.ne']
  have hsector' : ξ * (b : ℝ) ^ 2 ≤ 2 * (α * (b : ℝ) ^ 2) * t := by
    have hh := mul_le_mul_of_nonneg_right hsector (sq_nonneg (b : ℝ))
    nlinarith only [hh]
  have hinner := norm_sum_Ico_le_of_initial_bound
    (gaussianPrimeMomentWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t)
    (fun B' hB' => norm_sum_gaussianPrimeMomentWeight_initial_le hσ hσ1
      (by positivity) (mul_le_mul_of_nonneg_right hαξ (sq_nonneg _)) ht hsector' hX hscale' hB') hA hB
  have he : (∑ a ∈ Ico A B, gaussianPrimeMomentWeight σ α ξ t (a * b)) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        ∑ a ∈ Ico A B, gaussianPrimeMomentWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
    rw [mul_sum]
    exact sum_congr rfl fun a ha => gaussianPrimeMomentWeight_dilate σ α ξ t
      (hA.trans (mem_Ico.mp ha).1) hb
  rw [he, norm_mul, gaussianMoment_dilation_scalar_norm]
  apply (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (b : ℝ) ^ (-σ))).trans
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hm := mul_le_mul_of_nonneg_left (gaussianMoment_dilated_scale_bound (σ := σ) (α := α) ht hb1 hbX)
    (by positivity : 0 ≤ 64000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12))
  convert hm using 1 <;> (first | rfl | ring)

/-- The logarithmic divisor fibre satisfies the same reciprocal-divisor estimate. -/
theorem norm_sum_log_gaussianPrimeMomentWeight_dilate_le {σ α ξ t X : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hα : 0 ≤ α) (hαξ : α ≤ ξ) (ht : 0 < t)
    (hsector : ξ ≤ 2 * α * t) (hscale : 2 ≤ α * X ^ 2)
    {A B b : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hb : 1 ≤ b) (hbX : (b : ℝ) ≤ X) :
    ‖∑ a ∈ Ico A B, (Real.log a : ℂ) * gaussianPrimeMomentWeight σ α ξ t (a * b)‖ ≤
      128000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12) *
        (Real.sqrt (α * t) + 1 / ((b : ℝ) * Real.sqrt t)) *
          X ^ (1 - σ) * (2 + Real.log X / Real.log 2) ^ 4 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hX : 1 ≤ X / b := (le_div_iff₀ hb0).mpr (by simpa using hbX)
  have hscale' : 2 ≤ (α * (b : ℝ) ^ 2) * (X / b) ^ 2 := by
    convert hscale using 1
    field_simp [hb0.ne']
  have hsector' : ξ * (b : ℝ) ^ 2 ≤ 2 * (α * (b : ℝ) ^ 2) * t := by
    have hh := mul_le_mul_of_nonneg_right hsector (sq_nonneg (b : ℝ))
    nlinarith only [hh]
  have hinner := norm_sum_Ico_le_of_initial_bound
    (fun a => (Real.log a : ℂ) * gaussianPrimeMomentWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a)
    (fun B' hB' => norm_sum_log_gaussianPrimeMomentWeight_initial_le hσ hσ1
      (by positivity) (mul_le_mul_of_nonneg_right hαξ (sq_nonneg _)) ht hsector' hX hscale' hB') hA hB
  have he : (∑ a ∈ Ico A B, (Real.log a : ℂ) * gaussianPrimeMomentWeight σ α ξ t (a * b)) =
      ((((b : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-t * Real.log b : ℝ) : ℂ) * I)) *
        ∑ a ∈ Ico A B, (Real.log a : ℂ) * gaussianPrimeMomentWeight σ (α * (b : ℝ) ^ 2) (ξ * (b : ℝ) ^ 2) t a := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [gaussianPrimeMomentWeight_dilate σ α ξ t (hA.trans (mem_Ico.mp ha).1) hb]
    ring
  rw [he, norm_mul, gaussianMoment_dilation_scalar_norm]
  apply (mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (b : ℝ) ^ (-σ))).trans
  have hq : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  have hm := mul_le_mul_of_nonneg_left (gaussianMoment_dilated_scale_bound (σ := σ) (α := α) ht hb1 hbX)
    (by positivity : 0 ≤ 128000 * (1 / ((2 : ℝ) ^ (1 - σ) - 1) + 12))
  convert hm using 1 <;> (first | rfl | ring)

#print axioms gaussianTypeIBound_dyadic_le
#print axioms gaussian_moment_curvature_absorption
#print axioms norm_gaussianPrimeMomentWeight_le
#print axioms gaussianPrimeMomentWeight_eq_shift
#print axioms norm_sum_gaussianPrimeMomentWeight_prefix_le
#print axioms norm_sum_log_gaussianPrimeMomentWeight_prefix_le
#print axioms norm_sum_gaussianPrimeMomentWeight_initial_le
#print axioms norm_sum_log_gaussianPrimeMomentWeight_initial_le
#print axioms gaussianPrimeMomentWeight_dilate
#print axioms norm_sum_gaussianPrimeMomentWeight_dilate_le
#print axioms norm_sum_log_gaussianPrimeMomentWeight_dilate_le

end GaloisForLFunctions.ExceptionalLayerTheory
