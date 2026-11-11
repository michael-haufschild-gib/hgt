import GaloisForLFunctions.MultiscaleMollifiedZetaField.TwistedSecondMomentsBelowSquareRoot
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Holomorphic displacement in the two twisted-moment main terms

The two finite gcd sums are exponential polynomials in the displacement.
The residue factor bounds zeta near its pole, and the chi-modulus formula
bounds the reflected weight on a fixed complex strip.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The common finite gcd polynomial in its two complex exponents. -/
def holomorphicGcdSum (a b : ℂ) (N : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
    (w h : ℂ) * (w k : ℂ) *
      Complex.exp (a * (Real.log ((h : ℝ) * k) : ℂ) +
        b * (Real.log (reducedProd h k) : ℂ))

private theorem reducedProd_pos {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    0 < reducedProd h k :=
  Nat.mul_pos (gcd_facts hh hk).2.1 (gcd_facts hh hk).2.2.1

/-- Nonpositive real exponents bound either gcd sum by the number of coefficient pairs. -/
theorem norm_holomorphicGcdSum_le {a b : ℂ} (ha : a.re ≤ 0) (hb : b.re ≤ 0)
    {N : ℕ} {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) :
    ‖holomorphicGcdSum a b N w‖ ≤ (N : ℝ) ^ 2 := by
  unfold holomorphicGcdSum
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ‖(w h : ℂ) * (w k : ℂ) * Complex.exp
          (a * (Real.log ((h : ℝ) * k) : ℂ) +
            b * (Real.log (reducedProd h k) : ℂ))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hhk : 1 ≤ (h : ℝ) * k := by nlinarith only [hh1, hk1]
      have hr : (1 : ℝ) ≤ reducedProd h k := by
        exact_mod_cast reducedProd_pos (by omega : 0 < h) (by omega : 0 < k)
      have hlog₁ := Real.log_nonneg hhk
      have hlog₂ := Real.log_nonneg hr
      have hexp : ‖Complex.exp (a * (Real.log ((h : ℝ) * k) : ℂ) +
          b * (Real.log (reducedProd h k) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp, Real.exp_le_one_iff]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg ha hlog₁)
          (mul_nonpos_of_nonpos_of_nonneg hb hlog₂)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hcoeff : |w h| * |w k| ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hw h hh) (hw k hk) (abs_nonneg _) zero_le_one
      simpa only [one_mul] using mul_le_mul hcoeff hexp (norm_nonneg _) zero_le_one
    _ = _ := by simp [pow_two]

private theorem holomorphicGcdSum_ofReal (a b : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    holomorphicGcdSum (a : ℂ) (b : ℂ) N w =
      ((∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        w h * w k * (((h : ℝ) * k) ^ a * (reducedProd h k : ℝ) ^ b) : ℝ) : ℂ) := by
  unfold holomorphicGcdSum
  push_cast
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hr0 : (0 : ℝ) < reducedProd h k := by
    exact_mod_cast reducedProd_pos (by omega : 0 < h) (by omega : 0 < k)
  rw [Real.rpow_def_of_pos (mul_pos hh0 hk0), Real.rpow_def_of_pos hr0,
    Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_mul]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The complex gcd polynomials restrict to the two literal main-term gcd sums. -/
theorem holomorphicGcdSum_direct_ofReal (d : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    holomorphicGcdSum ((d : ℂ) - 1 / 2) ((d : ℂ) - 1 / 2) N w =
      (gcdSum₁ d N w : ℂ) := by
  have he : (d : ℂ) - 1 / 2 = ((-(1 / 2 - d) : ℝ) : ℂ) := by push_cast; ring
  rw [he, holomorphicGcdSum_ofReal]
  rfl

theorem holomorphicGcdSum_reflected_ofReal (d : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    holomorphicGcdSum ((d : ℂ) - 1 / 2) (-(d : ℂ) - 1 / 2) N w =
      (gcdSum₂ d N w : ℂ) := by
  have he : (d : ℂ) - 1 / 2 = ((-(1 / 2 - d) : ℝ) : ℂ) := by push_cast; ring
  have he' : -(d : ℂ) - 1 / 2 = ((-(1 / 2 + d) : ℝ) : ℂ) := by push_cast; ring
  rw [he, he', holomorphicGcdSum_ofReal]
  rfl

/-- Clearing the pole gives a uniform inverse-distance bound on a fixed disk. -/
theorem exists_norm_riemannZeta_le_div_dist_one :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, ‖s - 1‖ ≤ 1 → s ≠ 1 →
      ‖riemannZeta s‖ ≤ C / ‖s - 1‖ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_zetaResidueFactor.continuous.continuousOn
  have hC1 := hC 1 (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  simp only [zetaResidueFactor_one, norm_one] at hC1
  refine ⟨C, hC1, fun s hs hne => ?_⟩
  have hh := hC s (by simpa only [mem_closedBall, dist_eq_norm] using hs)
  rw [zetaResidueFactor_of_ne hne, norm_mul] at hh
  exact (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).mpr
    (by simpa only [mul_comm] using hh)

private theorem norm_zetaChi_displaced_le {d τ : ℝ} (hd : 0 ≤ d) (hd4 : d ≤ 1 / 4)
    (hτ : 2 ≤ τ) :
    ‖zetaChi (displacedLinePt d τ)‖ ≤ Real.exp 1 * (τ + 1) := by
  have hτ0 : 0 < τ := by linarith only [hτ]
  obtain ⟨e, he, heq⟩ := exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp hd hd4 hτ0
  have hπ : Real.pi / τ ≤ 2 := (div_le_iff₀ hτ0).mpr (by linarith only [hτ, Real.pi_le_four])
  have hsq : (4 : ℝ) ≤ τ ^ 2 := by nlinarith only [hτ]
  have h5 : 5 / τ ^ 2 ≤ 5 / 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
  have hm := mul_le_mul hd4 (add_le_add hπ h5) (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have he1 : e ≤ 1 := by have hh := (abs_le.mp he).2; linarith only [hh, hm]
  have hw : chiModulusWeight d τ ≤ τ + 1 := by
    unfold chiModulusWeight
    have hb : τ / (2 * Real.pi) ≤ τ + 1 :=
      (div_le_self hτ0.le (by linarith only [Real.pi_gt_three])).trans (by linarith)
    calc
      _ ≤ (τ + 1) ^ d := Real.rpow_le_rpow (by positivity) hb hd
      _ ≤ (τ + 1) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by linarith only [hτ]) (by linarith only [hd4])
      _ = _ := Real.rpow_one _
  rw [heq]
  have hh := mul_le_mul hw (Real.exp_le_exp.mpr he1) (Real.exp_pos _).le
    (by linarith only [hτ] : 0 ≤ τ + 1)
  simpa only [mul_comm] using hh

private theorem norm_zetaChi_displaced_le_abs {d τ : ℝ} (hd : 0 ≤ d) (hd4 : d ≤ 1 / 4)
    (hτ : 2 ≤ |τ|) :
    ‖zetaChi (displacedLinePt d τ)‖ ≤ Real.exp 1 * (|τ| + 1) := by
  have he : ‖zetaChi (displacedLinePt d τ)‖ = ‖zetaChi (displacedLinePt d |τ|)‖ := by
    rcases le_total 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, displacedLinePt_neg_eq_conj, zetaChi_conj, Complex.norm_conj]
  rw [he]
  exact norm_zetaChi_displaced_le hd hd4 hτ

private theorem norm_complex_displaced_chi_le {z : ℂ} (hz0 : 0 ≤ z.re) (hz4 : z.re ≤ 1 / 4)
    (hzim : |z.im| ≤ 1) {t : ℝ} (ht : 4 ≤ |t|) :
    ‖zetaChi ((1 / 2 : ℂ) - z + (t : ℂ) * I)‖ ≤ Real.exp 1 * (|t| + 2) := by
  have he : (1 / 2 : ℂ) - z + (t : ℂ) * I = displacedLinePt z.re (t - z.im) := by
    apply Complex.ext <;> simp [displacedLinePt] <;> ring
  have hτ : 2 ≤ |t - z.im| := by
    have hh := abs_add_le (t - z.im) z.im
    rw [sub_add_cancel] at hh
    linarith only [hh, hzim, ht]
  have hτup := (abs_sub t z.im).trans (add_le_add (le_refl |t|) hzim)
  rw [he]
  refine (norm_zetaChi_displaced_le_abs hz0 hz4 hτ).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  linarith only [hτup]

/-- Opposite-height chi factors with complex displacement. -/
def holomorphicChiPair (z : ℂ) (t : ℝ) : ℂ :=
  zetaChi ((1 / 2 : ℂ) - z + (t : ℂ) * I) *
    zetaChi ((1 / 2 : ℂ) - z - (t : ℂ) * I)

/-- The two actual main terms, continued in the displacement. -/
def holomorphicTwistedMomentMain (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (z : ℂ) : ℂ :=
  holomorphicGcdSum (z - 1 / 2) (z - 1 / 2) N w *
      (riemannZeta (1 - 2 * z) * ∫ t, blockWindowC p q η t) +
    holomorphicGcdSum (z - 1 / 2) (-z - 1 / 2) N w *
      (riemannZeta (1 + 2 * z) * ∫ t, blockWindowC p q η t * holomorphicChiPair z t)

theorem holomorphicChiPair_ofReal (d t : ℝ) :
    holomorphicChiPair (d : ℂ) t = chiPairWeight d t := by
  unfold holomorphicChiPair chiPairWeight displacedLinePt
  push_cast
  congr 2 <;> ring

/-- The continued expression agrees with the given two-main-term formula. -/
theorem holomorphicTwistedMomentMain_ofReal (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (d : ℝ) :
    holomorphicTwistedMomentMain p q η N w (d : ℂ) = twistedMomentMain d p q η N w := by
  unfold holomorphicTwistedMomentMain twistedMomentMain
  rw [holomorphicGcdSum_direct_ofReal, holomorphicGcdSum_reflected_ofReal]
  simp_rw [holomorphicChiPair_ofReal]
  congr 3 <;> push_cast <;> ring

private theorem norm_holomorphicChiPair_le {z : ℂ} (hz0 : 0 ≤ z.re) (hz4 : z.re ≤ 1 / 4)
    (hzim : |z.im| ≤ 1) {t : ℝ} (ht : 4 ≤ |t|) :
    ‖holomorphicChiPair z t‖ ≤ (Real.exp 1 * (|t| + 2)) ^ 2 := by
  have he : (1 / 2 : ℂ) - z - (t : ℂ) * I = (1 / 2 : ℂ) - z + ((-t : ℝ) : ℂ) * I := by
    push_cast; ring
  unfold holomorphicChiPair
  rw [he, norm_mul]
  have hp := norm_complex_displaced_chi_le hz0 hz4 hzim ht
  have hm := norm_complex_displaced_chi_le hz0 hz4 hzim (show 4 ≤ |-t| by simpa using ht)
  simp only [abs_neg] at hm
  simpa only [pow_two] using mul_le_mul hp hm (norm_nonneg _) (by positivity)

private theorem chi_kernel_bound {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz4 : z.re ≤ 1 / 4) (hzim : |z.im| ≤ 1) (t : ℝ) :
    ‖blockWindowC p q η t * holomorphicChiPair z t‖ ≤
      blockWindow p q η t * (Real.exp 1 * (q + η + 2)) ^ 2 := by
  by_cases ht : t ∈ Icc (p - η) (q + η)
  · have ht0 : 0 ≤ t := by linarith only [hp, ht.1]
    have hh := norm_holomorphicChiPair_le hz0 hz4 hzim
      (show 4 ≤ |t| by rw [abs_of_nonneg ht0]; exact hp.trans ht.1)
    have hscale : Real.exp 1 * (|t| + 2) ≤ Real.exp 1 * (q + η + 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [abs_of_nonneg ht0]
      linarith only [ht.2]
    rw [norm_mul, norm_blockWindowC_eq]
    exact mul_le_mul_of_nonneg_left
      (hh.trans (pow_le_pow_left₀ (by positivity) hscale 2)) (blockWindow_nonneg p q η t)
  · rw [blockWindowC_eq_zero hη ht]
    have hzero : blockWindow p q η t = 0 := by
      by_contra hn
      exact ht (support_blockWindow_subset hη hn)
    simp only [hzero, zero_mul, norm_zero, le_refl]

/-- The reflected integral has a polynomial bound uniform in the complex displacement strip. -/
theorem norm_integral_holomorphicChiPair_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q)
    (hp : 4 ≤ p - η) {z : ℂ} (hz0 : 0 ≤ z.re) (hz4 : z.re ≤ 1 / 4) (hzim : |z.im| ≤ 1) :
    ‖∫ t, blockWindowC p q η t * holomorphicChiPair z t‖ ≤
      (q - p + 2 * η) * (Real.exp 1 * (q + η + 2)) ^ 2 := by
  have hW : Integrable (blockWindow p q η) volume :=
    (contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_blockWindow hη)
  have hh := norm_integral_le_of_norm_le (hW.mul_const ((Real.exp 1 * (q + η + 2)) ^ 2))
    (Eventually.of_forall (chi_kernel_bound hη hp hz0 hz4 hzim))
  refine hh.trans ?_
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_blockWindow_le hη hpq) (sq_nonneg _)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
