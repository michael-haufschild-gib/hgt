import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RHTower.EvenIndexHermitianPoleRecurrence
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!
# Unconditional positive recurrence of the binary Liouville additive correlation

The exponential profile `Λ x = ∑ λ(n) e^{-n x}` cannot stay bounded at the origin
(`not_isBigO_liouvilleProfile`).  Boundedness would make its Mellin transform analytic on
`Re s > 0`; dividing by `Γ` and clearing both zeta poles with the entire multiple
`zetaEntire s = (s - 1) ζ s` turns the closed form `L ↗λ s * ζ s = ζ (2 s)` into an identity of two
functions analytic on the whole half-plane, which the identity theorem propagates to `s = 1/2`.
There the left side vanishes while the right side is minus half the residue of `ζ` at `1`, a
contradiction.

Radial blow-up then feeds the even-index parity law: the real parts of the even-index Hermitian
convolution powers are positive at cofinally many indices, and at the binary order the coefficients
are integers, giving the unconditional sign-majority statement

`1 ≤ ∑_{a + b = 2q} λ(a) λ(b)` for infinitely many `q`
(`frequently_one_le_liouvilleBinaryCorrelation`).
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped LSeries.notation Topology BigOperators

namespace RHTower

noncomputable section

/-- The exponential profile of the Liouville coefficients. -/
noncomputable def liouvilleProfile : ℝ → ℂ :=
  GaloisForLFunctions.HTGeometry.coeffLaplaceProfile (fun n : ℕ => liouvilleC n)

theorem liouvilleC_zero : (fun n : ℕ => liouvilleC n) 0 = 0 := by
  simp

/-- The entire multiple of zeta takes the value of the residue at the pole. -/
theorem zetaEntire_one : zetaEntire 1 = 1 := by
  have hcont : ContinuousAt zetaEntire 1 := (differentiable_zetaEntire 1).continuousAt
  have h1 : Tendsto zetaEntire (𝓝[≠] (1 : ℂ)) (𝓝 (zetaEntire 1)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ))
      (𝓝 (zetaEntire 1)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact zetaEntire_eq hs
  exact tendsto_nhds_unique h2 riemannZeta_residue_one

theorem convex_decayHalfPlane (b : ℝ) : Convex ℝ {s : ℂ | b < s.re} := by
  intro x hx y hy u v hu hv huv
  have hx' : b < x.re := hx
  have hy' : b < y.re := hy
  show b < (u • x + v • y).re
  rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
  simp only [smul_eq_mul]
  rcases lt_or_ge 0 u with hu0 | hu0
  · have h1 : u * b < u * x.re := mul_lt_mul_of_pos_left hx' hu0
    have h2 : v * b ≤ v * y.re := mul_le_mul_of_nonneg_left hy'.le hv
    have h3 : u * b + v * b = b := by rw [← add_mul, huv, one_mul]
    linarith
  · have hu' : u = 0 := le_antisymm hu0 hu
    have hv' : v = 1 := by linarith
    rw [hu', hv']
    linarith

/-- **The Liouville exponential profile is unbounded at the origin.**  A bounded profile would
continue `Γ · L ↗λ` holomorphically past the structural pole of `ζ(2s)` at `s = 1/2`. -/
theorem not_isBigO_liouvilleProfile :
    ¬ (liouvilleProfile =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(0 : ℝ))) := by
  intro hO
  have hb : ∀ n : ℕ, ‖liouvilleC n‖ ≤ 1 := norm_liouvilleC_le_one
  have hint : LocallyIntegrableOn liouvilleProfile (Ioi 0) volume :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_locallyIntegrableOn hb
  have htop : liouvilleProfile =O[atTop] fun x : ℝ => Real.exp (-1 * x) :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_isBigO_exp_neg hb liouvilleC_zero
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_decayHalfPlane 0).isPreconnected
  have hnotpole : ∀ s ∈ U, ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro s hs m hcon
    have hsre : 0 < s.re := hs
    rw [hcon] at hsre
    simp at hsre
    linarith
  have hGammaDiff : ∀ s ∈ U, DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s (hnotpole s hs)
  have hGammaNe : ∀ s ∈ U, Complex.Gamma s ≠ 0 := fun s hs =>
    Complex.Gamma_ne_zero (hnotpole s hs)
  have hMellinDiff : ∀ s ∈ U, DifferentiableAt ℂ (mellin liouvilleProfile) s := by
    intro s hs
    exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0) (by norm_num)
      hint htop hO hs
  set G : ℂ → ℂ := fun s => mellin liouvilleProfile s / Complex.Gamma s with hGdef
  have hGdiff : ∀ s ∈ U, DifferentiableAt ℂ G s := fun s hs =>
    (hMellinDiff s hs).div (hGammaDiff s hs) (hGammaNe s hs)
  have hlin : Differentiable ℂ fun s : ℂ => 2 * s - 1 := by fun_prop
  have hlin' : Differentiable ℂ fun s : ℂ => s - 1 := by fun_prop
  have hF1 : AnalyticOnNhd ℂ (fun s : ℂ => (2 * s - 1) * G s * zetaEntire s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    exact (((hlin s).mul (hGdiff s hs)).mul (differentiable_zetaEntire s)).differentiableWithinAt
  have hF2 : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * zetaEntire (2 * s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    have h2 : DifferentiableAt ℂ (fun s : ℂ => zetaEntire (2 * s)) s :=
      (differentiable_zetaEntire (2 * s)).comp s (by fun_prop)
    exact ((hlin' s).mul h2).differentiableWithinAt
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2V : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have hagree : (fun s : ℂ => (2 * s - 1) * G s * zetaEntire s)
      =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ => (s - 1) * zetaEntire (2 * s) := by
    filter_upwards [hVopen.mem_nhds h2V] with s hs
    have hs1 : (1 : ℝ) < s.re := hs
    have hsU : s ∈ U := by
      have : (0 : ℝ) < s.re := by linarith
      exact this
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have h2sne : 2 * s ≠ 1 := by
      intro h
      have hre : (2 * s).re = (1 : ℂ).re := by rw [h]
      rw [Complex.mul_re] at hre
      simp at hre
      linarith
    have hmel := GaloisForLFunctions.HTGeometry.mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
      hb liouvilleC_zero hs1
    have hGs : G s = LSeries (fun n : ℕ => liouvilleC n) s := by
      rw [hGdef]
      simp only [liouvilleProfile] at *
      rw [hmel, mul_comm, mul_div_assoc, div_self (hGammaNe s hsU), mul_one]
    have hLz := LSeries_liouvilleC_mul_riemannZeta hs1
    rw [hGs, zetaEntire_eq hsne, zetaEntire_eq h2sne]
    linear_combination ((2 * s - 1) * (s - 1)) * hLz
  have h2U : (2 : ℂ) ∈ U := by
    show (0 : ℝ) < (2 : ℂ).re
    simp
  have hhalfU : ((1 : ℂ) / 2) ∈ U := by
    show (0 : ℝ) < ((1 : ℂ) / 2).re
    simp
  have heq := hF1.eqOn_of_preconnected_of_eventuallyEq hF2 hUconn h2U hagree
  have hhalf := heq hhalfU
  simp only at hhalf
  rw [show (2 : ℂ) * (1 / 2) - 1 = 0 by ring, zero_mul, zero_mul,
    show (2 : ℂ) * (1 / 2) = 1 by ring, zetaEntire_one] at hhalf
  norm_num at hhalf

/-- Radial blow-up of the Liouville Abel series at the boundary of the unit disc. -/
theorem exists_norm_gt_liouville (B : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ B < ‖∑' N : ℕ, liouvilleC N * (r : ℂ) ^ N‖ :=
  exists_norm_gt_of_not_isBigO (fun n : ℕ => liouvilleC n)
    (Af := liouvilleProfile)
    (fun x => GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x)
    not_isBigO_liouvilleProfile B

/-- **Even-index sign recurrence for Liouville.**  For every `k ≥ 1` the real parts of the
even-index Hermitian `2k`-fold additive convolution powers of the Liouville coefficients are
positive at infinitely many indices. -/
theorem frequently_re_pos_liouville {k : ℕ} (hk : 1 ≤ k) :
    ∃ᶠ q in atTop, 0 < (mixedAdditiveConvolutionPower (fun n : ℕ => liouvilleC n) k (2 * q)).re :=
  frequently_re_pos_of_norm_unbounded _ hk
    (fun _r hr0 hr1 => GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      norm_liouvilleC_le_one hr0 hr1)
    exists_norm_gt_liouville

/-- The ordered binary additive Liouville correlation at a total. -/
def liouvilleBinaryCorrelation (N : ℕ) : ℤ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    ArithmeticFunction.liouville ab.1 * ArithmeticFunction.liouville ab.2

theorem mixedAdditiveConvolutionPower_liouville_eq (N : ℕ) :
    mixedAdditiveConvolutionPower (fun n : ℕ => liouvilleC n) 1 N
      = ((liouvilleBinaryCorrelation N : ℤ) : ℂ) := by
  rw [mixedAdditiveConvolutionPower_one, liouvilleBinaryCorrelation]
  push_cast
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [conj_liouvilleC, liouvilleC_apply, liouvilleC_apply]

theorem mixedAdditiveConvolutionPower_liouville_re (N : ℕ) :
    (mixedAdditiveConvolutionPower (fun n : ℕ => liouvilleC n) 1 N).re
      = ((liouvilleBinaryCorrelation N : ℤ) : ℝ) := by
  rw [mixedAdditiveConvolutionPower_liouville_eq, Complex.intCast_re]

/-- **Unconditional binary Liouville sign majority.**  For infinitely many even totals the ordered
binary additive Liouville correlation is at least `1`: same-sign Liouville pairs strictly
outnumber opposite-sign pairs. -/
theorem frequently_one_le_liouvilleBinaryCorrelation :
    ∃ᶠ q in atTop, 1 ≤ liouvilleBinaryCorrelation (2 * q) := by
  refine (frequently_re_pos_liouville (le_refl 1)).mono fun q hq => ?_
  rw [mixedAdditiveConvolutionPower_liouville_re] at hq
  have hz : (0 : ℤ) < liouvilleBinaryCorrelation (2 * q) := by exact_mod_cast hq
  omega

end

end RHTower
