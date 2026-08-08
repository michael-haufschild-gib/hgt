import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.LiouvilleEvenIndexPositiveRecurrence

/-!
# Unconditional positive recurrence of the binary Möbius additive correlation

The Möbius exponential profile `M x = ∑ μ(n) e^{-n x}` cannot decay like `x^{-b}` at the origin for
any `b` below the real part of a zeta zero (`not_isBigO_moebiusProfile_rpow`).  Such decay would
make its Mellin transform analytic on `Re s > b`; dividing by `Γ` and clearing the pole of `ζ` with
the entire multiple `zetaEntire s = (s-1) ζ s` turns `L ↗μ s · ζ s = 1` into the identity
`G(s) · zetaEntire(s) = s - 1` between two functions analytic on the whole half-plane.  Evaluating
the propagated identity at a zeta zero `ρ` gives `0 = ρ - 1`, contradicting `Re ρ < 1`.

The zeta zero itself is unconditional: `exists_riemannZeta_zero_mem_openStrip`.

Radial blow-up then feeds the even-index parity law, giving the unconditional sign-majority
statement

`1 ≤ ∑_{a + b = 2q} μ(a) μ(b)` for infinitely many `q`
(`frequently_one_le_moebiusBinaryCorrelation`),

and the order lower edge `2k Re ρ - 1 ≤ Ψ_k^even` at every zeta zero
(`le_evenIndexOrder_moebius`).
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped LSeries.notation Topology BigOperators

namespace RHTower

noncomputable section

/-- The complex Möbius coefficient sequence. -/
def moebiusCoeffC (n : ℕ) : ℂ := ((ArithmeticFunction.moebius n : ℤ) : ℂ)

theorem moebiusCoeff_zero : moebiusCoeffC 0 = 0 := by simp [moebiusCoeffC]

theorem norm_moebiusCoeff_le_one (n : ℕ) : ‖moebiusCoeffC n‖ ≤ 1 := by
  rw [moebiusCoeffC, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

theorem conj_moebiusCoeff (n : ℕ) : (starRingEnd ℂ) (moebiusCoeffC n) = moebiusCoeffC n := by
  rw [moebiusCoeffC]
  exact map_intCast (starRingEnd ℂ) _

/-- The exponential profile of the Möbius coefficients. -/
def moebiusProfile : ℝ → ℂ :=
  GaloisForLFunctions.HTGeometry.coeffLaplaceProfile moebiusCoeffC

/-- The Möbius Dirichlet series inverts zeta on the half-plane of absolute convergence. -/
theorem LSeries_moebiusCoeff_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries moebiusCoeffC s * riemannZeta s = 1 := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  rw [mul_comm]
  exact h

/-- **No origin decay below a zeta zero.**  If `ζ ρ = 0` with `Re ρ < 1` and `0 ≤ b < Re ρ`, the
Möbius profile is not `O(x^{-b})` at the origin. -/
theorem not_isBigO_moebiusProfile_rpow {b : ℝ} {ρ : ℂ} (hb0 : 0 ≤ b)
    (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) (hbρ : b < ρ.re) :
    ¬ (moebiusProfile =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b)) := by
  intro hO
  have hb1 : b < 1 := lt_trans hbρ hρ1
  have hbb : ∀ n : ℕ, ‖moebiusCoeffC n‖ ≤ 1 := norm_moebiusCoeff_le_one
  have hint : LocallyIntegrableOn moebiusProfile (Ioi 0) volume :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_locallyIntegrableOn hbb
  have htop : moebiusProfile =O[atTop] fun x : ℝ => Real.exp (-1 * x) :=
    GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_isBigO_exp_neg hbb moebiusCoeff_zero
  set U : Set ℂ := {s : ℂ | b < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_decayHalfPlane b).isPreconnected
  have hnotpole : ∀ s ∈ U, ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro s hs m hcon
    have hsre : b < s.re := hs
    rw [hcon] at hsre
    simp at hsre
    linarith
  have hGammaDiff : ∀ s ∈ U, DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s (hnotpole s hs)
  have hGammaNe : ∀ s ∈ U, Complex.Gamma s ≠ 0 := fun s hs =>
    Complex.Gamma_ne_zero (hnotpole s hs)
  have hMellinDiff : ∀ s ∈ U, DifferentiableAt ℂ (mellin moebiusProfile) s := by
    intro s hs
    exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := b) (by norm_num)
      hint htop hO hs
  set G : ℂ → ℂ := fun s => mellin moebiusProfile s / Complex.Gamma s with hGdef
  have hGdiff : ∀ s ∈ U, DifferentiableAt ℂ G s := fun s hs =>
    (hMellinDiff s hs).div (hGammaDiff s hs) (hGammaNe s hs)
  have hF1 : AnalyticOnNhd ℂ (fun s : ℂ => G s * zetaEntire s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUopen
    exact ((hGdiff s hs).mul (differentiable_zetaEntire s)).differentiableWithinAt
  have hF2 : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U := by
    refine DifferentiableOn.analyticOnNhd (fun s _ => ?_) hUopen
    exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - 1) s).differentiableWithinAt
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2V : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
  have hagree : (fun s : ℂ => G s * zetaEntire s) =ᶠ[𝓝 (2 : ℂ)] fun s : ℂ => s - 1 := by
    filter_upwards [hVopen.mem_nhds h2V] with s hs
    have hs1 : (1 : ℝ) < s.re := hs
    have hsU : s ∈ U := by
      have : b < s.re := by linarith
      exact this
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hmel := GaloisForLFunctions.HTGeometry.mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
      hbb moebiusCoeff_zero hs1
    have hGs : G s = LSeries moebiusCoeffC s := by
      rw [hGdef]
      simp only [moebiusProfile] at *
      rw [hmel, mul_comm, mul_div_assoc, div_self (hGammaNe s hsU), mul_one]
    have hinv := LSeries_moebiusCoeff_mul_riemannZeta hs1
    rw [hGs, zetaEntire_eq hsne]
    linear_combination (s - 1) * hinv
  have h2U : (2 : ℂ) ∈ U := by
    show b < (2 : ℂ).re
    simp only [Complex.re_ofNat]
    linarith
  have hρU : ρ ∈ U := hbρ
  have heq := hF1.eqOn_of_preconnected_of_eventuallyEq hF2 hUconn h2U hagree
  have hval := heq hρU
  simp only at hval
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρ1
    simp at hρ1
  rw [zetaEntire_eq hρne1, hρ, mul_zero, mul_zero] at hval
  have hρeq : ρ = 1 := by linear_combination -hval
  rw [hρeq] at hρ1
  simp at hρ1

theorem not_isBigO_moebiusProfile :
    ¬ (moebiusProfile =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(0 : ℝ))) := by
  obtain ⟨ρ, hρ0, hρ1, hρz⟩ := exists_riemannZeta_zero_mem_openStrip
  exact not_isBigO_moebiusProfile_rpow le_rfl hρz hρ1 hρ0

/-- Radial blow-up of the Möbius Abel series at the boundary of the unit disc. -/
theorem exists_norm_gt_moebius (B : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ B < ‖∑' N : ℕ, moebiusCoeffC N * (r : ℂ) ^ N‖ :=
  exists_norm_gt_of_not_isBigO moebiusCoeffC
    (Af := moebiusProfile)
    (fun x => GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x)
    not_isBigO_moebiusProfile B

/-- **Even-index sign recurrence for Möbius.** -/
theorem frequently_re_pos_moebius {k : ℕ} (hk : 1 ≤ k) :
    ∃ᶠ q in atTop, 0 < (mixedAdditiveConvolutionPower moebiusCoeffC k (2 * q)).re :=
  frequently_re_pos_of_norm_unbounded _ hk
    (fun _r hr0 hr1 => GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      norm_moebiusCoeff_le_one hr0 hr1)
    exists_norm_gt_moebius

/-- The ordered binary additive Möbius correlation at a total. -/
def moebiusBinaryCorrelation (N : ℕ) : ℤ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    ArithmeticFunction.moebius ab.1 * ArithmeticFunction.moebius ab.2

theorem mixedAdditiveConvolutionPower_moebius_eq (N : ℕ) :
    mixedAdditiveConvolutionPower moebiusCoeffC 1 N
      = ((moebiusBinaryCorrelation N : ℤ) : ℂ) := by
  rw [mixedAdditiveConvolutionPower_one, moebiusBinaryCorrelation]
  push_cast
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [conj_moebiusCoeff, moebiusCoeffC, moebiusCoeffC]

theorem mixedAdditiveConvolutionPower_moebius_re (N : ℕ) :
    (mixedAdditiveConvolutionPower moebiusCoeffC 1 N).re
      = ((moebiusBinaryCorrelation N : ℤ) : ℝ) := by
  rw [mixedAdditiveConvolutionPower_moebius_eq, Complex.intCast_re]

/-- **Unconditional binary Möbius sign majority `(34)`.**  For infinitely many even totals the
ordered binary additive Möbius correlation is at least `1`. -/
theorem frequently_one_le_moebiusBinaryCorrelation :
    ∃ᶠ q in atTop, 1 ≤ moebiusBinaryCorrelation (2 * q) := by
  refine (frequently_re_pos_moebius (le_refl 1)).mono fun q hq => ?_
  rw [mixedAdditiveConvolutionPower_moebius_re] at hq
  have hz : (0 : ℤ) < moebiusBinaryCorrelation (2 * q) := by exact_mod_cast hq
  omega

/-! ### The Möbius order lower edge -/

/-- No even-index subpower bound can push the Möbius decay exponent below a zeta zero. -/
theorem re_le_of_evenIndex_subpower_moebius {k : ℕ} {α C : ℝ} {ρ : ℂ} (hk : 0 < k) (hα : 0 ≤ α)
    (hC : 0 ≤ C) (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1)
    (hupper : ∀ q : ℕ,
      (mixedAdditiveConvolutionPower moebiusCoeffC k (2 * q)).re ≤ C * ((q : ℝ) + 1) ^ α) :
    ρ.re ≤ (α + 1) / (2 * (k : ℝ)) := by
  by_contra hcon
  push Not at hcon
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hb0 : (0 : ℝ) ≤ (α + 1) / (2 * (k : ℝ)) := by positivity
  refine not_isBigO_moebiusProfile_rpow hb0 hρ hρ1 hcon ?_
  have hbig := isBigO_zero_of_evenIndex_subpower (a := moebiusCoeffC) hk hα hC
    (fun r hr0 hr1 => GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      norm_moebiusCoeff_le_one hr0 hr1) hupper
  refine hbig.congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  exact (GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x).symm

/-- **The Möbius even-index order lower edge `(8)` at a zeta zero.** -/
theorem le_evenIndexOrder_moebius (j : ℕ) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ.re < 1) :
    2 * ((j : ℝ) + 1) * ρ.re - 1 ≤ evenIndexOrder moebiusCoeffC (j + 1) := by
  refine le_evenIndexOrder_of_subpower_threshold norm_moebiusCoeff_le_one
    fun α C hα hC hbound => ?_
  have hkey := re_le_of_evenIndex_subpower_moebius (k := j + 1) (Nat.succ_pos j) hα hC hρ hρ1 hbound
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rwa [hcast] at hkey

end

end RHTower
