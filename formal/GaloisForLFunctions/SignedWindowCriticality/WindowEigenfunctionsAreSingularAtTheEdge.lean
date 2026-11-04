import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemIsTheJetHankelSystem
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketEnergy
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts

/-!
# Window eigenfunctions are singular at the edge

DRAFT
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Real Nat

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis
open Zeta23
open _root_.RHTower (levyEnergy primeSum gammaHardyPhaseRate coshHalfMoment sinhHalfMoment archForm)

variable {f : ℝ → ℝ}

/-! ### Calculus on smooth compactly supported functions -/

/-- **Integration by parts**: `∫ f' g = −∫ f g'` for compactly supported `C¹` functions. -/
theorem integral_deriv_mul_eq_neg {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) :
    ∫ u, deriv f u * g u = -∫ u, f u * deriv g u := by
  have hdf : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdg : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hcg : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have h0 := GaloisForLFunctions.HTGeometry.integral_deriv_eq_zero_of_hasCompactSupport
    (g := fun u => f u * g u) (g' := fun u => deriv f u * g u + f u * deriv g u)
    (fun t => (hdf t).hasDerivAt.mul (hdg t).hasDerivAt) ((hcf.mul hg.continuous).add
      (hf.continuous.mul hcg)) hfc.mul_right
  have i1 : Integrable fun u => deriv f u * g u :=
    (hcf.mul hg.continuous).integrable_of_hasCompactSupport hfc.deriv.mul_right
  have i2 : Integrable fun u => f u * deriv g u :=
    (hf.continuous.mul hcg).integrable_of_hasCompactSupport hfc.mul_right
  rw [integral_add i1 i2] at h0
  linarith

theorem contDiff_deriv_of_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (deriv g) := by
  simpa using contDiff_iteratedDeriv_of_smooth hg 1

theorem supportedIn_deriv {R : ℝ} {g : ℝ → ℝ} (hg : SupportedIn R g) : SupportedIn R (deriv g) := by
  simpa using iteratedDeriv_supportedIn hg 1

/-- `∫ |g| ≤ √(2R) ‖g‖₂` for a continuous `g` supported in `[−R, R]`. -/
theorem integral_abs_le_sqrt {R : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgR : SupportedIn R g) (hR : 0 ≤ R) :
    ∫ u, |g u| ≤ Real.sqrt (2 * R) * Real.sqrt (∫ u, g u ^ 2) := by
  set b : ℝ → ℝ := (Icc (-R) R).indicator fun _ => (1 : ℝ)
  have hb2 : Integrable fun u => b u ^ 2 := by
    have : (fun u => b u ^ 2) = b := by
      funext u; simp only [b, indicator]; split_ifs <;> norm_num
    rw [this]
    exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hab : (fun u => |g u| * b u) = fun u => |g u| := by
    funext u
    simp only [b, indicator]
    split_ifs with hu
    · ring
    · rw [hgR u (lt_abs_of_notMem_Icc' hu)]; simp
  have hg2 : Integrable fun u => |g u| ^ 2 := by
    simpa only [sq_abs] using integrable_sq_of_continuous hg hgc
  have hi : Integrable fun u => |g u| * b u := by
    rw [hab]; exact (hg.integrable_of_hasCompactSupport hgc).abs
  have := abs_integral_mul_le hg2 hb2 hi
  rw [hab] at this
  have hbint : ∫ u, b u ^ 2 = 2 * R := by
    have : (fun u => b u ^ 2) = b := by
      funext u; simp only [b, indicator]; split_ifs <;> norm_num
    rw [this, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
      smul_eq_mul, mul_one]
    ring
  simp only [sq_abs] at this
  rw [hbint] at this
  rw [mul_comm (Real.sqrt (2 * R))]
  exact (le_abs_self _).trans this

/-! ### A compactly supported function cannot have geometrically bounded derivatives -/

/-- `|g(x)| ≤ ∫|g'|` for a `C¹` function supported in `[−R, R]`. -/
theorem abs_le_integral_abs_deriv {R : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgR : SupportedIn R g) (hR : 0 ≤ R) (x : ℝ) : |g x| ≤ ∫ u, |deriv g u| := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_supportedIn' hgR
  have hcd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hint : Integrable fun u => |deriv g u| :=
    (hcd.integrable_of_hasCompactSupport hgc.deriv).abs
  rcases le_or_gt x (-R - 1) with hx | hx
  · rw [hgR x (by rw [abs_of_neg (by linarith)]; linarith)]
    simpa using integral_nonneg fun u => abs_nonneg (deriv g u)
  have hdg : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hftc : ∫ u in (-R - 1)..x, deriv g u = g x - g (-R - 1) :=
    intervalIntegral.integral_deriv_eq_sub (fun u _ => hdg u)
      (hcd.intervalIntegrable _ _)
  rw [hgR (-R - 1) (by rw [abs_of_neg (by linarith)]; linarith), sub_zero] at hftc
  rw [← hftc]
  calc |∫ u in (-R - 1)..x, deriv g u| ≤ ∫ u in (-R - 1)..x, |deriv g u| :=
        intervalIntegral.abs_integral_le_integral_abs hx.le
    _ = ∫ u in Ioc (-R - 1) x, |deriv g u| := intervalIntegral.integral_of_le hx.le
    _ ≤ ∫ u, |deriv g u| := setIntegral_le_integral hint (Eventually.of_forall fun _ =>
        abs_nonneg _)

/-- **Iterated integration**: if `|g^{(m+j)}| ≤ S`, then `|g^{(m)}(x)| ≤ S (x − x₀)^j/j!` for
`x ≥ x₀ = −R − 1`, `g` smooth and supported in `[−R, R]`. -/
theorem abs_iteratedDeriv_le_pow {R : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgR : SupportedIn R g) (hR : 0 ≤ R) {S : ℝ} (j : ℕ) :
    ∀ m : ℕ, (∀ x, |iteratedDeriv (m + j) g x| ≤ S) →
      ∀ x, -R - 1 ≤ x → |iteratedDeriv m g x| ≤ S * (x - (-R - 1)) ^ j / j ! := by
  induction j with
  | zero => intro m hS x _; simpa using hS x
  | succ j ih =>
    intro m hS x hx
    have hS' : ∀ y, |iteratedDeriv (m + 1 + j) g y| ≤ S := fun y => by
      rw [show m + 1 + j = m + (j + 1) by ring]; exact hS y
    have hih := ih (m + 1) hS'
    set x₀ := -R - 1
    have hDm : Differentiable ℝ (iteratedDeriv m g) :=
      (contDiff_iteratedDeriv_of_smooth hg m).differentiable (by simp)
    have hcont : Continuous (iteratedDeriv (m + 1) g) :=
      (contDiff_iteratedDeriv_of_smooth hg (m + 1)).continuous
    have hftc : ∫ u in x₀..x, iteratedDeriv (m + 1) g u =
        iteratedDeriv m g x - iteratedDeriv m g x₀ := by
      rw [iteratedDeriv_succ]
      exact intervalIntegral.integral_deriv_eq_sub (fun u _ => hDm u)
        (by rw [← iteratedDeriv_succ]; exact hcont.intervalIntegrable _ _)
    have h0 : iteratedDeriv m g x₀ = 0 :=
      iteratedDeriv_supportedIn hgR m x₀ (by simp only [x₀]; rw [abs_of_neg (by linarith)]; linarith)
    rw [h0, sub_zero] at hftc
    rw [← hftc]
    have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
    calc |∫ u in x₀..x, iteratedDeriv (m + 1) g u|
        ≤ ∫ u in x₀..x, S * (u - x₀) ^ j / j ! := by
          refine intervalIntegral.abs_integral_le_integral_abs hx |>.trans ?_
          refine intervalIntegral.integral_mono_on hx (hcont.abs.intervalIntegrable _ _)
            ((by fun_prop : Continuous fun u => S * (u - x₀) ^ j / (j ! : ℝ)).intervalIntegrable _ _)
            fun u hu => hih u hu.1
      _ = S * (x - x₀) ^ (j + 1) / (j + 1)! := by
          have : ∫ u in x₀..x, S * (u - x₀) ^ j / j ! =
              S / j ! * ∫ u in x₀..x, (u - x₀) ^ j := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1; funext u; ring
          rw [this, intervalIntegral.integral_comp_sub_right (fun u => u ^ j), sub_self,
            integral_pow, zero_pow (Nat.succ_ne_zero j), sub_zero, Nat.factorial_succ]
          push_cast
          field_simp

/-- **Quasi-analyticity of compact support**: a smooth compactly supported function whose
derivatives grow at most geometrically in `L²` vanishes. -/
theorem eq_zero_of_sq_iteratedDeriv_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h : ∀ k, ∫ u, iteratedDeriv k g u ^ 2 ≤ C * B ^ k) : g = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_supportedIn_of_hasCompactSupport hgc
  funext x
  simp only [Pi.zero_apply]
  rcases le_or_gt x (-R - 1) with hx | hx
  · exact hR x (by rw [abs_of_neg (by linarith)]; linarith)
  set D := x - (-R - 1)
  have hD : 0 ≤ D := by simp only [D]; linarith
  -- `|g^{(n)}| ≤ √(2R) √(C B^{n+1})`
  have hsup : ∀ n y, |iteratedDeriv n g y| ≤
      Real.sqrt (2 * R) * Real.sqrt (C * B ^ (n + 1)) := by
    intro n y
    have hgn := contDiff_iteratedDeriv_of_smooth hg n
    have h1 := abs_le_integral_abs_deriv (by exact_mod_cast contDiff_infty.mp hgn 1)
      (iteratedDeriv_supportedIn hR n) hR0 y
    rw [← iteratedDeriv_succ] at h1
    have hgn1 := contDiff_iteratedDeriv_of_smooth hg (n + 1)
    have h2 := integral_abs_le_sqrt hgn1.continuous
      (hasCompactSupport_of_supportedIn' (iteratedDeriv_supportedIn hR (n + 1)))
      (iteratedDeriv_supportedIn hR (n + 1)) hR0
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (h (n + 1)))
      (Real.sqrt_nonneg _)))
  have hbound : ∀ n, |g x| ≤ Real.sqrt (2 * R) * Real.sqrt (C * B) *
      ((Real.sqrt B * D) ^ n / n !) := by
    intro n
    have := abs_iteratedDeriv_le_pow hg hR hR0 n 0 (by simpa using hsup n) x hx.le
    simp only [iteratedDeriv_zero] at this
    refine this.trans (le_of_eq ?_)
    have hsp : Real.sqrt (B ^ n) = Real.sqrt B ^ n := by
      rw [show B ^ n = (Real.sqrt B ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hB],
        Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
    rw [pow_succ, mul_comm (B ^ n) B, ← mul_assoc, Real.sqrt_mul (by positivity), hsp, mul_pow]
    simp only [D]
    ring
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (2 * R) * Real.sqrt (C * B) *
      ((Real.sqrt B * D) ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (Real.sqrt B * D)).const_mul
      (Real.sqrt (2 * R) * Real.sqrt (C * B))
  have h0 : |g x| ≤ 0 := ge_of_tendsto' hlim hbound
  exact abs_nonpos_iff.mp h0

end GaloisForLFunctions.SignedWindowCriticality

end
