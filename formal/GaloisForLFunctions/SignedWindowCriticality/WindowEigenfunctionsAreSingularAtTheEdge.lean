import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemIsTheJetHankelSystem
import GaloisForLFunctions.SignedWindowCriticality.TheParitySectorsAreTheBandAtTheCentre
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
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) R]
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

/-! ### The jet norms are log-convex and escape to infinite frequency -/

/-- The `L²` jet norms `N_k = ‖g^{(k)}‖₂²`. -/
def jetNormSq (g : ℝ → ℝ) (k : ℕ) : ℝ := ∫ u, iteratedDeriv k g u ^ 2

theorem jetNormSq_nonneg (g : ℝ → ℝ) (k : ℕ) : 0 ≤ jetNormSq g k :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Log-convexity**: `N_{k+1}² ≤ N_k N_{k+2}`. -/
theorem jetNormSq_sq_le {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (k : ℕ) :
    jetNormSq g (k + 1) ^ 2 ≤ jetNormSq g k * jetNormSq g (k + 2) := by
  have hk := (iteratedDeriv_mem_realTests hg hgc k)
  have hk1 := (iteratedDeriv_mem_realTests hg hgc (k + 1))
  have hk2 := (iteratedDeriv_mem_realTests hg hgc (k + 2))
  have hibp := integral_deriv_mul_eq_neg (f := iteratedDeriv k g) (g := iteratedDeriv (k + 1) g)
    (by exact_mod_cast contDiff_infty.mp (contDiff_iteratedDeriv_of_smooth hg k) 1) hk.2
    (by exact_mod_cast contDiff_infty.mp (contDiff_iteratedDeriv_of_smooth hg (k + 1)) 1)
  rw [← iteratedDeriv_succ, ← iteratedDeriv_succ] at hibp
  have hcs := abs_integral_mul_le (integrable_sq_of_continuous hk.1.continuous hk.2)
    (integrable_sq_of_continuous hk2.1.continuous hk2.2)
    ((hk.1.continuous.mul hk2.1.continuous).integrable_of_hasCompactSupport hk.2.mul_right)
  have hN : jetNormSq g (k + 1) = -∫ u, iteratedDeriv k g u * iteratedDeriv (k + 2) g u := by
    rw [jetNormSq, ← hibp]; congr 1; funext u; ring
  have hN0 := jetNormSq_nonneg g (k + 1)
  have hle : jetNormSq g (k + 1) ≤ Real.sqrt (jetNormSq g k) * Real.sqrt (jetNormSq g (k + 2)) := by
    rw [hN]; exact (neg_le_abs _).trans hcs
  calc jetNormSq g (k + 1) ^ 2 ≤ (Real.sqrt (jetNormSq g k) * Real.sqrt (jetNormSq g (k + 2))) ^ 2 :=
        pow_le_pow_left₀ hN0 hle 2
    _ = jetNormSq g k * jetNormSq g (k + 2) := by
        rw [mul_pow, Real.sq_sqrt (jetNormSq_nonneg g k), Real.sq_sqrt (jetNormSq_nonneg g (k + 2))]

theorem iteratedDeriv_add_eq {g : ℝ → ℝ} (i j : ℕ) :
    iteratedDeriv (i + j) g = iteratedDeriv i (iteratedDeriv j g) := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

/-- **A nonzero bump has nonzero jets of every order.** -/
theorem jetNormSq_pos {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hg0 : g ≠ 0)
    (k : ℕ) : 0 < jetNormSq g k := by
  refine lt_of_le_of_ne (jetNormSq_nonneg g k) fun h0 => hg0 ?_
  have hk := iteratedDeriv_mem_realTests hg hgc k
  have hz : iteratedDeriv k g = 0 := by
    have hint := integrable_sq_of_continuous hk.1.continuous hk.2
    have hae : (fun u => iteratedDeriv k g u ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg (iteratedDeriv k g u)) hint).mp h0.symm
    have hc : Continuous fun u => iteratedDeriv k g u ^ 2 := hk.1.continuous.pow 2
    have heq : (fun u => iteratedDeriv k g u ^ 2) = 0 := (hc.ae_eq_iff_eq volume continuous_zero).mp hae
    funext u
    have := congrFun heq u
    simpa using this
  refine eq_zero_of_sq_iteratedDeriv_le hg hgc (C := ∑ i ∈ Finset.range k, jetNormSq g i)
    (B := 1) (Finset.sum_nonneg fun i _ => jetNormSq_nonneg g i) zero_le_one fun j => ?_
  rw [one_pow, mul_one]
  rcases lt_or_ge j k with hj | hj
  · exact Finset.single_le_sum (fun i _ => jetNormSq_nonneg g i) (Finset.mem_range.mpr hj)
  · have : iteratedDeriv j g = 0 := by
      rw [show j = (j - k) + k by omega, iteratedDeriv_add_eq, hz]
      funext u; simp
    rw [this]
    simpa using Finset.sum_nonneg fun i (_ : i ∈ Finset.range k) => jetNormSq_nonneg g i

/-- **The jets escape to infinite frequency**: the ratios `N_{k+1}/N_k` are unbounded, and once
above `B` they stay above `B`. -/
theorem exists_jetNormSq_ratio_ge {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg0 : g ≠ 0) (B : ℝ) : ∃ K, ∀ k ≥ K, B * jetNormSq g k ≤ jetNormSq g (k + 1) := by
  have hpos := jetNormSq_pos hg hgc hg0
  -- the ratio is monotone
  have hmono : ∀ k, jetNormSq g (k + 1) / jetNormSq g k ≤ jetNormSq g (k + 2) / jetNormSq g (k + 1) :=
    fun k => by
      rw [div_le_div_iff₀ (hpos k) (hpos (k + 1))]
      nlinarith [jetNormSq_sq_le hg hgc k]
  by_contra hcon
  push Not at hcon
  -- otherwise the ratios stay below `B` and the jets grow geometrically
  have hbd : ∀ k, jetNormSq g (k + 1) ≤ B * jetNormSq g k := by
    intro k
    by_contra hk
    push Not at hk
    obtain ⟨k', hk', hlt⟩ := hcon k
    have hr : B < jetNormSq g (k + 1) / jetNormSq g k := by
      rw [lt_div_iff₀ (hpos k)]; linarith
    have hmono' : ∀ m, jetNormSq g (k + 1) / jetNormSq g k ≤
        jetNormSq g (k + m + 1) / jetNormSq g (k + m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => exact ih.trans (by simpa [add_assoc] using hmono (k + m))
    have := hmono' (k' - k)
    rw [show k + (k' - k) = k' by omega] at this
    have : B < jetNormSq g (k' + 1) / jetNormSq g k' := lt_of_lt_of_le hr this
    rw [lt_div_iff₀ (hpos k')] at this
    linarith
  have hB : 0 ≤ B := by
    have := hbd 0
    by_contra hneg
    push Not at hneg
    nlinarith [hpos 0, hpos 1]
  refine hg0 (eq_zero_of_sq_iteratedDeriv_le hg hgc (jetNormSq_nonneg g 0) hB fun k => ?_)
  show jetNormSq g k ≤ _
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; nlinarith [hbd k]

/-! ### Weil's form on a high jet -/

theorem deriv_ofReal {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    deriv (fun u => (g u : ℂ)) = fun u => ((deriv g u : ℝ) : ℂ) := by
  funext u; exact ((hg u).hasDerivAt.ofReal_comp).deriv

/-- The paper transform of a derivative has `|(g')^(r)|² = r²|ĝ(r)|²`. -/
theorem norm_sq_paperFT_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (r : ℝ) :
    ‖paperFT (fun u => ((deriv g u : ℝ) : ℂ)) r‖ ^ 2 = r ^ 2 * ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 := by
  have hG : ContDiff ℝ 1 fun u => (g u : ℂ) := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have h := _root_.RHTower.EvenSector.paperFT_deriv_of_compact hG hGc (r : ℂ)
  rw [deriv_ofReal (hg.differentiable one_ne_zero)] at h
  rw [h, norm_mul, mul_pow, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- **Plancherel** for a real test: `∫|ĝ|² = 2π ∫ g²`. -/
theorem integral_norm_sq_paperFT_real {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 = 2 * π * ∫ u, g u ^ 2 := by
  have hG : Continuous fun u => (g u : ℂ) := Complex.continuous_ofReal.comp hg
  have hGc : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  rw [_root_.RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp
    (hG.integrable_of_hasCompactSupport hGc) (hG.memLp_of_hasCompactSupport hGc)]
  congr 2; funext u; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The archimedean form sees high frequencies logarithmically**: for `Λ ≥ 0` and a test `g`,
`archForm g' ≥ log(1 + Λ/4)(‖g'‖² − Λ²‖g‖²) − 10‖g'‖²`. -/
theorem archForm_deriv_ge {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) :
    Real.log (1 + Λ / 4) * ((∫ u, deriv g u ^ 2) - Λ ^ 2 * ∫ u, g u ^ 2) -
      10 * ∫ u, deriv g u ^ 2 ≤ archForm (deriv g) := by
  have hd2 : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have hdc : HasCompactSupport (deriv g) := hgc.deriv
  set F : ℝ → ℝ := fun r => ‖paperFT (fun u => ((deriv g u : ℝ) : ℂ)) r‖ ^ 2
  set G : ℝ → ℝ := fun r => ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2
  set L := Real.log (1 + Λ / 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hFi : Integrable F := _root_.RHTower.integrable_normSq_paperFT_ofReal hd2 hdc
  have hGi : Integrable G :=
    _root_.RHTower.integrable_normSq_paperFT_ofReal (hg.of_le (by norm_num)) hgc
  have hFG : ∀ r, F r = r ^ 2 * G r := fun r =>
    norm_sq_paperFT_deriv (hg.of_le (by norm_num)) hgc r
  set I : Set ℝ := Icc (-Λ) Λ
  have hlow : ∫ r, I.indicator F r ≤ Λ ^ 2 * ∫ r, G r := by
    rw [← integral_const_mul]
    refine integral_mono (hFi.indicator measurableSet_Icc) (hGi.const_mul _) fun r => ?_
    by_cases hr : r ∈ I
    · rw [indicator_of_mem hr, hFG r]
      have : r ^ 2 ≤ Λ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr hr) 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    · rw [indicator_of_notMem hr]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpt : ∀ r, L * F r - L * I.indicator F r - 10 * F r ≤ F r * EF.gammaBracket r := by
    intro r
    have hgb := _root_.RHTower.WeilWorkPBAP.gammaBracket_lower r
    have hF0 : 0 ≤ F r := sq_nonneg _
    by_cases hr : r ∈ I
    · rw [indicator_of_mem hr]
      have : 0 ≤ Real.log (1 + |r| / 4) := Real.log_nonneg (by have := abs_nonneg r; linarith)
      nlinarith
    · rw [indicator_of_notMem hr, mul_zero, sub_zero]
      have hrΛ : Λ < |r| := lt_abs_of_notMem_Icc' hr
      have hlog : L ≤ Real.log (1 + |r| / 4) := Real.log_le_log (by positivity) (by linarith)
      nlinarith
  have hi : Integrable (fun r => L * F r - L * I.indicator F r - 10 * F r) :=
    ((hFi.const_mul L).sub ((hFi.indicator measurableSet_Icc).const_mul L)).sub (hFi.const_mul 10)
  have hint : ∫ r, (L * F r - L * I.indicator F r - 10 * F r) ≤ ∫ r, F r * EF.gammaBracket r :=
    integral_mono hi (_root_.RHTower.integrable_normSq_paperFT_mul_gammaBracket hd2 hdc) hpt
  have hlhs : ∫ r, (L * F r - L * I.indicator F r - 10 * F r) =
      L * (∫ r, F r) - L * (∫ r, I.indicator F r) - 10 * ∫ r, F r := by
    have i0 : Integrable fun r => L * F r := hFi.const_mul L
    have i0' : Integrable fun r => L * I.indicator F r :=
      (hFi.indicator measurableSet_Icc).const_mul L
    have i1 : Integrable fun r => L * F r - L * I.indicator F r := i0.sub i0'
    have i2 : Integrable fun r => 10 * F r := hFi.const_mul 10
    rw [integral_sub i1 i2, integral_sub i0 i0', integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hPF : ∫ r, F r = 2 * π * ∫ u, deriv g u ^ 2 :=
    integral_norm_sq_paperFT_real hd2.continuous hdc
  have hPG : ∫ r, G r = 2 * π * ∫ u, g u ^ 2 :=
    integral_norm_sq_paperFT_real hg.continuous hgc
  have harch : archForm (deriv g) = 1 / (2 * π) * ∫ r, F r * EF.gammaBracket r := rfl
  rw [hlhs, hPF] at hint
  rw [hPG] at hlow
  have hπ : 0 < 2 * π := by positivity
  rw [harch, one_div, ← div_eq_inv_mul, le_div_iff₀ hπ]
  nlinarith [mul_le_mul_of_nonneg_left hlow hL]

end GaloisForLFunctions.SignedWindowCriticality

end
