import GaloisForLFunctions.ConjugateDiagonalGeometry.HeckeDefectHorizontalMultiplicity

/-!
# Archimedean, Paley–Wiener, and Hyperbolic Kernel Foundations at Logarithmic Scale

Foundational analytic and algebraic identities for `baseBump`, `heckeAvgBump L`, `depthKernel`,
and `archPart (heckeAvgBump L) (-γ / (2π))` across arbitrary logarithmic scales `L = c log T`
(`c > 0`):

1. **Polynomial hyperbolic scale transfer** (`exists_depthKernel_scale_transfer`):
   Iterating `depthKernel (2L) d = 4 depthKernel L d + (depthKernel L d)²` transfers any upper
   bound `depthKernel L₁ d ≤ B` to `depthKernel L₂ d ≤ K(B, r) depthKernel L₁ d` whenever
   `0 ≤ L₂ ≤ r L₁`.
2. **Strip-uniform `C_c^∞` Paley–Wiener rapid decay** (`norm_tr_twist_baseBump_le_exp`,
   `exists_norm_tr_twist_baseBump_le_pow`):
   Integration by parts of `f(t) e^{wt}` on `[-1, 1]` yields `w ∫ f(t) e^{wt} dt = -∫ f'(t) e^{wt} dt`.
   Inducting on derivative order `K : ℕ` bounds `‖tr (twist γ baseBump) s‖ ≤ C_K / |s.im - γ|^K`
   uniformly across the entire strip `|s.re - 1/2| ≤ 1/2`.
3. **Near-ordinate `baseBump` coercivity** (`cos_quarter_mul_sq_le_normSq_tr_twist_baseBump`,
   `unitWindow_depthCharge_le_heckeDefect`):
   When `|ρ.im - γ| ≤ A` with `A / 4 < π / 2`, evenness and nonnegativity of `baseBumpReal` on
   `[-1/4, 1/4]` give `(Real.cos (A / 4))² ≤ Complex.normSq (tr (twist γ baseBump) ρ)`, coercing
   `heckeDefect (baseTwistTest γ) L` from below by the unit-window depth charge uniformly on
   `γ ∈ [T, T + 1)`.
4. **Separated-ordinate `heckeAvgBump` decay** (`normSq_tr_twist_heckeAvgBump_le_of_sep`):
   For `|ρ.im - γ| ≥ η > 0`, exact evaluation of `∫_{-L}^L e^{zℓ} dℓ` decomposes
   `Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)` into an `O((1 + η⁻²) L⁻² (1 + (γ - ρ.im)²)⁻¹)`
   Lorentzian term plus `(4 η² L²)⁻¹ Complex.normSq (tr (twist γ baseBump) ρ) depthKernel L δ_ρ`.
5. **Pole-reflection decomposition and all-`c` archimedean bounds**
   (`exists_abs_re_archPart_sub_pole_heckeAvgBump_le`, `exists_abs_re_archPart_heckeAvgBump_log_le`):
   Evenness and reality of `heckeAvgBump L` identify the `s = 0, 1` pole sum in
   `Re A_{F_L}(-γ / 2π)` with `2 Re((tr (twist γ F_L) 1)²)`; combining two-sided `mu`-integral
   bounds with `K`-fold Paley–Wiener pole decay bounds `|Re A_{F_{c log T}}(-γ / 2π)| ≤ C_arch(c)`
   for every `c > 0`, removing the `c ≤ 4` restriction.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Dyadic-polynomial hyperbolic scale transfer for `depthKernel` -/

/-- Dyadic iteration of `depthKernel_double`: if `depthKernel L d ≤ B` (`B ≥ 0`), then for every
`k : ℕ` there exist `B_k ≥ 0` and `M_k ≥ 1` depending only on `(B, k)` such that
`depthKernel (2^k * L) d ≤ B_k` and `depthKernel (2^k * L) d ≤ M_k * depthKernel L d`. -/
private theorem exists_depthKernel_pow_two_transfer (B : ℝ) (hB : 0 ≤ B) :
    ∀ k : ℕ, ∃ B_k M_k : ℝ, 0 ≤ B_k ∧ 1 ≤ M_k ∧
      ∀ L d : ℝ, depthKernel L d ≤ B →
        depthKernel ((2 : ℝ) ^ k * L) d ≤ B_k ∧
        depthKernel ((2 : ℝ) ^ k * L) d ≤ M_k * depthKernel L d
  | 0 => ⟨B, 1, hB, le_rfl, fun L d h => ⟨by simpa using h, by simp⟩⟩
  | k + 1 => by
      obtain ⟨Bk, Mk, hBk, hMk, ih⟩ := exists_depthKernel_pow_two_transfer B hB k
      refine ⟨(4 + Bk) * Bk, (4 + Bk) * Mk, by positivity, ?_, fun L d h => ?_⟩
      · nlinarith
      · obtain ⟨h1, h2⟩ := ih L d h
        have hnn := depthKernel_nonneg ((2 : ℝ) ^ k * L) d
        have hdbl : depthKernel ((2 : ℝ) ^ (k + 1) * L) d =
            4 * depthKernel ((2 : ℝ) ^ k * L) d + depthKernel ((2 : ℝ) ^ k * L) d ^ 2 := by
          rw [pow_succ', mul_assoc]
          exact depthKernel_double ((2 : ℝ) ^ k * L) d
        have hstep : depthKernel ((2 : ℝ) ^ (k + 1) * L) d ≤
            (4 + Bk) * depthKernel ((2 : ℝ) ^ k * L) d := by
          rw [hdbl]
          nlinarith [mul_le_mul_of_nonneg_right h1 hnn]
        refine ⟨hstep.trans (mul_le_mul_of_nonneg_left h1 (by positivity)), ?_⟩
        exact hstep.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_assoc _ _ _).symm)

/-- **Hyperbolic scale transfer.** Whenever `depthKernel L₁ d ≤ B` (`B ≥ 0`) and `0 ≤ L₂ ≤ r * L₁`
(`0 ≤ L₁`, `0 ≤ r`), `depthKernel L₂ d ≤ K * depthKernel L₁ d` for a constant `K ≥ 1` depending
only on `(B, r)`. -/
theorem exists_depthKernel_scale_transfer (B r : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ L₁ L₂ d : ℝ, 0 ≤ L₁ → 0 ≤ L₂ → L₂ ≤ r * L₁ →
      depthKernel L₁ d ≤ B → depthKernel L₂ d ≤ K * depthKernel L₁ d := by
  set k : ℕ := ⌈r⌉₊
  obtain ⟨_, M, _, hM, hpow⟩ := exists_depthKernel_pow_two_transfer B hB k
  refine ⟨M, hM, fun L₁ L₂ d hL₁ hL₂ hle hB₁ => ?_⟩
  have hr2 : r ≤ (2 : ℝ) ^ k := by
    calc r ≤ (k : ℝ) := Nat.le_ceil r
      _ ≤ (2 : ℝ) ^ k := by
        exact_mod_cast Nat.lt_two_pow_self.le
  have hL₂_le : L₂ ≤ (2 : ℝ) ^ k * L₁ := hle.trans (mul_le_mul_of_nonneg_right hr2 hL₁)
  have hmono : depthKernel L₂ d ≤ depthKernel ((2 : ℝ) ^ k * L₁) d := by
    have hsym1 : depthKernel L₂ d = depthKernel d L₂ := by unfold depthKernel; ring_nf
    have hsym2 : depthKernel ((2 : ℝ) ^ k * L₁) d = depthKernel d ((2 : ℝ) ^ k * L₁) := by
      unfold depthKernel; ring_nf
    rw [hsym1, hsym2]
    refine depthKernel_mono_depth d ?_
    rw [abs_of_nonneg hL₂, abs_of_nonneg (mul_nonneg (by positivity) hL₁)]
    exact hL₂_le
  exact hmono.trans (hpow L₁ d hB₁).2

/-! ## §2. Strip-uniform `C_c^∞` Paley–Wiener rapid decay for `baseBump` -/

/-- Whole-line integration by parts `w ∫ f(t) e^{wt} dt = -∫ f'(t) e^{wt} dt` for smooth functions
supported in `[-1/4, 1/4]`. -/
private theorem mul_integral_cexp_eq_neg_integral_deriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hsupp : tsupport f ⊆ Icc (-(1 / 4 : ℝ)) (1 / 4)) (w : ℂ) :
    w * (∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))) =
      -(∫ t : ℝ, deriv f t * Complex.exp (w * (t : ℂ))) := by
  have hdf : Differentiable ℝ f := (contDiff_infty_iff_deriv.mp hf).1
  have hcd_df : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hsupp_df : tsupport (deriv f) ⊆ Icc (-(1 / 4 : ℝ)) (1 / 4) :=
    tsupport_deriv_subset.trans hsupp
  have hzero_f : ∀ t : ℝ, 1 ≤ |t| → f t = 0 := fun t ht => by
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have h := abs_le.mpr (hsupp hm)
    linarith
  have hzero_df : ∀ t : ℝ, 1 ≤ |t| → deriv f t = 0 := fun t ht => by
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have h := abs_le.mpr (hsupp_df hm)
    linarith
  have hint_eq : ∀ g : ℝ → ℂ, (∀ t : ℝ, 1 ≤ |t| → g t = 0) →
      (∫ t : ℝ, g t * Complex.exp (w * (t : ℂ))) =
        ∫ t in (-1 : ℝ)..1, g t * Complex.exp (w * (t : ℂ)) := by
    intro g hg0
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    have habs : 1 ≤ |t| := by
      rcases ht with h1 | h2
      · exact (by linarith : 1 ≤ -t).trans (neg_le_abs t)
      · exact h2.le.trans (le_abs_self t)
    rw [hg0 t habs, zero_mul]
  rw [hint_eq f hzero_f, hint_eq (deriv f) hzero_df]
  set G : ℝ → ℂ := fun t => f t * Complex.exp (w * (t : ℂ))
  set G' : ℝ → ℂ := fun t =>
    deriv f t * Complex.exp (w * (t : ℂ)) + f t * (w * Complex.exp (w * (t : ℂ)))
  have hderiv : ∀ t : ℝ, HasDerivAt G (G' t) t := by
    intro t
    have hexp : HasDerivAt (fun x : ℝ => Complex.exp (w * (x : ℂ)))
        (w * Complex.exp (w * (t : ℂ))) t := by
      simpa [mul_one, mul_comm] using (((hasDerivAt_id t).ofReal_comp).const_mul w).cexp
    exact (hdf t).hasDerivAt.mul hexp
  have hcont_G' : Continuous G' := by
    have hc_exp : Continuous (fun t : ℝ => Complex.exp (w * (t : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (hcd_df.continuous.mul hc_exp).add (hf.continuous.mul (continuous_const.mul hc_exp))
  have hftc : (∫ t in (-1 : ℝ)..1, G' t) = G 1 - G (-1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont_G'.intervalIntegrable _ _)
  have hG1 : G 1 = 0 := by simp [G, hzero_f 1 (by norm_num)]
  have hGn1 : G (-1) = 0 := by simp [G, hzero_f (-1) (by norm_num)]
  rw [hG1, hGn1, sub_self] at hftc
  have hc_exp : Continuous (fun t : ℝ => Complex.exp (w * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hi1 : IntervalIntegrable (fun t : ℝ => deriv f t * Complex.exp (w * (t : ℂ))) volume (-1) 1 :=
    (hcd_df.continuous.mul hc_exp).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => w * (f t * Complex.exp (w * (t : ℂ)))) volume (-1) 1 :=
    (continuous_const.mul (hf.continuous.mul hc_exp)).intervalIntegrable _ _
  have hsplit : (∫ t in (-1 : ℝ)..1, G' t) =
      (∫ t in (-1 : ℝ)..1, deriv f t * Complex.exp (w * (t : ℂ))) +
        w * ∫ t in (-1 : ℝ)..1, f t * Complex.exp (w * (t : ℂ)) := by
    have hcongr : G' = fun t : ℝ =>
        deriv f t * Complex.exp (w * (t : ℂ)) + w * (f t * Complex.exp (w * (t : ℂ))) := by
      ext t; dsimp [G']; ring
    rw [hcongr, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul]
  rw [hsplit] at hftc
  exact eq_neg_of_add_eq_zero_right hftc

/-- Inductive strip-uniform Paley–Wiener bound on `∫ f(t) e^{wt} dt` for `|Re w| ≤ 1/2`. -/
private theorem exists_norm_integral_cexp_le_pow :
    ∀ (K : ℕ) {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      tsupport f ⊆ Icc (-(1 / 4 : ℝ)) (1 / 4) →
      ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, |w.re| ≤ 1 / 2 → w.im ≠ 0 →
        ‖∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))‖ ≤ C / |w.im| ^ K
  | 0, f, hf, hsupp => by
      have hfc : HasCompactSupport f :=
        HasCompactSupport.of_support_subset_isCompact isCompact_Icc
          ((subset_tsupport f).trans hsupp)
      have hint_f : Integrable (fun t : ℝ => ‖f t‖) :=
        hf.continuous.norm.integrable_of_hasCompactSupport hfc.norm
      set C : ℝ := Real.exp (1 / 8) * (∫ t : ℝ, ‖f t‖) + 1
      have hC : 0 < C := by
        have : 0 ≤ ∫ t : ℝ, ‖f t‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      refine ⟨C, hC, fun w hw _ => ?_⟩
      rw [pow_zero, div_one]
      have hint_w : Integrable (fun t : ℝ => ‖f t * Complex.exp (w * (t : ℂ))‖) :=
        (hf.continuous.mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).norm.integrable_of_hasCompactSupport
          (hfc.mul_right.norm)
      refine (norm_integral_le_integral_norm _).trans ?_
      have hmono : (∫ t : ℝ, ‖f t * Complex.exp (w * (t : ℂ))‖) ≤
          ∫ t : ℝ, Real.exp (1 / 8) * ‖f t‖ := by
        refine integral_mono hint_w (hint_f.const_mul _) fun t => ?_
        dsimp only
        by_cases ht : t ∈ tsupport f
        · have htabs : |t| ≤ 1 / 4 := abs_le.mpr (hsupp ht)
          rw [norm_mul, Complex.norm_exp]
          have hre : (w * (t : ℂ)).re = w.re * t := by simp
          rw [hre, mul_comm ‖f t‖]
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
          calc w.re * t ≤ |w.re * t| := le_abs_self _
            _ = |w.re| * |t| := abs_mul _ _
            _ ≤ (1 / 2) * (1 / 4) := mul_le_mul hw htabs (abs_nonneg _) (by norm_num)
            _ = 1 / 8 := by norm_num
        · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul, norm_zero, mul_zero]
      rw [integral_const_mul] at hmono
      linarith
  | K + 1, f, hf, hsupp => by
      obtain ⟨C', hC', ih⟩ := exists_norm_integral_cexp_le_pow K
        (contDiff_infty_iff_deriv.mp hf).2 (tsupport_deriv_subset.trans hsupp)
      refine ⟨C', hC', fun w hw hwim => ?_⟩
      have hibp := congrArg norm (mul_integral_cexp_eq_neg_integral_deriv hf hsupp w)
      rw [norm_mul, norm_neg] at hibp
      have him_pos : 0 < |w.im| := abs_pos.mpr hwim
      have him_le : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      have hstep : |w.im| * ‖∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))‖ ≤
          C' / |w.im| ^ K := by
        calc |w.im| * ‖∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))‖
            ≤ ‖w‖ * ‖∫ t : ℝ, f t * Complex.exp (w * (t : ℂ))‖ :=
              mul_le_mul_of_nonneg_right him_le (norm_nonneg _)
          _ = ‖∫ t : ℝ, deriv f t * Complex.exp (w * (t : ℂ))‖ := hibp
          _ ≤ C' / |w.im| ^ K := ih w hw hwim
      rw [pow_succ, ← div_div, le_div_iff₀ him_pos]
      simpa [mul_comm] using hstep

/-- Universal strip bound `‖tr (twist γ baseBump) s‖ ≤ e^{1/8}` for `|s.re - 1/2| ≤ 1/2`. -/
theorem norm_tr_twist_baseBump_le_exp (γ : ℝ) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    ‖tr (twist γ baseBump) s‖ ≤ Real.exp (1 / 8) := by
  rw [tr_twist, tr_eq]
  set w : ℂ := s - (γ : ℂ) * I - 1 / 2
  have hwre : |w.re| ≤ 1 / 2 := by
    have : w.re = s.re - 1 / 2 := by simp [w]
    rwa [this]
  have hint_b : Integrable baseBumpReal := baseContDiffBump.integrable_normed
  have hint_w : Integrable (fun u : ℝ => ‖baseBump u * Complex.exp (w * (u : ℂ))‖) :=
    ((contDiff_baseBump (n := ⊤)).continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).norm.integrable_of_hasCompactSupport
      (hasCompactSupport_baseBump.mul_right.norm)
  refine (norm_integral_le_integral_norm _).trans ?_
  calc (∫ u : ℝ, ‖baseBump u * Complex.exp (w * (u : ℂ))‖)
      ≤ ∫ u : ℝ, Real.exp (1 / 8) * baseBumpReal u := by
        refine integral_mono hint_w (hint_b.const_mul _) fun u => ?_
        dsimp only
        by_cases hu : 1 / 4 ≤ |u|
        · rw [baseBump_eq_zero_of_abs_ge hu, baseBumpReal_eq_zero_of_abs_ge hu,
            zero_mul, norm_zero, mul_zero]
        · have hu_le : |u| ≤ 1 / 4 := (not_le.mp hu).le
          rw [norm_mul, baseBump, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (baseBumpReal_nonneg u), Complex.norm_exp]
          have hre : (w * (u : ℂ)).re = w.re * u := by simp
          rw [hre, mul_comm (baseBumpReal u)]
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (baseBumpReal_nonneg u)
          calc w.re * u ≤ |w.re * u| := le_abs_self _
            _ = |w.re| * |u| := abs_mul _ _
            _ ≤ (1 / 2) * (1 / 4) := mul_le_mul hwre hu_le (abs_nonneg _) (by norm_num)
            _ = 1 / 8 := by norm_num
    _ = Real.exp (1 / 8) * ∫ u : ℝ, baseBumpReal u := integral_const_mul _ _
    _ = Real.exp (1 / 8) := by rw [integral_baseBumpReal, mul_one]

/-- **All-order strip-uniform Paley–Wiener rapid decay of `baseBump`.** For every `K : ℕ`, there
exists `C_K > 0` such that for all `γ ∈ ℝ` and `s ∈ ℂ` with `|s.re - 1/2| ≤ 1/2` and `s.im ≠ γ`,
`‖tr (twist γ baseBump) s‖ ≤ C_K / |s.im - γ|^K`. -/
theorem exists_norm_tr_twist_baseBump_le_pow (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (s : ℂ), |s.re - 1 / 2| ≤ 1 / 2 → s.im ≠ γ →
      ‖tr (twist γ baseBump) s‖ ≤ C / |s.im - γ| ^ K := by
  have hcd_b : ContDiff ℝ ∞ baseBump :=
    contDiff_infty.mpr fun n => contDiff_baseBump (n := n)
  obtain ⟨C, hC, hbound⟩ := exists_norm_integral_cexp_le_pow K
    hcd_b tsupport_baseBump_subset
  refine ⟨C, hC, fun γ s hs hne => ?_⟩
  rw [tr_twist, tr_eq]
  set w : ℂ := s - (γ : ℂ) * I - 1 / 2
  have hwre : |w.re| ≤ 1 / 2 := by
    have : w.re = s.re - 1 / 2 := by simp [w]
    rwa [this]
  have hwim_eq : w.im = s.im - γ := by simp [w]
  have hwim : w.im ≠ 0 := by rw [hwim_eq]; exact sub_ne_zero.mpr hne
  simpa [hwim_eq] using hbound w hwre hwim

/-! ## §3. Near-ordinate `baseBump` coercivity and unit-window depth charge -/

/-- **Near-ordinate `baseBump` coercivity.** Whenever `|s.im - γ| ≤ A` with `0 ≤ A` and
`A / 4 < π / 2`, `(Real.cos (A / 4))² ≤ Complex.normSq (tr (twist γ baseBump) s)`. -/
theorem cos_quarter_mul_sq_le_normSq_tr_twist_baseBump {A γ : ℝ} {s : ℂ}
    (hA0 : 0 ≤ A) (hApi : A / 4 < Real.pi / 2) (him : |s.im - γ| ≤ A) :
    Real.cos (A / 4) ^ 2 ≤ Complex.normSq (tr (twist γ baseBump) s) := by
  set δ : ℝ := s.re - 1 / 2
  set dω : ℝ := s.im - γ
  have hcos_pos : 0 < Real.cos (A / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hApi⟩
  rw [tr_twist, tr_eq]
  have hexp_re : ∀ u : ℝ, (baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))).re =
      baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u) := by
    intro u
    have hw : (s - (γ : ℂ) * I - 1 / 2) * (u : ℂ) = ((δ * u : ℝ) : ℂ) + ((dω * u : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [δ, dω]
    rw [baseBump, hw, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.I_re,
      Complex.sin_ofReal_im, Complex.I_im, mul_one, mul_zero, add_zero]
    ring
  have hint_c : Integrable (fun u : ℝ => baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))) :=
    ((contDiff_baseBump (n := ⊤)).continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport
      hasCompactSupport_baseBump.mul_right
  have hre_int : (∫ u : ℝ, baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))).re =
      ∫ u : ℝ, baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u) :=
    ((RCLike.reCLM (K := ℂ)).integral_comp_comm hint_c).symm.trans
      (integral_congr_ae (Eventually.of_forall fun u => hexp_re u))
  have hint_pos : Integrable (fun u : ℝ => baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u)) :=
    (((contDiff_baseBumpReal (n := ⊤)).continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (hasCompactSupport_baseBumpReal.mul_right.mul_right)
  have hint_neg : Integrable (fun u : ℝ => baseBumpReal u * Real.exp (-(δ * u)) * Real.cos (dω * u)) :=
    (((contDiff_baseBumpReal (n := ⊤)).continuous.mul
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_const.mul continuous_id)))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (hasCompactSupport_baseBumpReal.mul_right.mul_right)
  have hsym : (∫ u : ℝ, baseBumpReal u * Real.exp (-(δ * u)) * Real.cos (dω * u)) =
      ∫ u : ℝ, baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [baseBumpReal_even, mul_neg, neg_neg, Real.cos_neg]
  have hcosh_eq : (∫ u : ℝ, baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u)) =
      ∫ u : ℝ, baseBumpReal u * Real.cosh (δ * u) * Real.cos (dω * u) := by
    have hfun : (fun u : ℝ => baseBumpReal u * Real.cosh (δ * u) * Real.cos (dω * u)) =
        fun u => (1 / 2 : ℝ) * (baseBumpReal u * Real.exp (δ * u) * Real.cos (dω * u) +
          baseBumpReal u * Real.exp (-(δ * u)) * Real.cos (dω * u)) := by
      ext u; rw [Real.cosh_eq]; ring
    rw [hfun, integral_const_mul, integral_add hint_pos hint_neg, hsym]
    ring
  have hint_cosh : Integrable (fun u : ℝ => baseBumpReal u * Real.cosh (δ * u) * Real.cos (dω * u)) :=
    (((contDiff_baseBumpReal (n := ⊤)).continuous.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (hasCompactSupport_baseBumpReal.mul_right.mul_right)
  have hint_b : Integrable baseBumpReal := baseContDiffBump.integrable_normed
  have hre_ge : Real.cos (A / 4) ≤
      (∫ u : ℝ, baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))).re := by
    rw [hre_int, hcosh_eq, ← mul_one (Real.cos (A / 4)), ← integral_baseBumpReal, ← integral_const_mul]
    refine integral_mono (hint_b.const_mul _) hint_cosh fun u => ?_
    dsimp only
    by_cases hu : 1 / 4 ≤ |u|
    · rw [baseBumpReal_eq_zero_of_abs_ge hu, mul_zero, zero_mul, zero_mul]
    · have hu_le : |u| ≤ 1 / 4 := (not_le.mp hu).le
      have hdωu : |dω * u| ≤ A / 4 := by
        calc |dω * u| = |dω| * |u| := abs_mul _ _
          _ ≤ A * (1 / 4) := mul_le_mul him hu_le (abs_nonneg _) hA0
          _ = A / 4 := by ring
      have hcos_le : Real.cos (A / 4) ≤ Real.cos (dω * u) := by
        rw [← Real.cos_abs (dω * u)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hdωu
      have hcosh1 : 1 ≤ Real.cosh (δ * u) := Real.one_le_cosh _
      have hb0 : 0 ≤ baseBumpReal u := baseBumpReal_nonneg u
      calc Real.cos (A / 4) * baseBumpReal u
          = baseBumpReal u * 1 * Real.cos (A / 4) := by ring
        _ ≤ baseBumpReal u * Real.cosh (δ * u) * Real.cos (dω * u) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hcosh1 hb0) hcos_le hcos_pos.le
              (mul_nonneg hb0 (by linarith))
  rw [Complex.normSq_apply]
  set z := ∫ u : ℝ, baseBump u * Complex.exp ((s - (γ : ℂ) * I - 1 / 2) * (u : ℂ))
  nlinarith [sq_nonneg z.im, hcos_pos]

/-- Positivity of `(Real.cos (1 / 4))²`. -/
theorem cos_quarter_sq_pos : 0 < Real.cos (1 / 4 : ℝ) ^ 2 := by
  have : 0 < Real.cos (1 / 4 : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  positivity

/-- Positivity of `(Real.cos (5 / 8))²`. -/
theorem cos_five_eighths_sq_pos : 0 < Real.cos (5 / 8 : ℝ) ^ 2 := by
  have : 0 < Real.cos (5 / 8 : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  positivity

/-- **Unit-window depth-charge lower bound on `heckeDefect`.** For every `T, L ∈ ℝ` and every
`γ ∈ [T, T + 1)`,
`(cos(1/4))² ∑_{ρ ∈ xiUnitWindowZeros T} ord_ξ(ρ) depthKernel L (ρ.re - 1/2) ≤ heckeDefect (baseTwistTest γ) L`. -/
theorem unitWindow_depthCharge_le_heckeDefect (T L : ℝ) {γ : ℝ}
    (hγT : T ≤ γ) (hγT1 : γ ≤ T + 1) :
    Real.cos (1 / 4 : ℝ) ^ 2 *
      (∑ ρ ∈ xiUnitWindowZeros T,
        ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2)) ≤
      heckeDefect (baseTwistTest γ) L := by
  classical
  have hmem_c : ∀ z ∈ xiUnitWindowZeros T, z ∈ zetaZeroConfig.carrier := by
    intro z hz
    obtain ⟨hS, _⟩ := mem_xiUnitWindowZeros.mp hz
    obtain ⟨⟨h0, h1, _, _⟩, hxi⟩ := (Set.Finite.mem_toFinset _).mp hS
    exact CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mpr
      ⟨hxi, h0, h1⟩
  let emb : {z // z ∈ xiUnitWindowZeros T} → zetaZeroConfig.carrier :=
    fun z => ⟨z.1, hmem_c z.1 z.2⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : zetaZeroConfig.carrier => (x : ℂ)) h)
  let S : Finset zetaZeroConfig.carrier := (xiUnitWindowZeros T).attach.image emb
  have hsum_eq :
      ∑ ρ ∈ S, Real.cos (1 / 4 : ℝ) ^ 2 *
        (((analyticOrderAt xi (ρ : ℂ)).toNat : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)) =
      Real.cos (1 / 4 : ℝ) ^ 2 *
        ∑ ρ ∈ xiUnitWindowZeros T,
          ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L (ρ.re - 1 / 2) := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h), Finset.mul_sum,
      ← Finset.sum_attach (xiUnitWindowZeros T)]
  rw [← hsum_eq]
  have hterm : ∀ z : {z // z ∈ xiUnitWindowZeros T},
      Real.cos (1 / 4 : ℝ) ^ 2 * (((analyticOrderAt xi z.1).toNat : ℝ) * depthKernel L (z.1.re - 1 / 2)) ≤
        zetaWeight (baseTwistTest γ) (emb z) * depthKernel L (zetaDepth (emb z)) := by
    intro z
    obtain ⟨hSz, hTle⟩ := mem_xiUnitWindowZeros.mp z.2
    obtain ⟨⟨h0, h1, _, hlt1⟩, _⟩ := (Set.Finite.mem_toFinset _).mp hSz
    have hmult : (analyticOrderAt xi z.1).toNat = zetaZeroConfig.mult z.1 := by
      change (analyticOrderAt xi z.1).toNat = (analyticOrderAt riemannZeta z.1).toNat
      exact congrArg ENat.toNat (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩)
    have him : |z.1.im - γ| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hcos := cos_quarter_mul_sq_le_normSq_tr_twist_baseBump (A := 1) zero_le_one
      (by linarith [Real.pi_gt_three]) him
    rw [hmult]
    dsimp [zetaWeight, baseTwistTest, zetaDepth, emb]
    have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult z.1 := Nat.cast_nonneg _
    have hdk0 : 0 ≤ depthKernel L (z.1.re - 1 / 2) := depthKernel_nonneg _ _
    calc Real.cos (1 / 4 : ℝ) ^ 2 *
          ((zetaZeroConfig.mult z.1 : ℝ) * depthKernel L (z.1.re - 1 / 2))
        = (zetaZeroConfig.mult z.1 : ℝ) * Real.cos (1 / 4 : ℝ) ^ 2 *
            depthKernel L (z.1.re - 1 / 2) := by ring
      _ ≤ (zetaZeroConfig.mult z.1 : ℝ) *
            Complex.normSq (tr (twist γ baseBump) z.1) * depthKernel L (z.1.re - 1 / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcos hm0) hdk0
  refine (Finset.sum_le_sum fun z hz => ?_).trans
    ((summable_heckeDefect (baseTwistTest γ) L).sum_le_tsum S
      fun ρ _ => mul_nonneg (zetaWeight_nonneg _ _) (depthKernel_nonneg _ _))
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
  exact hterm y

/-! ## §4. Master separated-ordinate `heckeAvgBump` bound -/

/-- Exact interval integral `∫_{-L}^L e^{zℓ} dℓ = (e^{zL} - e^{-zL}) / z` for `z ≠ 0`. -/
theorem intervalIntegral_cexp_mul_eq_div {L : ℝ} {z : ℂ} (hz : z ≠ 0) :
    (∫ l in (-L)..L, Complex.exp (z * (l : ℂ))) =
      (Complex.exp (z * (L : ℂ)) - Complex.exp (-(z * (L : ℂ)))) / z := by
  rw [integral_exp_mul_complex hz]
  push_cast
  ring

/-- Exact squared-norm identity `‖e^{(δ + i dω)L} - e^{-(δ + i dω)L}‖² = depthKernel L δ + 4 sin²(dω L)`. -/
private theorem normSq_exp_sub_exp_neg_eq (L δ dω : ℝ) :
    Complex.normSq (Complex.exp ((((δ : ℂ) + (dω : ℂ) * I)) * (L : ℂ)) -
      Complex.exp (-((((δ : ℂ) + (dω : ℂ) * I)) * (L : ℂ)))) =
      depthKernel L δ + 4 * Real.sin (dω * L) ^ 2 := by
  have hz1 : (((δ : ℂ) + (dω : ℂ) * I)) * (L : ℂ) = ((δ * L : ℝ) : ℂ) + ((dω * L : ℝ) : ℂ) * I := by
    push_cast; ring
  have hz2 : -((((δ : ℂ) + (dω : ℂ) * I)) * (L : ℂ)) =
      ((-(δ * L) : ℝ) : ℂ) + ((-(dω * L) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hz2, hz1, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_zero, zero_mul, add_zero,
    Complex.cos_ofReal_im, Complex.sub_im, Complex.mul_im, Complex.add_im, zero_add,
    Real.cos_neg, Real.sin_neg]
  have hdk : depthKernel L δ = (Real.exp (δ * L) - Real.exp (-(δ * L))) ^ 2 := by
    rw [depthKernel_eq_four_sinh_sq, Real.sinh_eq]; ring
  have hexp_prod : Real.exp (δ * L) * Real.exp (-(δ * L)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have htrig : Real.cos (dω * L) ^ 2 + Real.sin (dω * L) ^ 2 = 1 := Real.cos_sq_add_sin_sq (dω * L)
  rw [hdk]
  nlinarith [hexp_prod, htrig]

/-- **Master separated-ordinate `heckeAvgBump` bound across the critical strip.** For any `L > 0`,
`η > 0`, `γ ∈ ℝ`, and `s ∈ ℂ` with `|s.re - 1/2| ≤ 1/2` and `η ≤ |s.im - γ|`:
`Complex.normSq (tr (twist γ (heckeAvgBump L)) s) ≤ ((1 + η⁻²) e^{1/4} / L²) / (1 + (γ - s.im)²) + (1 / (4 η² L²)) Complex.normSq (tr (twist γ baseBump) s) depthKernel L (s.re - 1/2)`. -/
theorem normSq_tr_twist_heckeAvgBump_le_of_sep_strip {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (γ : ℝ) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) (hsep : η ≤ |s.im - γ|) :
    Complex.normSq (tr (twist γ (heckeAvgBump L)) s) ≤
      (1 + η⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 * (1 / (1 + (γ - s.im) ^ 2)) +
        1 / (4 * η ^ 2 * L ^ 2) *
          (Complex.normSq (tr (twist γ baseBump) s) * depthKernel L (s.re - 1 / 2)) := by
  set δ : ℝ := s.re - 1 / 2
  set dω : ℝ := s.im - γ
  set z : ℂ := s - 1 / 2 - (γ : ℂ) * I
  have hz_eq : z = (δ : ℂ) + (dω : ℂ) * I := by
    apply Complex.ext <;> simp [z, δ, dω]
  have hdω_ne : dω ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hsep
    linarith
  have hz_ne : z ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [hz_eq] at this
    exact hdω_ne this
  have hfac := tr_twist_heckeAvgBump_eq hL γ s
  have hint_const : (∫ l in (-L)..L, Complex.exp (z * (l : ℂ)) * tr (twist γ baseBump) s) =
      (∫ l in (-L)..L, Complex.exp (z * (l : ℂ))) * tr (twist γ baseBump) s :=
    intervalIntegral.integral_mul_const _ _
  rw [show s - 1 / 2 - (γ : ℂ) * I = z from rfl] at hfac
  rw [hfac, hint_const, intervalIntegral_cexp_mul_eq_div hz_ne,
    map_mul, map_mul, map_div₀, ← mul_assoc]
  have hnsq_12L : Complex.normSq (((1 / (2 * L) : ℝ) : ℂ)) = 1 / (4 * L ^ 2) := by
    rw [Complex.normSq_ofReal]; ring
  have hnsq_num : Complex.normSq (Complex.exp (z * (L : ℂ)) - Complex.exp (-(z * (L : ℂ)))) ≤
      depthKernel L δ + 4 := by
    rw [hz_eq, normSq_exp_sub_exp_neg_eq]
    have hsin : Real.sin (dω * L) ^ 2 ≤ 1 := Real.sin_sq_le_one (dω * L)
    linarith
  have hnsq_z : dω ^ 2 ≤ Complex.normSq z := by
    rw [hz_eq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    nlinarith [sq_nonneg δ]
  have hdω_pos : 0 < dω ^ 2 := sq_pos_of_ne_zero hdω_ne
  have hη_sq : η ^ 2 ≤ dω ^ 2 := by
    have := pow_le_pow_left₀ hη.le hsep 2
    rwa [sq_abs] at this
  have hfrac_le : Complex.normSq (((1 / (2 * L) : ℝ) : ℂ)) *
      (Complex.normSq (Complex.exp (z * (L : ℂ)) - Complex.exp (-(z * (L : ℂ)))) /
        Complex.normSq z) ≤
      1 / (L ^ 2 * dω ^ 2) + depthKernel L δ / (4 * η ^ 2 * L ^ 2) := by
    rw [hnsq_12L]
    have h1 : 1 / (4 * L ^ 2) *
        (Complex.normSq (Complex.exp (z * (L : ℂ)) - Complex.exp (-(z * (L : ℂ)))) /
          Complex.normSq z) ≤
        1 / (4 * L ^ 2) * ((depthKernel L δ + 4) / dω ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div₀ (by linarith [depthKernel_nonneg L δ]) hnsq_num hdω_pos hnsq_z
    have h2 : 1 / (4 * L ^ 2) * ((depthKernel L δ + 4) / dω ^ 2) =
        1 / (L ^ 2 * dω ^ 2) + depthKernel L δ / (4 * dω ^ 2 * L ^ 2) := by
      field_simp; ring
    have h3 : depthKernel L δ / (4 * dω ^ 2 * L ^ 2) ≤ depthKernel L δ / (4 * η ^ 2 * L ^ 2) :=
      div_le_div_of_nonneg_left (depthKernel_nonneg L δ) (by positivity) (by nlinarith)
    linarith
  have hlor : 1 / dω ^ 2 ≤ (1 + η⁻¹ ^ 2) * (1 / (1 + (γ - s.im) ^ 2)) := by
    have hdω_sym : (γ - s.im) ^ 2 = dω ^ 2 := by dsimp [dω]; ring
    rw [hdω_sym, mul_one_div, div_le_div_iff₀ hdω_pos (by positivity)]
    have hprod : η⁻¹ ^ 2 * dω ^ 2 ≥ 1 := by
      rw [inv_pow, inv_mul_eq_div, ge_iff_le, one_le_div (by positivity)]
      exact hη_sq
    nlinarith
  have hb_exp : Complex.normSq (tr (twist γ baseBump) s) ≤ Real.exp (1 / 4) := by
    rw [Complex.normSq_eq_norm_sq]
    have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_tr_twist_baseBump_le_exp γ hs) 2
    refine hle.trans_eq ?_
    rw [← Real.exp_nat_mul]
    norm_num
  set B_s := Complex.normSq (tr (twist γ baseBump) s)
  have hB0 : 0 ≤ B_s := Complex.normSq_nonneg _
  calc Complex.normSq (((1 / (2 * L) : ℝ) : ℂ)) *
        (Complex.normSq (Complex.exp (z * (L : ℂ)) - Complex.exp (-(z * (L : ℂ)))) /
          Complex.normSq z) * B_s
      ≤ (1 / (L ^ 2 * dω ^ 2) + depthKernel L δ / (4 * η ^ 2 * L ^ 2)) * B_s :=
        mul_le_mul_of_nonneg_right hfrac_le hB0
    _ = (1 / L ^ 2) * (1 / dω ^ 2) * B_s +
          1 / (4 * η ^ 2 * L ^ 2) * (B_s * depthKernel L δ) := by ring
    _ ≤ (1 / L ^ 2) * ((1 + η⁻¹ ^ 2) * (1 / (1 + (γ - s.im) ^ 2))) * Real.exp (1 / 4) +
          1 / (4 * η ^ 2 * L ^ 2) * (B_s * depthKernel L δ) := by
        have hterm1 : (1 / L ^ 2) * (1 / dω ^ 2) * B_s ≤
            (1 / L ^ 2) * ((1 + η⁻¹ ^ 2) * (1 / (1 + (γ - s.im) ^ 2))) * Real.exp (1 / 4) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hlor (by positivity)) hb_exp hB0
            (by positivity)
        linarith
    _ = (1 + η⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 * (1 / (1 + (γ - s.im) ^ 2)) +
          1 / (4 * η ^ 2 * L ^ 2) * (B_s * depthKernel L (s.re - 1 / 2)) := by
        dsimp [δ]; ring

/-- Specialization of `normSq_tr_twist_heckeAvgBump_le_of_sep_strip` to `ρ ∈ zetaZeroConfig.carrier`. -/
theorem normSq_tr_twist_heckeAvgBump_le_of_sep {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (γ : ℝ) (ρ : zetaZeroConfig.carrier) (hsep : η ≤ |(ρ : ℂ).im - γ|) :
    Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) ≤
      (1 + η⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2)) +
        1 / (4 * η ^ 2 * L ^ 2) *
          (Complex.normSq (tr (twist γ baseBump) ρ) * depthKernel L (zetaDepth ρ)) :=
  normSq_tr_twist_heckeAvgBump_le_of_sep_strip hL hη γ (abs_zetaDepth_le ρ) hsep

/-! ## §5. Pole-reflection decomposition and all-`c` archimedean bounds -/

/-- Dictionary `paperFT f (I/2 - γ) = tr (twist γ f) 0` and
`paperFT f (-I/2 - γ) = tr (twist γ f) 1`. -/
theorem paperFT_pole_sub_eq_tr_twist (f : ℝ → ℂ) (γ : ℝ) :
    paperFT f (I / 2 - (γ : ℂ)) = tr (twist γ f) 0 ∧
      paperFT f (-I / 2 - (γ : ℂ)) = tr (twist γ f) 1 := by
  constructor
  · rw [paperFT, tr_twist, tr_eq]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only; congr 1; congr 1; ring_nf; rw [I_sq]; ring
  · rw [paperFT, tr_twist, tr_eq]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only; congr 1; congr 1; ring_nf; rw [I_sq]; ring

/-- Since `heckeAvgBump L` is real and even, `tr (twist γ (heckeAvgBump L)) 0 = conj (tr (twist γ (heckeAvgBump L)) 1)`. -/
theorem tr_twist_heckeAvgBump_zero_eq_conj_one (L γ : ℝ) :
    tr (twist γ (heckeAvgBump L)) 0 = conj (tr (twist γ (heckeAvgBump L)) 1) := by
  rw [tr_twist, tr_twist, tr_eq, tr_eq]
  have hconj_int : conj (∫ u : ℝ, heckeAvgBump L u * Complex.exp ((1 - (γ : ℂ) * I - 1 / 2) * (u : ℂ))) =
      ∫ u : ℝ, conj (heckeAvgBump L u * Complex.exp ((1 - (γ : ℂ) * I - 1 / 2) * (u : ℂ))) :=
    (starL' ℝ (A := ℂ)).integral_comp_comm _ |>.symm
  rw [hconj_int, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [heckeAvgBump, heckeAvgReal_even, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1; congr 1
  simp [Complex.conj_I, map_ofNat]
  ring

/-- Exact pole-term identity for `heckeAvgBump L` (`L > 0`) at `ξ = -γ / (2π)`: the pole contribution
to `(archPart (heckeAvgBump L) (-γ / (2π))).re` equals `2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re`. -/
theorem re_pole_terms_heckeAvgBump_eq {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    (paperFT (EF.weilTest (heightShift (-γ / (2 * Real.pi)) (heckeAvgBump L))
        (heightShift (-γ / (2 * Real.pi)) (heckeAvgBump L))) (I / 2) +
      paperFT (EF.weilTest (heightShift (-γ / (2 * Real.pi)) (heckeAvgBump L))
        (heightShift (-γ / (2 * Real.pi)) (heckeAvgBump L))) (-I / 2)).re =
      2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re := by
  set ξ : ℝ := -γ / (2 * Real.pi)
  set g := heightShift ξ (heckeAvgBump L)
  have hg : ContDiff ℝ 2 g := heightShift_contDiff (contDiff_heckeAvgBump L) ξ
  have hgs : tsupport g ⊆ Icc (-(L + 1 / 4)) (L + 1 / 4) :=
    (tsupport_heightShift_subset ξ (heckeAvgBump L)).trans (tsupport_heckeAvgBump_subset hL)
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc,
    EF.paperFT_weilTest hg.continuous hg.continuous hgc hgc, hc1, hc2,
    paperFT_heightShift, paperFT_heightShift]
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) * (ξ : ℂ) = -(γ : ℂ) := by
    simp only [ξ]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  rw [show I / 2 + 2 * (Real.pi : ℂ) * (ξ : ℂ) = I / 2 - (γ : ℂ) by rw [h2pi]; ring,
    show -I / 2 + 2 * (Real.pi : ℂ) * (ξ : ℂ) = -I / 2 - (γ : ℂ) by rw [h2pi]; ring]
  obtain ⟨hp0, hp1⟩ := paperFT_pole_sub_eq_tr_twist (heckeAvgBump L) γ
  rw [hp0, hp1, tr_twist_heckeAvgBump_zero_eq_conj_one]
  set z₁ := tr (twist γ (heckeAvgBump L)) 1
  rw [conj_conj]
  have hconj_sq : conj z₁ * conj z₁ = conj (z₁ ^ 2) := by rw [sq, map_mul]
  rw [hconj_sq, ← sq, Complex.add_re, Complex.conj_re]
  ring

/-- **Scale-uniform two-sided `mu`-integral bound for `heckeAvgBump L`.** There exists `C_mu > 0`
such that for all `L ≥ 1` and `γ ∈ ℝ`,
`|(archPart (heckeAvgBump L) (-γ / 2π)).re - 2 Re((tr (twist γ F_L) 1)²)| ≤ C_mu + log(2 + |γ|) / (2L)`. -/
theorem exists_abs_re_archPart_sub_pole_heckeAvgBump_le :
    ∃ C_mu : ℝ, 0 < C_mu ∧ ∀ L γ : ℝ, 1 ≤ L →
      |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re -
          2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re| ≤
        C_mu + Real.log (2 + |γ|) / (2 * L) := by
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := exists_mu_le
  set B := heckeAvgEnvelopeCap
  have hB0 : 0 ≤ B := (envelope_nonneg (heckeAvgBump 1)).trans (envelope_heckeAvgBump_le le_rfl)
  set C_mu := B ^ 2 * (1 / 2 + Real.pi * C₀) + 5 + 1
  refine ⟨C_mu, by positivity, fun L γ hL1 => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  set ξ : ℝ := -γ / (2 * Real.pi)
  have hf := contDiff_heckeAvgBump L
  have hfs := tsupport_heckeAvgBump_subset hLpos
  have hg : ContDiff ℝ 2 (heightShift ξ (heckeAvgBump L)) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ (heckeAvgBump L)) ⊆ Icc (-(L + 1 / 4)) (L + 1 / 4) :=
    (tsupport_heightShift_subset ξ (heckeAvgBump L)).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hwi : Integrable fun τ : ℝ => ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ (heckeAvgBump L))
      (heightShift ξ (heckeAvgBump L))) τ * (mu τ : ℂ)).re =
      ∫ τ : ℝ, ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ (heckeAvgBump L))
        (heightShift ξ (heckeAvgBump L))) τ * (mu τ : ℂ)) = fun τ : ℝ =>
        ((‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ; rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  have hdiff : (archPart (heckeAvgBump L) ξ).re - 2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re =
      ∫ τ : ℝ, ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    rw [archPart, Complex.add_re, re_pole_terms_heckeAvgBump_eq hLpos γ, hμre]
    ring
  rw [hdiff]
  have hup := integral_norm_sq_paperFT_shift_mul_mu_le hC₀_nn hC₀ hf hfs ξ
  have h2piξ : 2 * Real.pi * |ξ| = |γ| := by
    simp only [ξ, abs_div, abs_neg, abs_of_pos Real.two_pi_pos]; field_simp
  have he_eq : 4 * ((∫ u, ‖heckeAvgBump L u‖) + ∫ u, ‖deriv (deriv (heckeAvgBump L)) u‖) =
      envelope (heckeAvgBump L) := rfl
  rw [he_eq, h2piξ] at hup
  -- Pointwise lower bound `mu τ ≥ -10 / (2π)` from `mu_ge_log τ`
  have hkdf := EF.weilTest_contDiff hf hf.continuous hfc
  have hkcf := EF.weilTest_hasCompactSupport hfc hfc
  have hFi : Integrable fun σ : ℝ => ‖paperFT (heckeAvgBump L) σ‖ ^ 2 := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkdf hkcf)).re.congr
      (Eventually.of_forall fun σ => ?_)
    simp only [paperFT_weilTest_self_ofReal hf.continuous hfc σ, RCLike.re_to_complex,
      Complex.ofReal_re]
  have hFyi : Integrable fun τ : ℝ => ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 :=
    hFi.comp_add_right (2 * Real.pi * ξ)
  have hlow_int : (-10 : ℝ) * (∫ t, ‖heckeAvgBump L t‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hmono : (∫ τ : ℝ, ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 *
        (-10 / (2 * Real.pi))) ≤
        ∫ τ : ℝ, ‖paperFT (heckeAvgBump L) ((τ + 2 * Real.pi * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
      refine integral_mono (hFyi.mul_const _) hwi fun τ => ?_
      dsimp only
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hm := mu_ge_log τ
      have hlog0 : 0 ≤ Real.log (1 + |τ| / 4) := Real.log_nonneg (by linarith [abs_nonneg τ])
      calc (-10 : ℝ) / (2 * Real.pi)
          ≤ (Real.log (1 + |τ| / 4) - 10) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right (by linarith) Real.two_pi_pos.le
        _ ≤ mu τ := hm
    rw [integral_mul_const,
      integral_add_right_eq_self (fun σ : ℝ => ‖paperFT (heckeAvgBump L) σ‖ ^ 2) (2 * Real.pi * ξ),
      integral_norm_sq_paperFT_eq hf hfs] at hmono
    have hsimp : (2 * Real.pi * ∫ t, ‖heckeAvgBump L t‖ ^ 2) * (-10 / (2 * Real.pi)) =
        (-10 : ℝ) * ∫ t, ‖heckeAvgBump L t‖ ^ 2 := by
      have hπ : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
      field_simp
    rwa [hsimp] at hmono
  have henv : envelope (heckeAvgBump L) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (envelope_nonneg _) (envelope_heckeAvgBump_le hL1) 2
  have hL2 := integral_norm_sq_heckeAvgBump_le hLpos
  have hN_half : ∫ t, ‖heckeAvgBump L t‖ ^ 2 ≤ 1 / 2 :=
    hL2.trans (div_le_div_of_nonneg_left zero_le_one zero_lt_two (by linarith))
  have hlog12 : Real.log (1 + |γ|) ≤ Real.log (2 + |γ|) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [abs_le]
  constructor
  · have h0 : 0 ≤ Real.log (2 + |γ|) / (2 * L) :=
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg γ])) (by positivity)
    have hBmu : 0 ≤ B ^ 2 * (1 / 2 + Real.pi * C₀) := by positivity
    dsimp [C_mu]
    linarith
  · have ht1 : (∫ t, ‖heckeAvgBump L t‖ ^ 2) * Real.log (1 + |γ|) ≤
        Real.log (2 + |γ|) / (2 * L) := by
      calc (∫ t, ‖heckeAvgBump L t‖ ^ 2) * Real.log (1 + |γ|)
          ≤ (1 / (2 * L)) * Real.log (2 + |γ|) :=
            mul_le_mul hL2 hlog12 (Real.log_nonneg (by linarith [abs_nonneg γ])) (by positivity)
        _ = Real.log (2 + |γ|) / (2 * L) := by ring
    have ht2 : envelope (heckeAvgBump L) ^ 2 * (1 / 2 + Real.pi * C₀) ≤
        B ^ 2 * (1 / 2 + Real.pi * C₀) :=
      mul_le_mul_of_nonneg_right henv (by positivity)
    dsimp [C_mu]
    linarith [sq_nonneg B]

/-- Bound `‖tr (twist γ (heckeAvgBump L)) 1‖ ≤ e^{L/2} ‖tr (twist γ baseBump) 1‖` for `L > 0`. -/
theorem norm_tr_twist_heckeAvgBump_one_le {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    ‖tr (twist γ (heckeAvgBump L)) 1‖ ≤
      Real.exp (L / 2) * ‖tr (twist γ baseBump) 1‖ := by
  rw [tr_twist_heckeAvgBump_eq hL γ 1, intervalIntegral.integral_mul_const,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos one_pos (mul_pos zero_lt_two hL))]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hint : IntervalIntegrable (fun _ : ℝ => Real.exp (L / 2)) volume (-L) L :=
    intervalIntegrable_const
  have hle : ‖∫ l in (-L)..L, Complex.exp (((1 : ℂ) - 1 / 2 - (γ : ℂ) * I) * (l : ℂ))‖ ≤
      ∫ l in (-L)..L, Real.exp (L / 2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_ hint
    refine Eventually.of_forall fun l hl => ?_
    rw [mem_Ioc] at hl
    rw [Complex.norm_exp]
    have hre : (((1 : ℂ) - 1 / 2 - (γ : ℂ) * I) * (l : ℂ)).re = l / 2 := by
      simp; ring
    rw [hre]
    exact Real.exp_le_exp.mpr (by linarith [hl.2])
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_neg_eq_add] at hle
  calc 1 / (2 * L) * ‖∫ l in (-L)..L, Complex.exp (((1 : ℂ) - 1 / 2 - (γ : ℂ) * I) * (l : ℂ))‖
      ≤ 1 / (2 * L) * ((L + L) * Real.exp (L / 2)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Real.exp (L / 2) := by field_simp; ring

/-- **All-`c` two-sided archimedean bound at `L = c log T`.** For every `c > 0` (with NO upper
restriction on `c`), there exists `C_arch > 0` such that for all `T ≥ 2` with `1 ≤ c * log T` and
all `γ ∈ [T, T + 1)`, `|(archPart (heckeAvgBump (c * log T)) (-γ / 2π)).re| ≤ C_arch`. -/
theorem exists_abs_re_archPart_heckeAvgBump_log_le {c : ℝ} (hc : 0 < c) :
    ∃ C_arch : ℝ, 0 < C_arch ∧ ∀ T γ : ℝ, 2 ≤ T → 1 ≤ c * Real.log T →
      T ≤ γ → γ ≤ T + 1 →
      |(archPart (heckeAvgBump (c * Real.log T)) (-γ / (2 * Real.pi))).re| ≤ C_arch := by
  obtain ⟨C_mu, hCmu, hmu_bd⟩ := exists_abs_re_archPart_sub_pole_heckeAvgBump_le
  set K : ℕ := ⌈c⌉₊ + 1
  obtain ⟨C_K, hCK, hpw⟩ := exists_norm_tr_twist_baseBump_le_pow K
  refine ⟨C_mu + 2 / c + 2 * C_K ^ 2, by positivity, fun T γ hT2 hL1 hγT hγT1 => ?_⟩
  set L : ℝ := c * Real.log T
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hγ_pos : 0 < γ := by linarith
  have hsub := hmu_bd L γ hL1
  have hpole_norm : |2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re| ≤ 2 * C_K ^ 2 := by
    have h1 : |2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re| ≤
        2 * ‖tr (twist γ (heckeAvgBump L)) 1‖ ^ 2 := by
      rw [abs_mul, abs_of_pos zero_lt_two, ← norm_pow]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) zero_le_two
    have h2 : ‖tr (twist γ (heckeAvgBump L)) 1‖ ≤ Real.exp (L / 2) * (C_K / γ ^ K) := by
      refine (norm_tr_twist_heckeAvgBump_one_le hLpos γ).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hpw1 := hpw γ 1 (by norm_num) (by simp; linarith)
      simpa [abs_of_pos hγ_pos] using hpw1
    have hexp_le : Real.exp (L / 2) ≤ γ ^ K := by
      have hcK : c / 2 ≤ (K : ℝ) := by
        have hceil : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
        have hKcast : (K : ℝ) = (⌈c⌉₊ : ℝ) + 1 := by simp [K]
        linarith
      have hTpos : 0 < T := by linarith
      calc Real.exp (L / 2)
          = Real.exp ((c / 2) * Real.log T) := by dsimp [L]; ring_nf
        _ ≤ Real.exp ((K : ℝ) * Real.log T) := by
            refine Real.exp_le_exp.mpr ?_
            exact mul_le_mul_of_nonneg_right hcK (Real.log_nonneg (by linarith))
        _ = T ^ K := by rw [Real.exp_nat_mul, Real.exp_log hTpos]
        _ ≤ γ ^ K := pow_le_pow_left₀ hTpos.le hγT K
    have hγK_pos : (0 : ℝ) < γ ^ K := pow_pos hγ_pos K
    have h3 : Real.exp (L / 2) * (C_K / γ ^ K) ≤ C_K := by
      calc Real.exp (L / 2) * (C_K / γ ^ K)
          = (Real.exp (L / 2) * C_K) / γ ^ K := (mul_div_assoc _ _ _).symm
        _ ≤ (γ ^ K * C_K) / γ ^ K :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp_le hCK.le) hγK_pos.le
        _ = C_K := mul_div_cancel_left₀ C_K hγK_pos.ne'
    have h4 : ‖tr (twist γ (heckeAvgBump L)) 1‖ ≤ C_K := h2.trans h3
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h4 2) zero_le_two)
  have hlog_le : Real.log (2 + |γ|) / (2 * L) ≤ 2 / c := by
    have habsγ : |γ| = γ := abs_of_pos hγ_pos
    rw [habsγ]
    have h2γ : 2 + γ ≤ T ^ 3 := by
      have : 0 ≤ (T - 2) * (T ^ 2 + 2 * T + 3) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    have hlog2γ : Real.log (2 + γ) ≤ 3 * Real.log T := by
      calc Real.log (2 + γ) ≤ Real.log (T ^ 3) := Real.log_le_log (by positivity) h2γ
        _ = 3 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
    have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
    calc Real.log (2 + γ) / (2 * L)
        ≤ (3 * Real.log T) / (2 * (c * Real.log T)) :=
          div_le_div_of_nonneg_right hlog2γ (by positivity)
      _ = 3 / (2 * c) := by field_simp
      _ ≤ 4 / (2 * c) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      _ = 2 / c := by field_simp; norm_num
  have htri := abs_add_le
    ((archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re -
      2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re)
    (2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re)
  rw [sub_add_cancel] at htri
  have htri' : |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re| ≤
      |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re -
          2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re| +
        |2 * ((tr (twist γ (heckeAvgBump L)) 1) ^ 2).re| := htri
  linarith

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_depthKernel_scale_transfer
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_norm_tr_twist_baseBump_le_pow
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_depthCharge_le_heckeDefect
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.normSq_tr_twist_heckeAvgBump_le_of_sep_strip
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_abs_re_archPart_sub_pole_heckeAvgBump_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_abs_re_archPart_heckeAvgBump_log_le
