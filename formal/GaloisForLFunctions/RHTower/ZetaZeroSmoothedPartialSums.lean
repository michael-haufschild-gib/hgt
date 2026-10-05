import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# Smoothed partial sums of `ζ` at a zero

Let `ν` be smooth, supported in `[1/2, 2]` (`IsHalfTwoBump`), with `∫ ν(x) dx/x = 1`, and let
`ψ = Smooth1 ν ε` be the smoothed indicator of `(0, 1]`, whose Mellin transform is `ν̃(εs)/s`.

* `exists_norm_mellin_le_rpow_of_bump`: `|ν̃(s)| ≤ C_K/|Im s|^K` on every vertical strip, for every
  `K` (repeated integration by parts; the support keeps away from `0` and `∞`), and `ν̃` is entire.
* `exists_norm_tsum_smooth1_zeroCoeff_sub_le`: if `ζ(ρ) = 0` with `0 < Re ρ < 1`, then for every
  `A > 0`

  `Σ_n n^{−ρ} ψ(n/X) = ν̃(ε(1 − ρ)) X^{1−ρ}/(1 − ρ) + O(X^{−A})`   uniformly in `X > 0`.

**Proof.**  The smoothed Perron formula writes the sum as
`(1/2πi)∫_{(3/2)} ζ(s + ρ) ν̃(εs) X^s ds/s`.  Because `ζ(ρ) = 0` the integrand
`Z_ρ(s) ν̃(εs) X^s`, `Z_ρ(s) = ζ(s + ρ)/s`, is holomorphic at `s = 0`; its only singularity is the
simple pole at `s = 1 − ρ`.  Shift to `Re s = −A`: the residue is the main term, the horizontal
edges vanish because `ν̃` decays faster than any power while `ζ` grows polynomially on strips, and
the new line contributes `X^{−A} ∫ |Z_ρ ν̃(ε·)|`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

namespace RHTower

noncomputable section

/-- Smooth real functions supported in `[1/2, 2]`. -/
def IsHalfTwoBump (g : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ Function.support g ⊆ Icc (1 / 2) 2

theorem IsHalfTwoBump.deriv {g : ℝ → ℝ} (hg : IsHalfTwoBump g) : IsHalfTwoBump (deriv g) := by
  refine ⟨?_, ?_⟩
  · have := hg.1.iterate_deriv 1
    simpa using this
  · refine (support_deriv_subset).trans ?_
    exact closure_minimal hg.2 isClosed_Icc

theorem rpow_le_two_rpow_abs_of_mem_Icc {x r : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) :
    x ^ r ≤ 2 ^ |r| := by
  have hx0 : 0 < x := by linarith [hx.1]
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr]
    exact Real.rpow_le_rpow hx0.le hx.2 hr
  · rw [abs_of_neg hr]
    have h1 : x ^ r = (x⁻¹) ^ (-r) := by
      rw [Real.inv_rpow hx0.le, Real.rpow_neg hx0.le, inv_inv]
    rw [h1]
    have hinv : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]; linarith [hx.1]
    exact Real.rpow_le_rpow (by positivity) hinv (by linarith)

/-- The Mellin transform of a continuous function supported in `[1/2, 2]` is bounded on vertical
strips. -/
theorem exists_norm_mellin_le_of_support {g : ℝ → ℝ} (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (1 / 2) 2) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖mellin (fun x : ℝ => (g x : ℂ)) s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hg.continuousOn
  set R : ℝ := 2 ^ (|a - 1| + |b - 1|) with hR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 (by norm_num))
  refine ⟨R * M * 2, by positivity, fun s hs1 hs2 => ?_⟩
  unfold mellin
  have hbound : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • ((g x : ℝ) : ℂ)‖ ≤
      (Icc (1 / 2 : ℝ) 2).indicator (fun _ => R * M) x := by
    intro x hx
    by_cases hxI : x ∈ Icc (1 / 2 : ℝ) 2
    · rw [Set.indicator_of_mem hxI, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
        Complex.norm_real]
      have h1 : x ^ (s - 1).re ≤ R := by
        refine (rpow_le_two_rpow_abs_of_mem_Icc hxI).trans ?_
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (s - 1).re = s.re - 1 := by simp
        rw [this]
        rcases le_or_gt 0 (s.re - 1) with h | h
        · rw [abs_of_nonneg h]
          have := abs_nonneg (a - 1); have := le_abs_self (b - 1); linarith
        · rw [abs_of_neg h]
          have := abs_nonneg (b - 1); have := neg_abs_le (a - 1); linarith
      exact mul_le_mul h1 (hM x hxI) (norm_nonneg _) (by positivity)
    · have hg0 : g x = 0 := by
        by_contra h; exact hxI (hsupp h)
      rw [Set.indicator_of_notMem hxI, hg0]; simp
  have hint0 : Integrable ((Icc (1 / 2 : ℝ) 2).indicator (fun _ => R * M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (continuous_const.integrableOn_Icc)
  have hint : Integrable ((Icc (1 / 2 : ℝ) 2).indicator (fun _ => R * M))
      (volume.restrict (Ioi 0)) := hint0.restrict
  calc ‖∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • ((g x : ℝ) : ℂ)‖
      ≤ ∫ x in Ioi (0 : ℝ), (Icc (1 / 2 : ℝ) 2).indicator (fun _ => R * M) x :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hbound))
    _ ≤ ∫ x, (Icc (1 / 2 : ℝ) 2).indicator (fun _ => R * M) x :=
        setIntegral_le_integral hint0
          (Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => by positivity) x)
    _ = R * M * (3 / 2) := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
          Real.volume_real_Icc_of_le (by norm_num)]
        ring
    _ ≤ R * M * 2 := by gcongr; norm_num

/-- **All-order Mellin decay of a smooth bump.**  For `g` smooth and supported in `[1/2, 2]`,
`|𝓜g(s)| ≤ C_K/|Im s|^K` on every vertical strip, for `|Im s| ≥ 1`. -/
theorem exists_norm_mellin_le_rpow_of_bump :
    ∀ (K : ℕ) {g : ℝ → ℝ}, IsHalfTwoBump g → ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
        ‖mellin (fun x : ℝ => (g x : ℂ)) s‖ ≤ C / |s.im| ^ K := by
  intro K
  induction K with
  | zero =>
    intro g hg a b
    obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_le_of_support hg.1.continuous hg.2 a b
    exact ⟨C, hC0, fun s h1 h2 _ => by simpa using hC s h1 h2⟩
  | succ K ih =>
    intro g hg a b
    obtain ⟨C, hC0, hC⟩ := ih hg.deriv (a + 1) (b + 1)
    refine ⟨C, hC0, fun s h1 h2 h3 => ?_⟩
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at h3; simp at h3; linarith
    have hparts := MellinOfPsi_aux (hg.1.of_le (by exact_mod_cast le_top)) hg.2 hs0
    have hmel : mellin (fun x : ℝ => (g x : ℂ)) s =
        -(1 / s) * mellin (fun x : ℝ => ((deriv g x : ℝ) : ℂ)) (s + 1) := by
      unfold mellin
      have e1 : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • ((g x : ℝ) : ℂ) =
          ∫ x in Ioi (0 : ℝ), ((g x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
        congr 1; funext x; rw [smul_eq_mul, mul_comm]
      have e2 : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s + 1 - 1) • ((deriv g x : ℝ) : ℂ) =
          ∫ x in Ioi (0 : ℝ), ((deriv g x : ℝ) : ℂ) * (x : ℂ) ^ s := by
        congr 1; funext x; rw [smul_eq_mul, mul_comm, add_sub_cancel_right]
      rw [e1, e2, hparts]
    have hb := hC (s + 1) (by simp; linarith) (by simp; linarith) (by simpa using h3)
    simp only [Complex.add_im, Complex.one_im, add_zero] at hb
    have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hpos : 0 < |s.im| := by linarith
    rw [hmel, norm_mul, norm_neg, norm_div, norm_one]
    calc 1 / ‖s‖ * ‖mellin (fun x : ℝ => ((deriv g x : ℝ) : ℂ)) (s + 1)‖
        ≤ 1 / |s.im| * (C / |s.im| ^ K) :=
          mul_le_mul (one_div_le_one_div_of_le hpos him) hb (norm_nonneg _) (by positivity)
      _ = C / |s.im| ^ (K + 1) := by rw [pow_succ]; field_simp

/-- The Mellin transform of a smooth bump is entire. -/
theorem differentiable_mellin_of_bump {g : ℝ → ℝ} (hg : IsHalfTwoBump g) :
    Differentiable ℂ (mellin (fun x : ℝ => (g x : ℂ))) := by
  intro s
  have hzero_top : (fun x : ℝ => (g x : ℂ)) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have : g x = 0 := by
      by_contra h; have := (hg.2 h).2; linarith
    simp [this]
  have hzero_bot : (fun x : ℝ => (g x : ℂ)) =ᶠ[𝓝[>] 0] 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    have : g x = 0 := by
      by_contra h; have := (hg.2 h).1; linarith [hx.2]
    simp [this]
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    ((Complex.continuous_ofReal.comp hg.1.continuous).locallyIntegrable.locallyIntegrableOn _)
    ?_ (by linarith) ?_
    (by linarith)
  · exact (hzero_top.isBigO).trans (isBigO_zero _ _)
  · exact (hzero_bot.isBigO).trans (isBigO_zero _ _)

/-! ## The Dirichlet series of a shifted zeta -/

/-- `c_n = n^{−ρ}` for `n ≥ 1`, `c_0 = 0`. -/
def zeroCoeff (ρ : ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else (n : ℂ) ^ (-ρ)

theorem norm_zeroCoeff_le {ρ : ℂ} (hρ : 0 ≤ ρ.re) (n : ℕ) : ‖zeroCoeff ρ n‖ ≤ 1 := by
  unfold zeroCoeff
  split_ifs with hn
  · simp
  · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
      (by linarith)

theorem LSeries_zeroCoeff {ρ s : ℂ} (hs : 1 < (s + ρ).re) :
    LSeries (zeroCoeff ρ) s = riemannZeta (s + ρ) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  unfold LSeries
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [zeroCoeff, if_neg hn, Pi.one_apply]
    rw [Complex.cpow_add _ _ hnc, Complex.cpow_neg]
    field_simp

/-! ## The shifted zeta quotient -/

/-- `Z_ρ(s) = ζ(s + ρ)/s`, continued across `s = 0` (where `ζ(ρ) = 0`). -/
def shiftedZetaQuot (ρ : ℂ) : ℂ → ℂ := dslope (fun s => riemannZeta (s + ρ)) 0

theorem shiftedZetaQuot_eq {ρ : ℂ} (hρ : riemannZeta ρ = 0) {s : ℂ} (hs : s ≠ 0) :
    shiftedZetaQuot ρ s = riemannZeta (s + ρ) / s := by
  unfold shiftedZetaQuot
  rw [dslope_of_ne _ hs, slope_def_field]
  simp [hρ]

theorem differentiableAt_shiftedZetaQuot {ρ : ℂ} (hρ1 : ρ ≠ 1) {s : ℂ} (hs : s ≠ 1 - ρ) :
    DifferentiableAt ℂ (shiftedZetaQuot ρ) s := by
  unfold shiftedZetaQuot
  by_cases h0 : s = 0
  · subst h0
    set r : ℝ := ‖1 - ρ‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hρ1))
    have hU : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hr0
    have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + ρ)) (Metric.ball 0 r) := by
      intro z hz
      have hz1 : z + ρ ≠ 1 := by
        intro h
        have : z = 1 - ρ := by linear_combination h
        rw [Metric.mem_ball, dist_zero_right, this] at hz
        exact lt_irrefl _ hz
      exact ((differentiableAt_riemannZeta hz1).comp z
        (differentiableAt_id.add_const ρ)).differentiableWithinAt
    exact ((differentiableOn_dslope hU).mpr hdiff).differentiableAt hU
  · rw [differentiableAt_dslope_of_ne h0]
    have hs1 : s + ρ ≠ 1 := fun h => hs (by linear_combination h)
    exact (differentiableAt_riemannZeta hs1).comp s (differentiableAt_id.add_const ρ)

/-- Polynomial growth of `Z_ρ` on vertical strips. -/
theorem exists_norm_shiftedZetaQuot_le {ρ : ℂ} (hρ : riemannZeta ρ = 0) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |ρ.im| + 1 ≤ |s.im| →
      ‖shiftedZetaQuot ρ s‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|a| + |b| + |ρ.re| + 1)
  refine ⟨C * 2 ^ N, N, by positivity, fun s ha hb him => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at him; simp at him; linarith [abs_nonneg ρ.im]
  rw [shiftedZetaQuot_eq hρ hs0, norm_div]
  have hsim : 1 ≤ |s.im| := by linarith [abs_nonneg ρ.im]
  have hnorm : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hsρ : s + ρ = ((s.re + ρ.re : ℝ) : ℂ) + ((s.im + ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hre : |s.re + ρ.re| ≤ |a| + |b| + |ρ.re| + 1 := by
    have := abs_add_le (s.re) (ρ.re)
    have : |s.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    linarith
  have himt : 1 ≤ |s.im + ρ.im| := by
    have := abs_sub_abs_le_abs_sub s.im (-ρ.im)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hz := hC _ _ hre himt
  rw [← hsρ] at hz
  have himt2 : |s.im + ρ.im| ≤ 2 * |s.im| := by
    have := abs_add_le s.im ρ.im; linarith
  have hpow : |s.im + ρ.im| ^ N ≤ (2 * |s.im|) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) himt2 N
  rw [div_le_iff₀ (by linarith)]
  calc ‖riemannZeta (s + ρ)‖ ≤ C * |s.im + ρ.im| ^ N := hz
    _ ≤ C * (2 * |s.im|) ^ N := mul_le_mul_of_nonneg_left hpow hC0
    _ = C * 2 ^ N * |s.im| ^ N * 1 := by rw [mul_pow]; ring
    _ ≤ C * 2 ^ N * |s.im| ^ N * ‖s‖ := by
        gcongr; linarith

/-! ## Integrability on vertical lines -/

/-- A continuous function on `ℝ` with `|g(y)| ≤ D/y²` for `|y| ≥ y₁` is integrable, with
`|g(y)| ≤ E(1 + |y|)^{−2}` for all `y`. -/
theorem exists_bound_one_add_sq_of_decay {g : ℝ → ℂ} (hg : Continuous g) {y₁ D : ℝ}
    (hy₁ : 1 ≤ y₁) (hD : 0 ≤ D) (hdec : ∀ y : ℝ, y₁ ≤ |y| → ‖g y‖ ≤ D * |y| ^ (-2 : ℝ)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ y : ℝ, ‖g y‖ ≤ E * (1 + |y|) ^ (-2 : ℝ) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -y₁) (b := y₁)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by constructor <;> linarith))
  refine ⟨max (M * (1 + y₁) ^ 2) (4 * D), by positivity, fun y => ?_⟩
  have hpos : 0 < 1 + |y| := by positivity
  have hinv : (1 + |y|) ^ (-2 : ℝ) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two]
  rcases le_or_gt |y| y₁ with hy | hy
  · have h1 := hM y (abs_le.mp hy)
    rw [hinv]
    calc ‖g y‖ ≤ M := h1
      _ = M * (1 + y₁) ^ 2 * ((1 + y₁) ^ 2)⁻¹ := by field_simp
      _ ≤ max (M * (1 + y₁) ^ 2) (4 * D) * ((1 + |y|) ^ 2)⁻¹ := by
          gcongr
          exact le_max_left _ _
  · have h1 := hdec y hy.le
    have hy0 : 0 < |y| := by linarith
    rw [hinv]
    rw [Real.rpow_neg hy0.le, Real.rpow_two] at h1
    calc ‖g y‖ ≤ D * (|y| ^ 2)⁻¹ := h1
      _ ≤ D * (4 * ((1 + |y|) ^ 2)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hD
          rw [show 4 * ((1 + |y|) ^ 2)⁻¹ = 4 / (1 + |y|) ^ 2 by ring, inv_eq_one_div,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = 4 * D * ((1 + |y|) ^ 2)⁻¹ := by ring
      _ ≤ max (M * (1 + y₁) ^ 2) (4 * D) * ((1 + |y|) ^ 2)⁻¹ := by
          gcongr; exact le_max_right _ _

/-! ## The smoothed partial sums at a zero -/

/-- The product `Z_ρ(s) ν̃(εs)` (no `X^s`). -/
def zeroSmoothKernel (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (s : ℂ) : ℂ :=
  shiftedZetaQuot ρ s * mellin (fun x : ℝ => (ν x : ℂ)) (ε * s)

theorem exists_norm_zeroSmoothKernel_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (a b : ℝ) :
    ∃ (D y₁ : ℝ), 0 ≤ D ∧ 1 ≤ y₁ ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → y₁ ≤ |s.im| →
      ‖zeroSmoothKernel ν ε ρ s‖ ≤ D * |s.im| ^ (-2 : ℝ) := by
  obtain ⟨CZ, N, hCZ0, hCZ⟩ := exists_norm_shiftedZetaQuot_le hρ a b
  obtain ⟨Cν, hCν0, hCν⟩ := exists_norm_mellin_le_rpow_of_bump (N + 2) hν
    (-(|a| + |b|)) (|a| + |b|)
  refine ⟨CZ * Cν / ε ^ (N + 2), max (|ρ.im| + 1) (1 / ε), by positivity,
    le_max_of_le_left (by linarith [abs_nonneg ρ.im]), fun s ha hb hy => ?_⟩
  have hy1 : |ρ.im| + 1 ≤ |s.im| := le_trans (le_max_left _ _) hy
  have hy2 : 1 / ε ≤ |s.im| := le_trans (le_max_right _ _) hy
  have hyp : 0 < |s.im| := by linarith [abs_nonneg ρ.im]
  have hεs : (↑ε * s).re = ε * s.re := by simp
  have hεsi : (↑ε * s).im = ε * s.im := by simp
  have hstrip1 : -(|a| + |b|) ≤ (↑ε * s).re := by
    rw [hεs]
    have : |ε * s.re| ≤ |a| + |b| := by
      rw [abs_mul, abs_of_pos hε0]
      have : |s.re| ≤ |a| + |b| := by
        rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
      nlinarith [abs_nonneg s.re]
    linarith [neg_abs_le (ε * s.re)]
  have hstrip2 : (↑ε * s).re ≤ |a| + |b| := by
    rw [hεs]
    have : |s.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    have := le_abs_self s.re
    nlinarith [abs_nonneg s.re]
  have him1 : 1 ≤ |(↑ε * s).im| := by
    rw [hεsi, abs_mul, abs_of_pos hε0]
    rw [div_le_iff₀ hε0] at hy2; linarith
  have hZ := hCZ s ha hb hy1
  have hM := hCν (↑ε * s) hstrip1 hstrip2 him1
  rw [hεsi, abs_mul, abs_of_pos hε0, mul_pow] at hM
  unfold zeroSmoothKernel
  rw [norm_mul]
  have hrpow : |s.im| ^ (-2 : ℝ) = |s.im| ^ N / |s.im| ^ (N + 2) := by
    rw [pow_add, Real.rpow_neg hyp.le, Real.rpow_two]
    field_simp
  rw [hrpow]
  calc ‖shiftedZetaQuot ρ s‖ * ‖mellin (fun x : ℝ => (ν x : ℂ)) (↑ε * s)‖
      ≤ (CZ * |s.im| ^ N) * (Cν / (ε ^ (N + 2) * |s.im| ^ (N + 2))) :=
        mul_le_mul hZ hM (norm_nonneg _) (by positivity)
    _ = CZ * Cν / ε ^ (N + 2) * (|s.im| ^ N / |s.im| ^ (N + 2)) := by
        field_simp

theorem differentiableAt_zeroSmoothKernel {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) (ε : ℝ)
    {ρ : ℂ} (hρ1 : ρ ≠ 1) {s : ℂ} (hs : s ≠ 1 - ρ) :
    DifferentiableAt ℂ (zeroSmoothKernel ν ε ρ) s :=
  (differentiableAt_shiftedZetaQuot hρ1 hs).mul
    ((differentiable_mellin_of_bump hν (ε * s)).comp s
      (differentiableAt_id.const_mul (ε : ℂ)))

/-- **Smoothed partial sums of `ζ` at a zero.**  If `ζ(ρ) = 0`, `0 < Re ρ < 1`, then for every
`A > 0` there is `C` with
`|Σ_n n^{−ρ} ψ(n/X) − ν̃(ε(1 − ρ)) X^{1−ρ}/(1 − ρ)| ≤ C X^{−A}`, `ψ = Smooth1 ν ε`, for all
`X > 0`. -/
theorem exists_norm_tsum_smooth1_zeroCoeff_sub_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 0 < X →
      ‖(∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ)) -
          (1 - ρ)⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * (1 - ρ)) * (X : ℂ) ^ (1 - ρ)‖ ≤
        C * X ^ (-A) := by
  have hρne1 : ρ ≠ 1 := fun h => by rw [h] at hρ1; simp at hρ1
  set p : ℂ := 1 - ρ with hp
  have hpre : p.re = 1 - ρ.re := by simp [hp]
  have hp0 : p ≠ 0 := fun h => by rw [h] at hpre; simp at hpre; linarith
  set G : ℂ → ℂ := zeroSmoothKernel ν ε ρ with hG
  -- the left line, independent of `X`
  obtain ⟨D, y₁, hD0, hy₁, hdec⟩ := exists_norm_zeroSmoothKernel_le hν hε0 hε1 hρ (-A) (3 / 2)
  have hleftcont : Continuous fun y : ℝ => G ((-A : ℝ) + (y : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : ((-A : ℝ) : ℂ) + (y : ℂ) * I ≠ p := by
      intro h; have := congrArg Complex.re h; simp [hpre] at this; linarith
    exact ((differentiableAt_zeroSmoothKernel hν ε hρne1 hne).continuousAt).comp
      (f := fun y : ℝ => ((-A : ℝ) : ℂ) + (y : ℂ) * I) (by fun_prop)
  obtain ⟨E, hE0, hE⟩ := exists_bound_one_add_sq_of_decay hleftcont hy₁ hD0 (fun y hy => by
    have := hdec ((-A : ℝ) + (y : ℂ) * I) (by simp) (by simp; linarith) (by simpa using hy)
    simpa using this)
  have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-2 : ℝ) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ)) :=
      integrable_one_add_norm (by norm_num)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  have hGleft : Integrable fun y : ℝ => G ((-A : ℝ) + (y : ℂ) * I) :=
    (hbase.const_mul E).mono' hleftcont.aestronglyMeasurable
      (Eventually.of_forall fun y => hE y)
  set J : ℝ := ∫ y : ℝ, ‖G ((-A : ℝ) + (y : ℂ) * I)‖ with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => norm_nonneg _
  refine ⟨(2 * Real.pi)⁻¹ * J, by positivity, fun X hX => ?_⟩
  set f : ℂ → ℂ := fun s => G s * (X : ℂ) ^ s with hf
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hnormX : ∀ s : ℂ, ‖(X : ℂ) ^ s‖ = X ^ s.re := fun s =>
    Complex.norm_cpow_eq_rpow_re_of_pos hX s
  have hre_line : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * I).re = x := fun x y => by simp
  have hfd : ∀ s : ℂ, s ≠ p → DifferentiableAt ℂ f s := fun s hs =>
    (differentiableAt_zeroSmoothKernel hν ε hρne1 hs).mul
      (differentiableAt_id.const_cpow (Or.inl hXc))
  -- Perron on `Re s = 3/2`
  have hP := GaloisForLFunctions.HTGeometry.SmoothedPerron.verticalIntegral'_eq_tsum_smooth1
    (hν.1.of_le (by exact_mod_cast le_top)) νpos hν.2 mass_one (zeroCoeff ρ) (by simp [zeroCoeff])
    (norm_zeroCoeff_le hρ0.le) hX hε0 hε1 (σ := 3 / 2) (by norm_num) (by norm_num)
  have hright_eq : VerticalIntegral' f (3 / 2) =
      VerticalIntegral' (fun s => LSeries (zeroCoeff ρ) s *
        mellin (fun x ↦ ((Smooth1 ν ε x : ℝ) : ℂ)) s * (X : ℂ) ^ s) (3 / 2) := by
    simp only [VerticalIntegral', VerticalIntegral]
    congr 3
    funext t
    set s : ℂ := ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = 3 / 2 := by simp [hs]
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; norm_num at hsre
    simp only [hf, hG, zeroSmoothKernel]
    rw [shiftedZetaQuot_eq hρ hs0, LSeries_zeroCoeff (by simp [hsre]; linarith),
      MellinOfSmooth1a
        (hν.1.of_le (by exact_mod_cast le_top)) hν.2 hε0 (by rw [hsre]; norm_num)]
    ring
  -- holomorphy
  have hhol : HolomorphicOn f (Set.Icc (-A) (3 / 2) ×ℂ Set.univ \ {p}) := by
    intro s hs
    exact (hfd s hs.2).differentiableWithinAt
  -- the pole
  set R₀ : ℂ := p⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * p) * (X : ℂ) ^ p with hR₀
  have hpole : (f - fun s => R₀ / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    set H : ℂ → ℂ := fun s => zetaResidueUnit (s + ρ) * s⁻¹ *
      mellin (fun x : ℝ => (ν x : ℂ)) (ε * s) * (X : ℂ) ^ s with hH
    have hHd : DifferentiableAt ℂ H p := by
      have h1 : DifferentiableAt ℂ (fun s => zetaResidueUnit (s + ρ)) p :=
        (analyticAt_zetaResidueUnit (p + ρ)).differentiableAt.comp p
          (differentiableAt_id.add_const ρ)
      exact ((h1.mul (differentiableAt_inv hp0)).mul
        ((differentiable_mellin_of_bump hν (ε * p)).comp p
          (differentiableAt_id.const_mul (ε : ℂ)))).mul
        (differentiableAt_id.const_cpow (Or.inl hXc))
    have hHp : H p = R₀ := by
      simp only [hH, hR₀, hp]
      rw [show (1 : ℂ) - ρ + ρ = 1 by ring, zetaResidueUnit_one, one_mul]
    have h := GaloisForLFunctions.HTGeometry.SmoothedPerron.isBigO_div_sub_div hHd
    rw [hHp] at h
    refine h.congr' ?_ (Eventually.of_forall fun s => rfl)
    have hU : {s : ℂ | s ≠ 0} ∈ 𝓝 p := isOpen_ne.mem_nhds hp0
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hU] with s hsp hs0
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsp
    simp only [Pi.sub_apply, hf, hG, hH, zeroSmoothKernel]
    have hs1 : s + ρ ≠ 1 := fun h => hsp (by rw [hp]; linear_combination h)
    have hZu : zetaResidueUnit (s + ρ) = (s + ρ - 1) * riemannZeta (s + ρ) :=
      (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds
    have hsub : s - p = s + ρ - 1 := by rw [hp]; ring
    have hsub0 : s + ρ - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [shiftedZetaQuot_eq hρ hs0, hZu, hsub]
    field_simp
  -- horizontal decay
  set B : ℝ := D * (X ^ (-A) + X ^ (3 / 2 : ℝ)) with hB
  have hhor : ∀ y : ℝ, y₁ ≤ |y| → ∀ x ∈ Ι (-A) (3 / 2),
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y| ^ (-2 : ℝ) := by
    intro y hy x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hdx := hdec ((x : ℂ) + (y : ℂ) * I) (by simp; linarith [hx.1]) (by simp; exact hx.2)
      (by simpa using hy)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at hdx
    have hXx : X ^ x ≤ X ^ (-A) + X ^ (3 / 2 : ℝ) := by
      rcases le_or_gt 1 X with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h hx.2
        linarith [Real.rpow_nonneg hX.le (-A)]
      · have := Real.rpow_le_rpow_of_exponent_ge hX h.le hx.1.le
        linarith [Real.rpow_nonneg hX.le (3 / 2 : ℝ)]
    simp only [hf]
    rw [norm_mul, hnormX, hre_line]
    calc ‖G ((x : ℂ) + (y : ℂ) * I)‖ * X ^ x ≤ D * |y| ^ (-2 : ℝ) *
          (X ^ (-A) + X ^ (3 / 2 : ℝ)) :=
          mul_le_mul hdx hXx (by positivity) (by positivity)
      _ = B * |y| ^ (-2 : ℝ) := by rw [hB]; ring
  have hlim : Tendsto (fun y : ℝ => B * |y| ^ (-2 : ℝ) * |3 / 2 - -A|) atTop (𝓝 0) ∧
      Tendsto (fun y : ℝ => B * |y| ^ (-2 : ℝ) * |3 / 2 - -A|) atBot (𝓝 0) := by
    have hp2 : Tendsto (fun y : ℝ => y ^ (-2 : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    constructor
    · have := ((hp2.comp tendsto_abs_atTop_atTop).const_mul B).mul_const |3 / 2 - -A|
      simpa using this
    · have := ((hp2.comp tendsto_abs_atBot_atTop).const_mul B).mul_const |3 / 2 - -A|
      simpa using this
  have htop : Tendsto (fun y : ℝ => ∫ x in (-A)..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim.1
    filter_upwards [eventually_ge_atTop y₁] with y hy
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hhor y (le_trans hy (le_abs_self y)) x hx
  have hbot : Tendsto (fun y : ℝ => ∫ x in (-A)..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim.2
    filter_upwards [eventually_le_atBot (-y₁)] with y hy
    have hy' : y₁ ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hhor y hy' x hx
  -- integrability on the two lines
  have hleftInt : Integrable fun y : ℝ => f ((-A : ℝ) + (y : ℂ) * I) := by
    refine (hGleft.norm.const_mul (X ^ (-A))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (hleftcont.mul (Continuous.const_cpow (by fun_prop) (Or.inl hXc))).aestronglyMeasurable
    · simp only [hf]
      rw [norm_mul, hnormX, hre_line, mul_comm]
  have hrightInt : Integrable fun y : ℝ => f (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    obtain ⟨D', y₁', hD'0, hy₁', hdec'⟩ :=
      exists_norm_zeroSmoothKernel_le hν hε0 hε1 hρ (3 / 2) (3 / 2)
    have hcont : Continuous fun y : ℝ => G (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun y => ?_
      have hne : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ p := by
        intro h; have := congrArg Complex.re h; simp [hpre] at this; linarith
      exact ((differentiableAt_zeroSmoothKernel hν ε hρne1 hne).continuousAt).comp
        (f := fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) (by fun_prop)
    obtain ⟨E', hE'0, hE'⟩ := exists_bound_one_add_sq_of_decay hcont hy₁' hD'0 (fun y hy => by
      have := hdec' (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) (by simp) (by simp) (by simpa using hy)
      simpa using this)
    refine (hbase.const_mul (E' * X ^ (3 / 2 : ℝ))).mono'
      (hcont.mul (Continuous.const_cpow (by fun_prop) (Or.inl hXc))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hf]
    rw [norm_mul, hnormX, hre_line]
    calc ‖G (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ * X ^ (3 / 2 : ℝ)
        ≤ E' * (1 + |y|) ^ (-2 : ℝ) * X ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hE' y) (by positivity)
      _ = E' * X ^ (3 / 2 : ℝ) * (1 + |y|) ^ (-2 : ℝ) := by ring
  -- the shift
  have hshift := GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole
    (σ := -A) (σ' := 3 / 2) (p := p) (A := R₀) (f := f) (by rw [hpre]; linarith)
    (by rw [hpre]; linarith) hhol hpole hbot htop hleftInt hrightInt
  have hsum : ∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ) =
      R₀ + VerticalIntegral' f (-A) := by
    rw [← hP, ← hright_eq]
    linear_combination hshift
  rw [show (∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ)) - R₀ =
    VerticalIntegral' f (-A) by rw [hsum]; ring]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hnorm : ‖1 / (2 * (Real.pi : ℂ) * I)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, one_div]
  rw [hnorm]
  have hpt : ∀ y : ℝ, ‖f ((-A : ℝ) + (y : ℂ) * I)‖ = X ^ (-A) * ‖G ((-A : ℝ) + (y : ℂ) * I)‖ := by
    intro y
    simp only [hf]
    rw [norm_mul, hnormX, hre_line]
    ring
  have hint := norm_integral_le_integral_norm (μ := volume)
    (fun y : ℝ => f ((-A : ℝ) + (y : ℂ) * I))
  simp_rw [hpt] at hint
  rw [integral_const_mul] at hint
  have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∫ y : ℝ, f (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * Real.pi)⁻¹ * (X ^ (-A) * J) := mul_le_mul_of_nonneg_left hint hπ.le
    _ = (2 * Real.pi)⁻¹ * J * X ^ (-A) := by ring

end

end RHTower
