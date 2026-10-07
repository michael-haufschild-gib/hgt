import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound

/-!
# Sharp gamma cost of polar integer resonators

The existing polar resonators have exact diagonal mass and integer samples.
Their gamma cost is bounded above by mass times `log N + O(1)`, with leading
coefficient exactly one. These are estimates on actual smooth functions;
no Weil positivity or arithmetic coefficient premise is imposed.

This is a dependency of the critical-coefficient argument in
`docs/reports/weil-work/results/01-pbap/CRITICAL-SLOPE.md`, not a proof of PBAP.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped Real ComplexConjugate ContDiff

noncomputable section
namespace RHTower.WeilWorkPBAP
open ResonatorProfile

/-- Positive mass of the shrinking polar profile. -/
def resonatorMass (N : ℕ) : ℝ := ∫ t, gR (1 / ((N : ℝ) + 1)) t ^ 2

/-- The fixed additive gamma cost of the profile. -/
def resonatorGammaConstant : ℝ := Real.log 2 + 9 / 2 + profileRatio / 2

theorem resonatorMass_pos (N : ℕ) : 0 < resonatorMass N := by
  have hw : 0 < 1 / ((N : ℝ) + 1) := by positivity
  exact lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity))
    (integral_gR_sq_ge hw)

theorem contDiff_resonator_infty (N : ℕ) (c : ℕ → ℂ) (w : ℝ) :
    ContDiff ℝ ∞ (resonator N c w) :=
  contDiff_infty.mpr (contDiff_resonator N c w)

/-- The exact Fourier mass and sharp leading logarithmic gamma bound. -/
theorem resonator_fourier_mass_and_arch_bound {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) :
    (∫ t : ℝ, ‖paperFT (resonator N c (1 / ((N : ℝ) + 1))) t‖ ^ 2) =
        2 * π * resonatorMass N * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 ∧
    (∫ t : ℝ, ‖paperFT (resonator N c (1 / ((N : ℝ) + 1))) t‖ ^ 2 *
        archimedeanWeilSymbol (t / (2 * π))) ≤
      2 * π * resonatorMass N *
        ((Real.log N + resonatorGammaConstant) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2) := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set w : ℝ := 1 / ((N : ℝ) + 1) with hwdef
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by rw [hwdef, div_le_one hN1]; linarith
  have hwN : w * ((N : ℝ) + 1) = 1 := by rw [hwdef]; field_simp
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
  set a : ℝ := Real.log N / 2 + w / 4 with hadef
  have ha : 0 ≤ a := by positivity
  set F := resonator N c w with hFdef
  set F' := resonatorDeriv N c w with hF'def
  have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) hu
  have hF'van : ∀ u, a < |u| → F' u = 0 := fun u hu =>
    sum_translates_eq_zero (fun v hv => deriv_gC_eq_zero hw hv) hu
  have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
  have hF's : tsupport F' ⊆ Icc (-a) a := tsupport_subset_of_vanish hF'van
  have hF2 : ContDiff ℝ 2 F := contDiff_resonator N c w 2
  have hF'2 : ContDiff ℝ 2 F' := contDiff_resonatorDeriv N c w 2
  have hFcs : HasCompactSupport F :=
    hasCompactSupport_of_support_subset_abs (Λ := a) fun u hu => by
      by_contra h; push Not at h; exact hu (hFvan u h)
  -- the autocorrelation masses
  set k0r : ℝ := ∫ t, gR w t ^ 2 with hk0r
  set k1r : ℝ := ∫ t, gR' w t ^ 2 with hk1r
  have hk0 : EF.weilTest (gC w) (gC w) 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := gR w)
  have hk1 : EF.weilTest (deriv (gC w)) (deriv (gC w)) 0 = (k1r : ℂ) := by
    rw [deriv_gC]; exact weilTest_self_zero_ofReal (g := gR' w)
  have hgap : 2 * (w / 4) < 1 / ((N : ℝ) + 1) := by
    rw [← hwdef]; linarith
  have hvan0 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by linarith)
  have hvan1 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| →
      EF.weilTest (deriv (gC w)) (deriv (gC w)) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => deriv_gC_eq_zero hw hu) (by linarith)
  have hgc0 : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgc1 : Continuous (deriv (gC w)) := (contDiff_deriv_gC w 0).continuous
  have hgs0 := hasCompactSupport_gC hw
  have hgs1 := hasCompactSupport_deriv_gC hw
  set sumc : ℝ := ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 with hsumc
  have hsum : 0 ≤ sumc := Finset.sum_nonneg fun m _ => sq_nonneg _
  -- the Plancherel masses
  have hmass0 : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 = 2 * π * k0r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF2 hFs 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc0 hgs0 hvan0 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m) from rfl, h0, hk0,
      sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hmass1 : ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = 2 * π * k1r * sumc := by
    have h := integral_normSq_paperFT_mul_cos_eq hF'2 hF's 0
    simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
    rw [h]
    have h0 := weilTest_translates_log (n := 1) hgc1 hgs1 hvan1 hc le_rfl
    simp only [Nat.cast_one, Real.log_one] at h0
    rw [show F' = fun u => ∑ m ∈ Finset.Icc 1 N, c m * deriv (gC w) (u - resPt N m) from rfl, h0,
      hk1, sum_mul_conj_eq]
    simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  -- the archimedean symbol on the spectrum of the resonator
  have hderiv : ∀ τ : ℝ, ‖paperFT F' τ‖ ^ 2 = τ ^ 2 * ‖paperFT F τ‖ ^ 2 := by
    intro τ
    rw [hF'def, ← deriv_resonator, paperFT_deriv (contDiff_resonator N c w 1) hFcs]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_pow, sq_abs]
  set α : ℝ := Real.log ((N : ℝ) + 1) + 9 / 2 with hα
  set β : ℝ := w ^ 2 / 2 with hβ
  have hpt : ∀ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2 := by
    intro τ
    have hA := archimedeanWeilSymbol_le_log_add τ
    have hpos1 : 0 < 1 + w * |τ| := by positivity
    have hle : 1 + |τ| ≤ ((N : ℝ) + 1) * (1 + w * |τ|) := by
      have : ((N : ℝ) + 1) * (1 + w * |τ|) = (N : ℝ) + 1 + |τ| := by
        rw [mul_add, mul_one, ← mul_assoc, mul_comm ((N : ℝ) + 1) w, hwN, one_mul]
      rw [this]; linarith
    have hlog1 : Real.log (1 + |τ|) ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
      calc Real.log (1 + |τ|) ≤ Real.log (((N : ℝ) + 1) * (1 + w * |τ|)) :=
            Real.log_le_log (by positivity) hle
        _ = Real.log ((N : ℝ) + 1) + Real.log (1 + w * |τ|) :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ Real.log ((N : ℝ) + 1) + w * |τ| := by
            have := Real.log_le_sub_one_of_pos hpos1; linarith
    have hamgm : w * |τ| ≤ 1 / 2 + w ^ 2 * τ ^ 2 / 2 := by
      have := sq_nonneg (w * |τ| - 1)
      have h2 : (w * |τ|) ^ 2 = w ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith
    have hA' : archimedeanWeilSymbol (τ / (2 * π)) ≤ α + β * τ ^ 2 := by
      rw [hα, hβ]; linarith
    rw [hderiv τ]
    have hnn : 0 ≤ ‖paperFT F τ‖ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left hA' hnn
    linarith
  have hint1 := integrable_normSq_paperFT_mul_arch hF2 hFs
  have hint2 := integrable_normSq_paperFT hF2 hFs
  have hint3 := integrable_normSq_paperFT hF'2 hF's
  have harch : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) ≤
      α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by
    calc ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))
        ≤ ∫ τ : ℝ, (α * ‖paperFT F τ‖ ^ 2 + β * ‖paperFT F' τ‖ ^ 2) :=
          integral_mono hint1 ((hint2.const_mul α).add (hint3.const_mul β)) hpt
      _ = α * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) + β * ∫ τ : ℝ, ‖paperFT F' τ‖ ^ 2 := by
          rw [integral_add (hint2.const_mul α) (hint3.const_mul β), integral_const_mul,
            integral_const_mul]
      _ = α * (2 * π * k0r * sumc) + β * (2 * π * k1r * sumc) := by rw [hmass0, hmass1]
  have hratio : β * k1r ≤ profileRatio / 2 * k0r := by
    have := sq_mul_integral_gR'_le hw hw1
    rw [hβ, hk1r, hk0r]; nlinarith
  have hlog2 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith)
  refine ⟨hmass0, ?_⟩
  have h1 : β * (2 * π * k1r * sumc) ≤ 2 * π * sumc * (profileRatio / 2 * k0r) := by
    have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * π * sumc by positivity)
    linarith
  have hk0nn : 0 ≤ k0r := integral_nonneg fun _ => sq_nonneg _
  have hlead : α + profileRatio / 2 ≤ Real.log N + resonatorGammaConstant := by
    dsimp [resonatorGammaConstant, hα]
    linarith
  have h2 := mul_le_mul_of_nonneg_left hlead
    (show 0 ≤ 2 * π * k0r * sumc by positivity)
  change (∫ t : ℝ, ‖paperFT F t‖ ^ 2 * archimedeanWeilSymbol (t / (2 * π))) ≤
    2 * π * k0r * ((Real.log N + resonatorGammaConstant) * sumc)
  linarith

theorem archimedeanWeilSymbol_paper (t : ℝ) :
    archimedeanWeilSymbol (t / (2 * π)) = EF.gammaBracket t := by
  rw [archimedeanWeilSymbol_eq, WeilHerglotz.gammaBracket_eq]
  rw [show π * (t / (2 * π)) = t / 2 by field_simp]

theorem hasCompactSupport_resonator {N : ℕ} (c : ℕ → ℂ) {w : ℝ} (hw : 0 < w) :
    HasCompactSupport (resonator N c w) := by
  apply hasCompactSupport_of_support_subset_abs (Λ := Real.log N / 2 + w / 4)
  intro u hu
  by_contra h
  push Not at h
  exact hu (sum_translates_eq_zero (fun v hv => gC_eq_zero hw hv) h)

/-- Both poles vanish exactly, before any positivity argument. -/
theorem resonator_poles (N : ℕ) (c : ℕ → ℂ) :
    paperFT (resonator N c (1 / ((N : ℝ) + 1))) (I / 2) = 0 ∧
    paperFT (resonator N c (1 / ((N : ℝ) + 1))) (-(I / 2)) = 0 :=
  paperFT_resonator_pole (by positivity)

/-- Every integer sample is the corresponding multiplicative coefficient correlation. -/
theorem resonator_log_sample (N : ℕ) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) (n : ℕ) (hn : 1 ≤ n) :
    let F := resonator N c (1 / ((N : ℝ) + 1))
    (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
      2 * resonatorMass N *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re := by
  let w : ℝ := 1 / ((N : ℝ) + 1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hgap : 2 * (w / 4) < 1 / ((N : ℝ) + 1) := by change 2 * (w / 4) < w; linarith
  have hvan : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest (gC w) (gC w) Y = 0 :=
    fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by linarith)
  have hgc : Continuous (gC w) := (contDiff_gC w 0).continuous
  have hgs := hasCompactSupport_gC hw
  have h1 := weilTest_translates_log hgc hgs hvan hc hn
  have h2 := weilTest_translates_neg_log hgc hgs hvan hc hn
  have hk : EF.weilTest (gC w) (gC w) 0 = ((∫ t, gR w t ^ 2 : ℝ) : ℂ) :=
    weilTest_self_zero_ofReal (g := gR w)
  rw [sum_conj_swap] at h2
  change (EF.weilTest (resonator N c w) (resonator N c w) (Real.log n) +
    EF.weilTest (resonator N c w) (resonator N c w) (-Real.log n)).re = _
  rw [show resonator N c w =
    (fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC w (u - resPt N m)) from rfl,
    h1, h2, hk]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re]
  change _ = 2 * (∫ t, gR w t ^ 2) * _
  ring

/-- Physical mass of the actual resonator, with no cross terms. -/
theorem resonator_mass {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) :
    (∫ u, ‖resonator N c (1 / ((N : ℝ) + 1)) u‖ ^ 2) =
      resonatorMass N * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  have h := LebesgueAtomWeil.integral_norm_sq_paperFT_eq
    (contDiff_resonator N c (1 / ((N : ℝ) + 1)) 2)
    (hasCompactSupport_resonator c (by positivity))
  rw [(resonator_fourier_mass_and_arch_bound hN c hc).1] at h
  rw [← h]
  field_simp

/-- Sharp coefficient one in the gamma cost, for arbitrary complex coefficients. -/
theorem resonator_gamma_bound {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    (hc : ∀ m, N < m → c m = 0) :
    (1 / (2 * π)) * (∫ t : ℝ,
        ‖paperFT (resonator N c (1 / ((N : ℝ) + 1))) t‖ ^ 2 * EF.gammaBracket t) ≤
      resonatorMass N *
        ((Real.log N + resonatorGammaConstant) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2) := by
  have h := (resonator_fourier_mass_and_arch_bound hN c hc).2
  simp_rw [archimedeanWeilSymbol_paper] at h
  have hp : (0 : ℝ) < 2 * π := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hp]
  calc
    _ ≤ 2 * π * resonatorMass N *
        ((Real.log N + resonatorGammaConstant) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2) := h
    _ = _ := by ring

end RHTower.WeilWorkPBAP
