import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonBlockBelowTheGridIsSharp
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.HTGeometry.InvAbsTailL2
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide

/-!
# Fourier recovery below the atom grid

The normalized atomic synthesis recovers a fixed smooth terminal profile in
squared Fourier norm below the grid. A quantitative complex Riemann sum
controls bounded frequencies; the Kuzmin–Landau estimate controls the tail.
On a critical overlap schedule, the error decays after multiplication by
every fixed overlap power, permitting mixed-energy comparisons.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology MeasureTheory Zeta23
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

/-- Normalized atomic synthesis has the normalized Dirichlet transform. -/
theorem paperFT_normalizedCentredAtomicTest {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (x : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    paperFT (cx (normalizedCentredAtomicTest φ x c N)) τ =
      paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ) *
        (((N : ℝ) : ℂ) ^ (-(1 / 2 + Complex.I * τ)) * dirichletPoly N x τ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hscale : (Real.sqrt N / c) * (c / N) = (Real.sqrt N)⁻¹ := by
    field_simp
    nlinarith [Real.sq_sqrt hn.le]
  have hlin : paperFT (cx (normalizedCentredAtomicTest φ x c N)) τ =
      ((Real.sqrt N / c : ℝ) : ℂ) * paperFT (cx (centredAtomicTest φ x c N)) τ := by
    simp only [paperFT_def, cx, normalizedCentredAtomicTest, Complex.ofReal_mul,
      mul_assoc, integral_const_mul]
  rw [hlin, paperFT_centredAtomicTest hφ hφc x hc hN]
  have hexp := inv_sqrt_mul_exp hN (1 / 2 - Complex.I * τ)
  have hpow : ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
      Complex.exp (-(Complex.I * (τ : ℂ) * Real.log N)) =
      ((N : ℝ) : ℂ) ^ (-(1 / 2 + Complex.I * τ)) := by
    have he1 : ((1 / 2 : ℂ) - Complex.I * τ - 1 / 2) * (Real.log N : ℂ) =
        -(Complex.I * (τ : ℂ) * Real.log N) := by ring
    have he2 : (1 / 2 : ℂ) - Complex.I * τ - 1 = -(1 / 2 + Complex.I * τ) := by ring
    rw [he1, he2] at hexp
    exact hexp
  calc
    _ = ((((Real.sqrt N / c) * (c / N) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (τ : ℂ) * Real.log N))) *
        (paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ) * dirichletPoly N x τ) := by
      push_cast
      ring
    _ = _ := by rw [hscale, Complex.ofReal_inv, hpow]; ring

private theorem integral_sq_invAbsTail_scale {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ, ‖HTGeometry.invAbsTail r t‖ ^ 2) =
      r⁻¹ * ∫ t : ℝ, ‖HTGeometry.invAbsTail 1 t‖ ^ 2 := by
  have heq (t : ℝ) : HTGeometry.invAbsTail r t =
      r⁻¹ * HTGeometry.invAbsTail 1 (t / r) := by
    unfold HTGeometry.invAbsTail
    rw [abs_div, abs_of_pos hr]
    have hiff : 1 < |t| / r ↔ r < |t| := by rw [lt_div_iff₀ hr, one_mul]
    by_cases ht : r < |t|
    · rw [if_pos ht, if_pos (hiff.mpr ht), inv_div, ← mul_div_assoc,
        inv_mul_cancel₀ hr.ne', one_div]
    · rw [if_neg ht, if_neg (fun h => ht (hiff.mp h)), mul_zero]
  simp_rw [heq, norm_mul, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_div (fun t : ℝ => ‖HTGeometry.invAbsTail 1 t‖ ^ 2) r, smul_eq_mul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), abs_of_pos hr]
  field_simp

/-- Cutting off an approximation leaves a local error and an integrable quadratic tail. -/
private theorem integral_cutoff_error_le {F G : ℝ → ℂ} {r T E D : ℝ}
    (hr : 0 < r) (hrT : r ≤ T) (hD : 0 ≤ D)
    (hcore : ∀ t, |t| ≤ r → ‖F t - G t‖ ≤ E)
    (hF : ∀ t, |t| ≤ T → ‖F t‖ ^ 2 ≤ D / (1 + t ^ 2))
    (hG : ∀ t, ‖G t‖ ^ 2 ≤ D / (1 + t ^ 2)) :
    (∫ t : ℝ, ‖(if |t| ≤ T then F t else 0) - G t‖ ^ 2) ≤
      2 * r * E ^ 2 + (4 * D / r) *
        ∫ t : ℝ, ‖HTGeometry.invAbsTail 1 t‖ ^ 2 := by
  let core : ℝ → ℝ := (Set.Icc (-r) r).indicator (fun _ => E ^ 2)
  have hci : Integrable core :=
    (integrableOn_const (C := E ^ 2) (s := Set.Icc (-r) r)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hti := (HTGeometry.integrable_sq_invAbsTail hr).const_mul (4 * D)
  have hpoint (t : ℝ) : ‖(if |t| ≤ T then F t else 0) - G t‖ ^ 2 ≤
      core t + 4 * D * ‖HTGeometry.invAbsTail r t‖ ^ 2 := by
    by_cases ht : |t| ≤ r
    · have htT := ht.trans hrT
      have htr : t ∈ Set.Icc (-r) r := abs_le.mp ht
      simp only [if_pos htT, core, Set.indicator_of_mem htr, HTGeometry.invAbsTail,
        if_neg (not_lt.mpr ht), norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcore t ht) 2
    · have hrt : r < |t| := lt_of_not_ge ht
      have htr : t ∉ Set.Icc (-r) r := fun hm => ht (abs_le.mpr hm)
      have ht0 : 0 < t ^ 2 := sq_pos_of_ne_zero (by intro he; simp [he] at hrt; linarith)
      have htail : D / (1 + t ^ 2) ≤ D * ‖HTGeometry.invAbsTail r t‖ ^ 2 := by
        simp only [HTGeometry.invAbsTail, if_pos hrt, Real.norm_eq_abs,
          abs_inv, abs_abs, inv_pow, sq_abs]
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hD ht0 (by linarith)
      simp only [core, Set.indicator_of_notMem htr, zero_add]
      have hgb := (hG t).trans htail
      by_cases htT : |t| ≤ T
      · rw [if_pos htT]
        have hfb := (hF t htT).trans htail
        have htri := norm_sub_le (F t) (G t)
        have hsq := sq_nonneg (‖F t‖ - ‖G t‖)
        nlinarith [sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖F t‖ + ‖G t‖) |>.mpr htri]
      · rw [if_neg htT, zero_sub, norm_neg]
        have hp : 0 ≤ D * ‖HTGeometry.invAbsTail r t‖ ^ 2 := by positivity
        nlinarith only [hgb, hp]
  have hb := integral_mono_of_nonneg
    (Eventually.of_forall fun t => sq_nonneg ‖(if |t| ≤ T then F t else 0) - G t‖)
    (hci.add hti) (Eventually.of_forall hpoint)
  have hcoreint : (∫ t, core t) = 2 * r * E ^ 2 := by
    rw [show core = (Set.Icc (-r) r).indicator (fun _ => E ^ 2) from rfl,
      integral_indicator measurableSet_Icc, setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r), smul_eq_mul]
    ring
  change (∫ t : ℝ, ‖(if |t| ≤ T then F t else 0) - G t‖ ^ 2) ≤
    ∫ t : ℝ, core t + 4 * D * ‖HTGeometry.invAbsTail r t‖ ^ 2 at hb
  rw [integral_add hci hti, hcoreint, integral_const_mul, integral_sq_invAbsTail_scale hr] at hb
  convert hb using 1; ring

/-- The normalized synthesized profile converges in squared Fourier norm below the grid,
with a polynomial error in the overlap and the intermediate frequency cutoff. -/
theorem integral_belowGrid_fourier_error_le {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 1 ≤ N →
      ∀ r : ℝ, 1 ≤ r → r ≤ N * Real.exp (-A) →
      (∫ τ : ℝ, ‖(if |τ| ≤ N * Real.exp (-A) then
          paperFT (cx (normalizedCentredAtomicTest φ (horizonWeights h N) c N)) τ
        else 0) - ((∫ u, φ u : ℝ) : ℂ) *
          horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2) ≤
        C * (c ^ 2 * r ^ 3 / (N : ℝ) ^ 2 + 1 / r) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc hφsupp
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  let D := 2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 * windowConst A Bh L ^ 2)
  let M := ∫ u, |φ u|
  let K := ((Lh : ℝ) + 2 * Bh) * Real.exp (2 * A)
  let J := M * (K + Real.sqrt D)
  let I := ∫ t : ℝ, ‖HTGeometry.invAbsTail 1 t‖ ^ 2
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hM : 0 ≤ M := integral_nonneg fun u => abs_nonneg _
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hJ : 0 ≤ J := mul_nonneg hM (add_nonneg hK (Real.sqrt_nonneg _))
  have hI : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  have hHle (τ : ℝ) : ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 ≤
      D / (1 + τ ^ 2) := normSq_horizonTransform_le hh hA hsupp hB hL τ
  have hHn (τ : ℝ) : ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ≤ Real.sqrt D :=
    Real.le_sqrt_of_sq_le ((hHle τ).trans (div_le_self hD (by nlinarith [sq_nonneg τ])))
  have hm : |∫ u, φ u| ≤ M := abs_integral_le_integral_abs
  have hP (t : ℝ) : ‖paperFT (cx φ) t‖ ≤ M := by
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs] using
      RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) t
  refine ⟨2 * J ^ 2 + 4 * M ^ 2 * D * I, by positivity, ?_⟩
  intro c hc N hN r hr hrT
  have hc0 : 0 < c := by linarith only [hc]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < r := by linarith only [hr]
  let An (τ : ℝ) := ((N : ℝ) : ℂ) ^ (-(1 / 2 + Complex.I * τ)) *
    dirichletPoly N (horizonWeights h N) τ
  let P (τ : ℝ) := paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)
  let H (τ : ℝ) := horizonTransform h (1 / 2 + Complex.I * τ)
  have ha (τ : ℝ) (hτ : |τ| ≤ r) : ‖An τ - H τ‖ ≤ K * r / N := by
    have hs0 : (0 : ℝ) ≤ (1 / 2 + Complex.I * (τ : ℂ)).re := by norm_num
    have hs2 : (1 / 2 + Complex.I * (τ : ℂ)).re ≤ (2 : ℝ) := by norm_num
    have he := norm_riemannSum_sub_le hh hsupp hA hB hLh hs0 hs2 hN
    rw [riemannSum_horizonProfile h _ hN, gammaOf_half_add] at he
    have hs1 : ‖(1 / 2 : ℂ) + Complex.I * τ - 1‖ ≤ 1 / 2 + |τ| := by
      rw [show (1 / 2 : ℂ) + Complex.I * τ - 1 = -(1 / 2 : ℂ) + Complex.I * τ by ring]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    refine he.trans ?_
    apply div_le_div_of_nonneg_right _ hN0.le
    dsimp only [K]
    rw [mul_right_comm _ _ r]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hx := mul_le_mul_of_nonneg_right hs1 hB0
    have hy := mul_le_mul_of_nonneg_right hτ hB0
    have hz := mul_le_mul_of_nonneg_right hr (show 0 ≤ (Lh : ℝ) by positivity)
    have hw := mul_le_mul_of_nonneg_right hr hB0
    nlinarith only [hx, hy, hz, hw, hB0]
  have hp (τ : ℝ) : ‖P τ‖ ≤ M := by
    simpa only [Complex.ofReal_mul] using hP (c / N * τ)
  have hpd (τ : ℝ) (hτ : |τ| ≤ r) :
      ‖P τ - ((∫ u, φ u : ℝ) : ℂ)‖ ≤ c * r / N * M := by
    have he := norm_paperFT_sub_zero_le hφ hφsupp (c / N * τ)
    rw [paperFT_cx_zero, Complex.ofReal_mul, abs_mul, abs_of_pos (div_pos hc0 hN0)] at he
    refine he.trans ?_
    have hmul := mul_le_mul_of_nonneg_left hτ (div_pos hc0 hN0).le
    convert mul_le_mul_of_nonneg_right hmul hM using 1 <;> ring
  have he (τ : ℝ) (hτ : |τ| ≤ r) :
      ‖P τ * An τ - ((∫ u, φ u : ℝ) : ℂ) * H τ‖ ≤ J * c * r / N := by
    calc
      _ = ‖P τ * (An τ - H τ) + (P τ - ((∫ u, φ u : ℝ) : ℂ)) * H τ‖ := by congr 1; ring
      _ ≤ ‖P τ * (An τ - H τ)‖ + ‖(P τ - ((∫ u, φ u : ℝ) : ℂ)) * H τ‖ := norm_add_le _ _
      _ ≤ M * (K * r / N) + (c * r / N * M) * Real.sqrt D := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul (hp τ) (ha τ hτ) (norm_nonneg _) hM)
          (mul_le_mul (hpd τ hτ) (hHn τ) (norm_nonneg _) (by positivity))
      _ ≤ J * c * r / N := by
        have hKc : K ≤ K * c := by nlinarith only [mul_le_mul_of_nonneg_left hc hK]
        have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKc
          (div_pos hr0 hN0).le) hM
        calc
          _ = M * (K * (r / N)) + (c * r / N * M) * Real.sqrt D := by ring
          _ ≤ M * (K * c * (r / N)) + (c * r / N * M) * Real.sqrt D :=
            add_le_add hmul le_rfl
          _ = _ := by dsimp only [J]; ring
  have hf (τ : ℝ) (hτ : |τ| ≤ N * Real.exp (-A)) :
      ‖P τ * An τ‖ ^ 2 ≤ (M ^ 2 * D) / (1 + τ ^ 2) := by
    have had := horizonDirichlet_sq_div_le hsupp hA hB hL hN hτ
    rw [norm_sq_div_eq hN, gammaOf_half_add] at had
    have hpp := pow_le_pow_left₀ (norm_nonneg _) (hp τ) 2
    rw [norm_mul, mul_pow]
    exact (mul_le_mul hpp had (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  have hg (τ : ℝ) : ‖((∫ u, φ u : ℝ) : ℂ) * H τ‖ ^ 2 ≤
      (M ^ 2 * D) / (1 + τ ^ 2) := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hm 2) (hHle τ)
      (sq_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  have hbound := integral_cutoff_error_le hr0 hrT
    (mul_nonneg (sq_nonneg M) hD) he hf hg
  have hident (τ : ℝ) :
      paperFT (cx (normalizedCentredAtomicTest φ (horizonWeights h N) c N)) τ = P τ * An τ :=
    paperFT_normalizedCentredAtomicTest hφ hφc _ hc0 hN τ
  simp_rw [hident]
  refine hbound.trans ?_
  have hx : 0 ≤ c ^ 2 * r ^ 3 / (N : ℝ) ^ 2 := by positivity
  have hy : 0 ≤ 1 / r := by positivity
  have hcross1 := mul_nonneg (show 0 ≤ 2 * J ^ 2 by positivity) hy
  have hcross2 := mul_nonneg (show 0 ≤ 4 * M ^ 2 * D * I by positivity) hx
  change 2 * r * (J * c * r / N) ^ 2 + (4 * (M ^ 2 * D) / r) * I ≤ _
  rw [show 2 * r * (J * c * r / N) ^ 2 = 2 * J ^ 2 * (c ^ 2 * r ^ 3 / (N : ℝ) ^ 2) by ring,
    show (4 * (M ^ 2 * D) / r) * I = (4 * M ^ 2 * D * I) * (1 / r) by ring]
  nlinarith only [hcross1, hcross2]

/-- The squared Fourier error between the truncated synthesized profile and its limit. -/
def belowGridFourierError (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (A : ℝ) : ℝ :=
  ∫ τ : ℝ, ‖(if |τ| ≤ N * Real.exp (-A) then
      paperFT (cx (normalizedCentredAtomicTest φ (horizonWeights h N) c N)) τ
    else 0) - ((∫ u, φ u : ℝ) : ℂ) *
      horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2

/-- On a critical overlap schedule, every fixed overlap power times the below-grid
squared Fourier error tends to zero. -/
theorem tendsto_criticalCurve_belowGrid_fourier_error {φ h : ℝ → ℝ} {A : ℝ}
    (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) (m : ℕ) :
    Tendsto (fun N : ℕ => c N ^ m * belowGridFourierError φ h (c N) N A)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := integral_belowGrid_fourier_error_le hφ hφsupp hh hsupp hA
  have hpow (k : ℕ) : Tendsto (fun N : ℕ => c N ^ k / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc1 hR hcrit k 0
  have hcinf := (criticalCurve_facts hc1 hR hcrit).1
  have hdecay : Tendsto (fun N : ℕ => C * (c N ^ (4 * m + 5) / (N : ℝ) ^ 2 + 1 / c N))
      atTop (𝓝 0) := by
    have hfirst := (hpow (4 * m + 5)).div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    have hsecond : Tendsto (fun N : ℕ => (1 : ℝ) / c N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hcinf
    have hh := (hfirst.add hsecond).const_mul C
    simpa only [div_div, ← pow_two, zero_add, mul_zero] using hh
  refine squeeze_zero' (Eventually.of_forall fun N => mul_nonneg
    (pow_nonneg (le_trans (by norm_num) (hc1 N)) _)
    (integral_nonneg fun _ => sq_nonneg _)) ?_ hdecay
  have hsmall := (hpow (m + 1)).eventually (eventually_le_nhds (Real.exp_pos (-A)))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c N := lt_of_lt_of_le zero_lt_one (hc1 N)
  have hr : 1 ≤ c N ^ (m + 1) := one_le_pow₀ (hc1 N)
  have hrT : c N ^ (m + 1) ≤ N * Real.exp (-A) := by
    have hh := (div_le_iff₀ hN0).mp hsmall
    simpa only [mul_comm] using hh
  have he := mul_le_mul_of_nonneg_left (hb (c N) (hc1 N) N hN (c N ^ (m + 1)) hr hrT)
    (pow_nonneg hc.le m)
  refine he.trans_eq ?_
  field_simp
  simp only [pow_add, pow_mul]
  ring

#print axioms integral_belowGrid_fourier_error_le
#print axioms tendsto_criticalCurve_belowGrid_fourier_error

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
