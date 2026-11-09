import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeilSymbolFromTheGeometricScatteringTower
import GaloisForLFunctions.RHTower.WeilLineIntegralAnyAbscissa

/-!
# Weil packets from renormalized geometric diagonals

The finite energies below use the actual Maass–Selberg pairings, a scalar
archimedean subtraction, and the two boundary poles. Their limit is the
full Weil functional on compactly supported C² autocorrelations. The
identification uses an integrable error bound, not a positivity assumption.
-/

open Complex Filter Topology MeasureTheory Set
open RHTower Zeta23 Zeta23.WeilEF
open RHTower.WeilLineIntegral RHTower.WeilLineAnyAbscissa

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower

noncomputable section

/-- The packet energy of the finite geometric tower on the line `Re s = 3/2`. -/
def geometricWeilEnergy (f : ℝ → ℂ) (N : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    lineF (EF.weilTest f f) (3 / 2) t * renormalizedTower ((3 / 2 : ℂ) + t * I) N

private theorem lamC_mangoldt :
    WeilHerglotz.lamC (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  unfold WeilHerglotz.lamC
  split_ifs with hn
  · rfl
  · have h : ArithmeticFunction.vonMangoldt n = 0 := by interval_cases n <;> simp
    simp [h]

private theorem summable_mangoldt (σ : ℝ) (hσ : 1 < σ) :
    Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ σ := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)
  refine h.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Complex.norm_real, Real.norm_eq_abs]

private theorem weilFunction_mangoldt {s : ℂ} (hs : 1 < s.re) :
    WeilHerglotz.weilFunction (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s =
      logDeriv xi s := by
  rw [weilFunction_eq _ (lt_trans zero_lt_one hs), lamC_mangoldt,
    logDeriv_xi_eq_arithmetic hs, gPair]
  simp only [sub_zero, one_div]
  ring

private theorem continuous_xi_symbol {c : ℝ} (hc : 1 < c) :
    Continuous (fun t : ℝ => logDeriv xi ((c : ℂ) + t * I)) := by
  have hpath : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
  have hd : Continuous (deriv xi) :=
    (xi_differentiable.contDiff (n := 1)).continuous_deriv le_rfl
  simp only [logDeriv_apply]
  exact (hd.comp hpath).div (xi_differentiable.continuous.comp hpath)
    (fun t => xi_ne_zero_of_one_lt_re (by simpa using hc))

/-- An analytic expression used only to prove measurability of the geometric energy. -/
private def analyticTower (s : ℂ) (N : ℕ) : ℂ :=
  logDeriv xi s - logDeriv xi (s + N) + robinCounterterm (s.re + N) +
    1 / (s + N) + 1 / (s + N - 1)

private theorem renormalizedTower_eq_analytic {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) (N : ℕ) : renormalizedTower s N = analyticTower s N := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have h := renormalizedTower_sub_symbol hs him N
  rw [analyticTower, logDeriv_xi_eq_arithmetic hsN]
  simp only [one_div] at h ⊢
  linear_combination h

private theorem continuous_analyticTower {c : ℝ} (hc : 1 < c) (N : ℕ) :
    Continuous (fun t : ℝ => analyticTower ((c : ℂ) + t * I) N) := by
  have hcN : 1 < c + N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hshift : ∀ t : ℝ, ((c : ℂ) + t * I) + N = ((c + N : ℝ) : ℂ) + t * I := by
    intro t
    push_cast
    ring
  unfold analyticTower
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  simp_rw [hshift]
  refine (((continuous_xi_symbol hc).sub (continuous_xi_symbol hcN)).add
    continuous_const |>.add ?_).add ?_
  · refine continuous_const.div (by fun_prop) fun t h => ?_
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hh
    linarith
  · refine continuous_const.div (by fun_prop) fun t h => ?_
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.one_re, Complex.zero_re] at hh
    linarith

private theorem packet_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Continuous (lineF (EF.weilTest f f) (3 / 2)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
        ‖lineF (EF.weilTest f f) (3 / 2) t‖ ≤ C / (1 + t ^ 2) ^ 2 := by
  have hk := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc := EF.weilTest_hasCompactSupport hfc hfc
  have hH := (differentiable_Hfn hk hkc).continuous
  refine ⟨(hH.comp (by fun_prop)).add (hH.comp (by fun_prop)), ?_⟩
  obtain ⟨D, hD, hbound⟩ := norm_Hfn_weilTest_le_wide hf hfc (3 / 2)
  refine ⟨2 * D, by positivity, fun t => ?_⟩
  have h1 := hbound (3 / 2) t (by norm_num)
  have h2 := hbound (-(1 / 2)) (-t) (by norm_num)
  have hpoint : (1 : ℂ) - (3 / 2 : ℝ) - t * I =
      ((-(1 / 2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  rw [lineF, hpoint]
  rw [neg_sq] at h2
  calc ‖Hfn (EF.weilTest f f) ((3 / 2 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (((-(1 / 2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖
      ≤ D / (1 + t ^ 2) ^ 2 + D / (1 + t ^ 2) ^ 2 :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * D / (1 + t ^ 2) ^ 2 := by ring

private theorem xi_symbol_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ,
    ‖logDeriv xi ((3 / 2 : ℂ) + t * I)‖ ≤ A * (1 + |t|) := by
  obtain ⟨A, hA, hb⟩ := WeilAtomic.norm_weilFunction_le summable_mangoldt
    (c := 3 / 2) (by norm_num) le_rfl
  refine ⟨A, hA, fun t => ?_⟩
  have h := hb t
  rw [weilFunction_mangoldt (by norm_num)] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using h

/-- The scalar-normalized geometric diagonal recovers the full Weil functional on packets. -/
theorem tendsto_geometricWeilEnergy {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Tendsto (geometricWeilEnergy f) atTop
      (𝓝 (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f))) := by
  obtain ⟨hFc, C, hC, hFb⟩ := packet_decay hf hfc
  obtain ⟨A, hA, hAb⟩ := xi_symbol_bound
  let F : ℝ → ℂ := lineF (EF.weilTest f f) (3 / 2)
  let B : ℝ := A + eulerMajorant (3 / 2) + 3
  have hB : 0 ≤ B := by dsimp [B]; linarith [eulerMajorant_nonneg (3 / 2)]
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun t : ℝ => F t * renormalizedTower ((3 / 2 : ℂ) + t * I) N) := by
    intro N
    have hc := hFc.mul (continuous_analyticTower (c := 3 / 2) (by norm_num) N)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hc
    refine hc.aestronglyMeasurable.congr ?_
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    change F t * analyticTower ((3 / 2 : ℂ) + t * I) N = _
    rw [renormalizedTower_eq_analytic (by norm_num) (by simpa using ht)]
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ t : ℝ,
      ‖F t * renormalizedTower ((3 / 2 : ℂ) + t * I) N‖ ≤
        2 * C * B * (1 + t ^ 2)⁻¹ := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
    have hden : 1 ≤ (3 / 2 : ℝ) + N := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hlarge : 4 ≤ (((3 / 2 : ℂ) + t * I).re + N) := by
      have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN
      norm_num
      linarith
    have he := norm_renormalizedTower_sub_symbol (s := (3 / 2 : ℂ) + t * I)
      (by norm_num) (by simpa using ht) N hlarge
    rw [show ((3 / 2 : ℂ) + t * I).re = (3 / 2 : ℝ) by norm_num,
      show ((3 / 2 : ℂ) + t * I).im = t by norm_num] at he
    have hpow : (2 : ℝ) ^ (-(N : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg N))
    have hg : (3 + |t| / 2) / ((3 / 2 : ℝ) + N) ≤ 3 + |t| / 2 :=
      div_le_self (by positivity) hden
    have hR : ‖renormalizedTower ((3 / 2 : ℂ) + t * I) N‖ ≤ B * (1 + |t|) := by
      have hn : ‖renormalizedTower ((3 / 2 : ℂ) + t * I) N‖ ≤
          ‖renormalizedTower ((3 / 2 : ℂ) + t * I) N -
            logDeriv xi ((3 / 2 : ℂ) + t * I)‖ +
              ‖logDeriv xi ((3 / 2 : ℂ) + t * I)‖ := by
        calc ‖renormalizedTower ((3 / 2 : ℂ) + t * I) N‖ =
            ‖(renormalizedTower ((3 / 2 : ℂ) + t * I) N -
              logDeriv xi ((3 / 2 : ℂ) + t * I)) +
                logDeriv xi ((3 / 2 : ℂ) + t * I)‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have hp := mul_le_mul_of_nonneg_right hpow (eulerMajorant_nonneg (3 / 2))
      have ha := hAb t
      dsimp [B]
      nlinarith [abs_nonneg t, mul_nonneg (eulerMajorant_nonneg (3 / 2)) (abs_nonneg t)]
    have hsq : 1 + |t| ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, abs_nonneg t]
    rw [norm_mul]
    calc ‖F t‖ * ‖renormalizedTower ((3 / 2 : ℂ) + t * I) N‖
        ≤ (C / (1 + t ^ 2) ^ 2) * (B * (1 + |t|)) :=
          mul_le_mul (hFb t) hR (norm_nonneg _) (by positivity)
      _ ≤ (C / (1 + t ^ 2) ^ 2) * (B * (2 * (1 + t ^ 2))) := by gcongr
      _ = 2 * C * B * (1 + t ^ 2)⁻¹ := by field_simp
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => 2 * C * B * (1 + t ^ 2)⁻¹)
    (Eventually.of_forall hmeas) hbound
    (integrable_inv_one_add_sq.const_mul (2 * C * B))
    (show ∀ᵐ t : ℝ, Tendsto
      (fun N : ℕ => F t * renormalizedTower ((3 / 2 : ℂ) + t * I) N) atTop
      (𝓝 (F t * logDeriv xi ((3 / 2 : ℂ) + t * I))) from by
      filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
      exact (tendsto_renormalizedTower (by norm_num) (by simpa using ht)).const_mul (F t))
  have hsum : LSeriesSummable
      (WeilHerglotz.lamC (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)))
      ((3 / 2 : ℝ) : ℂ) := by
    rw [lamC_mangoldt]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hw := weilFullFunctional_weilTest_eq_line (c := 3 / 2) le_rfl hsum hf hfc
  have hident : (∫ t : ℝ, lineF (EF.weilTest f f) (3 / 2) t *
      WeilHerglotz.weilFunction (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        ((3 / 2 : ℝ) + t * I)) =
      ∫ t : ℝ, F t * logDeriv xi ((3 / 2 : ℂ) + t * I) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [weilFunction_mangoldt (s := ((3 / 2 : ℝ) : ℂ) + t * I) (by norm_num)]
    simp only [F, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hident] at hw
  rw [hw]
  exact hlim.const_mul (1 / (2 * Real.pi) : ℂ)

private theorem integral_line_packet {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (c : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, lineF k c t = 2 * k 0 := by
  have hsingle (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn g ((c : ℂ) + t * I) = g 0 := by
    simp_rw [Hfn_line]
    simpa using line_integral_term hg hgc c (fun _ => (1 : ℂ)) 1
  have hint (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
      Integrable (fun t : ℝ => Hfn g ((c : ℂ) + t * I)) := by
    simp_rw [Hfn_line]
    exact Zeta23.EF.integrable_paperFT_ofReal
      (Zeta23.EF.integrable_fourier_of_contDiff_two (tilt_contDiff hg _)
        (tilt_hasCompactSupport hgc _))
  have hkn : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknc : HasCompactSupport (fun u : ℝ => k (-u)) :=
    hkc.comp_homeomorph (Homeomorph.neg ℝ)
  simp_rw [lineF, Hfn_mirror]
  rw [integral_add (hint k hk hkc) (hint _ hkn hknc), mul_add,
    hsingle k hk hkc, hsingle _ hkn hknc, neg_zero]
  ring

/-- The subtraction is a local diagonal mass, exactly twice the Robin constant times `‖f‖₂²`. -/
theorem robinCounterterm_packet {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (c x : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      lineF (EF.weilTest f f) c t * robinCounterterm x =
        2 * robinCounterterm x * ((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
  have hzero : EF.weilTest f f 0 = ((∫ u : ℝ, ‖f u‖ ^ 2 : ℝ) : ℂ) := by
    unfold EF.weilTest
    rw [convolution_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.mul_apply', EF.tilde, zero_sub, neg_neg,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [integral_mul_const, ← mul_assoc,
    integral_line_packet (EF.weilTest_contDiff hf hf.continuous hfc)
      (EF.weilTest_hasCompactSupport hfc hfc), hzero]
  ring

#print axioms tendsto_geometricWeilEnergy
#print axioms robinCounterterm_packet

end

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
