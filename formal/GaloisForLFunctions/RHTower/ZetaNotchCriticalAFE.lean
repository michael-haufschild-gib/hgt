import GaloisForLFunctions.RHTower.ZetaNotchDualWeightBounds
import GaloisForLFunctions.RHTower.ProductAFEExact
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The windowed twisted second moment of `ζ` through the product AFE

For `t ≠ 0` the exact product approximate functional equation at the conjugate pair
`(½+it, ½−it)` and scale `x = L` reads (`zetaSq_eq_afe`)

`|ζ(½+it)|² = Σ_{m,n} (mn)^{−1/2} V(mn/L) (n/m)^{it} + Σ_{m,n} (mn)^{−1/2} W_t(mnL) (m/n)^{it} − R_L(t)`.

On the critical line `χ(½+it)χ(½−it) = 1`. Against the window `ω` and the oscillation `e^{−iξt}` the
two sums may be exchanged with the height integral (`twistedMoment_eq`):

`∫ ω(t)|ζ(½+it)|² e^{−iξt} dt = Σ_{m,n} (mn)^{−1/2} V(mn/L) ω̂(ξ − log(n/m))
      + Σ_{m,n} (mn)^{−1/2} J(mnL, ξ − log(m/n)) − ∫ ω R_L e^{−iξt}`,

with `ω̂(η) = ∫ ω e^{−iηt}` and `J(Y, η) = ∫ ω W_t(Y) e^{−iηt}`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-! ## `|ζ(½+it)|²` and the critical pair -/

/-- `|ζ(½+it)|²` as the product of the two conjugate values. -/
def zetaSq (t : ℝ) : ℂ := riemannZeta (linePt t) * riemannZeta (linePt (-t))

theorem linePt_neg_eq_conj (t : ℝ) : linePt (-t) = starRingEnd ℂ (linePt t) := by
  unfold linePt
  apply Complex.ext <;> simp

theorem zetaSq_eq_normSq (t : ℝ) : zetaSq t = ((‖riemannZeta (linePt t)‖ ^ 2 : ℝ) : ℂ) := by
  unfold zetaSq
  rw [linePt_neg_eq_conj, riemannZeta_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem linePt_ne_neg {t : ℝ} (ht : t ≠ 0) : linePt t ≠ linePt (-t) := by
  intro h
  have := congrArg Complex.im h
  simp [linePt_im] at this
  exact ht (by linarith)

theorem linePt_neg_eq_one_sub (t : ℝ) : linePt (-t) = 1 - linePt t := by
  unfold linePt
  apply Complex.ext <;> norm_num

theorem zetaChi_mul_zetaChi_line (t : ℝ) : zetaChi (linePt t) * zetaChi (linePt (-t)) = 1 := by
  rw [linePt_neg_eq_one_sub]
  exact zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos t) (linePt_re_lt_one t)

/-! ## The terms of the critical AFE -/

/-- The direct term at the pair `p` (indices `m = p.1 + 1`, `n = p.2 + 1`). -/
def directTerm (L t : ℝ) (p : ℕ × ℕ) : ℂ :=
  (p.1 + 1 : ℂ) ^ (-linePt t) * (p.2 + 1 : ℂ) ^ (-linePt (-t)) *
    smoothAFECutoff (((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)) / L)

/-- The dual term at the pair `p`. -/
def dualTerm (L t : ℝ) (p : ℕ × ℕ) : ℂ :=
  (zetaChi (linePt t) * zetaChi (linePt (-t)) * (p.1 + 1 : ℂ) ^ (linePt t - 1) *
    (p.2 + 1 : ℂ) ^ (linePt (-t) - 1)) *
    productAFEDualWeight (linePt t) (linePt (-t)) ((p.1 + 1 : ℝ) * (p.2 + 1 : ℝ) * L)

/-- The two shifted residues. -/
def residueTerm (L t : ℝ) : ℂ :=
  productAFEShiftedResidue (linePt t) (linePt (-t)) L +
    productAFEShiftedResidue (linePt (-t)) (linePt t) L

/-- **The critical product AFE.** -/
theorem zetaSq_eq_afe {L t : ℝ} (hL : 0 < L) (ht : t ≠ 0) :
    zetaSq t = (∑' p : ℕ × ℕ, directTerm L t p) + (∑' p : ℕ × ℕ, dualTerm L t p) -
      residueTerm L t := by
  have h := riemannZeta_mul_eq_productAFE hL (linePt_re_pos t) (linePt_re_lt_one t)
    (linePt_re_pos (-t)) (linePt_re_lt_one (-t)) (linePt_ne_neg ht)
  unfold zetaSq residueTerm directTerm dualTerm
  rw [h]
  ring

/-! ## Closed forms of the terms -/

/-- The pair amplitude `(mn)^{−1/2}`. -/
def pairAmp (p : ℕ × ℕ) : ℝ :=
  Real.exp (-(Real.log (p.1 + 1 : ℝ) + Real.log (p.2 + 1 : ℝ)) / 2)

/-- The pair frequency `log n − log m`. -/
def pairFreq (p : ℕ × ℕ) : ℝ := Real.log (p.2 + 1 : ℝ) - Real.log (p.1 + 1 : ℝ)

/-- The pair product `mn`. -/
def pairProd (p : ℕ × ℕ) : ℝ := (p.1 + 1 : ℝ) * (p.2 + 1 : ℝ)

theorem pairAmp_pos (p : ℕ × ℕ) : 0 < pairAmp p := Real.exp_pos _

theorem pairProd_pos (p : ℕ × ℕ) : 0 < pairProd p := by unfold pairProd; positivity

theorem pairAmp_eq (p : ℕ × ℕ) : pairAmp p = (Real.sqrt (pairProd p))⁻¹ := by
  unfold pairAmp pairProd
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), Real.rpow_def_of_pos (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  congr 1
  ring

theorem natCast_add_one_cpow (a : ℕ) (z : ℂ) :
    ((a : ℂ) + 1) ^ z = Complex.exp (z * (Real.log ((a : ℝ) + 1) : ℂ)) := by
  have ha : ((a : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [Complex.cpow_def_of_ne_zero ha, mul_comm]
  congr 2
  rw [show ((a : ℂ) + 1) = (((a : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_log (by positivity)]

theorem cpow_pair (t : ℝ) (p : ℕ × ℕ) :
    (p.1 + 1 : ℂ) ^ (-linePt t) * (p.2 + 1 : ℂ) ^ (-linePt (-t)) =
      (pairAmp p : ℂ) * Complex.exp ((t * pairFreq p : ℝ) * I) := by
  rw [natCast_add_one_cpow, natCast_add_one_cpow, ← Complex.exp_add, pairAmp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  unfold linePt pairFreq
  push_cast
  ring

theorem cpow_pair_dual (t : ℝ) (p : ℕ × ℕ) :
    (p.1 + 1 : ℂ) ^ (linePt t - 1) * (p.2 + 1 : ℂ) ^ (linePt (-t) - 1) =
      (pairAmp p : ℂ) * Complex.exp ((t * (-pairFreq p) : ℝ) * I) := by
  rw [natCast_add_one_cpow, natCast_add_one_cpow, ← Complex.exp_add, pairAmp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  unfold linePt pairFreq
  push_cast
  ring

theorem directTerm_eq (L t : ℝ) (p : ℕ × ℕ) :
    directTerm L t p = (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
      Complex.exp ((t * pairFreq p : ℝ) * I) := by
  unfold directTerm pairProd
  rw [cpow_pair]
  ring

theorem dualTerm_eq (L t : ℝ) (p : ℕ × ℕ) :
    dualTerm L t p = (pairAmp p : ℂ) * critDualWeight t (pairProd p * L) *
      Complex.exp ((t * (-pairFreq p) : ℝ) * I) := by
  unfold dualTerm pairProd critDualWeight
  rw [zetaChi_mul_zetaChi_line, one_mul, cpow_pair_dual]
  ring

/-! ## Envelopes of the terms -/

theorem norm_directTerm_le (L t : ℝ) (p : ℕ × ℕ) :
    ‖directTerm L t p‖ ≤ pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖ := by
  rw [directTerm_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pairAmp_pos p), Complex.norm_exp]
  simp

theorem norm_dualTerm_le (L t : ℝ) (p : ℕ × ℕ) :
    ‖dualTerm L t p‖ ≤ pairAmp p * ‖critDualWeight t (pairProd p * L)‖ := by
  rw [dualTerm_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pairAmp_pos p), Complex.norm_exp]
  simp

/-- `Σ_{m,n} (mn)^{−s}` converges for `s > 1`. -/
theorem summable_pairProd_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun p : ℕ × ℕ => pairProd p ^ (-s)) := by
  have h1 : Summable (fun a : ℕ => ((a : ℝ) + 1) ^ (-s)) := by
    have := (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).comp_injective
      (add_left_injective 1)
    simpa [Function.comp_def] using this
  have h := h1.mul_of_nonneg h1 (fun _ => by positivity) (fun _ => by positivity)
  refine h.congr fun p => ?_
  unfold pairProd
  rw [Real.mul_rpow (by positivity) (by positivity)]

theorem pairAmp_mul_rpow (p : ℕ × ℕ) (s : ℝ) :
    pairAmp p * pairProd p ^ (-s) = pairProd p ^ (-(s + 1 / 2)) := by
  rw [pairAmp_eq, Real.sqrt_eq_rpow, ← Real.rpow_neg (pairProd_pos p).le,
    ← Real.rpow_add (pairProd_pos p)]
  congr 1
  ring

/-- The direct envelope is summable: `‖V(y)‖ ≤ K/y`. -/
theorem summable_direct_envelope {L : ℝ} (hL : 0 < L) :
    Summable (fun p : ℕ × ℕ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) := by
  obtain ⟨K, hK, hV⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) one_pos
  have hs := (summable_pairProd_rpow (s := 3 / 2) (by norm_num)).mul_left (K * L)
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (pairAmp_pos p).le (norm_nonneg _))
    (fun p => ?_) hs
  have hb := hV (div_pos (pairProd_pos p) hL)
  rw [Real.rpow_neg_one, inv_div] at hb
  calc pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖ ≤ pairAmp p * (K * (L / pairProd p)) :=
        mul_le_mul_of_nonneg_left hb (pairAmp_pos p).le
    _ = K * L * (pairAmp p * pairProd p ^ (-(1 : ℝ))) := by
        rw [Real.rpow_neg_one]
        ring
    _ = K * L * pairProd p ^ (-(3 / 2 : ℝ)) := by
        rw [pairAmp_mul_rpow]
        norm_num

/-! ## The windowed twisted moment -/

/-- The window transform `ω̂(η) = ∫ ω(t) e^{−iηt} dt`. -/
def windowHat (L η : ℝ) : ℂ := ∫ t, notchWindow L t * Complex.exp (-(η * t) * I)

/-- The windowed dual oscillation `J(Y, η) = ∫ ω(t) W_t(Y) e^{−iηt} dt`. -/
def dualOsc (L Y η : ℝ) : ℂ := ∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(η * t) * I)

/-- The windowed twisted moment of `|ζ(½+it)|²`. -/
def twistedMoment (L ξ : ℝ) : ℂ := ∫ t, notchWindow L t * zetaSq t * Complex.exp (-(ξ * t) * I)

theorem integrable_notchWindow_mul_continuous {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : Continuous f) : Integrable (fun t => notchWindow L t * f t) := by
  refine ((continuous_notchWindow L).mul hf).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (L / 2) (5 * L / 2))
    isCompact_Icc ?_
  intro t ht
  by_contra hnot
  exact ht (by show notchWindow L t * f t = 0; rw [notchWindow_eq_zero hL hnot, zero_mul])

theorem integrable_dualOsc_integrand {L Y η : ℝ} (hL : 2 ≤ L) (hY : 0 < Y) :
    Integrable (fun t => notchWindow L t * critDualWeight t Y * Complex.exp (-(η * t) * I)) := by
  have hL0 : 0 < L := by linarith
  set F : ℝ → ℝ → ℂ := fun t v => critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
    smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I) with hFdef
  have hint := integrable_notch_mellin (ξ := η) hL0 (F := F) (continuous_dualMellin_uncurry hY)
    (integrable_one_add_abs_pow_mul_exp_neg_sq 2)
    (fun t ht v => norm_dualMellin_le hL hY ht)
  have h := (hint.integral_prod_left).smul (1 / (2 * Real.pi))
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.uncurry_apply_pair, Pi.smul_apply, hFdef]
  rw [critDualWeight_eq, integral_mul_const, integral_const_mul, Complex.real_smul,
    Complex.real_smul]
  ring

/-- The dual envelope on the window. -/
theorem exists_norm_dualTerm_window_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L t : ℝ}, 2 ≤ L → t ∈ Icc (L / 2) (5 * L / 2) → ∀ p : ℕ × ℕ,
      ‖dualTerm L t p‖ ≤ C * L * pairProd p ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hW⟩ := exists_norm_critDualWeight_le
  refine ⟨9 * C, by positivity, fun {L t} hL ht p => ?_⟩
  have hL0 : 0 < L := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  refine (norm_dualTerm_le L t p).trans ?_
  have hY : 0 < pairProd p * L := mul_pos (pairProd_pos p) hL0
  have hb := hW t hY
  have habs : (1 + |t|) ^ 2 ≤ 9 * L ^ 2 := by
    rw [abs_of_nonneg ht0]
    nlinarith [ht.2]
  calc pairAmp p * ‖critDualWeight t (pairProd p * L)‖
      ≤ pairAmp p * (C * (9 * L ^ 2) / (pairProd p * L)) := by
        apply mul_le_mul_of_nonneg_left _ (pairAmp_pos p).le
        refine hb.trans ?_
        gcongr
    _ = 9 * C * L * (pairAmp p * pairProd p ^ (-(1 : ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = 9 * C * L * pairProd p ^ (-(3 / 2 : ℝ)) := by
        rw [pairAmp_mul_rpow]
        norm_num

theorem norm_window_mul_le_indicator {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ} {M : ℝ}
    (hf : ∀ t ∈ Icc (L / 2) (5 * L / 2), ‖f t‖ ≤ M) (ξ t : ℝ) :
    ‖notchWindow L t * f t * Complex.exp (-(ξ * t) * I)‖ ≤
      (Icc (L / 2) (5 * L / 2)).indicator (fun _ => M) t := by
  by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
  · rw [indicator_of_mem ht, norm_mul, norm_mul, Complex.norm_exp]
    have hre : (-(↑ξ * ↑t) * I).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
    exact (mul_le_mul (norm_notchWindow_le_one L t) (hf t ht) (norm_nonneg _)
      zero_le_one).trans (le_of_eq (one_mul M))
  · rw [indicator_of_notMem ht, notchWindow_eq_zero hL ht]
    simp

theorem integral_indicator_window {L M : ℝ} (hL : 0 < L) :
    ∫ t, (Icc (L / 2) (5 * L / 2)).indicator (fun _ => M) t = 2 * L * M := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
  ring

/-- The critical dual weight is continuous in the height. -/
theorem continuous_critDualWeight {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun t : ℝ => critDualWeight t Y) := by
  have hFc := continuous_dualMellin_uncurry hY
  rw [continuous_iff_continuousAt]
  intro t₀
  have hcont : ContinuousAt (fun t : ℝ => ∫ v : ℝ, critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)) t₀ := by
    refine continuousAt_of_dominated (bound := fun v : ℝ => ((2 + |t₀|) ^ 2 * (Y⁻¹ * Real.exp 1)) *
      ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun t =>
        (hFc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds t₀ one_pos] with t ht
      refine Filter.Eventually.of_forall fun v => (norm_critDualIntegrand_one_le hY t v).trans ?_
      have htt : |t| ≤ 1 + |t₀| := by
        have := Metric.mem_ball.mp ht
        rw [Real.dist_eq] at this
        have h2 := abs_sub_abs_le_abs_sub t t₀
        linarith
      have h1 : (1 + |t|) ^ 2 ≤ (2 + |t₀|) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity))
        (by positivity)
    · exact (integrable_one_add_abs_sq_mul_exp_neg_sq).const_mul _
    · exact Filter.Eventually.of_forall fun v =>
        (hFc.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt
  have h := hcont.const_smul (1 / (2 * Real.pi))
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (critDualWeight_eq t Y).symm

/-- **The windowed twisted moment through the product AFE.** -/
theorem twistedMoment_eq {L ξ : ℝ} (hL : 16 ≤ L) :
    twistedMoment L ξ =
      (∑' p : ℕ × ℕ, (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
          windowHat L (ξ - pairFreq p)) +
        (∑' p : ℕ × ℕ, (pairAmp p : ℂ) * dualOsc L (pairProd p * L) (ξ + pairFreq p)) -
        ∫ t, notchWindow L t * residueTerm L t * Complex.exp (-(ξ * t) * I) := by
  have hL0 : 0 < L := by linarith
  set e : ℝ → ℂ := fun t => Complex.exp (-(ξ * t) * I) with he
  -- the direct family
  set FD : ℕ × ℕ → ℝ → ℂ := fun p t => notchWindow L t * directTerm L t p * e t with hFD
  have hFD_eq : ∀ p t, FD p t = (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
      (notchWindow L t * Complex.exp (-((ξ - pairFreq p) * t) * I)) := by
    intro p t
    simp only [hFD, he, directTerm_eq]
    have hexp : Complex.exp ((↑(t * pairFreq p) : ℂ) * I) * Complex.exp (-(↑ξ * ↑t) * I) =
        Complex.exp (-((↑ξ - ↑(pairFreq p)) * ↑t) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← hexp]
    ring
  have hFD_int : ∀ p, Integrable (FD p) := by
    intro p
    have h := (integrable_notchWindow_mul_continuous hL0 (f := fun t =>
      Complex.exp (-((ξ - pairFreq p) * t) * I)) (by fun_prop)).const_mul
      ((pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L))
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hFD_eq]
  have hFD_norm : ∀ p, ∫ t, ‖FD p t‖ ≤ 2 * L * (pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) := by
    intro p
    have hpt : ∀ t, ‖FD p t‖ ≤ (Icc (L / 2) (5 * L / 2)).indicator
        (fun _ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) t :=
      fun t => norm_window_mul_le_indicator hL0 (f := fun t => directTerm L t p)
        (fun t _ => norm_directTerm_le L t p) ξ t
    calc ∫ t, ‖FD p t‖ ≤ ∫ t, (Icc (L / 2) (5 * L / 2)).indicator
          (fun _ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) t :=
          integral_mono (hFD_int p).norm
            ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) hpt
      _ = _ := integral_indicator_window hL0
  have hFD_sum : Summable (fun p => ∫ t, ‖FD p t‖) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _) hFD_norm
      ((summable_direct_envelope hL0).mul_left (2 * L))
  -- the dual family
  obtain ⟨Cd, hCd, hdual⟩ := exists_norm_dualTerm_window_le
  set FS : ℕ × ℕ → ℝ → ℂ := fun p t => notchWindow L t * dualTerm L t p * e t with hFS
  have hFS_eq : ∀ p t, FS p t = (pairAmp p : ℂ) *
      (notchWindow L t * critDualWeight t (pairProd p * L) *
        Complex.exp (-((ξ + pairFreq p) * t) * I)) := by
    intro p t
    simp only [hFS, he, dualTerm_eq]
    have hexp : Complex.exp ((↑(t * -pairFreq p) : ℂ) * I) * Complex.exp (-(↑ξ * ↑t) * I) =
        Complex.exp (-((↑ξ + ↑(pairFreq p)) * ↑t) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← hexp]
    ring
  have hFS_int : ∀ p, Integrable (FS p) := by
    intro p
    have h := (integrable_dualOsc_integrand (L := L) (η := ξ + pairFreq p) (by linarith)
      (mul_pos (pairProd_pos p) hL0)).const_mul (pairAmp p : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    rw [hFS_eq]
    push_cast
    rfl
  have hFS_norm : ∀ p, ∫ t, ‖FS p t‖ ≤ 2 * L * (Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) := by
    intro p
    have hpt : ∀ t, ‖FS p t‖ ≤ (Icc (L / 2) (5 * L / 2)).indicator
        (fun _ => Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) t :=
      fun t => norm_window_mul_le_indicator hL0 (f := fun t => dualTerm L t p)
        (fun t ht => hdual (by linarith) ht p) ξ t
    calc ∫ t, ‖FS p t‖ ≤ ∫ t, (Icc (L / 2) (5 * L / 2)).indicator
          (fun _ => Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) t :=
          integral_mono (hFS_int p).norm
            ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) hpt
      _ = _ := integral_indicator_window hL0
  have hFS_sum : Summable (fun p => ∫ t, ‖FS p t‖) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _) hFS_norm
      (((summable_pairProd_rpow (s := 3 / 2) (by norm_num)).mul_left (Cd * L)).mul_left (2 * L))
  -- integrability of the three pieces
  have hFD_meas : ∀ p, Measurable (FD p) := by
    intro p
    have hc : Continuous (FD p) := by
      have h : Continuous (fun t => (pairAmp p : ℂ) * smoothAFECutoff (pairProd p / L) *
          (notchWindow L t * Complex.exp (-((ξ - pairFreq p) * t) * I))) :=
        continuous_const.mul ((continuous_notchWindow L).mul (by fun_prop))
      exact h.congr fun t => (hFD_eq p t).symm
    exact hc.measurable
  have hFS_meas : ∀ p, Measurable (FS p) := by
    intro p
    have hc : Continuous (FS p) := by
      have h : Continuous (fun t => (pairAmp p : ℂ) *
          (notchWindow L t * critDualWeight t (pairProd p * L) *
            Complex.exp (-((ξ + pairFreq p) * t) * I))) :=
        continuous_const.mul (((continuous_notchWindow L).mul
          (continuous_critDualWeight (mul_pos (pairProd_pos p) hL0))).mul (by fun_prop))
      exact h.congr fun t => (hFS_eq p t).symm
    exact hc.measurable
  have hD_env : Summable (fun p : ℕ × ℕ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) :=
    summable_direct_envelope hL0
  have hS_env : Summable (fun p : ℕ × ℕ => Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) :=
    (summable_pairProd_rpow (s := 3 / 2) (by norm_num)).mul_left (Cd * L)
  have hFD_pt : ∀ p t, ‖FD p t‖ ≤ (Icc (L / 2) (5 * L / 2)).indicator
      (fun _ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) t :=
    fun p t => norm_window_mul_le_indicator hL0 (f := fun t => directTerm L t p)
      (fun t _ => norm_directTerm_le L t p) ξ t
  have hFS_pt : ∀ p t, ‖FS p t‖ ≤ (Icc (L / 2) (5 * L / 2)).indicator
      (fun _ => Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) t :=
    fun p t => norm_window_mul_le_indicator hL0 (f := fun t => dualTerm L t p)
      (fun t ht => hdual (by linarith) ht p) ξ t
  have hind_sum : ∀ {c : ℕ × ℕ → ℝ}, Summable c → ∀ t,
      Summable (fun p => (Icc (L / 2) (5 * L / 2)).indicator (fun _ => c p) t) := by
    intro c hc t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · simpa [indicator_of_mem ht] using hc
    · simp [indicator_of_notMem ht]
  have hind_tsum : ∀ {c : ℕ × ℕ → ℝ}, ∀ t,
      ∑' p, (Icc (L / 2) (5 * L / 2)).indicator (fun _ => c p) t =
        (Icc (L / 2) (5 * L / 2)).indicator (fun _ => ∑' p, c p) t := by
    intro c t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  have hind_int : ∀ c : ℝ, Integrable ((Icc (L / 2) (5 * L / 2)).indicator (fun _ => c)) :=
    fun c => (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hD_int : Integrable (fun t => ∑' p, FD p t) := by
    refine Integrable.mono' (hind_int (∑' p, pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖))
      (Measurable.tsum hFD_meas).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have hsn : Summable (fun p => ‖FD p t‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hFD_pt p t) (hind_sum hD_env t)
    calc ‖∑' p, FD p t‖ ≤ ∑' p, ‖FD p t‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' p, (Icc (L / 2) (5 * L / 2)).indicator
            (fun _ => pairAmp p * ‖smoothAFECutoff (pairProd p / L)‖) t :=
          hsn.tsum_le_tsum (fun p => hFD_pt p t) (hind_sum hD_env t)
      _ = _ := hind_tsum t
  have hS_int : Integrable (fun t => ∑' p, FS p t) := by
    refine Integrable.mono' (hind_int (∑' p, Cd * L * pairProd p ^ (-(3 / 2 : ℝ))))
      (Measurable.tsum hFS_meas).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    have hsn : Summable (fun p => ‖FS p t‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hFS_pt p t) (hind_sum hS_env t)
    calc ‖∑' p, FS p t‖ ≤ ∑' p, ‖FS p t‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' p, (Icc (L / 2) (5 * L / 2)).indicator
            (fun _ => Cd * L * pairProd p ^ (-(3 / 2 : ℝ))) t :=
          hsn.tsum_le_tsum (fun p => hFS_pt p t) (hind_sum hS_env t)
      _ = _ := hind_tsum t
  have hZ_int : Integrable (fun t => notchWindow L t * zetaSq t * e t) := by
    have hcont : Continuous (fun t => zetaSq t * e t) := by
      have hz : Continuous zetaSq := by
        unfold zetaSq
        have h1 : Continuous (fun t : ℝ => riemannZeta (linePt t)) := by
          rw [continuous_iff_continuousAt]
          intro t
          have hne : linePt t ≠ 1 := by
            intro h; have := congrArg Complex.re h; simp [linePt_re] at this
          exact (differentiableAt_riemannZeta hne).continuousAt.comp continuous_linePt.continuousAt
        have h2 : Continuous (fun t : ℝ => riemannZeta (linePt (-t))) :=
          h1.comp continuous_neg
        exact h1.mul h2
      exact hz.mul (by fun_prop)
    have h := integrable_notchWindow_mul_continuous hL0 hcont
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  -- the pointwise decomposition
  have hpt : ∀ t, notchWindow L t * zetaSq t * e t =
      (∑' p, FD p t) + (∑' p, FS p t) - notchWindow L t * residueTerm L t * e t := by
    intro t
    by_cases ht : t ∈ Icc (L / 2) (5 * L / 2)
    · have ht0 : t ≠ 0 := by
        intro h; rw [h] at ht; linarith [ht.1]
      simp only [hFD, hFS]
      rw [tsum_mul_right, tsum_mul_left, tsum_mul_right, tsum_mul_left,
        zetaSq_eq_afe hL0 ht0]
      ring
    · simp only [hFD, hFS, notchWindow_eq_zero hL0 ht, zero_mul, tsum_zero, sub_zero, add_zero]
  have hR_int : Integrable (fun t => notchWindow L t * residueTerm L t * e t) := by
    have h := (hD_int.add hS_int).sub hZ_int
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hpt t]
    ring
  unfold twistedMoment
  simp_rw [show ∀ t, notchWindow L t * zetaSq t * Complex.exp (-(ξ * t) * I) =
    notchWindow L t * zetaSq t * e t from fun t => rfl, hpt]
  have hsum_int : Integrable (fun t => ∑' p, FD p t + ∑' p, FS p t) := hD_int.add hS_int
  rw [integral_sub hsum_int hR_int, integral_add hD_int hS_int,
    ← integral_tsum_of_summable_integral_norm hFD_int hFD_sum,
    ← integral_tsum_of_summable_integral_norm hFS_int hFS_sum]
  congr 2
  · congr 1
    funext p
    simp_rw [hFD_eq]
    rw [integral_const_mul]
    unfold windowHat
    push_cast
    rfl
  · congr 1
    funext p
    simp_rw [hFS_eq]
    rw [integral_const_mul]
    unfold dualOsc
    push_cast
    rfl

end RHTower.ZetaNotch
