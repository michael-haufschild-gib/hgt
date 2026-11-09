import GaloisForLFunctions.ExceptionalLayerTheory.BoundaryZeroFreeContours

/-!
# Independent arithmetic savings for boundary damping

A full zero-free rectangle of cubic height retains the complete filter.
Its vertical shift gains the Vinogradov–Korobov width, while reciprocal
angular margin makes the horizontal edges and Euler tails quadratically
small. No exceptional-layer assumption enters the arithmetic bound.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Boundary-angle damping retains the actual zero-free saving, uniformly
in every filter spacing, including the critical contraction scale. -/
theorem exists_boundaryPrimeDampingFilter_vinogradovKorobov_bound
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      ‖rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h)
        σ β a h (boundaryDampingAngle t) t‖ ≤
      C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
        Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (t ^ 3 + 1) / 4) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let r : ℝ := 9 / 8
  let l := (1 - σ) / 2
  let u := r - σ
  have hl : 0 < l := by dsimp only [l]; linarith only [hσ]
  have hr : 1 < r := by norm_num [r]
  have hu : 0 < u := sub_pos.mpr (hσ.trans hr)
  obtain ⟨A, N, hA, hkernel⟩ := exists_boundaryFilteredWeight_strip_envelope F ρ σ β l u hl
  obtain ⟨D, hD, hrectangle⟩ := eventually_zeta_vk_full_rectangle
  let E := (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r) + 1
  have hE : 0 < E := by
    have hs : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r :=
      tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    dsimp only [E]
    linarith only [hs]
  let J := ∫ v : ℝ, Real.exp (-(|v| / 8))
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  let k := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp only [k]; positivity
  refine ⟨k * A * (64 * D + E * J + 1), N + 15, by positivity, ?_⟩
  have hHlim : Tendsto (fun t : ℝ => t ^ 3) atTop atTop := tendsto_pow_atTop (by decide)
  have hWlim : Tendsto (fun t : ℝ => vkHadamardWidth (t ^ 3 + 1)) atTop (𝓝 0) :=
    tendsto_vkHadamardWidth_zero.comp (tendsto_atTop_add_const_right atTop 1 hHlim)
  have hsmall : ∀ᶠ t : ℝ in atTop, vkHadamardWidth (t ^ 3 + 1) < min 1 (1 - σ) :=
    hWlim.eventually (gt_mem_nhds (lt_min zero_lt_one (sub_pos.mpr hσ)))
  filter_upwards [hHlim.eventually hrectangle, hsmall,
    hHlim.eventually (eventually_ge_atTop (Real.exp (Real.exp 1))),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * a)] with t htR hsmall htE ht ht4a
  intro h hh hh1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  let H := t ^ 3
  let w := vkHadamardWidth (H + 1)
  let c := 1 - w / 2
  let δ := 1 / (4 * t)
  let y := Real.exp (-a * t)
  let φ := boundaryDampingAngle t
  let G : ℂ → ℂ := fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
    (-logDeriv riemannZeta z)
  let M := A * h ^ d * t ^ N
  let L := Real.exp (a * t * (c - σ) / 2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hL : 0 < L := Real.exp_pos _
  have hH : 1 ≤ H := one_le_pow₀ ht
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hw : 0 < w := vkHadamardWidth_pos (by dsimp only [H]; linarith only [htE])
  have hw1 : w ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hws : w < 1 - σ := hsmall.trans_le (min_le_right _ _)
  have hc : 1 / 2 ≤ c := by dsimp only [c]; linarith only [hw1]
  have hc1 : c < 1 := by dsimp only [c]; linarith only [hw]
  have hcl : l ≤ c - σ := by dsimp only [c, l]; linarith only [hws]
  have hσc : σ < c := by linarith only [hl, hcl]
  have hcr : c ≤ r := (hc1.trans hr).le
  have hrc : r - c ≤ 1 := by dsimp only [r]; linarith only [hc]
  have hφ : |φ| < Real.pi / 2 := by
    rw [show φ = boundaryDampingAngle t from rfl, abs_boundaryDampingAngle ht]
    linarith only [one_div_pos.mpr ht0]
  have hweight (x v : ℝ) (hx : c ≤ x) (hxr : x ≤ r) :
      ‖rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t ((x : ℂ) + v * I)‖ ≤
        M * Real.exp (a * t * (x - σ) / 2) * Real.exp (-(δ * |v|)) := by
    have hb := hkernel y h t (x - σ) v (Real.exp_pos _) hh hh1 ht
      (by linarith only [hcl, hx]) (by dsimp only [u]; linarith only [hxr])
    have he : σ + (x - σ) = x := by ring
    rw [he] at hb
    have hyexp : y ^ (-((x - σ) / 2)) = Real.exp (a * t * (x - σ) / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [hyexp] at hb
    convert hb using 1 <;> dsimp only [δ] <;> congr 1 <;> ring
  have hnz (x v : ℝ) (hx : c ≤ x) (hxr : x ≤ r) (hv : |v| ≤ H) :
      zetaResidueUnit ((x : ℂ) + v * I) ≠ 0 :=
    (htR ((x : ℂ) + v * I) (by simpa using hv)
      (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hx)
      (by simpa only [r, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hxr)).1
  have hlog (x v : ℝ) (hx : c ≤ x) (hxr : x ≤ r) (hv : |v| ≤ H)
      (hdist : w / 2 ≤ ‖((x : ℂ) + v * I) - 1‖) :
      ‖logDeriv riemannZeta ((x : ℂ) + v * I)‖ ≤ D * (1 + H) ^ 4 :=
    (htR ((x : ℂ) + v * I) (by simpa using hv)
      (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hx)
      (by simpa only [r, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hxr)).2 hdist
  have hEuler (v : ℝ) : ‖logDeriv riemannZeta ((r : ℂ) + v * I)‖ ≤ E := by
    have hn := norm_LSeries_vonMangoldt_le (s := (r : ℂ) + v * I) (by simpa using hr)
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hr),
      neg_div, ← logDeriv_apply, norm_neg] at hn
    have hn' : ‖logDeriv riemannZeta ((r : ℂ) + v * I)‖ ≤
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ r := by simpa using hn
    exact hn'.trans (by dsimp only [E]; linarith)
  have hline (v : ℝ) : ‖G ((r : ℂ) + v * I)‖ ≤
      M * Real.exp (a * t * (r - σ) / 2) * E * Real.exp (-(δ * |v|)) := by
    dsimp only [G]
    rw [norm_mul, norm_neg]
    exact (mul_le_mul (hweight r v hcr le_rfl) (hEuler v)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hcont : Continuous (fun v : ℝ => G ((r : ℂ) + v * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hs1 : (r : ℂ) + v * I ≠ 1 := by
      intro he
      have hRe := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.one_re] at hRe
      linarith only [hRe, hr]
    have hz := analyticOn_riemannZeta ((r : ℂ) + v * I) hs1
    have hwc := (analyticOnNhd_rotatedDivisorFilteredMellinWeight F ρ σ β h φ t
      (Real.exp_pos (-a * t))) ((r : ℂ) + v * I) (by simpa using hσ.trans hr)
    have hd : ContinuousAt G ((r : ℂ) + v * I) :=
      hwc.continuousAt.mul (hz.deriv.continuousAt.div hz.continuousAt
        (riemannZeta_ne_zero_of_one_lt_re (by simpa using hr))).neg
    exact hd.comp (f := fun v : ℝ => (r : ℂ) + v * I) (by fun_prop)
  have hGi : Integrable (fun v : ℝ => G ((r : ℂ) + v * I)) :=
    ((integrable_exp_neg_mul_abs' hδ).const_mul
      (M * Real.exp (a * t * (r - σ) / 2) * E)).mono'
        hcont.aestronglyMeasurable (Eventually.of_forall hline)
  have hpoly : (1 + H) ^ 4 ≤ 16 * t ^ 12 := by
    calc
      _ ≤ (2 * H) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only [hH]) 4
      _ = _ := by dsimp only [H]; ring
  have hp12 : t ^ 12 ≤ t ^ 15 := pow_le_pow_right₀ ht (by norm_num)
  have hpoly15 : (1 + H) ^ 4 ≤ 16 * t ^ 15 :=
    hpoly.trans (mul_le_mul_of_nonneg_left hp12 (by norm_num))
  have hp1 : t ≤ t ^ 15 := by simpa using pow_le_pow_right₀ ht (by norm_num : (1 : ℕ) ≤ 15)
  have hedgeexp : Real.exp (a * t * (r - σ) / 2) * Real.exp (-(δ * H / 2)) ≤ L := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscale : δ * H / 2 = t ^ 2 / 8 := by
      dsimp only [δ, H]
      field_simp [ht0.ne'] <;> ring
    rw [hscale]
    have hgap := mul_le_mul_of_nonneg_left hrc (mul_nonneg ha.le ht0.le)
    have hlarge := mul_le_mul_of_nonneg_right ht4a ht0.le
    dsimp only [L]
    nlinarith only [hgap, hlarge]
  have hleft : ‖∫ v in (-H)..H, G ((c : ℂ) + v * I)‖ ≤
      32 * D * M * t ^ 15 * L := by
    have hpt : ∀ v ∈ uIoc (-H) H, ‖G ((c : ℂ) + v * I)‖ ≤ M * L * (D * (1 + H) ^ 4) := by
      intro v hv
      rw [uIoc_of_le (by linarith only [hH0])] at hv
      have hvH : |v| ≤ H := abs_le.mpr ⟨hv.1.le, hv.2⟩
      have hd := Complex.abs_re_le_norm (((c : ℂ) + v * I) - 1)
      have he : (((c : ℂ) + v * I) - 1).re = -(w / 2) := by simp [c]; ring
      rw [he, abs_neg, abs_of_pos (by positivity : 0 < w / 2)] at hd
      have hld := hlog c v le_rfl hcr hvH hd
      dsimp only [G]
      rw [norm_mul, norm_neg]
      calc
        _ ≤ (M * L * Real.exp (-(δ * |v|))) * (D * (1 + H) ^ 4) :=
          mul_le_mul (hweight c v le_rfl hcr) hld (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hδ.le (abs_nonneg v)))
          nlinarith only [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ M * L * (D * (1 + H) ^ 4))]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [show H - -H = 2 * H by ring, abs_of_pos (by positivity : 0 < 2 * H)] at hi
    refine hi.trans ?_
    calc
      _ ≤ M * L * (D * (16 * t ^ 12)) * (2 * H) := by gcongr
      _ = _ := by dsimp only [H]; ring
  have hedge (v : ℝ) (hv : |v| = H) :
      ‖∫ x in c..r, G ((x : ℂ) + v * I)‖ ≤ 16 * D * M * t ^ 15 * L := by
    have hpt : ∀ x ∈ uIoc c r, ‖G ((x : ℂ) + v * I)‖ ≤
        M * (D * (1 + H) ^ 4) * L := by
      intro x hx
      rw [uIoc_of_le hcr] at hx
      have hd := Complex.abs_im_le_norm (((x : ℂ) + v * I) - 1)
      have him : (((x : ℂ) + v * I) - 1).im = v := by simp
      rw [him, hv] at hd
      have hdist : w / 2 ≤ ‖((x : ℂ) + v * I) - 1‖ := by linarith only [hw1, hH, hd]
      have hld := hlog x v hx.1.le hx.2 hv.le hdist
      have he : Real.exp (a * t * (x - σ) / 2) * Real.exp (-(δ * |v|)) ≤ L := by
        rw [hv]
        refine (mul_le_mul (Real.exp_le_exp.mpr ?_)
          (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.exp_pos _).le).trans hedgeexp
        · have hm := mul_le_mul_of_nonneg_left hx.2 (mul_nonneg ha.le ht0.le)
          nlinarith only [hm]
        · nlinarith only [mul_nonneg hδ.le hH0.le]
      dsimp only [G]
      rw [norm_mul, norm_neg]
      calc
        _ ≤ (M * Real.exp (a * t * (x - σ) / 2) * Real.exp (-(δ * |v|))) * (D * (1 + H) ^ 4) :=
          mul_le_mul (hweight x v hx.1.le hx.2) hld (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          nlinarith only [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ M * (D * (1 + H) ^ 4))]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_nonneg (sub_nonneg.mpr hcr)] at hi
    refine hi.trans ?_
    calc
      _ ≤ M * (D * (16 * t ^ 15)) * L * 1 := by gcongr
      _ = _ := by ring
  have hJscale : (∫ v : ℝ, Real.exp (-(δ / 2 * |v|))) = t * J := by
    have he : (fun v : ℝ => Real.exp (-(δ / 2 * |v|))) =
        (fun v : ℝ => Real.exp (-(|t⁻¹ * v| / 8))) := by
      funext v
      rw [abs_mul, abs_inv, abs_of_pos ht0]
      congr 1
      dsimp only [δ]
      ring
    rw [he, Measure.integral_comp_mul_left (fun v : ℝ => Real.exp (-(|v| / 8))),
      inv_inv, abs_of_pos ht0, smul_eq_mul]
  have htail : ‖(∫ v : ℝ, G ((r : ℂ) + v * I)) - ∫ v in (-H)..H, G ((r : ℂ) + v * I)‖ ≤
      E * J * M * t ^ 15 * L := by
    have hb := norm_integral_sub_intervalIntegral_le_scaled hGi hH0.le
      (by positivity : 0 ≤ M * Real.exp (a * t * (r - σ) / 2) * E) hδ hline
    rw [hJscale] at hb
    refine hb.trans ?_
    calc
      _ = E * J * M * t * (Real.exp (a * t * (r - σ) / 2) * Real.exp (-(δ * H / 2))) := by ring
      _ ≤ E * J * M * t ^ 15 * L := by gcongr
  have hrect := boundaryFilteredWeight_zero_free_rectangle F ρ σ β h φ t
    (Real.exp_pos (-a * t)) hσc hc1 hr hH0 hnz
  have hmid : ‖∫ v in (-H)..H, G ((r : ℂ) + v * I)‖ ≤
      ‖∫ v in (-H)..H, G ((c : ℂ) + v * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + (-H : ℝ) * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + H * I)‖ :=
    norm_vertical_integral_le_of_rectIntegral_zero hrect
  have hfull : ‖∫ v : ℝ, G ((r : ℂ) + v * I)‖ ≤
      (64 * D + E * J) * M * t ^ 15 * L := by
    have htri := norm_add_le (∫ v in (-H)..H, G ((r : ℂ) + v * I))
      ((∫ v : ℝ, G ((r : ℂ) + v * I)) - ∫ v in (-H)..H, G ((r : ℂ) + v * I))
    rw [add_sub_cancel] at htri
    have hb := hedge (-H) (by rw [abs_neg, abs_of_pos hH0])
    have ht' := hedge H (abs_of_pos hH0)
    nlinarith only [htri, hmid, hleft, hb, ht', htail]
  rw [rotatedPrimeDampingFilter_eq_absolute_euler_integral F ρ σ β a h φ t r hφ hr (hσ.trans hr),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    _ ≤ k * ((64 * D + E * J) * M * t ^ 15 * L) := mul_le_mul_of_nonneg_left hfull hk.le
    _ ≤ k * ((64 * D + E * J + 1) * M * t ^ 15 * L) := by gcongr; linarith
    _ = _ := by
      have he : a * t * (c - σ) / 2 =
          a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (t ^ 3 + 1) / 4 := by
        dsimp only [c, w, H]
        ring
      dsimp only [M, L]
      rw [he, pow_add]
      ring

#print axioms exists_boundaryPrimeDampingFilter_vinogradovKorobov_bound

/-- The zero-free saving at cubic contour height dominates every polynomial
in the observation height. -/
theorem tendsto_polynomial_mul_exp_neg_boundary_vk_width (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ n *
      Real.exp (-(b * t * vkHadamardWidth (t ^ 3 + 1)))) atTop (𝓝 0) := by
  have hloglim := Real.tendsto_log_atTop
  have hsmall : ∀ᶠ t : ℝ in atTop, Real.log t ^ 4 * Real.exp (-Real.log t) <
      b / (64 * 10 ^ 8 * ((n : ℝ) + 1)) :=
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp hloglim).eventually
      (gt_mem_nhds (by positivity))
  have hheight : Tendsto (fun t : ℝ => t ^ 3 + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_pow_atTop (by decide))
  refine squeeze_zero' ?_ ?_ (Real.tendsto_exp_neg_atTop_nhds_zero.comp hloglim)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ),
      hheight.eventually (eventually_ge_atTop (Real.exp (Real.exp 1)))] with t ht ht2 htE
    have ht0 : 0 < t := by linarith only [ht2]
    have ht1 : 1 ≤ t := by linarith only [ht2]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith only [ht2])
    have hw := vkHadamardWidth_pos htE
    have hL0 : 0 ≤ Real.log (t ^ 3 + 1) := Real.log_nonneg (by positivity)
    have hL : Real.log (t ^ 3 + 1) ≤ 4 * Real.log t := by
      have hc : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht1
      have hm := mul_le_mul_of_nonneg_left ht2 (by positivity : 0 ≤ t ^ 3)
      have hpow : t ^ 3 + 1 ≤ t ^ 4 := by nlinarith only [hc, hm]
      have hh := Real.log_le_log (by positivity : 0 < t ^ 3 + 1) hpow
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hrecip : (vkHadamardWidth (t ^ 3 + 1))⁻¹ ≤
        64 * 10 ^ 8 * Real.log t ^ 3 := by
      calc
        _ ≤ 10 ^ 8 * Real.log (t ^ 3 + 1) ^ 3 := inv_vkHadamardWidth_le_log_cube htE
        _ ≤ 10 ^ 8 * (4 * Real.log t) ^ 3 := by gcongr
        _ = _ := by ring
    have hh := ht.le
    rw [Real.exp_neg, Real.exp_log ht0, ← div_eq_mul_inv,
      div_le_div_iff₀ ht0 (by positivity : 0 < 64 * 10 ^ 8 * ((n : ℝ) + 1))] at hh
    have hbudget : 64 * 10 ^ 8 * ((n : ℝ) + 1) * Real.log t ^ 4 ≤ b * t := by
      nlinarith only [hh]
    have hq : ((n : ℝ) + 1) * Real.log t ≤ b * t * vkHadamardWidth (t ^ 3 + 1) := by
      apply (div_le_iff₀ hw).mp
      calc
        _ ≤ (((n : ℝ) + 1) * Real.log t) * (64 * 10 ^ 8 * Real.log t ^ 3) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = 64 * 10 ^ 8 * ((n : ℝ) + 1) * Real.log t ^ 4 := by ring
        _ ≤ b * t := hbudget
    calc
      _ = Real.exp ((n : ℝ) * Real.log t - b * t * vkHadamardWidth (t ^ 3 + 1)) := by
        rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log ht0, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hq])

/-- A width-sized relaxation of critical contraction still forces the
literal rotated prime filter to zero, independently of the zero divisor. -/
theorem tendsto_boundary_prime_filter_zero_of_vk_relaxed_contraction
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a)
    {h : ℝ → ℝ} (hpos : ∀ᶠ t : ℝ in atTop, 0 ≤ h t ∧ h t ≤ 1)
    (hcontract : ∀ᶠ t : ℝ in atTop,
      (h t) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) ≤
        Real.exp (-(a * (1 - σ) * t / 2) + a * t * vkHadamardWidth (t ^ 3 + 1) / 8)) :
    Tendsto (fun t : ℝ => rotatedPrimeDampingFilter
      (divisorDampingFilter F ρ β (h t)) σ β a (h t) (boundaryDampingAngle t) t)
      atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨C, N, hC, hb⟩ := exists_boundaryPrimeDampingFilter_vinogradovKorobov_bound F ρ σ β a hσ ha
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := (tendsto_polynomial_mul_exp_neg_boundary_vk_width N
    (by positivity : 0 < a / 8)).const_mul C
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hb, hpos, hcontract, eventually_ge_atTop (0 : ℝ)] with t ht hh hct ht0
  calc
    _ ≤ C * (h t) ^ d * t ^ N *
        Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (t ^ 3 + 1) / 4) :=
      ht (h t) hh.1 hh.2
    _ ≤ C * Real.exp (-(a * (1 - σ) * t / 2) +
          a * t * vkHadamardWidth (t ^ 3 + 1) / 8) * t ^ N *
        Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (t ^ 3 + 1) / 4) := by gcongr
    _ = C * (t ^ N *
        (Real.exp (-(a * (1 - σ) * t / 2) + a * t * vkHadamardWidth (t ^ 3 + 1) / 8) *
          Real.exp (a * (1 - σ) * t / 2 - a * t * vkHadamardWidth (t ^ 3 + 1) / 4))) := by ring
    _ = C * (t ^ N * Real.exp (-(a / 8 * t * vkHadamardWidth (t ^ 3 + 1)))) := by
      rw [← Real.exp_add]
      congr 3
      ring

/-- The arithmetic decay range includes equality at the absolute threshold. -/
theorem tendsto_boundary_prime_filter_zero_of_critical_contraction
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a κ : ℝ)
    (hσ : σ < 1) (ha : 0 < a) (hκ : 0 < κ)
    (hr : a * (1 - σ) / 2 ≤
      ((1 + (F.filter (fun q => xiZero q ≠ ρ)).card : ℕ) : ℝ) * κ) :
    Tendsto (fun t : ℝ => rotatedPrimeDampingFilter
      (divisorDampingFilter F ρ β (Real.exp (-κ * t)))
        σ β a (Real.exp (-κ * t)) (boundaryDampingAngle t) t) atTop (𝓝 0) := by
  apply tendsto_boundary_prime_filter_zero_of_vk_relaxed_contraction F ρ σ β a hσ ha
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ.le) ht
  · have hheight : Tendsto (fun t : ℝ => t ^ 3 + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 (tendsto_pow_atTop (by decide))
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      hheight.eventually (eventually_ge_atTop (Real.exp (Real.exp 1)))] with t ht htE
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hr ht
    have hw := mul_nonneg (mul_nonneg ha.le ht) (vkHadamardWidth_pos htE).le
    nlinarith only [hm, hw]

/-- Explicit critical spacing enlarged by the boundary-angle zero-free saving. -/
def boundaryVkRelaxedDampingStep (d : ℕ) (σ a t : ℝ) : ℝ :=
  Real.exp ((-(a * (1 - σ) / 2) + a * vkHadamardWidth (t ^ 3 + 1) / 8) * t / d)

/-- An explicit spacing slower than critical exponential contraction still
makes the complete boundary-damped prime filter vanish. -/
theorem tendsto_boundary_prime_filter_zero_of_vk_schedule
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a : ℝ) (hσ : σ < 1) (ha : 0 < a) :
    let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
    Tendsto (fun t : ℝ => rotatedPrimeDampingFilter
      (divisorDampingFilter F ρ β (boundaryVkRelaxedDampingStep d σ a t))
        σ β a (boundaryVkRelaxedDampingStep d σ a t) (boundaryDampingAngle t) t) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  have hd : 0 < (d : ℝ) := by dsimp only [d]; positivity
  apply tendsto_boundary_prime_filter_zero_of_vk_relaxed_contraction F ρ σ β a hσ ha
  · have hwidthlim : Tendsto (fun t : ℝ => vkHadamardWidth (t ^ 3 + 1)) atTop (𝓝 0) :=
      tendsto_vkHadamardWidth_zero.comp
        (tendsto_atTop_add_const_right atTop 1 (tendsto_pow_atTop (by decide)))
    filter_upwards [hwidthlim.eventually
      (gt_mem_nhds (show 0 < 2 * (1 - σ) by linarith only [hσ])),
      eventually_ge_atTop (0 : ℝ)] with t ht ht0
    refine ⟨(Real.exp_pos _).le, ?_⟩
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hd.le
    apply mul_nonpos_of_nonpos_of_nonneg _ ht0
    nlinarith only [ht, ha, mul_pos ha (sub_pos.mpr hσ)]
  · refine Eventually.of_forall fun t => ?_
    change (boundaryVkRelaxedDampingStep d σ a t) ^ d ≤ _
    rw [boundaryVkRelaxedDampingStep, ← Real.exp_nat_mul]
    apply le_of_eq
    congr 1
    field_simp [hd.ne']

#print axioms tendsto_polynomial_mul_exp_neg_boundary_vk_width
#print axioms tendsto_boundary_prime_filter_zero_of_vk_relaxed_contraction
#print axioms tendsto_boundary_prime_filter_zero_of_critical_contraction
#print axioms tendsto_boundary_prime_filter_zero_of_vk_schedule

end GaloisForLFunctions.ExceptionalLayerTheory
