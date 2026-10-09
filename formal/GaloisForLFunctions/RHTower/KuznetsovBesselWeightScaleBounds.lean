import GaloisForLFunctions.RHTower.KuznetsovBesselWeightBounds
import GaloisForLFunctions.RHTower.DeningerSechDecay

/-!
# Scale bounds for the spectral weights of a test function

Let `φ` be a test function with `φ̃(1) = 0`, with profile quotient `Q = G_φ/cosh`, and write

* `A = ‖φ‖₁` (`besselMassA`), `D = ‖(φ/y)'‖₁` (`besselSlopeD`),
* `Σ = Σ_{k≥1} |φ̃(2k+1)|` (`besselTailSigma`), `A₁ = ∫ |y| |φ(y)| dy` (`besselMomentA`).

Integrating the pointwise majorants of `Q` against the spectral kernels, split at a scale `w₀ > 0`,
gives for `0 ≤ ν < ½` (exceptional parameters, `norm_specWeight_besselWeight_real_le_scale`)

`|∫ h |W(1+it, ν)|²| ≤ 2π [(A cosh w₀/4 + Σ/2) cosh(2νw₀) w₀²/2
    + (D/2)(1 + (1 − e^{−2w₀})^{−1}) (1 + w₀) e^{−(1−2ν)w₀}/(1 − 2ν)²]`

and for every real `κ` (tempered parameters, `norm_specWeight_besselWeight_imag_le_scale`)

`|∫ h |W(1+it, iκ)|²| ≤ 4 [(A cosh w₀/4 + Σ/2) w₀²/2 + (D/2)(1 + (1 − e^{−2w₀})^{−1}) (1 + w₀) e^{−w₀}]`.

On `(0, w₀]` the small-scale majorant `|Q(w)| ≤ A cosh w/4 + Σ e^{−3w}/2` is used, on `(w₀, ∞)` the
large-scale one, `|Q(w)| ≤ D/(4 cosh w) + D/(4 sinh w) ≤ (D/2)(1 + (1 − e^{−2w₀})^{−1}) e^{−w}`.

Every derivative of `Q` is integrable (`integrable_iteratedDeriv_profileQ`): by Leibniz, the
derivatives of `G_φ` decay like `e^{−2|w|}` and those of `1/cosh` are bounded. Hence for `κ ≠ 0` and
every `K` (`norm_specWeight_besselWeight_imag_le_decay`)

`|∫ h |W(1+it, iκ)|²| ≤ π ‖Q^{(K)}‖₁ / (|sinh πκ| |2κ|^K)`.

Finally `Σ ≤ (A + A₁)/4` (`besselTailSigma_le`). For odd `m`, two integrations by parts in Bessel's
integral `J_m(y) = (2/π) ∫_0^{π/2} sin(mθ) sin(y sin θ) dθ` give `|J_m(y)| ≤ (|y| + y²)/m²`
(`abs_besselJ_odd_le`), so `|φ̃(m)| ≤ (A + A₁)/m²`, and `Σ_{k≥1} (2k+1)^{−2} ≤ 1/4`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-! ### The tail integral `∫_{w₀}^∞ w e^{−cw} dw` -/

theorem hasDerivAt_mul_exp_neg_primitive {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -(s / c + 1 / c ^ (2 : ℕ)) * Real.exp (-(c * s)))
      (t * Real.exp (-(c * t))) t := by
  have hin : HasDerivAt (fun s : ℝ => -(s / c + 1 / c ^ (2 : ℕ))) (-(1 / c)) t := by
    have h1 : HasDerivAt (fun s : ℝ => s / c + 1 / c ^ (2 : ℕ)) (1 / c) t := by
      simpa using ((hasDerivAt_id t).div_const c).add_const (1 / c ^ (2 : ℕ))
    simpa [Pi.neg_def] using h1.neg
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(c * s))) (Real.exp (-(c * t)) * (-c)) t := by
    have hlin : HasDerivAt (fun s : ℝ => -(c * s)) (-c) t := by
      simpa [Pi.neg_def] using ((hasDerivAt_id t).const_mul c).neg
    exact hlin.exp
  refine (hin.mul hexp).congr_deriv ?_
  field_simp
  ring

theorem tendsto_mul_exp_neg_primitive {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ => -(s / c + 1 / c ^ (2 : ℕ)) * Real.exp (-(c * s))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have h1 : Tendsto (fun t : ℝ => (c * t) * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    exact hpow.comp hscale
  have h2 : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hcomb := (h1.const_mul (-(1 / c ^ (2 : ℕ)))).add (h2.const_mul (-(1 / c ^ (2 : ℕ))))
  rw [show (-(1 / c ^ (2 : ℕ)) * (0 : ℝ) + -(1 / c ^ (2 : ℕ)) * (0 : ℝ)) = 0 by ring] at hcomb
  refine hcomb.congr fun t => ?_
  field_simp
  ring

/-- `∫_{w₀}^∞ w e^{−cw} dw = (w₀/c + 1/c²) e^{−cw₀}` for `c > 0`, `w₀ ≥ 0`. -/
theorem integral_Ioi_mul_exp_neg_mul_of_nonneg {c w₀ : ℝ} (hc : 0 < c) (hw₀ : 0 ≤ w₀) :
    ∫ w in Ioi w₀, w * Real.exp (-(c * w)) =
      (w₀ / c + 1 / c ^ (2 : ℕ)) * Real.exp (-(c * w₀)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hasDerivAt_mul_exp_neg_primitive hc.ne' x)
    (fun x hx => mul_nonneg (hw₀.trans (le_of_lt hx)) (Real.exp_pos _).le)
    (tendsto_mul_exp_neg_primitive hc)]
  ring

theorem integrableOn_Ioi_mul_exp_neg_mul_of_nonneg {c w₀ : ℝ} (hc : 0 < c) (hw₀ : 0 ≤ w₀) :
    IntegrableOn (fun w : ℝ => w * Real.exp (-(c * w))) (Ioi w₀) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_mul_exp_neg_primitive hc.ne' x)
    (fun _ hx => mul_nonneg (hw₀.trans (le_of_lt hx)) (Real.exp_pos _).le)
    (tendsto_mul_exp_neg_primitive hc)

/-! ### The data of a test function -/

variable (T : BesselTestFunction)

/-- `A = ‖φ‖₁`. -/
def besselMassA : ℝ := ∫ y, ‖T.φ y‖

/-- `D = ‖(φ/y)'‖₁`. -/
def besselSlopeD : ℝ := ∫ y, ‖deriv T.ψ y‖

/-- `Σ = Σ_{k≥1} |φ̃(2k+1)|`. -/
def besselTailSigma : ℝ := ∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖

theorem besselMassA_nonneg : 0 ≤ besselMassA T := integral_nonneg fun _ => norm_nonneg _

theorem besselSlopeD_nonneg : 0 ≤ besselSlopeD T := integral_nonneg fun _ => norm_nonneg _

theorem besselTailSigma_nonneg : 0 ≤ besselTailSigma T := tsum_nonneg fun _ => norm_nonneg _

/-! ### Majorants of `Q` below and above the scale `w₀` -/

/-- On `[0, w₀]`: `|Q(w)| ≤ A cosh w₀/4 + Σ/2`. -/
theorem norm_profileQ_le_head (h1 : T.besselCoeff 1 = 0) {w₀ w : ℝ} (hw : 0 ≤ w) (hww : w ≤ w₀) :
    ‖profileQ T w‖ ≤ Real.cosh w₀ * besselMassA T / 4 + besselTailSigma T / 2 := by
  refine (norm_profileQ_le_small T h1 hw).trans ?_
  have hA := besselMassA_nonneg T
  have hS := besselTailSigma_nonneg T
  have hc : Real.cosh w ≤ Real.cosh w₀ := Real.cosh_le_cosh.2 (by
    rw [abs_of_nonneg hw, abs_of_nonneg (hw.trans hww)]; exact hww)
  have he : Real.exp (-(3 * w)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc Real.cosh w * (∫ y, ‖T.φ y‖) / 4 +
        Real.exp (-(3 * w)) * (∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖) / 2
      ≤ Real.cosh w₀ * besselMassA T / 4 + 1 * besselTailSigma T / 2 := by
        unfold besselMassA besselTailSigma at *
        gcongr
    _ = _ := by ring

/-- The constant `M = (D/2)(1 + (1 − e^{−2w₀})^{−1})` of the large-scale majorant. -/
def besselTailConst (w₀ : ℝ) : ℝ := besselSlopeD T / 2 * (1 + 1 / (1 - Real.exp (-(2 * w₀))))

theorem besselTailConst_nonneg {w₀ : ℝ} (hw₀ : 0 < w₀) : 0 ≤ besselTailConst T w₀ := by
  have hD := besselSlopeD_nonneg T
  have he : Real.exp (-(2 * w₀)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have : 0 < 1 - Real.exp (-(2 * w₀)) := by linarith
  unfold besselTailConst
  positivity

/-- On `[w₀, ∞)`, `w₀ > 0`: `|Q(w)| ≤ M e^{−w}`. -/
theorem norm_profileQ_le_tail (h1 : T.besselCoeff 1 = 0) {w₀ w : ℝ} (hw₀ : 0 < w₀) (hww : w₀ ≤ w) :
    ‖profileQ T w‖ ≤ besselTailConst T w₀ * Real.exp (-w) := by
  have hw : 0 < w := lt_of_lt_of_le hw₀ hww
  refine (norm_profileQ_le_large T h1 hw).trans ?_
  have hD := besselSlopeD_nonneg T
  have hE : Real.exp (-(2 * w₀)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hq : 0 < 1 - Real.exp (-(2 * w₀)) := by linarith
  have hew := Real.exp_pos w
  have hemw := Real.exp_pos (-w)
  have hprod : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  have hcosh : 2 * Real.exp w ≤ 4 * Real.cosh w := by
    rw [Real.cosh_eq]; linarith
  have hkey : Real.exp (-w) ≤ Real.exp w * Real.exp (-(2 * w₀)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hsinh : 2 * Real.exp w * (1 - Real.exp (-(2 * w₀))) ≤ 4 * Real.sinh w := by
    rw [Real.sinh_eq]; nlinarith
  have hs : 0 < Real.sinh w := Real.sinh_pos_iff.2 hw
  have h1' : (∫ y, ‖deriv T.ψ y‖) / (4 * Real.cosh w) ≤
      besselSlopeD T / (2 * Real.exp w) :=
    div_le_div_of_nonneg_left hD (by positivity) hcosh
  have h2' : (∫ y, ‖deriv T.ψ y‖) / (4 * Real.sinh w) ≤
      besselSlopeD T / (2 * Real.exp w * (1 - Real.exp (-(2 * w₀)))) :=
    div_le_div_of_nonneg_left hD (by positivity) hsinh
  refine (add_le_add h1' h2').trans (le_of_eq ?_)
  unfold besselTailConst
  have hinv : Real.exp (-w) = 1 / Real.exp w := by rw [Real.exp_neg, one_div]
  rw [hinv]
  field_simp

/-! ### The weighted integral of `|Q|` -/

theorem integrableOn_norm_profileQ_mul (h1 : T.besselCoeff 1 = 0) {ν : ℝ} (h0 : 0 ≤ ν)
    (hν : ν < 1 / 2) :
    IntegrableOn (fun w : ℝ => ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w))) (Ioi 0) := by
  have hint := integrable_norm_G_mul_abs_cosh (besselOddProfile T h1) (ν := ν)
    (by rw [abs_of_nonneg h0]; linarith)
  refine hint.integrableOn.congr_fun (fun w hw => ?_) measurableSet_Ioi
  have hw0 : (0 : ℝ) < w := hw
  show ‖besselProfile T w‖ * _ = _
  rw [norm_besselProfile_eq, abs_of_pos hw0]
  field_simp

/-- **The split integral.** For `0 ≤ ν < ½` and `w₀ > 0`,
`∫_0^∞ |Q(w)| w cosh(2νw) dw ≤ (A cosh w₀/4 + Σ/2) cosh(2νw₀) w₀²/2
  + M (1 + w₀)/(1 − 2ν)² · e^{−(1−2ν)w₀}`. -/
theorem integral_norm_profileQ_mul_le (h1 : T.besselCoeff 1 = 0) {ν : ℝ} (h0 : 0 ≤ ν)
    (hν : ν < 1 / 2) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∫ w in Ioi (0 : ℝ), ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w)) ≤
      (Real.cosh w₀ * besselMassA T / 4 + besselTailSigma T / 2) * Real.cosh (2 * ν * w₀) *
          (w₀ ^ 2 / 2) +
        besselTailConst T w₀ * ((1 + w₀) / (1 - 2 * ν) ^ 2 * Real.exp (-((1 - 2 * ν) * w₀))) := by
  have hc : 0 < 1 - 2 * ν := by linarith
  have hc1 : 1 - 2 * ν ≤ 1 := by linarith
  have hA := besselMassA_nonneg T
  have hS := besselTailSigma_nonneg T
  have hM := besselTailConst_nonneg T hw₀
  have hfint := integrableOn_norm_profileQ_mul T h1 h0 hν
  rw [← Ioc_union_Ioi_eq_Ioi hw₀.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hfint.mono_set Ioc_subset_Ioi_self) (hfint.mono_set (Ioi_subset_Ioi hw₀.le))]
  refine add_le_add ?_ ?_
  · obtain ⟨H, hH⟩ : ∃ H : ℝ, H = Real.cosh w₀ * besselMassA T / 4 + besselTailSigma T / 2 :=
      ⟨_, rfl⟩
    rw [← hH]
    have hH0 : 0 ≤ H := by rw [hH]; positivity
    have hmaj : IntegrableOn (fun w : ℝ => H * Real.cosh (2 * ν * w₀) * w) (Ioc 0 w₀) :=
      (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc ∫ w in Ioc 0 w₀, ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w))
        ≤ ∫ w in Ioc 0 w₀, H * Real.cosh (2 * ν * w₀) * w :=
          setIntegral_mono_on (hfint.mono_set Ioc_subset_Ioi_self) hmaj measurableSet_Ioc
            fun w hw => by
              have hQ := norm_profileQ_le_head T h1 (w₀ := w₀) hw.1.le hw.2
              rw [← hH] at hQ
              have hch : Real.cosh (2 * ν * w) ≤ Real.cosh (2 * ν * w₀) := Real.cosh_le_cosh.2 (by
                rw [abs_of_nonneg (by have := hw.1.le; positivity),
                  abs_of_nonneg (by positivity)]
                exact mul_le_mul_of_nonneg_left hw.2 (by positivity))
              calc ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w))
                  ≤ H * (w * Real.cosh (2 * ν * w₀)) :=
                    mul_le_mul hQ (mul_le_mul_of_nonneg_left hch hw.1.le)
                      (by have := hw.1.le; positivity) hH0
                _ = H * Real.cosh (2 * ν * w₀) * w := by ring
      _ = H * Real.cosh (2 * ν * w₀) * (w₀ ^ 2 / 2) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hw₀.le, integral_id]
        ring
  · have hmaj : IntegrableOn
        (fun w : ℝ => besselTailConst T w₀ * (w * Real.exp (-((1 - 2 * ν) * w)))) (Ioi w₀) :=
      (integrableOn_Ioi_mul_exp_neg_mul_of_nonneg hc hw₀.le).const_mul _
    calc ∫ w in Ioi w₀, ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w))
        ≤ ∫ w in Ioi w₀, besselTailConst T w₀ * (w * Real.exp (-((1 - 2 * ν) * w))) :=
          setIntegral_mono_on (hfint.mono_set (Ioi_subset_Ioi hw₀.le)) hmaj measurableSet_Ioi
            fun w hw => by
              have hww : w₀ ≤ w := le_of_lt hw
              have hw0 : 0 ≤ w := hw₀.le.trans hww
              have hQ := norm_profileQ_le_tail T h1 hw₀ hww
              have hch : Real.cosh (2 * ν * w) ≤ Real.exp (2 * ν * w) :=
                (cosh_le_exp_abs'' _).trans (le_of_eq (by
                  rw [abs_of_nonneg (by positivity)]))
              calc ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w))
                  ≤ besselTailConst T w₀ * Real.exp (-w) * (w * Real.exp (2 * ν * w)) :=
                    mul_le_mul hQ (mul_le_mul_of_nonneg_left hch hw0) (by positivity)
                      (by positivity)
                _ = besselTailConst T w₀ * (w * Real.exp (-((1 - 2 * ν) * w))) := by
                  rw [show -((1 - 2 * ν) * w) = -w + 2 * ν * w by ring, Real.exp_add]
                  ring
      _ = besselTailConst T w₀ *
            ((w₀ / (1 - 2 * ν) + 1 / (1 - 2 * ν) ^ (2 : ℕ)) * Real.exp (-((1 - 2 * ν) * w₀))) := by
        rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_of_nonneg hc hw₀.le]
      _ ≤ _ := by
        have hsq : (1 - 2 * ν) ^ 2 ≤ 1 - 2 * ν := by nlinarith
        have hkey : w₀ / (1 - 2 * ν) ≤ w₀ / (1 - 2 * ν) ^ 2 :=
          div_le_div_of_nonneg_left hw₀.le (by positivity) hsq
        have : w₀ / (1 - 2 * ν) + 1 / (1 - 2 * ν) ^ (2 : ℕ) ≤ (1 + w₀) / (1 - 2 * ν) ^ 2 := by
          rw [add_div, add_comm (1 / _)]
          linarith
        gcongr

/-! ### Exceptional and tempered weights -/

/-- **Exceptional weights at scale `w₀`.** For `0 ≤ ν < ½` and `w₀ > 0`,
`|∫ h |W(1+it, ν)|²| ≤ 2π [(A cosh w₀/4 + Σ/2) cosh(2νw₀) w₀²/2
  + M (1 + w₀) e^{−(1−2ν)w₀}/(1 − 2ν)²]`, `M = (D/2)(1 + (1 − e^{−2w₀})^{−1})`. -/
theorem norm_specWeight_besselWeight_real_le_scale (h1 : T.besselCoeff 1 = 0) {ν : ℝ}
    (h0 : 0 ≤ ν) (hν : ν < 1 / 2) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ‖specWeight (besselWeight T h1) 1 ν‖ ≤
      2 * Real.pi *
        ((Real.cosh w₀ * besselMassA T / 4 + besselTailSigma T / 2) * Real.cosh (2 * ν * w₀) *
            (w₀ ^ 2 / 2) +
          besselTailConst T w₀ * ((1 + w₀) / (1 - 2 * ν) ^ 2 * Real.exp (-((1 - 2 * ν) * w₀)))) :=
  (norm_specWeight_besselWeight_real_le T h1 h0 hν).trans
    (mul_le_mul_of_nonneg_left (integral_norm_profileQ_mul_le T h1 h0 hν hw₀) (by positivity))

/-- **Tempered weights at scale `w₀`.** For every real `κ` and `w₀ > 0`,
`|∫ h |W(1+it, iκ)|²| ≤ 4 [(A cosh w₀/4 + Σ/2) w₀²/2 + M (1 + w₀) e^{−w₀}]`. -/
theorem norm_specWeight_besselWeight_imag_le_scale (h1 : T.besselCoeff 1 = 0) (κ : ℝ) {w₀ : ℝ}
    (hw₀ : 0 < w₀) :
    ‖specWeight (besselWeight T h1) 1 ((κ : ℂ) * Complex.I)‖ ≤
      4 * ((Real.cosh w₀ * besselMassA T / 4 + besselTailSigma T / 2) * (w₀ ^ 2 / 2) +
        besselTailConst T w₀ * ((1 + w₀) * Real.exp (-w₀))) := by
  have h := integral_norm_profileQ_mul_le T h1 le_rfl (by norm_num : (0 : ℝ) < 1 / 2) hw₀
  simp only [mul_zero, zero_mul, Real.cosh_zero, mul_one, sub_zero, one_pow, div_one,
    one_mul] at h
  exact (norm_specWeight_besselWeight_imag_le T h1 κ).trans
    (mul_le_mul_of_nonneg_left h (by norm_num))


/-! ### Decay in the tempered parameter -/

/-- `1/cosh = 2u` with `u = 1/(2 cosh)` the two-sided inverse weight, as a complex function. -/
def sechC (w : ℝ) : ℂ := ((2 * _root_.RHTower.deningerSechWeight 1 w : ℝ) : ℂ)

theorem div_cosh_eq_mul_sechC (z : ℂ) (w : ℝ) : z / (Real.cosh w : ℂ) = z * sechC w := by
  have hc : (Real.cosh w : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos w).ne'
  rw [sechC, _root_.RHTower.deningerSechWeight, one_mul]
  push_cast
  field_simp

theorem contDiff_sechC (n : ℕ) : ContDiff ℝ n sechC :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul
    (_root_.RHTower.deningerSechWeight_contDiff 1)).of_le (by exact_mod_cast le_top))

/-- Every derivative of `1/cosh` is bounded. -/
theorem exists_norm_iteratedFDeriv_sechC_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, ‖iteratedFDeriv ℝ j sechC w‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := _root_.RHTower.deningerSechWeight_iteratedFDeriv_le_mul 1 j
  refine ⟨C, hC0, fun w => ?_⟩
  have hu := _root_.RHTower.deningerSechWeight_contDiff 1
  have hv : ContDiff ℝ ∞ (fun w : ℝ => 2 * _root_.RHTower.deningerSechWeight 1 w) :=
    contDiff_const.mul hu
  have e1 : sechC = Complex.ofRealLI ∘ (fun w : ℝ => 2 * _root_.RHTower.deningerSechWeight 1 w) :=
    funext fun _ => rfl
  rw [e1, LinearIsometry.norm_iteratedFDeriv_comp_left _ hv.contDiffAt
    (by exact_mod_cast le_top)]
  have e2 : (fun w : ℝ => 2 * _root_.RHTower.deningerSechWeight 1 w) =
      (2 : ℝ) • _root_.RHTower.deningerSechWeight 1 := funext fun _ => rfl
  rw [e2, iteratedFDeriv_const_smul_apply (hu.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, Real.norm_two]
  have hle : _root_.RHTower.deningerSechWeight 1 w ≤ 1 / 2 := by
    rw [_root_.RHTower.deningerSechWeight, one_mul]
    exact div_le_div_of_nonneg_left zero_le_one two_pos
      (by nlinarith [Real.one_le_cosh w])
  calc 2 * ‖iteratedFDeriv ℝ j (_root_.RHTower.deningerSechWeight 1) w‖
      ≤ 2 * (C * _root_.RHTower.deningerSechWeight 1 w) := by gcongr; exact hC w
    _ ≤ 2 * (C * (1 / 2)) := by gcongr
    _ = C := by ring

theorem contDiff_div_cosh (P : OddDecayProfile) (n : ℕ) :
    ContDiff ℝ n (fun w : ℝ => P.G w / (Real.cosh w : ℂ)) := by
  have e : (fun w : ℝ => P.G w / (Real.cosh w : ℂ)) = fun w => P.G w * sechC w :=
    funext fun w => div_cosh_eq_mul_sechC _ w
  rw [e]
  exact (P.contDiff n).mul (contDiff_sechC n)

/-- **Every derivative of `G/cosh` is integrable**: by Leibniz, `|(G/cosh)^{(n)}(w)| ≤ K_n e^{−2|w|}`. -/
theorem integrable_iteratedDeriv_div_cosh (P : OddDecayProfile) (n : ℕ) :
    Integrable (iteratedDeriv n fun w : ℝ => P.G w / (Real.cosh w : ℂ)) := by
  have e : (fun w : ℝ => P.G w / (Real.cosh w : ℂ)) = fun w => P.G w * sechC w :=
    funext fun w => div_cosh_eq_mul_sechC _ w
  choose CG hCG0 hCG using P.exists_bound
  choose Cs hCs0 hCs using exists_norm_iteratedFDeriv_sechC_le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CG i * Cs (n - i) :=
    ⟨_, rfl⟩
  refine ((integrable_exp_neg_mul_abs' two_pos).const_mul K).mono'
    (((contDiff_div_cosh P n).continuous_iteratedDeriv' n).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, e]
  refine (norm_iteratedFDeriv_mul_le (P.contDiff n) (contDiff_sechC n) w le_rfl).trans ?_
  rw [hK, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv (f := P.G)]
  have h1 := hCG i w
  have h2 := hCs (n - i) w
  have h3 := hCG0 i
  calc (n.choose i : ℝ) * ‖iteratedDeriv i P.G w‖ * ‖iteratedFDeriv ℝ (n - i) sechC w‖
      ≤ (n.choose i : ℝ) * (CG i * Real.exp (-(2 * |w|))) * Cs (n - i) := by gcongr
    _ = (n.choose i : ℝ) * CG i * Cs (n - i) * Real.exp (-(2 * |w|)) := by ring

theorem contDiff_profileQ (h1 : T.besselCoeff 1 = 0) (n : ℕ) : ContDiff ℝ n (profileQ T) :=
  contDiff_div_cosh (besselOddProfile T h1) n

/-- `C_K(T) = ‖Q^{(K)}‖₁` is finite. -/
theorem integrable_iteratedDeriv_profileQ (h1 : T.besselCoeff 1 = 0) (n : ℕ) :
    Integrable (iteratedDeriv n (profileQ T)) :=
  integrable_iteratedDeriv_div_cosh (besselOddProfile T h1) n

/-- **Decay of the tempered weights.** For `κ ≠ 0` and every `K`,
`|∫ h |W(1+it, iκ)|²| ≤ π ‖Q^{(K)}‖₁ / (|sinh πκ| |2κ|^K)`. -/
theorem norm_specWeight_besselWeight_imag_le_decay (h1 : T.besselCoeff 1 = 0) {κ : ℝ}
    (hκ : κ ≠ 0) (K : ℕ) :
    ‖specWeight (besselWeight T h1) 1 ((κ : ℂ) * Complex.I)‖ ≤
      Real.pi * (∫ w, ‖iteratedDeriv K (profileQ T) w‖) /
        (|Real.sinh (Real.pi * κ)| * |2 * κ| ^ K) := by
  have h := norm_specWeight_imag_le_of_iteratedDeriv (besselOddProfile T h1) hκ K
    (contDiff_div_cosh (besselOddProfile T h1) K)
    (fun n _ => integrable_iteratedDeriv_div_cosh (besselOddProfile T h1) n)
  refine h.trans (le_of_eq ?_)
  rw [div_mul_div_comm]
  rfl

/-! ### The odd Bessel coefficients -/

/-- `∫_0^∞ |y| |φ(y)| dy`. -/
def besselMomentA : ℝ := ∫ y, |y| * ‖T.φ y‖

/-- The second `θ`-derivative of `sin(y sin θ)`. -/
def besselAngleSecond (y θ : ℝ) : ℝ :=
  -Real.sin (y * Real.sin θ) * (y * Real.cos θ) ^ 2 - Real.cos (y * Real.sin θ) * (y * Real.sin θ)

theorem continuous_besselAngleSecond (y : ℝ) : Continuous (besselAngleSecond y) := by
  unfold besselAngleSecond; fun_prop

theorem abs_besselAngleSecond_le (y θ : ℝ) : |besselAngleSecond y θ| ≤ |y| + y ^ 2 := by
  unfold besselAngleSecond
  have hs1 := Real.abs_sin_le_one (y * Real.sin θ)
  have hc1 := Real.abs_cos_le_one (y * Real.sin θ)
  have hs2 := Real.abs_sin_le_one θ
  have hc2 := Real.abs_cos_le_one θ
  calc |-Real.sin (y * Real.sin θ) * (y * Real.cos θ) ^ 2 -
        Real.cos (y * Real.sin θ) * (y * Real.sin θ)|
      ≤ |Real.sin (y * Real.sin θ)| * (|y| * |Real.cos θ|) ^ 2 +
          |Real.cos (y * Real.sin θ)| * (|y| * |Real.sin θ|) := by
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_mul, abs_mul]
    _ ≤ 1 * (|y| * 1) ^ 2 + 1 * (|y| * 1) := by gcongr
    _ = |y| + y ^ 2 := by rw [mul_one, sq_abs]; ring

/-- `∫_0^{π/2} sin(mθ) sin(y sin θ) dθ = −m^{−2} ∫_0^{π/2} sin(mθ) ∂²_θ sin(y sin θ) dθ` for odd `m`. -/
theorem integral_sin_mul_sin_sin_eq (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * Real.sin (y * Real.sin θ) =
      -((∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sin ((2 * k + 1 : ℕ) * θ) * besselAngleSecond y θ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((2 * k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 < m := by rw [hm]; positivity
  have hH : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => -Real.cos (m * θ) * Real.sin (y * Real.sin θ) / m +
      Real.sin (m * θ) * (Real.cos (y * Real.sin θ) * (y * Real.cos θ)) / m ^ 2)
      (Real.sin (m * θ) * Real.sin (y * Real.sin θ) +
        Real.sin (m * θ) * besselAngleSecond y θ / m ^ 2) θ := by
    intro θ
    have hs : HasDerivAt (fun θ : ℝ => Real.sin (m * θ)) (Real.cos (m * θ) * m) θ := by
      simpa using ((hasDerivAt_id θ).const_mul m).sin
    have hc : HasDerivAt (fun θ : ℝ => Real.cos (m * θ)) (-Real.sin (m * θ) * m) θ := by
      simpa using ((hasDerivAt_id θ).const_mul m).cos
    have hsin : HasDerivAt (fun θ : ℝ => y * Real.sin θ) (y * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).const_mul y
    have hcos : HasDerivAt (fun θ : ℝ => y * Real.cos θ) (y * -Real.sin θ) θ :=
      (Real.hasDerivAt_cos θ).const_mul y
    have hg : HasDerivAt (fun θ : ℝ => Real.sin (y * Real.sin θ))
        (Real.cos (y * Real.sin θ) * (y * Real.cos θ)) θ := hsin.sin
    have hg1 : HasDerivAt (fun θ : ℝ => Real.cos (y * Real.sin θ) * (y * Real.cos θ))
        (besselAngleSecond y θ) θ := by
      refine ((hsin.cos).mul hcos).congr_deriv ?_
      unfold besselAngleSecond
      ring
    refine (((hc.neg.mul hg).div_const m).add ((hs.mul hg1).div_const (m ^ 2))).congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hc1 : Continuous fun θ : ℝ => Real.sin (m * θ) * Real.sin (y * Real.sin θ) := by fun_prop
  have hc2 : Continuous fun θ : ℝ => Real.sin (m * θ) * besselAngleSecond y θ / m ^ 2 :=
    ((by fun_prop : Continuous fun θ : ℝ => Real.sin (m * θ)).mul
      (continuous_besselAngleSecond y)).div_const _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := Real.pi / 2)
    (fun θ _ => hH θ) ((hc1.add hc2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_div] at hFTC
  have hcm : Real.cos (m * (Real.pi / 2)) = 0 := by rw [hm]; exact cos_odd_mul_pi_div_two k
  simp only [hcm, Real.cos_pi_div_two, mul_zero, zero_mul, neg_zero, zero_div, Real.sin_zero,
    add_zero, sub_zero] at hFTC
  linarith

/-- **`|J_m(y)| ≤ (|y| + y²)/m²` for odd `m`.** Two integrations by parts in Bessel's integral;
the boundary terms vanish because `cos(mπ/2) = 0`, `sin(y sin 0) = 0` and `cos(π/2) = 0`. -/
theorem abs_besselJ_odd_le (k : ℕ) (y : ℝ) :
    |besselJ (2 * k + 1) y| ≤ (|y| + y ^ 2) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
  have hm : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hbound : |∫ θ in (0 : ℝ)..Real.pi / 2, Real.sin ((2 * k + 1 : ℕ) * θ) * besselAngleSecond y θ| ≤
      (|y| + y ^ 2) * |Real.pi / 2 - 0| := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin ((2 * k + 1 : ℕ) * θ)| * |besselAngleSecond y θ| ≤ 1 * (|y| + y ^ 2) :=
          mul_le_mul (Real.abs_sin_le_one _) (abs_besselAngleSecond_le y θ) (abs_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)] at hbound
  rw [besselJ_odd_eq_integral, integral_sin_mul_sin_sin_eq, abs_mul, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi), abs_div, abs_of_pos hm]
  calc 2 / Real.pi * (|∫ θ in (0 : ℝ)..Real.pi / 2,
        Real.sin ((2 * k + 1 : ℕ) * θ) * besselAngleSecond y θ| / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
      ≤ 2 / Real.pi * ((|y| + y ^ 2) * (Real.pi / 2) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by gcongr
    _ = (|y| + y ^ 2) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by field_simp

theorem integrable_abs_mul_norm_φ : Integrable fun y : ℝ => |y| * ‖T.φ y‖ :=
  (continuous_abs.mul T.continuous_φ.norm).integrable_of_hasCompactSupport
    T.hasCompactSupport_φ.norm.mul_left

/-- `|φ̃(m)| ≤ (A + A₁)/m²` for odd `m`. -/
theorem norm_besselCoeff_odd_le (k : ℕ) :
    ‖T.besselCoeff (2 * k + 1)‖ ≤
      (besselMassA T + besselMomentA T) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
  have hm : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  rw [BesselTestFunction.besselCoeff, besselMassA, besselMomentA, ← integral_add T.integrable_φ.norm
    (integrable_abs_mul_norm_φ T), ← integral_div]
  refine norm_integral_le_of_norm_le
    ((T.integrable_φ.norm.add (integrable_abs_mul_norm_φ T)).div_const _)
    (Eventually.of_forall fun y => ?_)
  have hφ : ‖T.φ y‖ = ‖T.ψ y‖ * |y| := by
    rw [← T.ψ_mul_self y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hφ]
  calc |besselJ (2 * k + 1) y| * ‖T.ψ y‖
      ≤ (|y| + y ^ 2) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 * ‖T.ψ y‖ := by
        gcongr; exact abs_besselJ_odd_le k y
    _ = (‖T.ψ y‖ * |y| + |y| * (‖T.ψ y‖ * |y|)) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← sq_abs y]; ring

theorem hasSum_one_div_succ_sub_one_div_succ_succ :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by positivity) (by linarith))]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) =
      1 - 1 / ((n : ℝ) + 1) := fun n => by
    have := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpart]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- **`Σ ≤ (A + A₁)/4`.** -/
theorem besselTailSigma_le : besselTailSigma T ≤ (besselMassA T + besselMomentA T) / 4 := by
  have hA := besselMassA_nonneg T
  have hA1 : 0 ≤ besselMomentA T := integral_nonneg fun _ => by positivity
  have htel := (hasSum_one_div_succ_sub_one_div_succ_succ).mul_left
    ((besselMassA T + besselMomentA T) / 4)
  rw [mul_one] at htel
  rw [besselTailSigma, ← htel.tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_norm_besselCoeff_tail T) htel.summable
  refine (norm_besselCoeff_odd_le T (k + 1)).trans ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hpos : (0 : ℝ) < ((2 * (k + 1) + 1 : ℕ) : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have e : (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp; ring
  rw [e]
  have hq : (4 : ℝ) * (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤ ((2 * (k + 1) + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast; nlinarith
  calc besselMassA T + besselMomentA T
      = (besselMassA T + besselMomentA T) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) *
          (4 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by field_simp
    _ ≤ (besselMassA T + besselMomentA T) / 4 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) *
          ((2 * (k + 1) + 1 : ℕ) : ℝ) ^ 2 := by gcongr

/-! ### The bounds in terms of `A`, `A₁` and `D` only -/

/-- **Exceptional weights, data form.** For `0 ≤ ν < ½` and `w₀ > 0`,
`|∫ h |W(1+it, ν)|²| ≤ 2π [(A cosh w₀/4 + (A + A₁)/8) cosh(2νw₀) w₀²/2
  + M (1 + w₀) e^{−(1−2ν)w₀}/(1 − 2ν)²]`. -/
theorem norm_specWeight_besselWeight_real_le_moments (h1 : T.besselCoeff 1 = 0) {ν : ℝ}
    (h0 : 0 ≤ ν) (hν : ν < 1 / 2) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ‖specWeight (besselWeight T h1) 1 ν‖ ≤
      2 * Real.pi *
        ((Real.cosh w₀ * besselMassA T / 4 + (besselMassA T + besselMomentA T) / 8) *
            Real.cosh (2 * ν * w₀) * (w₀ ^ 2 / 2) +
          besselTailConst T w₀ * ((1 + w₀) / (1 - 2 * ν) ^ 2 * Real.exp (-((1 - 2 * ν) * w₀)))) := by
  refine (norm_specWeight_besselWeight_real_le_scale T h1 h0 hν hw₀).trans ?_
  have hS := besselTailSigma_le T
  have : besselTailSigma T / 2 ≤ (besselMassA T + besselMomentA T) / 8 := by linarith
  gcongr

/-- **Tempered weights, data form.** For every real `κ` and `w₀ > 0`,
`|∫ h |W(1+it, iκ)|²| ≤ 4 [(A cosh w₀/4 + (A + A₁)/8) w₀²/2 + M (1 + w₀) e^{−w₀}]`. -/
theorem norm_specWeight_besselWeight_imag_le_moments (h1 : T.besselCoeff 1 = 0) (κ : ℝ) {w₀ : ℝ}
    (hw₀ : 0 < w₀) :
    ‖specWeight (besselWeight T h1) 1 ((κ : ℂ) * Complex.I)‖ ≤
      4 * ((Real.cosh w₀ * besselMassA T / 4 + (besselMassA T + besselMomentA T) / 8) *
          (w₀ ^ 2 / 2) + besselTailConst T w₀ * ((1 + w₀) * Real.exp (-w₀))) := by
  refine (norm_specWeight_besselWeight_imag_le_scale T h1 κ hw₀).trans ?_
  have hS := besselTailSigma_le T
  have : besselTailSigma T / 2 ≤ (besselMassA T + besselMomentA T) / 8 := by linarith
  gcongr

end

end GaloisForLFunctions.RHTower.DeckPointPair
