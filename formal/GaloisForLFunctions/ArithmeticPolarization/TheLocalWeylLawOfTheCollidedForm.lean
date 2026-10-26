import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormIsAPolarization
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity

/-!
# The local Weyl law of the collided form

At height `γ` the collided form of a twisted test, `D(e^{−iγu} f) = Σ_ρ m_ρ |f̂(ρ − iγ)|²`, weighs the
zeros of `ζ` near ordinate `γ` by the profile `|f̂|²`. It has the size of the conductor at every
height, unconditionally:

* **Upper bound** (`collidedForm_twist_le`): `D(e^{−iγu} f) ≤ 8 e^{a} B_f² (C + log(|γ| + 4))` for a
  `C²` test supported in `[−a, a]`, `B_f = 4(‖f‖₁ + ‖f″‖₁)`: transform decay against the Lorentzian
  zero mass `Σ_ρ 1/(1 + (γ − γ_ρ)²) = O(log |γ|)`.
* **Lower bound** (`collidedForm_twist_ge`): for every `ε > 0` there is `C` with
  `D(e^{−iγu} f) ≥ (log(1 + |γ|/8) − C − (4 + ε)e^a) ‖f‖₂² − (decaying tail terms)`: the collided form
  dominates Weil's form, and the shifted digamma density pays the prime sum.
* **The local Weyl law** (`eventually_collidedForm_twist_ge`, `eventually_collidedForm_twist_le`):
  as `|γ| → ∞`, `(1 − η) ‖f‖₂² log |γ| ≤ D(e^{−iγu} f) ≤ K_f log |γ|` for every `η > 0`: the collided
  polarization at height `γ` is the local zero density, with lower constant `‖f‖₂²`. Under RH it equals Weil's form, whose archimedean part is `log |γ| ‖f‖₂²`; the
  off-line defect `Δ = D − Re W` is what an unconditional evaluation of `D` must still bound.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- The envelope `B_f = 4(∫|f| + ∫|f″|)` of a `C²` test. -/
def envelope (f : ℝ → ℂ) : ℝ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)

theorem envelope_nonneg (f : ℝ → ℂ) : 0 ≤ envelope f := by
  unfold envelope
  have : 0 ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  positivity

/-- Transform decay at a twisted zero: `|f̂(ρ − iγ)| ≤ e^{a/2} B_f / (1 + |γ_ρ − γ|)²`. -/
theorem norm_tr_twist_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (γ : ℝ) {ρ : ℂ} (hρ : 0 ≤ ρ.re ∧ ρ.re ≤ 1) :
    ‖tr (twist γ f) ρ‖ ≤ Real.exp (a / 2) * envelope f / (1 + |ρ.im - γ|) ^ 2 := by
  rw [tr_twist, tr]
  have hdec := RHTower.norm_paperFT_le_decay hf hsupp (gammaOf (ρ - γ * I))
  have him : |(gammaOf (ρ - γ * I)).im| ≤ 1 / 2 := by
    rw [gammaOf, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [abs_le]; constructor <;> norm_num <;> linarith [hρ.1, hρ.2]
  have hre : (gammaOf (ρ - γ * I)).re = ρ.im - γ := by
    rw [gammaOf, Complex.div_I]; simp
  refine hdec.trans ?_
  rw [hre]
  have hexp : Real.exp (|(gammaOf (ρ - γ * I)).im| * a) ≤ Real.exp (a / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (gammaOf (ρ - γ * I)).im])
  have hB := envelope_nonneg f
  unfold envelope at hB ⊢
  gcongr

/-- **Upper bound.** The collided form at height `γ` is at most the Lorentzian zero mass there,
times the envelope of the test. -/
theorem collidedForm_twist_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (γ : ℝ) :
    collidedForm zetaZeroConfig (twist γ f) ≤
      Real.exp a * envelope f ^ 2 *
        (8 * (RHTower.xiLineTwoLogDerivConstant + Real.log (|γ| + 4))) := by
  set g : ℂ → ℝ := fun z => 1 / (1 + (γ - z.im) ^ 2)
  have hg0 : ∀ z, 0 ≤ g z := fun z => by simp only [g]; positivity
  have hgs : Summable fun q : RHTower.XiZeroCopy => g (q.1 : ℂ) :=
    RHTower.summable_lorentzMassTerm γ
  have hsum := ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy hg0 hgs
  have hbridge := ArithmeticCastelnuovoSeveri.tsum_xiZeroCopy_eq_zetaCarrier hgs
  have hmass : ∑' q : RHTower.XiZeroCopy, g (q.1 : ℂ) = RHTower.lorentzMass γ := rfl
  have hE : 0 ≤ Real.exp a * envelope f ^ 2 := by positivity
  calc collidedForm zetaZeroConfig (twist γ f)
      ≤ ∑' ρ : zetaZeroConfig.carrier,
          Real.exp a * envelope f ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * g (ρ : ℂ)) := by
        refine Summable.tsum_le_tsum (fun ρ => ?_)
          (zeta_summable_collided (contDiff_twist hf γ) ?_) (hsum.mul_left _)
        · have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
          have hnorm := norm_tr_twist_le hf ha hsupp γ (zetaZeroConfig.strip ρ ρ.2)
          rw [Complex.normSq_eq_norm_sq]
          have hd : 0 < 1 + |(ρ : ℂ).im - γ| := by positivity
          have hsq : ‖tr (twist γ f) ρ‖ ^ 2 ≤ Real.exp a * envelope f ^ 2 * g (ρ : ℂ) := by
            have h1 : ‖tr (twist γ f) ρ‖ ^ 2 ≤
                (Real.exp (a / 2) * envelope f / (1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hnorm 2
            have h2 : (Real.exp (a / 2) * envelope f / (1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2 =
                Real.exp a * envelope f ^ 2 / (1 + |(ρ : ℂ).im - γ|) ^ 4 := by
              rw [div_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
            have h3 : 1 + (γ - (ρ : ℂ).im) ^ 2 ≤ (1 + |(ρ : ℂ).im - γ|) ^ 4 := by
              have : (γ - (ρ : ℂ).im) ^ 2 = |(ρ : ℂ).im - γ| ^ 2 := by rw [sq_abs]; ring
              rw [this]
              nlinarith [abs_nonneg ((ρ : ℂ).im - γ), sq_nonneg (|(ρ : ℂ).im - γ|)]
            rw [h2] at h1
            refine h1.trans ?_
            simp only [g]
            rw [mul_one_div]
            exact div_le_div_of_nonneg_left hE (by positivity) h3
          nlinarith
        · exact hasCompactSupport_twist (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a))
            fun u hu => by
              by_contra h; exact hu (by rw [mem_Icc, ← abs_le]; exact hsupp u h)) γ
    _ = Real.exp a * envelope f ^ 2 * RHTower.lorentzMass γ := by
        rw [tsum_mul_left, ← hmass, hbridge]
    _ ≤ _ := mul_le_mul_of_nonneg_left (RHTower.lorentzMass_le_log γ) hE

/-- **Lower bound.** The collided form at height `γ` dominates Weil's form there, which the
shifted digamma density bounds below once the prime sum is paid. -/
theorem collidedForm_twist_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 ≤ a → ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      tsupport f ⊆ Set.Icc (-a) a → ∀ γ : ℝ,
        (Real.log (1 + |γ| / 8) - (C + (4 + ε) * Real.exp a)) * (∫ t, ‖f t‖ ^ 2) -
          envelope f ^ 2 / (8 * (1 + |γ| / 2)) -
          2 * Real.exp a * envelope f ^ 2 / (1 + |γ|) ^ 4 ≤
        collidedForm zetaZeroConfig (twist γ f) := by
  obtain ⟨C, hC0, hC⟩ := SquareRootThreshold.exists_mu_add_PX_ge hε
  refine ⟨C, hC0, fun {a} ha {f} hf hfs γ => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hsq : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show 2 * a = a + a by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos a).le]
  have hW := ArithmeticPositivityTheory.zetaZeroConfig_re_W_heightShift_ge_of_symbol_decay ha hf hfs
    (-γ / (2 * Real.pi)) (E := C + (4 + ε) * Real.exp a) fun τ => by
      simpa [hsq] using hC _ (Real.exp_pos (2 * a)).le τ
  have hξ : Real.pi * |(-γ / (2 * Real.pi))| = |γ| / 2 := by
    rw [abs_div, abs_neg, abs_of_pos Real.two_pi_pos]; field_simp
  rw [show Real.pi * |(-γ / (2 * Real.pi))| / 4 = |γ| / 8 by rw [hξ]; ring, hξ,
    show 2 * Real.pi * |(-γ / (2 * Real.pi))| = |γ| by rw [mul_assoc, hξ]; ring,
    ← twist_eq_heightShift] at hW
  exact hW.trans (re_W_le_collided (zeta_summable_collided (contDiff_twist hf γ)
    (hasCompactSupport_twist hfc γ)))

/-- **Local Weyl law, lower half.** For every `η > 0`, eventually in `|γ|`,
`(1 − η) ‖f‖₂² log |γ| ≤ D(e^{−iγu} f)`. -/
theorem eventually_collidedForm_twist_ge {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (ha : 0 ≤ a)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ γ in cocompact ℝ, (1 - η) * (∫ t, ‖f t‖ ^ 2) * Real.log |γ| ≤
      collidedForm zetaZeroConfig (twist γ f) := by
  obtain ⟨C, -, hC⟩ := collidedForm_twist_ge (ε := 1) one_pos
  set N := ∫ t, ‖f t‖ ^ 2
  have hN : 0 ≤ N := integral_nonneg fun _ => by positivity
  set B := envelope f
  set K := C + (4 + 1) * Real.exp a
  -- `|γ| → ∞` along the cocompact filter
  have habs : Tendsto (fun γ : ℝ => |γ|) (cocompact ℝ) atTop := by
    simpa using tendsto_norm_cocompact_atTop (E := ℝ)
  have hlog : Tendsto (fun γ : ℝ => Real.log |γ|) (cocompact ℝ) atTop :=
    Real.tendsto_log_atTop.comp habs
  rcases eq_or_lt_of_le hN with hN0 | hNpos
  · -- a null test: the collided form is nonnegative
    refine Eventually.of_forall fun γ => ?_
    rw [← hN0, mul_zero, zero_mul]
    exact collidedForm_nonneg _
  · -- the tails vanish and `η log |γ|` beats the constants
    have ht1 : Tendsto (fun γ : ℝ => B ^ 2 / (8 * (1 + |γ| / 2))) (cocompact ℝ) (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_left _ _
        (habs.atTop_div_const (by norm_num)))
    have ht2 : Tendsto (fun γ : ℝ => 2 * Real.exp a * B ^ 2 / (1 + |γ|) ^ 4) (cocompact ℝ)
        (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ _ habs)
    have hev1 := ht1.eventually (gt_mem_nhds (show (0 : ℝ) < N / 2 by linarith))
    have hev2 := ht2.eventually (gt_mem_nhds (show (0 : ℝ) < N / 2 by linarith))
    have hev3 := hlog.eventually_ge_atTop ((K + Real.log 8 + 1) / η)
    have hev4 := habs.eventually_ge_atTop 1
    filter_upwards [hev1, hev2, hev3, hev4] with γ h1 h2 h3 h4
    have hb := hC ha hf hfs γ
    have hlog8 : Real.log |γ| - Real.log 8 ≤ Real.log (1 + |γ| / 8) := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) (by linarith)
    have h3' : K + Real.log 8 + 1 ≤ η * Real.log |γ| := by
      rwa [div_le_iff₀ hη, mul_comm] at h3
    nlinarith [mul_le_mul_of_nonneg_left hlog8 hN, mul_le_mul_of_nonneg_left h3' hN]

/-- **Local Weyl law, upper half.** Eventually in `|γ|`, `D(e^{−iγu} f) ≤ K log |γ|`. -/
theorem eventually_collidedForm_twist_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) :
    ∃ K : ℝ, ∀ᶠ γ in cocompact ℝ, collidedForm zetaZeroConfig (twist γ f) ≤ K * Real.log |γ| := by
  set E := Real.exp a * envelope f ^ 2
  have hE : 0 ≤ E := by positivity
  set C := RHTower.xiLineTwoLogDerivConstant
  refine ⟨E * 8 * (|C| + 2), ?_⟩
  have habs : Tendsto (fun γ : ℝ => |γ|) (cocompact ℝ) atTop := by
    simpa using tendsto_norm_cocompact_atTop (E := ℝ)
  have hlog : Tendsto (fun γ : ℝ => Real.log |γ|) (cocompact ℝ) atTop :=
    Real.tendsto_log_atTop.comp habs
  filter_upwards [hlog.eventually_ge_atTop 1, habs.eventually_ge_atTop 4] with γ h1 h4
  refine (collidedForm_twist_le hf ha hsupp γ).trans ?_
  have hl : Real.log (|γ| + 4) ≤ Real.log |γ| + 1 := by
    have : |γ| + 4 ≤ 2 * |γ| := by linarith
    calc Real.log (|γ| + 4) ≤ Real.log (2 * |γ|) := Real.log_le_log (by positivity) this
      _ = Real.log 2 + Real.log |γ| := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 1 + Real.log |γ| := by linarith [Real.log_two_lt_d9]
      _ = _ := by ring
  have hC : C ≤ |C| := le_abs_self C
  nlinarith [abs_nonneg C]

end GaloisForLFunctions.ArithmeticPolarization
