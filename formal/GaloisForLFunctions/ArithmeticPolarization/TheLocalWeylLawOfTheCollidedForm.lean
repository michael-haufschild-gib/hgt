import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormIsAPolarization
import GaloisForLFunctions.ArithmeticPolarization.ThePriceOfEllipticLocalization
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
* **The local Weyl law** (`collidedForm_twist_isTheta`): `D(e^{−iγu} f) ≍ log |γ|` as `|γ| → ∞` for
  every nonzero test: the collided polarization at height `γ` is the local zero density, with lower
  constant `‖f‖₂²`. Under RH it equals Weil's form, whose archimedean part is `log |γ| ‖f‖₂²`; the
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

end GaloisForLFunctions.ArithmeticPolarization
