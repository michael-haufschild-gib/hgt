import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.JointAncestryQuasiRHChainExclusion

/-!
# The two legs give the Riemann hypothesis

The route "a half-plane, then the line" for `ζ`, as one chain of theorems.

* **The zeta kernel** (`isSignalKernel_zetaKernel`). For a real centre `c`,
  `G(s) = exp((s − c)²) / ((s − 1) ζ(s))` is holomorphic on `Re s > 1` and decays like
  `C/(1+t²)` on the strips `2 ≤ Re s ≤ B`: the Gaussian decays, `|ζ| ≥ ¼` and `|s − 1| ≥ 1` there.
* **Leg A, receiver** (`riemannZeta_ne_zero_of_signal_le`, `xiZeroHalfPlaneBound_of_signal_le`).
  If the signal of the zeta kernel is `O(Z^b)`, `b < 1`, then `ζ` has no zero in `Re s > b`.
  With two estimates for one sum (`xiZeroHalfPlaneBound_of_common_signal`) this is the
  continuation step for `ζ`.
* **Both legs** (`riemannHypothesis_of_signal_le_of_jasDressedPSD_one`). A signal bound with
  exponent below `1` and positivity of the dressed lag aggregate at level one give the Riemann
  hypothesis: the first supplies the half-plane, and under a half-plane positivity at level one
  excludes every off-line zero.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.FamilyContinuationTheory

open RHTower

/-- The zeta kernel with Gaussian centre `c`: `exp((s − c)²) / ((s − 1) ζ(s))`. -/
def zetaKernel (c : ℝ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2) / zetaEntire s

/-- `(s − 1) ζ(s)` has no zero in `Re s > 1`. -/
theorem zetaEntire_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : zetaEntire s ≠ 0 := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  rw [zetaEntire_eq hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)

/-- On `Re s ≥ 2` the function `(s − 1) ζ(s)` has modulus at least `¼`. -/
theorem quarter_le_norm_zetaEntire {s : ℂ} (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ ‖zetaEntire s‖ := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  rw [zetaEntire_eq hs1, norm_mul]
  have h1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre : (1 : ℝ) ≤ (s - 1).re := by rw [sub_re, one_re]; linarith
    exact le_trans hre (le_trans (le_abs_self _) (abs_re_le_norm _))
  calc (1 : ℝ) / 4 = 1 * (1 / 4) := by ring
    _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
        mul_le_mul h1 (norm_riemannZeta_ge_of_two_le_re hs) (by norm_num) (norm_nonneg _)

/-- The modulus of the Gaussian factor: `exp((σ − c)² − t²)`. -/
theorem norm_cexp_sub_sq (c : ℝ) (s : ℂ) :
    ‖cexp ((s - c) ^ 2)‖ = Real.exp ((s.re - c) ^ 2 - s.im ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  have h : ((s - c) ^ 2).re = (s - c).re ^ 2 - (s - c).im ^ 2 := by
    rw [sq, mul_re]; ring
  rw [h, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]

/-- **The zeta kernel is a signal kernel.** -/
theorem isSignalKernel_zetaKernel (c : ℝ) : IsSignalKernel (zetaKernel c) where
  differentiableAt s hs := by
    unfold zetaKernel
    exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).div
      (differentiable_zetaEntire s) (zetaEntire_ne_zero_of_one_lt_re hs)
  decay B := by
    refine ⟨4 * Real.exp ((B + |c|) ^ 2), fun s h2 hB => ?_⟩
    have hz := quarter_le_norm_zetaEntire h2
    have hzpos : (0 : ℝ) < ‖zetaEntire s‖ := lt_of_lt_of_le (by norm_num) hz
    -- the Gaussian factor
    have hsq : (s.re - c) ^ 2 ≤ (B + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ B + |c| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le c, le_abs_self c]
        · linarith [neg_abs_le c, le_abs_self c]
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (B + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hexp : Real.exp (-(s.im ^ 2)) ≤ 1 / (1 + s.im ^ 2) := by
      rw [Real.exp_neg, one_div]
      refine inv_anti₀ (by positivity) ?_
      linarith [Real.add_one_le_exp (s.im ^ 2)]
    have hnum : ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := by
      rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul (Real.exp_le_exp.mpr hsq) hexp (Real.exp_pos _).le (Real.exp_pos _).le
    unfold zetaKernel
    rw [norm_div, div_le_iff₀ hzpos]
    calc ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := hnum
      _ = 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * (1 / 4) := by ring
      _ ≤ 4 * Real.exp ((B + |c|) ^ 2) / (1 + s.im ^ 2) * ‖zetaEntire s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)

/-- **Leg A for `ζ`.** If the signal of the zeta kernel is `O(Z^b)` with `b < 1`, then `ζ` has
no zero in `Re s > b`. -/
theorem riemannZeta_ne_zero_of_signal_le {c b K Z₀ : ℝ} (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) (hρ1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 := by
  have hE : DifferentiableOn ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) {s : ℂ | b < s.re} :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn
  have h := ne_zero_of_signal_le (isSignalKernel_zetaKernel c) hb hZ₀ hK
    differentiable_zetaEntire.differentiableOn hE (fun s _ => Complex.exp_ne_zero _)
    (fun s hs => by
      unfold zetaKernel
      exact div_mul_cancel₀ _ (zetaEntire_ne_zero_of_one_lt_re hs)) ρ hρ
  intro h0
  apply h
  rw [zetaEntire_eq hρ1, h0, mul_zero]

/-- A signal bound with exponent `b ∈ [½, 1)` puts every zero of `ξ` in `Re ρ ≤ b`. -/
theorem xiZeroHalfPlaneBound_of_signal_le {c b K Z₀ : ℝ} (hb₀ : 1 / 2 ≤ b) (hb : b < 1)
    (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b) :
    XiZeroHalfPlaneBound (b - 1 / 2) := by
  refine (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound (by linarith)).mp ?_
  intro s hs hs1
  exact riemannZeta_ne_zero_of_signal_le hb hZ₀ hK s (by linarith) hs1

/-- **The continuation step for `ζ`.** A sum with a direct bound `Z^{a₁}` and a comparison
`Z^{a₂}` with the signal of the zeta kernel puts every zero of `ξ` in `Re ρ ≤ max a₁ a₂`. -/
theorem xiZeroHalfPlaneBound_of_common_signal {c a₁ a₂ K Z₀ : ℝ} (J : ℝ → ℂ)
    (ha : 1 / 2 ≤ max a₁ a₂) (ha₁ : a₁ < 1) (ha₂ : a₂ < 1) (hZ₀ : 1 ≤ Z₀)
    (hJ : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ K * Z ^ a₁)
    (hJf : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ a₂) :
    XiZeroHalfPlaneBound (max a₁ a₂ - 1 / 2) := by
  refine (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound (by linarith)).mp ?_
  intro s hs hs1 h0
  have hE : DifferentiableOn ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) {s : ℂ | max a₁ a₂ < s.re} :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn
  refine ne_zero_of_common_signal (isSignalKernel_zetaKernel c) J ha₁ ha₂ hZ₀ hJ hJf
    differentiable_zetaEntire.differentiableOn hE (fun s _ => Complex.exp_ne_zero _)
    (fun s hs => by
      unfold zetaKernel
      exact div_mul_cancel₀ _ (zetaEntire_ne_zero_of_one_lt_re hs)) s (by linarith) ?_
  rw [zetaEntire_eq hs1, h0, mul_zero]

/-- **Both legs.** A signal bound for the zeta kernel with exponent `b ∈ [½, 1)` and positivity
of the dressed lag aggregate at level one give the Riemann hypothesis. -/
theorem riemannHypothesis_of_signal_le_of_jasDressedPSD_one {c b K Z₀ : ℝ} (hb₀ : 1 / 2 ≤ b)
    (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b)
    (hPSD : JasDressedPSD 1) : RiemannHypothesis :=
  riemannHypothesis_iff_jasDressedPSD_one_and_quasi.mpr
    ⟨hPSD, b - 1 / 2, by linarith, by linarith, xiZeroHalfPlaneBound_of_signal_le hb₀ hb hZ₀ hK⟩

end GaloisForLFunctions.FamilyContinuationTheory
