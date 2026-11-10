import GaloisForLFunctions.FamilyContinuationTheory.ContinuationFromACommonSignal
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.JointAncestryLevelOneCapstones
import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAbscissa

/-!
# The signal exponent is the positivity level

The zero abscissa of `ζ` read on two scales.

* **The zeta kernel** (`isSignalKernel_zetaKernel`). For a real centre `c`,
  `G(s) = exp((s − c)²) / ((s − 1) ζ(s))` is holomorphic on `Re s > 1` and decays like
  `C/(1+t²)` on the strips `2 ≤ Re s ≤ B`: the Gaussian decays, `|ζ| ≥ ¼` and `|s − 1| ≥ 1` there.
* **The signal exponent** (`riemannZeta_ne_zero_of_signal_le`, `xiZeroHalfPlaneBound_of_signal_le`).
  If the signal of the zeta kernel is `O(Z^b)`, `b < 1`, then `ζ` has no zero in `Re s > b`.
  With two estimates for one sum (`xiZeroHalfPlaneBound_of_common_signal`) this is the
  continuation step for `ζ`. Bounds with every exponent above `½` give the Riemann hypothesis
  (`riemannHypothesis_of_forall_signal_le`).
* **The positivity level** (`exists_jasDressedPSDAbove_of_signal_le`). A signal bound with exponent
  `b ∈ [½, 1)` places the dressed lag aggregate at every level above `b + ½` on the characters of
  large primes. Conversely positivity at a level `σ ≥ 1` on large primes puts the zeros in
  `Re ρ ≤ σ − ½` (`xiZeroHalfPlaneBound_of_jasDressedPSDAbove`), and level one is the Riemann
  hypothesis (`riemannHypothesis_iff_jasDressedPSD_one`).

The exponent `b` of the signal and the level `b + ½` of the dressed aggregate measure the same
abscissa; a half-plane is not a premise of the positivity criterion.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.FamilyContinuationTheory

open _root_.RHTower

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

/-- **Every exponent above `½`.** Signal bounds for the zeta kernel with every exponent
`b > ½` give the Riemann hypothesis. -/
theorem riemannHypothesis_of_forall_signal_le
    (h : ∀ b : ℝ, 1 / 2 < b → ∃ c K Z₀ : ℝ, 0 < Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- the exponent `½ + min ε ¼` gives the width `min ε ¼ ≤ ε`
  obtain ⟨c, K, Z₀, hZ₀, hK⟩ := h (1 / 2 + min ε (1 / 4)) (by
    have : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
    linarith)
  have hmin : min ε (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hmin0 : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have hXi := xiZeroHalfPlaneBound_of_signal_le (c := c) (b := 1 / 2 + min ε (1 / 4))
    (by linarith) (by linarith) hZ₀ hK
  have := hXi ρ hρ
  have hle : min ε (1 / 4) ≤ ε := min_le_left _ _
  linarith

/-- **From the exponent to the level.** A signal bound for the zeta kernel with exponent
`b ∈ [½, 1)` gives positivity of the dressed lag aggregate on the characters of large primes at
every level `b + ½ + ε`. -/
theorem exists_jasDressedPSDAbove_of_signal_le {c b K Z₀ ε : ℝ} (hb₀ : 1 / 2 ≤ b) (hb : b < 1)
    (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : ∃ X : ℕ, JasDressedPSDAbove X (b + 1 / 2 + ε) := by
  have hXi := xiZeroHalfPlaneBound_of_signal_le hb₀ hb hZ₀ hK
  refine ⟨⌈Real.exp (1 / ε + 1)⌉₊ + 2, ?_⟩
  have hX : (2 : ℕ) ≤ ⌈Real.exp (1 / ε + 1)⌉₊ + 2 := by omega
  have hlog : 1 / ε + 1 ≤ Real.log ((⌈Real.exp (1 / ε + 1)⌉₊ + 2 : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    push_cast
    linarith [Nat.le_ceil (Real.exp (1 / ε + 1))]
  have h := jasDressedPSDAbove_of_xiZeroHalfPlaneBound (alpha := b - 1 / 2) (by linarith) hXi
    hε hε1 hX hlog
  rwa [show 1 + (b - 1 / 2) + ε = b + 1 / 2 + ε by ring] at h

end GaloisForLFunctions.FamilyContinuationTheory
