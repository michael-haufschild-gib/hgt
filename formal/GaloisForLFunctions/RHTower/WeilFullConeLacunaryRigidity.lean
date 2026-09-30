import GaloisForLFunctions.RHTower.WeilFullConeSummableDeficitRigidity

/-!
# Lacunary rigidity: a Weil-positive system cannot deviate from `Λ` on a sparse set

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_lacunary`, unconditional). Let `lam` be
Weil-positive with the pole term (`WeilPositiveFull`). Suppose it agrees with `Λ` off a lacunary set
`n_0 < n_1 < ⋯` with `n_0 ≥ 3` and `n_{i+1} ≥ 3 n_i`. Then `lam = Λ`. The values on the lacunary set
are arbitrary a priori: they may change sign and need not be summable.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_of_powers`). For `p ≥ 3`, no Weil-positive system
differs from `Λ` only at the powers of `p`.

**The test.** The pair `f = Φχ_L + ε Φχ_L(· − log n_j)` (`pairRiemannKernel`), with `ε = ∓1` chosen
against the sign of the deviation at `n_j`.
- Its autocorrelation is `2K_L(y) + ε(K_L(y + c) + K_L(y − c))`, so the atom `n_j` pays `−2|v_j| K(0)`.
- Every other atom sits at log-distance at least `log 3` from `0`, from `log n_j` and from
  `−log n_j`.

**The decay input.** `(1 + D) K(D) ≤ 4.0804 e^{3D} e^{−π(e^D − 1)} K(0)` for `D ≥ log 2`
(`one_add_mul_riemannAutocorr_le`). This follows from the L156 shift law
(`riemannAutocorr_two_mul_le`) and `R(x) ≤ 4x² e^{−π(x−1)}`. Summed over a 3-lacunary set it gives
at most `0.218` per family (`lacunary_sum_decay_le`, `lacunary_sum_decay_sub_le`).

**The argument.** Let `v = (Λ − lam)/√n` and `M = sup_i |v(n_i)|/(1 + log n_i)`, which is finite by
the Weil box bound `abs_le_of_weilPositive`.
- Positivity at each atom gives `|v(n_j)| ≤ 0.873 M (1 + log n_j)` (`lacunary_atom_le`).
- Taking the supremum gives `M ≤ 0.873 M`, so `M = 0`.

**Reach of the method.** The mechanism is incoherence of `Φ` against *separated* sets of log-atoms.
Sets whose logarithms accumulate, such as `{p^a q^b}` or all integers, escape it. Producers of
Weil positivity must have dense support (`WeilPositiveShortIntervalSupport`), so sparse deviations
are exactly what the kernel method can pin.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## The two-point test `Φχ_L + ε Φχ_L(· − c)` -/

/-- The two-point combination `Φχ_L + ε Φχ_L(· − c)`. -/
def pairRiemannKernel (L c ε : ℝ) (u : ℝ) : ℂ :=
  truncatedRiemannKernel L u + (ε : ℂ) * truncatedRiemannKernel L (u - c)

/-- Its real profile. -/
def pairRiemannKernelReal (L c ε : ℝ) (u : ℝ) : ℝ :=
  truncatedRiemannKernelReal L u + ε * truncatedRiemannKernelReal L (u - c)

theorem pairRiemannKernel_eq (L c ε : ℝ) :
    pairRiemannKernel L c ε = fun u => (pairRiemannKernelReal L c ε u : ℂ) := by
  funext u
  simp only [pairRiemannKernel, pairRiemannKernelReal, truncatedRiemannKernel_eq]
  push_cast; rfl

theorem contDiff_pairRiemannKernel (L c ε : ℝ) : ContDiff ℝ 2 (pairRiemannKernel L c ε) := by
  have h := contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))
  have h1 : ContDiff ℝ 2 fun u : ℝ => truncatedRiemannKernel L (u - c) :=
    h.comp (contDiff_id.sub contDiff_const)
  exact h.add (contDiff_const.mul h1)

theorem hasCompactSupport_pairRiemannKernel (L c ε : ℝ) :
    HasCompactSupport (pairRiemannKernel L c ε) :=
  (hasCompactSupport_truncatedRiemannKernel L).add
    ((hasCompactSupport_comp_sub (hasCompactSupport_truncatedRiemannKernel L) c).mul_left)

/-- The transform of the pair: `(1 + ε e^{izc}) û(z)`. -/
theorem paperFT_pairRiemannKernel (L c ε : ℝ) (z : ℂ) :
    paperFT (pairRiemannKernel L c ε) z =
      (1 + (ε : ℂ) * Complex.exp (I * z * c)) * paperFT (truncatedRiemannKernel L) z := by
  have h0 : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) := by
    simpa using integrable_translate_mul_cexp L 0 z
  have h1 := integrable_translate_mul_cexp L c z
  have e1 := paperFT_comp_sub (truncatedRiemannKernel L) c z
  unfold paperFT at e1 ⊢
  have hsplit : (fun u : ℝ => pairRiemannKernel L c ε u * Complex.exp (I * z * u)) =
      fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) +
        (ε : ℂ) * (truncatedRiemannKernel L (u - c) * Complex.exp (I * z * u)) := by
    funext u; simp only [pairRiemannKernel]; ring
  beta_reduce at e1
  rw [hsplit, integral_add h0 (h1.const_mul _), integral_const_mul, e1]
  ring

theorem norm_pairMultiplier_le {c : ℝ} (hc : 0 ≤ c) (ε : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖1 + (ε : ℂ) * Complex.exp (I * z * c)‖ ≤ 1 + |ε| * Real.exp (c / 2) := by
  have hre : (I * z * (c : ℂ)).re = -(z.im * c) := by simp [Complex.mul_re]
  have h1 : -(z.im * c) ≤ c / 2 := by
    have h2 : |z.im * c| ≤ 1 / 2 * c := by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_right hz hc
    have := neg_abs_le (z.im * c)
    linarith
  calc ‖1 + (ε : ℂ) * Complex.exp (I * z * c)‖ ≤ ‖(1 : ℂ)‖ + ‖(ε : ℂ) * Complex.exp (I * z * c)‖ :=
        norm_add_le _ _
    _ = 1 + |ε| * Real.exp (-(z.im * c)) := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
    _ ≤ 1 + |ε| * Real.exp (c / 2) := by gcongr

/-- The zero side of the pair. -/
theorem norm_W_pairRiemannKernel_le (L : ℝ) {c : ℝ} (hc : 0 ≤ c) (ε : ℝ) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (pairRiemannKernel L c ε) (pairRiemannKernel L c ε)‖ ≤
      (1 + |ε| * Real.exp (c / 2)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have hm0 : 0 ≤ 1 + |ε| * Real.exp (c / 2) := by positivity
  have h := norm_W_le_of_zero_bound (f := pairRiemannKernel L c ε)
    (E := (1 + |ε| * Real.exp (c / 2)) * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum *
          ((1 + |ε| * Real.exp (c / 2)) * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = _ := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  constructor
  · rw [paperFT_pairRiemannKernel, norm_mul]
    have hm := norm_pairMultiplier_le hc ε hIm
    calc (1 + |(ρ : ℂ).im|) * (‖1 + (ε : ℂ) * Complex.exp (I * gammaOf ρ * c)‖ *
          ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖1 + (ε : ℂ) * Complex.exp (I * gammaOf ρ * c)‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ (1 + |ε| * Real.exp (c / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv1 (by positivity) hm0
  · rw [paperFT_pairRiemannKernel, norm_mul]
    have hm := norm_pairMultiplier_le hc ε hIm'
    calc (1 + |(ρ : ℂ).im|) * (‖1 + (ε : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c)‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖1 + (ε : ℂ) * Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c)‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ (1 + |ε| * Real.exp (c / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv2 (by positivity) hm0

/-- The autocorrelation of the pair: `(1 + ε²) K_L(y) + ε (K_L(y + c) + K_L(y − c))`. -/
theorem weilTest_pairRiemannKernel (L c ε y : ℝ) :
    EF.weilTest (pairRiemannKernel L c ε) (pairRiemannKernel L c ε) y =
      (((1 + ε ^ 2) * truncatedRiemannAutocorr L y +
        ε * (truncatedRiemannAutocorr L (y + c) + truncatedRiemannAutocorr L (y - c)) : ℝ) : ℂ) := by
  rw [pairRiemannKernel_eq, weilTest_ofReal_eq]
  congr 1
  have hF : ∀ t, truncatedRiemannKernelReal L t + ε * truncatedRiemannKernelReal L (t - c) =
      ∑ i : Fin 2, ![1, ε] i * truncatedRiemannKernelReal L (t - ![0, c] i) := by
    intro t
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    ring
  have e := integral_translateComb_autocorr Finset.univ ![1, ε] ![0, c]
    (continuous_truncatedRiemannKernelReal L) (hasCompactSupport_truncatedRiemannKernelReal L) y
  have hk : ∀ v, (∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - v)) =
      truncatedRiemannAutocorr L v := fun v => rfl
  simp only [hk] at e
  have hint : (∫ t, pairRiemannKernelReal L c ε t * pairRiemannKernelReal L c ε (t - y)) =
      ∫ t, (∑ i : Fin 2, ![1, ε] i * truncatedRiemannKernelReal L (t - ![0, c] i)) *
        (∑ j : Fin 2, ![1, ε] j * truncatedRiemannKernelReal L (t - y - ![0, c] j)) := by
    congr 1; funext t; simp only [pairRiemannKernelReal]; rw [hF, hF (t - y)]
  rw [hint, e]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show y + 0 - 0 = y by ring, show y + c - 0 = y + c by ring, show y + 0 - c = y - c by ring,
    show y + c - c = y by ring]
  ring

/-! ## Decay of the kernel autocorrelation -/

theorem riemannAutocorr_neg (y : ℝ) : riemannAutocorr (-y) = riemannAutocorr y := by
  unfold riemannAutocorr
  rw [← integral_sub_right_eq_self (fun t => riemannKernelReal t * riemannKernelReal (t - -y)) y]
  congr 1; funext t
  rw [show t - y - -y = t by ring, mul_comm]

theorem riemannAutocorr_nonneg (y : ℝ) : 0 ≤ riemannAutocorr y :=
  integral_nonneg fun t => mul_nonneg (riemannKernelReal_pos t).le (riemannKernelReal_pos _).le

/-- `R(x) ≤ 4x² e^{−π(x−1)}` for `x ≥ 1`. -/
theorem riemannShiftRatio_le_four_sq {x : ℝ} (hx : 1 ≤ x) :
    riemannShiftRatio x ≤ 4 * x ^ 2 * Real.exp (-(π * (x - 1))) := by
  unfold riemannShiftRatio
  have hπ := Real.pi_gt_three
  have hD : 0 < 4 * π ^ 2 - 6 * π := by nlinarith
  have h1 : (4 * π ^ 2 * x - 6 * π) / (4 * π ^ 2 - 6 * π) ≤ 2 * x := by
    rw [div_le_iff₀ hD]
    have hk : 0 ≤ 4 * π * (π - 3) * x :=
      mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hπ.le)) (by linarith)
    have hp := Real.pi_pos
    have e : 2 * x * (4 * π ^ 2 - 6 * π) - (4 * π ^ 2 * x - 6 * π) = 4 * π * (π - 3) * x + 6 * π := by
      ring
    nlinarith
  have h0 : 0 ≤ (4 * π ^ 2 * x - 6 * π) / (4 * π ^ 2 - 6 * π) := by
    apply div_nonneg _ hD.le; nlinarith
  have hsq : ((4 * π ^ 2 * x - 6 * π) / (4 * π ^ 2 - 6 * π)) ^ 2 ≤ 4 * x ^ 2 := by
    calc _ ≤ (2 * x) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * x ^ 2 := by ring
  calc Real.exp (-(π * (x - 1))) * ((4 * π ^ 2 * x - 6 * π) / (4 * π ^ 2 - 6 * π)) ^ 2
      ≤ Real.exp (-(π * (x - 1))) * (4 * x ^ 2) := mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = _ := by ring

/-- The decay profile `4.0804 e^{3D} e^{−π(e^D − 1)}`. -/
def lacunaryDecay (D : ℝ) : ℝ := 4.0804 * Real.exp (3 * D) * Real.exp (-(π * (Real.exp D - 1)))

theorem lacunaryDecay_nonneg (D : ℝ) : 0 ≤ lacunaryDecay D := by unfold lacunaryDecay; positivity

/-- `(1 + D) K(D) ≤ lacunaryDecay(D) K(0)` for `D ≥ log 2`. -/
theorem one_add_mul_riemannAutocorr_le {D : ℝ} (hD : Real.log 2 ≤ D) :
    (1 + D) * riemannAutocorr D ≤ lacunaryDecay D * riemannAutocorr 0 := by
  have hD0 : 0 ≤ D := le_trans (Real.log_nonneg (by norm_num)) hD
  have hx2 : 2 ≤ Real.exp (2 * (D / 2)) := by
    rw [show 2 * (D / 2) = D by ring]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hD
  have h := riemannAutocorr_two_mul_le (h := D / 2) (by linarith) hx2
  rw [show 2 * (D / 2) = D by ring] at h
  have hK0 := riemannAutocorr_zero_pos
  have hR := riemannShiftRatio_le_four_sq (x := Real.exp D) (Real.one_le_exp hD0)
  have h1D : 1 + D ≤ Real.exp D := by have := Real.add_one_le_exp D; linarith
  have hKD := riemannAutocorr_nonneg D
  have hR0 : 0 ≤ riemannShiftRatio (Real.exp D) := by unfold riemannShiftRatio; positivity
  calc (1 + D) * riemannAutocorr D
      ≤ Real.exp D * ((101 / 100) ^ 2 * riemannShiftRatio (Real.exp D) * riemannAutocorr 0) :=
        mul_le_mul h1D h hKD (Real.exp_pos _).le
    _ ≤ Real.exp D * ((101 / 100) ^ 2 * (4 * Real.exp D ^ 2 * Real.exp (-(π * (Real.exp D - 1)))) *
          riemannAutocorr 0) := by gcongr
    _ = lacunaryDecay D * riemannAutocorr 0 := by
        unfold lacunaryDecay
        have e3 : Real.exp (3 * D) = Real.exp D * Real.exp D ^ 2 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
        rw [e3]; norm_num; ring

theorem lacunaryDecay_antitone {D D' : ℝ} (hD : 0 ≤ D) (hDD : D ≤ D') :
    lacunaryDecay D' ≤ lacunaryDecay D := by
  unfold lacunaryDecay
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hπ := Real.pi_gt_three
  have h1 : Real.exp D * (D' - D) ≤ Real.exp D' - Real.exp D := by
    have := Real.add_one_le_exp (D' - D)
    have e : Real.exp D' = Real.exp D * Real.exp (D' - D) := by rw [← Real.exp_add]; ring_nf
    rw [e]; nlinarith [Real.exp_pos D]
  have h2 : D' - D ≤ Real.exp D * (D' - D) := by
    have := Real.one_le_exp hD
    nlinarith
  nlinarith

/-- `lacunaryDecay (k log 3) ≤ 0.2177 · 1000^{1−k}` for `k ≥ 1`. -/
theorem lacunaryDecay_log_three_le (k : ℕ) :
    lacunaryDecay ((k + 1 : ℕ) * Real.log 3) ≤ 0.2177 * (1 / 1000 : ℝ) ^ k := by
  have hπ1 := Real.pi_gt_d2
  have hpi := exp_pi_ge
  have h3 : ∀ m : ℕ, Real.exp ((m : ℝ) * Real.log 3) = 3 ^ m := by
    intro m; rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  induction k with
  | zero =>
    unfold lacunaryDecay
    simp only [Nat.zero_add, Nat.cast_one, one_mul, pow_zero, mul_one]
    rw [Real.exp_log (by norm_num)]
    have e3 : Real.exp (3 * Real.log 3) = 27 := by
      rw [show (3 : ℝ) * Real.log 3 = ((3 : ℕ) : ℝ) * Real.log 3 by norm_num, h3]; norm_num
    rw [e3, show -(π * (3 - 1)) = -(2 * π) by ring]
    have he : (506.25 : ℝ) ≤ Real.exp (2 * π) := by
      rw [show 2 * π = π + π by ring, Real.exp_add]; nlinarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith
  | succ k ih =>
    have hstep : lacunaryDecay ((k + 1 + 1 : ℕ) * Real.log 3) ≤
        (1 / 1000) * lacunaryDecay ((k + 1 : ℕ) * Real.log 3) := by
      unfold lacunaryDecay
      have ea : Real.exp ((k + 1 + 1 : ℕ) * Real.log 3) = 3 * Real.exp ((k + 1 : ℕ) * Real.log 3) := by
        rw [h3, h3]; ring
      set X := Real.exp ((k + 1 : ℕ) * Real.log 3) with hX
      have hX3 : 3 ≤ X := by
        rw [hX, h3]; exact le_self_pow₀ (by norm_num) (by omega)
      rw [ea]
      have e27 : Real.exp (3 * ((k + 1 + 1 : ℕ) * Real.log 3)) =
          27 * Real.exp (3 * ((k + 1 : ℕ) * Real.log 3)) := by
        rw [show (3 : ℝ) * ((k + 1 + 1 : ℕ) * Real.log 3) =
            3 * Real.log 3 + 3 * ((k + 1 : ℕ) * Real.log 3) by push_cast; ring, Real.exp_add]
        rw [show (3 : ℝ) * Real.log 3 = ((3 : ℕ) : ℝ) * Real.log 3 by norm_num, h3]; norm_num
      rw [e27]
      have hexp : Real.exp (-(π * (3 * X - 1))) ≤ (1 / 27000) * Real.exp (-(π * (X - 1))) := by
        have e : -(π * (3 * X - 1)) = -(π * (X - 1)) - 2 * π * X := by ring
        rw [e, Real.exp_sub]
        have hbig : (27000 : ℝ) ≤ Real.exp (2 * π * X) := by
          have h6 : (27000 : ℝ) ≤ Real.exp (6 * π) := by
            have h2 : (506.25 : ℝ) ≤ Real.exp (2 * π) := by
              rw [show 2 * π = π + π by ring, Real.exp_add]; nlinarith
            have h4 := mul_le_mul h2 h2 (by norm_num) (Real.exp_pos _).le
            have h6' := mul_le_mul h4 h2 (by norm_num) (by positivity)
            rw [show 6 * π = 2 * π + 2 * π + 2 * π by ring, Real.exp_add, Real.exp_add]
            nlinarith
          calc (27000 : ℝ) ≤ Real.exp (6 * π) := h6
            _ ≤ Real.exp (2 * π * X) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
        rw [div_le_iff₀ (Real.exp_pos _)]
        have := Real.exp_pos (-(π * (X - 1)))
        nlinarith
      have hpos : 0 ≤ 4.0804 * Real.exp (3 * ((k + 1 : ℕ) * Real.log 3)) := by positivity
      calc 4.0804 * (27 * Real.exp (3 * ((k + 1 : ℕ) * Real.log 3))) *
            Real.exp (-(π * (3 * X - 1)))
          ≤ 4.0804 * (27 * Real.exp (3 * ((k + 1 : ℕ) * Real.log 3))) *
            ((1 / 27000) * Real.exp (-(π * (X - 1)))) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (1 / 1000) * (4.0804 * Real.exp (3 * ((k + 1 : ℕ) * Real.log 3)) *
            Real.exp (-(π * (X - 1)))) := by ring
    calc lacunaryDecay ((k + 1 + 1 : ℕ) * Real.log 3)
        ≤ (1 / 1000) * lacunaryDecay ((k + 1 : ℕ) * Real.log 3) := hstep
      _ ≤ (1 / 1000) * (0.2177 * (1 / 1000 : ℝ) ^ k) := by gcongr
      _ = 0.2177 * (1 / 1000 : ℝ) ^ (k + 1) := by ring

/-! ## Lacunary sequences -/

section Lacunary

variable {n : ℕ → ℕ}

theorem lacunary_mul_le (hs : ∀ i, 3 * n i ≤ n (i + 1)) (i k : ℕ) :
    3 ^ k * n i ≤ n (i + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc 3 ^ (k + 1) * n i = 3 * (3 ^ k * n i) := by ring
      _ ≤ 3 * n (i + k) := Nat.mul_le_mul_left 3 ih
      _ ≤ n (i + k + 1) := hs (i + k)
      _ = n (i + (k + 1)) := by rw [Nat.add_assoc]

theorem lacunary_pos (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (i : ℕ) : 3 ≤ n i := by
  have h := lacunary_mul_le hs 0 i
  rw [Nat.zero_add] at h
  calc 3 ≤ 3 ^ i * 3 := by
        have : 1 ≤ 3 ^ i := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
    _ ≤ 3 ^ i * n 0 := Nat.mul_le_mul_left _ h0
    _ ≤ n i := h

theorem log_lacunary_sub_ge (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (i k : ℕ) :
    (k : ℝ) * Real.log 3 ≤ Real.log (n (i + k)) - Real.log (n i) := by
  have hpos : (0 : ℝ) < n i := by exact_mod_cast (show 0 < n i by linarith [lacunary_pos h0 hs i])
  have h := lacunary_mul_le hs i k
  have hR : (3 : ℝ) ^ k * n i ≤ n (i + k) := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow] at hlog
  linarith

theorem log_lacunary_ge (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (i : ℕ) :
    ((i + 1 : ℕ) : ℝ) * Real.log 3 ≤ Real.log (n i) := by
  have h := log_lacunary_sub_ge h0 hs 0 i
  rw [Nat.zero_add] at h
  have h3 : Real.log 3 ≤ Real.log (n 0) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h0)
  push_cast; linarith

theorem lacunary_strictMono (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) : StrictMono n := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  have := lacunary_pos h0 hs i
  have := hs i
  omega

theorem lacunaryDecay_nat_summable :
    Summable fun k : ℕ => lacunaryDecay ((k + 1 : ℕ) * Real.log 3) :=
  Summable.of_nonneg_of_le (fun _ => lacunaryDecay_nonneg _) lacunaryDecay_log_three_le
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 0.2177)

theorem tsum_lacunaryDecay_nat_le :
    ∑' k : ℕ, lacunaryDecay ((k + 1 : ℕ) * Real.log 3) ≤ 0.218 := by
  have hg : Summable fun k : ℕ => (0.2177 : ℝ) * (1 / 1000 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 0.2177
  calc ∑' k : ℕ, lacunaryDecay ((k + 1 : ℕ) * Real.log 3)
      ≤ ∑' k : ℕ, (0.2177 : ℝ) * (1 / 1000 : ℝ) ^ k :=
        lacunaryDecay_nat_summable.tsum_le_tsum lacunaryDecay_log_three_le hg
    _ = 0.2177 * (1 - 1 / 1000)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ ≤ 0.218 := by norm_num

theorem log_three_le_log_lacunary (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (i : ℕ) :
    Real.log 3 ≤ Real.log (n i) :=
  Real.log_le_log (by norm_num) (by exact_mod_cast lacunary_pos h0 hs i)

/-- `Σ_i lacunaryDecay(log n_i) ≤ 0.218`. -/
theorem lacunary_sum_decay_le (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) :
    Summable (fun i => lacunaryDecay (Real.log (n i))) ∧
      ∑' i, lacunaryDecay (Real.log (n i)) ≤ 0.218 := by
  have hle : ∀ i, lacunaryDecay (Real.log (n i)) ≤ lacunaryDecay ((i + 1 : ℕ) * Real.log 3) :=
    fun i => lacunaryDecay_antitone (by positivity) (log_lacunary_ge h0 hs i)
  have hsum := Summable.of_nonneg_of_le (fun _ => lacunaryDecay_nonneg _) hle lacunaryDecay_nat_summable
  exact ⟨hsum, (hsum.tsum_le_tsum hle lacunaryDecay_nat_summable).trans tsum_lacunaryDecay_nat_le⟩

/-- `Σ_i lacunaryDecay(log n_i + log n_j) ≤ 0.001`. -/
theorem lacunary_sum_decay_add_le (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (j : ℕ) :
    Summable (fun i => lacunaryDecay (Real.log (n i) + Real.log (n j))) ∧
      ∑' i, lacunaryDecay (Real.log (n i) + Real.log (n j)) ≤ 0.001 := by
  have hle : ∀ i, lacunaryDecay (Real.log (n i) + Real.log (n j)) ≤ 0.2177 * (1 / 1000 : ℝ) ^ (i + 1) := by
    intro i
    have h1 := log_lacunary_ge h0 hs i
    have h2 := log_three_le_log_lacunary h0 hs j
    have hge : ((i + 1 + 1 : ℕ) : ℝ) * Real.log 3 ≤ Real.log (n i) + Real.log (n j) := by
      push_cast at h1 ⊢; linarith
    exact (lacunaryDecay_antitone (by positivity) hge).trans (lacunaryDecay_log_three_le (i + 1))
  have hg : Summable fun i : ℕ => (0.2177 : ℝ) * (1 / 1000 : ℝ) ^ (i + 1) :=
    ((summable_geometric_of_lt_one (r := (1 / 1000 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (0.2177 * (1 / 1000))).congr fun i => by rw [pow_succ]; ring
  have hsum := Summable.of_nonneg_of_le (fun _ => lacunaryDecay_nonneg _) hle hg
  refine ⟨hsum, (hsum.tsum_le_tsum hle hg).trans ?_⟩
  have e : ∑' i : ℕ, (0.2177 : ℝ) * (1 / 1000 : ℝ) ^ (i + 1) = 0.2177 * (1 / 1000) * (1 - 1 / 1000)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (r := (1 / 1000 : ℝ)) (by norm_num) (by norm_num), ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  rw [e]; norm_num

/-- The shifted-and-reflected majorant of the off-diagonal decay sum. -/
theorem sum_shift_reflect_le {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k) (hgs : Summable g) (j : ℕ) :
    Summable (fun i => (if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0)) ∧
      ∑' i, ((if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0)) ≤
        2 * ∑' k, g k := by
  set F : ℕ → ℝ := fun i => if j < i then g (i - j - 1) else 0 with hF
  set G : ℕ → ℝ := fun i => if i < j then g (j - i - 1) else 0 with hG
  have e : ∀ k, F (k + (j + 1)) = g k := by
    intro k; simp only [hF]; rw [if_pos (by omega)]; congr 1; omega
  have hs' : Summable fun k => F (k + (j + 1)) := hgs.congr fun k => (e k).symm
  have hFs : Summable F := (summable_nat_add_iff (j + 1)).mp hs'
  have hFt : ∑' i, F i = ∑' k, g k := by
    rw [← hFs.sum_add_tsum_nat_add (j + 1)]
    have hz : ∑ i ∈ Finset.range (j + 1), F i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hF]; rw [if_neg (by have := Finset.mem_range.mp hi; omega)]
    rw [hz, zero_add]
    exact tsum_congr e
  have hz : ∀ i ∉ Finset.range j, G i = 0 :=
    fun i hi => by simp only [hG]; rw [if_neg (by simpa using hi)]
  have hGs : Summable G := summable_of_ne_finset_zero hz
  have hGt : ∑' i, G i ≤ ∑' k, g k := by
    rw [tsum_eq_sum hz]
    have e2 : ∑ i ∈ Finset.range j, G i = ∑ i ∈ Finset.range j, g (j - 1 - i) :=
      Finset.sum_congr rfl fun i hi => by
        simp only [hG]; rw [if_pos (Finset.mem_range.mp hi)]; congr 1; omega
    rw [e2, Finset.sum_range_reflect]
    exact hgs.sum_le_tsum _ fun k _ => hg0 k
  refine ⟨hFs.add hGs, ?_⟩
  rw [hFs.tsum_add hGs, hFt]
  linarith

/-- `Σ_{i ≠ j} lacunaryDecay(|log n_i − log n_j|) ≤ 0.436`. -/
theorem lacunary_sum_decay_sub_le (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1)) (j : ℕ) :
    Summable (fun i => if i = j then 0 else lacunaryDecay |Real.log (n i) - Real.log (n j)|) ∧
      ∑' i, (if i = j then 0 else lacunaryDecay |Real.log (n i) - Real.log (n j)|) ≤ 0.436 := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℝ, g = fun k => lacunaryDecay ((k + 1 : ℕ) * Real.log 3) :=
    ⟨_, rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by rw [hgdef]; exact lacunaryDecay_nonneg _
  have hgs : Summable g := by rw [hgdef]; exact lacunaryDecay_nat_summable
  have hgt : ∑' k, g k ≤ 0.218 := by rw [hgdef]; exact tsum_lacunaryDecay_nat_le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hle : ∀ i, (if i = j then 0 else lacunaryDecay |Real.log (n i) - Real.log (n j)|) ≤
      (if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0) := by
    intro i
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_neg hij.ne, if_neg (by omega), if_pos hij, zero_add, hgdef]
      have hd := log_lacunary_sub_ge h0 hs i (j - i)
      rw [show i + (j - i) = j by omega] at hd
      have hk0 : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
      refine lacunaryDecay_antitone (by positivity) ?_
      have : ((j - i - 1 + 1 : ℕ) : ℝ) = ((j - i : ℕ) : ℝ) := by congr 1; omega
      rw [this]; exact hd
    · subst hij; simp
    · rw [if_neg hij.ne', if_pos hij, if_neg (by omega), add_zero, hgdef]
      have hd := log_lacunary_sub_ge h0 hs j (i - j)
      rw [show j + (i - j) = i by omega] at hd
      have hk0 : (0 : ℝ) ≤ ((i - j : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_of_nonneg (by nlinarith)]
      refine lacunaryDecay_antitone (by positivity) ?_
      have : ((i - j - 1 + 1 : ℕ) : ℝ) = ((i - j : ℕ) : ℝ) := by congr 1; omega
      rw [this]; exact hd
  obtain ⟨hhs, hht⟩ := sum_shift_reflect_le hg0 hgs j
  have hnn : ∀ i, 0 ≤ (if i = j then 0 else lacunaryDecay |Real.log (n i) - Real.log (n j)|) :=
    fun i => by split_ifs; exacts [le_rfl, lacunaryDecay_nonneg _]
  have hsum := Summable.of_nonneg_of_le hnn hle hhs
  refine ⟨hsum, (hsum.tsum_le_tsum hle hhs).trans (hht.trans ?_)⟩
  linarith

end Lacunary

/-! ## Lacunary rigidity -/

/-- The normalized deficit `v(m) = (Λ(m) − lam(m))/√m` on `m ≥ 2`. -/
def normDeficit (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m then ((ArithmeticFunction.vonMangoldt m : ℝ) - lam m) / Real.sqrt m else 0

/-- `w_i ≤ w_j (1 + |log n_i − log n_j|)` for the weight `w = 1 + log`. -/
theorem one_add_log_le_mul {a b : ℝ} (hb : 0 ≤ b) :
    1 + a ≤ (1 + b) * (1 + |a - b|) := by
  rcases le_or_gt a b with h | h
  · have : 0 ≤ (1 + b) * |a - b| := by positivity
    nlinarith
  · rw [abs_of_pos (by linarith)]; nlinarith

/-- An off-atom term is dominated by its absolute value. -/
theorem pair_term_le {c ε K1 K2 K3 : ℝ} (hε : |ε| = 1) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2) (h3 : 0 ≤ K3) :
    c * (4 * K1 + 2 * ε * (K2 + K3)) ≤ |c| * (4 * K1 + 2 * K2 + 2 * K3) := by
  have hcε : c * ε ≤ |c| := by
    calc c * ε ≤ |c * ε| := le_abs_self _
      _ = |c| := by rw [abs_mul, hε, mul_one]
  have hc := le_abs_self c
  have hK23 : 0 ≤ K2 + K3 := add_nonneg h2 h3
  have e : c * (4 * K1 + 2 * ε * (K2 + K3)) = 4 * (c * K1) + 2 * ((c * ε) * (K2 + K3)) := by ring
  have e2 : |c| * (4 * K1 + 2 * K2 + 2 * K3) = 4 * (|c| * K1) + 2 * (|c| * (K2 + K3)) := by ring
  rw [e, e2]
  have := mul_le_mul_of_nonneg_right hc h1
  have := mul_le_mul_of_nonneg_right hcε hK23
  linarith

/-- The atom term, after adding back `2|c| K(0)`. -/
theorem pair_atom_le {c ε K1 K2 K0 : ℝ} (hεc : ε * c = -|c|) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2) :
    c * (4 * K1 + 2 * ε * (K2 + K0)) + 2 * |c| * K0 ≤ |c| * (4 * K1 + 2 * K2) := by
  have e : c * (4 * K1 + 2 * ε * (K2 + K0)) + 2 * |c| * K0 =
      4 * (c * K1) + 2 * (ε * c) * K2 + 2 * (ε * c) * K0 + 2 * |c| * K0 := by ring
  rw [e, hεc]
  have := mul_le_mul_of_nonneg_right (le_abs_self c) h1
  have := mul_nonneg (abs_nonneg c) h2
  nlinarith

/-- **The key inequality at one lacunary atom.** -/
theorem lacunary_atom_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {n : ℕ → ℕ} (h0 : 3 ≤ n 0)
    (hs : ∀ i, 3 * n i ≤ n (i + 1))
    (hsupp : ∀ m, 2 ≤ m → m ∉ Set.range n → lam m = ArithmeticFunction.vonMangoldt m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, |normDeficit lam (n i)| ≤ M * (1 + Real.log (n i))) (j : ℕ) :
    2 * |normDeficit lam (n j)| * riemannAutocorr 0 ≤
      M * (1 + Real.log (n j)) * (1.746 * riemannAutocorr 0) := by
  have hK0 := riemannAutocorr_zero_pos
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = normDeficit lam := ⟨_, rfl⟩
  rw [← hvdef] at hM ⊢
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.log (n j) := ⟨_, rfl⟩
  rw [← hc₀]
  have hlog3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hc₀3 : Real.log 3 ≤ c₀ := hc₀ ▸ log_three_le_log_lacunary h0 hs j
  have hc₀0 : 0 ≤ c₀ := le_trans (Real.log_nonneg (by norm_num)) hc₀3
  obtain ⟨wj, hwj⟩ : ∃ wj : ℝ, wj = 1 + c₀ := ⟨_, rfl⟩
  rw [← hwj]
  have hwj1 : 1 ≤ wj := by rw [hwj]; linarith
  have hinj : Function.Injective n := (lacunary_strictMono h0 hs).injective
  obtain ⟨hS1, hS1t⟩ := lacunary_sum_decay_le h0 hs
  obtain ⟨hS3, hS3t⟩ := lacunary_sum_decay_add_le h0 hs j
  obtain ⟨hS2, hS2t⟩ := lacunary_sum_decay_sub_le h0 hs j
  rw [← hc₀] at hS3 hS3t hS2 hS2t
  -- the majorant `β`
  set P : ℝ := M * wj * riemannAutocorr 0 with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun i => P * (4 * lacunaryDecay (Real.log (n i)) +
      2 * lacunaryDecay (Real.log (n i) + c₀) +
      2 * (if i = j then 0 else lacunaryDecay |Real.log (n i) - c₀|)) := ⟨_, rfl⟩
  have hβs : Summable β := by
    rw [hβ]; exact (((hS1.mul_left 4).add (hS3.mul_left 2)).add (hS2.mul_left 2)).mul_left _
  have hβt : ∑' i, β i ≤ P * 1.746 := by
    rw [hβ, tsum_mul_left, Summable.tsum_add ((hS1.mul_left 4).add (hS3.mul_left 2)) (hS2.mul_left 2),
      Summable.tsum_add (hS1.mul_left 4) (hS3.mul_left 2), tsum_mul_left, tsum_mul_left, tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ hP0
    linarith
  -- weighted decay bounds
  have hwK : ∀ i (D : ℝ), Real.log 2 ≤ D → (1 + Real.log (n i)) ≤ wj * (1 + D) →
      M * (1 + Real.log (n i)) * riemannAutocorr D ≤ P * lacunaryDecay D := by
    intro i D hD hw
    have h := one_add_mul_riemannAutocorr_le hD
    have hKD := riemannAutocorr_nonneg D
    have hw0 : 0 ≤ 1 + Real.log (n i) := by
      have := Real.log_natCast_nonneg (n i); linarith
    calc M * (1 + Real.log (n i)) * riemannAutocorr D
        ≤ M * (wj * (1 + D)) * riemannAutocorr D := by gcongr
      _ = M * wj * ((1 + D) * riemannAutocorr D) := by ring
      _ ≤ M * wj * (lacunaryDecay D * riemannAutocorr 0) := by gcongr
      _ = P * lacunaryDecay D := by rw [hP]; ring
  have hlogi : ∀ i, Real.log 3 ≤ Real.log (n i) := fun i => log_three_le_log_lacunary h0 hs i
  have hw1 : ∀ i, (1 + Real.log (n i)) ≤ wj * (1 + Real.log (n i)) := fun i =>
    le_mul_of_one_le_left (by have := hlogi i; have := Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num); linarith) hwj1
  have hw2 : ∀ i, (1 + Real.log (n i)) ≤ wj * (1 + (Real.log (n i) + c₀)) := fun i => by
    have h := hw1 i
    have : wj * (1 + Real.log (n i)) ≤ wj * (1 + (Real.log (n i) + c₀)) := by gcongr; linarith
    linarith
  have hw3 : ∀ i, (1 + Real.log (n i)) ≤ wj * (1 + |Real.log (n i) - c₀|) := fun i => by
    rw [hwj]; exact one_add_log_le_mul hc₀0
  have hD3 : ∀ i, i ≠ j → Real.log 3 ≤ |Real.log (n i) - c₀| := by
    intro i hij
    have hl := Real.log_pos (show (1:ℝ) < 3 by norm_num)
    rcases lt_or_gt_of_ne hij with h | h
    · have hd := log_lacunary_sub_ge h0 hs i (j - i)
      rw [show i + (j - i) = j by omega, ← hc₀] at hd
      have : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j - i by omega)
      rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]; nlinarith
    · have hd := log_lacunary_sub_ge h0 hs j (i - j)
      rw [show j + (i - j) = i by omega, ← hc₀] at hd
      have : (1 : ℝ) ≤ ((i - j : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ i - j by omega)
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
  -- the limit over truncations
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨L₁, hL₁⟩ := exists_truncatedRiemannAutocorr_zero_ge
    (η := δ / (4 * (|v (n j)| + 1))) (by positivity)
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (1 + 1 * Real.exp (c₀ / 2)) ^ 2 := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨L₂, hL₂⟩ := exists_nearRadicalEnergy_le (ε := δ / (2 * (Q + 1))) (by positivity)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max L₁ L₂ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = if 0 ≤ v (n j) then -1 else 1 := ⟨_, rfl⟩
  have hεabs : |ε| = 1 := by rw [hε]; split_ifs <;> norm_num
  have hε2 : ε ^ 2 = 1 := by rw [hε]; split_ifs <;> norm_num
  have hεv : ε * v (n j) = -|v (n j)| := by
    rw [hε]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hfd : ContDiff ℝ 2 (pairRiemannKernel L c₀ ε) := contDiff_pairRiemannKernel L c₀ ε
  have hfc : HasCompactSupport (pairRiemannKernel L c₀ ε) := hasCompactSupport_pairRiemannKernel L c₀ ε
  have hWL : ‖zetaZeroConfig.W (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε)‖ ≤ δ / 2 := by
    have h1 := norm_W_pairRiemannKernel_le L hc₀0 ε hΛ'
    rw [hεabs, ← hQ] at h1
    have h2 := hL₂ L (by rw [hL]; exact le_max_right _ _)
    calc _ ≤ Q * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := h1
      _ ≤ Q * (δ / (2 * (Q + 1))) := mul_le_mul_of_nonneg_left h2 hQ0
      _ ≤ δ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hKL0 := hL₁ L (by rw [hL]; exact le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℂ, k = EF.weilTest (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε) :=
    ⟨_, rfl⟩
  have hkc : HasCompactSupport k := hk ▸ EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨KL, hKL⟩ : ∃ KL : ℝ → ℝ, KL = truncatedRiemannAutocorr L := ⟨_, rfl⟩
  have hKLle : ∀ y, KL y ≤ riemannAutocorr y := fun y => hKL ▸ truncatedRiemannAutocorr_le_riemannAutocorr L y
  have hKLnn : ∀ y, 0 ≤ KL y := fun y => hKL ▸ truncatedRiemannAutocorr_nonneg L y
  have hKLneg : ∀ y, KL (-y) = KL y := fun y => hKL ▸ truncatedRiemannAutocorr_neg L y
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun m : ℕ =>
      4 * KL (Real.log (m : ℝ)) + 2 * ε * (KL (Real.log (m : ℝ) + c₀) + KL (Real.log (m : ℝ) - c₀)) :=
    ⟨_, rfl⟩
  have hkT : ∀ m : ℕ, k (Real.log m) + k (-Real.log m) = ((T m : ℝ) : ℂ) := by
    intro m
    rw [hk, weilTest_pairRiemannKernel, weilTest_pairRiemannKernel, hε2, ← hKL, hT]
    have e1 := hKLneg (Real.log m)
    have e2 : KL (-Real.log m + c₀) = KL (Real.log m - c₀) := by
      rw [show -Real.log m + c₀ = -(Real.log m - c₀) by ring]; exact hKLneg _
    have e3 : KL (-Real.log m - c₀) = KL (Real.log m + c₀) := by
      rw [show -Real.log m - c₀ = -(Real.log m + c₀) by ring]; exact hKLneg _
    simp only
    rw [e1, e2, e3]; push_cast; ring
  -- positivity
  have hpos := hW _ hfd hfc
  rw [← hk, weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt, hk,
    ← zeta_W_eq_weilFullFunctional hfd hfc, ← hk] at hpos
  set a : ℕ → ℝ := fun m => if 2 ≤ m then
      (lam m - ArithmeticFunction.vonMangoldt m) / Real.sqrt m else 0 with ha
  have hav : ∀ m, a m = -v m := by
    intro m; rw [hvdef]; simp only [ha, normDeficit]; split_ifs <;> ring
  have hsum := summable_primeAtoms a hkc
  rw [Complex.sub_re, Complex.re_tsum hsum] at hpos
  have hre : ∀ m : ℕ, (((a m : ℝ) : ℂ) * (k (Real.log m) + k (-Real.log m))).re = -(v m * T m) := by
    intro m; rw [hkT, ← Complex.ofReal_mul, Complex.ofReal_re, hav]; ring
  obtain ⟨N₁, hN₁⟩ := exists_forall_log_eq_zero hkc
  have hTz : ∀ m, N₁ ≤ m → T m = 0 := by
    intro m hm
    obtain ⟨h1, h2⟩ := hN₁ m hm
    have := hkT m
    rw [h1, h2, add_zero] at this
    exact_mod_cast this.symm
  have hvz : ∀ m, m ∉ Set.range n → v m = 0 := by
    intro m hm
    rw [hvdef]; simp only [normDeficit]
    split_ifs with h2
    · rw [hsupp m h2 hm, sub_self, zero_div]
    · rfl
  have hsupport : Function.support (fun m => v m * T m) ⊆ Set.range n := by
    intro m hm
    by_contra hc
    exact hm (by simp only; rw [hvz m hc, zero_mul])
  have hreindex : ∑' i, v (n i) * T (n i) = ∑' m, v m * T m :=
    hinj.tsum_eq (f := fun m => v m * T m) hsupport
  have hni : ∀ i, i ≤ n i := fun i => by
    have h1 := lacunary_mul_le hs 0 i
    rw [Nat.zero_add] at h1
    have h3 : i < 3 ^ i := Nat.lt_pow_self (by norm_num)
    have := lacunary_pos h0 hs 0
    nlinarith
  have hsumT : Summable fun i => v (n i) * T (n i) :=
    summable_of_ne_finset_zero (s := Finset.range N₁) fun i hi => by
      rw [Finset.mem_range, not_lt] at hi
      rw [hTz (n i) (le_trans hi (hni i)), mul_zero]
  have hmain : -(δ / 2) ≤ ∑' i, v (n i) * T (n i) := by
    rw [hreindex]
    have e : (∑' m : ℕ, (((a m : ℝ) : ℂ) * (k (Real.log m) + k (-Real.log m))).re) =
        -∑' m, v m * T m := by rw [← tsum_neg]; exact tsum_congr hre
    rw [e] at hpos
    have := Complex.re_le_norm (zetaZeroConfig.W (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε))
    linarith
  -- add back the atom and majorize termwise
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun i => if i = j then 2 * |v (n j)| * KL 0 else (0 : ℝ) :=
    ⟨_, rfl⟩
  have hAs : Summable A := by
    rw [hA]; exact summable_of_ne_finset_zero (s := {j}) fun i hi => by
      rw [Finset.mem_singleton] at hi; rw [if_neg hi]
  have hAt : ∑' i, A i = 2 * |v (n j)| * KL 0 := by rw [hA, tsum_ite_eq]
  have hle : ∀ i, v (n i) * T (n i) + A i ≤ β i := by
    intro i
    have hMi := hM i
    have hvi := abs_nonneg (v (n i))
    have hb1 : |v (n i)| * (4 * KL (Real.log (n i))) ≤ P * (4 * lacunaryDecay (Real.log (n i))) := by
      have h := hwK i (Real.log (n i)) (le_trans hlog3 (hlogi i)) (hw1 i)
      have h2 := mul_le_mul hMi (hKLle (Real.log (n i))) (hKLnn _) (by
        have := Real.log_natCast_nonneg (n i); positivity)
      calc |v (n i)| * (4 * KL (Real.log (n i))) = 4 * (|v (n i)| * KL (Real.log (n i))) := by ring
        _ ≤ 4 * (M * (1 + Real.log (n i)) * riemannAutocorr (Real.log (n i))) := by linarith
        _ ≤ 4 * (P * lacunaryDecay (Real.log (n i))) := by linarith
        _ = P * (4 * lacunaryDecay (Real.log (n i))) := by ring
    have hb2 : |v (n i)| * (2 * KL (Real.log (n i) + c₀)) ≤ P * (2 * lacunaryDecay (Real.log (n i) + c₀)) := by
      have h := hwK i (Real.log (n i) + c₀) (by linarith [hlogi i]) (hw2 i)
      have h2 := mul_le_mul hMi (hKLle (Real.log (n i) + c₀)) (hKLnn _) (by
        have := Real.log_natCast_nonneg (n i); positivity)
      calc |v (n i)| * (2 * KL (Real.log (n i) + c₀)) = 2 * (|v (n i)| * KL (Real.log (n i) + c₀)) := by
            ring
        _ ≤ 2 * (M * (1 + Real.log (n i)) * riemannAutocorr (Real.log (n i) + c₀)) := by linarith
        _ ≤ 2 * (P * lacunaryDecay (Real.log (n i) + c₀)) := by linarith
        _ = P * (2 * lacunaryDecay (Real.log (n i) + c₀)) := by ring
    have hTi : T (n i) = 4 * KL (Real.log (n i)) +
        2 * ε * (KL (Real.log (n i) + c₀) + KL (Real.log (n i) - c₀)) := by rw [hT]
    have hβi : β i = P * (4 * lacunaryDecay (Real.log (n i)) +
        2 * lacunaryDecay (Real.log (n i) + c₀) +
        2 * (if i = j then 0 else lacunaryDecay |Real.log (n i) - c₀|)) := by rw [hβ]
    have hAi : A i = if i = j then 2 * |v (n j)| * KL 0 else 0 := by rw [hA]
    rw [hTi, hβi, hAi]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl, ← hc₀, sub_self]
      have hat := pair_atom_le (c := v (n i)) (ε := ε) (K1 := KL c₀)
        (K2 := KL (c₀ + c₀)) (K0 := KL 0) hεv (hKLnn _) (hKLnn _)
      rw [← hc₀] at hb1 hb2
      have hd0 : (0 : ℝ) ≤ P * 2 * 0 := by simp
      linarith
    · rw [if_neg hij, if_neg hij, add_zero]
      have hD := hD3 i hij
      have hKabs : KL (Real.log (n i) - c₀) = KL |Real.log (n i) - c₀| := by
        rcases le_or_gt 0 (Real.log (n i) - c₀) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h, hKLneg]
      rw [hKabs]
      have ht := pair_term_le (c := v (n i)) (K1 := KL (Real.log (n i))) (K2 := KL (Real.log (n i) + c₀))
        (K3 := KL |Real.log (n i) - c₀|) hεabs (hKLnn _) (hKLnn _) (hKLnn _)
      have hb3 : |v (n i)| * (2 * KL |Real.log (n i) - c₀|) ≤
          P * (2 * lacunaryDecay |Real.log (n i) - c₀|) := by
        have h := hwK i |Real.log (n i) - c₀| (le_trans hlog3 hD) (hw3 i)
        have h2 := mul_le_mul hMi (hKLle |Real.log (n i) - c₀|) (hKLnn _) (by
          have := Real.log_natCast_nonneg (n i); positivity)
        calc |v (n i)| * (2 * KL |Real.log (n i) - c₀|) = 2 * (|v (n i)| * KL |Real.log (n i) - c₀|) := by
              ring
          _ ≤ 2 * (M * (1 + Real.log (n i)) * riemannAutocorr |Real.log (n i) - c₀|) := by linarith
          _ ≤ 2 * (P * lacunaryDecay |Real.log (n i) - c₀|) := by linarith
          _ = P * (2 * lacunaryDecay |Real.log (n i) - c₀|) := by ring
      have e : |v (n i)| * (4 * KL (Real.log (n i)) + 2 * KL (Real.log (n i) + c₀) +
          2 * KL |Real.log (n i) - c₀|) = |v (n i)| * (4 * KL (Real.log (n i))) +
          |v (n i)| * (2 * KL (Real.log (n i) + c₀)) + |v (n i)| * (2 * KL |Real.log (n i) - c₀|) := by
        ring
      have e2 : P * (4 * lacunaryDecay (Real.log (n i)) + 2 * lacunaryDecay (Real.log (n i) + c₀) +
          2 * lacunaryDecay |Real.log (n i) - c₀|) = P * (4 * lacunaryDecay (Real.log (n i))) +
          P * (2 * lacunaryDecay (Real.log (n i) + c₀)) + P * (2 * lacunaryDecay |Real.log (n i) - c₀|) := by
        ring
      linarith
  have hsum2 : ∑' i, (v (n i) * T (n i) + A i) ≤ ∑' i, β i :=
    (hsumT.add hAs).tsum_le_tsum hle hβs
  rw [hsumT.tsum_add hAs, hAt] at hsum2
  -- assemble
  have hcorr : 2 * |v (n j)| * (δ / (4 * (|v (n j)| + 1))) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := abs_nonneg (v (n j)); nlinarith
  have hKL0' : riemannAutocorr 0 - δ / (4 * (|v (n j)| + 1)) ≤ KL 0 := by rw [hKL]; exact hKL0
  have hv0 := abs_nonneg (v (n j))
  have hmul : 2 * |v (n j)| * (riemannAutocorr 0 - δ / (4 * (|v (n j)| + 1))) ≤ 2 * |v (n j)| * KL 0 :=
    mul_le_mul_of_nonneg_left hKL0' (by positivity)
  have hPe : P * 1.746 = M * wj * (1.746 * riemannAutocorr 0) := by rw [hP]; ring
  linarith

/-- **Lacunary rigidity.** If `lam` is Weil-positive with the pole term and agrees with `Λ` off a
lacunary set `n_0 < n_1 < …` with `n_0 ≥ 3` and `n_{i+1} ≥ 3 n_i`, then `lam = Λ`. The values of `lam`
on the set are arbitrary a priori; no sign, size or summability condition is assumed. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_lacunary {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {n : ℕ → ℕ} (h0 : 3 ≤ n 0) (hs : ∀ i, 3 * n i ≤ n (i + 1))
    (hsupp : ∀ m, 2 ≤ m → m ∉ Set.range n → lam m = ArithmeticFunction.vonMangoldt m) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  obtain ⟨C₀, hC₀⟩ := abs_le_of_weilPositive (weilPositive_of_weilPositiveFull hW)
  set B : ℝ := 2 + |C₀| with hB
  have hw : ∀ i, 0 < 1 + Real.log (n i) := fun i => by
    have := Real.log_natCast_nonneg (n i); linarith
  have hbox : ∀ i, |normDeficit lam (n i)| ≤ B * (1 + Real.log (n i)) := by
    intro i
    have hn2 : 2 ≤ n i := by have := lacunary_pos h0 hs i; omega
    have hsq1 : 1 ≤ Real.sqrt (n i) := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ n i)
    have hsq0 : 0 < Real.sqrt (n i) := by linarith
    have hlog0 := Real.log_natCast_nonneg (n i)
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n i)
    have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt (n i) := ArithmeticFunction.vonMangoldt_nonneg
    have hl := hC₀ (n i) hn2
    simp only [normDeficit, if_pos hn2]
    rw [abs_div, abs_of_pos hsq0, div_le_iff₀ hsq0]
    have h1 : |(ArithmeticFunction.vonMangoldt (n i) : ℝ) - lam (n i)| ≤
        Real.log (n i) + Real.sqrt (n i) * (Real.log (n i) + C₀) := by
      calc _ ≤ |(ArithmeticFunction.vonMangoldt (n i) : ℝ)| + |lam (n i)| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hΛ0]; linarith
    have h2 : Real.log (n i) ≤ Real.log (n i) * Real.sqrt (n i) := le_mul_of_one_le_right hlog0 hsq1
    have h3 : C₀ ≤ |C₀| := le_abs_self C₀
    have h4 : Real.sqrt (n i) * C₀ ≤ Real.sqrt (n i) * |C₀| := mul_le_mul_of_nonneg_left h3 hsq0.le
    have h5 : 0 ≤ Real.sqrt (n i) * |C₀| * Real.log (n i) := by positivity
    nlinarith
  set r : ℕ → ℝ := fun i => |normDeficit lam (n i)| / (1 + Real.log (n i)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (hw i).le
  have hrB : ∀ i, r i ≤ B := fun i => by
    simp only [hr]; rw [div_le_iff₀ (hw i)]; exact hbox i
  have hbdd : BddAbove (Set.range r) := ⟨B, by rintro _ ⟨i, rfl⟩; exact hrB i⟩
  set M := ⨆ i, r i with hMdef
  have hM0 : 0 ≤ M := le_trans (hr0 0) (le_ciSup hbdd 0)
  have hM : ∀ i, |normDeficit lam (n i)| ≤ M * (1 + Real.log (n i)) := fun i => by
    have := le_ciSup hbdd i
    simp only [hr] at this
    rwa [div_le_iff₀ (hw i)] at this
  have hK0 := riemannAutocorr_zero_pos
  have hrle : ∀ j, r j ≤ 0.873 * M := by
    intro j
    have h := lacunary_atom_le hW h0 hs hsupp hM0 hM j
    simp only [hr]
    rw [div_le_iff₀ (hw j)]
    have e : M * (1 + Real.log (n j)) * (1.746 * riemannAutocorr 0) =
        (2 * (0.873 * M * (1 + Real.log (n j)))) * riemannAutocorr 0 := by ring
    rw [e, mul_assoc 2] at h
    have := le_of_mul_le_mul_right (by linarith : 2 * |normDeficit lam (n j)| * riemannAutocorr 0 ≤
      2 * (0.873 * M * (1 + Real.log (n j))) * riemannAutocorr 0) hK0
    linarith
  have hMle : M ≤ 0.873 * M := ciSup_le hrle
  have hMz : M = 0 := by linarith
  intro m hm
  by_cases hmr : m ∈ Set.range n
  · obtain ⟨j, rfl⟩ := hmr
    have h := hM j
    rw [hMz, zero_mul] at h
    have hv : normDeficit lam (n j) = 0 := abs_nonpos_iff.mp h
    simp only [normDeficit, if_pos hm] at hv
    have hsq : Real.sqrt (n j) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n j))).ne'
    rw [div_eq_zero_iff, sub_eq_zero] at hv
    rcases hv with hv | hv
    · exact hv.symm
    · exact absurd hv hsq
  · exact hsupp m hm hmr

/-- **Prime-power lines are rigid.** For an integer `p ≥ 3`, a Weil-positive system that agrees
with `Λ` except at the powers `p^k` (`k ≥ 1`) is `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_powers {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : 3 ≤ p)
    (hsupp : ∀ m, 2 ≤ m → (∀ k, 1 ≤ k → m ≠ p ^ k) → lam m = ArithmeticFunction.vonMangoldt m) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_lacunary hW (n := fun i => p ^ (i + 1))
    (by simpa using hp) (fun i => ?_) (fun m hm hmr => hsupp m hm fun k hk hmk => ?_)
  · show 3 * p ^ (i + 1) ≤ p ^ (i + 1 + 1)
    rw [pow_succ p (i + 1), mul_comm]; exact Nat.mul_le_mul_left _ hp
  · exact hmr ⟨k - 1, by show p ^ (k - 1 + 1) = m; rw [Nat.sub_add_cancel hk, hmk]⟩

end

end RHTower
