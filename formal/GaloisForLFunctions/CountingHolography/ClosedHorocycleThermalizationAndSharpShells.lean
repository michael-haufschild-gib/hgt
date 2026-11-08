import GaloisForLFunctions.CountingHolography.ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip
import GaloisForLFunctions.CountingHolography.TheRateOfASharpShell
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainVKAbsorption
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.FiniteMellinShift
import GaloisForLFunctions.RHTower.XiRightDiscAdjointSeamSupremum
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.MertensPowerBoundsControlMobiusHarmonicSums

/-!
# Closed horocycle thermalization, zero-free strips, and sharp shells

Let `A_ψ(y) = ∫₀¹ F_ψ(x + iy) dx` be the mean of a pseudo-Eisenstein observable along the closed
horocycle of height `y ≤ 1`. Together with `zeroFreeStrip_iff_fareyCount_rate`, this module
establishes the complete unconditional rate structure of smooth profiles and sharp horoball shells:

1. **Unconditional `y^{3/4}` ceiling (`δ ≤ 1/4`)** (`not_horocycle_rate_gt_three_quarters`,
   `not_fareyCount_rate_gt_three_quarters`, `not_horocycle_power_saving_gt_quarter`,
   `not_single_shell_rate_gt_three_quarters`): Hardy's critical-line zero of `ξ` rules out any
   uniform power rate `O(y^α)` with `α > 3/4` (`δ > 1/4`) both for smooth profiles and for any
   single sharp shell `1 < a < b`.
2. **Unconditional super-square-root thermalization for smooth profiles**
   (`horocycle_rate_stretched_exp`, `fareyCount_rate_stretched_exp`, `horocycle_rate_sqrt_exact`,
   `horocycle_rate_log_pow`, `horocycle_div_sqrt_tendsto_zero`): shifting the regularized Mellin
   inversion contour into the shrinking Vinogradov–Korobov zero-free rectangle gives the
   unconditional stretched-exponential saving
     `‖A_φ(y) - (6/π) φ̃(-1)‖ ≤ C · y^{1/2} · exp(-√(-log y))`
   on `(0, 1]`, hence exact `O(y^{1/2})`, every logarithmic power `O(y^{1/2} (-log y)^{-A})`, and
   `o(y^{1/2})` as `y → 0⁺`.
3. **Unconditional log-free `O(y^{1/2})` rate for sharp shells** (`abs_circleRemainder_le_sqrt`,
   `abs_horoballSum_sub_le_linear`, `shell_rate_sqrt`): algebraic concavity bounds the quarter-disc
   lattice remainder by `|E(Y)| ≤ 8 √Y`; combined with `|∑_{d ≤ X} μ(d)/d| ≤ 1`, this removes the
   logarithmic loss in `shell_rate` and proves `|H(X) - 3/(2π) X²| ≤ 19 X` and
   `‖A_{shell(a,b)}(y) - (6/π)(1/a - 1/b)‖ ≤ 76 (√(y/a) + √(y/b))`.
4. **Single-shell converse and exact RH × Möbius-circle characterization**
   (`re_le_of_single_shell_rate`, `horoball_rh_rate_iff_rh_and_moebius_circle`,
   `single_shell_rh_rate_iff_rh_and_moebius_circle`): left-shifted continuous trapezoidal
   approximants pass the horocycle Mellin identity to a single indicator `1_{[a, b)}`, whose Mellin
   transform `(a^{-s} - b^{-s})/s` never vanishes on `Re s > 0`. Under `RiemannHypothesis`, both
   Möbius main-term remainders in `horoballSum_decomposition` collapse to `O_ε(X^{1/2 + ε})`,
   isolating `∑_{d ≤ X} μ(d) E(X/d)` as the exact arithmetic obstruction to the RH rate for sharp
   shells.
-/

set_option autoImplicit false

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open BlackHoleRingdown HTGeometry
open GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-! ### 1. The unconditional `y^{3/4}` barrier (`δ ≤ 1/4`) -/

/-- Riemann's `ζ` has a nontrivial zero on the critical line `Re s = 1/2` (Hardy's theorem). -/
theorem exists_zeta_zero_on_critical_line :
    ∃ ρ₀ : ℂ, ρ₀.re = 1 / 2 ∧ riemannZeta ρ₀ = 0 := by
  obtain ⟨ρ₀, hre, hxi⟩ := _root_.RHTower.XiSeamSupremum.exists_xi_zero_on_line
  exact ⟨ρ₀, hre, (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1⟩

/-- **No smooth horocycle rate exceeds `y^{3/4}`.** -/
theorem not_horocycle_rate_gt_three_quarters {α : ℝ} (hα : 3 / 4 < α) :
    ¬(∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α) := by
  intro h
  obtain ⟨ρ₀, hre, hζ⟩ := exists_zeta_zero_on_critical_line
  have hbound := re_le_of_horocycle_rate h hζ (by linarith)
  linarith

/-- **No smoothed Farey count rate exceeds `y^{3/4}`.** -/
theorem not_fareyCount_rate_gt_three_quarters {α : ℝ} (hα : 3 / 4 < α) :
    ¬(∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖fareyCount (fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α) := by
  intro h
  exact not_horocycle_rate_gt_three_quarters hα ((horocycle_rate_iff_fareyCount_rate α).mpr h)

/-- **Power-saving ceiling `δ ≤ 1/4`.** No power gain `y^{1/2 + δ}` with `δ > 1/4` holds across
smooth compactly supported profiles above height `1`. -/
theorem not_horocycle_power_saving_gt_quarter {δ : ℝ} (hδ : 1 / 4 < δ) :
    ¬(∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ (1 / 2 + δ)) :=
  not_horocycle_rate_gt_three_quarters (by linarith)

/-! ### 2. Unconditional super-square-root thermalization for smooth profiles -/

/-- On the closed half-plane `1 ≤ Re z ≤ d`, `|Im z| ≥ 2`, `1/ζ(z)` grows at most polynomially
(`O(|Im z|^{14})`), combining Euler-region boundedness on `Re z ≥ 2`, the Vinogradov–Korobov bound
on `1 ≤ Re z ≤ 2` at large height, and compactness at bounded height. -/
private theorem invZeta_poly_ge_one (d : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ d → 2 ≤ |z.im| →
      ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
  obtain ⟨Cζ, δ, T₀, hCζ, hδ, hT₀, hTexp, _, hinv⟩ :=
    _root_.RHTower.Sieve.exists_bound_invZeta_vk_uniform
  obtain ⟨S₁, hS₁_cost⟩ := Filter.eventually_atTop.mp eventually_narainVKCost_le_log_power
  set S : ℝ := max T₀ (max S₁ 3)
  have hS3 : 3 ≤ S := le_trans (le_max_right S₁ 3) (le_max_right T₀ _)
  have hST₀ : T₀ ≤ S := le_max_left _ _
  have hSS₁ : S₁ ≤ S := le_trans (le_max_left S₁ 3) (le_max_right T₀ _)
  set box : Set ℂ := (Icc (1 : ℝ) 2 ×ℂ Icc (-S) S) ∩ {z : ℂ | 2 ≤ |z.im|}
  have hbox : IsCompact box :=
    ((isCompact_Icc.reProdIm isCompact_Icc)).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hne1 : ∀ z : ℂ, 2 ≤ |z.im| → z ≠ 1 := fun z hzt h1 => by
    rw [h1, Complex.one_im, abs_zero] at hzt
    linarith
  have hcont : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) box := by
    intro z hz
    have hz0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.1.1.1
    exact ((differentiableAt_riemannZeta (hne1 z hz.2)).continuousAt.inv₀ hz0).continuousWithinAt
  obtain ⟨M, hM⟩ := hbox.exists_bound_of_continuousOn hcont
  set K : ℝ := max (max M 2) (Cζ * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ))
  have hK2 : 2 ≤ K := le_trans (le_max_right M 2) (le_max_left _ _)
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K, 14, hK0, fun z hz1 _ hzt => ?_⟩
  have hpow1 : (1 : ℝ) ≤ |z.im| ^ (14 : ℕ) := one_le_pow₀ (by linarith)
  rcases le_or_gt 2 z.re with hz2 | hz2
  · have hb := _root_.RHTower.norm_inv_riemannZeta_le_of_le_re (by norm_num : (1 : ℝ) < 2) hz2
    have hb2 : ‖(riemannZeta z)⁻¹‖ ≤ 2 := hb.trans_eq (by norm_num)
    calc ‖(riemannZeta z)⁻¹‖ ≤ 2 := hb2
      _ ≤ K * 1 := by linarith
      _ ≤ K * |z.im| ^ (14 : ℕ) := mul_le_mul_of_nonneg_left hpow1 hK0
  · rcases le_or_gt |z.im| S with hsmall | hbig
    · have hmem : z ∈ box :=
        ⟨⟨⟨hz1, hz2.le⟩, ⟨by linarith [neg_abs_le z.im], le_trans (le_abs_self _) hsmall⟩⟩, hzt⟩
      have hMK : M ≤ K := le_trans (le_max_left M 2) (le_max_left _ _)
      calc ‖(riemannZeta z)⁻¹‖ ≤ M := hM z hmem
        _ ≤ K * 1 := by linarith
        _ ≤ K * |z.im| ^ (14 : ℕ) := mul_le_mul_of_nonneg_left hpow1 hK0
    · set T : ℝ := |z.im|
      have hT3 : 3 ≤ T := le_trans hS3 hbig.le
      have hTT₀ : T₀ ≤ 2 * T := by linarith [le_trans hST₀ hbig.le]
      have hexp1 : Real.exp (Real.exp 1) ≤ 2 * T + 1 := by
        have he : Real.exp (Real.exp 1) ≤ Real.exp (Real.exp 30) :=
          Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))
        linarith [he, hTexp, hTT₀, hT3]
      have hw0 : 0 < _root_.RHTower.vkHadamardWidth (2 * T + 1) :=
        _root_.RHTower.vkHadamardWidth_pos hexp1
      have hlo : 1 - min δ (_root_.RHTower.vkHadamardWidth (2 * T + 1)) / 4 ≤ z.re := by
        have hm : 0 ≤ min δ (_root_.RHTower.vkHadamardWidth (2 * T + 1)) / 4 :=
          div_nonneg (le_min hδ.le hw0.le) (by norm_num)
        linarith
      have hζ := hinv z (2 * T) hTT₀ (by linarith) hlo hz2.le
      rw [_root_.RHTower.Sieve.invZeta_eq_inv (hne1 z hzt)] at hζ
      have hcost : narainVKCost T ≤ 3 ^ (7 : ℕ) * Real.log (2 * T + 1) ^ (14 : ℕ) :=
        hS₁_cost T (le_trans hSS₁ hbig.le)
      have hlog : Real.log (2 * T + 1) ≤ 2 * T := by
        have h1 := log_double_add_one_le hT3
        have h2 := Real.log_le_sub_one_of_pos (by linarith : 0 < T)
        linarith
      have hlog0 : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
      have hpow : Real.log (2 * T + 1) ^ (14 : ℕ) ≤ 2 ^ (14 : ℕ) * T ^ (14 : ℕ) := by
        calc Real.log (2 * T + 1) ^ (14 : ℕ) ≤ (2 * T) ^ (14 : ℕ) :=
              pow_le_pow_left₀ hlog0 hlog 14
          _ = 2 ^ (14 : ℕ) * T ^ (14 : ℕ) := mul_pow 2 T 14
      have hCK : Cζ * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ) ≤ K := le_max_right _ _
      calc ‖(riemannZeta z)⁻¹‖
          ≤ Cζ * narainVKCost T := by simpa only [narainVKCost, mul_assoc] using hζ
        _ ≤ Cζ * (3 ^ (7 : ℕ) * (2 ^ (14 : ℕ) * T ^ (14 : ℕ))) :=
            mul_le_mul_of_nonneg_left (hcost.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
              hCζ.le
        _ = (Cζ * 3 ^ (7 : ℕ) * 2 ^ (14 : ℕ)) * |z.im| ^ (14 : ℕ) := by ring
        _ ≤ K * |z.im| ^ (14 : ℕ) := mul_le_mul_of_nonneg_right hCK (by positivity)

/-- Pointwise holomorphy of `regularPart ψ` wherever `w.re > -3/4` and `ξ(2(w + 1)) ≠ 0`. -/
private theorem differentiableAt_regularPart_of_xi_ne_zero {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : IsTest ψ a b) {w : ℂ} (hw : -3 / 4 < w.re)
    (hxi : _root_.RHTower.xi (2 * (w + 1)) ≠ 0) :
    DifferentiableAt ℂ (regularPart ψ) w := by
  set U : Set ℂ := {s : ℂ | 1 / 4 < s.re ∧ _root_.RHTower.xi (2 * s) ≠ 0}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_ne_fun
        (_root_.RHTower.xi_differentiable.continuous.comp (continuous_const.mul continuous_id))
        continuous_const)
  have h1U : (1 : ℂ) ∈ U :=
    ⟨by norm_num, by simpa using _root_.RHTower.xi_ne_zero_of_one_le_re (ρ := 2) (by norm_num)⟩
  have hd_num : DifferentiableOn ℂ (poleNumerator ψ) U := by
    intro s hs
    have hΓ : DifferentiableAt ℂ Complex.Gamma s := by
      refine Complex.differentiableAt_Gamma s fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp at hre
      linarith [hs.1, Nat.cast_nonneg (α := ℝ) m]
    unfold poleNumerator
    exact (((differentiableAt_scatterQ hs.2).const_mul 2).mul
      ((hψ.differentiableAt_mellin (-s)).comp s differentiableAt_id.neg)).sub
      (hΓ.const_mul _) |>.differentiableWithinAt
  have hd := (Complex.differentiableOn_dslope (hU.mem_nhds h1U)).2 hd_num
  have hw1 : w + 1 ∈ U := ⟨by simp; linarith, hxi⟩
  exact ((hψ.differentiableAt_mellin w).const_mul 2).add
    (((hd _ hw1).differentiableAt (hU.mem_nhds hw1)).comp w (differentiableAt_id.add_const 1))

/-- Rapid vertical decay of `regularPart ψ` on the closed strip `-1/2 ≤ Re w ≤ 1`, including the
boundary line `Re w = -1/2` (`Re(2(w + 1)) = 1`). -/
private theorem exists_norm_regularPart_closed_strip_le {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : IsTest ψ a b) (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, -1 / 2 ≤ w.re → w.re ≤ 1 →
      ‖regularPart ψ w‖ ≤ B / (1 + w.im ^ 2) ^ K := by
  have hdiff_strip : ∀ w : ℂ, -1 / 2 ≤ w.re → DifferentiableAt ℂ (regularPart ψ) w := by
    intro w hw
    refine differentiableAt_regularPart_of_xi_ne_zero hψ (by linarith) ?_
    exact _root_.RHTower.xi_ne_zero_of_one_le_re (by simp; linarith)
  have hbox : IsCompact (Icc (-1 / 2 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hbox.exists_bound_of_continuousOn (f := regularPart ψ) fun w hw =>
    (hdiff_strip w hw.1.1).continuousAt.continuousWithinAt
  obtain ⟨K₀, N₀, hK₀, hinv⟩ := invZeta_poly_ge_one 4
  have hinv' : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (K₀ * 2 ^ N₀) * |s.im| ^ N₀ := by
    intro s hs0 hs1 ht
    have h2 : 2 ≤ |(2 * s).im| := by simp [abs_mul]; linarith
    have hb := hinv (2 * s) (by simp; linarith) (by simp; linarith) h2
    calc ‖(riemannZeta (2 * s))⁻¹‖ ≤ K₀ * |(2 * s).im| ^ N₀ := hb
      _ = (K₀ * 2 ^ N₀) * |s.im| ^ N₀ := by simp [abs_mul, mul_pow]; ring
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hinv'
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_norm_mellin_le_decay_pow hψ 6 K
  obtain ⟨C₂, hC₂, hm₂⟩ := exists_norm_mellin_le_decay_pow hψ 6 (K + NQ)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (1 / 2) 2
  obtain ⟨CE, hCE, hE⟩ := exists_pow_mul_exp_le NΓ K
  set B : ℝ := max B₀ 0 * 2 ^ K + (2 * C₁ + 2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE))
  refine ⟨B, by positivity, fun w hw1 hw2 => ?_⟩
  have hpos : 0 < (1 + w.im ^ 2) ^ K := by positivity
  rcases le_or_gt |w.im| 1 with ht | ht
  · have hwb : w ∈ Icc (-1 / 2 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1 := ⟨⟨hw1, hw2⟩, abs_le.mp ht⟩
    have h1 : (1 + w.im ^ 2) ^ K ≤ 2 ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_abs w.im]
    rw [le_div_iff₀ hpos]
    calc ‖regularPart ψ w‖ * (1 + w.im ^ 2) ^ K
        ≤ max B₀ 0 * 2 ^ K :=
          mul_le_mul ((hB₀ w hwb).trans (le_max_left _ _)) h1 (by positivity) (le_max_right _ _)
      _ ≤ B := le_add_of_nonneg_right (by positivity)
  · have ht1 : 1 ≤ |w.im| := ht.le
    have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at ht; linarith
    have hnw : 1 ≤ ‖w‖ := ht1.trans (Complex.abs_im_le_norm w)
    rw [regularPart_eq hw0]
    set s := w + 1
    have hsre0 : (1 / 2 : ℝ) ≤ s.re := by simp [s]; linarith
    have hsre1 : s.re ≤ 2 := by simp [s]; linarith
    have hsim : s.im = w.im := by simp [s]
    have hP1 : ‖mellin ψ w‖ ≤ C₁ / (1 + w.im ^ 2) ^ K :=
      hm₁ w (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hP2 : ‖mellin ψ (-s)‖ ≤ C₂ / (1 + w.im ^ 2) ^ (K + NQ) := by
      have h := hm₂ (-s) (by simp [s]; rw [abs_le]; constructor <;> linarith)
      simpa [s] using h
    have hQs := hQ s hsre0 hsre1 (by rw [hsim]; exact ht1)
    rw [hsim] at hQs
    have hΓs : ‖Complex.Gamma s‖ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by
      have h := hΓ s hsre0 hsre1 (by rw [hsim]; exact ht1)
      rw [hsim] at h
      calc ‖Complex.Gamma s‖ ≤ CΓ * (|w.im| ^ NΓ * Real.exp (-(Real.pi * |w.im| / 2))) := by
            linarith [h]
        _ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by gcongr; exact hE _ ht1
    have hpowle : |w.im| ^ NQ ≤ (1 + w.im ^ 2) ^ NQ :=
      pow_le_pow_left₀ (abs_nonneg _) (by nlinarith [sq_abs w.im])
    have hQψ : ‖scatterQ s‖ * ‖mellin ψ (-s)‖ ≤ CQ * C₂ / (1 + w.im ^ 2) ^ K := by
      calc ‖scatterQ s‖ * ‖mellin ψ (-s)‖
          ≤ (CQ * |w.im| ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) :=
            mul_le_mul hQs hP2 (norm_nonneg _) (by positivity)
        _ ≤ (CQ * (1 + w.im ^ 2) ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) := by gcongr
        _ = CQ * C₂ / (1 + w.im ^ 2) ^ K := by rw [pow_add]; field_simp
    have hN : ‖poleNumerator ψ s‖ ≤
        (2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by
      unfold poleNumerator
      calc ‖2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Complex.Gamma s‖
          ≤ 2 * (‖scatterQ s‖ * ‖mellin ψ (-s)‖) + ‖residueConst ψ‖ * ‖Complex.Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
            norm_num
        _ ≤ 2 * (CQ * C₂ / (1 + w.im ^ 2) ^ K) +
            ‖residueConst ψ‖ * (CΓ * (CE / (1 + w.im ^ 2) ^ K)) := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin ψ w + poleNumerator ψ s / w‖
        ≤ 2 * ‖mellin ψ w‖ + ‖poleNumerator ψ s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_div]
          norm_num
          exact div_le_self (norm_nonneg _) hnw
      _ ≤ 2 * (C₁ / (1 + w.im ^ 2) ^ K) +
          (2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by gcongr
      _ = (2 * C₁ + 2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ B / (1 + w.im ^ 2) ^ K :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hpos.le

/-- Vertical contour shift of `mellinInv` directly onto the boundary line `Re w = -1/2`. -/
private theorem mellinInv_one_eq_neg_half {ψ : ℝ → ℂ} {a b : ℝ} (hψ : IsTest ψ a b)
    {y : ℝ} (hy : 0 < y) :
    mellinInv 1 (regularPart ψ) y = mellinInv (-1 / 2) (regularPart ψ) y := by
  unfold mellinInv
  congr 1
  obtain ⟨B, hB0, hB⟩ := exists_norm_regularPart_closed_strip_le hψ 1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have huIcc : uIcc (1 : ℝ) (-1 / 2) = Icc (-1 / 2) 1 := by
    rw [uIcc_comm, uIcc_of_le (by norm_num)]
  have hshift := integral_vertical_line_shift_of_decay
    (Φ := fun s : ℂ => (y : ℂ) ^ (-s) * regularPart ψ s) (c₁ := 1) (c₂ := -1 / 2)
    (C := (y ^ (-1 : ℝ) + y ^ (1 / 2 : ℝ)) * B)
    (fun s hs => by
      rw [huIcc] at hs
      refine ((differentiableAt_id.neg).const_cpow (Or.inl hy0)).mul ?_
      exact differentiableAt_regularPart_of_xi_ne_zero hψ (by linarith [hs.1])
        (_root_.RHTower.xi_ne_zero_of_one_le_re (by simp; linarith [hs.1])))
    (fun s hs => by
      rw [huIcc] at hs
      have hb := hB s hs.1 hs.2
      rw [pow_one] at hb
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.neg_re]
      have hpow : y ^ (-s.re) ≤ y ^ (-1 : ℝ) + y ^ (1 / 2 : ℝ) := by
        have h1 : 0 ≤ y ^ (-1 : ℝ) := Real.rpow_nonneg hy.le _
        have h2 : 0 ≤ y ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy.le _
        rcases le_or_gt y 1 with hy1 | hy1
        · have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show -s.re ≥ -1 by linarith [hs.2])
          linarith
        · have := Real.rpow_le_rpow_of_exponent_le hy1.le (show -s.re ≤ 1 / 2 by linarith [hs.1])
          linarith
      calc y ^ (-s.re) * ‖regularPart ψ s‖
          ≤ (y ^ (-1 : ℝ) + y ^ (1 / 2 : ℝ)) * (B / (1 + s.im ^ 2)) :=
            mul_le_mul hpow hb (norm_nonneg _) (by positivity)
        _ = (y ^ (-1 : ℝ) + y ^ (1 / 2 : ℝ)) * B / (1 + s.im ^ 2) := by ring)
  simpa [smul_eq_mul] using hshift

/-- Polynomial height bound on the `1/ζ(2s)`-free factor of `scatterQ s` across `3/8 ≤ Re s ≤ 1/2`,
`|Im s| ≥ 1`, with constants independent of any height cutoff. -/
private theorem exists_norm_scatterPrefactor_le :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, 3 / 8 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖(s - 1) * (Complex.Gammaℝ (2 * s - 1) / Complex.Gammaℝ (2 * s)) *
        riemannZeta (2 * s - 1)‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ := exists_sharp_bound_norm_Gamma_strip (-1 / 8) 0
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ := exists_bound_norm_inv_Gamma_strip (3 / 8) (1 / 2)
  obtain ⟨C₃, N₃, hC₃, hζ⟩ := exists_bound_norm_riemannZeta_strip 1
  refine ⟨3 * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃), 1 + (N₁ + N₂) + N₃,
    by positivity, fun s hs0 hs1 ht => ?_⟩
  rw [norm_mul, norm_mul, norm_gammaℝ_div]
  have hA : ‖s - 1‖ ≤ 3 * |s.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h1
    have hre : |s.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hB1 : ‖Complex.Gamma (s - 1 / 2)‖ ≤
      C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2)) := by
    have h := hΓ₁ (s - 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using h
  have hB2 := hΓ₂ s hs0 hs1 ht
  have hB : ‖Complex.Gamma (s - 1 / 2)‖ * ‖(Complex.Gamma s)⁻¹‖ ≤
      C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
    calc ‖Complex.Gamma (s - 1 / 2)‖ * ‖(Complex.Gamma s)⁻¹‖
        ≤ (C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2))) *
            (C₂ * |s.im| ^ N₂ * Real.exp (Real.pi * |s.im| / 2)) :=
          mul_le_mul hB1 hB2 (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
          rw [pow_add]
          have hexp : Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (C₁ * C₂ * |s.im| ^ N₁ * |s.im| ^ N₂) * hexp
  have hC : ‖riemannZeta (2 * s - 1)‖ ≤ C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by
    have hz : (2 : ℂ) * s - 1 = (((2 * s.re - 1 : ℝ)) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hσ : |2 * s.re - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have ht2 : 1 ≤ |2 * s.im| := by rw [abs_mul]; norm_num; linarith
    have hb := hζ (2 * s.re - 1) (2 * s.im) hσ ht2
    rw [hz]
    calc ‖riemannZeta ((((2 * s.re - 1 : ℝ)) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I)‖
        ≤ C₃ * |2 * s.im| ^ N₃ := hb
      _ = C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by rw [abs_mul, mul_pow]; norm_num; ring
  calc ‖s - 1‖ * (Real.pi ^ (1 / 2 : ℝ) * (‖Complex.Gamma (s - 1 / 2)‖ * ‖(Complex.Gamma s)⁻¹‖)) *
        ‖riemannZeta (2 * s - 1)‖
      ≤ (3 * |s.im|) * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂ * |s.im| ^ (N₁ + N₂))) *
          (C₃ * 2 ^ N₃ * |s.im| ^ N₃) := by gcongr
    _ = 3 * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃) *
          |s.im| ^ (1 + (N₁ + N₂) + N₃) := by ring

/-- Across the shrinking Vinogradov–Korobov rectangle `-narainVKWidth δ T ≤ Re u ≤ 0`, `|Im u| ≤ T`,
`F(u) = regularPart ψ (u - 1/2)` is holomorphic and satisfies rapid vertical decay with height-loss
factor `narainVKCost T`, with `(δ, T₀)` independent of the decay order `K`. -/
private theorem exists_regularPart_vk_rect {ψ : ℝ → ℂ} {a b : ℝ} (hψ : IsTest ψ a b) :
    ∃ δ T₀ : ℝ, 0 < δ ∧ 3 ≤ T₀ ∧ Real.exp (Real.exp 1) ≤ T₀ ∧
      ∀ K : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧
        ∀ T : ℝ, T₀ ≤ T →
          0 < narainVKWidth δ T ∧ narainVKWidth δ T ≤ 1 / 8 ∧
          ∀ u : ℂ, -narainVKWidth δ T ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
            DifferentiableAt ℂ (fun u => regularPart ψ (u - 1 / 2)) u ∧
            ‖regularPart ψ (u - 1 / 2)‖ ≤ CK * narainVKCost T / (1 + u.im ^ 2) ^ K := by
  obtain ⟨Cζ, δ, T₀, hCζ, hδ, hT₀, hTexp, hzero, hinv⟩ :=
    _root_.RHTower.Sieve.exists_bound_invZeta_vk_uniform
  have hexp1 : Real.exp (Real.exp 1) ≤ T₀ :=
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by norm_num))).trans hTexp
  have hexp_2T₀ : Real.exp (Real.exp 1) ≤ 2 * T₀ + 1 := by linarith [hT₀]
  have hvk_strip : ∀ T : ℝ, T₀ ≤ T →
      0 < narainVKWidth δ T ∧ narainVKWidth δ T ≤ 1 / 8 ∧
      ∀ u : ℂ, -narainVKWidth δ T ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
        _root_.RHTower.xi (1 + 2 * u) ≠ 0 ∧
        (1 ≤ |u.im| → ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ Cζ * narainVKCost T) := by
    intro T hT
    have hT3 : 3 ≤ T := hT₀.trans hT
    have hK2 : T₀ ≤ 2 * T := by linarith
    have hw : 0 < _root_.RHTower.vkHadamardWidth (2 * T + 1) :=
      _root_.RHTower.vkHadamardWidth_pos (by linarith)
    have hd : 0 < narainVKWidth δ T := div_pos (lt_min (lt_min hδ zero_lt_one) hw) (by norm_num)
    have hd8 : narainVKWidth δ T ≤ 1 / 8 := by
      unfold narainVKWidth
      exact div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right δ 1)) (by norm_num)
    have hdmin : 2 * narainVKWidth δ T ≤
        min δ (_root_.RHTower.vkHadamardWidth (2 * T + 1)) / 4 := by
      have hm : min (min δ 1) (_root_.RHTower.vkHadamardWidth (2 * T + 1)) ≤
          min δ (_root_.RHTower.vkHadamardWidth (2 * T + 1)) :=
        min_le_min (min_le_left _ _) le_rfl
      unfold narainVKWidth
      linarith
    refine ⟨hd, hd8, fun u hlo hhi him => ?_⟩
    have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
    have him' : |(1 + 2 * u).im| ≤ 2 * T := by
      have he : (1 + 2 * u).im = 2 * u.im := by simp
      rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hlo' : 1 - min δ (_root_.RHTower.vkHadamardWidth (2 * T + 1)) / 4 ≤ (1 + 2 * u).re := by
      rw [hre]; linarith
    have hre0 : 0 < (1 + 2 * u).re := by rw [hre]; linarith
    have hxi : _root_.RHTower.xi (1 + 2 * u) ≠ 0 := by
      by_cases hne : 1 + 2 * u = 1
      · rw [hne, _root_.RHTower.xi_one]; norm_num
      · exact fun hz => hzero (1 + 2 * u) (2 * T) hK2 him' hlo' hne
          ((_root_.RHTower.xi_eq_zero_iff hre0 hne).mp hz)
    refine ⟨hxi, fun ht => ?_⟩
    have hne : 1 + 2 * u ≠ 1 := by
      intro hz
      have hv := congrArg Complex.im hz
      simp at hv
      rw [hv, abs_zero] at ht
      linarith
    have hζ := hinv (1 + 2 * u) (2 * T) hK2 him' hlo' (by rw [hre]; linarith)
    rw [_root_.RHTower.Sieve.invZeta_eq_inv hne] at hζ
    simpa only [narainVKCost, mul_assoc] using hζ
  have hdiff_u : ∀ T : ℝ, T₀ ≤ T → ∀ u : ℂ, -narainVKWidth δ T ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
      DifferentiableAt ℂ (fun u => regularPart ψ (u - 1 / 2)) u := by
    intro T hT u hlo hhi him
    obtain ⟨_, hd8, hpt⟩ := hvk_strip T hT
    obtain ⟨hxi, _⟩ := hpt u hlo hhi him
    have h2 : 2 * ((u - 1 / 2) + 1) = 1 + 2 * u := by ring
    exact (differentiableAt_regularPart_of_xi_ne_zero hψ
      (by simp; linarith) (by rwa [h2])).comp u (differentiableAt_id.sub_const _)
  set box0 : Set ℂ := Icc (-narainVKWidth δ T₀) 0 ×ℂ Icc (-1 : ℝ) 1
  have hbox0 : IsCompact box0 := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hbox0.exists_bound_of_continuousOn
    (f := fun u : ℂ => regularPart ψ (u - 1 / 2)) fun u hu =>
      (hdiff_u T₀ le_rfl u hu.1.1 hu.1.2 ((abs_le.mpr hu.2).trans (by linarith))).continuousAt
        |>.continuousWithinAt
  obtain ⟨Cpre, Npre, hCpre, hpre⟩ := exists_norm_scatterPrefactor_le
  refine ⟨δ, T₀, hδ, hT₀, hexp1, fun K => ?_⟩
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_norm_mellin_le_decay_pow hψ 6 K
  obtain ⟨C₂, hC₂, hm₂⟩ := exists_norm_mellin_le_decay_pow hψ 6 (K + Npre)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (3 / 8) (1 / 2)
  obtain ⟨CE, hCE, hE⟩ := exists_pow_mul_exp_le NΓ K
  set CK : ℝ := max B₀ 0 * 2 ^ K +
    (2 * C₁ + 2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE))
  refine ⟨CK, by positivity, fun T hT => ?_⟩
  obtain ⟨hd, hd8, hpt⟩ := hvk_strip T hT
  have hcost1 : 1 ≤ narainVKCost T := one_le_narainVKCost (by linarith)
  refine ⟨hd, hd8, fun u hlo hhi him => ⟨hdiff_u T hT u hlo hhi him, ?_⟩⟩
  have hpos : 0 < (1 + u.im ^ 2) ^ K := by positivity
  rcases le_or_gt |u.im| 1 with ht | ht
  · have hw_anti : narainVKWidth δ T ≤ narainVKWidth δ T₀ := narainVKWidth_anti δ hexp_2T₀ hT
    have hub : u ∈ box0 := ⟨⟨by linarith, hhi⟩, abs_le.mp ht⟩
    have h1 : (1 + u.im ^ 2) ^ K ≤ 2 ^ K :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [sq_abs u.im])
    rw [le_div_iff₀ hpos]
    calc ‖regularPart ψ (u - 1 / 2)‖ * (1 + u.im ^ 2) ^ K
        ≤ max B₀ 0 * 2 ^ K :=
          mul_le_mul ((hB₀ u hub).trans (le_max_left _ _)) h1 (by positivity) (le_max_right _ _)
      _ ≤ CK * 1 := by simp only [CK, mul_one]; exact le_add_of_nonneg_right (by positivity)
      _ ≤ CK * narainVKCost T := mul_le_mul_of_nonneg_left hcost1 (by positivity)
  · have ht1 : 1 ≤ |u.im| := ht.le
    obtain ⟨_, hζ_bd⟩ := hpt u hlo hhi him
    have hinv_u := hζ_bd ht1
    set w : ℂ := u - 1 / 2
    set s : ℂ := w + 1
    have hwim : w.im = u.im := by simp [w]
    have hsim : s.im = u.im := by simp [s, w]
    have hw0 : w ≠ 0 := fun h => by
      have := congrArg Complex.im h
      rw [hwim, Complex.zero_im] at this
      rw [this, abs_zero] at ht
      linarith
    have hnw : 1 ≤ ‖w‖ := (by rw [hwim]; exact ht1).trans (Complex.abs_im_le_norm w)
    have hsre0 : (3 / 8 : ℝ) ≤ s.re := by simp [s, w]; linarith
    have hsre1 : s.re ≤ 1 / 2 := by simp [s, w]; linarith
    have h2s : 2 * s = 1 + 2 * u := by simp [s, w]; ring
    have hs_im0 : s.im ≠ 0 := fun h => by rw [hsim] at h; rw [h, abs_zero] at ht1; linarith
    have hQs : ‖scatterQ s‖ ≤ (Cpre * Cζ) * narainVKCost T * |u.im| ^ Npre := by
      rw [scatterQ_eq hs_im0, norm_mul]
      have hp := hpre s hsre0 hsre1 (by rw [hsim]; exact ht1)
      rw [hsim] at hp
      rw [h2s]
      calc ‖(s - 1) * (Complex.Gammaℝ (2 * s - 1) / Complex.Gammaℝ (2 * s)) *
              riemannZeta (2 * s - 1)‖ * ‖(riemannZeta (1 + 2 * u))⁻¹‖
          ≤ (Cpre * |u.im| ^ Npre) * (Cζ * narainVKCost T) :=
            mul_le_mul hp hinv_u (norm_nonneg _) (by positivity)
        _ = (Cpre * Cζ) * narainVKCost T * |u.im| ^ Npre := by ring
    have hP1 : ‖mellin ψ w‖ ≤ C₁ / (1 + u.im ^ 2) ^ K := by
      have h := hm₁ w (by simp [w]; rw [abs_le]; constructor <;> linarith)
      rwa [hwim] at h
    have hP2 : ‖mellin ψ (-s)‖ ≤ C₂ / (1 + u.im ^ 2) ^ (K + Npre) := by
      have h := hm₂ (-s) (by simp [s, w]; rw [abs_le]; constructor <;> linarith)
      simpa [s, w] using h
    have hΓs : ‖Complex.Gamma s‖ ≤ CΓ * (CE / (1 + u.im ^ 2) ^ K) := by
      have h := hΓ s hsre0 hsre1 (by rw [hsim]; exact ht1)
      rw [hsim] at h
      calc ‖Complex.Gamma s‖ ≤ CΓ * (|u.im| ^ NΓ * Real.exp (-(Real.pi * |u.im| / 2))) := by
            linarith [h]
        _ ≤ CΓ * (CE / (1 + u.im ^ 2) ^ K) := by gcongr; exact hE _ ht1
    have hpowle : |u.im| ^ Npre ≤ (1 + u.im ^ 2) ^ Npre :=
      pow_le_pow_left₀ (abs_nonneg _) (by nlinarith [sq_abs u.im])
    have hQψ : ‖scatterQ s‖ * ‖mellin ψ (-s)‖ ≤
        (Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K := by
      calc ‖scatterQ s‖ * ‖mellin ψ (-s)‖
          ≤ ((Cpre * Cζ) * narainVKCost T * |u.im| ^ Npre) *
              (C₂ / (1 + u.im ^ 2) ^ (K + Npre)) :=
            mul_le_mul hQs hP2 (norm_nonneg _) (by positivity)
        _ ≤ ((Cpre * Cζ) * narainVKCost T * (1 + u.im ^ 2) ^ Npre) *
              (C₂ / (1 + u.im ^ 2) ^ (K + Npre)) := by gcongr
        _ = (Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K := by
            rw [pow_add]; field_simp
    rw [show regularPart ψ (u - 1 / 2) = regularPart ψ w from rfl, regularPart_eq hw0]
    have hN : ‖poleNumerator ψ s‖ ≤
        (2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) *
          narainVKCost T / (1 + u.im ^ 2) ^ K := by
      unfold poleNumerator
      calc ‖2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Complex.Gamma s‖
          ≤ 2 * (‖scatterQ s‖ * ‖mellin ψ (-s)‖) + ‖residueConst ψ‖ * ‖Complex.Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
            norm_num
        _ ≤ 2 * ((Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K) +
              ‖residueConst ψ‖ * (CΓ * (CE / (1 + u.im ^ 2) ^ K)) * 1 := by
            rw [mul_one]; gcongr
        _ ≤ 2 * ((Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K) +
              ‖residueConst ψ‖ * (CΓ * (CE / (1 + u.im ^ 2) ^ K)) * narainVKCost T := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin ψ w + poleNumerator ψ s / w‖
        ≤ 2 * ‖mellin ψ w‖ + ‖poleNumerator ψ s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_div]
          norm_num
          exact div_le_self (norm_nonneg _) hnw
      _ ≤ 2 * (C₁ / (1 + u.im ^ 2) ^ K) * 1 +
            (2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) *
              narainVKCost T / (1 + u.im ^ 2) ^ K := by
          rw [mul_one]; gcongr
      _ ≤ 2 * (C₁ / (1 + u.im ^ 2) ^ K) * narainVKCost T +
            (2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) *
              narainVKCost T / (1 + u.im ^ 2) ^ K := by gcongr
      _ = (2 * C₁ + 2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) *
            narainVKCost T / (1 + u.im ^ 2) ^ K := by ring
      _ ≤ CK * narainVKCost T / (1 + u.im ^ 2) ^ K := by
          refine div_le_div_of_nonneg_right ?_ hpos.le
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by linarith)

/-- Elementary polynomial-to-exponential domination `x^n ≤ (n + 1)^n exp x` for `x ≥ 0`. -/
private theorem pow_le_succ_pow_mul_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ ((n : ℝ) + 1) ^ n * Real.exp x := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : x / ((n : ℝ) + 1) ≤ Real.exp (x / ((n : ℝ) + 1)) := by
    linarith [Real.add_one_le_exp (x / ((n : ℝ) + 1))]
  have h2 : (x / ((n : ℝ) + 1)) ^ n ≤ Real.exp x := by
    calc (x / ((n : ℝ) + 1)) ^ n
        ≤ Real.exp (x / ((n : ℝ) + 1)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((n : ℝ) * (x / ((n : ℝ) + 1))) := (Real.exp_nat_mul _ n).symm
      _ ≤ Real.exp x := by
          apply Real.exp_le_exp.mpr
          rw [mul_div_assoc', div_le_iff₀ hpos]
          nlinarith
  rw [div_pow, div_le_iff₀ (pow_pos hpos n)] at h2
  linarith

/-- Core contour-shift bound into the shrinking Vinogradov–Korobov rectangle: every test profile
above height `1` thermalizes at stretched-exponential super-square-root rate
`O(y^{1/2} exp(-√(-log y)))` on `(0, 1]`. -/
private theorem norm_horocycleMean_sub_le_stretched_exp_test {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : IsTest ψ a b) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein ψ) y - residueConst ψ‖ ≤
        C * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y)) := by
  have ha0 : 0 < a := by linarith
  have hψa : ∀ t, t < a → ψ t = 0 := hψ.zero_left
  have hψb : ∀ t, b < t → ψ t = 0 := hψ.zero_right
  obtain ⟨δ, T₀, hδ, hT₀, hTexp1, hrect⟩ := exists_regularPart_vk_rect hψ
  set c₀ : ℝ := min δ 1 / 32
  have hmin0 : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hc₀ : 0 < c₀ := div_pos hmin0 (by norm_num)
  have hc₀_le : c₀ ≤ 1 / 32 :=
    div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
  set K : ℕ := ⌈2 / c₀⌉₊ + 1
  have hK1 : 1 ≤ K := by omega
  have hK_sub : 2 ≤ ((K - 1 : ℕ) : ℝ) * c₀ := by
    have h1 : 2 / c₀ ≤ ((K - 1 : ℕ) : ℝ) := by
      simp only [K, add_tsub_cancel_right]
      exact Nat.le_ceil _
    exact (div_le_iff₀ hc₀).mp h1
  have hK_mul : 2 ≤ (K : ℝ) * c₀ := by
    have hle : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.sub_le K 1
    exact hK_sub.trans (mul_le_mul_of_nonneg_right hle hc₀.le)
  obtain ⟨B_K, hB_K0, hB_K⟩ := exists_norm_regularPart_closed_strip_le hψ K
  obtain ⟨CK, hCK0, hCK⟩ := hrect K
  obtain ⟨S_cost, hS_cost⟩ := Filter.eventually_atTop.mp eventually_narainVKCost_le_log_power
  obtain ⟨S_width, hS_width⟩ := Filter.eventually_atTop.mp (eventually_narainVKWidth_ge_inv_log hδ)
  set S_all : ℝ := max (max T₀ 3) (max S_cost S_width)
  have hS3 : 3 ≤ S_all := (le_max_right T₀ 3).trans (le_max_left _ _)
  have hST₀ : T₀ ≤ S_all := (le_max_left T₀ 3).trans (le_max_left _ _)
  have hScost : S_cost ≤ S_all := (le_max_left S_cost S_width).trans (le_max_right _ _)
  have hSwidth : S_width ≤ S_all := (le_max_right S_cost S_width).trans (le_max_right _ _)
  set L₀ : ℝ := (max (Real.log S_all / c₀) 1 + 1) ^ 2
  have hL₀_ge : 4 ≤ L₀ := by
    have : 2 ≤ max (Real.log S_all / c₀) 1 + 1 := by linarith [le_max_right (Real.log S_all / c₀) 1]
    nlinarith
  obtain ⟨C_base, hC_base0, hbase⟩ := norm_horocycleMean_sub_le_of_zeroFree hψ ha (θ := 1)
    zero_le_one le_rfl (fun z hz => xi_ne_zero_of_one_lt_re hz)
    (fun δ' hδ' d => ⟨1 + 1 / δ', 0, by positivity, fun z hz _ _ => by
      simpa using _root_.RHTower.norm_inv_riemannZeta_le_of_le_re (by linarith : 1 < 1 + δ') hz⟩)
    (ε := 1 / 4) (by norm_num) (by norm_num)
  have hΨ_strip := mellinRegularStrip_regularPart hψ zero_le_one le_rfl
    (fun z hz => xi_ne_zero_of_one_lt_re hz)
    (fun δ' hδ' d => ⟨1 + 1 / δ', 0, by positivity, fun z hz _ _ => by
      simpa using _root_.RHTower.norm_inv_riemannZeta_le_of_le_re (by linarith : 1 < 1 + δ') hz⟩)
  obtain ⟨B_pe, -, hB_pe⟩ := exists_norm_pseudoEisenstein_le hψ.continuous ha hψa hψb
  have hFc := continuous_pseudoEisenstein hψ.continuous ha0 hψa
  set c := residueConst ψ
  set I₀ : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun t => by positivity
  set D_vk : ℝ := (3 : ℝ) ^ (7 : ℕ) * (30 : ℝ) ^ (14 : ℕ)
  set C_rect : ℝ := (1 / (2 * Real.pi)) * (3 * CK * D_vk + B_K * I₀) +
    ‖c‖ * Real.exp (1 / 2)
  set C_low : ℝ := C_base * Real.exp (L₀ / 2 + Real.sqrt L₀)
  set C_tot : ℝ := C_low + C_rect + 1
  have hC_tot : 0 < C_tot := by positivity
  refine ⟨C_tot, hC_tot, fun y hy hy1 => ?_⟩
  set L : ℝ := -Real.log y
  have hL0 : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hy.le hy1)
  have hy_half : y ^ (1 / 2 : ℝ) = Real.exp (-L / 2) := by
    rw [Real.rpow_def_of_pos hy]
    congr 1
    simp only [L]
    ring
  rcases le_or_gt L L₀ with hLL₀ | hLL₀
  · have hb1 : ‖horocycleMean (pseudoEisenstein ψ) y - c‖ ≤ C_base := by
      have hb := hbase y hy hy1
      have hrp : y ^ (1 - (1 : ℝ) / 2 - 1 / 4) ≤ 1 :=
        Real.rpow_le_one hy.le hy1 (by norm_num)
      calc ‖horocycleMean (pseudoEisenstein ψ) y - c‖
          ≤ C_base * y ^ (1 - (1 : ℝ) / 2 - 1 / 4) := hb
        _ ≤ C_base * 1 := mul_le_mul_of_nonneg_left hrp hC_base0
        _ = C_base := mul_one _
    have hs_le : Real.sqrt L ≤ Real.sqrt L₀ := Real.sqrt_le_sqrt hLL₀
    have hexp_ge : 1 ≤ Real.exp (L₀ / 2 + Real.sqrt L₀) *
        (y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt L)) := by
      rw [hy_half, ← Real.exp_add, ← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖horocycleMean (pseudoEisenstein ψ) y - c‖
        ≤ C_base * 1 := by linarith
      _ ≤ C_base * (Real.exp (L₀ / 2 + Real.sqrt L₀) *
            (y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt L))) :=
          mul_le_mul_of_nonneg_left hexp_ge hC_base0
      _ = C_low * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt L) := by ring
      _ ≤ C_tot * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt L) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.le _)
          simp only [C_tot]
          linarith [hCK0, hB_K0, hI₀, norm_nonneg c, Real.exp_nonneg (1 / 2 : ℝ)]
  · -- Large `L > L₀`: shift `g(y) = A_ψ(y) - c e^{-y}` into the VK rectangle
    set s : ℝ := Real.sqrt L
    have hs_sq : s ^ 2 = L := Real.sq_sqrt hL0
    have hs_gt : max (Real.log S_all / c₀) 1 + 1 < s := by
      have h0 : 0 ≤ max (Real.log S_all / c₀) 1 + 1 := by positivity
      nlinarith [Real.sqrt_nonneg L, hs_sq]
    have hs1 : 1 < s := by linarith [le_max_right (Real.log S_all / c₀) 1]
    have hs0 : 0 < s := by linarith
    have hlog_lt : Real.log S_all < c₀ * s := by
      have hdiv : Real.log S_all / c₀ < s := by linarith [le_max_left (Real.log S_all / c₀) 1]
      rwa [div_lt_iff₀ hc₀] at hdiv
    set T : ℝ := Real.exp (c₀ * s)
    have hS_le_T : S_all ≤ T := by
      have hpos : 0 < S_all := by linarith
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr hlog_lt.le
    have hT3 : 3 ≤ T := hS3.trans hS_le_T
    have hTT₀ : T₀ ≤ T := hST₀.trans hS_le_T
    have hT0 : 0 ≤ T := by linarith
    obtain ⟨hd0, hd8, hrect_T⟩ := hCK T hTT₀
    set d : ℝ := narainVKWidth δ T
    -- Step 1: Identify `g y = mellinInv (-1 / 2) (regularPart ψ) y`
    set g : ℝ → ℂ := fun u => horocycleMean (pseudoEisenstein ψ) u -
      c * ((Real.exp (-u) : ℝ) : ℂ)
    have hconv : MellinConvergent g 1 := by
      have h1 := mellinConvergent_horocycleMean hψ.continuous ha hψa hψb (s := 2) (by norm_num)
      have h2 := (mellinConvergent_exp_neg (w := 1) (by norm_num)).const_smul c
      norm_num at h1
      refine (h1.sub h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, g, smul_eq_mul]
      ring
    have hline : ∀ t : ℝ, mellin g ((1 : ℝ) + t * Complex.I) =
        regularPart ψ ((1 : ℝ) + t * Complex.I) :=
      fun t => mellin_sub_exp_eq_regularPart hψ ha (by simp)
    have hvert : VerticalIntegrable (mellin g) 1 := by
      refine (hΨ_strip.integrable_line (by norm_num) (by norm_num)).congr
        (Eventually.of_forall fun t => (hline t).symm)
    have hcont : ContinuousAt g y :=
      (continuousAt_horocycleMean hFc hB_pe hy).sub (continuousAt_const.mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt)
    have hgy_eq : g y = mellinInv (-1 / 2) (regularPart ψ) y := by
      rw [← mellinInv_mellin_eq 1 g hy hconv hvert hcont]
      have hinv1 : mellinInv 1 (mellin g) y = mellinInv 1 (regularPart ψ) y := by
        unfold mellinInv
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun t => by simp only; rw [hline t])
      rw [hinv1, mellinInv_one_eq_neg_half hψ hy]
    -- Step 2: Factor `y^{1/2}` out of `mellinInv (-1/2) (regularPart ψ) y`
    set G₀ : ℂ → ℂ := fun u => Complex.exp ((L : ℂ) * u) * regularPart ψ (u - 1 / 2)
    have hy0_c : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hcpow_line : ∀ t : ℝ,
        (y : ℂ) ^ (-(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          regularPart ψ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) * G₀ ((t : ℂ) * Complex.I) := by
      intro t
      rw [Complex.cpow_def_of_ne_zero hy0_c, Complex.ofReal_log hy.le]
      have hexp_arg : ((Real.log y : ℝ) : ℂ) * (-(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
          ((-L / 2 : ℝ) : ℂ) + (L : ℂ) * ((t : ℂ) * Complex.I) := by
        simp only [L]
        push_cast
        ring
      have harg_u : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I - 1 / 2 := by
        push_cast; ring
      rw [hexp_arg, Complex.exp_add, ← Complex.ofReal_exp, ← hy_half, harg_u]
      simp only [G₀, mul_assoc]
    have hgy_norm : ‖g y‖ =
        (1 / (2 * Real.pi)) * y ^ (1 / 2 : ℝ) * ‖∫ t : ℝ, G₀ ((t : ℂ) * Complex.I)‖ := by
      rw [hgy_eq]
      unfold mellinInv
      simp_rw [hcpow_line]
      rw [integral_const_mul, norm_smul, norm_mul, Real.norm_of_nonneg (by positivity),
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]
      ring
    -- Step 3: Split `∫_ℝ G₀(it) dt` into `[-T, T]` and `(Ioc (-T) T)ᶜ`
    have hG₀_norm_line : ∀ t : ℝ,
        ‖G₀ ((t : ℂ) * Complex.I)‖ ≤ B_K / (1 + t ^ 2) ^ K := by
      intro t
      simp only [G₀, norm_mul, Complex.norm_exp]
      have hre0 : ((L : ℂ) * ((t : ℂ) * Complex.I)).re = 0 := by simp
      rw [hre0, Real.exp_zero, one_mul]
      have hb := hB_K ((t : ℂ) * Complex.I - 1 / 2) (by simp) (by simp)
      simpa using hb
    have hG₀_cont : Continuous fun t : ℝ => G₀ ((t : ℂ) * Complex.I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hw : DifferentiableAt ℂ (regularPart ψ) ((t : ℂ) * Complex.I - 1 / 2) :=
        differentiableAt_regularPart_of_xi_ne_zero hψ (by simp; norm_num)
          (_root_.RHTower.xi_ne_zero_of_one_le_re (by simp))
      exact (((Complex.differentiableAt_exp.comp _
        ((differentiableAt_id.const_mul (L : ℂ)))).continuousAt.comp (by fun_prop)).mul
        (hw.continuousAt.comp (by fun_prop)))
    have hG₀_int : Integrable fun t : ℝ => G₀ ((t : ℂ) * Complex.I) := by
      refine (integrable_inv_one_add_sq.const_mul B_K).mono' hG₀_cont.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      have h1 : (1 + t ^ 2) ^ 1 ≤ (1 + t ^ 2) ^ K :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg t]) hK1
      rw [pow_one] at h1
      calc ‖G₀ ((t : ℂ) * Complex.I)‖
          ≤ B_K / (1 + t ^ 2) ^ K := hG₀_norm_line t
        _ ≤ B_K / (1 + t ^ 2) := div_le_div_of_nonneg_left hB_K0 (by positivity) h1
        _ = B_K * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _
    have hsplit_int : (∫ t : ℝ, G₀ ((t : ℂ) * Complex.I)) =
        (∫ t : ℝ in (-T)..T, G₀ ((t : ℂ) * Complex.I)) +
          (∫ t : ℝ in (Ioc (-T) T)ᶜ, G₀ ((t : ℂ) * Complex.I)) := by
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact (MeasureTheory.integral_add_compl measurableSet_Ioc hG₀_int).symm
    -- Step 4: Bound the vertical tail on `(Ioc (-T) T)ᶜ`
    have htail_bd : ‖∫ t : ℝ in (Ioc (-T) T)ᶜ, G₀ ((t : ℂ) * Complex.I)‖ ≤
        B_K * I₀ / T ^ (2 * (K - 1)) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc.compl]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt_tail : ∀ t : ℝ, ‖(Ioc (-T) T)ᶜ.indicator (fun t : ℝ => G₀ ((t : ℂ) * Complex.I)) t‖ ≤
          (B_K / T ^ (2 * (K - 1))) * (1 + t ^ 2)⁻¹ := by
        intro t
        by_cases ht : t ∈ (Ioc (-T) T)ᶜ
        · rw [Set.indicator_of_mem ht]
          have hTt : T ≤ |t| := by
            rw [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
            rcases ht with h1 | h1
            · linarith [neg_le_abs t]
            · linarith [le_abs_self t]
          have hTsq : T ^ 2 ≤ 1 + t ^ 2 := by
            have : T ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hT0 hTt 2
            rw [sq_abs] at this
            linarith
          have hpowK : T ^ (2 * (K - 1)) * (1 + t ^ 2) ≤ (1 + t ^ 2) ^ K := by
            have hk_eq : (K - 1) + 1 = K := Nat.sub_add_cancel hK1
            calc T ^ (2 * (K - 1)) * (1 + t ^ 2)
                = (T ^ 2) ^ (K - 1) * (1 + t ^ 2) := by rw [pow_mul]
              _ ≤ (1 + t ^ 2) ^ (K - 1) * (1 + t ^ 2) :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hTsq _) (by positivity)
              _ = (1 + t ^ 2) ^ K := by rw [← pow_succ, hk_eq]
          calc ‖G₀ ((t : ℂ) * Complex.I)‖
              ≤ B_K / (1 + t ^ 2) ^ K := hG₀_norm_line t
            _ ≤ B_K / (T ^ (2 * (K - 1)) * (1 + t ^ 2)) :=
                div_le_div_of_nonneg_left hB_K0 (by positivity) hpowK
            _ = (B_K / T ^ (2 * (K - 1))) * (1 + t ^ 2)⁻¹ := by field_simp
        · rw [Set.indicator_of_notMem ht, norm_zero]
          positivity
      have hint_dom : Integrable (fun t : ℝ => (B_K / T ^ (2 * (K - 1))) * (1 + t ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul _
      calc ∫ t : ℝ, ‖(Ioc (-T) T)ᶜ.indicator (fun t : ℝ => G₀ ((t : ℂ) * Complex.I)) t‖
          ≤ ∫ t : ℝ, (B_K / T ^ (2 * (K - 1))) * (1 + t ^ 2)⁻¹ :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint_dom
              (Eventually.of_forall hpt_tail)
        _ = (B_K / T ^ (2 * (K - 1))) * I₀ := integral_const_mul _ _
        _ = B_K * I₀ / T ^ (2 * (K - 1)) := by ring
    -- Step 5: Shift the finite segment `[-T, T]` across `[-d, 0] × [-T, T]`
    have hrect_bd : ‖∫ t : ℝ in (-T)..T, G₀ ((t : ℂ) * Complex.I)‖ ≤
        2 * T * CK * narainVKCost T * Real.exp (-(d * L)) +
          2 * d * CK * narainVKCost T / T ^ (2 * K) := by
      have hd_nn : 0 ≤ d := hd0.le
      have hdiff_G₀ : DifferentiableOn ℂ G₀ (uIcc (-d) 0 ×ℂ uIcc (-T) T) := by
        intro u hu
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hu
        have hF := (hrect_T u hu.1.1 hu.1.2 (abs_le.mpr hu.2)).1
        exact ((Complex.differentiableAt_exp.comp u
          (differentiableAt_id.const_mul (L : ℂ))).mul hF).differentiableWithinAt
      have hshift := _root_.RHTower.Sieve.integral_vertical_sub_eq_horizontal_rect T hdiff_G₀
      have hG₀_norm : ∀ u : ℂ, ‖G₀ u‖ = Real.exp (L * u.re) * ‖regularPart ψ (u - 1 / 2)‖ := by
        intro u; simp [G₀, Complex.norm_exp, Complex.mul_re]
      have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -T) (b := T) (f := fun t : ℝ => G₀ ((-d : ℂ) + t * Complex.I))
        (C := CK * narainVKCost T * Real.exp (-(d * L))) (fun t ht => by
          rw [uIoc_of_le (by linarith)] at ht
          have habs : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
          have hb := (hrect_T ((-d : ℂ) + t * Complex.I) (by simp) (by simpa using hd_nn)
            (by simpa using habs)).2
          have h1 : 1 ≤ (1 + ((-d : ℂ) + (t : ℂ) * Complex.I).im ^ 2) ^ K :=
            one_le_pow₀ (by nlinarith [sq_nonneg (((-d : ℂ) + (t : ℂ) * Complex.I).im)])
          have hb' : ‖regularPart ψ (((-d : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)‖ ≤
              CK * narainVKCost T :=
            hb.trans (div_le_self (by positivity) h1)
          rw [hG₀_norm, show ((-d : ℂ) + (t : ℂ) * Complex.I).re = -d by simp,
            show L * -d = -(d * L) by ring]
          calc Real.exp (-(d * L)) * ‖regularPart ψ (((-d : ℂ) + (t : ℂ) * Complex.I) - 1 / 2)‖
              ≤ Real.exp (-(d * L)) * (CK * narainVKCost T) :=
                mul_le_mul_of_nonneg_left hb' (Real.exp_nonneg _)
            _ = CK * narainVKCost T * Real.exp (-(d * L)) := by ring)
      have hedge : ∀ v : ℝ, |v| = T →
          ‖∫ r : ℝ in (-d)..0, G₀ ((r : ℂ) + v * Complex.I)‖ ≤
            (CK * narainVKCost T / T ^ (2 * K)) * d := by
        intro v hv
        have hi := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := -d) (b := 0) (f := fun r : ℝ => G₀ ((r : ℂ) + v * Complex.I))
          (C := CK * narainVKCost T / T ^ (2 * K)) (fun r hr => by
            rw [uIoc_of_le (by linarith)] at hr
            have hb := (hrect_T ((r : ℂ) + v * Complex.I) (by simpa using hr.1.le)
              (by simpa using hr.2) (by simpa using hv.le)).2
            have him_sq : ((r : ℂ) + (v : ℂ) * Complex.I).im ^ 2 = T ^ 2 := by
              have him : ((r : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
              rw [him, ← sq_abs, hv]
            rw [him_sq] at hb
            have hTpow : T ^ (2 * K) ≤ (1 + T ^ 2) ^ K := by
              rw [pow_mul]
              exact pow_le_pow_left₀ (by positivity) (by linarith) K
            have hb' : ‖regularPart ψ (((r : ℂ) + (v : ℂ) * Complex.I) - 1 / 2)‖ ≤
                CK * narainVKCost T / T ^ (2 * K) :=
              hb.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hTpow)
            rw [hG₀_norm, show ((r : ℂ) + (v : ℂ) * Complex.I).re = r by simp]
            have hexp1 : Real.exp (L * r) ≤ 1 :=
              Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hL0 hr.2)
            calc Real.exp (L * r) * ‖regularPart ψ (((r : ℂ) + (v : ℂ) * Complex.I) - 1 / 2)‖
                ≤ 1 * (CK * narainVKCost T / T ^ (2 * K)) :=
                  mul_le_mul hexp1 hb' (norm_nonneg _) (by positivity)
              _ = _ := one_mul _)
        simpa only [sub_neg_eq_add, zero_add, abs_of_nonneg hd_nn] using hi
      have htop := hedge T (abs_of_nonneg hT0)
      have hbot := hedge (-T) (by rw [abs_neg, abs_of_nonneg hT0])
      have hleft' : ‖∫ t : ℝ in (-T)..T, G₀ ((-d : ℂ) + t * Complex.I)‖ ≤
          (CK * narainVKCost T * Real.exp (-(d * L))) * (2 * T) := by
        simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * T)] using hleft
      simp only [Complex.ofReal_zero, Complex.ofReal_neg] at hshift hbot
      have hdiffnorm : ‖(∫ t : ℝ in (-T)..T, G₀ ((0 : ℂ) + t * Complex.I)) -
          ∫ t : ℝ in (-T)..T, G₀ ((-d : ℂ) + t * Complex.I)‖ ≤
            2 * (CK * narainVKCost T / T ^ (2 * K)) * d := by
        rw [← smul_sub] at hshift
        have hn := congrArg norm hshift
        simp only [norm_smul, Complex.norm_I, one_mul] at hn
        rw [hn]
        exact (norm_sub_le _ _).trans (by linarith only [htop, hbot])
      have htri := norm_add_le
        ((∫ t : ℝ in (-T)..T, G₀ ((0 : ℂ) + t * Complex.I)) -
          ∫ t : ℝ in (-T)..T, G₀ ((-d : ℂ) + t * Complex.I))
        (∫ t : ℝ in (-T)..T, G₀ ((-d : ℂ) + t * Complex.I))
      rw [sub_add_cancel] at htri
      have htot := htri.trans (add_le_add hdiffnorm hleft')
      simp only [zero_add] at htot
      exact htot.trans_eq (by ring)
    -- Step 6: Absorb `T`, `narainVKCost T`, `exp(-d L)`, `T^{-2K}`, and `T^{-2(K-1)}` into `exp(-s)`
    have hlog2T : Real.log (2 * T + 1) ≤ 2 * c₀ * s := by
      have h1 := log_double_add_one_le hT3
      rw [Real.log_exp] at h1
      linarith
    have hlog2T_pos : 0 < Real.log (2 * T + 1) := Real.log_pos (by linarith)
    have hdL : 2 * s ≤ d * L := by
      have hw := hS_width T (hSwidth.trans hS_le_T)
      have hden : 8 * Real.log (2 * T + 1) ≤ min δ 1 * s / 2 := by
        calc 8 * Real.log (2 * T + 1) ≤ 16 * c₀ * s := by linarith
          _ = min δ 1 * s / 2 := by simp only [c₀]; ring
      have hd_ge : 2 / s ≤ d := by
        calc 2 / s = min δ 1 / (min δ 1 * s / 2) := by field_simp [hmin0.ne']
          _ ≤ min δ 1 / (8 * Real.log (2 * T + 1)) :=
              div_le_div_of_nonneg_left hmin0.le (by positivity) hden
          _ ≤ d := hw
      calc 2 * s = (2 / s) * s ^ 2 := by field_simp [hs0.ne']
        _ ≤ d * s ^ 2 := mul_le_mul_of_nonneg_right hd_ge (sq_nonneg s)
        _ = d * L := by rw [hs_sq]
    have hcost_exp : narainVKCost T ≤ D_vk * Real.exp (s / 2) := by
      have hc1 := hS_cost T (hScost.trans hS_le_T)
      have hls : Real.log (2 * T + 1) ≤ s := by linarith [hc₀_le, hs0]
      have hp1 : Real.log (2 * T + 1) ^ (14 : ℕ) ≤ s ^ (14 : ℕ) :=
        pow_le_pow_left₀ hlog2T_pos.le hls 14
      have hp2 : s ^ (14 : ℕ) ≤ (30 : ℝ) ^ (14 : ℕ) * Real.exp (s / 2) := by
        have hdom := pow_le_succ_pow_mul_exp (by positivity : 0 ≤ s / 2) 14
        rw [div_pow, show ((14 : ℕ) : ℝ) + 1 = 15 by norm_num, div_le_iff₀ (by positivity)] at hdom
        calc s ^ (14 : ℕ) ≤ (15 : ℝ) ^ (14 : ℕ) * Real.exp (s / 2) * 2 ^ (14 : ℕ) := hdom
          _ = (30 : ℝ) ^ (14 : ℕ) * Real.exp (s / 2) := by
              rw [show (30 : ℝ) = 15 * 2 by norm_num, mul_pow]; ring
      calc narainVKCost T ≤ 3 ^ (7 : ℕ) * Real.log (2 * T + 1) ^ (14 : ℕ) := hc1
        _ ≤ 3 ^ (7 : ℕ) * s ^ (14 : ℕ) := mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ ≤ 3 ^ (7 : ℕ) * ((30 : ℝ) ^ (14 : ℕ) * Real.exp (s / 2)) :=
            mul_le_mul_of_nonneg_left hp2 (by positivity)
        _ = D_vk * Real.exp (s / 2) := by simp only [D_vk]; ring
    have hT_exp : T ≤ Real.exp (s / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hc₀_le, hs0]
    have hT_powK : Real.exp (4 * s) ≤ T ^ (2 * K) := by
      have heq : T ^ (2 * K) = Real.exp ((2 * (K : ℝ) * c₀) * s) := by
        simp only [T]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact Real.exp_le_exp.mpr (by nlinarith [hK_mul, hs0])
    have hT_powK1 : Real.exp (4 * s) ≤ T ^ (2 * (K - 1)) := by
      have heq : T ^ (2 * (K - 1)) = Real.exp ((2 * ((K - 1 : ℕ) : ℝ) * c₀) * s) := by
        simp only [T]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact Real.exp_le_exp.mpr (by nlinarith [hK_sub, hs0])
    have hterm1 : 2 * T * CK * narainVKCost T * Real.exp (-(d * L)) ≤
        2 * CK * D_vk * Real.exp (-s) := by
      have he1 : Real.exp (-(d * L)) ≤ Real.exp (-(2 * s)) :=
        Real.exp_le_exp.mpr (by linarith)
      calc 2 * T * CK * narainVKCost T * Real.exp (-(d * L))
          = 2 * CK * (T * (narainVKCost T * Real.exp (-(d * L)))) := by ring
        _ ≤ 2 * CK * (Real.exp (s / 2) * ((D_vk * Real.exp (s / 2)) * Real.exp (-(2 * s)))) := by
            gcongr
        _ = 2 * CK * D_vk * (Real.exp (s / 2) * Real.exp (s / 2) * Real.exp (-(2 * s))) := by ring
        _ = 2 * CK * D_vk * Real.exp (-s) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 2; ring
    have hterm2 : 2 * d * CK * narainVKCost T / T ^ (2 * K) ≤
        CK * D_vk * Real.exp (-s) := by
      have hd_half : 2 * d ≤ 1 := by linarith [hd8]
      have hinvK : (T ^ (2 * K))⁻¹ ≤ Real.exp (-(4 * s)) := by
        rw [Real.exp_neg]
        exact inv_anti₀ (Real.exp_pos _) hT_powK
      calc 2 * d * CK * narainVKCost T / T ^ (2 * K)
          = (2 * d) * CK * narainVKCost T * (T ^ (2 * K))⁻¹ := by ring
        _ ≤ 1 * CK * (D_vk * Real.exp (s / 2)) * Real.exp (-(4 * s)) := by gcongr
        _ = CK * D_vk * Real.exp (-(7 / 2 * s)) := by
            rw [one_mul, mul_assoc (CK * D_vk), ← Real.exp_add]
            congr 1; ring_nf
        _ ≤ CK * D_vk * Real.exp (-s) := by
            gcongr; linarith
    have hterm3 : B_K * I₀ / T ^ (2 * (K - 1)) ≤ B_K * I₀ * Real.exp (-s) := by
      have hinvK1 : (T ^ (2 * (K - 1)))⁻¹ ≤ Real.exp (-s) := by
        calc (T ^ (2 * (K - 1)))⁻¹ ≤ (Real.exp (4 * s))⁻¹ :=
              inv_anti₀ (Real.exp_pos _) hT_powK1
          _ = Real.exp (-(4 * s)) := (Real.exp_neg _).symm
          _ ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinvK1 (by positivity)
    have hG₀_tot : ‖∫ t : ℝ, G₀ ((t : ℂ) * Complex.I)‖ ≤
        (3 * CK * D_vk + B_K * I₀) * Real.exp (-s) := by
      rw [hsplit_int]
      refine (norm_add_le _ _).trans ?_
      calc ‖∫ t : ℝ in (-T)..T, G₀ ((t : ℂ) * Complex.I)‖ +
            ‖∫ t : ℝ in (Ioc (-T) T)ᶜ, G₀ ((t : ℂ) * Complex.I)‖
          ≤ (2 * T * CK * narainVKCost T * Real.exp (-(d * L)) +
              2 * d * CK * narainVKCost T / T ^ (2 * K)) +
            B_K * I₀ / T ^ (2 * (K - 1)) := add_le_add hrect_bd htail_bd
        _ ≤ (2 * CK * D_vk * Real.exp (-s) + CK * D_vk * Real.exp (-s)) +
            B_K * I₀ * Real.exp (-s) := add_le_add (add_le_add hterm1 hterm2) hterm3
        _ = (3 * CK * D_vk + B_K * I₀) * Real.exp (-s) := by ring
    -- Step 7: Combine `‖g y‖` with the cutoff error `‖c (e^{-y} - 1)‖ ≤ ‖c‖ y`
    have hexp_cut : ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ y := by
      rw [show ((Real.exp (-y) : ℝ) : ℂ) - 1 = ((Real.exp (-y) - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith)]
      linarith [Real.add_one_le_exp (-y)]
    have hy_le_target : y ≤ Real.exp (1 / 2) * (y ^ (1 / 2 : ℝ) * Real.exp (-s)) := by
      have hy_eq : y = Real.exp (-s ^ 2) := by
        rw [hs_sq]; simp only [L, neg_neg, Real.exp_log hy]
      rw [hy_eq, hy_half, ← hs_sq, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (s - 1)]
    have hsplit_Ay : horocycleMean (pseudoEisenstein ψ) y - c =
        g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1) := by
      simp only [g]; ring
    rw [hsplit_Ay]
    calc ‖g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1)‖
        ≤ ‖g y‖ + ‖c‖ * ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (1 / (2 * Real.pi)) * y ^ (1 / 2 : ℝ) *
            ((3 * CK * D_vk + B_K * I₀) * Real.exp (-s)) +
          ‖c‖ * (Real.exp (1 / 2) * (y ^ (1 / 2 : ℝ) * Real.exp (-s))) := by
          rw [hgy_norm]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hG₀_tot (by positivity))
            (mul_le_mul_of_nonneg_left (hexp_cut.trans hy_le_target) (norm_nonneg c))
      _ = C_rect * y ^ (1 / 2 : ℝ) * Real.exp (-s) := by simp only [C_rect]; ring
      _ ≤ C_tot * y ^ (1 / 2 : ℝ) * Real.exp (-s) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy.le _)
          simp only [C_tot]
          linarith [hC_base0, Real.exp_nonneg (L₀ / 2 + Real.sqrt L₀)]

/-- **Unconditional stretched-exponential super-square-root thermalization.** Every smooth compactly
supported profile above height `1` thermalizes at rate `y^{1/2} exp(-√(-log y))` on `(0, 1]`. -/
theorem horocycle_rate_stretched_exp {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤
        C * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y)) := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
  obtain ⟨C, hC, hbd⟩ := norm_horocycleMean_sub_le_stretched_exp_test hψ ha
  rw [residueConst_eq] at hbd
  exact ⟨C, hC, hbd⟩

/-- **Stretched-exponential rate for smoothed Farey counts.** -/
theorem fareyCount_rate_stretched_exp {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖fareyCount (fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤
        C * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y)) := by
  obtain ⟨C, hC, hbd⟩ := horocycle_rate_stretched_exp hφ hc hs
  exact ⟨C, hC, fun y hy hy1 => by
    rw [← horocycleMean_eq_fareyCount hφ hc hs hy hy1]
    exact hbd y hy hy1⟩

/-- **Exact unconditional `O(y^{1/2})` thermalization (no `-ε` loss).** -/
theorem horocycle_rate_sqrt_exact {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C * y ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbd⟩ := horocycle_rate_stretched_exp hφ hc hs
  refine ⟨C, hC, fun y hy hy1 => (hbd y hy hy1).trans ?_⟩
  have hexp : Real.exp (-Real.sqrt (-Real.log y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
  calc C * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y))
      ≤ C * y ^ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hC.le (Real.rpow_nonneg hy.le _))
    _ = C * y ^ (1 / 2 : ℝ) := mul_one _

/-- **Every logarithmic power saving beyond `y^{1/2}` holds unconditionally** for smooth profiles
above height `1`. -/
theorem horocycle_rate_log_pow {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioi 1) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y < 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ * (-Real.log y) ^ A ≤
        C * y ^ (1 / 2 : ℝ) := by
  obtain ⟨C₀, hC₀, hbd⟩ := horocycle_rate_stretched_exp hφ hc hs
  refine ⟨C₀ * (((2 * A : ℕ) : ℝ) + 1) ^ (2 * A), by positivity, fun y hy hy1 => ?_⟩
  have hL0 : 0 ≤ -Real.log y := neg_nonneg.mpr (Real.log_nonpos hy.le hy1.le)
  have hpow : (-Real.log y) ^ A ≤
      (((2 * A : ℕ) : ℝ) + 1) ^ (2 * A) * Real.exp (Real.sqrt (-Real.log y)) := by
    have hsq : (-Real.log y) ^ A = Real.sqrt (-Real.log y) ^ (2 * A) := by
      rw [pow_mul, Real.sq_sqrt hL0]
    rw [hsq]
    exact pow_le_succ_pow_mul_exp (Real.sqrt_nonneg _) (2 * A)
  calc ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
          6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ * (-Real.log y) ^ A
      ≤ (C₀ * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y))) *
          ((((2 * A : ℕ) : ℝ) + 1) ^ (2 * A) * Real.exp (Real.sqrt (-Real.log y))) :=
        mul_le_mul (hbd y hy hy1.le) hpow (pow_nonneg hL0 A) (by positivity)
    _ = C₀ * (((2 * A : ℕ) : ℝ) + 1) ^ (2 * A) * y ^ (1 / 2 : ℝ) *
          (Real.exp (-Real.sqrt (-Real.log y)) * Real.exp (Real.sqrt (-Real.log y))) := by ring
    _ = C₀ * (((2 * A : ℕ) : ℝ) + 1) ^ (2 * A) * y ^ (1 / 2 : ℝ) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- **Unconditional `o(y^{1/2})` decay.** Every smooth horocycle mean beats `y^{1/2}` as `y → 0⁺`. -/
theorem horocycle_div_sqrt_tendsto_zero {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1) :
    Tendsto (fun y : ℝ =>
      (horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)) / ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := horocycle_rate_log_pow hφ hc hs 1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : 0 < Real.exp (-(C / ε)) := Real.exp_pos _
  filter_upwards [Ioo_mem_nhdsGT (lt_min hsmall one_pos)] with y hy
  have hy0 : 0 < y := hy.1
  have hy_exp : y < Real.exp (-(C / ε)) := hy.2.trans_le (min_le_left _ _)
  have hy1 : y < 1 := hy.2.trans_le (min_le_right _ _)
  have hlog : C / ε < -Real.log y := by
    have h := Real.log_lt_log hy0 hy_exp
    rw [Real.log_exp] at h
    linarith
  have hLpos : 0 < -Real.log y := lt_trans (div_pos hC hε) hlog
  have h1 := hbd y hy0 hy1
  rw [pow_one] at h1
  have hrp : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hrp.le, div_lt_iff₀ hrp]
  have h2 : ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
      6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C / (-Real.log y) * y ^ (1 / 2 : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hLpos]
    exact h1
  have h3 : C / (-Real.log y) < ε := (div_lt_iff₀ hLpos).mpr ((div_lt_iff₀ hε).mp hlog)
  calc ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
          6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖
      ≤ C / (-Real.log y) * y ^ (1 / 2 : ℝ) := h2
    _ < ε * y ^ (1 / 2 : ℝ) := mul_lt_mul_of_pos_right h3 hrp

/-! ### 3. Unconditional log-free `O(y^{1/2})` rate for sharp shells -/

/-- Elementary partial sum bound `∑_{1 ≤ d ≤ D} 1 / √d ≤ 2 √D`. -/
theorem sum_Icc_one_div_sqrt_le (D : ℕ) :
    ∑ d ∈ Icc 1 D, 1 / Real.sqrt d ≤ 2 * Real.sqrt D := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs1 : 0 < Real.sqrt ((D + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hle : Real.sqrt (D : ℝ) ≤ Real.sqrt ((D + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ D)
    have hprod : (Real.sqrt ((D + 1 : ℕ) : ℝ) - Real.sqrt (D : ℝ)) *
        (Real.sqrt ((D + 1 : ℕ) : ℝ) + Real.sqrt (D : ℝ)) = 1 := by
      have hsq1 : Real.sqrt ((D + 1 : ℕ) : ℝ) ^ 2 = (D : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hsq0 : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) := Real.sq_sqrt (Nat.cast_nonneg D)
      nlinarith
    have hstep : 1 / Real.sqrt ((D + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((D + 1 : ℕ) : ℝ) - Real.sqrt (D : ℝ)) := by
      rw [div_le_iff₀ hs1]
      nlinarith [hle, hprod]
    linarith

/-- **Algebraic concavity bound on the quarter-disc remainder:** `|E(Y)| ≤ 8 √Y` for all `Y ≥ 0`.
On each unit interval `[k, k + 1]` with `k + 1 ≤ ⌊Y⌋ - 1`, `f(x) = √(Y² - x²)` lies above its
secant line and within `(k + 1)/f(k + 1) - k/f(k)` of it, so the trapezoidal defects telescope to
`N / √(Y² - N²) ≤ √Y`. -/
theorem abs_circleRemainder_le_sqrt {Y : ℝ} (hY : 0 ≤ Y) :
    |circleRemainder Y| ≤ 8 * Real.sqrt Y := by
  rcases lt_or_ge Y 2 with hY2 | hY2
  · have hb := abs_circleRemainder_le hY
    have hsq2 : Real.sqrt Y ≤ 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by linarith⟩
    have hY_le : Y ≤ 2 * Real.sqrt Y := by
      calc Y = Real.sqrt Y * Real.sqrt Y := (Real.mul_self_sqrt hY).symm
        _ ≤ 2 * Real.sqrt Y := mul_le_mul_of_nonneg_right hsq2 (Real.sqrt_nonneg Y)
    linarith [Real.sqrt_nonneg Y]
  · have hfl2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY2)
    set N : ℕ := ⌊Y⌋₊ - 1
    have hN1 : 1 ≤ N := by omega
    have hfl_eq : ⌊Y⌋₊ = N + 1 := by omega
    have hNY1 : (N : ℝ) + 1 ≤ Y := by
      have h := Nat.floor_le hY
      rw [hfl_eq] at h
      push_cast at h
      exact h
    have hYN2 : Y < (N : ℝ) + 2 := by
      have h := Nat.lt_floor_add_one Y
      rw [hfl_eq] at h
      push_cast at h
      linarith
    set f : ℝ → ℝ := fun x => Real.sqrt (Y ^ 2 - x ^ 2)
    have hf_pos : ∀ x : ℝ, 0 ≤ x → x ≤ N → 0 < f x := by
      intro x hx0 hxN
      apply Real.sqrt_pos.mpr
      have hx2 : x ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hx0 hxN 2
      have hN2 : (N : ℝ) ^ 2 ≤ (Y - 1) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) 2
      nlinarith
    have hunit : ∀ k ∈ range N,
        0 ≤ (∫ x in (k : ℝ)..((k : ℝ) + 1), f x) - (f k + f ((k : ℝ) + 1)) / 2 ∧
        (∫ x in (k : ℝ)..((k : ℝ) + 1), f x) - (f k + f ((k : ℝ) + 1)) / 2 ≤
          ((k : ℝ) + 1) / f ((k : ℝ) + 1) - (k : ℝ) / f k := by
      intro k hk
      have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
      have hkR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hkN
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      set A : ℝ := f k
      set B : ℝ := f ((k : ℝ) + 1)
      have hA : 0 < A := hf_pos k hk0 (by linarith)
      have hB : 0 < B := hf_pos ((k : ℝ) + 1) (by positivity) hkR
      have hA2 : A ^ 2 = Y ^ 2 - (k : ℝ) ^ 2 :=
        Real.sq_sqrt (by have := hA; exact (Real.sqrt_pos.mp this).le)
      have hB2 : B ^ 2 = Y ^ 2 - ((k : ℝ) + 1) ^ 2 :=
        Real.sq_sqrt (by have := hB; exact (Real.sqrt_pos.mp this).le)
      have hBA : B ≤ A := antitoneOn_disc Y hk0 (by positivity) (by linarith)
      set L_sec : ℝ → ℝ := fun x => ((k : ℝ) + 1 - x) * A + (x - (k : ℝ)) * B
      have hpt : ∀ x ∈ Icc (k : ℝ) ((k : ℝ) + 1),
          L_sec x ≤ f x ∧ f x - L_sec x ≤ ((k : ℝ) + 1) / B - (k : ℝ) / A := by
        intro x hx
        set t : ℝ := x - k
        have ht0 : 0 ≤ t := by simp only [t]; linarith [hx.1]
        have ht1 : 0 ≤ 1 - t := by simp only [t]; linarith [hx.2]
        have hx_eq : x = (k : ℝ) + t := by simp only [t]; ring
        have hfx0 : 0 < f x := hf_pos x (hx.1.trans' hk0) (hx.2.trans hkR)
        have hfx2 : f x ^ 2 = Y ^ 2 - x ^ 2 :=
          Real.sq_sqrt (Real.sqrt_pos.mp hfx0).le
        have hL_nn : 0 ≤ L_sec x := by
          have : L_sec x = (1 - t) * A + t * B := by simp only [L_sec, t]; ring
          rw [this]; positivity
        have hdiff_sq : f x ^ 2 - L_sec x ^ 2 = t * (1 - t) * (1 + (A - B) ^ 2) := by
          simp only [L_sec]
          linear_combination hfx2 - (1 - t) * hA2 - t * hB2 - (2 * (k : ℝ) + t + 1 - 1) * 0 +
            (show -(x ^ 2) + (1 - t) * (k : ℝ) ^ 2 + t * ((k : ℝ) + 1) ^ 2 =
              t * (1 - t) by rw [hx_eq]; ring) +
            (show -(((k : ℝ) + 1 - x) * A + (x - (k : ℝ)) * B) ^ 2 + (1 - t) * A ^ 2 + t * B ^ 2 =
              t * (1 - t) * (A - B) ^ 2 by rw [hx_eq]; ring)
        have hlo : L_sec x ≤ f x := by
          nlinarith [hdiff_sq, mul_nonneg ht0 ht1, sq_nonneg (A - B), hL_nn, hfx0.le]
        -- Upper bound via the two endpoint chords
        have hfx_le_A : f x ≤ A := antitoneOn_disc Y hk0 (hx.1.trans' hk0) hx.1
        have hB_le_fx : B ≤ f x := antitoneOn_disc Y (hx.1.trans' hk0) (by positivity) hx.2
        have hch1 : f x ≤ A - ((k : ℝ) / A) * t := by
          have h1 : 2 * (k : ℝ) * t ≤ (A - f x) * (2 * A) := by
            have hid : (A - f x) * (A + f x) = 2 * (k : ℝ) * t + t ^ 2 := by
              linear_combination hA2 - hfx2 + (show x ^ 2 - (k : ℝ) ^ 2 = 2 * (k : ℝ) * t + t ^ 2 by
                rw [hx_eq]; ring)
            nlinarith [sq_nonneg t, hfx_le_A]
          have h2 : ((k : ℝ) / A) * t ≤ A - f x := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hA]
            linarith
          linarith
        have hch2 : f x ≤ B + (((k : ℝ) + 1) / B) * (1 - t) := by
          have h1 : (f x - B) * (2 * B) ≤ 2 * ((k : ℝ) + 1) * (1 - t) := by
            have hid : (f x - B) * (f x + B) = (1 - t) * (2 * (k : ℝ) + 1 + t) := by
              linear_combination hfx2 - hB2 +
                (show ((k : ℝ) + 1) ^ 2 - x ^ 2 = (1 - t) * (2 * (k : ℝ) + 1 + t) by
                  rw [hx_eq]; ring)
            nlinarith [ht1, B, hB_le_fx]
          have h2 : f x - B ≤ (((k : ℝ) + 1) / B) * (1 - t) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hB]
            linarith
          linarith
        have hslope_nn : 0 ≤ ((k : ℝ) + 1) / B - (k : ℝ) / A := by
          have : (k : ℝ) / A ≤ ((k : ℝ) + 1) / B :=
            div_le_div₀ (by positivity) (by linarith) hB hBA
          linarith
        have hcomb : f x - L_sec x ≤ t * (1 - t) * (((k : ℝ) + 1) / B - (k : ℝ) / A) := by
          have hL_t : L_sec x = (1 - t) * A + t * B := by simp only [L_sec, t]; ring
          have h1 := mul_le_mul_of_nonneg_left hch1 ht1
          have h2 := mul_le_mul_of_nonneg_left hch2 ht0
          nlinarith [hL_t, h1, h2]
        have ht_prod : t * (1 - t) ≤ 1 := by nlinarith [ht0, ht1]
        exact ⟨hlo, hcomb.trans (by nlinarith [hslope_nn, ht_prod])⟩
      -- Integrate `L_sec` and `f` on `[k, k + 1]`
      have hint_L : ∫ x in (k : ℝ)..((k : ℝ) + 1), L_sec x = (A + B) / 2 := by
        set P : ℝ → ℝ := fun x =>
          -(((k : ℝ) + 1 - x) ^ 2 / 2) * A + ((x - (k : ℝ)) ^ 2 / 2) * B
        have hdP : ∀ x ∈ uIcc (k : ℝ) ((k : ℝ) + 1), HasDerivAt P (L_sec x) x := by
          intro x _
          have h1 : HasDerivAt (fun x : ℝ => (k : ℝ) + 1 - x) (-1) x := by
            simpa using (hasDerivAt_id x).const_sub ((k : ℝ) + 1)
          have h2 : HasDerivAt (fun x : ℝ => x - (k : ℝ)) 1 x := by
            simpa using (hasDerivAt_id x).sub_const (k : ℝ)
          have hd := (((h1.pow 2).div_const 2).neg.mul_const A).add
            (((h2.pow 2).div_const 2).mul_const B)
          exact hd.congr_deriv (by simp only [L_sec]; ring)
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdP
          (by unfold L_sec; exact (by fun_prop : Continuous _).intervalIntegrable _ _)]
        simp only [P]
        ring
      have hf_cont : Continuous f := by unfold f; fun_prop
      have hL_cont : Continuous L_sec := by unfold L_sec; fun_prop
      have hlo_int := intervalIntegral.integral_mono_on (by linarith)
        (hL_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)
        fun x hx => (hpt x hx).1
      have hhi_int := intervalIntegral.integral_mono_on (by linarith)
        ((hf_cont.sub hL_cont).intervalIntegrable _ _) intervalIntegrable_const
        fun x hx => (hpt x hx).2
      rw [intervalIntegral.integral_sub (hf_cont.intervalIntegrable _ _)
        (hL_cont.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, hint_L]
        at hhi_int
      rw [hint_L] at hlo_int
      exact ⟨by linarith, by linarith⟩
    -- Sum over `k ∈ range N`
    have hf_cont : Continuous f := by unfold f; fun_prop
    have hsum_int : ∑ k ∈ range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), f x =
        ∫ x in (0 : ℝ)..(N : ℝ), f x := by
      have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
        (k := N) fun k _ => hf_cont.intervalIntegrable _ _
      simpa [Nat.cast_add, Nat.cast_one] using h
    have hsum_err : ∑ k ∈ range N, (((k : ℝ) + 1) / f ((k : ℝ) + 1) - (k : ℝ) / f k) =
        (N : ℝ) / f N := by
      have h := Finset.sum_range_sub (fun k : ℕ => (k : ℝ) / f k) N
      simpa [Nat.cast_add, Nat.cast_one] using h
    have htrap_lo : 0 ≤ (∫ x in (0 : ℝ)..(N : ℝ), f x) -
        ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2 := by
      rw [← hsum_int, ← Finset.sum_sub_distrib]
      exact Finset.sum_nonneg fun k hk => (hunit k hk).1
    have htrap_hi : (∫ x in (0 : ℝ)..(N : ℝ), f x) -
        ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2 ≤ (N : ℝ) / f N := by
      rw [← hsum_int, ← Finset.sum_sub_distrib, ← hsum_err]
      exact Finset.sum_le_sum fun k hk => (hunit k hk).2
    -- Bound `(N : ℝ) / f N ≤ √Y` and the boundary `[N, Y]` pieces
    have hfN_ge : Real.sqrt Y ≤ f N := by
      apply Real.sqrt_le_sqrt
      have hN2 : (N : ℝ) ^ 2 ≤ (Y - 1) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) 2
      nlinarith
    have hNfN_le : (N : ℝ) / f N ≤ Real.sqrt Y := by
      have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr (by linarith)
      calc (N : ℝ) / f N ≤ Y / Real.sqrt Y :=
            div_le_div₀ (by linarith) (by linarith) hsY0 hfN_ge
        _ = Real.sqrt Y := by
            rw [div_eq_iff hsY0.ne', Real.mul_self_sqrt hY]
    have hfN_le : f N ≤ 2 * Real.sqrt Y := by
      have h1 : Y ^ 2 - (N : ℝ) ^ 2 ≤ 4 * Y := by
        have : (Y - 2) ^ 2 ≤ (N : ℝ) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        nlinarith
      calc f N ≤ Real.sqrt (4 * Y) := Real.sqrt_le_sqrt h1
        _ = 2 * Real.sqrt Y := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
    have hfN1_le : f ((N : ℝ) + 1) ≤ 2 * Real.sqrt Y :=
      (antitoneOn_disc Y (Nat.cast_nonneg N) (by positivity) (by linarith)).trans hfN_le
    have hfN1_nn : 0 ≤ f ((N : ℝ) + 1) := Real.sqrt_nonneg _
    have hfN_nn : 0 ≤ f N := Real.sqrt_nonneg _
    have hint_tail_nn : 0 ≤ ∫ x in (N : ℝ)..Y, f x :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => Real.sqrt_nonneg _
    have hint_tail_le : ∫ x in (N : ℝ)..Y, f x ≤ 4 * Real.sqrt Y := by
      have hm := intervalIntegral.integral_mono_on (by linarith : (N : ℝ) ≤ Y)
        (hf_cont.intervalIntegrable _ _) intervalIntegrable_const
        fun x hx => (antitoneOn_disc Y (Nat.cast_nonneg N) (hx.1.trans' (Nat.cast_nonneg N)) hx.1).trans hfN_le
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      calc ∫ x in (N : ℝ)..Y, f x ≤ (Y - (N : ℝ)) * (2 * Real.sqrt Y) := hm
        _ ≤ 2 * (2 * Real.sqrt Y) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 4 * Real.sqrt Y := by ring
    -- Express `circleRemainder Y` via the trapezoidal sum and `[N, Y]` boundary
    have harea : Real.pi * Y ^ 2 / 4 =
        (∫ x in (0 : ℝ)..(N : ℝ), f x) + ∫ x in (N : ℝ)..Y, f x := by
      rw [← integral_disc hY le_rfl,
        ← intervalIntegral.integral_add_adjacent_intervals (b := (N : ℝ))
          (hf_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)]
    have htrap_sum : ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2 =
        Y / 2 + quarterDisc Y ⌊Y⌋₊ - f ((N : ℝ) + 1) - f N / 2 := by
      have hs1 := Finset.sum_range_succ (fun k : ℕ => f k) N
      have hs2 := Finset.sum_range_succ' (fun k : ℕ => f k) N
      have hf0 : f (0 : ℕ) = Y := by
        simp only [f, Nat.cast_zero]
        rw [show Y ^ 2 - (0 : ℝ) ^ 2 = Y ^ 2 by ring, Real.sqrt_sq hY]
      have hqd : quarterDisc Y ⌊Y⌋₊ =
          (∑ k ∈ range N, f ((k + 1 : ℕ) : ℝ)) + f ((N : ℝ) + 1) := by
        rw [hfl_eq, quarterDisc, sum_Icc_eq_sum_range, Finset.sum_range_succ]
        simp [f, Nat.cast_add, Nat.cast_one]
      have hhalves : 2 * ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2 =
          (∑ k ∈ range N, f k) + ∑ k ∈ range N, f ((k + 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Nat.cast_add, Nat.cast_one]
        ring
      linarith
    have hrem_id : circleRemainder Y =
        -(∫ x in (0 : ℝ)..(N : ℝ), f x - ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2) +
          f ((N : ℝ) + 1) + f N / 2 - ∫ x in (N : ℝ)..Y, f x := by
      unfold circleRemainder
      linarith [harea, htrap_sum]
    rw [hrem_id, abs_le]
    constructor <;> linarith [htrap_lo, htrap_hi, hNfN_le, hfN_le, hfN1_le, hfN1_nn, hfN_nn,
      hint_tail_nn, hint_tail_le, Real.sqrt_nonneg Y]

/-- Terms in `horoballSum X N` beyond `⌊X⌋₊` vanish identically. -/
theorem horoballSum_eq_horoballSum_floor {X : ℝ} (hX : 0 ≤ X) {N : ℕ} (hN : ⌊X⌋₊ ≤ N) :
    horoballSum X N = horoballSum X ⌊X⌋₊ := by
  unfold horoballSum
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hN)]
  intro c hc hnot
  simp only [Finset.mem_Icc, not_and, not_le] at hc hnot
  have hcX : X < c := by
    have h1 := Nat.lt_floor_add_one X
    have h2 : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ c := by exact_mod_cast hnot hc.1
    push_cast at h2
    linarith
  have hc0 : (0 : ℝ) < c := Nat.cast_pos.mpr hc.1
  have hdiv : X / c < 1 := (div_lt_one hc0).mpr hcX
  have hdiv0 : 0 ≤ X / c := div_nonneg hX hc0.le
  rw [Real.sqrt_eq_zero'.mpr (by nlinarith), mul_zero]

/-- **Log-free linear remainder bound for the horoball profile:**
`|H(X) - 3/(2π) X²| ≤ 19 X` for all `X ≥ 1` and `N ≥ X`. -/
theorem abs_horoballSum_sub_le_linear {X : ℝ} (hX : 1 ≤ X) {N : ℕ} (hN : X ≤ N) :
    |horoballSum X N - 3 / (2 * Real.pi) * X ^ 2| ≤ 19 * X := by
  have hX0 : 0 ≤ X := by linarith
  set D := ⌊X⌋₊
  have hD1 : 1 ≤ D := Nat.le_floor (by exact_mod_cast hX)
  have hDX : (D : ℝ) ≤ X := Nat.floor_le hX0
  have hXD : X < (D : ℝ) + 1 := Nat.lt_floor_add_one X
  rw [horoballSum_decomposition hX0 hN]
  have hT1 : |∑ d ∈ Icc 1 D, (μ d : ℝ) * circleRemainder (X / d)| ≤ 16 * X := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ d ∈ Icc 1 D,
        |(μ d : ℝ) * circleRemainder (X / d)| ≤ 8 * Real.sqrt X * (1 / Real.sqrt d) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp hd).1
      have hμ : |(μ d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      rw [abs_mul]
      calc |(μ d : ℝ)| * |circleRemainder (X / d)|
          ≤ 1 * (8 * Real.sqrt (X / d)) :=
            mul_le_mul hμ (abs_circleRemainder_le_sqrt (div_nonneg hX0 hd0.le))
              (abs_nonneg _) zero_le_one
        _ = 8 * Real.sqrt X * (1 / Real.sqrt d) := by
            rw [one_mul, Real.sqrt_div hX0]
            ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    calc 8 * Real.sqrt X * ∑ d ∈ Icc 1 D, 1 / Real.sqrt d
        ≤ 8 * Real.sqrt X * (2 * Real.sqrt D) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_div_sqrt_le D) (by positivity)
      _ ≤ 8 * Real.sqrt X * (2 * Real.sqrt X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hDX) (by norm_num))
            (by positivity)
      _ = 16 * X := by
          rw [show 8 * Real.sqrt X * (2 * Real.sqrt X) = 16 * (Real.sqrt X * Real.sqrt X) by ring,
            Real.mul_self_sqrt hX0]
  have hT2 : |X / 2 * ∑ d ∈ Icc 1 D, (μ d : ℝ) / d| ≤ X := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hm := _root_.RHTower.abs_sum_moebius_div_le_one D hD1
    nlinarith
  have hT3 : |Real.pi / 4 * X ^ 2 * (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤
      2 * X := by
    have ht := _root_.RHTower.abs_sum_moebius_div_sq_sub_le hD1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hinv : 1 / (D : ℝ) ≤ 2 / X := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    calc Real.pi / 4 * X ^ 2 * |∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2|
        ≤ Real.pi / 4 * X ^ 2 * (2 / X) :=
          mul_le_mul_of_nonneg_left (ht.trans hinv) (by positivity)
      _ = Real.pi / 2 * X := by field_simp; norm_num
      _ ≤ 2 * X := by nlinarith [Real.pi_le_four]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_sub _ _) le_rfl).trans ?_
  linarith

/-- **Sharp shells thermalize at exact rate `O(y^{1/2})` unconditionally (no logarithmic loss).** -/
theorem shell_rate_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {y : ℝ} (hy : 0 < y)
    (hyb : y ≤ 1 / b) (hya : y < a) :
    ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y -
      ((6 / Real.pi * (1 / a - 1 / b) : ℝ) : ℂ)‖ ≤
      76 * (Real.sqrt (y / a) + Real.sqrt (y / b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set Xa := 1 / Real.sqrt (a * y)
  set Xb := 1 / Real.sqrt (b * y)
  have hay : 0 < a * y := mul_pos ha hy
  have hby : 0 < b * y := mul_pos hb hy
  have hsa : Real.sqrt (a * y) ^ 2 = a * y := Real.sq_sqrt hay.le
  have hsb : Real.sqrt (b * y) ^ 2 = b * y := Real.sq_sqrt hby.le
  have hsa0 : 0 < Real.sqrt (a * y) := Real.sqrt_pos.mpr hay
  have hsb0 : 0 < Real.sqrt (b * y) := Real.sqrt_pos.mpr hby
  have hby1 : b * y ≤ 1 := by have := (le_div_iff₀ hb).mp hyb; linarith
  have hXb : 1 ≤ Xb := by
    rw [le_div_iff₀ hsb0, one_mul]
    exact Real.sqrt_le_one.mpr hby1
  have hXab : Xb ≤ Xa := one_div_le_one_div_of_le hsa0 (Real.sqrt_le_sqrt (by nlinarith))
  have hXa : 1 ≤ Xa := hXb.trans hXab
  set C := ⌈Xa⌉₊
  have hCa : Xa ≤ C := Nat.le_ceil Xa
  have hC : 1 < ((C : ℝ) + 1) ^ 2 * a * y := by
    have h1 : Xa ^ 2 * (a * y) = 1 := by rw [div_pow, one_pow, hsa]; field_simp
    have h2 : Xa ^ 2 < ((C : ℝ) + 1) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
    nlinarith
  rw [horocycleMean_shell_eq ha hab hy hya hC, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have ha' := abs_horoballSum_sub_le_linear hXa hCa
  have hb' := abs_horoballSum_sub_le_linear hXb (hXab.trans hCa)
  have hmain : 4 * y * (3 / (2 * Real.pi) * Xa ^ 2 - 3 / (2 * Real.pi) * Xb ^ 2) =
      6 / Real.pi * (1 / a - 1 / b) := by
    simp only [Xa, Xb, div_pow, one_pow, hsa, hsb]
    field_simp
    ring
  have hya' : y * Xa = Real.sqrt (y / a) := by
    simp only [Xa]
    rw [Real.sqrt_div hy.le, mul_one_div,
      div_eq_div_iff hsa0.ne' (Real.sqrt_pos.mpr ha).ne', Real.sqrt_mul ha.le,
      ← mul_assoc, mul_comm (Real.sqrt y) (Real.sqrt a), mul_assoc, Real.mul_self_sqrt hy.le]
    ring
  have hyb' : y * Xb = Real.sqrt (y / b) := by
    simp only [Xb]
    rw [Real.sqrt_div hy.le, mul_one_div,
      div_eq_div_iff hsb0.ne' (Real.sqrt_pos.mpr hb).ne', Real.sqrt_mul hb.le,
      ← mul_assoc, mul_comm (Real.sqrt y) (Real.sqrt b), mul_assoc, Real.mul_self_sqrt hy.le]
    ring
  have key : 4 * y * (horoballSum Xa C - horoballSum Xb C) - 6 / Real.pi * (1 / a - 1 / b) =
      4 * y * (horoballSum Xa C - 3 / (2 * Real.pi) * Xa ^ 2) -
        4 * y * (horoballSum Xb C - 3 / (2 * Real.pi) * Xb ^ 2) := by
    rw [← hmain]; ring
  rw [key]
  have h4y : 0 ≤ 4 * y := by linarith
  calc _ ≤ |4 * y * (horoballSum Xa C - 3 / (2 * Real.pi) * Xa ^ 2)| +
        |4 * y * (horoballSum Xb C - 3 / (2 * Real.pi) * Xb ^ 2)| := abs_sub _ _
    _ ≤ 4 * y * (19 * Xa) + 4 * y * (19 * Xb) := by
        rw [abs_mul (4 * y), abs_mul (4 * y), abs_of_nonneg h4y]
        exact add_le_add (mul_le_mul_of_nonneg_left ha' h4y) (mul_le_mul_of_nonneg_left hb' h4y)
    _ = 76 * (Real.sqrt (y / a) + Real.sqrt (y / b)) := by
        linear_combination 76 * hya' + 76 * hyb'

/-! ### 4. Single-shell converse and exact RH × Möbius-circle characterization -/

/-- Left-shifted continuous unit ramp on `[c - ε, c]`. -/
private def leftRamp (c ε t : ℝ) : ℝ := min 1 (max 0 ((t - (c - ε)) / ε))

/-- Continuous left-shifted trapezoidal approximant to `1_{[a, b)}`. Because both ramps sit on the
left of the endpoints `a` and `b`, `shellTrap a b ε t` converges pointwise to `1_{[a, b)}(t)` at
every real `t`, including both endpoints `a` and `b`. -/
private def shellTrap (a b ε t : ℝ) : ℝ := leftRamp a ε t - leftRamp b ε t

private theorem continuous_shellTrap (a b ε : ℝ) : Continuous (shellTrap a b ε) := by
  unfold shellTrap leftRamp
  fun_prop

private theorem shellTrap_bounds {a b ε : ℝ} (hε : 0 < ε) (hεba : ε ≤ b - a) (t : ℝ) :
    0 ≤ shellTrap a b ε t ∧ shellTrap a b ε t ≤ 1 := by
  unfold shellTrap leftRamp
  have h1 : max 0 ((t - (b - ε)) / ε) ≤ max 0 ((t - (a - ε)) / ε) := by
    refine max_le_max le_rfl ?_
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hle : min 1 (max 0 ((t - (b - ε)) / ε)) ≤ min 1 (max 0 ((t - (a - ε)) / ε)) :=
    min_le_min le_rfl h1
  have hge0 : 0 ≤ min 1 (max 0 ((t - (b - ε)) / ε)) := le_min zero_le_one (le_max_left _ _)
  have hle1 : min 1 (max 0 ((t - (a - ε)) / ε)) ≤ 1 := min_le_left _ _
  constructor <;> linarith

private theorem shellTrap_eq_zero_of_lt {a b ε t : ℝ} (hε : 0 < ε) (hεba : ε ≤ b - a)
    (ht : t < a - ε) : shellTrap a b ε t = 0 := by
  unfold shellTrap leftRamp
  have h1 : (t - (a - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have h2 : (t - (b - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [max_eq_left h1, max_eq_left h2, min_eq_right zero_le_one]
  ring

private theorem shellTrap_eq_zero_of_ge {a b ε t : ℝ} (hε : 0 < ε) (hεba : ε ≤ b - a)
    (ht : b ≤ t) : shellTrap a b ε t = 0 := by
  unfold shellTrap leftRamp
  have h1 : 1 ≤ (t - (a - ε)) / ε := (le_div_iff₀ hε).mpr (by linarith)
  have h2 : 1 ≤ (t - (b - ε)) / ε := (le_div_iff₀ hε).mpr (by linarith)
  rw [max_eq_right (zero_le_one.trans h1), max_eq_right (zero_le_one.trans h2),
    min_eq_left h1, min_eq_left h2]
  ring

private theorem shellTrap_eq_one_of_mem {a b ε t : ℝ} (hε : 0 < ε) (hta : a ≤ t)
    (htb : t ≤ b - ε) : shellTrap a b ε t = 1 := by
  unfold shellTrap leftRamp
  have h1 : 1 ≤ (t - (a - ε)) / ε := (le_div_iff₀ hε).mpr (by linarith)
  have h2 : (t - (b - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1,
    max_eq_left h2, min_eq_right zero_le_one]
  ring

/-- Pointwise eventual equality `shellTrap a b (δ₀ / (n + 1)) t = 1_{[a, b)}(t)` at every `t : ℝ`. -/
private theorem eventually_shellTrap_eq_indicator {a b δ₀ : ℝ} (hab : a < b) (hδ0 : 0 < δ₀)
    (hδba : δ₀ ≤ (b - a) / 2) (t : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ((shellTrap a b (δ₀ / ((n : ℝ) + 1)) t : ℝ) : ℂ) = (Ico a b).indicator 1 t := by
  have hε_pos : ∀ n : ℕ, 0 < δ₀ / ((n : ℝ) + 1) := fun n => div_pos hδ0 (by positivity)
  have hε_ba : ∀ n : ℕ, δ₀ / ((n : ℝ) + 1) ≤ b - a := fun n => by
    have h1 : δ₀ / ((n : ℝ) + 1) ≤ δ₀ := div_le_self hδ0.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  rcases lt_or_ge t a with hta | hta
  · obtain ⟨N, hN⟩ := exists_nat_gt (δ₀ / (a - t))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpos : 0 < a - t := by linarith
    have hlt : δ₀ / ((n : ℝ) + 1) < a - t := by
      rw [div_lt_iff₀ (by positivity)]
      have hN' : δ₀ < (N : ℝ) * (a - t) := (div_lt_iff₀ hpos).mp hN
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    rw [shellTrap_eq_zero_of_lt (hε_pos n) (hε_ba n) (by linarith),
      Set.indicator_of_notMem (fun h => by linarith [h.1])]
    simp
  · rcases lt_or_ge t b with htb | htb
    · obtain ⟨N, hN⟩ := exists_nat_gt (δ₀ / (b - t))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hpos : 0 < b - t := by linarith
      have hle : δ₀ / ((n : ℝ) + 1) ≤ b - t := by
        rw [div_le_iff₀ (by positivity)]
        have hN' : δ₀ < (N : ℝ) * (b - t) := (div_lt_iff₀ hpos).mp hN
        have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      rw [shellTrap_eq_one_of_mem (hε_pos n) hta (by linarith),
        Set.indicator_of_mem ⟨hta, htb⟩]
      simp
    · filter_upwards with n
      rw [shellTrap_eq_zero_of_ge (hε_pos n) (hε_ba n) htb,
        Set.indicator_of_notMem (fun h => by linarith [h.2])]
      simp

/-- Mellin convergence and unfolding identity for a single sharp shell `1 < a < b`, obtained by
passing the continuous trapezoidal approximants `shellTrap` through `mellin_horocycleMean`. -/
private theorem mellin_horocycleMean_shell {a b : ℝ} (ha : 1 < a) (hab : a < b)
    {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (horocycleMean (pseudoEisenstein ((Ico a b).indicator 1))) (s - 1) ∧
    mellin (horocycleMean (pseudoEisenstein ((Ico a b).indicator 1))) (s - 1) =
      2 * mellin ((Ico a b).indicator (1 : ℝ → ℂ)) (s - 1) +
        2 * (msB (s - 1 / 2) / msA (s - 1 / 2)) *
          mellin ((Ico a b).indicator (1 : ℝ → ℂ)) (-s) := by
  classical
  set ψ_sh : ℝ → ℂ := (Ico a b).indicator 1
  set δ₀ : ℝ := min ((a - 1) / 2) ((b - a) / 2)
  have hδ0 : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hδa : δ₀ ≤ (a - 1) / 2 := min_le_left _ _
  have hδba : δ₀ ≤ (b - a) / 2 := min_le_right _ _
  set a₀ : ℝ := (a + 1) / 2
  have ha₀1 : 1 < a₀ := by simp only [a₀]; linarith
  have ha₀0 : 0 < a₀ := by linarith
  set ψn : ℕ → ℝ → ℂ := fun n t => ((shellTrap a b (δ₀ / ((n : ℝ) + 1)) t : ℝ) : ℂ)
  have hψn_cont : ∀ n, Continuous (ψn n) := fun n =>
    Complex.continuous_ofReal.comp (continuous_shellTrap a b _)
  have hψn_a₀ : ∀ n t, t < a₀ → ψn n t = 0 := by
    intro n t ht
    have hε0 : 0 < δ₀ / ((n : ℝ) + 1) := div_pos hδ0 (by positivity)
    have hε_le : δ₀ / ((n : ℝ) + 1) ≤ δ₀ :=
      div_le_self hδ0.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    simp only [ψn]
    rw [shellTrap_eq_zero_of_lt hε0 (by linarith) (by simp only [a₀] at ht; linarith)]
    simp
  have hψn_b : ∀ n t, b < t → ψn n t = 0 := by
    intro n t ht
    have hε0 : 0 < δ₀ / ((n : ℝ) + 1) := div_pos hδ0 (by positivity)
    have hε_le : δ₀ / ((n : ℝ) + 1) ≤ δ₀ :=
      div_le_self hδ0.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    simp only [ψn]
    rw [shellTrap_eq_zero_of_ge hε0 (by linarith) ht.le]
    simp
  have hψn_norm : ∀ n t, ‖ψn n t‖ ≤ 1 := by
    intro n t
    have hε0 : 0 < δ₀ / ((n : ℝ) + 1) := div_pos hδ0 (by positivity)
    have hε_le : δ₀ / ((n : ℝ) + 1) ≤ δ₀ :=
      div_le_self hδ0.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    obtain ⟨h0, h1⟩ := shellTrap_bounds (a := a) (b := b) hε0 (by linarith) t
    simp only [ψn, Complex.norm_real, Real.norm_of_nonneg h0]
    exact h1
  have hψsh_a₀ : ∀ t, t < a₀ → ψ_sh t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => by simp only [a₀] at ht; linarith [h.1]) _
  have hψsh_b : ∀ t, b < t → ψ_sh t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hψsh_norm : ∀ t, ‖ψ_sh t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ico a b
    · simp [ψ_sh, Set.indicator_of_mem ht]
    · simp [ψ_sh, Set.indicator_of_notMem ht]
  -- Pointwise eventual equality of `pseudoEisenstein (ψn n) z` and `pseudoEisenstein ψ_sh z`
  have hpe_ev : ∀ z : UpperHalfPlane,
      ∀ᶠ n in atTop, pseudoEisenstein (ψn n) z = pseudoEisenstein ψ_sh z := by
    intro z
    have hfin := _root_.RHTower.DeckPointPair.finite_rows_im_ge (isCompact_singleton (x := z)) ha₀0
    set S := hfin.toFinset
    have hall : ∀ᶠ n in atTop, ∀ p ∈ S,
        ψn n (EisensteinSeries.gammaSetMatrix p • z).im =
          ψ_sh (EisensteinSeries.gammaSetMatrix p • z).im :=
      Filter.eventually_all_finset.mpr fun p _ =>
        eventually_shellTrap_eq_indicator hab hδ0 hδba _
    filter_upwards [hall] with n hn
    have hout_n : ∀ p ∉ S, ψn n (EisensteinSeries.gammaSetMatrix p • z).im = 0 := fun p hp =>
      hψn_a₀ n _ (lt_of_not_ge fun hge => hp (hfin.mem_toFinset.2 ⟨z, rfl, hge⟩))
    have hout_sh : ∀ p ∉ S, ψ_sh (EisensteinSeries.gammaSetMatrix p • z).im = 0 := fun p hp =>
      hψsh_a₀ _ (lt_of_not_ge fun hge => hp (hfin.mem_toFinset.2 ⟨z, rfl, hge⟩))
    rw [pseudoEisenstein_eq_sum hout_n, pseudoEisenstein_eq_sum hout_sh]
    exact Finset.sum_congr rfl hn
  -- Uniform bound `≤ 2` on `pseudoEisenstein (ψn n)` and `pseudoEisenstein ψ_sh`
  have hpe_bd_n : ∀ n z, ‖pseudoEisenstein (ψn n) z‖ ≤ 2 := by
    intro n z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    rw [← pseudoEisenstein_smul g z, pseudoEisenstein_of_mem_fd ha₀1 (hψn_a₀ n) hg, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    linarith [hψn_norm n (g • z).im]
  have hpe_bd_sh : ∀ z, ‖pseudoEisenstein ψ_sh z‖ ≤ 2 := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    rw [← pseudoEisenstein_smul g z, pseudoEisenstein_of_mem_fd ha₀1 hψsh_a₀ hg, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    linarith [hψsh_norm (g • z).im]
  -- Pointwise convergence and bounds for `horocycleMean` on `Ioi 0`
  have hm_tendsto : ∀ y : ℝ, 0 < y →
      Tendsto (fun n => horocycleMean (pseudoEisenstein (ψn n)) y) atTop
        (𝓝 (horocycleMean (pseudoEisenstein ψ_sh) y)) := by
    intro y _
    unfold horocycleMean
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
      (fun n => ((continuous_pseudoEisenstein (hψn_cont n) ha₀0 (hψn_a₀ n)).comp
        (by
          have hmk : Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
            have : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
              funext x; apply Complex.ext <;> simp
            rw [this]; fun_prop
          exact continuous_iff_continuousAt.2 fun x =>
            (UpperHalfPlane.ofComplex.continuousAt (by simp [UpperHalfPlane.ofComplex, ‹0 < y›])).comp
              hmk.continuousAt)).aestronglyMeasurable)
      (integrableOn_const (C := (2 : ℝ)) (by simp))
      (fun n => Eventually.of_forall fun x => hpe_bd_n n _)
      (Eventually.of_forall fun x =>
        tendsto_const_nhds.congr' (by
          filter_upwards [hpe_ev (UpperHalfPlane.ofComplex ⟨x, y⟩)] with n hn using hn.symm))
  set Y : ℝ := max b a₀⁻¹
  have hY0 : 0 < Y := lt_of_lt_of_le (inv_pos.2 ha₀0) (le_max_right _ _)
  have hm_zero_n : ∀ n, ∀ y : ℝ, Y < y → horocycleMean (pseudoEisenstein (ψn n)) y = 0 :=
    fun n y hy => horocycleMean_eq_zero_of_gt ha₀0 (hψn_a₀ n) (hψn_b n) hy
  have hm_zero_sh : ∀ y : ℝ, Y < y → horocycleMean (pseudoEisenstein ψ_sh) y = 0 :=
    fun y hy => horocycleMean_eq_zero_of_gt ha₀0 hψsh_a₀ hψsh_b hy
  have hm_norm_n : ∀ n, ∀ y : ℝ, ‖horocycleMean (pseudoEisenstein (ψn n)) y‖ ≤ 2 := by
    intro n y
    unfold horocycleMean
    refine (norm_setIntegral_le_of_norm_le_const (by simp) fun x _ => hpe_bd_n n _).trans ?_
    simp
  have hm_norm_sh : ∀ y : ℝ, ‖horocycleMean (pseudoEisenstein ψ_sh) y‖ ≤ 2 := by
    intro y
    unfold horocycleMean
    refine (norm_setIntegral_le_of_norm_le_const (by simp) fun x _ => hpe_bd_sh _).trans ?_
    simp
  -- Dominated convergence for `mellin (horocycleMean ... ) (s - 1)` on `Ioi 0`
  set dom : ℝ → ℝ := (Ioc 0 Y).indicator fun y => 2 * y ^ (s.re - 2)
  have hdom_int : IntegrableOn dom (Ioi 0) volume := by
    have h1 : IntegrableOn (fun y : ℝ => 2 * y ^ (s.re - 2)) (Ioc 0 Y) volume :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := s.re - 2)
        (by linarith)).1.const_mul 2
    exact (h1.integrable_indicator measurableSet_Ioc).integrableOn
  have hmeas_n : ∀ n, AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein (ψn n)) y)
      (volume.restrict (Ioi 0)) := fun n =>
    (mellinConvergent_horocycleMean (hψn_cont n) ha₀1 (hψn_a₀ n) (hψn_b n) hs).aestronglyMeasurable
  have hpt_mellin : ∀ᵐ y ∂volume.restrict (Ioi 0),
      Tendsto (fun n => (y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein (ψn n)) y) atTop
        (𝓝 ((y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy => (hm_tendsto y hy).const_smul _
  have hbd_mellin_n : ∀ n, ∀ᵐ y ∂volume.restrict (Ioi 0),
      ‖(y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein (ψn n)) y‖ ≤ dom y := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((s - 1) - 1).re = s.re - 2 := by simp; ring
    rw [hre]
    by_cases hyY : y ≤ Y
    · rw [Set.indicator_of_mem (show y ∈ Ioc 0 Y from ⟨hy0, hyY⟩), mul_comm]
      exact mul_le_mul_of_nonneg_right (hm_norm_n n y) (Real.rpow_nonneg hy0.le _)
    · rw [Set.indicator_of_notMem (show y ∉ Ioc 0 Y from fun h => hyY h.2),
        hm_zero_n n y (not_le.mp hyY), norm_zero, mul_zero]
  have hbd_mellin_sh : ∀ᵐ y ∂volume.restrict (Ioi 0),
      ‖(y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y‖ ≤ dom y := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((s - 1) - 1).re = s.re - 2 := by simp; ring
    rw [hre]
    by_cases hyY : y ≤ Y
    · rw [Set.indicator_of_mem (show y ∈ Ioc 0 Y from ⟨hy0, hyY⟩), mul_comm]
      exact mul_le_mul_of_nonneg_right (hm_norm_sh y) (Real.rpow_nonneg hy0.le _)
    · rw [Set.indicator_of_notMem (show y ∉ Ioc 0 Y from fun h => hyY h.2),
        hm_zero_sh y (not_le.mp hyY), norm_zero, mul_zero]
  have hmeas_sh : AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y)
      (volume.restrict (Ioi 0)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas_n hpt_mellin
  have hconv_sh : MellinConvergent (horocycleMean (pseudoEisenstein ψ_sh)) (s - 1) :=
    hdom_int.mono' hmeas_sh hbd_mellin_sh
  have htend_lhs : Tendsto (fun n => mellin (horocycleMean (pseudoEisenstein (ψn n))) (s - 1))
      atTop (𝓝 (mellin (horocycleMean (pseudoEisenstein ψ_sh)) (s - 1))) :=
    tendsto_integral_of_dominated_convergence dom hmeas_n hdom_int hbd_mellin_n hpt_mellin
  -- Dominated convergence for `mellin (ψn n) w → mellin ψ_sh w` at any `w : ℂ`
  have htend_ψ : ∀ w : ℂ, Tendsto (fun n => mellin (ψn n) w) atTop (𝓝 (mellin ψ_sh w)) := by
    intro w
    set dom_w : ℝ → ℝ := (Icc a₀ b).indicator fun y => y ^ (w.re - 1)
    have hcont_w : ContinuousOn (fun y : ℝ => y ^ (w.re - 1)) (Icc a₀ b) := fun y hy =>
      (Real.continuousAt_rpow_const y (w.re - 1) (Or.inl (by linarith [hy.1]))).continuousWithinAt
    have hdom_w : IntegrableOn dom_w (Ioi 0) volume :=
      (hcont_w.integrableOn_Icc.integrable_indicator measurableSet_Icc).integrableOn
    refine tendsto_integral_of_dominated_convergence dom_w
      (fun n => (differentiableAt_mellin_of_band (hψn_cont n) ha₀0 (hψn_a₀ n) (hψn_b n) w)
        |>. locallyIntegrableOn_iff_merely ?_ ; ?_) hdom_w ?_ ?_
    all_goals sorry
  sorry
