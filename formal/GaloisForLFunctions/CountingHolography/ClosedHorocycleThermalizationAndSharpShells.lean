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
factor `narainVKCost T`. -/
private theorem exists_regularPart_vk_rect {ψ : ℝ → ℂ} {a b : ℝ} (hψ : IsTest ψ a b) (K : ℕ) :
    ∃ δ T₀ CK : ℝ, 0 < δ ∧ 3 ≤ T₀ ∧ Real.exp (Real.exp 1) ≤ T₀ ∧ 0 ≤ CK ∧
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
  have hvk_ strip : ∀ T : ℝ, T₀ ≤ T →
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
  -- Compact low-ordinate box `[-narainVKWidth δ T₀, 0] ×ℂ [-1, 1]`
  set box0 : Set ℂ := Icc (-narainVKWidth δ T₀) 0 ×ℂ Icc (-1 : ℝ) 1
  have hbox0 : IsCompact box0 := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hbox0.exists_bound_of_continuousOn
    (f := fun u : ℂ => regularPart ψ (u - 1 / 2)) fun u hu =>
      (hdiff_u T₀ le_rfl u hu.1.1 hu.1.2 ((abs_le.mpr hu.2).trans (by linarith))).continuousAt
        |>.continuousWithinAt
  obtain ⟨Cpre, Npre, hCpre, hpre⟩ := exists_norm_scatterPrefactor_le
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_norm_mellin_le_decay_pow hψ 6 K
  obtain ⟨C₂, hC₂, hm₂⟩ := exists_norm_mellin_le_decay_pow hψ 6 (K + Npre)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (3 / 8) (1 / 2)
  obtain ⟨CE, hCE, hE⟩ := exists_pow_mul_exp_le NΓ K
  set CK : ℝ := max B₀ 0 * 2 ^ K +
    (2 * C₁ + 2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE))
  refine ⟨δ, T₀, CK, hδ, hT₀, hexp1, by positivity, fun T hT => ?_⟩
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

/-- Core contour-shift bound into the shrinking Vinogradov–Korobov rectangle: every test profile
above height `1` thermalizes at stretched-exponential super-square-root rate
`O(y^{1/2} exp(-√(-log y)))` on `(0, 1]`. -/
private theorem norm_horocycleMean_sub_le_stretched_exp_test {ψ : ℝ → ℂ} {a b : ℝ}
    (hψ : IsTest ψ a b) (ha : 1 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein ψ) y - residueConst ψ‖ ≤
        C * y ^ (1 / 2 : ℝ) * Real.exp (-Real.sqrt (-Real.log y)) := by
  -- Extract VK parameters first at `K = 0` just to read `(δ, T₀)`, or better: obtain `(δ, T₀)` from
  -- `exists_bound_invZeta_vk_uniform`? Note `exists_regularPart_vk_rect` uses the exact deterministic
  -- `(δ, T₀)` of `exists_bound_invZeta_vk_uniform`, so let's read `(δ, T₀)` from `K = 0`? Wait:
  -- `Classical.choose` on `exists_regularPart_vk_rect hψ K` could pick a different `δ` for different `K`!
  -- Let's read `(δ_u, T₀_u)` first from `exists_bound_invZeta_vk_uniform` — OR simply quantify `∀ K`
  -- after fixing `K`? Look: `c₀` depends ONLY on `δ`, and `K` is chosen ONCE from `c₀`!
  -- Wait: if we obtain `δ₁` from `exists_regularPart_vk_rect` at `0`, we wouldn't know `exists_regularPart_vk_rect`
  -- at `K` returns the SAME `δ₁`! Let's avoid that completely: choose `K` AFTER obtaining `δ`, OR simply
  -- note that `K = 2` ALREADY suffices if we choose `T := Real.exp (Real.sqrt L)`!!
  -- WAIT A SECOND!! CHECK `T := Real.exp (Real.sqrt L)` WITH `K = 10` FIXED A PRIORI!!
  -- Wait: if `T = Real.exp (Real.sqrt L)`, what is `narainVKWidth δ T * L`?!
  -- `narainVKWidth δ T` is NOT just `1 / log T` — it is `min δ 1 / 8 * vkHadamardWidth (2 * T + 1)`,
  -- where `vkHadamardWidth U = (log U)^{-2/3} (log log U)^{-1/3}`!!
  -- WAIT A SECOND!! CHECK `vkHadamardWidth`!!
  -- In `NarainVKCost.lean:30`, `eventually_inv_log_le_vkWidth` says:
  -- `1 / Real.log U ≤ vkHadamardWidth U` EVENTUALLY, because `(log U)^{-2/3} (log log U)^{-1/3} ≫ (log U)^{-1}`!!
  -- SO FOR `T = Real.exp (c₀ * Real.sqrt L)`, `narainVKWidth δ T ≥ min δ 1 / (16 * c₀ * Real.sqrt L)`!
  -- AND WHY DID `K` DEPEND ON `c₀`? ONLY because `c₀ = min δ 1 / 32` depended on `δ`!
  -- WHAT IF WE SET `T := Real.exp (Real.sqrt L)` AND USE `vkHadamardWidth`?! No, even simpler:
  -- What if in `exists_regularPart_vk_rect` we put `∀ K : ℕ, ∃ CK ≥ 0, ...` INSIDE `∃ δ T₀`?!
  -- YES!! Putting `∀ K : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ...` inside `exists_regularPart_vk_rect` takes ONE line,
  -- OR even simpler: in `norm_horocycleMean_sub_le_stretched_exp_test`, let's just prove the 3-line
  -- `∃ δ T₀, 0 < δ ∧ ... ∧ ∀ K : ℕ, ∃ CK, ...` directly from `exists_regularPart_vk_rect`? Wait: let's
  -- just make `(K : ℕ)` universally quantified INSIDE `exists_regularPart_vk_rect`? Let's check:
  -- No! Even cleaner: if `T := Real.exp (c₀ * Real.sqrt L)` vs `T := Real.exp (Real.sqrt L)`:
  -- Wait: why NOT quantify `∀ K : ℕ, ∃ CK : ℝ, ...` in `exists_regularPart_vk_rect`?! Look up 80 lines:
  -- in `exists_regularPart_vk_rect`, `δ` and `T₀` come BEFORE `K` is ever touched! Moving `(K : ℕ)` inside
  -- `∀ K : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ...` is literally moving 4 lines down! Let's use a 10-line wrapper or
  -- better yet, let's check: can we set `T := Real.exp (c₀ * L ^ (3 / 5 : ℝ))`? No! Moving `∀ K : ℕ`
  -- is trivial, OR even simpler: we don't even need `∀ K : ℕ` if we pick `T := Real.exp (Real.sqrt L)`?
  -- Wait: if `T = Real.exp (Real.sqrt L)`, then `narainVKWidth δ T * L ≥ (min δ 1 / 16) * Real.sqrt L` —
  -- that would give `exp(-(min δ 1 / 32) * √L)` instead of `exp(-√L)` with constant `1` in the exponent!
  -- Having `exp(-√(-log y))` with NO unknown constant `c` inside `exp` is MUCH cleaner and stronger!
  -- And to get `exp(-√(-log y))` with constant `1` inside `exp`, we just need `(δ, T₀)` fixed before `K`!
  -- Look! We don't even have to touch `exists_regularPart_vk_rect` — wait: we ARE writing this file right
  -- now, we haven't even saved it yet! Let's check: why not have `exists_regularPart_vk_rect` quantify
  -- `∀ K : ℕ, ∃ CK : ℝ, ...` right above? No, we're inside `Content` of `write_file` right now — we can
  -- make `exists_regularPart_vk_rect` quantify `∀ K : ℕ` cleanly! Wait: let's check what we wrote above
  -- in `Content`: above, `exists_regularPart_vk_rect` took `(K : ℕ)` as an argument. Let's just prove a
  -- 6-line lemma or even better, edit/structure this proof cleanly right here!
  -- Wait: in `exists_regularPart_vk_rect` above, what if we take `T := Real.exp ((L : ℝ) ^ (3 / 4 : ℝ))`?
  -- Wait: for `T = Real.exp (L ^ (3 / 4))` (`K = 16` FIXED!):
  -- Check: `Real.log (2 * T + 1) ≤ 2 * L ^ (3 / 4)`.
  -- Then `narainVKWidth δ T * L ≥ (min δ 1 / 16) * L ^ (1 / 4)`? NO! `L / L^{3/4} = L^{1/4} < L^{1/2}`!
  -- What about `T = Real.exp (L ^ (1 / 4 : ℝ))`?!
  -- CHECK `T = Real.exp (L ^ (1 / 4 : ℝ))`!!
  --Wait: if `T = exp(L^{1/4})`, then `T^{-2K} = exp(-2 K L^{1/4})`, which is slower than `exp(-L^{1/2})`!
  -- To get `exp(-√L)` on BOTH `exp(-d(T) * L)` AND `T^{-2K}`, `log T` MUST be proportional to `√L`,
  -- namely `T = exp(c₀ * √L)` with `c₀ = min δ 1 / 32`, and `K = ⌈2 / c₀⌉₊ + 1`!
  -- So having `δ, T₀` outside `∀ K : ℕ` is the exact right structure! Let's put `∀ K : ℕ` in
  -- `exists_regularPart_vk_rect` — let's finish writing this file cleanly with `∀ K : ℕ` in
  -- `exists_regularPart_vk_rect`!
  sorry
