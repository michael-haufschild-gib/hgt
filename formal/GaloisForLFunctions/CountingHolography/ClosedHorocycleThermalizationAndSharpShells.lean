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
  have hd_num : DifferentiableOn ℂ (BlackHoleRingdown.poleNumerator ψ) U := by
    intro s hs
    have hΓ : DifferentiableAt ℂ Complex.Gamma s := by
      refine Complex.differentiableAt_Gamma s fun m hm => ?_
      have hre := congrArg Complex.re hm
      simp at hre
      linarith [hs.1, Nat.cast_nonneg (α := ℝ) m]
    unfold BlackHoleRingdown.poleNumerator
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
  · have hwb : w ∈ Set.Icc (-1 / 2 : ℝ) 1 ×ℂ Set.Icc (-1 : ℝ) 1 := ⟨⟨hw1, hw2⟩, abs_le.mp ht⟩
    have him2 : w.im ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg w.im) ht 2
    have h1 : (1 + w.im ^ 2) ^ K ≤ 2 ^ K :=
      pow_le_pow_left₀ (by positivity) (by linarith) K
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
    have habs_le : |w.im| ≤ 1 + w.im ^ 2 := by
      nlinarith [sq_nonneg (1 - |w.im|), sq_abs w.im]
    have hpowle : |w.im| ^ NQ ≤ (1 + w.im ^ 2) ^ NQ :=
      pow_le_pow_left₀ (abs_nonneg w.im) habs_le NQ
    have hQψ : ‖scatterQ s‖ * ‖mellin ψ (-s)‖ ≤ CQ * C₂ / (1 + w.im ^ 2) ^ K := by
      calc ‖scatterQ s‖ * ‖mellin ψ (-s)‖
          ≤ (CQ * |w.im| ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) :=
            mul_le_mul hQs hP2 (norm_nonneg _) (by positivity)
        _ ≤ (CQ * (1 + w.im ^ 2) ^ NQ) * (C₂ / (1 + w.im ^ 2) ^ (K + NQ)) := by gcongr
        _ = CQ * C₂ / (1 + w.im ^ 2) ^ K := by rw [pow_add]; field_simp
    have hN : ‖BlackHoleRingdown.poleNumerator ψ s‖ ≤
        (2 * CQ * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by
      unfold BlackHoleRingdown.poleNumerator
      calc ‖2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Complex.Gamma s‖
          ≤ 2 * (‖scatterQ s‖ * ‖mellin ψ (-s)‖) + ‖residueConst ψ‖ * ‖Complex.Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
            norm_num [mul_assoc]
        _ ≤ 2 * (CQ * C₂ / (1 + w.im ^ 2) ^ K) +
            ‖residueConst ψ‖ * (CΓ * (CE / (1 + w.im ^ 2) ^ K)) := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin ψ w + BlackHoleRingdown.poleNumerator ψ s / w‖
        ≤ 2 * ‖mellin ψ w‖ + ‖BlackHoleRingdown.poleNumerator ψ s‖ := by
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
  have huIcc : Set.uIcc (1 : ℝ) (-1 / 2) = Set.Icc (-1 / 2) 1 := by
    rw [Set.uIcc_comm, Set.uIcc_of_le (by norm_num)]
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
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ := HTGeometry.exists_bound_norm_inv_Gamma_strip (3 / 8) (1 / 2)
  obtain ⟨C₃, N₃, hC₃, hζ⟩ := _root_.RHTower.exists_bound_norm_riemannZeta_strip 1
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
    have huim2 : u.im ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg u.im) ht 2
    have h1 : (1 + u.im ^ 2) ^ K ≤ 2 ^ K :=
      pow_le_pow_left₀ (by positivity) (by linarith) K
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
    have h1w : 1 ≤ |w.im| := by rwa [hwim]
    have hnw : 1 ≤ ‖w‖ := h1w.trans (Complex.abs_im_le_norm w)
    have hsre0 : (3 / 8 : ℝ) ≤ s.re := by simp [s, w]; linarith
    have hsre1 : s.re ≤ 1 / 2 := by simp [s, w]; linarith
    have h2s : 2 * s = 1 + 2 * u := by simp [s, w]; ring
    have hs_im0 : s.im ≠ 0 := fun h => by rw [hsim] at h; rw [h, abs_zero] at ht1; linarith
    have hQs : ‖scatterQ s‖ ≤ (Cpre * Cζ) * narainVKCost T * |u.im| ^ Npre := by
      rw [scatterQ_eq hs_im0, norm_mul]
      have hp := hpre s hsre0 hsre1 (by rw [hsim]; exact ht1)
      rw [hsim] at hp
      rw [← h2s] at hinv_u
      calc ‖(s - 1) * (Complex.Gammaℝ (2 * s - 1) / Complex.Gammaℝ (2 * s)) *
              riemannZeta (2 * s - 1)‖ * ‖(riemannZeta (2 * s))⁻¹‖
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
    have habs_le : |u.im| ≤ 1 + u.im ^ 2 := by
      nlinarith [sq_nonneg (1 - |u.im|), sq_abs u.im]
    have hpowle : |u.im| ^ Npre ≤ (1 + u.im ^ 2) ^ Npre :=
      pow_le_pow_left₀ (abs_nonneg u.im) habs_le Npre
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
    have hN : ‖BlackHoleRingdown.poleNumerator ψ s‖ ≤
        (2 * (Cpre * Cζ) * C₂ + ‖residueConst ψ‖ * (CΓ * CE)) *
          narainVKCost T / (1 + u.im ^ 2) ^ K := by
      unfold BlackHoleRingdown.poleNumerator
      calc ‖2 * scatterQ s * mellin ψ (-s) - residueConst ψ * Complex.Gamma s‖
          ≤ 2 * (‖scatterQ s‖ * ‖mellin ψ (-s)‖) + ‖residueConst ψ‖ * ‖Complex.Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
            norm_num [mul_assoc]
        _ ≤ 2 * ((Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K) +
              ‖residueConst ψ‖ * (CΓ * (CE / (1 + u.im ^ 2) ^ K)) * 1 := by
            rw [mul_one]; gcongr
        _ ≤ 2 * ((Cpre * Cζ) * C₂ * narainVKCost T / (1 + u.im ^ 2) ^ K) +
              ‖residueConst ψ‖ * (CΓ * (CE / (1 + u.im ^ 2) ^ K)) * narainVKCost T := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin ψ w + BlackHoleRingdown.poleNumerator ψ s / w‖
        ≤ 2 * ‖mellin ψ w‖ + ‖BlackHoleRingdown.poleNumerator ψ s‖ := by
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
  have hψa : ∀ t, t < a → ψ t = 0 := fun _ ht => hψ.eq_zero_of_le ht.le
  have hψb : ∀ t, b < t → ψ t = 0 := fun _ ht => hψ.eq_zero_of_ge ht.le
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
  have hC_rect0 : 0 ≤ C_rect := by positivity
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
          linarith [hC_rect0]
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
      linarith [(div_lt_iff₀ hc₀).mp hdiv]
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
    have hvert : Complex.VerticalIntegrable (mellin g) 1 := by
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
      rw [Complex.cpow_def_of_ne_zero hy0_c, ← Complex.ofReal_log hy.le]
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
      have hint_eq :
          (∫ t : ℝ, (y : ℂ) ^ (-(((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) •
            regularPart ψ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
          ∫ t : ℝ, ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) * G₀ ((t : ℂ) * Complex.I) :=
        integral_congr_ae (Eventually.of_forall fun t => by
          simpa only [smul_eq_mul] using hcpow_line t)
      rw [hint_eq, integral_const_mul, norm_smul, norm_mul, Real.norm_of_nonneg (by positivity),
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]
      ring
    -- Step 3: Split `∫_ℝ G₀(it) dt` into `[-T, T]` and `(Ioc (-T) T)ᶜ`
    have hG₀_norm_line : ∀ t : ℝ,
        ‖G₀ ((t : ℂ) * Complex.I)‖ ≤ B_K / (1 + t ^ 2) ^ K := by
      intro t
      simp only [G₀, norm_mul, Complex.norm_exp]
      have hre0 : ((L : ℂ) * ((t : ℂ) * Complex.I)).re = 0 := by simp
      rw [hre0, Real.exp_zero, one_mul]
      have hb := hB_K ((t : ℂ) * Complex.I - 1 / 2) (by simp; norm_num) (by simp; norm_num)
      simpa using hb
    have hG₀_cont : Continuous fun t : ℝ => G₀ ((t : ℂ) * Complex.I) := by
      have hline_cont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.mul continuous_const
      have hshift_cont : Continuous (fun t : ℝ => (t : ℂ) * Complex.I - 1 / 2) :=
        hline_cont.sub continuous_const
      have hregular_cont : Continuous (fun t : ℝ => regularPart ψ ((t : ℂ) * Complex.I - 1 / 2)) := by
        rw [continuous_iff_continuousAt]
        intro t
        have hw : DifferentiableAt ℂ (regularPart ψ) ((t : ℂ) * Complex.I - 1 / 2) :=
          differentiableAt_regularPart_of_xi_ne_zero hψ (by simp; norm_num)
            (_root_.RHTower.xi_ne_zero_of_one_le_re (by simp; norm_num))
        exact hw.continuousAt.comp t hshift_cont.continuousAt
      exact (Complex.continuous_exp.comp (continuous_const.mul hline_cont)).mul hregular_cont
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
    rw [div_mul_eq_mul_div C (-Real.log y), le_div_iff₀ hLpos]
    exact h1
  have h3 : C / (-Real.log y) < ε :=
    (div_lt_iff₀ hLpos).mpr (by linarith [(div_lt_iff₀ hε).mp hlog])
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
      have hBA : B ≤ A :=
        antitoneOn_disc Y (Set.mem_Ici.mpr hk0) (Set.mem_Ici.mpr (by positivity)) (by linarith)
      set L_sec : ℝ → ℝ := fun x => ((k : ℝ) + 1 - x) * A + (x - (k : ℝ)) * B
      have hpt : ∀ x ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1),
          L_sec x ≤ f x ∧ f x - L_sec x ≤ ((k : ℝ) + 1) / B - (k : ℝ) / A := by
        intro x hx
        have hx0 : 0 ≤ x := le_trans hk0 hx.1
        set t : ℝ := x - k
        have ht0 : 0 ≤ t := by simp only [t]; linarith [hx.1]
        have ht1 : 0 ≤ 1 - t := by simp only [t]; linarith [hx.2]
        have hx_eq : x = (k : ℝ) + t := by simp only [t]; ring
        have hfx0 : 0 < f x := hf_pos x hx0 (hx.2.trans hkR)
        have hfx2 : f x ^ 2 = Y ^ 2 - x ^ 2 :=
          Real.sq_sqrt (Real.sqrt_pos.mp hfx0).le
        have hdiff_sq : f x ^ 2 - L_sec x ^ 2 = t * (1 - t) * (1 + (A - B) ^ 2) := by
          have he1 : -(x ^ 2) + (1 - t) * (k : ℝ) ^ 2 + t * ((k : ℝ) + 1) ^ 2 = t * (1 - t) := by
            rw [hx_eq]; ring
          have he2 : -(((k : ℝ) + 1 - x) * A + (x - (k : ℝ)) * B) ^ 2 +
              (1 - t) * A ^ 2 + t * B ^ 2 = t * (1 - t) * (A - B) ^ 2 := by
            rw [hx_eq]; ring
          simp only [L_sec]
          linear_combination hfx2 - (1 - t) * hA2 - t * hB2 + he1 + he2
        have hlo : L_sec x ≤ f x := by
          by_contra hlt
          push Not at hlt
          have hsq_lt : f x ^ 2 < L_sec x ^ 2 := pow_lt_pow_left₀ hlt hfx0.le two_ne_zero
          have hnn : 0 ≤ t * (1 - t) * (1 + (A - B) ^ 2) :=
            mul_nonneg (mul_nonneg ht0 ht1) (by positivity)
          linarith [hdiff_sq]
        -- Upper bound via the two endpoint chords
        have hfx_le_A : f x ≤ A :=
          antitoneOn_disc Y (Set.mem_Ici.mpr hk0) (Set.mem_Ici.mpr hx0) hx.1
        have hB_le_fx : B ≤ f x :=
          antitoneOn_disc Y (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr (by positivity)) hx.2
        have hch1 : f x ≤ A - ((k : ℝ) / A) * t := by
          have he3 : x ^ 2 - (k : ℝ) ^ 2 = 2 * (k : ℝ) * t + t ^ 2 := by rw [hx_eq]; ring
          have hid : (A - f x) * (A + f x) = 2 * (k : ℝ) * t + t ^ 2 := by
            linear_combination hA2 - hfx2 + he3
          have h1 : 2 * (k : ℝ) * t ≤ (A - f x) * (2 * A) := by
            calc 2 * (k : ℝ) * t
                ≤ 2 * (k : ℝ) * t + t ^ 2 := le_add_of_nonneg_right (sq_nonneg t)
              _ = (A - f x) * (A + f x) := hid.symm
              _ ≤ (A - f x) * (2 * A) :=
                  mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hfx_le_A)
          have h2 : ((k : ℝ) / A) * t ≤ A - f x := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hA]
            linarith
          linarith
        have hch2 : f x ≤ B + (((k : ℝ) + 1) / B) * (1 - t) := by
          have he4 : ((k : ℝ) + 1) ^ 2 - x ^ 2 = (1 - t) * (2 * (k : ℝ) + 1 + t) := by
            rw [hx_eq]; ring
          have hid : (f x - B) * (f x + B) = (1 - t) * (2 * (k : ℝ) + 1 + t) := by
            linear_combination hfx2 - hB2 + he4
          have h1 : (f x - B) * (2 * B) ≤ 2 * ((k : ℝ) + 1) * (1 - t) := by
            calc (f x - B) * (2 * B)
                ≤ (f x - B) * (f x + B) :=
                  mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hB_le_fx)
              _ = (1 - t) * (2 * (k : ℝ) + 1 + t) := hid
              _ ≤ (1 - t) * (2 * ((k : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_left (by linarith) ht1
              _ = 2 * ((k : ℝ) + 1) * (1 - t) := by ring
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
          have hfx_split : f x = (1 - t) * f x + t * f x := by ring
          calc f x - L_sec x
              = ((1 - t) * f x + t * f x) - ((1 - t) * A + t * B) := by rw [← hfx_split, hL_t]
            _ ≤ ((1 - t) * (A - (k : ℝ) / A * t) + t * (B + ((k : ℝ) + 1) / B * (1 - t))) -
                  ((1 - t) * A + t * B) := sub_le_sub_right (add_le_add h1 h2) _
            _ = t * (1 - t) * (((k : ℝ) + 1) / B - (k : ℝ) / A) := by ring
        have ht_prod : t * (1 - t) ≤ 1 := by
          calc t * (1 - t) ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) ht1 zero_le_one
            _ = 1 := one_mul 1
        exact ⟨hlo, hcomb.trans (mul_le_of_le_one_left hslope_nn ht_prod)⟩
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
      have hlo_int := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
        (hL_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)
        fun x hx => (hpt x hx).1
      have hhi_int := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
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
        (n := N) fun k _ => hf_cont.intervalIntegrable _ _
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
      (antitoneOn_disc Y (Set.mem_Ici.mpr (Nat.cast_nonneg N))
        (Set.mem_Ici.mpr (by positivity)) (by linarith)).trans hfN_le
    have hfN1_nn : 0 ≤ f ((N : ℝ) + 1) := Real.sqrt_nonneg _
    have hfN_nn : 0 ≤ f N := Real.sqrt_nonneg _
    have hint_tail_nn : 0 ≤ ∫ x in (N : ℝ)..Y, f x :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => Real.sqrt_nonneg _
    have hint_tail_le : ∫ x in (N : ℝ)..Y, f x ≤ 4 * Real.sqrt Y := by
      have hm := intervalIntegral.integral_mono_on (by linarith : (N : ℝ) ≤ Y)
        (hf_cont.intervalIntegrable _ _) intervalIntegrable_const
        fun x hx => (antitoneOn_disc Y (Set.mem_Ici.mpr (Nat.cast_nonneg N))
          (Set.mem_Ici.mpr (hx.1.trans' (Nat.cast_nonneg N))) hx.1).trans hfN_le
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
        -((∫ x in (0 : ℝ)..(N : ℝ), f x) - ∑ k ∈ range N, (f k + f ((k : ℝ) + 1)) / 2) +
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
    have hterm : ∀ d ∈ Finset.Icc 1 D,
        |(μ d : ℝ) * circleRemainder (X / d)| ≤ 8 * Real.sqrt X * (1 / Real.sqrt d) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
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

open _root_.RHTower GaloisForLFunctions.RHTower.DeckPointPair

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
private theorem eventually_shellTrap_eq_indicator {a b δ₀ : ℝ} (_hab : a < b) (hδ0 : 0 < δ₀)
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
        Set.indicator_of_mem (show t ∈ Set.Ico a b from ⟨hta, htb⟩)]
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
    have hfin := finite_rows_im_ge (isCompact_singleton (x := z)) ha₀0
    set S := hfin.toFinset
    have hall : ∀ᶠ n in atTop, ∀ p ∈ S,
        ψn n (gammaSetMatrix p • z).im =
          ψ_sh (gammaSetMatrix p • z).im :=
      (Filter.eventually_all_finset S).mpr fun p _ =>
        eventually_shellTrap_eq_indicator hab hδ0 hδba _
    filter_upwards [hall] with n hn
    have hout_n : ∀ p ∉ S, ψn n (gammaSetMatrix p • z).im = 0 := fun p hp =>
      hψn_a₀ n _ (lt_of_not_ge fun hge => hp (hfin.mem_toFinset.2 ⟨z, rfl, hge⟩))
    have hout_sh : ∀ p ∉ S, ψ_sh (gammaSetMatrix p • z).im = 0 := fun p hp =>
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
      (volume.restrict (Set.Ioi (0 : ℝ))) := fun n =>
    (mellinConvergent_horocycleMean (hψn_cont n) ha₀1 (hψn_a₀ n) (hψn_b n) hs).aestronglyMeasurable
  have hpt_mellin : ∀ᵐ (y : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun n => (y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein (ψn n)) y) atTop
        (𝓝 ((y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun y hy => (hm_tendsto y hy).const_smul _
  have hbd_mellin_n : ∀ n, ∀ᵐ (y : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖(y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein (ψn n)) y‖ ≤ dom y := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((s - 1) - 1).re = s.re - 2 := by simp; ring
    rw [hre]
    dsimp only [dom]
    by_cases hyY : y ≤ Y
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioc 0 Y from ⟨hy0, hyY⟩), mul_comm]
      exact mul_le_mul_of_nonneg_right (hm_norm_n n y) (Real.rpow_nonneg hy0.le _)
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ioc 0 Y from fun h => hyY h.2),
        hm_zero_n n y (not_le.mp hyY), norm_zero, mul_zero]
  have hbd_mellin_sh : ∀ᵐ (y : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖(y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y‖ ≤ dom y := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : ((s - 1) - 1).re = s.re - 2 := by simp; ring
    rw [hre]
    dsimp only [dom]
    by_cases hyY : y ≤ Y
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioc 0 Y from ⟨hy0, hyY⟩), mul_comm]
      exact mul_le_mul_of_nonneg_right (hm_norm_sh y) (Real.rpow_nonneg hy0.le _)
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ioc 0 Y from fun h => hyY h.2),
        hm_zero_sh y (not_le.mp hyY), norm_zero, mul_zero]
  have hmeas_sh : AEStronglyMeasurable
      (fun y : ℝ => (y : ℂ) ^ ((s - 1) - 1) • horocycleMean (pseudoEisenstein ψ_sh) y)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
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
    have hmeas_ψn : ∀ n, AEStronglyMeasurable
        (fun y : ℝ => (y : ℂ) ^ (w - 1) • ψn n y) (volume.restrict (Ioi 0)) := fun n =>
      ContinuousOn.aestronglyMeasurable
        (fun y hy =>
          ((Complex.continuousAt_ofReal_cpow_const y (w - 1)
            (Or.inr (mem_Ioi.mp hy).ne')).smul (hψn_cont n).continuousAt).continuousWithinAt)
        measurableSet_Ioi
    have hbd_ψn : ∀ n, ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi (0 : ℝ)),
        ‖(y : ℂ) ^ (w - 1) • ψn n y‖ ≤ dom_w y := by
      intro n
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun y hy => ?_
      have hy0 : (0 : ℝ) < y := hy
      rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
        Complex.sub_re, Complex.one_re]
      dsimp only [dom_w]
      by_cases hmem : y ∈ Icc a₀ b
      · rw [Set.indicator_of_mem hmem]
        exact mul_le_of_le_one_right (Real.rpow_nonneg hy0.le _) (hψn_norm n y)
      · rw [Set.indicator_of_notMem hmem]
        rcases lt_or_ge y a₀ with hlt | hge
        · rw [hψn_a₀ n y hlt, norm_zero, mul_zero]
        · have hgt : b < y := lt_of_not_ge fun hle => hmem ⟨hge, hle⟩
          rw [hψn_b n y hgt, norm_zero, mul_zero]
    have hpt_ψn : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi (0 : ℝ)),
        Tendsto (fun n => (y : ℂ) ^ (w - 1) • ψn n y) atTop
          (𝓝 ((y : ℂ) ^ (w - 1) • ψ_sh y)) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun y _ => ?_
      refine (tendsto_const_nhds.congr' ?_).const_smul _
      filter_upwards [eventually_shellTrap_eq_indicator hab hδ0 hδba y] with n hn
      exact hn.symm
    exact tendsto_integral_of_dominated_convergence dom_w hmeas_ψn hdom_w hbd_ψn hpt_ψn
  refine ⟨hconv_sh, ?_⟩
  have htend_rhs : Tendsto
      (fun n => 2 * mellin (ψn n) (s - 1) +
        2 * (msB (s - 1 / 2) / msA (s - 1 / 2)) * mellin (ψn n) (-s))
      atTop
      (𝓝 (2 * mellin ψ_sh (s - 1) +
        2 * (msB (s - 1 / 2) / msA (s - 1 / 2)) * mellin ψ_sh (-s))) :=
    ((htend_ψ (s - 1)).const_mul 2).add (((htend_ψ (-s)).const_mul _).congr fun _ => rfl)
  exact tendsto_nhds_unique htend_lhs
    (htend_rhs.congr fun n =>
      (mellin_horocycleMean (hψn_cont n) ha₀1 (hψn_a₀ n) (hψn_b n) hs).symm)

/-- The Mellin transform of a sharp shell indicator `1_{[a, b)}` (`0 < a ≤ b`) is entire. -/
theorem differentiableAt_mellin_shell {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (w : ℂ) :
    DifferentiableAt ℂ (mellin ((Ico a b).indicator (1 : ℝ → ℂ))) w := by
  have hint : Integrable ((Set.Ico a b).indicator (1 : ℝ → ℂ)) volume :=
    (integrableOn_const (C := (1 : ℂ)) (by simp)).integrable_indicator measurableSet_Ico
  refine mellin_differentiableAt_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1)
    hint.integrableOn.locallyIntegrableOn ?_ (by linarith) ?_ (by linarith)
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop b] with y hy
    exact (Set.indicator_of_notMem (fun h => by linarith [h.2]) _).symm
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    exact (Set.indicator_of_notMem (fun h => by linarith [hy.2, h.1]) _).symm

/-- Explicit Mellin transform of a sharp shell indicator:
`∫₀^∞ 1_{[a, b)}(y) y^{w - 1} dy = (b^w - a^w) / w` for `0 < a ≤ b` and `w ≠ 0`. -/
theorem mellin_shell_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {w : ℂ} (hw : w ≠ 0) :
    mellin ((Ico a b).indicator (1 : ℝ → ℂ)) w = ((b : ℂ) ^ w - (a : ℂ) ^ w) / w := by
  unfold mellin
  have heq : (fun y : ℝ => (y : ℂ) ^ (w - 1) • (Set.Ico a b).indicator (1 : ℝ → ℂ) y) =
      (Set.Ico a b).indicator (fun y : ℝ => (y : ℂ) ^ (w - 1)) := by
    funext y
    by_cases hy : y ∈ Set.Ico a b <;> simp [hy]
  rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ico,
    Set.inter_eq_right.mpr (fun y (hy : y ∈ Set.Ico a b) => Set.mem_Ioi.mpr (lt_of_lt_of_le ha hy.1)),
    MeasureTheory.integral_Ico_eq_integral_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ w / w) ((x : ℂ) ^ (w - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hw1 : w - 1 ≠ -1 := fun h => hw (by linear_combination h)
    simpa [sub_add_cancel] using hasDerivAt_ofReal_cpow_const' hx0 hw1
  have hcont : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (w - 1)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x (w - 1)
      (Or.inr (by linarith [hx.1]))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable, sub_div]

/-- The Mellin transform of a non-degenerate sharp shell `0 < a < b` never vanishes on the open
left half-plane (i.e. at `-s₀` with `Re s₀ > 0`), because `|b^{-s₀}| < |a^{-s₀}|`. -/
theorem mellin_shell_ne_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    mellin ((Ico a b).indicator (1 : ℝ → ℂ)) (-s₀) ≠ 0 := by
  have hne0 : -s₀ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [mellin_shell_eq ha hab.le hne0]
  refine div_ne_zero (sub_ne_zero.mpr fun hpow => ?_) hne0
  have hnorm := congrArg norm hpow
  have hb0 : 0 < b := lt_trans ha hab
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb0, Complex.norm_cpow_eq_rpow_re_of_pos ha,
    Complex.neg_re] at hnorm
  exact (Real.rpow_lt_rpow_of_neg ha hab (by linarith)).ne hnorm

/-- Analytic continuation of the single-shell Mellin unfolding identity into `quarterPlane α`. -/
private theorem msB_mul_mellin_shell_eq_zero_of_rate {α a b : ℝ} (ha : 1 < a) (hab : a < b)
    {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - c‖ ≤ C * y ^ α)
    {s₀ : ℂ} (hs₀ : s₀ ∈ quarterPlane α) (hA : msA (s₀ - 1 / 2) = 0) :
    msB (s₀ - 1 / 2) * mellin ((Ico a b).indicator (1 : ℝ → ℂ)) (-s₀) = 0 := by
  have ha0 : 0 < a := by linarith
  set ψ : ℝ → ℂ := (Ico a b).indicator 1
  have hpe_eq : horocycleMean (pseudoEisenstein ψ) =
      horocycleMean (fun z => (shellCount a b z : ℂ)) := by
    funext y
    unfold horocycleMean
    congr 1
    funext x
    exact pseudoEisenstein_shell ha0 _
  set A := horocycleMean (pseudoEisenstein ψ) with hAdef
  set ind : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun _ => c with hind
  set g : ℝ → ℂ := fun y => A y - ind y with hg
  have hψa : ∀ y, y < a → ψ y = 0 := fun y hy =>
    Set.indicator_of_notMem (fun h => by linarith [h.1]) _
  have hψb : ∀ y, b < y → ψ y = 0 := fun y hy =>
    Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hind_smul : ind = fun y => c • (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) y := by
    funext y
    by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [hind, hy]
  have hindM : ∀ w : ℂ, 0 < w.re → MellinConvergent ind w ∧ mellin ind w = c / w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hasMellin_one_Ioc hw
    rw [hind_smul]
    refine ⟨h1.const_smul c, ?_⟩
    rw [mellin_const_smul, h2, smul_eq_mul]
    ring
  have hAint : IntegrableOn A (Ioi 0) := by
    have h := (mellin_horocycleMean_shell ha hab (s := 2) (by norm_num)).1
    refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
    rfl
  have hindint : IntegrableOn ind (Ioi 0) := by
    have := (hindM 1 one_pos).1
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    norm_num
  have hsplit : ∀ s : ℂ, 1 < s.re → mellin A (s - 1) = mellin g (s - 1) + c / (s - 1) := by
    intro s hs
    have hw : 0 < (s - 1).re := by simp; linarith
    have hAM := (mellin_horocycleMean_shell ha hab hs).1
    obtain ⟨hiM, hiV⟩ := hindM (s - 1) hw
    have hgM : MellinConvergent g (s - 1) := by
      refine (hAM.sub hiM).congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hg, smul_sub]
      rfl
    rw [← hiV, mellin, mellin, mellin, ← integral_add hgM hiM]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hg, smul_sub, sub_add_cancel]
  have heq : ∀ s : ℂ, 1 < s.re →
      msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)) =
        2 * msB (s - 1 / 2) * mellin ψ (-s) := by
    intro s hs
    have hu : 1 / 2 < (s - 1 / 2).re := by simp; linarith
    have hA0 := msA_ne_zero_of_re hu
    rw [← hsplit s hs, (mellin_horocycleMean_shell ha hab hs).2]
    generalize msA (s - 1 / 2) = M at hA0 ⊢
    field_simp
    ring
  have hgint : LocallyIntegrableOn g (Ioi 0) := (hAint.sub hindint).locallyIntegrableOn
  have hg_top : ∀ w : ℂ, g =O[atTop] (· ^ (-(w.re + 1))) := by
    intro w
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (max (max b a⁻¹) 1)] with y hy
    have h1 : max b a⁻¹ < y := lt_of_le_of_lt (le_max_left _ _) hy
    have h2 : ¬ y ≤ 1 := not_le.2 (lt_of_le_of_lt (le_max_right _ _) hy)
    simp [hg, hAdef, horocycleMean_eq_zero_of_gt ha0 hψa hψb h1, hind, h2]
  have hg_bot : g =O[𝓝[>] 0] (· ^ (-(-α))) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    have hy1 : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg hy.1.le _)]
    have hAy : A y = horocycleMean (fun z => (shellCount a b z : ℂ)) y := congrFun hpe_eq y
    simp only [hg, hAy, hind, Set.indicator_of_mem hy1]
    exact hrate y hy.1 hy.2.le
  have hdiff : ∀ s ∈ quarterPlane α, DifferentiableAt ℂ
      (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1))) s ∧
      DifferentiableAt ℂ (fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s)) s := by
    intro s hs
    have hL := mem_eisensteinLineDomain_of_mem_quarterPlane hs
    have hsub : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) s := differentiableAt_id.sub_const _
    have hmA := (hasDerivAt_msA hL).differentiableAt.comp s hsub
    have hmB := (hasDerivAt_msB hL).differentiableAt.comp s hsub
    have hs1 : s - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [hs.2]
    have hre : -α < (s - 1).re := by
      have := lt_of_le_of_lt (le_max_left _ _) hs.1
      simp
      linarith
    have hmg : DifferentiableAt ℂ (mellin g) (s - 1) :=
      mellin_differentiableAt_of_isBigO_rpow hgint (hg_top (s - 1)) (by linarith) hg_bot hre
    have hmψ := differentiableAt_mellin_shell ha0 hab.le
    refine ⟨hmA.mul (((hmg.comp s (differentiableAt_id.sub_const 1)).add
      ((differentiableAt_const c).div (differentiableAt_id.sub_const 1) hs1)).sub
      (((hmψ (s - 1)).comp s (differentiableAt_id.sub_const 1)).const_mul 2)), ?_⟩
    exact (hmB.const_mul 2).mul ((hmψ (-s)).comp s differentiableAt_id.neg)
  have hU := isOpen_quarterPlane α
  have hf₁ : AnalyticOnNhd ℂ
      (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)))
      (quarterPlane α) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hdiff s hs).1.differentiableWithinAt) hU
  have hf₂ : AnalyticOnNhd ℂ (fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s)) (quarterPlane α) :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hdiff s hs).2.differentiableWithinAt) hU
  set z₀ : ℂ := ((max (1 - α) 1 + 1 : ℝ) : ℂ) + Complex.I with hz₀
  have hz₀re : z₀.re = max (1 - α) 1 + 1 := by simp [hz₀]
  have hz₀U : z₀ ∈ quarterPlane α := by
    refine ⟨?_, by simp [hz₀]⟩
    rw [hz₀re]
    have : max (1 - α) 0 ≤ max (1 - α) 1 := max_le_max le_rfl zero_le_one
    linarith
  have hev : (fun s => msA (s - 1 / 2) * (mellin g (s - 1) + c / (s - 1) - 2 * mellin ψ (s - 1)))
      =ᶠ[𝓝 z₀] fun s => 2 * msB (s - 1 / 2) * mellin ψ (-s) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : z₀ ∈ {s : ℂ | 1 < s.re} := by
      show 1 < z₀.re
      rw [hz₀re]
      linarith [le_max_right (1 - α) 1]
    filter_upwards [hopen.mem_nhds hmem] with s hs using heq s hs
  have hEq := hf₁.eqOn_of_preconnected_of_eventuallyEq hf₂ (isPreconnected_quarterPlane α) hz₀U
    hev hs₀
  simp only [hA, zero_mul] at hEq
  have := hEq.symm
  rw [mul_assoc] at this
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

/-- **Single-shell Zagier converse.** Because the Mellin transform `(a^{-s} - b^{-s})/s` of a
single sharp shell `1 < a < b` never vanishes on `Re s > 0`, a power rate `O(y^α)` on `(0, 1]` for
a **single** fixed shell already forces every zero `ρ` of `ζ` with `Re ρ > 0` to satisfy
`Re ρ ≤ 2 - 2α`. -/
theorem re_le_of_single_shell_rate {α a b : ℝ} (ha : 1 < a) (hab : a < b) {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - c‖ ≤ C * y ^ α)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) :
    ρ.re ≤ 2 - 2 * α := by
  by_contra hlt
  push Not at hlt
  have hρ1 : ρ.re < 1 := by
    by_contra h1
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h1) hρ
  obtain ⟨ρ', hρ', hre', him'⟩ : ∃ ρ' : ℂ, riemannZeta ρ' = 0 ∧ ρ'.re = ρ.re ∧ 0 < ρ'.im := by
    rcases lt_trichotomy ρ.im 0 with hi | hi | hi
    · refine ⟨(starRingEnd ℂ) ρ, by rw [riemannZeta_conj, hρ, map_zero], by simp, ?_⟩
      simp; linarith
    · exfalso
      have hreal : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
      exact riemannZeta_ne_zero_of_ofReal_mem_Ioo hρ0 hρ1 (hreal ▸ hρ)
    · exact ⟨ρ, hρ, rfl, hi⟩
  set s₀ : ℂ := ρ' / 2 with hs₀def
  have hs₀ : s₀ ∈ quarterPlane α := by
    refine ⟨max_lt ?_ ?_, ?_⟩ <;> simp [hs₀def] <;> linarith
  have hA : msA (s₀ - 1 / 2) = 0 := by
    rw [msA, show 1 + 2 * (s₀ - 1 / 2) = ρ' by rw [hs₀def]; ring, reflectedCompletedLambda, hρ',
      mul_zero]
  have hB : msB (s₀ - 1 / 2) ≠ 0 := msB_ne_zero_of_zero (by rw [hre']; exact hρ1) him'
  have hprod := msB_mul_mellin_shell_eq_zero_of_rate ha hab hrate hs₀ hA
  have hm := (mul_eq_zero.1 hprod).resolve_left hB
  exact mellin_shell_ne_zero (by linarith) hab (by simp [hs₀def]; linarith) hm

/-- **No single sharp shell `1 < a < b` thermalizes faster than `y^{3/4}`.** -/
theorem not_single_shell_rate_gt_three_quarters {α a b : ℝ} (ha : 1 < a) (hab : a < b)
    (hα : 3 / 4 < α) :
    ¬∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - c‖ ≤ C * y ^ α := by
  rintro ⟨c, C, hrate⟩
  obtain ⟨ρ₀, hre, hζ⟩ := exists_zeta_zero_on_critical_line
  have := re_le_of_single_shell_rate ha hab hrate hζ (by linarith)
  linarith

/-- Rate `y^{3/4 - ε}` for any single sharp shell `1 < a < b` implies `RiemannHypothesis`. -/
theorem riemannHypothesis_of_single_shell_rate {a b : ℝ} (ha : 1 < a) (hab : a < b)
    (h : ∀ ε : ℝ, 0 < ε → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hρ, hρ1, -⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  set ε := (ρ.re - 1 / 2) / 4 with hε
  obtain ⟨c, C, hrate⟩ := h ε (by rw [hε]; linarith)
  have := re_le_of_single_shell_rate ha hab hrate hρ (by linarith)
  rw [hε] at this
  linarith

/-- Uniform norm bound `‖horocycleMean (shellCount a b) y‖ ≤ 2` for every shell above height `1`. -/
private theorem norm_horocycleMean_shellCount_le_two {a b : ℝ} (ha : 1 < a) (y : ℝ) :
    ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y‖ ≤ 2 := by
  have ha0 : 0 < a := by linarith
  set ψ : ℝ → ℂ := (Ico a b).indicator 1
  have hψa : ∀ t, t < a → ψ t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => by linarith [h.1]) _
  have hψ_norm : ∀ t, ‖ψ t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ico a b
    · simp [ψ, Set.indicator_of_mem ht]
    · simp [ψ, Set.indicator_of_notMem ht]
  have hpe_bd : ∀ z : UpperHalfPlane, ‖(shellCount a b z : ℂ)‖ ≤ 2 := by
    intro z
    rw [← pseudoEisenstein_shell ha0 z]
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    rw [← pseudoEisenstein_smul g z, pseudoEisenstein_of_mem_fd ha hψa hg, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    linarith [hψ_norm (g • z).im]
  unfold horocycleMean
  refine (norm_setIntegral_le_of_norm_le_const (by simp) fun x _ => hpe_bd _).trans ?_
  simp

/-- Under `RiemannHypothesis`, for every `0 < δ ≤ 1/4`, both Möbius main-term remainders in
`horoballSum_decomposition` enjoy `O_δ(D^{-1/2 + δ})` and `O_δ(D^{-3/2 + δ})` cancellation:
`|∑_{1 ≤ d ≤ D} μ(d)/d| ≤ C₁ D^{-1/2 + δ}` and
`|∑_{1 ≤ d ≤ D} μ(d)/d² - 6/π²| ≤ C₂ D^{-3/2 + δ}`. -/
theorem moebius_harmonic_and_sq_tail_of_rh (hRH : RiemannHypothesis) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ D : ℕ, 1 ≤ D →
        |∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ)| ≤ C₁ * (D : ℝ) ^ (-1 / 2 + δ) ∧
        |(∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2| ≤
          C₂ * (D : ℝ) ^ (-3 / 2 + δ) := by
  obtain ⟨CM, hCM0, hCM⟩ :=
    _root_.RHTower.riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ0
  set C_M : ℝ := CM * 2 ^ (1 / 2 + δ)
  have hC_M0 : 0 ≤ C_M := mul_nonneg hCM0 (Real.rpow_nonneg zero_le_two _)
  have hmert_eq : ∀ N : ℕ, ‖_root_.RHTower.mobiusMertensPartialSum N‖ =
      |_root_.RHTower.Sieve.mertensM N| := by
    intro N
    have hc : _root_.RHTower.mobiusMertensPartialSum N =
        ((_root_.RHTower.Sieve.mertensM N : ℝ) : ℂ) := by
      unfold _root_.RHTower.mobiusMertensPartialSum _root_.RHTower.Sieve.mertensM
        _root_.RHTower.mobiusComplexCoefficient
      push_cast
      rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have hmert_pow : ∀ n : ℕ, 1 ≤ n →
      |_root_.RHTower.Sieve.mertensM n| ≤ C_M * (n : ℝ) ^ (1 / 2 + δ) := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    calc |_root_.RHTower.Sieve.mertensM n|
        = ‖_root_.RHTower.mobiusMertensPartialSum n‖ := (hmert_eq n).symm
      _ ≤ CM * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := hCM n
      _ ≤ CM * (2 * (n : ℝ)) ^ (1 / 2 + δ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) h1 (by linarith)) hCM0
      _ = C_M * (n : ℝ) ^ (1 / 2 + δ) := by
          rw [Real.mul_rpow zero_le_two (by positivity)]
          ring
  set η : ℝ := 1 / 2 - δ
  have hη : 0 < η := by simp only [η]; linarith
  set C₁ : ℝ := C_M * (1 + 1 / η)
  set C₂ : ℝ := 2 * C_M + 6 * C_M / (3 / 2 - δ)
  have hC₁0 : 0 ≤ C₁ := mul_nonneg hC_M0 (by positivity)
  have hC₂0 : 0 ≤ C₂ := by
    have : 0 < 3 / 2 - δ := by linarith
    positivity
  refine ⟨C₁, C₂, hC₁0, hC₂0, fun D hD1 => ⟨?_, ?_⟩⟩
  · -- First bound: `|∑_{1 ≤ d ≤ D} μ(d)/d| ≤ C₁ D^{-1/2 + δ}`
    have hden_eq : _root_.RHTower.deningerHarmonicPartial D =
        ∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) := by
      unfold _root_.RHTower.deningerHarmonicPartial
      rw [sum_Icc_eq_sum_range, Finset.sum_range_succ', Nat.cast_zero, div_zero, add_zero]
    rw [← hden_eq, show (-1 / 2 + δ : ℝ) = -η by simp only [η]; ring]
    refine _root_.RHTower.abs_deningerHarmonicPartial_le_of_mertens_power hη hC_M0 ?_ hD1
    intro n hn
    rw [show (1 : ℝ) - η = 1 / 2 + δ by simp only [η]; ring]
    exact hmert_pow n hn
  · -- Second bound: `|∑_{1 ≤ d ≤ D} μ(d)/d² - 6/π²| ≤ C₂ D^{-3/2 + δ}`
    set f : ℕ → ℝ := fun n => (μ n : ℝ) / (n : ℝ) ^ (2 : ℕ)
    have hs := _root_.RHTower.hasSum_moebius_div_sq
    have hsplit := hs.summable.sum_add_tsum_nat_add (D + 1)
    rw [hs.tsum_eq] at hsplit
    have hsum_eq : ∑ n ∈ range (D + 1), f n = ∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 := by
      rw [sum_Icc_eq_sum_range, Finset.sum_range_succ']
      simp [f]
    have htail_eq : (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2 =
        -(∑' i : ℕ, f (i + (D + 1))) := by
      have hpi : (6 : ℝ) / Real.pi ^ (2 : ℕ) = 6 / Real.pi ^ 2 := rfl
      linarith [hsplit, hsum_eq]
    rw [htail_eq, abs_neg]
    have hsub_sum : Summable (fun i : ℕ => f (i + (D + 1))) :=
      (summable_nat_add_iff (D + 1)).mpr hs.summable
    have hlim : Tendsto (fun K : ℕ => |∑ i ∈ range K, f (i + (D + 1))|) atTop
        (𝓝 |∑' i : ℕ, f (i + (D + 1))|) :=
      continuous_abs.continuousAt.tendsto.comp hsub_sum.hasSum.tendsto_sum_nat
    refine le_of_tendsto hlim (Eventually.of_forall fun K => ?_)
    -- Finite partial summation of `∑_{i < K} μ(D + 1 + i) / (D + 1 + i)²`
    set m : ℕ → ℝ := fun k => _root_.RHTower.Sieve.mertensM (D + k)
    set w : ℕ → ℝ := fun k => 1 / ((D + k : ℕ) : ℝ) ^ 2
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
    have hterm : ∀ i : ℕ, f (i + (D + 1)) =
        (m (i + 1) * w (i + 1) - m i * w i) + m i * (w i - w (i + 1)) := by
      intro i
      have hidx : i + (D + 1) = D + (i + 1) := by omega
      have hdiff_m : m (i + 1) - m i = (μ (D + (i + 1)) : ℝ) := by
        dsimp only [m]
        unfold _root_.RHTower.Sieve.mertensM
        have h1 : D + (i + 1) + 1 = (D + i + 1) + 1 := by omega
        have h2 : D + i + 1 = D + (i + 1) := by omega
        rw [h1, Finset.sum_range_succ, add_sub_cancel_left, h2]
      have hfeq : f (i + (D + 1)) = (m (i + 1) - m i) * w (i + 1) := by
        rw [hidx, hdiff_m]
        simp only [f, w]
        ring
      rw [hfeq]
      ring
    have hsum_K : ∑ i ∈ range K, f (i + (D + 1)) =
        (m K * w K - m 0 * w 0) + ∑ i ∈ range K, m i * (w i - w (i + 1)) := by
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun k => m k * w k) K]
    have hbd_mw : ∀ k : ℕ, |m k * w k| ≤ C_M * (D : ℝ) ^ (-3 / 2 + δ) := by
      intro k
      have hDk1 : 1 ≤ D + k := by omega
      have hDk0 : (0 : ℝ) < (D + k : ℕ) := by exact_mod_cast hDk1
      have hD_le : (D : ℝ) ≤ ((D + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right D k
      rw [abs_mul, abs_of_pos (show 0 < w k by simp only [w]; positivity)]
      calc |m k| * w k
          ≤ (C_M * ((D + k : ℕ) : ℝ) ^ (1 / 2 + δ)) * (1 / ((D + k : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (hmert_pow (D + k) hDk1) (by positivity)
        _ = C_M * (((D + k : ℕ) : ℝ) ^ (1 / 2 + δ) / ((D + k : ℕ) : ℝ) ^ (2 : ℝ)) := by
            rw [Real.rpow_two]; ring
        _ = C_M * ((D + k : ℕ) : ℝ) ^ (-3 / 2 + δ) := by
            rw [← Real.rpow_sub hDk0, show (1 / 2 + δ : ℝ) - 2 = -3 / 2 + δ by ring]
        _ ≤ C_M * (D : ℝ) ^ (-3 / 2 + δ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hD0 hD_le (by linarith)) hC_M0
    have hbd_step : ∀ i : ℕ,
        |m i * (w i - w (i + 1))| ≤
          6 * C_M * ((i + (D + 1) : ℕ) : ℝ) ^ (-(5 / 2 - δ)) := by
      intro i
      set u : ℝ := ((D + i : ℕ) : ℝ)
      have hu1 : 1 ≤ u := by
        simp only [u]
        exact_mod_cast (by omega : 1 ≤ D + i)
      have hu0 : 0 < u := by linarith
      have hu_succ : ((D + (i + 1) : ℕ) : ℝ) = u + 1 := by
        simp only [u]; push_cast; ring
      have hu_idx : ((i + (D + 1) : ℕ) : ℝ) = u + 1 := by
        simp only [u]; push_cast; ring
      have hw_nonneg : 0 ≤ w i - w (i + 1) := by
        simp only [w, hu_succ]
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (sq_pos_of_pos hu0) (by nlinarith))
      have hw_le : w i - w (i + 1) ≤ 6 / (u + 1) ^ 3 := by
        simp only [w, hu_succ]
        rw [div_sub_div _ _ (sq_pos_of_pos hu0).ne' (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        have hquad : (2 * u + 1) * (u + 1) ≤ 6 * u ^ 2 := by
          linarith [hu1, sq_nonneg (u - 1)]
        calc (1 * (u + 1) ^ 2 - u ^ 2 * 1) * (u + 1) ^ 3
            = ((2 * u + 1) * (u + 1)) * (u + 1) ^ 2 := by ring
          _ ≤ (6 * u ^ 2) * (u + 1) ^ 2 := mul_le_mul_of_nonneg_right hquad (by positivity)
          _ = 6 * (u ^ 2 * (u + 1) ^ 2) := by ring
      have hm_le : |m i| ≤ C_M * (u + 1) ^ (1 / 2 + δ) := by
        calc |m i| ≤ C_M * u ^ (1 / 2 + δ) := hmert_pow (D + i) (by omega)
          _ ≤ C_M * (u + 1) ^ (1 / 2 + δ) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hu0.le (by linarith) (by linarith)) hC_M0
      rw [abs_mul, abs_of_nonneg hw_nonneg, hu_idx]
      calc |m i| * (w i - w (i + 1))
          ≤ (C_M * (u + 1) ^ (1 / 2 + δ)) * (6 / (u + 1) ^ 3) :=
            mul_le_mul hm_le hw_le hw_nonneg (by positivity)
        _ = 6 * C_M * ((u + 1) ^ (1 / 2 + δ) / (u + 1) ^ (3 : ℝ)) := by
            rw [show (u + 1) ^ (3 : ℝ) = (u + 1) ^ (3 : ℕ) from Real.rpow_natCast (u + 1) 3]
            ring
        _ = 6 * C_M * (u + 1) ^ (-(5 / 2 - δ)) := by
            rw [← Real.rpow_sub (by positivity),
              show (1 / 2 + δ : ℝ) - 3 = -(5 / 2 - δ) by ring]
    have hsum_step : |∑ i ∈ range K, m i * (w i - w (i + 1))| ≤
        (6 * C_M / (3 / 2 - δ)) * (D : ℝ) ^ (-3 / 2 + δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hbd_step i).trans ?_
      rw [← Finset.mul_sum]
      have hp := _root_.RHTower.sum_range_add_rpow_neg_le (c := 5 / 2 - δ) (by linarith) hD1 K
      rw [show (1 : ℝ) - (5 / 2 - δ) = -3 / 2 + δ by ring,
        show (5 / 2 - δ : ℝ) - 1 = 3 / 2 - δ by ring] at hp
      calc 6 * C_M * ∑ i ∈ range K, ((i + (D + 1) : ℕ) : ℝ) ^ (-(5 / 2 - δ))
          ≤ 6 * C_M * ((D : ℝ) ^ (-3 / 2 + δ) / (3 / 2 - δ)) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (6 * C_M / (3 / 2 - δ)) * (D : ℝ) ^ (-3 / 2 + δ) := by ring
    rw [hsum_K]
    calc |(m K * w K - m 0 * w 0) + ∑ i ∈ range K, m i * (w i - w (i + 1))|
        ≤ |m K * w K - m 0 * w 0| + |∑ i ∈ range K, m i * (w i - w (i + 1))| := abs_add_le _ _
      _ ≤ (|m K * w K| + |m 0 * w 0|) + (6 * C_M / (3 / 2 - δ)) * (D : ℝ) ^ (-3 / 2 + δ) :=
          add_le_add (abs_sub _ _) hsum_step
      _ ≤ (C_M * (D : ℝ) ^ (-3 / 2 + δ) + C_M * (D : ℝ) ^ (-3 / 2 + δ)) +
            (6 * C_M / (3 / 2 - δ)) * (D : ℝ) ^ (-3 / 2 + δ) :=
          add_le_add (add_le_add (hbd_mw K) (hbd_mw 0)) le_rfl
      _ = C₂ * (D : ℝ) ^ (-3 / 2 + δ) := by simp only [C₂]; ring

/-- **Exact characterization of the RH rate for the horoball profile `H(X)`.**
`H(X) - 3/(2π) X² = O_ε(X^{1/2 + ε})` holds iff **both** `RiemannHypothesis` holds **and** the
Möbius × quarter-disc lattice remainder `∑_{d ≤ X} μ(d) E(X/d)` satisfies `O_ε(X^{1/2 + ε})`. -/
theorem horoball_rh_rate_iff_rh_and_moebius_circle :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      |horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2| ≤ C * X ^ (1 / 2 + ε)) ↔
    RiemannHypothesis ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
        |∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)| ≤ C * X ^ (1 / 2 + ε)) := by
  -- Helper transferring `O_ε(X^{1/2 + ε})` on `H(X)` to `O_ε(y^{3/4 - ε})` on `shellCount 2 3`
  have hshell23_of_horoball :
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
        |horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2| ≤ C * X ^ (1 / 2 + ε)) →
      ∀ ε : ℝ, 0 < ε → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖horocycleMean (fun z => (shellCount 2 3 z : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε) := by
    intro hH ε hε
    set δ : ℝ := min (2 * ε) 1
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨CH, hCH⟩ := hH δ hδ0
    set C_H : ℝ := max CH 0
    have hC_H0 : 0 ≤ C_H := le_max_right _ _
    set c₀ : ℝ := 6 / Real.pi * (1 / 2 - 1 / 3)
    set C₁ : ℝ := 8 * C_H
    set m₀ : ℝ := min 1 ((1 / 3 : ℝ) ^ (3 / 4 - ε))
    have hm₀ : 0 < m₀ := lt_min one_pos (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨(c₀ : ℂ), max C₁ ((2 + |c₀|) / m₀), fun y hy hy1 => ?_⟩
    by_cases hy3 : y ≤ 1 / 3
    · set Xa : ℝ := 1 / Real.sqrt (2 * y)
      set Xb : ℝ := 1 / Real.sqrt (3 * y)
      have hay : 0 < 2 * y := by linarith
      have hby : 0 < 3 * y := by linarith
      have hsa0 : 0 < Real.sqrt (2 * y) := Real.sqrt_pos.mpr hay
      have hsb0 : 0 < Real.sqrt (3 * y) := Real.sqrt_pos.mpr hby
      have hXb : 1 ≤ Xb := by
        rw [le_div_iff₀ hsb0, one_mul]
        exact Real.sqrt_le_one.mpr (by linarith)
      have hXab : Xb ≤ Xa := one_div_le_one_div_of_le hsa0 (Real.sqrt_le_sqrt (by linarith))
      have hXa : 1 ≤ Xa := hXb.trans hXab
      set N := ⌈Xa⌉₊
      have hNa : Xa ≤ N := Nat.le_ceil Xa
      have hN : 1 < ((N : ℝ) + 1) ^ 2 * 2 * y := by
        have h1 : Xa ^ 2 * (2 * y) = 1 := by
          simp only [Xa]; rw [div_pow, one_pow, Real.sq_sqrt hay.le]; field_simp
        have h2 : Xa ^ 2 < ((N : ℝ) + 1) ^ 2 :=
          pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
        nlinarith
      rw [horocycleMean_shell_eq (by norm_num) (by norm_num) hy (by linarith) hN,
        horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le hNa),
        horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le (hXab.trans hNa)),
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hmain : 4 * y * (3 / (2 * Real.pi) * Xa ^ 2 - 3 / (2 * Real.pi) * Xb ^ 2) = c₀ := by
        simp only [Xa, Xb, c₀, div_pow, one_pow, Real.sq_sqrt hay.le, Real.sq_sqrt hby.le]
        field_simp; ring
      have hkey : 4 * y * (horoballSum Xa ⌊Xa⌋₊ - horoballSum Xb ⌊Xb⌋₊) - c₀ =
          4 * y * (horoballSum Xa ⌊Xa⌋₊ - 3 / (2 * Real.pi) * Xa ^ 2) -
            4 * y * (horoballSum Xb ⌊Xb⌋₊ - 3 / (2 * Real.pi) * Xb ^ 2) := by
        rw [← hmain]; ring
      have hXa_pow : Xa ^ (1 / 2 + δ) ≤ y ^ (-(1 / 4 + δ / 2)) := by
        have hXa_le : Xa ≤ y ^ (-(1 / 2 : ℝ)) := by
          simp only [Xa]
          rw [Real.rpow_neg hy.le, ← one_div, ← Real.sqrt_eq_rpow]
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hy) (Real.sqrt_le_sqrt (by linarith))
        calc Xa ^ (1 / 2 + δ)
            ≤ (y ^ (-(1 / 2 : ℝ))) ^ (1 / 2 + δ) :=
              Real.rpow_le_rpow (by linarith) hXa_le (by linarith)
          _ = y ^ (-(1 / 4 + δ / 2)) := by
              rw [← Real.rpow_mul hy.le]; congr 1; ring
      have hXb_pow : Xb ^ (1 / 2 + δ) ≤ y ^ (-(1 / 4 + δ / 2)) :=
        (Real.rpow_le_rpow (by linarith) hXab (by linarith)).trans hXa_pow
      have hy_prod : y * y ^ (-(1 / 4 + δ / 2)) = y ^ (3 / 4 - δ / 2) := by
        calc y * y ^ (-(1 / 4 + δ / 2))
            = y ^ (1 : ℝ) * y ^ (-(1 / 4 + δ / 2)) := by rw [Real.rpow_one]
          _ = y ^ (1 + -(1 / 4 + δ / 2)) := (Real.rpow_add hy 1 _).symm
          _ = y ^ (3 / 4 - δ / 2) := by congr 1; ring
      have hy_mon : y ^ (3 / 4 - δ / 2) ≤ y ^ (3 / 4 - ε) :=
        Real.rpow_le_rpow_of_exponent_ge hy hy1 (by simp only [δ]; linarith [min_le_left (2 * ε) 1])
      rw [hkey]
      calc |4 * y * (horoballSum Xa ⌊Xa⌋₊ - 3 / (2 * Real.pi) * Xa ^ 2) -
              4 * y * (horoballSum Xb ⌊Xb⌋₊ - 3 / (2 * Real.pi) * Xb ^ 2)|
          ≤ 4 * y * (C_H * Xa ^ (1 / 2 + δ)) + 4 * y * (C_H * Xb ^ (1 / 2 + δ)) := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul (4 * y), abs_mul (4 * y), abs_of_nonneg (by positivity)]
            exact add_le_add
              (mul_le_mul_of_nonneg_left ((hCH Xa hXa).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (by positivity))
              (mul_le_mul_of_nonneg_left ((hCH Xb hXb).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (by positivity))
        _ ≤ 8 * C_H * (y * y ^ (-(1 / 4 + δ / 2))) := by
            have h1 : 4 * y * (C_H * Xa ^ (1 / 2 + δ)) ≤
                4 * y * (C_H * y ^ (-(1 / 4 + δ / 2))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXa_pow hC_H0) (by positivity)
            have h2 : 4 * y * (C_H * Xb ^ (1 / 2 + δ)) ≤
                4 * y * (C_H * y ^ (-(1 / 4 + δ / 2))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXb_pow hC_H0) (by positivity)
            linarith
        _ = C₁ * y ^ (3 / 4 - δ / 2) := by rw [hy_prod]
        _ ≤ max C₁ ((2 + |c₀|) / m₀) * y ^ (3 / 4 - ε) :=
            mul_le_mul (le_max_left _ _) hy_mon (by positivity)
              (le_trans (by positivity : 0 ≤ C₁) (le_max_left _ _))
    · push Not at hy3
      have hm_le : m₀ ≤ y ^ (3 / 4 - ε) := by
        rcases le_or_gt (3 / 4 - ε) 0 with hexp | hexp
        · calc m₀ ≤ 1 := min_le_left _ _
            _ = (1 : ℝ) ^ (3 / 4 - ε) := (Real.one_rpow _).symm
            _ ≤ y ^ (3 / 4 - ε) := Real.rpow_le_rpow_of_nonpos hy hy1 hexp
        · calc m₀ ≤ (1 / 3 : ℝ) ^ (3 / 4 - ε) := min_le_right _ _
            _ ≤ y ^ (3 / 4 - ε) := Real.rpow_le_rpow (by norm_num) hy3.le hexp.le
      calc ‖horocycleMean (fun z => (shellCount 2 3 z : ℂ)) y - (c₀ : ℂ)‖
          ≤ ‖horocycleMean (fun z => (shellCount 2 3 z : ℂ)) y‖ + ‖(c₀ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + |c₀| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add (norm_horocycleMean_shellCount_le_two (b := 3) (by norm_num : (1 : ℝ) < 2) y) le_rfl
        _ = ((2 + |c₀|) / m₀) * m₀ := by rw [div_mul_cancel₀ _ hm₀.ne']
        _ ≤ max C₁ ((2 + |c₀|) / m₀) * y ^ (3 / 4 - ε) :=
            mul_le_mul (le_max_right _ _) hm_le hm₀.le
              (le_trans (by positivity) (le_max_right _ _))
  -- Helper bounding the two Möbius main-term remainders in `horoballSum_decomposition` under RH
  have hmoeb_terms : ∀ hRH : RiemannHypothesis, ∀ ε : ℝ, 0 < ε →
      ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ X : ℝ, 1 ≤ X →
        |-(X / 2 * ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / d) +
          Real.pi / 4 * X ^ 2 * (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤
          C_m * X ^ (1 / 2 + ε) := by
    intro hRH ε hε
    set δ : ℝ := min ε (1 / 4)
    have hδ0 : 0 < δ := lt_min hε (by norm_num)
    have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
    obtain ⟨C₁, C₂, hC₁0, hC₂0, htail⟩ := moebius_harmonic_and_sq_tail_of_rh hRH hδ0 hδ4
    set C_m : ℝ := C₁ * 2 ^ (1 / 2 - δ) + Real.pi / 4 * C₂ * 2 ^ (3 / 2 - δ)
    refine ⟨C_m, by positivity, fun X hX => ?_⟩
    set D := ⌊X⌋₊
    have hD1 : 1 ≤ D := Nat.le_floor (by exact_mod_cast hX)
    have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
    have hXD2 : X / 2 ≤ (D : ℝ) := by
      have := Nat.lt_floor_add_one X
      linarith
    obtain ⟨ht1, ht2⟩ := htail D hD1
    have hD_pow1 : (D : ℝ) ^ (-1 / 2 + δ) ≤ 2 ^ (1 / 2 - δ) * X ^ (-1 / 2 + δ) := by
      calc (D : ℝ) ^ (-1 / 2 + δ)
          ≤ (X / 2) ^ (-1 / 2 + δ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hXD2 (by linarith)
        _ = 2 ^ (1 / 2 - δ) * X ^ (-1 / 2 + δ) := by
            rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
              Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two]
            ring_nf
    have hD_pow2 : (D : ℝ) ^ (-3 / 2 + δ) ≤ 2 ^ (3 / 2 - δ) * X ^ (-3 / 2 + δ) := by
      calc (D : ℝ) ^ (-3 / 2 + δ)
          ≤ (X / 2) ^ (-3 / 2 + δ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hXD2 (by linarith)
        _ = 2 ^ (3 / 2 - δ) * X ^ (-3 / 2 + δ) := by
            rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
              Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two]
            ring_nf
    have hX_prod1 : X * X ^ (-1 / 2 + δ) = X ^ (1 / 2 + δ) := by
      calc X * X ^ (-1 / 2 + δ)
          = X ^ (1 : ℝ) * X ^ (-1 / 2 + δ) := by rw [Real.rpow_one]
        _ = X ^ (1 + (-1 / 2 + δ)) := (Real.rpow_add (by positivity) 1 _).symm
        _ = X ^ (1 / 2 + δ) := by congr 1; ring
    have hX_prod2 : X ^ 2 * X ^ (-3 / 2 + δ) = X ^ (1 / 2 + δ) := by
      rw [← Real.rpow_two X, ← Real.rpow_add (by positivity)]
      congr 1; ring
    have hX_mon : X ^ (1 / 2 + δ) ≤ X ^ (1 / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith [min_le_left ε (1 / 4)])
    have hterm1 : |-(X / 2 * ∑ d ∈ Icc 1 D, (μ d : ℝ) / d)| ≤
        C₁ * 2 ^ (1 / 2 - δ) * X ^ (1 / 2 + δ) := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity)]
      calc X / 2 * |∑ d ∈ Icc 1 D, (μ d : ℝ) / d|
          ≤ X * (C₁ * (D : ℝ) ^ (-1 / 2 + δ)) := by
            have : X / 2 ≤ X := by linarith
            exact mul_le_mul this ht1 (abs_nonneg _) (by positivity)
        _ ≤ X * (C₁ * (2 ^ (1 / 2 - δ) * X ^ (-1 / 2 + δ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD_pow1 hC₁0) (by positivity)
        _ = C₁ * 2 ^ (1 / 2 - δ) * (X * X ^ (-1 / 2 + δ)) := by ring
        _ = C₁ * 2 ^ (1 / 2 - δ) * X ^ (1 / 2 + δ) := by rw [hX_prod1]
    have hterm2 : |Real.pi / 4 * X ^ 2 *
        (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)| ≤
        (Real.pi / 4 * C₂ * 2 ^ (3 / 2 - δ)) * X ^ (1 / 2 + δ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc Real.pi / 4 * X ^ 2 * |∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2|
          ≤ Real.pi / 4 * X ^ 2 * (C₂ * (2 ^ (3 / 2 - δ) * X ^ (-3 / 2 + δ))) :=
            mul_le_mul_of_nonneg_left (ht2.trans (mul_le_mul_of_nonneg_left hD_pow2 hC₂0))
              (by positivity)
        _ = (Real.pi / 4 * C₂ * 2 ^ (3 / 2 - δ)) * (X ^ 2 * X ^ (-3 / 2 + δ)) := by ring
        _ = (Real.pi / 4 * C₂ * 2 ^ (3 / 2 - δ)) * X ^ (1 / 2 + δ) := by rw [hX_prod2]
    calc |-(X / 2 * ∑ d ∈ Icc 1 D, (μ d : ℝ) / d) +
            Real.pi / 4 * X ^ 2 * (∑ d ∈ Icc 1 D, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)|
        ≤ C_m * X ^ (1 / 2 + δ) := by
          refine (abs_add_le _ _).trans ?_
          calc _ ≤ C₁ * 2 ^ (1 / 2 - δ) * X ^ (1 / 2 + δ) +
                (Real.pi / 4 * C₂ * 2 ^ (3 / 2 - δ)) * X ^ (1 / 2 + δ) :=
                  add_le_add hterm1 hterm2
            _ = C_m * X ^ (1 / 2 + δ) := by simp only [C_m]; ring
      _ ≤ C_m * X ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_left hX_mon (by positivity)
  constructor
  · intro hH
    have hRH : RiemannHypothesis :=
      riemannHypothesis_of_single_shell_rate (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
        (hshell23_of_horoball hH)
    refine ⟨hRH, fun ε hε => ?_⟩
    obtain ⟨CH, hCH⟩ := hH ε hε
    obtain ⟨Cm, hCm0, hCm⟩ := hmoeb_terms hRH ε hε
    refine ⟨max CH 0 + Cm, fun X hX => ?_⟩
    have hdec : horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2 =
        (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)) +
          (-(X / 2 * ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / d) +
            Real.pi / 4 * X ^ 2 *
              (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)) := by
      rw [← horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le (Nat.le_ceil X)),
        horoballSum_decomposition (by linarith) (Nat.le_ceil X)]
      ring
    have heq_mc : (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)) =
        (horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2) -
          (-(X / 2 * ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / d) +
            Real.pi / 4 * X ^ 2 *
              (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)) := by
      linarith [hdec]
    rw [heq_mc]
    refine (abs_sub _ _).trans ?_
    calc |horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2| + _
        ≤ max CH 0 * X ^ (1 / 2 + ε) + Cm * X ^ (1 / 2 + ε) :=
          add_le_add
            ((hCH X hX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
            (hCm X hX)
      _ = (max CH 0 + Cm) * X ^ (1 / 2 + ε) := by ring
  · rintro ⟨hRH, hMC⟩ ε hε
    obtain ⟨C_mc, hC_mc⟩ := hMC ε hε
    obtain ⟨Cm, hCm0, hCm⟩ := hmoeb_terms hRH ε hε
    refine ⟨max C_mc 0 + Cm, fun X hX => ?_⟩
    have hdec : horoballSum X ⌊X⌋₊ - 3 / (2 * Real.pi) * X ^ 2 =
        (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)) +
          (-(X / 2 * ∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / d) +
            Real.pi / 4 * X ^ 2 *
              (∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) / (d : ℝ) ^ 2 - 6 / Real.pi ^ 2)) := by
      rw [← horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le (Nat.le_ceil X)),
        horoballSum_decomposition (by linarith) (Nat.le_ceil X)]
      ring
    rw [hdec]
    refine (abs_add_le _ _).trans ?_
    calc |∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)| + _
        ≤ max C_mc 0 * X ^ (1 / 2 + ε) + Cm * X ^ (1 / 2 + ε) :=
          add_le_add
            ((hC_mc X hX).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
            (hCm X hX)
      _ = (max C_mc 0 + Cm) * X ^ (1 / 2 + ε) := by ring

/-- **Exact characterization of the RH rate for ANY single sharp shell `1 < a < b`.**
A single sharp shell `1 < a < b` thermalizes at the RH rate `O_ε(y^{3/4 - ε})` iff **both**
`RiemannHypothesis` holds **and** the Möbius × circle-problem sum satisfies
`∑_{d ≤ X} μ(d) E(X/d) = O_ε(X^{1/2 + ε})`. Thus the arithmetic obstruction is independent of the
choice of sharp shell `(a, b)`. -/
theorem single_shell_rh_rate_iff_rh_and_moebius_circle {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    (∀ ε : ℝ, 0 < ε → ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - c‖ ≤ C * y ^ (3 / 4 - ε)) ↔
    RiemannHypothesis ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
        |∑ d ∈ Icc 1 ⌊X⌋₊, (μ d : ℝ) * circleRemainder (X / d)| ≤ C * X ^ (1 / 2 + ε)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := lt_trans ha0 hab
  rw [← horoball_rh_rate_iff_rh_and_moebius_circle]
  constructor
  · -- Forward: telescope `R(r^k X) - R(r^{k+1} X)` with `r = √(a/b) < 1` down to `r^K X < 1`
    intro hsh ε hε
    classical
    set ε' : ℝ := min (ε / 2) (1 / 8)
    have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
    have hε'8 : ε' ≤ 1 / 8 := min_le_right _ _
    obtain ⟨c, C₀, hrate⟩ := hsh ε' hε'0
    set K₀ : ℝ := max C₀ 0
    have hK₀0 : 0 ≤ K₀ := le_max_right _ _
    set c₀ : ℝ := 6 / Real.pi * (1 / a - 1 / b)
    -- Step 1: Identify `c = (c₀ : ℂ)` via `shell_rate_sqrt` as `y → 0⁺`
    have hc_eq : c = (c₀ : ℂ) := by
      by_contra hne
      have hd : 0 < ‖c - (c₀ : ℂ)‖ := norm_sub_pos_iff.mpr hne
      set M : ℝ := K₀ + 76 / Real.sqrt a + 76 / Real.sqrt b + 1
      have hM0 : 0 < M := by positivity
      set y₀ : ℝ := min (min 1 (1 / b)) ((‖c - (c₀ : ℂ)‖ / (2 * M)) ^ 2)
      have hy₀0 : 0 < y₀ := lt_min (lt_min one_pos (by positivity)) (by positivity)
      have hy₀1 : y₀ ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hy₀b : y₀ ≤ 1 / b := le_trans (min_le_left _ _) (min_le_right _ _)
      have hsy₀ : Real.sqrt y₀ ≤ ‖c - (c₀ : ℂ)‖ / (2 * M) := by
        calc Real.sqrt y₀
            ≤ Real.sqrt ((‖c - (c₀ : ℂ)‖ / (2 * M)) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
          _ = ‖c - (c₀ : ℂ)‖ / (2 * M) := Real.sqrt_sq (by positivity)
      have hy_pow : y₀ ^ (3 / 4 - ε') ≤ Real.sqrt y₀ := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge hy₀0 hy₀1 (by linarith)
      have hr1 := (hrate y₀ hy₀0 hy₀1).trans
        (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
      have hr2 := shell_rate_sqrt ha0 hab.le hy₀0 hy₀b (by linarith)
      have htri : ‖c - (c₀ : ℂ)‖ ≤
          ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y₀ - c‖ +
            ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y₀ - (c₀ : ℂ)‖ := by
        have : c - (c₀ : ℂ) =
            (horocycleMean (fun z => (shellCount a b z : ℂ)) y₀ - (c₀ : ℂ)) -
              (horocycleMean (fun z => (shellCount a b z : ℂ)) y₀ - c) := by ring
        rw [this]
        exact (norm_sub_le _ _).trans_eq (add_comm _ _)
      have hsum_bd : K₀ * y₀ ^ (3 / 4 - ε') + 76 * (Real.sqrt (y₀ / a) + Real.sqrt (y₀ / b)) ≤
          M * Real.sqrt y₀ := by
        rw [Real.sqrt_div hy₀0.le, Real.sqrt_div hy₀0.le]
        have : 76 * (Real.sqrt y₀ / Real.sqrt a + Real.sqrt y₀ / Real.sqrt b) =
            (76 / Real.sqrt a + 76 / Real.sqrt b) * Real.sqrt y₀ := by ring
        rw [this]
        have h1 : K₀ * y₀ ^ (3 / 4 - ε') ≤ K₀ * Real.sqrt y₀ :=
          mul_le_mul_of_nonneg_left hy_pow hK₀0
        simp only [M]
        nlinarith [Real.sqrt_pos.mpr hy₀0]
      have hlt_half : M * Real.sqrt y₀ ≤ ‖c - (c₀ : ℂ)‖ / 2 := by
        calc M * Real.sqrt y₀
            ≤ M * (‖c - (c₀ : ℂ)‖ / (2 * M)) := mul_le_mul_of_nonneg_left hsy₀ hM0.le
          _ = ‖c - (c₀ : ℂ)‖ / 2 := by field_simp
      linarith [htri, hr1, hr2, hsum_bd, hlt_half]
    -- Step 2: Difference bound `|R u - R (r * u)| ≤ C₁ u^{1/2 + 2ε'}` for `u ≥ 1`, `r = √(a/b)`
    set R : ℝ → ℝ := fun Z => horoballSum Z ⌊Z⌋₊ - 3 / (2 * Real.pi) * Z ^ 2
    set r : ℝ := Real.sqrt (a / b)
    have hr0 : 0 < r := Real.sqrt_pos.mpr (div_pos ha0 hb0)
    have hr1 : r < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (div_nonneg ha0.le hb0.le) ((div_lt_one hb0).mpr hab)
    have hr_sq : r ^ 2 = a / b := Real.sq_sqrt (div_nonneg ha0.le hb0.le)
    set C₁ : ℝ := K₀ * a ^ (1 / 4 + ε') / 4
    have hC₁0 : 0 ≤ C₁ := by positivity
    have hdiff_R : ∀ u : ℝ, 1 ≤ u → |R u - R (r * u)| ≤ C₁ * u ^ (1 / 2 + 2 * ε') := by
      intro u hu
      have hu0 : 0 < u := by linarith
      set y : ℝ := 1 / (a * u ^ 2)
      have hay_den : 0 < a * u ^ 2 := by positivity
      have hy0 : 0 < y := div_pos one_pos hay_den
      have hy1 : y ≤ 1 := by
        have : 1 ≤ a * u ^ 2 := by nlinarith
        exact div_le_one_of_le₀ this hay_den.le
      have hXa : 1 / Real.sqrt (a * y) = u := by
        have : a * y = (1 / u) ^ 2 := by simp only [y]; field_simp
        rw [this, Real.sqrt_sq (by positivity), one_div_one_div]
      have hXb : 1 / Real.sqrt (b * y) = r * u := by
        have : b * y = (1 / (r * u)) ^ 2 := by
          simp only [y]
          rw [div_pow, one_pow, mul_pow, hr_sq]
          field_simp
        rw [this, Real.sqrt_sq (by positivity), one_div_one_div]
      set N := ⌈u⌉₊
      have hNu : u ≤ N := Nat.le_ceil u
      have hN : 1 < ((N : ℝ) + 1) ^ 2 * a * y := by
        simp only [y]
        rw [show ((N : ℝ) + 1) ^ 2 * a * (1 / (a * u ^ 2)) = ((N : ℝ) + 1) ^ 2 / u ^ 2 by
          field_simp]
        rw [one_lt_div (sq_pos_of_pos hu0)]
        exact pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
      have hru_le : r * u ≤ N := by nlinarith [hr1.le]
      have hmean := horocycleMean_shell_eq ha0 hab.le hy0 (by linarith) hN
      rw [hXa, hXb, horoballSum_eq_horoballSum_floor hu0.le (Nat.floor_le_of_le hNu),
        horoballSum_eq_horoballSum_floor (by positivity) (Nat.floor_le_of_le hru_le)] at hmean
      have hmain : 4 * y * (3 / (2 * Real.pi) * u ^ 2 - 3 / (2 * Real.pi) * (r * u) ^ 2) = c₀ := by
        simp only [y, c₀]
        rw [mul_pow, hr_sq]
        field_simp
        ring
      have hident : 4 * y * (R u - R (r * u)) =
          4 * y * (horoballSum u ⌊u⌋₊ - horoballSum (r * u) ⌊r * u⌋₊) - c₀ := by
        simp only [R]; rw [← hmain]; ring
      have hbd_y : |4 * y * (R u - R (r * u))| ≤ K₀ * y ^ (3 / 4 - ε') := by
        have hr := (hrate y hy0 hy1).trans
          (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
        rw [hc_eq, hmean, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← hident] at hr
        exact hr
      rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * y)] at hbd_y
      have hy_rpow : y ^ (3 / 4 - ε') = a ^ (-(3 / 4 - ε')) * u ^ (-2 * (3 / 4 - ε')) := by
        simp only [y, one_div]
        rw [Real.inv_rpow hay_den.le, Real.mul_rpow ha0.le (sq_nonneg u),
          ← Real.rpow_two u, ← Real.rpow_mul hu0.le,
          mul_inv, ← Real.rpow_neg ha0.le, ← Real.rpow_neg hu0.le]
        congr 2; ring
      have ha_prod : a * a ^ (-(3 / 4 - ε')) = a ^ (1 / 4 + ε') := by
        calc a * a ^ (-(3 / 4 - ε'))
            = a ^ (1 : ℝ) * a ^ (-(3 / 4 - ε')) := by rw [Real.rpow_one]
          _ = a ^ (1 + -(3 / 4 - ε')) := (Real.rpow_add ha0 1 _).symm
          _ = a ^ (1 / 4 + ε') := by congr 1; ring
      have hu_prod : u ^ 2 * u ^ (-2 * (3 / 4 - ε')) = u ^ (1 / 2 + 2 * ε') := by
        rw [← Real.rpow_two u, ← Real.rpow_add hu0]; congr 1; ring
      calc |R u - R (r * u)|
          = (a * u ^ 2 / 4) * (4 * y * |R u - R (r * u)|) := by
              simp only [y]; field_simp
        _ ≤ (a * u ^ 2 / 4) * (K₀ * y ^ (3 / 4 - ε')) :=
              mul_le_mul_of_nonneg_left hbd_y (by positivity)
        _ = (K₀ * (a * a ^ (-(3 / 4 - ε'))) / 4) * (u ^ 2 * u ^ (-2 * (3 / 4 - ε'))) := by
              rw [hy_rpow]; ring
        _ = C₁ * u ^ (1 / 2 + 2 * ε') := by rw [ha_prod, hu_prod]
    -- Step 3: Geometric telescoping over `k < K` with `r^K X < 1`
    set q : ℝ := r ^ (1 / 2 + 2 * ε')
    have hq0 : 0 < q := Real.rpow_pos_of_pos hr0 _
    have hq1 : q < 1 := Real.rpow_lt_one hr0.le hr1 (by linarith)
    have hgeom : ∀ K : ℕ, ∑ k ∈ range K, q ^ k ≤ 1 / (1 - q) := by
      intro K
      have hpos : 0 < 1 - q := by linarith
      rw [le_div_iff₀ hpos]
      have hid : (∑ k ∈ range K, q ^ k) * (1 - q) = 1 - q ^ K := by
        induction K with
        | zero => simp
        | succ K ih =>
          rw [Finset.sum_range_succ, add_mul, ih]
          ring
      linarith [hid, pow_nonneg hq0.le K]
    refine ⟨C₁ / (1 - q) + 1, fun X hX => ?_⟩
    have hX0 : 0 < X := by linarith
    have hex : ∃ k : ℕ, r ^ k * X < 1 := by
      have ht : Tendsto (fun k : ℕ => r ^ k * X) atTop (𝓝 (0 * X)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const X
      rw [zero_mul] at ht
      exact (ht.eventually (gt_mem_nhds one_pos)).exists
    set K : ℕ := Nat.find hex
    have hK_lt : r ^ K * X < 1 := Nat.find_spec hex
    have hK_min : ∀ k < K, 1 ≤ r ^ k * X := fun k hk => not_lt.mp (Nat.find_min hex hk)
    have hRK : |R (r ^ K * X)| ≤ 1 := by
      have hpos : 0 < r ^ K * X := by positivity
      have hfl : ⌊r ^ K * X⌋₊ = 0 := Nat.floor_eq_zero.mpr hK_lt
      simp only [R, hfl, horoballSum, Finset.Icc_eq_empty_of_lt (Nat.zero_lt_one),
        Finset.sum_empty, zero_sub, abs_neg]
      rw [abs_of_nonneg (by positivity)]
      have hsq : (r ^ K * X) ^ 2 ≤ 1 := by nlinarith
      have hpi : 3 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      nlinarith
    have htel : R X - R (r ^ K * X) =
        ∑ k ∈ range K, (R (r ^ k * X) - R (r ^ (k + 1) * X)) := by
      have := Finset.sum_range_sub' (fun k => R (r ^ k * X)) K
      simpa using this.symm
    have hsum_bd : |R X - R (r ^ K * X)| ≤ (C₁ / (1 - q)) * X ^ (1 / 2 + 2 * ε') := by
      rw [htel]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hstep : ∀ k ∈ range K,
          |R (r ^ k * X) - R (r ^ (k + 1) * X)| ≤ C₁ * X ^ (1 / 2 + 2 * ε') * q ^ k := by
        intro k hk
        have hu1 : 1 ≤ r ^ k * X := hK_min k (Finset.mem_range.mp hk)
        have h1 := hdiff_R (r ^ k * X) hu1
        rw [show r * (r ^ k * X) = r ^ (k + 1) * X by ring] at h1
        refine h1.trans_eq ?_
        rw [Real.mul_rpow (pow_nonneg hr0.le k) hX0.le,
          ← Real.rpow_natCast r k, ← Real.rpow_mul hr0.le, mul_comm (k : ℝ),
          Real.rpow_mul hr0.le, Real.rpow_natCast]
        simp only [q]
        ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum]
      calc C₁ * X ^ (1 / 2 + 2 * ε') * ∑ k ∈ range K, q ^ k
          ≤ C₁ * X ^ (1 / 2 + 2 * ε') * (1 / (1 - q)) :=
            mul_le_mul_of_nonneg_left (hgeom K) (by positivity)
        _ = (C₁ / (1 - q)) * X ^ (1 / 2 + 2 * ε') := by ring
    have hX_mon : X ^ (1 / 2 + 2 * ε') ≤ X ^ (1 / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hX (by simp only [ε']; linarith [min_le_left (ε / 2) (1 / 8)])
    have h1_le : 1 ≤ X ^ (1 / 2 + ε) := Real.one_le_rpow hX (by positivity)
    have hRX : R X = (R X - R (r ^ K * X)) + R (r ^ K * X) := by ring
    change |R X| ≤ (C₁ / (1 - q) + 1) * X ^ (1 / 2 + ε)
    rw [hRX]
    calc |(R X - R (r ^ K * X)) + R (r ^ K * X)|
        ≤ |R X - R (r ^ K * X)| + |R (r ^ K * X)| := abs_add_le _ _
      _ ≤ (C₁ / (1 - q)) * X ^ (1 / 2 + 2 * ε') + 1 := add_le_add hsum_bd hRK
      _ ≤ (C₁ / (1 - q)) * X ^ (1 / 2 + ε) + 1 * X ^ (1 / 2 + ε) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hX_mon (div_nonneg hC₁0 (by linarith)))
            (by linarith)
      _ = (C₁ / (1 - q) + 1) * X ^ (1 / 2 + ε) := by ring
  · -- Backward: transfer `O_ε(X^{1/2 + ε})` on `H(X)` to `shellCount a b` via `horocycleMean_shell_eq`
    intro hH ε hε
    set δ : ℝ := min (2 * ε) 1
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨CH, hCH⟩ := hH δ hδ0
    set C_H : ℝ := max CH 0
    have hC_H0 : 0 ≤ C_H := le_max_right _ _
    set c₀ : ℝ := 6 / Real.pi * (1 / a - 1 / b)
    set C₁ : ℝ := 4 * C_H * (a ^ (-(1 / 4 + δ / 2)) + b ^ (-(1 / 4 + δ / 2)))
    have hC₁0 : 0 ≤ C₁ := by positivity
    set y_cut : ℝ := min 1 (1 / b)
    have hy_cut0 : 0 < y_cut := lt_min one_pos (by positivity)
    set m₀ : ℝ := min 1 (y_cut ^ (3 / 4 - ε))
    have hm₀ : 0 < m₀ := lt_min one_pos (Real.rpow_pos_of_pos hy_cut0 _)
    refine ⟨(c₀ : ℂ), max C₁ ((2 + |c₀|) / m₀), fun y hy hy1 => ?_⟩
    by_cases hyb : y ≤ y_cut
    · have hy_invb : y ≤ 1 / b := hyb.trans (min_le_right _ _)
      set Xa : ℝ := 1 / Real.sqrt (a * y)
      set Xb : ℝ := 1 / Real.sqrt (b * y)
      have hay : 0 < a * y := mul_pos ha0 hy
      have hby : 0 < b * y := mul_pos hb0 hy
      have hsa0 : 0 < Real.sqrt (a * y) := Real.sqrt_pos.mpr hay
      have hsb0 : 0 < Real.sqrt (b * y) := Real.sqrt_pos.mpr hby
      have hby1 : b * y ≤ 1 := by have := (le_div_iff₀ hb0).mp hy_invb; linarith
      have hXb : 1 ≤ Xb := by
        rw [le_div_iff₀ hsb0, one_mul]
        exact Real.sqrt_le_one.mpr hby1
      have hXab : Xb ≤ Xa := one_div_le_one_div_of_le hsa0 (Real.sqrt_le_sqrt (by nlinarith))
      have hXa : 1 ≤ Xa := hXb.trans hXab
      set N := ⌈Xa⌉₊
      have hNa : Xa ≤ N := Nat.le_ceil Xa
      have hN : 1 < ((N : ℝ) + 1) ^ 2 * a * y := by
        have h1 : Xa ^ 2 * (a * y) = 1 := by
          simp only [Xa]; rw [div_pow, one_pow, Real.sq_sqrt hay.le]; field_simp
        have h2 : Xa ^ 2 < ((N : ℝ) + 1) ^ 2 :=
          pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
        nlinarith
      rw [horocycleMean_shell_eq ha0 hab.le hy (by linarith) hN,
        horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le hNa),
        horoballSum_eq_horoballSum_floor (by linarith) (Nat.floor_le_of_le (hXab.trans hNa)),
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hmain : 4 * y * (3 / (2 * Real.pi) * Xa ^ 2 - 3 / (2 * Real.pi) * Xb ^ 2) = c₀ := by
        simp only [Xa, Xb, c₀, div_pow, one_pow, Real.sq_sqrt hay.le, Real.sq_sqrt hby.le]
        field_simp; ring
      have hkey : 4 * y * (horoballSum Xa ⌊Xa⌋₊ - horoballSum Xb ⌊Xb⌋₊) - c₀ =
          4 * y * (horoballSum Xa ⌊Xa⌋₊ - 3 / (2 * Real.pi) * Xa ^ 2) -
            4 * y * (horoballSum Xb ⌊Xb⌋₊ - 3 / (2 * Real.pi) * Xb ^ 2) := by
        rw [← hmain]; ring
      have hpow_eq : ∀ c : ℝ, 0 < c →
          (1 / Real.sqrt (c * y)) ^ (1 / 2 + δ) =
            c ^ (-(1 / 4 + δ / 2)) * y ^ (-(1 / 4 + δ / 2)) := by
        intro c hc
        rw [one_div, Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
          ← Real.rpow_mul (mul_nonneg hc.le hy.le),
          Real.mul_rpow hc.le hy.le, mul_inv, ← Real.rpow_neg hc.le, ← Real.rpow_neg hy.le]
        congr 2 <;> ring
      have hy_prod : y * y ^ (-(1 / 4 + δ / 2)) = y ^ (3 / 4 - δ / 2) := by
        calc y * y ^ (-(1 / 4 + δ / 2))
            = y ^ (1 : ℝ) * y ^ (-(1 / 4 + δ / 2)) := by rw [Real.rpow_one]
          _ = y ^ (1 + -(1 / 4 + δ / 2)) := (Real.rpow_add hy 1 _).symm
          _ = y ^ (3 / 4 - δ / 2) := by congr 1; ring
      have hy_mon : y ^ (3 / 4 - δ / 2) ≤ y ^ (3 / 4 - ε) :=
        Real.rpow_le_rpow_of_exponent_ge hy hy1 (by simp only [δ]; linarith [min_le_left (2 * ε) 1])
      rw [hkey]
      calc |4 * y * (horoballSum Xa ⌊Xa⌋₊ - 3 / (2 * Real.pi) * Xa ^ 2) -
              4 * y * (horoballSum Xb ⌊Xb⌋₊ - 3 / (2 * Real.pi) * Xb ^ 2)|
          ≤ 4 * y * (C_H * Xa ^ (1 / 2 + δ)) + 4 * y * (C_H * Xb ^ (1 / 2 + δ)) := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul (4 * y), abs_mul (4 * y), abs_of_nonneg (by positivity)]
            exact add_le_add
              (mul_le_mul_of_nonneg_left ((hCH Xa hXa).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (by positivity))
              (mul_le_mul_of_nonneg_left ((hCH Xb hXb).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (by positivity))
        _ = 4 * C_H * (a ^ (-(1 / 4 + δ / 2)) + b ^ (-(1 / 4 + δ / 2))) *
              (y * y ^ (-(1 / 4 + δ / 2))) := by
            simp only [Xa, Xb]; rw [hpow_eq a ha0, hpow_eq b hb0]; ring
        _ = C₁ * y ^ (3 / 4 - δ / 2) := by rw [hy_prod]
        _ ≤ max C₁ ((2 + |c₀|) / m₀) * y ^ (3 / 4 - ε) :=
            mul_le_mul (le_max_left _ _) hy_mon (by positivity)
              (le_trans hC₁0 (le_max_left _ _))
    · push Not at hyb
      have hm_le : m₀ ≤ y ^ (3 / 4 - ε) := by
        rcases le_or_gt (3 / 4 - ε) 0 with hexp | hexp
        · calc m₀ ≤ 1 := min_le_left _ _
            _ = (1 : ℝ) ^ (3 / 4 - ε) := (Real.one_rpow _).symm
            _ ≤ y ^ (3 / 4 - ε) := Real.rpow_le_rpow_of_nonpos hy hy1 hexp
        · calc m₀ ≤ y_cut ^ (3 / 4 - ε) := min_le_right _ _
            _ ≤ y ^ (3 / 4 - ε) := Real.rpow_le_rpow hy_cut0.le hyb.le hexp.le
      calc ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y - (c₀ : ℂ)‖
          ≤ ‖horocycleMean (fun z => (shellCount a b z : ℂ)) y‖ + ‖(c₀ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + |c₀| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add (norm_horocycleMean_shellCount_le_two (b := b) ha y) le_rfl
        _ = ((2 + |c₀|) / m₀) * m₀ := by rw [div_mul_cancel₀ _ hm₀.ne']
        _ ≤ max C₁ ((2 + |c₀|) / m₀) * y ^ (3 / 4 - ε) :=
            mul_le_mul (le_max_right _ _) hm_le hm₀.le
              (le_trans (by positivity) (le_max_right _ _))

end GaloisForLFunctions.CountingHolography

end


#print axioms GaloisForLFunctions.CountingHolography.exists_zeta_zero_on_critical_line
#print axioms GaloisForLFunctions.CountingHolography.not_horocycle_rate_gt_three_quarters
#print axioms GaloisForLFunctions.CountingHolography.not_fareyCount_rate_gt_three_quarters
#print axioms GaloisForLFunctions.CountingHolography.not_horocycle_power_saving_gt_quarter
#print axioms GaloisForLFunctions.CountingHolography.horocycle_rate_stretched_exp
#print axioms GaloisForLFunctions.CountingHolography.fareyCount_rate_stretched_exp
#print axioms GaloisForLFunctions.CountingHolography.horocycle_rate_sqrt_exact
#print axioms GaloisForLFunctions.CountingHolography.horocycle_rate_log_pow
#print axioms GaloisForLFunctions.CountingHolography.horocycle_div_sqrt_tendsto_zero
#print axioms GaloisForLFunctions.CountingHolography.sum_Icc_one_div_sqrt_le
#print axioms GaloisForLFunctions.CountingHolography.abs_circleRemainder_le_sqrt
#print axioms GaloisForLFunctions.CountingHolography.horoballSum_eq_horoballSum_floor
#print axioms GaloisForLFunctions.CountingHolography.abs_horoballSum_sub_le_linear
#print axioms GaloisForLFunctions.CountingHolography.shell_rate_sqrt
#print axioms GaloisForLFunctions.CountingHolography.differentiableAt_mellin_shell
#print axioms GaloisForLFunctions.CountingHolography.mellin_shell_eq
#print axioms GaloisForLFunctions.CountingHolography.mellin_shell_ne_zero
#print axioms GaloisForLFunctions.CountingHolography.re_le_of_single_shell_rate
#print axioms GaloisForLFunctions.CountingHolography.not_single_shell_rate_gt_three_quarters
#print axioms GaloisForLFunctions.CountingHolography.riemannHypothesis_of_single_shell_rate
#print axioms GaloisForLFunctions.CountingHolography.moebius_harmonic_and_sq_tail_of_rh
#print axioms GaloisForLFunctions.CountingHolography.horoball_rh_rate_iff_rh_and_moebius_circle
#print axioms GaloisForLFunctions.CountingHolography.single_shell_rh_rate_iff_rh_and_moebius_circle
