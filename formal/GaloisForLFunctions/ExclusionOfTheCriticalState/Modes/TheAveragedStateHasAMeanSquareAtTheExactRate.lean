import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheAveragedStateIsTheSumOfItsZeroModes
import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalParseval
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount

/-!
# Mean squares of the averaged state at the exact rate

Let `Θ = sup Re ρ`, `κ = Θ - ½`, `Ā` the averaged state and `g(t) = e^{(8 - κ)t} Ā(t)`
(`ratedAveragedState`). The averaged state is its zero modes `m_z e^{(z - 8)t}` plus archimedean modes
`O(e^{-9t})`, with `Σ |m_z| < ∞`, and every centred zero has `Re z ≤ κ`. So
`g(t) = Σ_{Re z = κ} m_z e^{i(Im z)t} + o(1)`: the modes off the extremal line vanish by dominated
convergence (Tannery), the archimedean modes are `O(e^{-(1 + κ)t})`.

* **Mean square at the exact rate** (`criticalState_tendsto_meanSquare_ratedAveragedState`).
  `T⁻¹ ∫_0^T g² → Re Σ m_z conj m_{z'}` over the pairs of extremal copies with equal ordinates
  (`extremalModeMass`).
* **The attained dichotomy** (`extremalModeMass_pos_iff`, `extremalModeMass_eq_zero_of_not_attained`).
  The limit is positive iff `Θ` is attained and `0` otherwise. On the extremal line the coefficients
  do not vanish: `m_z = -a⁻¹ LF(z) A(z - 8)` and `LF(z) ≠ 0` on `Re z ≥ 0`. So "`Θ` is attained" is a
  property of the averaged state in mean square, at the endpoint rate.
-/

open MeasureTheory Set Filter Complex Topology

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- The extremal copies: the centred zeros on the line `Re z = Θ - ½`. -/
def extremalCopies : Set XiZeroCopy := {q | (centredZero q).re = zetaZeroAbscissa - 1 / 2}

/-- The averaged state at the rate of the zeros: `e^{(17/2 - Θ)t} Ā(t)`. -/
def ratedAveragedState (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((17 / 2 - zetaZeroAbscissa) * t) * averagedState F t

/-- The pair term `m_q conj m_{q'}` of two extremal copies with equal ordinates, `0` otherwise. -/
def extremalPairTerm (W₀ : ℝ) (F : ℝ → ℝ) (p : extremalCopies × extremalCopies) : ℂ :=
  if (centredZero p.1).im - (centredZero p.2).im = 0 then
    zeroModeCoeff W₀ F p.1 * (starRingEnd ℂ) (zeroModeCoeff W₀ F p.2) else 0

/-- The extremal mode mass `Re Σ m_q conj m_{q'}` over extremal pairs with equal ordinates. -/
def extremalModeMass (W₀ : ℝ) (F : ℝ → ℝ) : ℝ := (∑' p, extremalPairTerm W₀ F p).re

theorem re_centredZero_le_abscissa (q : XiZeroCopy) :
    (centredZero q).re ≤ zetaZeroAbscissa - 1 / 2 := by
  have h := re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)
  simp only [centredZero, Complex.sub_re]
  norm_num
  linarith

/-- Centred zeros are not real: `ξ` has no real zero. -/
theorem im_centredZero_ne_zero (q : XiZeroCopy) : (centredZero q).im ≠ 0 := by
  intro h
  have hq : (q.1 : ℂ) = (((q.1 : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [centredZero, Complex.sub_im] at h
      norm_num at h
      simp [h]
  exact xi_ne_zero_of_real _ (hq ▸ xi_xiZeroCopy_eq_zero q)

/-- An extremal mode is a pure oscillation: `(z - κ) t = i (Im z) t` on the extremal line. -/
theorem cexp_extremal {q : XiZeroCopy} (hq : q ∈ extremalCopies) (u : ℝ) :
    cexp ((centredZero q - (zetaZeroAbscissa - 1 / 2 : ℝ)) * u) =
      cexp (((centredZero q).im : ℂ) * I * u) := by
  congr 1
  have hq' : (centredZero q).re = zetaZeroAbscissa - 1 / 2 := hq
  have e : centredZero q - ((zetaZeroAbscissa - 1 / 2 : ℝ) : ℂ) = ((centredZero q).im : ℂ) * I := by
    apply Complex.ext <;> simp [hq']
  rw [e]

theorem continuous_ratedAveragedState {F : ℝ → ℝ} (hF : Integrable F) :
    Continuous (ratedAveragedState F) :=
  (by fun_prop : Continuous fun t : ℝ => Real.exp ((17 / 2 - zetaZeroAbscissa) * t)).mul
    (continuous_averagedState hF)

/-- **The mean square of the averaged state at the exact rate.**
`T⁻¹ ∫_0^T (e^{(17/2 - Θ)t} Ā(t))² dt → Re Σ m_q conj m_{q'}` over the pairs of extremal copies with
equal ordinates. -/
theorem criticalState_tendsto_meanSquare_ratedAveragedState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T, ratedAveragedState F u ^ 2) atTop
      (𝓝 (extremalModeMass W₀ F)) := by
  classical
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  set κ : ℝ := zetaZeroAbscissa - 1 / 2 with hκdef
  have hκ : 0 ≤ κ := by linarith [half_le_zetaZeroAbscissa]
  let m : XiZeroCopy → ℂ := zeroModeCoeff W₀ F
  have hm : Summable fun q => ‖m q‖ := criticalState_summable_norm_zeroModeCoeff hW ht hF
  set E : Set XiZeroCopy := extremalCopies with hEdef
  -- the full modes at the rate, split into the extremal line and the rest
  let P : XiZeroCopy → ℝ → ℂ := fun q u => m q * cexp ((centredZero q - (κ : ℂ)) * u)
  let Pin : XiZeroCopy → ℝ → ℂ := fun q u =>
    if q ∈ E then m q * cexp (((centredZero q).im : ℂ) * I * u) else 0
  let Pout : XiZeroCopy → ℝ → ℂ := fun q u => if q ∈ E then 0 else P q u
  have hPsplit : ∀ q u, P q u = Pin q u + Pout q u := fun q u => by
    by_cases hq : q ∈ E
    · simp only [P, Pin, Pout, if_pos hq, add_zero]
      rw [show ((κ : ℂ)) = ((zetaZeroAbscissa - 1 / 2 : ℝ) : ℂ) from rfl, cexp_extremal hq]
    · simp only [P, Pin, Pout, if_neg hq, zero_add]
  have hnormP : ∀ q (u : ℝ), 0 ≤ u → ‖P q u‖ ≤ ‖m q‖ := fun q u hu => by
    simp only [P, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [norm_cexp_mul_ofReal]
    refine Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ?_ hu)
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [re_centredZero_le_abscissa q]
  have hnormPin : ∀ q (u : ℝ), ‖Pin q u‖ ≤ ‖m q‖ := fun q u => by
    simp only [Pin]
    split_ifs
    · rw [norm_mul, show ((centredZero q).im : ℂ) * I * u = ((centredZero q).im * u : ℝ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
    · simp
  have hnormPout : ∀ q (u : ℝ), 0 ≤ u → ‖Pout q u‖ ≤ ‖m q‖ := fun q u hu => by
    simp only [Pout]
    split_ifs
    · simp
    · exact hnormP q u hu
  have sP : ∀ u : ℝ, 0 ≤ u → Summable fun q => P q u := fun u hu =>
    Summable.of_norm_bounded hm fun q => hnormP q u hu
  have sPin : ∀ u : ℝ, Summable fun q => Pin q u := fun u =>
    Summable.of_norm_bounded hm fun q => hnormPin q u
  have sPout : ∀ u : ℝ, 0 ≤ u → Summable fun q => Pout q u := fun u hu =>
    Summable.of_norm_bounded hm fun q => hnormPout q u hu
  -- the extremal almost-periodic sum
  let c : E → ℂ := fun q => -m q
  let μ : E → ℝ := fun q => (centredZero q).im
  have hmE : Summable fun q : E => ‖m q‖ := hm.subtype E
  have hc : Summable fun q : E => ‖c q‖ := by
    simpa only [c, norm_neg] using hmE
  have h0 : (∑' q : E, if μ q = 0 then c q else 0) = 0 := by
    refine (tsum_congr fun q => ?_).trans tsum_zero
    exact if_neg (im_centredZero_ne_zero q)
  have hS : ∀ u : ℝ, (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) = -∑' q, Pin q u := fun u => by
    rw [← tsum_neg, tsum_subtype E (fun q => -(m q * cexp (((centredZero q).im : ℂ) * I * u)))]
    refine tsum_congr fun q => ?_
    by_cases hq : q ∈ E
    · simp only [indicator_of_mem hq, Pin, if_pos hq]
    · simp only [indicator_of_notMem hq, Pin, if_neg hq, neg_zero]
  -- the rated state is the extremal sum plus a vanishing remainder
  have hsplit : ∀ u : ℝ, 0 < u →
      (ratedAveragedState F u : ℂ) + (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) - 0 =
        (∑' q, Pout q u) + ((Real.exp ((8 - κ) * u) : ℝ) : ℂ) * archimedeanModes W₀ F u := by
    intro u hu
    have hexp := criticalState_averagedState_eq_modes hW ht hF hu
    have hrate : (17 / 2 - zetaZeroAbscissa) = 8 - κ := by rw [hκdef]; ring
    have hmodes : ((Real.exp ((8 - κ) * u) : ℝ) : ℂ) * zeroModeSeries W₀ F u = ∑' q, P q u := by
      unfold zeroModeSeries
      rw [← tsum_mul_left]
      refine tsum_congr fun q => ?_
      simp only [P, m]
      rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [ratedAveragedState, hrate, Complex.ofReal_mul, hexp, mul_add, hmodes, hS,
      tsum_congr (hPsplit · u), (sPin u).tsum_add (sPout u hu.le)]
    ring
  -- the remainder tends to zero
  have hpt : ∀ q, Tendsto (fun u : ℝ => Pout q u) atTop (𝓝 0) := by
    intro q
    by_cases hq : q ∈ E
    · simp only [Pout, if_pos hq]
      exact tendsto_const_nhds
    · simp only [Pout, if_neg hq, P]
      have hlt : (centredZero q).re - κ < 0 := by
        have := re_centredZero_le_abscissa q
        have hne : (centredZero q).re ≠ κ := hq
        exact sub_neg.mpr (lt_of_le_of_ne this hne)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have he : Tendsto (fun u : ℝ => ‖m q‖ * Real.exp (((centredZero q).re - κ) * u)) atTop
          (𝓝 (‖m q‖ * 0)) :=
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hlt)).const_mul _
      rw [mul_zero] at he
      refine he.congr fun u => ?_
      rw [norm_mul, norm_cexp_mul_ofReal]
      simp only [Complex.sub_re, Complex.ofReal_re]
  have hR : Tendsto (fun u : ℝ => ∑' q, Pout q u) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun u q => Pout q u)
      (g := fun _ => (0 : ℂ)) hm hpt
      ((eventually_ge_atTop 0).mono fun u hu q => hnormPout q u hu)
    simpa using h
  have hA : Tendsto (fun u : ℝ => ((Real.exp ((8 - κ) * u) : ℝ) : ℂ) * archimedeanModes W₀ F u)
      atTop (𝓝 0) := by
    set K : ℝ := ‖stateMeromorphic W₀ F (-9)‖ + ‖stateMeromorphic W₀ F (-10)‖ +
      ‖stateMeromorphic W₀ F (-11)‖ + ‖stateMeromorphic W₀ F (-12)‖
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have he : Tendsto (fun u : ℝ => K * Real.exp (-(1 + κ) * u)) atTop (𝓝 (K * 0)) :=
      (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by linarith : -(1 + κ) < 0))).const_mul _
    rw [mul_zero] at he
    refine squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _)
      ((eventually_ge_atTop 0).mono fun u hu => ?_) he
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp ((8 - κ) * u) * ‖archimedeanModes W₀ F u‖
        ≤ Real.exp ((8 - κ) * u) * (K * Real.exp (-(9 * u))) :=
          mul_le_mul_of_nonneg_left (norm_archimedeanModes_le W₀ F hu) (Real.exp_pos _).le
      _ = K * Real.exp (-(1 + κ) * u) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hlim : Tendsto (fun u : ℝ => (ratedAveragedState F u : ℂ) +
      (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) - 0) atTop (𝓝 0) := by
    have h := hR.add hA
    rw [add_zero] at h
    exact h.congr' ((eventually_gt_atTop 0).mono fun u hu => (hsplit u hu).symm)
  have hmain := tendsto_meanSquare_of_tendsto_add_tsum (continuous_ratedAveragedState hd.integrable)
    c hc μ 0 hlim h0
  convert hmain using 2
  rw [norm_zero, sq, zero_mul, zero_add, extremalModeMass]
  congr 1
  refine tsum_congr fun p => ?_
  simp only [extremalPairTerm, c, μ, m, map_neg, neg_mul_neg]

/-- The coefficient of an extremal mode is not zero. -/
theorem zeroModeCoeff_ne_zero_of_re_nonneg {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {q : XiZeroCopy}
    (hq : 0 ≤ (centredZero q).re) : zeroModeCoeff W₀ F q ≠ 0 := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  have hL := criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW ht hF hq
  have hfac : ∀ n : ℝ, 0 < n → centredZero q + n ≠ 0 := fun n hn h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  have hA : averageSymbol (centredZero q - 8) ≠ 0 := by
    unfold averageSymbol
    refine inv_ne_zero ?_
    have e : (centredZero q - 8 + 9) * (centredZero q - 8 + 10) * (centredZero q - 8 + 11) *
        (centredZero q - 8 + 12) = (centredZero q + (1 : ℝ)) * (centredZero q + (2 : ℝ)) *
          (centredZero q + (3 : ℝ)) * (centredZero q + (4 : ℝ)) := by push_cast; ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hfac 1 one_pos) (hfac 2 two_pos))
      (hfac 3 three_pos)) (hfac 4 four_pos)
  unfold zeroModeCoeff
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero ha)) hL) hA

private theorem re_mul_conj_self (w : ℂ) : (w * (starRingEnd ℂ) w).re = ‖w‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The pair terms are nonnegative reals: equal ordinates on the extremal line mean equal zeros. -/
theorem extremalPairTerm_re_nonneg (W₀ : ℝ) (F : ℝ → ℝ) (p : extremalCopies × extremalCopies) :
    0 ≤ (extremalPairTerm W₀ F p).re := by
  unfold extremalPairTerm
  split_ifs with h
  · have h₁ : (centredZero (p.1 : XiZeroCopy)).re = zetaZeroAbscissa - 1 / 2 := p.1.2
    have h₂ : (centredZero (p.2 : XiZeroCopy)).re = zetaZeroAbscissa - 1 / 2 := p.2.2
    have hz : centredZero (p.1 : XiZeroCopy) = centredZero (p.2 : XiZeroCopy) :=
      Complex.ext (h₁.trans h₂.symm) (sub_eq_zero.mp h)
    have hc : zeroModeCoeff W₀ F p.1 = zeroModeCoeff W₀ F p.2 := by
      unfold zeroModeCoeff; rw [hz]
    rw [← hc, re_mul_conj_self]
    positivity
  · simp

theorem extremalPairTerm_diag (W₀ : ℝ) (F : ℝ → ℝ) (q : extremalCopies) :
    (extremalPairTerm W₀ F (q, q)).re = ‖zeroModeCoeff W₀ F q‖ ^ 2 := by
  unfold extremalPairTerm
  rw [if_pos (sub_self _), re_mul_conj_self]

theorem summable_extremalPairTerm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable (extremalPairTerm W₀ F) := by
  have hm : Summable fun q : extremalCopies => ‖zeroModeCoeff W₀ F q‖ :=
    (criticalState_summable_norm_zeroModeCoeff hW ht hF).subtype extremalCopies
  have hmc : Summable fun q : extremalCopies => ‖(starRingEnd ℂ) (zeroModeCoeff W₀ F q)‖ := by
    simpa only [Complex.norm_conj] using hm
  have hpair : Summable fun p : extremalCopies × extremalCopies =>
      ‖zeroModeCoeff W₀ F p.1‖ * ‖(starRingEnd ℂ) (zeroModeCoeff W₀ F p.2)‖ :=
    Summable.mul_norm (f := fun q : extremalCopies => zeroModeCoeff W₀ F q)
      (g := fun q : extremalCopies => (starRingEnd ℂ) (zeroModeCoeff W₀ F q)) hm hmc
  refine Summable.of_norm_bounded hpair fun p => ?_
  unfold extremalPairTerm
  split_ifs
  · rw [norm_mul]
  · rw [norm_zero]; positivity

/-- **The attained dichotomy.** The extremal mode mass is positive iff `Θ` is attained. -/
theorem extremalModeMass_pos_iff {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < extremalModeMass W₀ F ↔ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa := by
  have hs := summable_extremalPairTerm hW ht hF
  have hsre : Summable fun p => (extremalPairTerm W₀ F p).re := Complex.reCLM.summable hs
  constructor
  · intro hpos
    by_contra hno
    push Not at hno
    have hempty : IsEmpty extremalCopies := ⟨fun ⟨q, hq⟩ => hno _
      (riemannZeta_xiZeroCopy_eq_zero q) (by
        have hq' : (centredZero q).re = zetaZeroAbscissa - 1 / 2 := hq
        simp only [centredZero, Complex.sub_re] at hq'
        norm_num at hq'
        linarith)⟩
    rw [extremalModeMass, tsum_empty, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨ρ, hζ, hρ⟩
    have hρ0 : 0 < ρ.re := by linarith [half_le_zetaZeroAbscissa]
    have hρ1 : ρ ≠ 1 := fun h => riemannZeta_ne_zero_of_one_le_re (by rw [h]; norm_num) hζ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
      ((xi_eq_zero_iff_riemannZeta_of_re_pos hρ0 hρ1).mpr hζ)
    have hqE : q ∈ extremalCopies := by
      show (centredZero q).re = zetaZeroAbscissa - 1 / 2
      simp only [centredZero, Complex.sub_re, hq, hρ]
      norm_num
    have hq0 : 0 ≤ (centredZero q).re := by
      rw [show (centredZero q).re = zetaZeroAbscissa - 1 / 2 from hqE]
      linarith [half_le_zetaZeroAbscissa]
    have hne := zeroModeCoeff_ne_zero_of_re_nonneg hW ht hF hq0
    rw [extremalModeMass, Complex.re_tsum hs]
    have hdiag := extremalPairTerm_diag W₀ F ⟨q, hqE⟩
    have hle := hsre.le_tsum (⟨q, hqE⟩, ⟨q, hqE⟩) fun p _ => extremalPairTerm_re_nonneg W₀ F p
    rw [hdiag] at hle
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hne) 2) hle

/-- If `Θ` is not attained the averaged state is `o(e^{-(17/2 - Θ)t})` in mean square. -/
theorem extremalModeMass_eq_zero_of_not_attained {W₀ : ℝ} {F : ℝ → ℝ}
    (hno : ¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa) :
    extremalModeMass W₀ F = 0 := by
  have hempty : IsEmpty extremalCopies := ⟨fun ⟨q, hq⟩ => hno ⟨_,
    riemannZeta_xiZeroCopy_eq_zero q, by
      have hq' : (centredZero q).re = zetaZeroAbscissa - 1 / 2 := hq
      simp only [centredZero, Complex.sub_re] at hq'
      norm_num at hq'
      linarith⟩⟩
  rw [extremalModeMass, tsum_empty, Complex.zero_re]

/-- **"`Θ` is attained" in mean square.** The averaged state at the exact rate has a positive mean
square iff `Θ` is attained; otherwise its mean square tends to `0`. -/
theorem criticalState_meanSquare_attained_dichotomy {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ((∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa) →
      ∃ L : ℝ, 0 < L ∧ Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        ratedAveragedState F u ^ 2) atTop (𝓝 L)) ∧
    ((¬ ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = zetaZeroAbscissa) →
      Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T, ratedAveragedState F u ^ 2) atTop (𝓝 0)) :=
  ⟨fun h => ⟨_, (extremalModeMass_pos_iff hW ht hF).mpr h,
      criticalState_tendsto_meanSquare_ratedAveragedState hW ht hF⟩,
    fun h => extremalModeMass_eq_zero_of_not_attained h ▸
      criticalState_tendsto_meanSquare_ratedAveragedState hW ht hF⟩

#print axioms criticalState_tendsto_meanSquare_ratedAveragedState
#print axioms extremalModeMass_pos_iff
#print axioms criticalState_meanSquare_attained_dichotomy

end GaloisForLFunctions.ExclusionOfTheCriticalState
