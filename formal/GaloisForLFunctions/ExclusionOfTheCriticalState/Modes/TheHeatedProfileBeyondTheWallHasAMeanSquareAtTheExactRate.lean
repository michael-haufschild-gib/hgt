import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheAveragedStateHasAMeanSquareAtTheExactRate
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheHeatedProfileBeyondTheWallGrowsAtTheRateOfTheZeros
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionMoments
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# Mean squares of the heated profile beyond the wall at the exact rate

For heat time `ε > 0` the heated profile beyond the wall is its zero series plus the heated confined
state: `a(F⁺_ε(T) - (e^{-8u}F)_ε(T)) = Σ_z LF(z) e^{εz² - zT}`. The series is real (conjugation of
the zero copies, `LF(z̄) = conj LF(z)`) and every centred zero has `Re z ≥ -κ`, `κ = Θ - ½`
(reflection `ρ ↦ 1 - ρ`). Let `g(T) = e^{-κT} a(F⁺_ε(T) - (e^{-8u}F)_ε(T))`
(`ratedHeatedBeyondWall`). The modes on the mirror line `Re z = -κ` are pure oscillations, the
others vanish by dominated convergence.

* **Mean square at the exact rate** (`criticalState_tendsto_meanSquare_ratedHeatedBeyondWall`).
  `T⁻¹ ∫_0^T g² → Re Σ b_q conj b_{q'}` over pairs of mirror copies with equal ordinates,
  `b_q = LF(z_q) e^{εz_q²}` (`mirrorModeMass`).
* **The seen dichotomy** (`mirrorModeMass_pos_iff`). The limit is positive iff some zero on the mirror
  line is seen, `LF(z) ≠ 0`: beyond the wall the rate is attained in mean square exactly by the seen
  zeros on `Re z = -κ`.
-/

open MeasureTheory Set Filter Complex Topology

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- The mirror copies: centred zeros on the line `Re z = -(Θ - ½)`. -/
def mirrorExtremalCopies : Set XiZeroCopy :=
  {q | (centredZero q).re = -(zetaZeroAbscissa - 1 / 2)}

/-- The heated zero coefficient `b_q = LF(z_q) e^{εz_q²}`. -/
def heatedZeroCoeff (ε : ℝ) (F : ℝ → ℝ) (q : XiZeroCopy) : ℂ :=
  negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q)

/-- The heated profile beyond the wall at the rate of the zeros:
`e^{-(Θ - ½)T} a (F⁺_ε(T) - (e^{-8u}F)_ε(T))`. -/
def ratedHeatedBeyondWall (ε W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) :
    ℝ :=
  Real.exp (-(zetaZeroAbscissa - 1 / 2) * T) *
    ((criticalAliasCoefficient W₀ : ℂ) * (heatedBeyondWall ε W₀ hF T - (heatedState ε F T : ℂ))).re

/-- The pair term `b_q conj b_{q'}` of two mirror copies with equal ordinates, `0` otherwise. -/
def mirrorPairTerm (ε : ℝ) (F : ℝ → ℝ) (p : mirrorExtremalCopies × mirrorExtremalCopies) : ℂ :=
  if (centredZero p.1).im = (centredZero p.2).im then
    heatedZeroCoeff ε F p.1 * (starRingEnd ℂ) (heatedZeroCoeff ε F p.2) else 0

/-- The mirror mode mass `Re Σ b_q conj b_{q'}` over mirror pairs with equal ordinates. -/
def mirrorModeMass (ε : ℝ) (F : ℝ → ℝ) : ℝ := (∑' p, mirrorPairTerm ε F p).re

/-- Every centred zero has `Re z ≥ -(Θ - ½)`: `1 - ρ` is a zero with the same multiplicity. -/
theorem neg_abscissa_le_re_centredZero (q : XiZeroCopy) :
    -(zetaZeroAbscissa - 1 / 2) ≤ (centredZero q).re := by
  have h := re_centredZero_le_abscissa (xiZeroCopyReflectEquiv q)
  simp only [centredZero, Complex.sub_re, xiZeroCopy_reflect_val, Complex.one_re] at h ⊢
  norm_num at h ⊢
  linarith

theorem centredZero_conjEquiv (q : XiZeroCopy) :
    centredZero (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (centredZero q) := by
  simp only [centredZero, xiZeroCopyConjEquiv_coe, map_sub, map_div₀, map_one, map_ofNat]

theorem laplace_cx_conj (F : ℝ → ℝ) (z : ℂ) :
    negativeHalfLineLaplace (cx F) ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (negativeHalfLineLaplace (cx F) z) :=
  negativeHalfLineLaplace_real_conj F z

theorem stateHeatSymbol_conj (ε T : ℝ) (z : ℂ) :
    stateHeatSymbol ε T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (stateHeatSymbol ε T z) := by
  unfold stateHeatSymbol
  rw [← Complex.exp_conj]
  congr 1
  simp [map_sub, map_mul, Complex.conj_ofReal, map_pow]

theorem stateHeatSymbol_eq (ε T : ℝ) (z : ℂ) :
    stateHeatSymbol ε T z = stateHeatSymbol ε 0 z * cexp (-z * T) := by
  unfold stateHeatSymbol
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The heated zero series is real.** -/
theorem heatedZeroSeries_im (F : ℝ → ℝ) (ε T : ℝ) :
    (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
      stateHeatSymbol ε T (centredZero q)).im = 0 := by
  set f : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q) with hf
  have hconj : ∀ q, f (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (f q) := fun q => by
    simp only [hf, centredZero_conjEquiv, laplace_cx_conj, stateHeatSymbol_conj, map_mul]
  have h : (∑' q, f q) = (starRingEnd ℂ) (∑' q, f q) := by
    rw [Complex.conj_tsum, ← xiZeroCopyConjEquiv.tsum_eq f]
    exact tsum_congr fun q => hconj q
  exact Complex.conj_eq_iff_im.mp h.symm

theorem criticalState_continuous_heatedZeroSeries {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun T : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
      stateHeatSymbol ε T (centredZero q) := by
  have hb := criticalState_summable_norm_heatedZeroModes hW ht hF hε 0
  rw [continuous_iff_continuousAt]
  intro T₀
  have hcont : ContinuousOn (fun T : ℝ => ∑' q : XiZeroCopy,
      negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))
      (Ioo (T₀ - 1) (T₀ + 1)) := by
    refine continuousOn_tsum (fun q => ?_) (hb.mul_right (Real.exp ((|T₀| + 1) / 2)))
      (fun q T hT => ?_)
    · exact (by unfold stateHeatSymbol; fun_prop : Continuous fun T : ℝ =>
        negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q)).continuousOn
    · rw [stateHeatSymbol_eq, ← mul_assoc, norm_mul, norm_cexp_mul_ofReal]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have hx := abs_lt.mp (abs_re_centredZero_lt q)
      have hT' : |T| ≤ |T₀| + 1 := by
        have := abs_sub_abs_le_abs_sub T T₀
        have h1 : |T - T₀| < 1 := abs_sub_lt_iff.mpr ⟨by linarith [hT.2], by linarith [hT.1]⟩
        linarith
      have h2 : |(centredZero q).re * T| ≤ 1 / 2 * |T| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_re_centredZero_lt q).le (abs_nonneg _)
      simp only [Complex.neg_re]
      nlinarith [neg_abs_le ((centredZero q).re * T), le_abs_self ((centredZero q).re * T)]
  exact hcont.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- The rated heated profile is `e^{-κT}` times the zero series. -/
theorem criticalState_ratedHeatedBeyondWall_eq {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    (ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T : ℂ) =
      ((Real.exp (-(zetaZeroAbscissa - 1 / 2) * T) : ℝ) : ℂ) *
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q) := by
  have hs := (criticalState_hasSum_heated_zeroSeries hW ht hF hε T).tsum_eq
  have him := heatedZeroSeries_im F ε T
  rw [ratedHeatedBeyondWall, ← hs, Complex.ofReal_mul]
  congr 1
  exact Complex.ext (by simp) (by simp [him])

theorem continuous_ratedHeatedBeyondWall {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    Continuous (ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF)) := by
  have h : ∀ T, ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T =
      Real.exp (-(zetaZeroAbscissa - 1 / 2) * T) *
        (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q)).re := fun T => by
    have e := congrArg Complex.re (criticalState_ratedHeatedBeyondWall_eq hW ht hF hε T)
    rwa [Complex.ofReal_re, Complex.re_ofReal_mul] at e
  rw [show ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) = _ from
    funext h]
  exact (by fun_prop : Continuous fun T : ℝ => Real.exp (-(zetaZeroAbscissa - 1 / 2) * T)).mul
    (Complex.continuous_re.comp (criticalState_continuous_heatedZeroSeries hW ht hF hε))

/-- **The mean square of the heated profile beyond the wall at the exact rate.**
`T⁻¹ ∫_0^T (e^{-κT} a(F⁺_ε - (e^{-8u}F)_ε))² → Re Σ b_q conj b_{q'}` over the pairs of mirror
copies with equal ordinates. -/
theorem criticalState_tendsto_meanSquare_ratedHeatedBeyondWall {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
      ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) u ^ 2) atTop
      (𝓝 (mirrorModeMass ε F)) := by
  classical
  set κ : ℝ := zetaZeroAbscissa - 1 / 2 with hκdef
  let b : XiZeroCopy → ℂ := heatedZeroCoeff ε F
  have hb : Summable fun q => ‖b q‖ := criticalState_summable_norm_heatedZeroModes hW ht hF hε 0
  set E : Set XiZeroCopy := mirrorExtremalCopies with hEdef
  let P : XiZeroCopy → ℝ → ℂ := fun q u => b q * cexp (-(centredZero q + (κ : ℂ)) * u)
  let Pin : XiZeroCopy → ℝ → ℂ := fun q u =>
    if q ∈ E then b q * cexp (((-(centredZero q).im : ℝ) : ℂ) * I * u) else 0
  let Pout : XiZeroCopy → ℝ → ℂ := fun q u => if q ∈ E then 0 else P q u
  have hPsplit : ∀ q u, P q u = Pin q u + Pout q u := fun q u => by
    by_cases hq : q ∈ E
    · simp only [P, Pin, Pout, if_pos hq, add_zero]
      congr 2
      have hq' : (centredZero q).re = -κ := hq
      apply Complex.ext <;> simp [hq']
    · simp only [P, Pin, Pout, if_neg hq, zero_add]
  have hnormP : ∀ q (u : ℝ), 0 ≤ u → ‖P q u‖ ≤ ‖b q‖ := fun q u hu => by
    simp only [P, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [norm_cexp_mul_ofReal]
    refine Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ?_ hu)
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith [neg_abscissa_le_re_centredZero q]
  have hnormPin : ∀ q (u : ℝ), ‖Pin q u‖ ≤ ‖b q‖ := fun q u => by
    simp only [Pin]
    split_ifs
    · rw [norm_mul, show ((-(centredZero q).im : ℝ) : ℂ) * I * u =
          ((-(centredZero q).im) * u : ℝ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    · simp
  have hnormPout : ∀ q (u : ℝ), 0 ≤ u → ‖Pout q u‖ ≤ ‖b q‖ := fun q u hu => by
    simp only [Pout]
    split_ifs
    · simp
    · exact hnormP q u hu
  have sPin : ∀ u : ℝ, Summable fun q => Pin q u := fun u =>
    Summable.of_norm_bounded hb fun q => hnormPin q u
  have sPout : ∀ u : ℝ, 0 ≤ u → Summable fun q => Pout q u := fun u hu =>
    Summable.of_norm_bounded hb fun q => hnormPout q u hu
  let c : E → ℂ := fun q => -b q
  let μ : E → ℝ := fun q => -(centredZero q).im
  have hbE : Summable fun q : E => ‖b q‖ := hb.subtype E
  have hc : Summable fun q : E => ‖c q‖ := by
    simpa only [c, norm_neg] using hbE
  have h0 : (∑' q : E, if μ q = 0 then c q else 0) = 0 := by
    refine (tsum_congr fun q => ?_).trans tsum_zero
    exact if_neg (neg_ne_zero.mpr (im_centredZero_ne_zero q))
  have hS : ∀ u : ℝ, (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) = -∑' q, Pin q u := fun u => by
    calc (∑' q : E, c q * cexp ((μ q : ℂ) * I * u))
        = ∑' q : XiZeroCopy, E.indicator
            (fun q => -(b q * cexp (((-(centredZero q).im : ℝ) : ℂ) * I * u))) q := by
          rw [← tsum_subtype]
          exact tsum_congr fun q => by simp only [c, μ, neg_mul]
      _ = -∑' q, Pin q u := by
          rw [← tsum_neg]
          refine tsum_congr fun q => ?_
          by_cases hq : q ∈ E
          · simp only [indicator_of_mem hq, Pin, if_pos hq]
          · simp only [indicator_of_notMem hq, Pin, if_neg hq, neg_zero]
  have hsplit : ∀ u : ℝ, 0 ≤ u →
      (ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) u : ℂ) +
        (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) - 0 = ∑' q, Pout q u := by
    intro u hu
    rw [criticalState_ratedHeatedBeyondWall_eq hW ht hF hε u, ← tsum_mul_left]
    have hmodes : ∀ q, ((Real.exp (-(zetaZeroAbscissa - 1 / 2) * u) : ℝ) : ℂ) *
        (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε u (centredZero q)) =
          P q u := fun q => by
      simp only [P, b, heatedZeroCoeff]
      rw [stateHeatSymbol_eq, Complex.ofReal_exp]
      calc cexp (((-(zetaZeroAbscissa - 1 / 2) * u : ℝ) : ℂ)) *
            (negativeHalfLineLaplace (cx F) (centredZero q) *
              (stateHeatSymbol ε 0 (centredZero q) * cexp (-centredZero q * u)))
          = negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q) *
              (cexp (((-(zetaZeroAbscissa - 1 / 2) * u : ℝ) : ℂ)) * cexp (-centredZero q * u)) := by
            ring
        _ = _ := by
            rw [← Complex.exp_add, hκdef]
            congr 2
            push_cast
            ring
    rw [tsum_congr hmodes, hS, tsum_congr (hPsplit · u), (sPin u).tsum_add (sPout u hu)]
    ring
  have hpt : ∀ q, Tendsto (fun u : ℝ => Pout q u) atTop (𝓝 0) := by
    intro q
    by_cases hq : q ∈ E
    · simp only [Pout, if_pos hq]
      exact tendsto_const_nhds
    · simp only [Pout, if_neg hq, P]
      have hlt : -((centredZero q).re + κ) < 0 := by
        have := neg_abscissa_le_re_centredZero q
        have hne : (centredZero q).re ≠ -κ := hq
        have : -κ < (centredZero q).re := lt_of_le_of_ne this (Ne.symm hne)
        linarith
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have he : Tendsto (fun u : ℝ => ‖b q‖ * Real.exp (-((centredZero q).re + κ) * u)) atTop
          (𝓝 (‖b q‖ * 0)) :=
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hlt)).const_mul _
      rw [mul_zero] at he
      refine he.congr fun u => ?_
      rw [norm_mul, norm_cexp_mul_ofReal]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
  have hR : Tendsto (fun u : ℝ => ∑' q, Pout q u) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun u q => Pout q u)
      (g := fun _ => (0 : ℂ)) hb hpt
      ((eventually_ge_atTop 0).mono fun u hu q => hnormPout q u hu)
    simpa using h
  have hlim : Tendsto (fun u : ℝ =>
      (ratedHeatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) u : ℂ) +
        (∑' q : E, c q * cexp ((μ q : ℂ) * I * u)) - 0) atTop (𝓝 0) :=
    hR.congr' ((eventually_ge_atTop 0).mono fun u hu => (hsplit u hu).symm)
  have hmain := tendsto_meanSquare_of_tendsto_add_tsum
    (continuous_ratedHeatedBeyondWall hW ht hF hε) c hc μ 0 hlim h0
  convert hmain using 2
  rw [norm_zero, sq, zero_mul, zero_add, mirrorModeMass]
  congr 1
  refine tsum_congr fun p => ?_
  simp only [mirrorPairTerm, c, μ, b, map_neg, neg_mul_neg, sub_eq_zero, neg_inj]

private theorem re_mul_conj_self' (w : ℂ) : (w * (starRingEnd ℂ) w).re = ‖w‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem mirrorPairTerm_eq (ε : ℝ) (F : ℝ → ℝ) (p : mirrorExtremalCopies × mirrorExtremalCopies) :
    mirrorPairTerm ε F p = if (centredZero p.1).im = (centredZero p.2).im then
      ((‖heatedZeroCoeff ε F p.1‖ ^ 2 : ℝ) : ℂ) else 0 := by
  unfold mirrorPairTerm
  split_ifs with h
  · have h₁ : (centredZero (p.1 : XiZeroCopy)).re = -(zetaZeroAbscissa - 1 / 2) := p.1.2
    have h₂ : (centredZero (p.2 : XiZeroCopy)).re = -(zetaZeroAbscissa - 1 / 2) := p.2.2
    have hz : centredZero (p.1 : XiZeroCopy) = centredZero (p.2 : XiZeroCopy) :=
      Complex.ext (h₁.trans h₂.symm) h
    have hc : heatedZeroCoeff ε F p.1 = heatedZeroCoeff ε F p.2 := by
      unfold heatedZeroCoeff; rw [hz]
    rw [← hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · rfl

theorem summable_mirrorPairTerm {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    Summable (mirrorPairTerm ε F) := by
  have hm : Summable fun q : mirrorExtremalCopies => ‖heatedZeroCoeff ε F q‖ :=
    (criticalState_summable_norm_heatedZeroModes hW ht hF hε 0).subtype mirrorExtremalCopies
  have hmc : Summable fun q : mirrorExtremalCopies =>
      ‖(starRingEnd ℂ) (heatedZeroCoeff ε F q)‖ := by
    simpa only [Complex.norm_conj] using hm
  have hpair : Summable fun p : mirrorExtremalCopies × mirrorExtremalCopies =>
      ‖heatedZeroCoeff ε F p.1 * (starRingEnd ℂ) (heatedZeroCoeff ε F p.2)‖ :=
    Summable.mul_norm (f := fun q : mirrorExtremalCopies => heatedZeroCoeff ε F q)
      (g := fun q : mirrorExtremalCopies => (starRingEnd ℂ) (heatedZeroCoeff ε F q)) hm hmc
  refine Summable.of_norm_bounded hpair fun p => ?_
  unfold mirrorPairTerm
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; positivity

/-- **The seen dichotomy beyond the wall.** The mirror mode mass is positive iff some zero on the
mirror line `Re z = -(Θ - ½)` is seen by the state. -/
theorem mirrorModeMass_pos_iff {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    0 < mirrorModeMass ε F ↔ ∃ q : XiZeroCopy,
      (centredZero q).re = -(zetaZeroAbscissa - 1 / 2) ∧
        negativeHalfLineLaplace (cx F) (centredZero q) ≠ 0 := by
  have hs := summable_mirrorPairTerm hW ht hF hε
  have hsre : Summable fun p => (mirrorPairTerm ε F p).re := Complex.reCLM.summable hs
  have hre : ∀ p, (mirrorPairTerm ε F p).re = if (centredZero p.1).im = (centredZero p.2).im then
      ‖heatedZeroCoeff ε F p.1‖ ^ 2 else 0 := fun p => by
    rw [mirrorPairTerm_eq]
    split_ifs
    · exact Complex.ofReal_re _
    · exact Complex.zero_re
  have hb : ∀ q, heatedZeroCoeff ε F q = 0 ↔ negativeHalfLineLaplace (cx F) (centredZero q) = 0 :=
    fun q => by
      unfold heatedZeroCoeff stateHeatSymbol
      exact ⟨fun h => (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _),
        fun h => by rw [h, zero_mul]⟩
  constructor
  · intro hpos
    by_contra hno
    push Not at hno
    have hzero : ∀ p, (mirrorPairTerm ε F p).re = 0 := fun p => by
      rw [hre]
      split_ifs
      · rw [(hb p.1).mpr (hno p.1 p.1.2), norm_zero]; ring
      · rfl
    rw [mirrorModeMass, Complex.re_tsum hs, tsum_congr hzero, tsum_zero] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨q, hq, hseen⟩
    have hne : heatedZeroCoeff ε F q ≠ 0 := fun h => hseen ((hb q).mp h)
    rw [mirrorModeMass, Complex.re_tsum hs]
    have hdiag : (mirrorPairTerm ε F (⟨q, hq⟩, ⟨q, hq⟩)).re = ‖heatedZeroCoeff ε F q‖ ^ 2 := by
      rw [hre, if_pos rfl]
    have hle := hsre.le_tsum (⟨q, hq⟩, ⟨q, hq⟩) fun p _ => by
      rw [hre]; split_ifs <;> positivity
    rw [hdiag] at hle
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hne) 2) hle

#print axioms criticalState_tendsto_meanSquare_ratedHeatedBeyondWall
#print axioms mirrorModeMass_pos_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState
