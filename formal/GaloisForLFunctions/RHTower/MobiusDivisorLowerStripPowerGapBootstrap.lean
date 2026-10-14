import GaloisForLFunctions.RHTower.MobiusDivisorOneSidedPowerGapBootstrap

/-!
# The `W ≡ -1` Threshold Pole Contradiction, One-Sided Lower Strip Laws, and Power-Gap Lower Bootstrap for the Möbius Divisor Abel Moment

`WeightedScrewPoleContradictionThreshold` (`abs_im_le_of_thr`) was proved for an arbitrary bounded,
even, nonvanishing weight `W : XiZeroCopy → ℂ` (`‖W q‖ ≤ C`, `(xiSpectralPoint q).im ≠ 0 → W q ≠ 0`),
requiring **no** sign condition on `W(q)` at the pole residue. However,
`SuzukiScrewSubexponentialCriterion` only instantiated `abs_im_le_of_thr` with `W ≡ +1`, which routed
one-sided **lower** bounds on `suzukiPsi` into **upper** bounds on `unitRieszSuzukiGreen`,
`criticalMellinChebyshevResolventSource`, and `mobiusDivisorSquareRootAbelMoment`.

This module develops the complete `W ≡ -1` mirror across the entire Suzuki–Green–Resolvent–Möbius-Divisor
chain, together with both a **bootstrap-free** `O(√n)`-gap lower transport and the arbitrary power-gap
lower bootstrap:

1. **The `W ≡ -1` threshold pole contradiction (`Section 1`):**
   Instantiating `abs_im_le_of_thr` with `W := fun _ => (-1 : ℂ)`
   (`weightedXiScrewDivisor (fun _ => (-1 : ℂ)) t = -xiScrewDivisor t`) proves that a one-sided
   exponential **upper** bound `suzukiPsi t ≤ C₀ exp(ε t)` (`ε ≥ 0`) confines every Xi zero copy to
   `|(xiSpectralPoint q).im| ≤ ε` (`abs_im_xiSpectralPoint_le_of_suzukiPsi_le'`). Consequently,
   `RiemannHypothesis` is equivalent to `SuzukiPsiSubexponentialAbove`
   (`riemannHypothesis_iff_suzukiPsiSubexponentialAbove`) and to subexponential lower control of
   `screwPrimeSum` (`riemannHypothesis_iff_screwPrimeSum_subexponential_lower`).

2. **One-sided lower exponential and power strip laws (`Section 2`):**
   Routing through `UnitRieszGreenInverse.le_quadratic_of_greenFilter_le`
   (`suzukiPsi_quadratic_upper_of_le_unitRieszSuzukiGreen`), the real-aperture Green identity, and the
   integer-logarithm cell comparison proves one-sided **lower** strip laws and RH equivalences for:
   - `unitRieszSuzukiGreen` (`abs_re_sub_half_le_of_neg_exp_le_unitRieszSuzukiGreen`,
     `riemannHypothesis_iff_unitRieszSuzukiGreen_boundedBelow`),
   - `criticalMellinChebyshevResolventSource` (`abs_re_sub_half_le_of_neg_exp_le_criticalResolvent`,
     `riemannHypothesis_iff_criticalResolvent_boundedBelow`,
     `abs_re_sub_half_le_of_neg_rpow_le_criticalResolvent_log_nat`,
     `riemannHypothesis_iff_criticalResolvent_logNat_boundedBelow`), and
   - `mobiusDivisorSquareRootAbelMoment` (`mobiusDivisorSquareRootAbel_le_resolvent_log_nat`,
     `abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel`,
     `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow`,
     `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_oneSided_subpower_lower`).

3. **Unconditional `O(√n)`-gap lower transport and arbitrary power-gap lower bootstrap (`Section 3`):**
   - Because `mobiusDivisorSquareRootAbel_sub_ge_neg_mul` holds unconditionally from `ψ(k) ≥ 0` and
     `γ ≥ 0`, dividing by `n` yields the **unconditional** pointwise lower transport
     `min (mobiusDivisorSquareRootAbelMoment k / k) 0 − (n − k) / √n ≤ mobiusDivisorSquareRootAbelMoment n / n`
     (`mobiusDivisorSquareRootAbel_div_ge_of_unconditional_sample`), which gives a **bootstrap-free**
     1-step lower strip law for any sampling set with `O(√n)` gaps
     (`abs_re_sub_half_le_of_sqrtGaps_neg_rpow_le_mobiusDivisorSquareRootAbel`).
   - For arbitrary power-saving gaps `n − k ≤ K n^{1−δ}` (`δ > 0`), our two-step supremum fixed-point
     bootstrap (`α = zeroReSup - 1/2`) proves the full zero-free strip
     (`abs_re_sub_half_le_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel`) and RH equivalences
     for arbitrary power-gap sets, `m`-th power meshes (`m ≥ 1`), and adaptive power windows
     (`riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddBelow_of_powerGaps`,
     `riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow`,
     `riemannHypothesis_iff_exists_powerWindow_le_mobiusDivisorSquareRootAbel`).
-/

open Complex Real Set MeasureTheory Filter Topology
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: The `W ≡ -1` threshold Widder–Landau pole contradiction and one-sided upper
subexponential criterion for Suzuki's screw function -/

/-- The constant weight `-1` negates the unweighted Xi screw divisor. -/
theorem weightedXiScrewDivisor_neg_one (t : ℝ) :
    weightedXiScrewDivisor (fun _ => (-1 : ℂ)) t = -xiScrewDivisor t := by
  simp [weightedXiScrewDivisor, xiScrewDivisor, tsum_neg]

/-- **Upper strip law for Suzuki's screw function (`W ≡ -1` mirror).**
A one-sided exponential upper bound `suzukiPsi t ≤ C₀ exp(ε t)` of rate `0 ≤ ε < 1/2` over the
source half-line confines every Xi zero copy to `|Im z_q| ≤ ε`. -/
theorem abs_im_xiSpectralPoint_le_of_suzukiPsi_le {C₀ ε : ℝ}
    (hup : ∀ t : ℝ, 0 ≤ t → suzukiPsi t ≤ C₀ * Real.exp (ε * t))
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  refine abs_im_le_of_thr (fun _ => (-1 : ℂ)) C₀ ε (C := 1) zero_le_one
    (fun _ => by simp) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => neg_ne_zero.mpr one_ne_zero) ?_ ?_ hε0 hε q
  · intro t ht
    rw [weightedXiScrewDivisor_neg_one, Complex.neg_re, ← suzukiPsi_eq_xiScrewDivisor_re ht]
    linarith [hup t ht]
  · intro t
    rw [weightedXiScrewDivisor_neg_one, Complex.neg_im, xiScrewDivisor_im_eq_zero, neg_zero]

/-- The upper strip law for `suzukiPsi` at every rate `ε ≥ 0`, using the unconditional bound
`|Im z_q| < 1/2`. -/
theorem abs_im_xiSpectralPoint_le_of_suzukiPsi_le' {C₀ ε : ℝ}
    (hup : ∀ t : ℝ, 0 ≤ t → suzukiPsi t ≤ C₀ * Real.exp (ε * t))
    (hε0 : 0 ≤ ε) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  rcases le_or_gt (1 / 2 : ℝ) ε with hε | hε
  · exact (abs_xiSpectralPoint_im_lt_half q).le.trans hε
  · exact abs_im_xiSpectralPoint_le_of_suzukiPsi_le hup hε0 hε q

/-- Suzuki's screw function is not exponentially positive at any positive rate. -/
def SuzukiPsiSubexponentialAbove : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, ∀ t : ℝ, 0 ≤ t → suzukiPsi t ≤ C₀ * Real.exp (ε * t)

/-- **Sub-exponential positivity of Suzuki's screw function implies RH.** -/
theorem riemannHypothesis_of_suzukiPsiSubexponentialAbove
    (h : SuzukiPsiSubexponentialAbove) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have him : (xiSpectralPoint q).im = 0 := by
    have hle : |(xiSpectralPoint q).im| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨C₀, hB⟩ := h ε hε
      have := abs_im_xiSpectralPoint_le_of_suzukiPsi_le' hB hε.le q
      linarith
    exact abs_nonpos_iff.mp hle
  exact ⟨(xiSpectralPoint q).re, by apply Complex.ext <;> simp [him]⟩

/-- Under RH the screw function is bounded (`riemannHypothesis_iff_suzukiExplicitScrewBounded`),
hence sub-exponential above. -/
theorem suzukiPsiSubexponentialAbove_of_riemannHypothesis (hRH : RiemannHypothesis) :
    SuzukiPsiSubexponentialAbove := by
  obtain ⟨C, hC⟩ := riemannHypothesis_iff_suzukiExplicitScrewBounded.mp hRH
  have hC0 : 0 ≤ C := (abs_nonneg (suzukiPsi 0)).trans (hC 0 le_rfl)
  intro ε hε
  refine ⟨C, fun t ht => ?_⟩
  have hexp : 1 ≤ Real.exp (ε * t) := Real.one_le_exp (mul_nonneg hε.le ht)
  have hle : suzukiPsi t ≤ C := (le_abs_self _).trans (hC t ht)
  nlinarith

/-- **RH is equivalent to sub-exponential positivity of Suzuki's screw function.** -/
theorem riemannHypothesis_iff_suzukiPsiSubexponentialAbove :
    RiemannHypothesis ↔ SuzukiPsiSubexponentialAbove :=
  ⟨suzukiPsiSubexponentialAbove_of_riemannHypothesis,
    riemannHypothesis_of_suzukiPsiSubexponentialAbove⟩

/-- **Prime-side lower strip law.** If the prime hinge sum falls short of its explicit smooth part
by at most `C₀ exp(ε t)` on the source half-line, every Xi zero copy satisfies `|Im z_q| ≤ ε`. -/
theorem abs_im_xiSpectralPoint_le_of_le_screwPrimeSum {C₀ ε : ℝ}
    (hle : ∀ t : ℝ, 0 ≤ t →
      ccmGuinandWeilXiScrewSmoothPart t - C₀ * Real.exp (ε * t) ≤
        GaloisForLFunctions.RHTower.screwPrimeSum t)
    (hε0 : 0 ≤ ε) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  refine abs_im_xiSpectralPoint_le_of_suzukiPsi_le' (C₀ := C₀) (ε := ε) ?_ hε0 q
  intro t ht
  rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht]
  linarith [hle t ht]

/-- **RH from one-sided sub-exponential lower control of the prime hinge sum.** -/
theorem riemannHypothesis_iff_screwPrimeSum_subexponential_lower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, ∀ t : ℝ, 0 ≤ t →
      ccmGuinandWeilXiScrewSmoothPart t - C₀ * Real.exp (ε * t) ≤
        GaloisForLFunctions.RHTower.screwPrimeSum t := by
  rw [riemannHypothesis_iff_suzukiPsiSubexponentialAbove]
  constructor
  · intro h ε hε
    obtain ⟨C₀, hB⟩ := h ε hε
    refine ⟨C₀, fun t ht => ?_⟩
    have := hB t ht
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht] at this
    linarith
  · intro h ε hε
    obtain ⟨C₀, hB⟩ := h ε hε
    refine ⟨C₀, fun t ht => ?_⟩
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht]
    linarith [hB t ht]

/-! ## Section 2: One-sided lower exponential and power strip laws for `unitRieszSuzukiGreen`,
`criticalMellinChebyshevResolventSource`, and `mobiusDivisorSquareRootAbelMoment` -/

open UnitRieszGreenInverse UnitRieszOneSided

/-- **Quadratic upper bound on `suzukiPsi` from a lower bound on `unitRieszSuzukiGreen`.**
Localizes the positive Green inverse (`le_quadratic_of_greenFilter_le`) to the compact interval
`[unitRieszSuzukiBase, t]`. -/
theorem suzukiPsi_quadratic_upper_of_le_unitRieszSuzukiGreen
    {B t : ℝ} (ht : unitRieszSuzukiBase ≤ t)
    (hB : ∀ u ∈ Icc unitRieszSuzukiBase t, -B ≤ unitRieszSuzukiGreen u) :
    suzukiPsi t ≤ 2 * (B + unitRieszSuzukiGreenBoundaryBound) *
      (1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
        (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2) := by
  refine le_quadratic_of_greenFilter_le continuous_suzukiPsi ht
    (B := 2 * (B + unitRieszSuzukiGreenBoundaryBound)) ?_
  intro u hu
  rw [greenFilter_suzukiPsi_eq hu.1]
  have hb := (abs_le.mp (abs_unitRieszSuzukiGreenBoundary_le hu.1)).2
  linarith [hB u hu]

/-- **One-sided lower exponential strip law for `unitRieszSuzukiGreen`.**
If `-(B e^{α t}) ≤ unitRieszSuzukiGreen t` for `t ≥ unitRieszSuzukiBase` (`B ≥ 0`, `α ≥ 0`), then
every `q : XiZeroCopy` satisfies `|(q.1 : ℂ).re - 1/2| ≤ α`. -/
theorem abs_re_sub_half_le_of_neg_exp_le_unitRieszSuzukiGreen {B α : ℝ} (hB0 : 0 ≤ B)
    (hα0 : 0 ≤ α)
    (hG : ∀ t : ℝ, unitRieszSuzukiBase ≤ t → -(B * Real.exp (α * t)) ≤ unitRieszSuzukiGreen t)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  have him : |(xiSpectralPoint q).im| ≤ α := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_suzukiPsi.continuousOn (s := Icc (0 : ℝ) unitRieszSuzukiBase))
    set A : ℝ := 2 * (B + unitRieszSuzukiGreenBoundaryBound) with hAdef
    have hA0 : 0 ≤ A := by
      rw [hAdef, unitRieszSuzukiGreenBoundaryBound]
      positivity
    set Q : ℝ := (η + 2) ^ 2 / η ^ 2 with hQdef
    have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
    set C₀ : ℝ := (2 * A + |M|) * Q with hC₀
    refine abs_im_xiSpectralPoint_le_of_suzukiPsi_le' (C₀ := C₀) (ε := α + η) ?_ (by linarith) q
    intro t ht
    have hquad : (1 + t) ^ 2 ≤ Q * Real.exp (η * t) :=
      UnitRieszGreenInverse.quadratic_le_exponential hη ht
    have hexpα : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht)
    have hsq1 : 1 ≤ (1 + t) ^ 2 := by nlinarith [sq_nonneg t]
    have hQexp : (1 + t) ^ 2 * Real.exp (α * t) ≤ Q * Real.exp ((α + η) * t) := by
      calc (1 + t) ^ 2 * Real.exp (α * t)
          ≤ (Q * Real.exp (η * t)) * Real.exp (α * t) :=
            mul_le_mul_of_nonneg_right hquad (Real.exp_pos _).le
        _ = Q * Real.exp ((α + η) * t) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    by_cases hbt : unitRieszSuzukiBase ≤ t
    · have hu_bound : ∀ u ∈ Icc unitRieszSuzukiBase t,
          -(B * Real.exp (α * t)) ≤ unitRieszSuzukiGreen u := by
        intro u hu
        have hexpu : B * Real.exp (α * u) ≤ B * Real.exp (α * t) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hα0)) hB0
        exact (neg_le_neg hexpu).trans (hG u hu.1)
      have hup := suzukiPsi_quadratic_upper_of_le_unitRieszSuzukiGreen hbt hu_bound
      have hd : 0 ≤ t - unitRieszSuzukiBase := sub_nonneg.mpr hbt
      have hdt : t - unitRieszSuzukiBase ≤ t := by linarith [unitRieszSuzukiBase_pos]
      have hp : 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
          (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 ≤ 2 * (1 + t) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hdt) (add_nonneg ht hd)]
      have hBbound : B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound ≤
          (B + unitRieszSuzukiGreenBoundaryBound) * Real.exp (α * t) := by
        have : 0 ≤ unitRieszSuzukiGreenBoundaryBound := by
          unfold unitRieszSuzukiGreenBoundaryBound; positivity
        nlinarith
      have h1 : 2 * (B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound) *
          (1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
            (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2) ≤
          2 * A * ((1 + t) ^ 2 * Real.exp (α * t)) := by
        have hp0 : 0 ≤ 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
            (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 := by positivity
        have hstep1 : 2 * (B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound) ≤
            A * Real.exp (α * t) := by rw [hAdef]; linarith
        have hstep2 := mul_le_mul hstep1 hp hp0 (mul_nonneg hA0 (Real.exp_pos _).le)
        linarith
      have h2 : 2 * A * ((1 + t) ^ 2 * Real.exp (α * t)) ≤
          C₀ * Real.exp ((α + η) * t) := by
        rw [hC₀]
        calc 2 * A * ((1 + t) ^ 2 * Real.exp (α * t))
            ≤ (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) :=
              mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M]) (by positivity)
          _ ≤ (2 * A + |M|) * (Q * Real.exp ((α + η) * t)) :=
              mul_le_mul_of_nonneg_left hQexp (by positivity)
          _ = (2 * A + |M|) * Q * Real.exp ((α + η) * t) := by ring
      exact hup.trans (h1.trans h2)
    · have hm := hM t ⟨ht, le_of_not_ge hbt⟩
      rw [Real.norm_eq_abs] at hm
      have hleM : suzukiPsi t ≤ |M| := (le_abs_self _).trans (hm.trans (le_abs_self M))
      have h1 : |M| ≤ (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) := by
        have : 1 ≤ (1 + t) ^ 2 * Real.exp (α * t) := one_le_mul_of_one_le_of_one_le hsq1 hexpα
        nlinarith [abs_nonneg M]
      have h2 : (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) ≤
          C₀ * Real.exp ((α + η) * t) := by
        rw [hC₀]
        calc (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t))
            ≤ (2 * A + |M|) * (Q * Real.exp ((α + η) * t)) :=
              mul_le_mul_of_nonneg_left hQexp (by positivity)
          _ = (2 * A + |M|) * Q * Real.exp ((α + η) * t) := by ring
      exact hleM.trans (h1.trans h2)
  rwa [xiSpectralPoint_im_eq, abs_sub_comm] at him

/-- **One-sided lower bound on `unitRieszSuzukiGreen` implies RH.** -/
theorem riemannHypothesis_of_unitRieszSuzukiGreen_boundedBelow
    {B : ℝ} (hB : ∀ t : ℝ, unitRieszSuzukiBase ≤ t → B ≤ unitRieszSuzukiGreen t) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_neg_exp_le_unitRieszSuzukiGreen (B := |B|) (α := 0)
    (abs_nonneg B) le_rfl (fun t ht => by
      rw [zero_mul, Real.exp_zero, mul_one]
      exact (neg_abs_le B).trans (hB t ht)) q
  linarith [(abs_le.mp h).2]

/-- **RH is equivalent to a one-sided lower bound on `unitRieszSuzukiGreen`.** -/
theorem riemannHypothesis_iff_unitRieszSuzukiGreen_boundedBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ t : ℝ,
      unitRieszSuzukiBase ≤ t → B ≤ unitRieszSuzukiGreen t := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := riemannHypothesis_iff_suzukiExplicitScrewBounded.mp hRH
    have hC0 : 0 ≤ C := (abs_nonneg (suzukiPsi 0)).trans (hC 0 le_rfl)
    refine ⟨-(4 * C + 2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase|), fun t ht => ?_⟩
    have habs := abs_unitRieszSuzukiGreen_le_of_suzuki_bound hC0 hC ht
    linarith [(abs_le.mp habs).1]
  · rintro ⟨B, hB⟩
    exact riemannHypothesis_of_unitRieszSuzukiGreen_boundedBelow hB

/-- **One-sided lower exponential strip law for `criticalMellinChebyshevResolventSource`.** -/
theorem abs_re_sub_half_le_of_neg_exp_le_criticalResolvent {B α : ℝ} (hB0 : 0 ≤ B) (hα0 : 0 ≤ α)
    (hR : ∀ t : ℝ, 0 ≤ t → -(B * Real.exp (α * t)) ≤ criticalMellinChebyshevResolventSource t)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  set B' : ℝ := B / 2 + unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  have hpolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    have := abs_unitRieszSuzukiPolarCorrection_le (le_rfl : unitRieszSuzukiBase ≤ unitRieszSuzukiBase)
    exact (abs_nonneg _).trans this
  have harch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    have := abs_unitRieszSuzukiArchCorrection_le (le_rfl : unitRieszSuzukiBase ≤ unitRieszSuzukiBase)
    exact (abs_nonneg _).trans this
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  refine abs_re_sub_half_le_of_neg_exp_le_unitRieszSuzukiGreen hB'0 hα0 (fun t ht => ?_) q
  have ht0 : 0 ≤ t := unitRieszSuzukiBase_pos.le.trans ht
  have heq := criticalMellinChebyshevResolventSource_half_eq_suzukiGreen ht
  have hpolar := (abs_le.mp (abs_unitRieszSuzukiPolarCorrection_le ht)).2
  have harch := (abs_le.mp (abs_unitRieszSuzukiArchCorrection_le ht)).1
  have hexp1 : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht0)
  have hRt := hR t ht0
  dsimp [B']
  nlinarith

/-- **One-sided lower bound on `criticalMellinChebyshevResolventSource` implies RH.** -/
theorem riemannHypothesis_of_criticalResolvent_boundedBelow
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → B ≤ criticalMellinChebyshevResolventSource t) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_neg_exp_le_criticalResolvent (B := |B|) (α := 0)
    (abs_nonneg B) le_rfl (fun t ht => by
      rw [zero_mul, Real.exp_zero, mul_one]
      exact (neg_abs_le B).trans (hB t ht)) q
  linarith [(abs_le.mp h).2]

/-- **RH is equivalent to a one-sided lower bound on `criticalMellinChebyshevResolventSource`.** -/
theorem riemannHypothesis_iff_criticalResolvent_boundedBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      B ≤ criticalMellinChebyshevResolventSource t := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ := riemannHypothesis_iff_unitRieszCriticalResolventBounded.mp hRH
    exact ⟨-B, fun t ht => by have := (abs_le.mp (hB t ht)).1; linarith⟩
  · rintro ⟨B, hB⟩
    exact riemannHypothesis_of_criticalResolvent_boundedBelow hB

/-- **One-sided lower integer-logarithmic strip law for `criticalMellinChebyshevResolventSource`.** -/
theorem abs_re_sub_half_le_of_neg_rpow_le_criticalResolvent_log_nat {B α : ℝ} (hB0 : 0 ≤ B)
    (hα0 : 0 ≤ α)
    (hN : ∀ N : ℕ, 2 ≤ N → -(B * (N : ℝ) ^ α) ≤ criticalMellinChebyshevResolventSource (Real.log N))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  refine abs_re_sub_half_le_of_neg_exp_le_criticalResolvent (B := B + 2 * (Real.log 4 + 5))
    (by positivity) hα0 (fun t ht => ?_) q
  have hexp1 : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht)
  by_cases hlog : Real.log 2 ≤ t
  · set X := Real.exp t
    set N : ℕ := ⌊X⌋₊
    have hX2 : (2 : ℝ) ≤ X := by
      rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
      exact Real.exp_le_exp.mpr hlog
    have hXpos : 0 < X := Real.exp_pos t
    have hN2 : 2 ≤ N := Nat.le_floor hX2
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hXpos.le
    have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
    have hcell := (abs_le.mp (UnitRieszOneSided.abs_resolvent_log_sub_nat_mul_le hN2 hNX hXN)).1
    rw [Real.log_exp] at hcell
    have hr0 : 0 ≤ (N : ℝ) / X := by positivity
    have hr1 : (N : ℝ) / X ≤ 1 := (div_le_one hXpos).2 hNX
    have hpow : (N : ℝ) ^ α ≤ Real.exp (α * t) := by
      calc (N : ℝ) ^ α ≤ X ^ α := Real.rpow_le_rpow (Nat.cast_nonneg N) hNX hα0
        _ = Real.exp (α * t) := by rw [← Real.exp_mul, mul_comm]
    have hsample : -(B * Real.exp (α * t)) ≤
        ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) := by
      have h1 : ((N : ℝ) / X) * (-(B * (N : ℝ) ^ α)) ≤
          ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) :=
        mul_le_mul_of_nonneg_left (hN N hN2) hr0
      have h2 : -(B * Real.exp (α * t)) ≤ ((N : ℝ) / X) * (-(B * (N : ℝ) ^ α)) := by
        have h3 : ((N : ℝ) / X) * (B * (N : ℝ) ^ α) ≤ 1 * (B * Real.exp (α * t)) :=
          mul_le_mul hr1 (mul_le_mul_of_nonneg_left hpow hB0) (by positivity) zero_le_one
        linarith
      exact h2.trans h1
    nlinarith
  · have hexp : Real.exp t < 2 := by
      calc Real.exp t < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (lt_of_not_ge hlog)
        _ = 2 := Real.exp_log (by norm_num)
    have hsum : (∑ k ∈ Finset.Icc 0 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp t))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkR : (k : ℝ) ≤ Real.exp t :=
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ)).trans
          (Nat.floor_le (Real.exp_pos t).le)
      have hk2 : k < 2 := by exact_mod_cast hkR.trans_lt hexp
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp
    have hsource := UnitRieszRealAperture.resolvent_log_eq_prime_sum (Real.exp_pos t)
    rw [Real.log_exp, hsum, mul_zero, zero_sub] at hsource
    rw [hsource]
    have hsqrt2 : Real.sqrt (Real.exp t) ≤ 2 := by
      have : Real.exp t ≤ 4 := by linarith
      calc Real.sqrt (Real.exp t) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt this
        _ = 2 := by norm_num
    nlinarith

/-- **RH is equivalent to a one-sided lower bound on `criticalMellinChebyshevResolventSource`
at integer logarithms.** -/
theorem riemannHypothesis_iff_criticalResolvent_logNat_boundedBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N →
      B ≤ criticalMellinChebyshevResolventSource (Real.log N) := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ :=
      exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
    exact ⟨-B, fun N hN => by have := (abs_le.mp (hB N hN)).1; linarith⟩
  · rintro ⟨B, hB⟩
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := abs_re_sub_half_le_of_neg_rpow_le_criticalResolvent_log_nat (B := |B|) (α := 0)
      (abs_nonneg B) le_rfl (fun N hN => by
        rw [Real.rpow_zero, mul_one]
        exact (neg_abs_le B).trans (hB N hN)) q
    linarith [(abs_le.mp h).2]

/-- **Lower comparison between `criticalMellinChebyshevResolventSource (Real.log M)` and
`mobiusDivisorSquareRootAbelMoment M / M`.** -/
theorem mobiusDivisorSquareRootAbel_le_resolvent_log_nat {M : ℕ} (hM : 2 ≤ M) :
    2 * (mobiusDivisorSquareRootAbelMoment M / M) -
        2 * (|2 * Real.eulerMascheroniConstant| + 1) ≤
      criticalMellinChebyshevResolventSource (Real.log M) := by
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsqrtSq := Real.sq_sqrt hMR.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by nlinarith [Real.sqrt_nonneg (M : ℝ)]
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |2 * Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_of_pos hMR, abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    apply (div_le_iff₀ hMR).2
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hlattice : |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hMR]
    exact (div_le_one hMR).2 ((abs_coherentSquareRootPolarLatticeDefect_le hM1).trans hsqrtLe)
  have hsource := congrArg (fun x : ℝ => x / (M : ℝ))
    (mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM1)
  rw [add_div] at hsource
  have hcharge := coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM
  rw [add_div] at hcharge
  have hres := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
  linarith [(abs_le.mp hgamma).2, (abs_le.mp hlattice).1]

/-- **One-sided lower power strip law for `mobiusDivisorSquareRootAbelMoment`.**
If `-(C + C M^c) ≤ mobiusDivisorSquareRootAbelMoment M / M` for `M ≥ 2` (`C ≥ 0`), then every
`q : XiZeroCopy` satisfies `|(q.1 : ℂ).re - 1/2| ≤ max 0 c`. -/
theorem abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → -(C + C * (M : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment M / M)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  set α : ℝ := max 0 c
  have hα0 : 0 ≤ α := le_max_left 0 c
  have hcα : c ≤ α := le_max_right 0 c
  refine abs_re_sub_half_le_of_neg_rpow_le_criticalResolvent_log_nat
    (B := 4 * C + 2 * (|2 * Real.eulerMascheroniConstant| + 1)) (by positivity) hα0
    (fun M hM2 => ?_) q
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hpow1 : 1 ≤ (M : ℝ) ^ α := Real.one_le_rpow hM1 hα0
  have hpowc : (M : ℝ) ^ c ≤ (M : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hM1 hcα
  have hres := mobiusDivisorSquareRootAbel_le_resolvent_log_nat hM2
  have hbound : -(2 * (C + C * (M : ℝ) ^ c)) ≤ 2 * (mobiusDivisorSquareRootAbelMoment M / M) := by
    have := mul_le_mul_of_nonneg_left (hM M hM2) (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hstep : -(4 * C + 2 * (|2 * Real.eulerMascheroniConstant| + 1)) * (M : ℝ) ^ α ≤
      -(2 * (C + C * (M : ℝ) ^ c)) - 2 * (|2 * Real.eulerMascheroniConstant| + 1) := by
    nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]
  exact ( by linarith [hstep] :
    -((4 * C + 2 * (|2 * Real.eulerMascheroniConstant| + 1)) * (M : ℝ) ^ α) ≤
      -(2 * (C + C * (M : ℝ) ^ c)) - 2 * (|2 * Real.eulerMascheroniConstant| + 1)).trans
    ((sub_le_sub_right hbound _).trans hres)

/-- **RH is equivalent to a one-sided lower bound on `mobiusDivisorSquareRootAbelMoment M / M`.** -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ M : ℕ, 2 ≤ M →
      B ≤ mobiusDivisorSquareRootAbelMoment M / M := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded.mp hRH
    exact ⟨-B, fun M hM => by have := (abs_le.mp (hB M hM)).1; linarith⟩
  · rintro ⟨B, hB⟩
    apply riemannHypothesis_iff_criticalResolvent_logNat_boundedBelow.mpr
    refine ⟨2 * B - 2 * (|2 * Real.eulerMascheroniConstant| + 1), fun M hM => ?_⟩
    have hres := mobiusDivisorSquareRootAbel_le_resolvent_log_nat hM
    have hBM : 2 * B ≤ 2 * (mobiusDivisorSquareRootAbelMoment M / M) :=
      mul_le_mul_of_nonneg_left (hB M hM) (by norm_num)
    exact (sub_le_sub_right hBM _).trans hres

/-- **One-sided lower subpower RH equivalence for `mobiusDivisorSquareRootAbelMoment`.** -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_oneSided_subpower_lower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      -(C * (M : ℝ) ^ ε) ≤ mobiusDivisorSquareRootAbelMoment M / M := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hbound⟩ :=
      riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower.mp hRH ε hε
    exact ⟨C, hC, fun M hM => by have := (abs_le.mp (hbound M hM)).1; linarith⟩
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC0, hC⟩ := h ε hε
    have hq := abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hC0
      (fun M hM => (neg_le_neg (le_add_of_nonneg_left hC0)).trans (hC M hM)) q
    rw [max_eq_right hε.le] at hq
    linarith [(abs_le.mp hq).2]

/-! ## Section 3: Unconditional square-root-gap lower transport and arbitrary power-gap
lower bootstrap for `mobiusDivisorSquareRootAbelMoment` -/

/-- **Unconditional pointwise lower transport for `mobiusDivisorSquareRootAbelMoment`.**
Requires only `1 ≤ k ≤ n` (using `ψ(k) ≥ 0` and `γ ≥ 0` via `mobiusDivisorSquareRootAbel_sub_ge_neg_mul`),
with **no** Chebyshev or zero-free-region bound. -/
theorem mobiusDivisorSquareRootAbel_div_ge_of_unconditional_sample {k n : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    min (mobiusDivisorSquareRootAbelMoment k / k) 0 - ((n : ℝ) - k) / Real.sqrt n ≤
      mobiusDivisorSquareRootAbelMoment n / n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn1 : 1 ≤ n := le_trans hk hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hdrift := mobiusDivisorSquareRootAbel_sub_ge_neg_mul hk hkn
  have hsq : Real.sqrt n - Real.sqrt k ≤ ((n : ℝ) - k) / Real.sqrt n :=
    (le_div_iff₀ hsn0).mpr (sqrt_sub_sqrt_mul_sqrt_le hkn)
  have herr : -(((n : ℝ) - k) / Real.sqrt n) ≤
      (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by
    have h1 : -(Real.sqrt n - Real.sqrt k) ≤
        (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by
      rw [le_div_iff₀ hn0]
      linarith
    exact (neg_le_neg hsq).trans h1
  have hbase : min (mobiusDivisorSquareRootAbelMoment k / k) 0 ≤
      mobiusDivisorSquareRootAbelMoment k / n := by
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hr0 : 0 ≤ (k : ℝ) / n := by positivity
    have hr1 : (k : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hknR
    have hmin0 : min (mobiusDivisorSquareRootAbelMoment k / k) 0 ≤ 0 := min_le_right _ _
    calc min (mobiusDivisorSquareRootAbelMoment k / k) 0
        = 1 * min (mobiusDivisorSquareRootAbelMoment k / k) 0 := (one_mul _).symm
      _ ≤ ((k : ℝ) / n) * min (mobiusDivisorSquareRootAbelMoment k / k) 0 :=
          mul_le_mul_of_nonpos_right hr1 hmin0
      _ ≤ ((k : ℝ) / n) * (mobiusDivisorSquareRootAbelMoment k / k) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hr0
      _ = mobiusDivisorSquareRootAbelMoment k / n := by field_simp
  have hsplit : mobiusDivisorSquareRootAbelMoment n / n =
      mobiusDivisorSquareRootAbelMoment k / n +
        (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by ring
  rw [hsplit, sub_eq_add_neg]
  exact add_le_add hbase herr

/-- **Bootstrap-free `O(√n)`-gap lower strip law for `mobiusDivisorSquareRootAbelMoment`.**
Because `mobiusDivisorSquareRootAbel_div_ge_of_unconditional_sample` loses at most `(n − k)/√n`, any
sampling set `A ⊆ ℕ` with gaps `n − k ≤ K √n` (such as the squares `k = j²`) transports a lower bound
`-(M + M k^c)` to all integers in a single step without any Chebyshev or Von Koch input. -/
theorem abs_re_sub_half_le_of_sqrtGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    {A : Set ℕ} {M c K : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hK : 0 ≤ K)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / k)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * Real.sqrt n)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  set a : ℝ := max 0 c
  have ha0 : 0 ≤ a := le_max_left 0 c
  have hca : c ≤ a := le_max_right 0 c
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  set N₁ : ℕ := max N₀ (max N₂ 4)
  set S : ℝ := ∑ j ∈ Finset.range N₁, |mobiusDivisorSquareRootAbelMoment j / j|
  have hS0 : 0 ≤ S := by positivity
  set D : ℝ := 2 * M + K + S
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hall : ∀ n : ℕ, 2 ≤ n →
      -(D + D * (n : ℝ) ^ a) ≤ mobiusDivisorSquareRootAbelMoment n / n := by
    intro n hn2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hna1 : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hn1 ha0
    rcases le_or_gt N₁ n with hnN₁ | hnN₁
    · have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hnN₁
      have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN₁
      have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN₁
      obtain ⟨k, hkA, hkn, hgapn⟩ := hgap n hnN₀
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hsplit : Real.sqrt n = (n : ℝ) ^ (-(1 / 2 : ℝ)) * n := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hn0.ne']
        congr 1; ring
      have hhalf : K * Real.sqrt n ≤ n / 2 := by
        have := hN₂ n hnN₂; rw [hsplit, ← mul_assoc]; nlinarith
      have hk2 : 2 ≤ k := by
        have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
        have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
        have : (2 : ℝ) ≤ k := by linarith
        exact_mod_cast this
      have hstep := mobiusDivisorSquareRootAbel_div_ge_of_unconditional_sample (by omega) hkn
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hkc : (k : ℝ) ^ c ≤ (n : ℝ) ^ a := by
        calc (k : ℝ) ^ c ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hk1 hca
          _ ≤ (n : ℝ) ^ a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) ha0
      have hAk : -(2 * M * (n : ℝ) ^ a) ≤ min (mobiusDivisorSquareRootAbelMoment k / k) 0 := by
        apply le_min
        · refine ( by nlinarith : -(2 * M * (n : ℝ) ^ a) ≤ -(M + M * (k : ℝ) ^ c)).trans
            (hA k hkA hk2)
        · have : 0 ≤ 2 * M * (n : ℝ) ^ a := by positivity
          linarith
      have hdiv : ((n : ℝ) - k) / Real.sqrt n ≤ K := (div_le_iff₀ hsn0).mpr hgapn
      have hDbound : -(D + D * (n : ℝ) ^ a) ≤ -(2 * M * (n : ℝ) ^ a) - K := by
        dsimp [D]; nlinarith
      exact hDbound.trans ((sub_le_sub hAk hdiv).trans hstep)
    · have hmem : n ∈ Finset.range N₁ := Finset.mem_range.mpr hnN₁
      have hleS : |mobiusDivisorSquareRootAbelMoment n / n| ≤ S :=
        Finset.single_le_sum (f := fun j : ℕ => |mobiusDivisorSquareRootAbelMoment j / j|)
          (fun j _ => abs_nonneg _) hmem
      have hSbound : -(D + D * (n : ℝ) ^ a) ≤ -S := by dsimp [D]; nlinarith
      exact hSbound.trans ((neg_le_neg hleS).trans (neg_abs_le _))
  have h := abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hD0 hall q
  rwa [max_eq_right ha0] at h

/-- **Pointwise power-gap lower transport for `mobiusDivisorSquareRootAbelMoment`.**
If `1 ≤ k ≤ n`, `n − k ≤ K n^{1−δ}`, and `|ψ(d) − d| ≤ C d^β` for `1 ≤ d`, then
`min (mobiusDivisorSquareRootAbelMoment k / k) 0 − K C n^{β − 1/2 − δ} ≤
mobiusDivisorSquareRootAbelMoment n / n`. -/
theorem mobiusDivisorSquareRootAbel_div_ge_of_sample {K δ C β : ℝ} {k n : ℕ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hgapn : (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β) :
    min (mobiusDivisorSquareRootAbelMoment k / k) 0 -
        K * C * (n : ℝ) ^ (β - 1 / 2 - δ) ≤
      mobiusDivisorSquareRootAbelMoment n / n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn1 : 1 ≤ n := le_trans hk hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsn : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    have := eulerMascheroniConstant_gt; linarith
  have hw : ∀ d : ℕ, 0 ≤ Real.sqrt (d + 1 : ℕ) - Real.sqrt d := fun d =>
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ d))
  have hterm : ∀ d ∈ Finset.Ico k n,
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) * (-(C * (n : ℝ) ^ β)) ≤
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder d + 2 * Real.eulerMascheroniConstant) := by
    intro d hd
    obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
    apply mul_le_mul_of_nonneg_left _ (hw d)
    have hd1 : 1 ≤ d := le_trans hk hkd
    have hdψ : -(C * (n : ℝ) ^ β) ≤ psiRemainder d := by
      rw [psiRemainder, chebyshevPsi_eq_psi]
      have h1 := (abs_le.mp (hψ d hd1)).1
      have h2 : C * (d : ℝ) ^ β ≤ C * (n : ℝ) ^ β :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdn.le) hβ) hC
      linarith
    linarith
  have hdiff : -((Real.sqrt n - Real.sqrt k) * (C * (n : ℝ) ^ β)) ≤
      mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k := by
    rw [mobiusDivisorSquareRootAbel_sub_eq hk hkn]
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, sum_Ico_sqrt_succ_sub hkn] at hsum
    linarith
  set y : ℝ := (n : ℝ) ^ (β - 1 / 2 - δ) with hy
  have hkey : (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β = y * ((n : ℝ) * Real.sqrt n) := by
    rw [hy, hsn, ← Real.rpow_add hn0, show (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) + 1 / 2) by rw [Real.rpow_add hn0, Real.rpow_one],
      ← Real.rpow_add hn0]
    ring_nf
  have herr : -(K * C * y) ≤
      (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by
    rw [le_div_iff₀ hn0]
    have hmul := mul_le_mul_of_nonneg_right hdiff hsn0.le
    have hsq := sqrt_sub_sqrt_mul_sqrt_le hkn
    have hstep : (Real.sqrt n - Real.sqrt k) * (C * (n : ℝ) ^ β) * Real.sqrt n ≤
        (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β) := by
      calc (Real.sqrt n - Real.sqrt k) * (C * (n : ℝ) ^ β) * Real.sqrt n
          = ((Real.sqrt n - Real.sqrt k) * Real.sqrt n) * (C * (n : ℝ) ^ β) := by ring
        _ ≤ (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β) :=
            mul_le_mul_of_nonneg_right (hsq.trans hgapn) (by positivity)
    have hstep2 : (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β) =
        (K * C * y * n) * Real.sqrt n := by
      calc (K * (n : ℝ) ^ (1 - δ)) * (C * (n : ℝ) ^ β)
          = K * C * ((n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β) := by ring
        _ = K * C * (y * ((n : ℝ) * Real.sqrt n)) := by rw [hkey]
        _ = (K * C * y * n) * Real.sqrt n := by ring
    have hcomb : -((K * C * y * n) * Real.sqrt n) ≤
        (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) * Real.sqrt n := by
      have hneg := neg_le_neg (hstep.trans hstep2.le)
      linarith
    exact le_of_mul_le_mul_right (by linarith [hcomb]) hsn0
  have hbase : min (mobiusDivisorSquareRootAbelMoment k / k) 0 ≤
      mobiusDivisorSquareRootAbelMoment k / n := by
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hr0 : 0 ≤ (k : ℝ) / n := by positivity
    have hr1 : (k : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hknR
    have hmin0 : min (mobiusDivisorSquareRootAbelMoment k / k) 0 ≤ 0 := min_le_right _ _
    calc min (mobiusDivisorSquareRootAbelMoment k / k) 0
        = 1 * min (mobiusDivisorSquareRootAbelMoment k / k) 0 := (one_mul _).symm
      _ ≤ ((k : ℝ) / n) * min (mobiusDivisorSquareRootAbelMoment k / k) 0 :=
          mul_le_mul_of_nonpos_right hr1 hmin0
      _ ≤ ((k : ℝ) / n) * (mobiusDivisorSquareRootAbelMoment k / k) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hr0
      _ = mobiusDivisorSquareRootAbelMoment k / n := by field_simp
  have hsplit : mobiusDivisorSquareRootAbelMoment n / n =
      mobiusDivisorSquareRootAbelMoment k / n +
        (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by ring
  rw [hsplit, sub_eq_add_neg]
  exact add_le_add hbase herr

/-- **One round of power-gap lower transport for `mobiusDivisorSquareRootAbelMoment`.** -/
theorem exists_neg_rpow_le_mobiusDivisorSquareRootAbel_of_powerGaps {A : Set ℕ} {M c K δ C β : ℝ}
    {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / k)
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ n : ℕ, 2 ≤ n →
      -(M' + M' * (n : ℝ) ^ max (max c 0) (max (β - 1 / 2 - δ) 0)) ≤
        mobiusDivisorSquareRootAbelMoment n / n := by
  set a := max (max c 0) (max (β - 1 / 2 - δ) 0) with hadef
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) (le_max_right _ _)
  have hca : c ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have hba : β - 1 / 2 - δ ≤ a := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  set N₁ : ℕ := max N₀ (max N₂ 4)
  set S : ℝ := ∑ j ∈ Finset.range N₁, |mobiusDivisorSquareRootAbelMoment j / j|
  have hS0 : 0 ≤ S := by positivity
  set D : ℝ := 2 * M + K * C + S
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD0, fun n hn2 => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hna1 : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hn1 ha0
  rcases le_or_gt N₁ n with hnN₁ | hnN₁
  · have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hnN₁
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN₁
    have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN₁
    obtain ⟨k, hkA, hkn, hgapn⟩ := hgap n hnN₀
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsplit : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
      rw [show (1 : ℝ) - δ = -δ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    have hhalf : K * (n : ℝ) ^ (1 - δ) ≤ n / 2 := by
      have := hN₂ n hnN₂; rw [hsplit, ← mul_assoc]; nlinarith
    have hk2 : 2 ≤ k := by
      have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
      have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      have : (2 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hstep := mobiusDivisorSquareRootAbel_div_ge_of_sample hC hβ (by omega) hkn hgapn hψ
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hkc : (k : ℝ) ^ c ≤ (n : ℝ) ^ a := by
      calc (k : ℝ) ^ c ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hk1 hca
        _ ≤ (n : ℝ) ^ a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) ha0
    have hnb : (n : ℝ) ^ (β - 1 / 2 - δ) ≤ (n : ℝ) ^ a :=
      Real.rpow_le_rpow_of_exponent_le hn1 hba
    have hAk : -(2 * M * (n : ℝ) ^ a) ≤ min (mobiusDivisorSquareRootAbelMoment k / k) 0 := by
      apply le_min
      · refine ( by nlinarith : -(2 * M * (n : ℝ) ^ a) ≤ -(M + M * (k : ℝ) ^ c)).trans
          (hA k hkA hk2)
      · have : 0 ≤ 2 * M * (n : ℝ) ^ a := by positivity
        linarith
    have hKC : -(K * C * (n : ℝ) ^ a) ≤ -(K * C * (n : ℝ) ^ (β - 1 / 2 - δ)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hnb (by positivity))
    have hDbound : -(D + D * (n : ℝ) ^ a) ≤ -(2 * M * (n : ℝ) ^ a) - K * C * (n : ℝ) ^ a := by
      dsimp [D]; nlinarith
    exact hDbound.trans ((sub_le_sub hAk (mul_le_mul_of_nonneg_left hnb (by positivity))).trans hstep)
  · have hmem : n ∈ Finset.range N₁ := Finset.mem_range.mpr hnN₁
    have hleS : |mobiusDivisorSquareRootAbelMoment n / n| ≤ S :=
      Finset.single_le_sum (f := fun j : ℕ => |mobiusDivisorSquareRootAbelMoment j / j|)
        (fun j _ => abs_nonneg _) hmem
    have hSbound : -(D + D * (n : ℝ) ^ a) ≤ -S := by dsimp [D]; nlinarith
    exact hSbound.trans ((neg_le_neg hleS).trans (neg_abs_le _))

/-- **Two-step supremum fixed-point lower bootstrap for `mobiusDivisorSquareRootAbelMoment`.**
If `A ⊆ ℕ` meets every window `[n − K n^{1−δ}, n]` for `n ≥ N₀` (`δ > 0`) and
`-(M + M k^c) ≤ mobiusDivisorSquareRootAbelMoment k / k` on `A` (`M ≥ 0`), then every zero satisfies
`|Re ρ − 1/2| ≤ max 0 c`. -/
theorem abs_re_sub_half_le_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / k)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα0 : 0 ≤ α := le_trans (abs_nonneg _) (hαall q)
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q' : XiZeroCopy => (xiZeroCopy_re_lt_one q').le)
    rw [hαdef]; linarith
  by_cases hc : 1 / 2 ≤ max 0 c
  · exact (hαall q).trans (by linarith)
  push Not at hc
  -- Step 1 (Chebyshev β = 1): prove α < 1/2
  have hψ1 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) ^ (1 : ℝ) := by
    intro N _
    rw [Real.rpow_one]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]; constructor <;> linarith
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_neg_rpow_le_mobiusDivisorSquareRootAbel_of_powerGaps hM0 hδ hK
    (by norm_num) (by norm_num) hA hψ1 hgap
  set a₁ := max (max c 0) (max ((1 : ℝ) - 1 / 2 - δ) 0) with ha₁
  have ha₁0 : 0 ≤ a₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₁ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + a₁ := fun q' => by
    have hq' := abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hM₁0 hM₁ q'
    rw [max_eq_right ha₁0] at hq'
    linarith [(abs_le.mp hq').2]
  have hsup₁ := zeroReSup_le hg₁
  have hle₁ : α ≤ a₁ := by linarith
  have hαlt : α < 1 / 2 := by
    have hc1 : max c 0 < 1 / 2 := by rwa [max_comm]
    have hc2 : max ((1 : ℝ) - 1 / 2 - δ) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
    exact lt_of_le_of_lt hle₁ (max_lt hc1 hc2)
  -- Step 2 (Von Koch at e = α < 1/2): prove α ≤ max 0 c
  obtain ⟨C₂, hC₂0, hC₂⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
    hα0 hαlt hXi (show 0 < δ / 2 by positivity)
  have hψ2 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C₂ * (N : ℝ) ^ (1 / 2 + α + δ / 2) := by
    intro N hN
    rw [psi_natCast_eq_sum_Icc_one]
    exact hC₂ N hN
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_neg_rpow_le_mobiusDivisorSquareRootAbel_of_powerGaps hM0 hδ hK
    hC₂0.le (by positivity) hA hψ2 hgap
  set a₂ := max (max c 0) (max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0) with ha₂
  have ha₂0 : 0 ≤ a₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₂ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + a₂ := fun q' => by
    have hq' := abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hM₂0 hM₂ q'
    rw [max_eq_right ha₂0] at hq'
    linarith [(abs_le.mp hq').2]
  have hsup₂ := zeroReSup_le hg₂
  have hle₂ : α ≤ a₂ := by linarith
  have hαc : α ≤ max 0 c := by
    by_contra hlt
    push Not at hlt
    have hc1 : max c 0 < α := by rwa [max_comm]
    have hc2 : max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0 < α :=
      max_lt (by linarith) (lt_of_le_of_lt (le_max_left 0 c) hlt)
    have hc3 : a₂ < α := max_lt hc1 hc2
    linarith
  exact (hαall q).trans hαc

/-- **Power-gap lower sampling of `mobiusDivisorSquareRootAbelMoment` gives RH.** -/
theorem riemannHypothesis_of_powerGaps_le_mobiusDivisorSquareRootAbel
    {A : Set ℕ} {M K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ mobiusDivisorSquareRootAbelMoment k / k) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hA' : ∀ k ∈ A, 2 ≤ k →
      -(|M| + |M| * (k : ℝ) ^ (0 : ℝ)) ≤ mobiusDivisorSquareRootAbelMoment k / k := by
    intro k hkA hk2
    rw [Real.rpow_zero, mul_one]
    exact ( by linarith [neg_abs_le M, abs_nonneg M] : -(|M| + |M|) ≤ M).trans (hA k hkA hk2)
  have h := abs_re_sub_half_le_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    (abs_nonneg M) hδ hK hA' hgap q
  rw [max_self] at h
  linarith [(abs_le.mp h).2]

/-- **RH ⟺ `mobiusDivisorSquareRootAbelMoment` is bounded below on a power-gap sampling set.** -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddBelow_of_powerGaps
    {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k →
      M ≤ mobiusDivisorSquareRootAbelMoment k / k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_powerGaps_le_mobiusDivisorSquareRootAbel hδ hK hgap hM

/-- **Every `m`-th power sequence (`m ≥ 1`) decides RH by lower boundedness of
`mobiusDivisorSquareRootAbelMoment`.** -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddBelow {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
      M ≤ mobiusDivisorSquareRootAbelMoment (j ^ m) / (j ^ m : ℕ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap : ∀ n : ℕ, 1 ≤ n → ∃ k ∈ Set.range (fun j : ℕ => j ^ m), k ≤ n ∧
      (n : ℝ) - k ≤ (m * 2 ^ (m - 1) : ℝ) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hj, hgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hj, hgap⟩
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddBelow_of_powerGaps
    (by positivity) (by positivity) hgap]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ hj⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k hk hk2 => ?_⟩
    obtain ⟨j, rfl⟩ := hk
    exact hM j hk2

/-- **Adaptive power-window lower criterion for `mobiusDivisorSquareRootAbelMoment`.**
RH holds iff for some `δ > 0` and level `M`, every power window `[n − n^{1−δ}, n]` contains a point
`k` where `M ≤ mobiusDivisorSquareRootAbelMoment k / k`. -/
theorem riemannHypothesis_iff_exists_powerWindow_le_mobiusDivisorSquareRootAbel :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) ∧
        M ≤ mobiusDivisorSquareRootAbelMoment k / k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedBelow.mp h
    refine ⟨1 / 2, by norm_num, M, 2, fun n hn => ⟨n, hn, le_rfl, ?_, hM n hn⟩⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, M, N₀, h⟩
    refine riemannHypothesis_of_powerGaps_le_mobiusDivisorSquareRootAbel
      (A := {k | 2 ≤ k ∧ M ≤ mobiusDivisorSquareRootAbelMoment k / k})
      (M := M) (K := 1) (N₀ := N₀) hδ zero_le_one (fun n hn => ?_) (fun k hk _ => hk.2)
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := h n hn
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

end
end RHTower
