import GaloisForLFunctions.RHTower.WeilFiniteBlockMinorantSeparation
import GaloisForLFunctions.RHTower.WeilDeviationTranslationBound

/-!
# Finite excess-mass budgets from log-shift observations

The finite complex probe panel has a uniform weighted l1 bound with constant
`4 * riemannAutocorr 0`. Capping coefficients at von Mangoldt changes that panel
by at most this constant times the visible normalized excess mass.

Consequently a prescribed deficit `δ` and a panel lower bound `-η` force visible
excess mass at least `max (δ / 100 - η / (4 * riemannAutocorr 0)) 0`, uniformly
over sufficiently large integer windows. No tail or full-positivity premise is used.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Normalized positive coefficient excess in the block visible to one finite panel. -/
def weilFiniteBlockExcessMass (windowIndex : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊,
    WeilExcess.deviationExcess lam n

/-- The paired log-shift kernel is bounded uniformly in truncation, shift and sample point. -/
theorem norm_logShiftRiemannPair_le (L c y : ℝ) :
    ‖EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) y +
      EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) (-y)‖ ≤
        4 * riemannAutocorr 0 := by
  have heq : EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) y +
      EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) (-y) =
      ((4 * truncatedRiemannAutocorr L y - 2 * truncatedRiemannAutocorr L (y + c) -
        2 * truncatedRiemannAutocorr L (y - c) : ℝ) : ℂ) := by
    rw [weilTest_logShiftRiemannDifference, weilTest_logShiftRiemannDifference,
      truncatedRiemannAutocorr_neg L y,
      show -y + c = -(y - c) by ring, show -y - c = -(y + c) by ring,
      truncatedRiemannAutocorr_neg L (y - c), truncatedRiemannAutocorr_neg L (y + c)]
    push_cast
    ring
  have hle (z : ℝ) : truncatedRiemannAutocorr L z ≤ riemannAutocorr 0 :=
    (truncatedRiemannAutocorr_le_riemannAutocorr L z).trans
      (WeilExcess.riemannAutocorr_le_zero z)
  have h0 := truncatedRiemannAutocorr_nonneg L y
  have h1 := truncatedRiemannAutocorr_nonneg L (y + c)
  have h2 := truncatedRiemannAutocorr_nonneg L (y - c)
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [h0, h1, h2, hle y, hle (y + c), hle (y - c)]

/-- Exact finite affine dependence of each complex panel entry on the visible coefficients. -/
theorem weilLogShiftWindowPanel_sub (windowIndex : ℕ) (lam mu : ℕ → ℝ)
    (m : Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊) :
    weilLogShiftWindowPanel windowIndex lam m - weilLogShiftWindowPanel windowIndex mu m =
      -∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊,
        (((lam n - mu n) / Real.sqrt n : ℝ) : ℂ) *
          (EF.weilTest (logShiftRiemannDifference windowIndex (Real.log m.1))
            (logShiftRiemannDifference windowIndex (Real.log m.1)) (Real.log n) +
           EF.weilTest (logShiftRiemannDifference windowIndex (Real.log m.1))
            (logShiftRiemannDifference windowIndex (Real.log m.1)) (-Real.log n)) := by
  let f := logShiftRiemannDifference windowIndex (Real.log m.1)
  let g := EF.weilTest f f
  let S := Finset.Icc 2 ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊
  let term (v : ℕ → ℝ) (n : ℕ) : ℂ :=
    (((if 2 ≤ n then weilLogShiftWindowCompletion windowIndex v n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (g (Real.log n) + g (-Real.log n)))
  have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference _ _
  have hgc : HasCompactSupport g := EF.weilTest_hasCompactSupport hfc hfc
  have hs (v : ℕ → ℝ) : Summable (term v) :=
    summable_primeAtoms (fun n => if 2 ≤ n then
      weilLogShiftWindowCompletion windowIndex v n / Real.sqrt n else 0) hgc
  have hout : ∀ n ∉ S, term lam n - term mu n = 0 := by
    intro n hn
    by_cases hn2 : 2 ≤ n
    · have hb : ¬ (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) := by
        intro hb
        exact hn (Finset.mem_Icc.mpr ⟨hn2, Nat.le_floor hb⟩)
      simp only [term, if_pos hn2, weilLogShiftWindowCompletion, if_neg hb, sub_self]
    · simp only [term, if_neg hn2, sub_self]
  have hdiff : (∑' n, term lam n) - (∑' n, term mu n) =
      ∑ n ∈ S, (((lam n - mu n) / Real.sqrt n : ℝ) : ℂ) *
        (g (Real.log n) + g (-Real.log n)) := by
    rw [← Summable.tsum_sub (hs lam) (hs mu), tsum_eq_sum (s := S) hout]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊ := (Finset.mem_Icc.mp hn).2
    have hb : (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) := by
      calc (n : ℝ) ≤ (⌊Real.exp (4 * (windowIndex : ℝ))⌋₊ : ℝ) := by exact_mod_cast hnN
        _ ≤ Real.exp (4 * (windowIndex : ℝ)) := Nat.floor_le (Real.exp_pos _).le
    simp only [term, if_pos hn2, weilLogShiftWindowCompletion, if_pos hb]
    push_cast
    ring
  have e1 := congrFun (weilLogShiftWindowPanel_completion windowIndex lam) m
  have e2 := congrFun (weilLogShiftWindowPanel_completion windowIndex mu) m
  change weilFullFunctional (weilLogShiftWindowCompletion windowIndex lam) g =
    weilFullFunctional lam g at e1
  change weilFullFunctional (weilLogShiftWindowCompletion windowIndex mu) g =
    weilFullFunctional mu g at e2
  change weilFullFunctional lam g - weilFullFunctional mu g =
    -∑ n ∈ S, (((lam n - mu n) / Real.sqrt n : ℝ) : ℂ) *
      (g (Real.log n) + g (-Real.log n))
  rw [← e1, ← e2]
  unfold weilFullFunctional
  calc _ = -((∑' n, term lam n) - ∑' n, term mu n) := by dsimp only [term]; ring
    _ = _ := by rw [hdiff]

/-- Uniform weighted l1 stability of every entry of the finite complex probe panel. -/
theorem weilLogShiftWindowPanel_lipschitz (windowIndex : ℕ) (lam mu : ℕ → ℝ)
    (m : Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊) :
    ‖weilLogShiftWindowPanel windowIndex lam m - weilLogShiftWindowPanel windowIndex mu m‖ ≤
      (4 * riemannAutocorr 0) *
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊,
          |(lam n - mu n) / Real.sqrt n| := by
  rw [weilLogShiftWindowPanel_sub, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ |(lam n - mu n) / Real.sqrt n| * (4 * riemannAutocorr 0) :=
      mul_le_mul_of_nonneg_left (norm_logShiftRiemannPair_le _ _ _) (abs_nonneg _)
    _ = _ := by ring

/-- A prescribed deficit and a lower bound on a finite panel force a quantitative visible
excess budget. The cutoff is independent of both the sequence and the panel lower bound. -/
theorem exists_uniform_finiteBlock_excessMass_budget (q : ℕ) (t : ℝ) :
    ∃ cutoff : ℕ, ∀ windowIndex : ℕ, cutoff ≤ windowIndex → ∀ η : ℝ,
      {lam : ℕ → ℝ |
        (∀ m, -η ≤ (weilLogShiftWindowPanel windowIndex lam m).re) ∧
        Real.exp t ≤ ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - lam (q + 2)) /
          Real.sqrt ((q + 2 : ℕ) : ℝ)} ⊆
      {lam | max (Real.exp t / 100 - η / (4 * riemannAutocorr 0)) 0 ≤
        weilFiniteBlockExcessMass windowIndex lam} := by
  obtain ⟨cutoff, hcutoff⟩ := exists_uniform_finiteBlock_logShift_separation q t
  refine ⟨cutoff, ?_⟩
  rintro windowIndex hk η lam ⟨hfloor, hgap⟩
  let capped : ℕ → ℝ := fun n => min (lam n) (ArithmeticFunction.vonMangoldt n : ℝ)
  have hblock : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) →
      capped n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    fun n _ _ => min_le_right _ _
  have hgap' : Real.exp t ≤
      ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - capped (q + 2)) /
        Real.sqrt ((q + 2 : ℕ) : ℝ) :=
    hgap.trans (div_le_div_of_nonneg_right
      (sub_le_sub_left (min_le_left _ _) _) (Real.sqrt_nonneg _))
  obtain ⟨m, hm2, hmBound, htest⟩ := hcutoff windowIndex hk ⟨hblock, hgap'⟩
  have hm : m ∈ Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊ :=
    Finset.mem_Icc.mpr ⟨hm2, Nat.le_floor hmBound⟩
  have hexc : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * (windowIndex : ℝ))⌋₊,
      |(lam n - capped n) / Real.sqrt n|) = weilFiniteBlockExcessMass windowIndex lam := by
    unfold weilFiniteBlockExcessMass
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    dsimp only [capped, WeilExcess.deviationExcess, WeilExcess.weilDeviation]
    rw [if_pos hn2]
    by_cases h : lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)
    · have hn : (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (Real.sqrt_nonneg _)
      simp only [min_eq_left h, sub_self, zero_div, abs_zero, max_eq_right hn]
    · have hle : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := (lt_of_not_ge h).le
      have hn : 0 ≤ (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n :=
        div_nonneg (sub_nonneg.mpr hle) (Real.sqrt_nonneg _)
      simp only [min_eq_right hle, abs_of_nonneg hn, max_eq_left hn]
  have hnorm := weilLogShiftWindowPanel_lipschitz windowIndex lam capped ⟨m, hm⟩
  rw [hexc] at hnorm
  have hreal := Complex.re_le_norm (weilLogShiftWindowPanel windowIndex lam ⟨m, hm⟩ -
    weilLogShiftWindowPanel windowIndex capped ⟨m, hm⟩)
  rw [Complex.sub_re] at hreal
  have hobs := hfloor ⟨m, hm⟩
  change (weilLogShiftWindowPanel windowIndex capped ⟨m, hm⟩).re ≤
    -(Real.exp t * riemannAutocorr 0) / 25 at htest
  have hbudget : (4 * riemannAutocorr 0) * (Real.exp t / 100) ≤
      (4 * riemannAutocorr 0) * weilFiniteBlockExcessMass windowIndex lam + η := by
    linarith only [hnorm, hreal, hobs, htest]
  have hC := riemannAutocorr_zero_pos
  have hC4 : 0 < 4 * riemannAutocorr 0 := by positivity
  have hdiv : (4 * riemannAutocorr 0) * (η / (4 * riemannAutocorr 0)) = η := by
    field_simp [hC.ne']
  have hbound : Real.exp t / 100 - η / (4 * riemannAutocorr 0) ≤
      weilFiniteBlockExcessMass windowIndex lam := by
    apply (mul_le_mul_iff_right₀ hC4).mp
    rw [mul_sub, hdiv]
    linarith only [hbudget]
  have hnonneg : 0 ≤ weilFiniteBlockExcessMass windowIndex lam :=
    Finset.sum_nonneg fun n _ => WeilExcess.deviationExcess_nonneg lam n
  exact max_le hbound hnonneg

/-- With a nonnegative finite panel, the visible normalized excess is at least one
hundredth of any prescribed positive coordinate deficit, uniformly beyond one cutoff. -/
theorem exists_uniform_finiteBlock_excessMass_of_deficit (q : ℕ) (t : ℝ) :
    ∃ cutoff : ℕ, ∀ windowIndex : ℕ, cutoff ≤ windowIndex →
      {lam : ℕ → ℝ |
        (∀ m, 0 ≤ (weilLogShiftWindowPanel windowIndex lam m).re) ∧
        Real.exp t ≤ ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - lam (q + 2)) /
          Real.sqrt ((q + 2 : ℕ) : ℝ)} ⊆
      {lam | Real.exp t / 100 ≤ weilFiniteBlockExcessMass windowIndex lam} := by
  obtain ⟨cutoff, hcutoff⟩ := exists_uniform_finiteBlock_excessMass_budget q t
  refine ⟨cutoff, ?_⟩
  rintro windowIndex hk lam ⟨hpos, hgap⟩
  have h := hcutoff windowIndex hk 0 ⟨by simpa only [neg_zero] using hpos, hgap⟩
  change max (Real.exp t / 100 - (0 : ℝ) / (4 * riemannAutocorr 0)) 0 ≤
    weilFiniteBlockExcessMass windowIndex lam at h
  have hδ : 0 ≤ Real.exp t / 100 := by positivity
  change Real.exp t / 100 ≤ weilFiniteBlockExcessMass windowIndex lam
  simpa only [zero_div, sub_zero, max_eq_left hδ] using h

end RHTower

end
