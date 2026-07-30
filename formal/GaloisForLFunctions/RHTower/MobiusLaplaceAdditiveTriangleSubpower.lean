import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTrianglePolylog
import GaloisForLFunctions.RHTower.MobiusLaplaceSubpowerCriterion
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Subpower additive-triangle source criterion

This file connects a one-sided `N^(1+o(1))` upper estimate for the cumulative additive Möbius
triangle to every strict half-power estimate for the Möbius--Laplace transform.  The analytic
input is a real-power exponential-moment bound obtained by sum--integral comparison.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Real-power exponential moments are summable and admit an explicit Gamma upper bound. -/
theorem summable_natSucc_rpow_exp_neg_and_tsum_le {r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 < x) :
    Summable (fun N : ℕ => ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ∧
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
        1 + Real.exp x * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
  let f : ℕ → ℝ := fun N => ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))
  let g : ℝ → ℝ := fun t =>
    Real.exp x * 2 ^ r * ((max t 0) ^ r * Real.exp (-(x * t)))
  have hbase : IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(x * t))) (Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := r) (b := x) (by linarith) (by norm_num) hx)
  have hbaseMax :
      IntegrableOn (fun t : ℝ => (max t 0) ^ r * Real.exp (-(x * t))) (Ioi 0) := by
    apply hbase.congr_fun
    · intro t ht
      change 0 < t at ht
      simp only [max_eq_left ht.le]
    · exact measurableSet_Ioi
  have hg : IntegrableOn g (Ioi 0) := by
    exact hbaseMax.const_mul (Real.exp x * 2 ^ r)
  have hgNonneg : ∀ t : ℝ, 0 ≤ g t := by
    intro t
    dsimp [g]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (Real.exp_pos _).le)
  have hfinite (M : ℕ) :
      ∑ N ∈ Finset.range M, f N ≤
        1 + Real.exp x * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
    by_cases hM : M = 0
    · subst M
      simp
      positivity
    have hMone : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    have hsplit :
        ∑ N ∈ Finset.range M, f N = 1 + ∑ N ∈ Finset.Ico 1 M, f N := by
      rw [Finset.sum_Ico_eq_sub f hMone]
      simp [f]
    rw [hsplit]
    have hcompare :
        ∑ N ∈ Finset.Ico 1 M, f N ≤ ∫ t in (1 : ℝ)..M, g t := by
      have hreal :
          ∑ N ∈ Finset.Ico 1 M,
              (((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
            ∫ t in (1 : ℝ)..M, g t := by
        have hpoint : ∀ i ∈ Set.Ico 1 M, ∀ t ∈ Set.Ico (i : ℝ) (i + 1 : ℕ),
            ((i : ℝ) + 1) ^ r * Real.exp (-((i : ℝ) * x)) ≤ g t := by
          intro i hi t ht
          have hiOne : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
          have hit : (i : ℝ) ≤ t := ht.1
          have htUpper : t < (i : ℝ) + 1 := by simpa using ht.2
          have hbaseLe : (i : ℝ) + 1 ≤ 2 * t := by linarith
          have hpowLe : ((i : ℝ) + 1) ^ r ≤ (2 * t) ^ r :=
            Real.rpow_le_rpow (by positivity) hbaseLe hr
          have hexpLe : Real.exp (-((i : ℝ) * x)) ≤
              Real.exp x * Real.exp (-(x * t)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith
          dsimp [g]
          rw [max_eq_left (by linarith : 0 ≤ t)]
          calc
            ((i : ℝ) + 1) ^ r * Real.exp (-((i : ℝ) * x)) ≤
                (2 * t) ^ r * Real.exp (-((i : ℝ) * x)) :=
              mul_le_mul_of_nonneg_right hpowLe (Real.exp_pos _).le
            _ ≤ (2 * t) ^ r * (Real.exp x * Real.exp (-(x * t))) :=
              mul_le_mul_of_nonneg_left hexpLe
                (Real.rpow_nonneg (by linarith : 0 ≤ 2 * t) r)
            _ = Real.exp x * 2 ^ r * (t ^ r * Real.exp (-(x * t))) := by
              rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ t)]
              ring
        have hint : IntegrableOn g (Set.Ico ((1 : ℕ) : ℝ) (M : ℝ)) := hg.mono_set (by
            intro t ht
            have htOne : (1 : ℝ) ≤ t := by exact_mod_cast ht.1
            exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) htOne)
        simpa only [Nat.cast_one] using
          (sum_Ico_le_integral_of_le
            (f := fun t : ℝ => (t + 1) ^ r * Real.exp (-(t * x)))
            (g := g) hMone hpoint hint)
      simpa [f] using hreal
    have hintegralLe : (∫ t in (1 : ℝ)..M, g t) ≤
        Real.exp x * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hMone)]
      calc
        (∫ t in Ioc (1 : ℝ) M, g t) ≤ ∫ t in Ioi 0, g t := by
          apply setIntegral_mono_set hg
          · filter_upwards with t
            exact hgNonneg t
          · filter_upwards with t ht
            exact lt_trans (by norm_num : (0 : ℝ) < 1) ht.1
        _ = Real.exp x * 2 ^ r *
            ((1 / x) ^ (r + 1) * Real.Gamma (r + 1)) := by
          rw [integral_const_mul]
          have hIntEq :
              (∫ t in Set.Ioi 0, (max t 0) ^ r * Real.exp (-(x * t))) =
                ∫ t in Set.Ioi 0, t ^ r * Real.exp (-(x * t)) := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            change 0 < t at ht
            simp only [max_eq_left ht.le]
          rw [hIntEq]
          have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
            (a := r + 1) (r := x) (by linarith) hx
          have hgamma' :
              (∫ t in Set.Ioi 0, t ^ r * Real.exp (-(x * t))) =
                (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
            simpa [one_div] using hgamma
          exact congrArg (fun y : ℝ => Real.exp x * 2 ^ r * y) hgamma'
        _ = _ := by ring
    linarith
  have hfNonneg : ∀ N : ℕ, 0 ≤ f N := by
    intro N
    dsimp [f]
    positivity
  have hsum : Summable f := summable_of_sum_range_le hfNonneg hfinite
  constructor
  · simpa [f] using hsum
  · apply Real.tsum_le_of_sum_range_le
    · exact hfNonneg
    · exact hfinite

/-- One-sided `N^(1+o(1))` cancellation in the cumulative additive Möbius triangle. -/
def MobiusAdditiveTriangleSubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (mobiusAdditiveTriangle N).re ≤ C * ((N : ℝ) + 1) ^ (1 + ε)

/-- Explicit Gamma constant for the subpower Abel estimate at exponent `ε`. -/
def mobiusAdditiveTriangleSubpowerAbelConstant (ε : ℝ) : ℝ :=
  1 + Real.exp 1 * 2 ^ (1 + ε) * Real.Gamma (2 + ε)

theorem mobiusAdditiveTriangleSubpowerAbelConstant_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ mobiusAdditiveTriangleSubpowerAbelConstant ε := by
  dsimp [mobiusAdditiveTriangleSubpowerAbelConstant]
  have hgamma := (Real.Gamma_pos_of_pos (by linarith : 0 < 2 + ε)).le
  positivity

/-- A one-sided `N^(1+ε)` triangle estimate gives the square bound of exponent `1+ε`. -/
theorem norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleSubpowerUpperBound
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsource : ∀ N : ℕ, (mobiusAdditiveTriangle N).re ≤
      C * ((N : ℝ) + 1) ^ (1 + ε))
    {x : ℝ} (hx : 0 < x) (hxOne : x ≤ 1) :
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      C * mobiusAdditiveTriangleSubpowerAbelConstant ε * x ^ (-(1 + ε)) := by
  let r : ℝ := 1 + ε
  let b : ℕ → ℝ := fun N => C * ((N : ℝ) + 1) ^ r
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le hr hx
  have hb : Summable (fun N : ℕ => b N * Real.exp (-((N : ℝ) * x))) := by
    have hmul := hmoment.1.mul_left C
    simpa only [b, mul_assoc] using! hmul
  have hsquare :=
    norm_sq_mobiusDiscreteLaplaceTransform_le_one_sub_exp_mul_tsum_of_triangleUpper
      b (by simpa only [b, r] using hsource) hx hb
  have hgamma : 0 ≤ Real.Gamma (r + 1) :=
    (Real.Gamma_pos_of_pos (by dsimp [r]; linarith)).le
  have hX : 1 ≤ (1 / x) ^ (r + 1) := by
    apply Real.one_le_rpow
    · exact (one_le_div hx).2 hxOne
    · linarith
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hxOne
  have hmomentCoarse :
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
        mobiusAdditiveTriangleSubpowerAbelConstant ε * (1 / x) ^ (r + 1) := by
    calc
      (∑' N : ℕ, ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x))) ≤
          1 + Real.exp x * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) :=
        hmoment.2
      _ ≤ 1 + Real.exp 1 * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
        have hfactor : 0 ≤ 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hexp hfactor]
      _ ≤ (1 + Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
          (1 / x) ^ (r + 1) := by
        calc
          1 + Real.exp 1 * 2 ^ r * (1 / x) ^ (r + 1) * Real.Gamma (r + 1) =
              1 + (Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
                (1 / x) ^ (r + 1) := by ring
          _ ≤ (1 / x) ^ (r + 1) +
              (Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
                (1 / x) ^ (r + 1) := by linarith
          _ = (1 + Real.exp 1 * 2 ^ r * Real.Gamma (r + 1)) *
              (1 / x) ^ (r + 1) := by ring
      _ = mobiusAdditiveTriangleSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1) := by
        dsimp [mobiusAdditiveTriangleSubpowerAbelConstant, r]
        ring
  have htsum :
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) ≤
        C * (mobiusAdditiveTriangleSubpowerAbelConstant ε * (1 / x) ^ (r + 1)) := by
    calc
      (∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x))) =
          C * ∑' N : ℕ,
            ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * x)) := by
        rw [← hmoment.1.tsum_mul_left C]
        apply tsum_congr
        intro N
        dsimp [b]
        ring
      _ ≤ C * (mobiusAdditiveTriangleSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1)) := mul_le_mul_of_nonneg_left hmomentCoarse hC
  have honeSub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  have htsumNonneg : 0 ≤ ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) := by
    apply tsum_nonneg
    intro N
    dsimp [b]
    positivity
  have hraw : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      x * (C * (mobiusAdditiveTriangleSubpowerAbelConstant ε *
        (1 / x) ^ (r + 1))) := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
          (1 - Real.exp (-x)) * ∑' N : ℕ,
            b N * Real.exp (-((N : ℝ) * x)) := hsquare
      _ ≤ x * ∑' N : ℕ, b N * Real.exp (-((N : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right honeSub htsumNonneg
      _ ≤ x * (C * (mobiusAdditiveTriangleSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := mul_le_mul_of_nonneg_left htsum hx.le
  have hInvPow : (1 / x) ^ (r + 1) = x ^ (-(r + 1)) := by
    rw [one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  have hxMul : x * x ^ (-(r + 1)) = x ^ (-r) := by
    calc
      x * x ^ (-(r + 1)) = x ^ (1 : ℝ) * x ^ (-(r + 1)) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(r + 1))) := (Real.rpow_add hx _ _).symm
      _ = x ^ (-r) := by congr 1; ring_nf
  calc
    ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
        x * (C * (mobiusAdditiveTriangleSubpowerAbelConstant ε *
          (1 / x) ^ (r + 1))) := hraw
    _ = C * mobiusAdditiveTriangleSubpowerAbelConstant ε *
        (x * x ^ (-(r + 1))) := by rw [hInvPow]; ring
    _ = C * mobiusAdditiveTriangleSubpowerAbelConstant ε * x ^ (-r) := by
      rw [hxMul]
    _ = C * mobiusAdditiveTriangleSubpowerAbelConstant ε * x ^ (-(1 + ε)) := by
      rfl

/-- **Square roots of a subpower bound give strict half-power decay.**  If the squared discrete
Laplace transform is dominated by `S · x^(-2b)` on `(0,1]` with `S ≥ 0`, the transform itself is
`O(x^(-b))` at `0⁺`.  The constant is inflated to `S + 1`, which is ≥ `√S` because `S ≤ (S+1)²`. -/
theorem isBigO_mobiusDiscreteLaplaceTransform_of_norm_sq_le
    {b S : ℝ} (hS : 0 ≤ S)
    (hsq : ∀ ⦃x : ℝ⦄, 0 < x → x ≤ 1 →
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤ S * x ^ (-(2 * b))) :
    mobiusDiscreteLaplaceTransform =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  let D : ℝ := S + 1
  rw [isBigO_iff]
  refine ⟨D, ?_⟩
  have hOneNhds : ∀ᶠ x : ℝ in nhds 0, x < 1 := Iio_mem_nhds (by norm_num)
  have hOne : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), x < 1 :=
    Filter.Eventually.filter_mono inf_le_left hOneNhds
  filter_upwards [self_mem_nhdsWithin, hOne] with x hx hxOne
  change 0 < x at hx
  change x < 1 at hxOne
  have hsqx := hsq hx hxOne.le
  have hrpowSq : (x ^ (-b)) ^ 2 = x ^ (-(2 * b)) := by
    calc
      (x ^ (-b)) ^ 2 = (x ^ (-b)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (x ^ (-b)) 2).symm
      _ = x ^ ((-b) * 2) := (Real.rpow_mul hx.le (-b) 2).symm
      _ = x ^ (-(2 * b)) := by
        have hExp : (-b) * 2 = -(2 * b) := by ring
        rw [hExp]
  rw [← hrpowSq] at hsqx
  have hSle : S ≤ D ^ 2 := by
    dsimp [D]
    nlinarith [sq_nonneg S]
  have hpowPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx _
  have htargetSq : ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤
      (D * x ^ (-b)) ^ 2 := by
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ^ 2 ≤ S * (x ^ (-b)) ^ 2 := hsqx
      _ ≤ D ^ 2 * (x ^ (-b)) ^ 2 :=
        mul_le_mul_of_nonneg_right hSle (sq_nonneg _)
      _ = (D * x ^ (-b)) ^ 2 := by ring
  have hnorm := norm_nonneg (mobiusDiscreteLaplaceTransform x)
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hright : 0 ≤ D * x ^ (-b) := mul_nonneg hD hpowPos.le
  rw [Real.norm_eq_abs, abs_of_pos hpowPos]
  nlinarith


/-- Every one-sided additive-triangle subpower estimate gives every strict half-power
Möbius--Laplace estimate. -/
theorem mobiusAdditiveTriangleSubpowerUpperBound_implies_allStrictHalfPowerDecay
    (hupper : MobiusAdditiveTriangleSubpowerUpperBound) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  have hε : (0 : ℝ) < 2 * b - 1 := by linarith
  obtain ⟨C, hC, hsource⟩ := hupper (2 * b - 1) hε
  refine isBigO_mobiusDiscreteLaplaceTransform_of_norm_sq_le
    (mul_nonneg hC (mobiusAdditiveTriangleSubpowerAbelConstant_nonneg hε)) ?_
  intro x hx hxOne
  have hbound := norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleSubpowerUpperBound hε hC hsource hx hxOne
  rwa [show -(1 + (2 * b - 1)) = -(2 * b) by ring] at hbound

/-- **Subpower additive-triangle criterion for RH.** A one-sided `N^(1+o(1))` upper estimate
for the cumulative additive Möbius triangle implies the Riemann hypothesis. -/
theorem mobiusAdditiveTriangleSubpowerUpperBound_implies_riemannHypothesis
    (hupper : MobiusAdditiveTriangleSubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusAdditiveTriangleSubpowerUpperBound_implies_allStrictHalfPowerDecay hupper)

end

end RHTower
