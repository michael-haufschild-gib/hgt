import GaloisForLFunctions.HTGeometry.WeightedMonicQuadraticHalfWindow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A reverse Gram bound for decreasing half-line densities

The sharp flat-window monic-quadratic norm has a nonnegative cumulative
gap. Integration by parts transfers that gap to every differentiable
decreasing density, giving a relative residual floor rather than a floor
depending on one selected window.
-/

open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private def monicQuadraticCumulativeGap (α β x : ℝ) : ℝ :=
  x ^ (11 : ℕ) / 11 + (2 * α / 9) * x ^ (9 : ℕ) +
    ((α ^ (2 : ℕ) + 2 * β) / 7) * x ^ (7 : ℕ) +
    (2 * α * β / 5) * x ^ (5 : ℕ) +
    (β ^ (2 : ℕ) / 3) * x ^ (3 : ℕ) -
    (64 / 43659 : ℝ) * x ^ (11 : ℕ)

private theorem monicQuadraticCumulativeGap_nonneg
    (α β x : ℝ) (hx : 0 ≤ x) :
    0 ≤ monicQuadraticCumulativeGap α β x := by
  let A : ℝ := α + (10 / 9) * x ^ (2 : ℕ)
  let B : ℝ := β - (5 / 21) * x ^ (4 : ℕ)
  have hid : monicQuadraticCumulativeGap α β x =
      (4 / 175 : ℝ) * A ^ (2 : ℕ) * x ^ (7 : ℕ) +
      (x ^ (3 : ℕ) / 3) *
        (B + (3 / 5 : ℝ) * A * x ^ (2 : ℕ)) ^ (2 : ℕ) := by
    dsimp [monicQuadraticCumulativeGap, A, B]
    ring
  rw [hid]
  positivity

private theorem hasDerivAt_monicQuadraticCumulativeGap
    (α β x : ℝ) :
    HasDerivAt (monicQuadraticCumulativeGap α β)
      (x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) -
        (64 / 3969 : ℝ) * x ^ (10 : ℕ)) x := by
  have h := (((((hasDerivAt_pow 11 x).div_const (11 : ℝ)).add
      ((hasDerivAt_pow 9 x).const_mul (2 * α / 9))).add
      ((hasDerivAt_pow 7 x).const_mul ((α ^ (2 : ℕ) + 2 * β) / 7))).add
      ((hasDerivAt_pow 5 x).const_mul (2 * α * β / 5))).add
      ((hasDerivAt_pow 3 x).const_mul (β ^ (2 : ℕ) / 3)) |>.sub
      ((hasDerivAt_pow 11 x).const_mul (64 / 43659 : ℝ))
  have hf : monicQuadraticCumulativeGap α β =
      (((((fun t : ℝ => t ^ (11 : ℕ) / 11) +
          (fun t => (2 * α / 9) * t ^ (9 : ℕ))) +
          (fun t => ((α ^ (2 : ℕ) + 2 * β) / 7) * t ^ (7 : ℕ))) +
          (fun t => (2 * α * β / 5) * t ^ (5 : ℕ))) +
          (fun t => (β ^ (2 : ℕ) / 3) * t ^ (3 : ℕ))) -
          (fun t => (64 / 43659 : ℝ) * t ^ (11 : ℕ)) := by
    funext t
    simp [monicQuadraticCumulativeGap, Pi.add_apply, Pi.sub_apply]
  rw [← hf] at h
  refine h.congr_deriv ?_
  norm_num
  ring

/-- Sharp relative quadratic residual floor on a finite interval for a
nonnegative decreasing differentiable density. The coefficient `64/3969`
is attained by a constant density. -/
theorem weighted_monic_quadratic_antitone_floor_interval
    (ρ : ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hρ' : Continuous (deriv ρ))
    (R α β : ℝ) (hR : 0 ≤ R)
    (hρR : 0 ≤ ρ R)
    (hder : ∀ x ∈ Set.Ioc (0 : ℝ) R, deriv ρ x ≤ 0) :
    (64 / 3969 : ℝ) *
      (∫ x : ℝ in 0..R, x ^ (10 : ℕ) * ρ x) ≤
      ∫ x : ℝ in 0..R,
        x ^ (2 : ℕ) *
          (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) * ρ x := by
  let H : ℝ → ℝ := monicQuadraticCumulativeGap α β
  let g : ℝ → ℝ := fun x =>
    x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) -
      (64 / 3969 : ℝ) * x ^ (10 : ℕ)
  have hHder (x : ℝ) : HasDerivAt H (g x) x := by
    exact hasDerivAt_monicQuadraticCumulativeGap α β x
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hρint : IntervalIntegrable (deriv ρ) volume 0 R := hρ'.intervalIntegrable _ _
  have hgint : IntervalIntegrable g volume 0 R := hgcont.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := ρ) (u' := deriv ρ) (v := H) (v' := g)
    (fun x _ => (hρ x).hasDerivAt) (fun x _ => hHder x) hρint hgint
  have hHzero : H 0 = 0 := by norm_num [H, monicQuadraticCumulativeGap]
  have hend : 0 ≤ ρ R * H R :=
    mul_nonneg hρR (monicQuadraticCumulativeGap_nonneg α β R hR)
  have hneg : ∫ x : ℝ in 0..R, deriv ρ x * H x ≤ 0 := by
    have hnonneg : 0 ≤ ∫ x : ℝ in 0..R, -(deriv ρ x * H x) := by
      apply intervalIntegral.integral_nonneg hR
      intro x hx
      by_cases hx0 : x = 0
      · subst x
        simp [H, monicQuadraticCumulativeGap]
      have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
      have hdx := hder x ⟨hxpos, hx.2⟩
      have hHx := monicQuadraticCumulativeGap_nonneg α β x hx.1
      change 0 ≤ -(deriv ρ x * H x)
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hdx hHx)
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  have hmain : 0 ≤ ∫ x : ℝ in 0..R, ρ x * g x := by
    rw [hibp, hHzero, mul_zero, sub_zero]
    linarith
  have hcρ : Continuous ρ := hρ.continuous
  have hnormint : IntervalIntegrable
      (fun x : ℝ => x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) * ρ x)
      volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htopint : IntervalIntegrable (fun x : ℝ => x ^ (10 : ℕ) * ρ x)
      volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpoint (x : ℝ) : ρ x * g x =
      x ^ (2 : ℕ) * (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) * ρ x -
        (64 / 3969 : ℝ) * (x ^ (10 : ℕ) * ρ x) := by
    dsimp [g]
    ring
  simp_rw [hpoint] at hmain
  rw [intervalIntegral.integral_sub hnormint (htopint.const_mul _),
    intervalIntegral.integral_const_mul] at hmain
  linarith

/-- The same sharp relative floor on the positive half-line. -/
theorem weighted_monic_quadratic_antitone_floor_Ioi
    (ρ : ℝ → ℝ) (hρ : Differentiable ℝ ρ)
    (hρ' : Continuous (deriv ρ))
    (hρnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ ρ x)
    (hder : ∀ x : ℝ, 0 < x → deriv ρ x ≤ 0)
    (α β : ℝ)
    (hintTop : IntegrableOn (fun x : ℝ => x ^ (10 : ℕ) * ρ x) (Set.Ioi 0))
    (hintNorm : IntegrableOn
      (fun x : ℝ => x ^ (2 : ℕ) *
        (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) * ρ x)
      (Set.Ioi 0)) :
    (64 / 3969 : ℝ) *
      (∫ x : ℝ in Set.Ioi 0, x ^ (10 : ℕ) * ρ x) ≤
      ∫ x : ℝ in Set.Ioi 0,
        x ^ (2 : ℕ) *
          (x ^ (4 : ℕ) + α * x ^ (2 : ℕ) + β) ^ (2 : ℕ) * ρ x := by
  have hleft :=
    (intervalIntegral_tendsto_integral_Ioi 0 hintTop Filter.tendsto_id).const_mul
      (64 / 3969 : ℝ)
  have hright := intervalIntegral_tendsto_integral_Ioi 0 hintNorm Filter.tendsto_id
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
  apply weighted_monic_quadratic_antitone_floor_interval ρ hρ hρ' R α β hR
  · exact hρnonneg R hR
  · intro x hx
    exact hder x hx.1

end
end GaloisForLFunctions.HTGeometry
