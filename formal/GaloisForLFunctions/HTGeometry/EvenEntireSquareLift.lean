import Mathlib

/-!
# An even entire function is an entire function of `z²`

For an even entire `f` set `evenSquareLift f (y) = Σ_k f^{(2k)}(0)/(2k)! · y^k`.  The Taylor series of
`f` has infinite radius, so this series converges absolutely for every `y`.  It defines an entire
function (`differentiable_evenSquareLift`) with `evenSquareLift f (z²) = f z` (`evenSquareLift_sq`), because the odd
Taylor coefficients of an even function vanish.
-/

open Complex Filter Topology
open scoped Nat NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The even Taylor coefficients `f^{(2k)}(0)/(2k)!`. -/
def evenSquareCoeff (f : ℂ → ℂ) (k : ℕ) : ℂ := iteratedDeriv (2 * k) f 0 / ((2 * k) ! : ℂ)

/-- The square-root lift `y ↦ Σ_k f^{(2k)}(0)/(2k)! · y^k`. -/
def evenSquareLift (f : ℂ → ℂ) (y : ℂ) : ℂ := ∑' k : ℕ, evenSquareCoeff f k * y ^ k

/-- The Taylor series of an entire function has infinite radius of convergence. -/
theorem radius_ofScalars_taylor_eq_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f 0 / (n ! : ℂ))).radius = ⊤ := by
  have h1 := (hf.analyticAt 0).hasFPowerSeriesAt
  have h2 := hf.hasFPowerSeriesOnBall 0 (R := 1) one_pos
  rw [h1.eq_formalMultilinearSeries h2.hasFPowerSeriesAt]
  exact top_le_iff.mp h2.r_le

/-- Absolute summability of the Taylor series of an entire function at every radius. -/
theorem summable_norm_taylor_mul_pow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun n => ‖iteratedDeriv n f 0 / (n ! : ℂ)‖ * r ^ n) := by
  have h := FormalMultilinearSeries.summable_norm_mul_pow
    (FormalMultilinearSeries.ofScalars ℂ (fun n => iteratedDeriv n f 0 / (n ! : ℂ)))
    (r := ⟨r, hr⟩) (by rw [radius_ofScalars_taylor_eq_top hf]; exact ENNReal.coe_lt_top)
  refine h.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  rfl

/-- Odd Taylor coefficients of an even function vanish. -/
theorem iteratedDeriv_odd_eq_zero_of_even {f : ℂ → ℂ} (heven : ∀ z, f (-z) = f z) (m : ℕ) :
    iteratedDeriv (2 * m + 1) f 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * m + 1) f 0
  have e : (fun z => f (-z)) = f := funext heven
  rw [e, neg_zero, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul] at h
  linear_combination (1 / 2 : ℂ) * h

theorem summable_norm_evenSquareCoeff_mul_pow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ)
    (hr : 0 ≤ r) : Summable (fun k => ‖evenSquareCoeff f k‖ * r ^ k) := by
  have h := summable_norm_taylor_mul_pow hf (Real.sqrt r) (Real.sqrt_nonneg r)
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  refine (h.comp_injective hinj).congr fun k => ?_
  simp only [Function.comp_apply, evenSquareCoeff, pow_mul, Real.sq_sqrt hr]

/-- The lift is the sum of a power series of infinite radius. -/
theorem hasFPowerSeriesOnBall_evenSquareLift {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    HasFPowerSeriesOnBall (evenSquareLift f)
      (FormalMultilinearSeries.ofScalars ℂ (evenSquareCoeff f)) 0 ⊤ := by
  set p := FormalMultilinearSeries.ofScalars ℂ (evenSquareCoeff f) with hp
  have hrad : p.radius = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun t => ?_
    refine p.le_radius_of_summable_norm ?_
    refine (summable_norm_evenSquareCoeff_mul_pow hf t t.coe_nonneg).congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
  have h := p.hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  rw [hrad] at h
  have hsum : p.sum = evenSquareLift f := by
    funext y
    rw [FormalMultilinearSeries.sum, evenSquareLift]
    exact tsum_congr fun n => by
      rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
      simp [smul_eq_mul, mul_comm]
  rw [hsum] at h
  exact h

/-- **The square-root lift of an entire function is entire.** -/
theorem differentiable_evenSquareLift {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (evenSquareLift f) := by
  have h := hasFPowerSeriesOnBall_evenSquareLift hf
  intro y
  have : AnalyticAt ℂ (evenSquareLift f) y :=
    h.analyticAt_of_mem (by simp)
  exact this.differentiableAt

/-- **`evenSquareLift f (z²) = f z` for even entire `f`.** -/
theorem evenSquareLift_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f) (heven : ∀ z, f (-z) = f z) (z : ℂ) :
    evenSquareLift f (z ^ 2) = f z := by
  have htaylor := Complex.hasSum_taylorSeries_of_entire hf 0 z
  simp only [sub_zero, smul_eq_mul] at htaylor
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      ((n ! : ℂ))⁻¹ * (z ^ n * iteratedDeriv n f 0) = 0 := by
    intro n hn
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact absurd ⟨m, rfl⟩ hn
    · rw [iteratedDeriv_odd_eq_zero_of_even heven, mul_zero, mul_zero]
  have heven_sum := (hinj.hasSum_iff hzero).mpr htaylor
  rw [evenSquareLift, ← heven_sum.tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [Function.comp_apply, evenSquareCoeff, pow_mul]
  ring

end

end GaloisForLFunctions.HTGeometry
