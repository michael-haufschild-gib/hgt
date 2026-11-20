import GaloisForLFunctions.HagedornBootstrap.BesselSeries
import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.BesselSzegoCertificate

/-!
# The Cardy kernel is the corpus Bessel function

The corpus defines the modified Bessel functions by their series
`I_j(x) = Σ (x/2)^{j+2i}/(i!(j+i)!)`. The Cardy kernel of the bootstrap is its order-zero member at
`x = 4π√(αt)`: `K_α(t) = I₀(4π√(αt))`. Consequently the corpus Bessel function inherits the
bootstrap Laplace identity `2π∫₀^∞ I₀(4π√(αt)) e^{−2πβt} dt = β⁻¹e^{2πα/β}`, and the corpus
comparison `I_{m+2} ≤ I_m` bounds the higher Bessel functions by the Cardy kernel. The two corpus
definitions of `I₀`, by series and by the integral `(1/π)∫₀^π cosh(u sin θ)`, coincide.
-/

noncomputable section

open Real Set MeasureTheory

namespace GaloisForLFunctions.HagedornBootstrap

open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-- **`K_α(t) = I₀(4π√(αt))`** with the corpus Bessel series. -/
theorem cardyKernel_eq_besselI {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    cardyKernel α t = besselI 0 (4 * π * √(α * t)) := by
  have hsq : √(α * t) ^ 2 = α * t := Real.sq_sqrt (by positivity)
  have hbase : (4 * π * √(α * t) / 2) ^ 2 = 4 * π ^ 2 * α * t := by
    rw [show (4 * π * √(α * t) / 2) ^ 2 = 4 * π ^ 2 * √(α * t) ^ 2 by ring, hsq]; ring
  unfold cardyKernel besselI
  congr 1; funext i
  simp only [zero_add]
  rw [pow_mul, hbase, sq ((i.factorial : ℕ) : ℝ)]

/-- The corpus Bessel function inherits the Laplace identity of the Cardy kernel. -/
theorem laplace_besselI_zero {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    2 * π * ∫ t in Ioi 0, besselI 0 (4 * π * √(α * t)) * Real.exp (-(2 * π * β * t)) =
      β⁻¹ * Real.exp (2 * π * α / β) := by
  rw [← laplace_cardyKernel hα hβ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [cardyKernel_eq_besselI hα (mem_Ioi.mp ht).le]

/-- Every even-order corpus Bessel function at the Cardy argument lies below the Cardy kernel. -/
theorem besselI_two_mul_le_cardyKernel {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) (m : ℕ) :
    besselI (2 * m) (4 * π * √(α * t)) ≤ cardyKernel α t := by
  rw [cardyKernel_eq_besselI hα ht]
  have hx : 0 ≤ 4 * π * √(α * t) := by positivity
  induction m with
  | zero => simp
  | succ m ih =>
    calc besselI (2 * (m + 1)) (4 * π * √(α * t)) = besselI (2 * m + 2) (4 * π * √(α * t)) := by
          ring_nf
      _ ≤ besselI (2 * m) (4 * π * √(α * t)) := besselI_add_two_le (2 * m) hx
      _ ≤ besselI 0 (4 * π * √(α * t)) := ih

/-- **The two corpus `I₀` agree:** the integral representation equals the series. -/
theorem besselI0_eq_besselI_zero (u : ℝ) : RHTower.besselI0 u = besselI 0 u := by
  rw [besselI0_eq_tsum]
  unfold besselI
  congr 1; funext i
  simp only [zero_add]
  rw [sq ((i.factorial : ℕ) : ℝ)]

/-- The corpus series `I₀` is nonnegative and at least `1`, as the integral representation shows. -/
theorem one_le_besselI_zero (u : ℝ) : 1 ≤ besselI 0 u := by
  rw [← besselI0_eq_besselI_zero, besselI0_eq_tsum]
  have hs : Summable fun n : ℕ => (u / 2) ^ (2 * n) / (n.factorial : ℝ) ^ 2 := by
    have := summable_cardyTerm ((u / 2) ^ 2)
    refine this.congr fun n => ?_
    rw [pow_mul]
  have := hs.le_tsum 0 (fun n _ => by
    have : 0 ≤ (u / 2) ^ (2 * n) := by rw [pow_mul]; positivity
    positivity)
  simpa using this

end GaloisForLFunctions.HagedornBootstrap
