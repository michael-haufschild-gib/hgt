import GaloisForLFunctions.RHTower.WeilBoundaryFractionalCountingTwin
import GaloisForLFunctions.RHTower.WeilFractionalTwoSidedRigidity

/-!
# Weil-positive systems with near-integer atomic spectrum

Let `lam` be full-cone Weil-positive whose boundary measure `μ_lam` is purely atomic:
`μ_lam = Σ_j c_j (δ_{t_j} + δ_{−t_j})` with distinct ordinates `t_j ≥ 1`, `t_j → ∞`, and real
masses `c_j ≥ 0` (in the sense of the Poisson representation of the Weil function).

**Theorem** (`vonMangoldt_and_riemannHypothesis_of_near_integer_atoms`).  If the masses are integers
up to a total deviation of power growth less than one,

`Σ_{t_j < y} |c_j − round(c_j)| = O(y^α)`,  `α < 1`,

then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.

This is stated in the Weil-cone language and needs no producer: no continuity of boundary values,
no growth premise.  With `c_j ∈ ℕ` it is the atomic case of integer-counting rigidity
(`vonMangoldt_and_riemannHypothesis_of_integer_counting`).  The masses may deviate from integers
at infinitely many ordinates, with infinite total deviation.

**Proof.**  The Poisson representation turns the Weil function into the atomic Herglotz series
with real masses (`weilFunction_eq_atomicPairSeries`).  Every Weil-positive system has
absolutely convergent Dirichlet series on `Re s > 1`
(`WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull`).  The two-sided fractional-mass
rigidity theorem (`AbelianTwist.fractional_two_sided_power_growth_rigidity`) then applies, with no
integer part.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity AbelianTwist FractionalMassRigidity FractionalMassTailRigidity

/-- The atomic Herglotz series with masses `π c_j` is the real-mass series `Σ c_j 2w/(w² + t_j²)`,
`w = s − ½`. -/
theorem atomicPairSeries_pi_mul_eq (c t : ℕ → ℝ) (s : ℂ) :
    atomicPairSeries (fun j => Real.pi * c j) t s =
      ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (t k : ℂ) ^ 2)) := by
  unfold atomicPairSeries
  rw [← tsum_mul_left]
  congr 1
  funext k
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

theorem atomicPairSeries_zero (t : ℕ → ℝ) (s : ℂ) :
    atomicPairSeries (fun _ => Real.pi * ((0 : ℕ) : ℝ)) t s = 0 := by
  unfold atomicPairSeries
  simp

/-- **Near-integer atomic spectra force `Λ` and RH.**  A full-cone Weil-positive system whose
boundary measure is `Σ_j c_j(δ_{t_j} + δ_{−t_j})`, with distinct `t_j ≥ 1`, `t_j → ∞`, `c_j ≥ 0`,
and `Σ_{t_j < y}|c_j − round(c_j)| ≤ K y^α` for some `α < 1`, is `Λ`, and RH holds. -/
theorem vonMangoldt_and_riemannHypothesis_of_near_integer_atoms {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (hinj : Function.Injective t) (htt : Tendsto t atTop atTop)
    (hsum : Summable fun j => c j / t j ^ 2)
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      ∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y →
      phaseSum (fun j => |c j - round (c j)|) t y ≤ K * y ^ α) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hid0 := weilFunction_eq_atomicPairSeries hW hc hone hsum hrep
  have hfun : (fun n => if 2 ≤ n then (lam n : ℂ) else 0) = lamC lam := by
    funext n
    rw [lamC]
    split_ifs <;> simp
  have hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * ((fun _ => 0 : ℕ → ℕ) j : ℝ)) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (t k : ℂ) ^ 2)) := by
    intro s hs
    rw [atomicPairSeries_zero, zero_add, ← atomicPairSeries_pi_mul_eq, ← hid0 s hs, weilFunction,
      zetaArchimedeanDatum, hfun]
  exact fractional_two_sided_power_growth_rigidity (m := fun _ => 0) hone
    (by simp) hc hone htt hinj hsum hgrowth
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hid

end RHTower.WeilSpectral
