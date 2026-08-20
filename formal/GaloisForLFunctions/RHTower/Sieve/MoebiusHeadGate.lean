import GaloisForLFunctions.RHTower.Sieve.AffineFromHead
import GaloisForLFunctions.RHTower.Sieve.FibreWindowBridge

/-!
# The Route E gate, reduced to one mean square at one height

Combining Gallagher's dyadic split with the observation of `Sieve/AffineFromHead`, the whole
Matomäki–Radziwiłł input for the corpus's fibre normalisation becomes a **single** inequality:

```text
   ∫_{|w| ≤ T₀} ‖∑_{n ≤ ⌊√x + h⌋} μ(n) n^{-2πiw}‖² dw  ≤  B(x) ,
```

with `T₀` any height above the Gallagher cutoff.  The slope of the affine majorant is then the
trivial mean value theorem's, with its height-free term divided by `T₀`, and nothing else about the
Möbius polynomial is used.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The slope of the affine majorant produced by one head bound at height `T₀`. -/
def moebiusHeadSlope (x h T₀ : ℝ) : ℝ :=
  5 * Real.pi / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
    + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
        * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀

theorem norm_moebius_complex_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  have := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast this

theorem zero_not_mem_fibreIndex (x h : ℝ) : (0 : ℕ) ∉ fibreIndex x h := by
  intro hc
  have := mem_fibreIndex.1 hc
  omega

theorem card_fibreIndex (x h : ℝ) : (fibreIndex x h).card = ⌊Real.sqrt x + h⌋₊ := by
  rw [fibreIndex, Nat.card_Icc]
  omega

/-- **The Route E gate from a single head bound.** -/
theorem averagedMeanSquare_moebius_of_headBound {hh G T₀ B : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hdata : ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ G x ∧ G x ≤ T₀ x ∧ 0 ≤ B x
        ∧ (∫ w in Set.Icc (-(T₀ x)) (T₀ x),
            ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
              (fibreIndex x (hh x)) w‖ ^ 2) ≤ B x)
    (hlim : Filter.Tendsto (fun x : ℝ =>
        (2 * fibreWidth x (hh x) ^ 2 * (moebiusHeadSlope x (hh x) (T₀ x) * G x + B x)
          + (4 * moebiusHeadSlope x (hh x) (T₀ x) / (Real.pi ^ 2 * G x)
            + 4 * B x / (3 * Real.pi ^ 2 * G x ^ 2))) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  refine averagedMeanSquare_of_gallagherBudget (f := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
    abs_moebius_real_le_one hgrow hhx ?_ ?_ hlim
  · filter_upwards [hdata] with x hx
    linarith [hx.1]
  · filter_upwards [hdata] with x hx
    intro T hT
    have hcongr : ∀ w : ℝ,
        ‖logPoly (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ))
            (fibreIndex x (hh x)) w‖ ^ 2
          = ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
              (fibreIndex x (hh x)) w‖ ^ 2 := by
      intro w
      rw [logPoly_moebius_congr]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hcongr w]
    have hsN : ∀ n ∈ fibreIndex x (hh x), n ≤ ⌊Real.sqrt x + hh x⌋₊ :=
      fun n hn => (mem_fibreIndex.1 hn).2
    have haff := integral_Icc_normSq_logPoly_affine_of_head
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) norm_moebius_complex_le_one
      (zero_not_mem_fibreIndex x (hh x)) hsN hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 T hT
    refine haff.trans (le_of_eq ?_)
    rw [moebiusHeadSlope, card_fibreIndex]

end

end RHTower.Sieve
