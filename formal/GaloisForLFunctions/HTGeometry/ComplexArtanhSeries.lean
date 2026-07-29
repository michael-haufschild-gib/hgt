import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# The odd power series of the complex inverse hyperbolic tangent

Subtracting the Mercator series at `z` and at `-z` kills the even powers and doubles the odd ones:

```
∑_{k} z^{2k+1}/(2k+1) = (log (1 + z) - log (1 - z)) / 2      for ‖z‖ < 1.
```

Mathlib has `Real.artanh` but no complex power series for it; `Complex.hasSum_taylorSeries_neg_log`
supplies both halves and the odd part is extracted by reindexing along `k ↦ 2k+1`.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The odd power series.**  Inside the unit disc the odd powers sum to the complex `artanh`. -/
theorem hasSum_oddPow_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / (2 * (k : ℂ) + 1))
      ((Complex.log (1 + z) - Complex.log (1 - z)) / 2) := by
  have h1 := Complex.hasSum_taylorSeries_neg_log hz
  have hz' : ‖(-z)‖ < 1 := by simpa using hz
  have h2 := Complex.hasSum_taylorSeries_neg_log hz'
  rw [show (1 : ℂ) - -z = 1 + z by ring] at h2
  have hdiff : HasSum (fun n : ℕ => z ^ n / (n : ℂ) - (-z) ^ n / (n : ℂ))
      (Complex.log (1 + z) - Complex.log (1 - z)) := by
    have hsub := h1.sub h2
    simpa only [sub_eq_add_neg, neg_neg, add_comm] using! hsub
  have hginj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    have h : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1),
      z ^ n / (n : ℂ) - (-z) ^ n / (n : ℂ) = 0 := by
    intro n hn
    have hev : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exfalso
        obtain ⟨j, hj⟩ := h
        exact hn ⟨j, by show 2 * j + 1 = n; omega⟩
    rw [hev.neg_pow]
    ring
  have hcomp := (hginj.hasSum_iff hzero).mpr hdiff
  have hterm : ∀ k : ℕ,
      (fun n : ℕ => z ^ n / (n : ℂ) - (-z) ^ n / (n : ℂ)) ((fun k : ℕ => 2 * k + 1) k)
        = 2 * (z ^ (2 * k + 1) / (2 * (k : ℂ) + 1)) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
    show z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ) - (-z) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)
      = 2 * (z ^ (2 * k + 1) / (2 * (k : ℂ) + 1))
    rw [hodd.neg_pow]
    push_cast
    ring
  have hdouble : HasSum (fun k : ℕ => 2 * (z ^ (2 * k + 1) / (2 * (k : ℂ) + 1)))
      (Complex.log (1 + z) - Complex.log (1 - z)) := by
    refine hcomp.congr_fun ?_
    intro k
    exact (hterm k).symm
  have hhalf := hdouble.div_const 2
  have heq : (fun k : ℕ => 2 * (z ^ (2 * k + 1) / (2 * (k : ℂ) + 1)) / 2)
      = fun k : ℕ => z ^ (2 * k + 1) / (2 * (k : ℂ) + 1) := by
    funext k
    ring
  rwa [heq] at hhalf

end GaloisForLFunctions.HTGeometry
