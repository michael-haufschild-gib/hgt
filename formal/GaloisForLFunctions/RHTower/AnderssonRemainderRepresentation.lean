import GaloisForLFunctions.RHTower.StepProfileMellinLSeries
import GaloisForLFunctions.HTGeometry.JumpProfileLevels
import GaloisForLFunctions.HTGeometry.MellinAntiderivativeStep

/-!
# The iterated Mellin representation of a remainder chain

Andersson's Theorem 1 rests on the representation

```text
∫_1^∞ q(x) x^{-s} dx + ∑_n a_n n^{-s}
      = s (s+1) ⋯ (s+j) ∫_1^∞ r_j(x) x^{-s-j-1} dx ,
```

where `r_0(x) = ∫_1^x q + ∑_{n ≤ x} a_n` and `r_{j+1} = ∫_1^x r_j`.  Both halves of the base
identity and the `j`-fold iteration are assembled here from the Fubini step, the integral form of
Abel summation, and the explicit levels of the remainder chain.
-/

noncomputable section

open MeasureTheory Set Complex GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **The base identity.**  Level `0` of the remainder chain transforms to the datum plus the
`L`-series of the arithmetic source. -/
theorem mellin_arithJumpProfile_zero {q : ℝ → ℂ} {a : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C)
    (ha : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, a m‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) (hsum : LSeriesSummable a s)
    (hq : IntegrableOn (fun t => q t * (t : ℂ) ^ (-s)) (Set.Ioi (1:ℝ))) :
    s * (∫ x in Set.Ioi (1:ℝ), arithJumpProfile q a 0 x * (x : ℂ) ^ (-s - 1))
      = (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + LSeries a s := by
  have hsplit : (∫ x in Set.Ioi (1:ℝ), arithJumpProfile q a 0 x * (x : ℂ) ^ (-s - 1))
      = (∫ x in Set.Ioi (1:ℝ), (∫ t in (1:ℝ)..x, q t) * (x : ℂ) ^ (-s - 1))
        + ∫ x in Set.Ioi (1:ℝ), (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m) * (x : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_add (integrableOn_antideriv_mellin hs hq)
      (integrableOn_complexPartialSum hC ha hs hθs)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show arithJumpProfile q a 0 x * (x : ℂ) ^ (-s - 1)
      = (∫ t in (1:ℝ)..x, q t) * (x : ℂ) ^ (-s - 1)
        + (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, a m) * (x : ℂ) ^ (-s - 1)
    rw [arithJumpProfile_zero]
    ring
  rw [hsplit, mul_add, mellin_antiderivative_step hs hq,
    mellin_complexPartialSum_eq_LSeries hC ha hs hθs hsum]

/-- **The `j`-fold iteration.** -/
theorem mellin_arithJumpProfile_iterate {q : ℝ → ℂ} (hq : Continuous q) (a : ℕ → ℂ) {s : ℂ}
    (hs : 0 < s.re)
    (hint : ∀ j : ℕ, IntegrableOn
      (fun t => arithJumpProfile q a j t * (t : ℂ) ^ (-(s + j))) (Set.Ioi (1:ℝ))) (j : ℕ) :
    (∫ x in Set.Ioi (1:ℝ), arithJumpProfile q a 0 x * (x : ℂ) ^ (-s))
      = (∏ i ∈ Finset.range j, (s + i)) *
        ∫ x in Set.Ioi (1:ℝ), arithJumpProfile q a j x * (x : ℂ) ^ (-(s + j)) :=
  mellin_iterated_step hs
    (fun j _ hx => (integral_arithJumpProfile hq a (le_of_lt hx) j).symm) hint j

/-- **The iterated Mellin representation.**  This is the analytic identity that Andersson's
Theorem 1 integrates by parts: the datum and the arithmetic `L`-series together are a rising
factorial multiple of the transform of the `j`-th remainder. -/
theorem mellin_representation_iterated {q : ℝ → ℂ} (hq : Continuous q) {a : ℕ → ℂ} {C θ : ℝ}
    (hC : 0 ≤ C) (ha : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, a m‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ}
    (hs : 0 < s.re) (hθs : θ < s.re) (hsum : LSeriesSummable a s)
    (hq0 : IntegrableOn (fun t => q t * (t : ℂ) ^ (-s)) (Set.Ioi (1:ℝ)))
    (hint : ∀ j : ℕ, IntegrableOn
      (fun t => arithJumpProfile q a j t * (t : ℂ) ^ (-(s + 1 + j))) (Set.Ioi (1:ℝ))) (j : ℕ) :
    (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + LSeries a s
      = s * (∏ i ∈ Finset.range j, (s + 1 + i)) *
        ∫ x in Set.Ioi (1:ℝ), arithJumpProfile q a j x * (x : ℂ) ^ (-(s + 1 + j)) := by
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hiter := mellin_arithJumpProfile_iterate hq a hs1 (by simpa using hint) j
  have hexp : (fun x : ℝ => arithJumpProfile q a 0 x * (x : ℂ) ^ (-s - 1))
      = fun x : ℝ => arithJumpProfile q a 0 x * (x : ℂ) ^ (-(s + 1)) := by
    funext x
    congr 2
    ring
  rw [← mellin_arithJumpProfile_zero hC ha hs hθs hsum hq0, hexp, hiter, ← mul_assoc]

end RHTower

end
