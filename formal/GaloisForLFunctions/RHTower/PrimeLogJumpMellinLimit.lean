import GaloisForLFunctions.RHTower.PrimeLogJumpMellinAsymptotic
import GaloisForLFunctions.HTGeometry.PairPhaseClock

/-!
# The two boundary phase channels are the two clock limits

Along a clock steering the endpoint phases to `(sin (κ A), sin (κ B)) → (c_A, c_B)`, the first
Mellin boundary trace of the jump packet converges, locally in `s`, to

```text
B^{-s} c_B − A^{-s} c_A − (c_B − c_A) H(s).
```

Unique factorization makes `A / B` irrational for a two-prime shell, so the two source-defined
clocks `(1, 0)` and `(0, 1)` exist, and their limits are exactly the two boundary phase channels
`F_A = H − A^{-s}` and `F_B = B^{-s} − H`.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter
open scoped Topology

variable {A B : ℝ}

/-- **The clock limit of the first Mellin boundary trace.** -/
theorem tendsto_jumpMellin_clock (hA : 0 < A) (hAB : A < B) {κ : ℕ → ℝ}
    (hκ : Tendsto κ atTop atTop) {cA cB : ℝ}
    (hlimA : Tendsto (fun j => Real.sin (κ j * A)) atTop (𝓝 cA))
    (hlimB : Tendsto (fun j => Real.sin (κ j * B)) atTop (𝓝 cB)) (s : ℂ) :
    Tendsto (fun j => ((κ j : ℝ) : ℂ) * jumpMellin A B (κ j) s) atTop
      (𝓝 ((B : ℂ) ^ (-s) * ((cB : ℝ) : ℂ) - (A : ℂ) ^ (-s) * ((cA : ℝ) : ℂ)
        - ((cB - cA : ℝ) : ℂ) * shellAverage A B s)) := by
  have hcastA : Tendsto (fun j => ((Real.sin (κ j * A) : ℝ) : ℂ)) atTop (𝓝 ((cA : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto cA).comp hlimA
  have hcastB : Tendsto (fun j => ((Real.sin (κ j * B) : ℝ) : ℂ)) atTop (𝓝 ((cB : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto cB).comp hlimB
  have hcastD : Tendsto (fun j => ((Real.sin (κ j * B) - Real.sin (κ j * A) : ℝ) : ℂ)) atTop
      (𝓝 ((cB - cA : ℝ) : ℂ)) := by
    have : Tendsto (fun j => Real.sin (κ j * B) - Real.sin (κ j * A)) atTop (𝓝 (cB - cA)) :=
      hlimB.sub hlimA
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hres : Tendsto
      (fun j : ℕ => s * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ j * x) : ℝ) : ℂ))
      atTop (𝓝 0) := (tendsto_jumpMellin_residual hA hAB s).comp hκ
  have hmain : Tendsto (fun j : ℕ =>
      (B : ℂ) ^ (-s) * ((Real.sin (κ j * B) : ℝ) : ℂ)
        - (A : ℂ) ^ (-s) * ((Real.sin (κ j * A) : ℝ) : ℂ)
        - ((Real.sin (κ j * B) - Real.sin (κ j * A) : ℝ) : ℂ) * shellAverage A B s
        + s * ∫ x in A..B, (x : ℂ) ^ (-s - 1) * ((Real.sin (κ j * x) : ℝ) : ℂ)) atTop
      (𝓝 ((B : ℂ) ^ (-s) * ((cB : ℝ) : ℂ) - (A : ℂ) ^ (-s) * ((cA : ℝ) : ℂ)
        - ((cB - cA : ℝ) : ℂ) * shellAverage A B s)) := by
    simpa using
      (((hcastB.const_mul ((B : ℂ) ^ (-s))).sub (hcastA.const_mul ((A : ℂ) ^ (-s)))).sub
        (hcastD.mul_const (shellAverage A B s))).add hres
  refine hmain.congr' ?_
  filter_upwards [hκ.eventually_gt_atTop 0] with j hj
  exact (jumpMellin_trace hA hAB (ne_of_gt hj) s).symm

/-- **`(18)`, `(20)`.**  The first source-defined clock: the trace converges to the first boundary
phase channel `F_A = H − A^{-s}`. -/
theorem exists_clock_tendsto_channelA (hA : 0 < A) (hAB : A < B)
    (hirr : Irrational (A / B)) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      Tendsto (fun j => Real.sin (κ j * A)) atTop (𝓝 1) ∧
      Tendsto (fun j => Real.sin (κ j * B)) atTop (𝓝 0) ∧
      ∀ s : ℂ, Tendsto (fun j => ((κ j : ℝ) : ℂ) * jumpMellin A B (κ j) s) atTop
        (𝓝 (channelA A B s)) := by
  have hB : B ≠ 0 := ne_of_gt (hA.trans hAB)
  obtain ⟨κ, hκ, hsa, hsb⟩ :=
    HTGeometry.exists_clock_seq hB hirr (Real.pi / 2) 0
  rw [Real.sin_pi_div_two] at hsa
  rw [Real.sin_zero] at hsb
  refine ⟨κ, hκ, hsa, hsb, fun s => ?_⟩
  have h := tendsto_jumpMellin_clock hA hAB hκ hsa hsb s
  convert h using 2
  rw [channelA]
  push_cast
  ring

/-- **`(19)`, `(21)`.**  The second source-defined clock: the trace converges to the second boundary
phase channel `F_B = B^{-s} − H`. -/
theorem exists_clock_tendsto_channelB (hA : 0 < A) (hAB : A < B)
    (hirr : Irrational (A / B)) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      Tendsto (fun j => Real.sin (κ j * A)) atTop (𝓝 0) ∧
      Tendsto (fun j => Real.sin (κ j * B)) atTop (𝓝 1) ∧
      ∀ s : ℂ, Tendsto (fun j => ((κ j : ℝ) : ℂ) * jumpMellin A B (κ j) s) atTop
        (𝓝 (channelB A B s)) := by
  have hB : B ≠ 0 := ne_of_gt (hA.trans hAB)
  obtain ⟨κ, hκ, hsa, hsb⟩ :=
    HTGeometry.exists_clock_seq hB hirr 0 (Real.pi / 2)
  rw [Real.sin_zero] at hsa
  rw [Real.sin_pi_div_two] at hsb
  refine ⟨κ, hκ, hsa, hsb, fun s => ?_⟩
  have h := tendsto_jumpMellin_clock hA hAB hκ hsa hsb s
  convert h using 2
  rw [channelB]
  push_cast
  ring

end GaloisForLFunctions.RHTower
