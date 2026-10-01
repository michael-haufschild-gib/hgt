import GaloisForLFunctions.RHTower.WeilFullConeHerglotzCriticalHalfPlane
import GaloisForLFunctions.RHTower.WeilPositiveAlmostAllShortIntervals

/-!
# Short-interval consequences of full-cone Weil positivity

With `herglotzWeilPositive_of_weilPositiveFull`, the short-interval theorems proved for
Herglotz–Weil-positive systems hold on the whole full Weil cone, with no further hypothesis.

* `exists_weight_ne_zero_mem_Ioo_of_weilPositiveFull`: the support of every full-cone
  Weil-positive system meets every interval `(x, x + x^{1/2+ε})` with `x` large.
* `volume_primeGapStarts_le_of_weilPositiveFull`: a prime-supported full-cone Weil-positive
  system forces primes in all windows `(e^u, e^u(1 + X^{ε−1}))`, `u ∈ [log X, log 2X]`, outside a
  set of measure `O(X^{−ε/2})`.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower.WeilSpectral

/-- **Short intervals meet the support of every Weil-positive system.** -/
theorem exists_weight_ne_zero_mem_Ioo_of_weilPositiveFull {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∃ n : ℕ, x < n ∧ (n : ℝ) < x + x ^ (1 / 2 + ε) ∧ 2 ≤ n ∧ lam n ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := exists_weight_ne_zero_mem_Ioo_of_zetaWeilPositive
    (herglotzWeilPositive_of_weilPositiveFull hW) hε
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := hx₀ x hx
  split_ifs at h3 with hn
  · exact ⟨n, h1, h2, hn, h3⟩
  · exact absurd rfl h3

/-- **Prime-supported Weil-positive systems force primes in almost all short windows.** -/
theorem volume_primeGapStarts_le_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hsupp : ∀ n : ℕ, lam n ≠ 0 → n.Prime) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      volume {u : ℝ | u ∈ Icc (Real.log X) (Real.log (2 * X)) ∧
        ∀ p : ℕ, p.Prime → Real.exp u < p → (p : ℝ) < Real.exp u + Real.exp u * X ^ (ε - 1) →
          False}
        ≤ ENNReal.ofReal (C * X ^ (-(ε / 2))) := by
  refine volume_primeGapStarts_le_of_zetaWeilPositive (herglotzWeilPositive_of_weilPositiveFull hW)
    (fun n hn => ?_) hε hε1
  split_ifs at hn with h
  · exact hsupp n hn
  · exact absurd rfl hn

end RHTower.WeilSpectral

end
