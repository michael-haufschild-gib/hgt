/-
# Factoring out an isolated zero of an entire function

An entire function whose only zero is a zero of order `d` at `c` factors globally as
`(z − c)^d · g` with `g` entire and nowhere zero.  Together with the logarithmic-derivative
residue this is the argument principle for a single zero.

The factorization is analytic division: `(z − c)^d` divides `f` in the ring of entire functions
because its divisor is dominated pointwise by that of `f`, and the quotient is nonvanishing
because the order at `c` is exactly `d`.

Main results:
* `analyticOrderAt_sub_pow_self`, `analyticOrderAt_sub_pow_of_ne` — the divisor of `(z − c)^d`.
* `exists_entire_factor_of_analyticOrder` — the factorization, needing only the order at `c`.
* `exists_entire_factor_of_analyticOrderAt` — with `g` nowhere zero, when `c` is the only zero.
* `circleIntegral_logDeriv_eq_analyticOrder`, `circleIntegral_logDeriv_eq_analyticOrder_local` —
  **the argument principle for a single zero**, globally and on a disc.
-/
import GaloisForLFunctions.HTGeometry.EntireBezout
import GaloisForLFunctions.HTGeometry.ArgumentPrincipleSingleZero

namespace GaloisForLFunctions.HTGeometry

open Complex

theorem analyticAt_sub_pow (c : ℂ) (d : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (w - c) ^ d) z := by
  fun_prop

/-- Away from `c` the function `(z − c)^d` does not vanish, so its order is zero. -/
theorem analyticOrderAt_sub_pow_of_ne (c : ℂ) (d : ℕ) {z : ℂ} (hz : z ≠ c) :
    analyticOrderAt (fun w : ℂ => (w - c) ^ d) z = 0 := by
  rw [(analyticAt_sub_pow c d z).analyticOrderAt_eq_zero]
  exact pow_ne_zero _ (sub_ne_zero.mpr hz)

/-- At `c` the order of `(z − c)^d` is `d`. -/
theorem analyticOrderAt_sub_pow_self (c : ℂ) (d : ℕ) :
    analyticOrderAt (fun w : ℂ => (w - c) ^ d) c = (d : ℕ∞) := by
  refine (analyticAt_sub_pow c d c).analyticOrderAt_eq_natCast.mpr ⟨fun _ => 1, by fun_prop,
    one_ne_zero, ?_⟩
  filter_upwards with w
  simp

/-- **Analytic division by `(z − c)^d`.**  An entire function of order exactly `d` at `c` is
`(z − c)^d` times an entire function nonzero at `c`. -/
theorem exists_entire_factor_of_analyticOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    {d : ℕ} (hord : analyticOrderAt f c = (d : ℕ∞)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g c ≠ 0 ∧ ∀ z, f z = (z - c) ^ d * g z := by
  have hP : Differentiable ℂ fun w : ℂ => (w - c) ^ d := by fun_prop
  have hP0 : ∃ z₀ : ℂ, (z₀ - c) ^ d ≠ 0 := ⟨c + 1, pow_ne_zero _ (by simp)⟩
  have hdiv : ∀ z, analyticOrderAt (fun w : ℂ => (w - c) ^ d) z ≤ analyticOrderAt f z := by
    intro z
    by_cases hz : z = c
    · rw [hz, analyticOrderAt_sub_pow_self, hord]
    · rw [analyticOrderAt_sub_pow_of_ne c d hz]
      simp
  obtain ⟨q, hq, hqf⟩ := exists_entire_quotient hf hP hP0 hdiv
  refine ⟨q, hq, ?_, fun z => by rw [hqf z]; ring⟩
  intro hq0
  have hqA : AnalyticAt ℂ q c := hq.differentiableOn.analyticAt Filter.univ_mem
  have hone : 1 ≤ analyticOrderAt q c := by
    rcases eq_or_ne (analyticOrderAt q c) 0 with h0 | h0
    · rw [hqA.analyticOrderAt_eq_zero] at h0
      exact absurd hq0 h0
    · exact Order.one_le_iff_ne_zero.mpr h0
  have hfmul : f = q * fun w : ℂ => (w - c) ^ d := funext hqf
  have hsum : analyticOrderAt f c = analyticOrderAt q c + (d : ℕ∞) := by
    rw [hfmul, analyticOrderAt_mul hqA (analyticAt_sub_pow c d c), analyticOrderAt_sub_pow_self]
  rw [hord] at hsum
  have hle : (1 : ℕ∞) + (d : ℕ∞) ≤ (d : ℕ∞) :=
    calc (1 : ℕ∞) + (d : ℕ∞) ≤ analyticOrderAt q c + (d : ℕ∞) := by gcongr
      _ = (d : ℕ∞) := hsum.symm
  have hcast : ((1 + d : ℕ) : ℕ∞) ≤ ((d : ℕ) : ℕ∞) := by simpa using hle
  have hnat := Nat.cast_le.mp hcast
  omega

/-- **Factoring out an isolated zero.**  An entire function with a zero of order exactly `d` at `c`
and no other zeros is `(z − c)^d` times a nowhere-vanishing entire function. -/
theorem exists_entire_factor_of_analyticOrderAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    {d : ℕ} (hord : analyticOrderAt f c = (d : ℕ∞)) (hne : ∀ z, z ≠ c → f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧ ∀ z, f z = (z - c) ^ d * g z := by
  obtain ⟨g, hg, hgc, hfg⟩ := exists_entire_factor_of_analyticOrder hf hord
  refine ⟨g, hg, fun z => ?_, hfg⟩
  by_cases hz : z = c
  · rw [hz]; exact hgc
  · intro hg0
    exact hne z hz (by rw [hfg z, hg0, mul_zero])

/-- **The argument principle for a single isolated zero.**  If the only zero of an entire `f` is a
zero of order `d` at `c`, then `∮ f′/f = 2πi·d` around any circle centred at `c`. -/
theorem circleIntegral_logDeriv_eq_analyticOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    {d : ℕ} (hord : analyticOrderAt f c = (d : ℕ∞)) (hne : ∀ z, z ≠ c → f z ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    (∮ z in C(c, r), deriv f z / f z) = 2 * Real.pi * Complex.I * (d : ℂ) := by
  obtain ⟨g, hg, hgne, hfg⟩ := exists_entire_factor_of_analyticOrderAt hf hord hne
  exact circleIntegral_logDeriv_of_factor d hg.differentiableOn (fun z _ => hgne z)
    (fun z _ => hfg z) hr (by linarith : r < r + 1)

/-- **The argument principle for a zero isolated only on a disc.** -/
theorem circleIntegral_logDeriv_eq_analyticOrder_local {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {d : ℕ} {R : ℝ} (hord : analyticOrderAt f c = (d : ℕ∞))
    (hne : ∀ z ∈ Metric.ball c R, z ≠ c → f z ≠ 0) {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∮ z in C(c, r), deriv f z / f z) = 2 * Real.pi * Complex.I * (d : ℂ) := by
  obtain ⟨g, hg, hgc, hfg⟩ := exists_entire_factor_of_analyticOrder hf hord
  refine circleIntegral_logDeriv_of_factor d hg.differentiableOn (fun z hz => ?_)
    (fun z _ => hfg z) hr hrR
  by_cases hzc : z = c
  · rw [hzc]; exact hgc
  · intro hg0
    exact hne z hz hzc (by rw [hfg z, hg0, mul_zero])

end GaloisForLFunctions.HTGeometry
