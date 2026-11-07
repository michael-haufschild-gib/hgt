import GaloisForLFunctions.PrimeTorusTheory.TheFiniteTimeBohrIsometry
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCalculusOfEulerColumns

/-!
# Certificates on the orbit

Which functions on `X = [1,∞) × 𝕋^∞` restrict to the current `base(t) − Σ_p column_p(t)` and have a sum-of-squares form with `t`-dependent coefficients? The answer depends only on how fast the
coefficients vary.

* **Pointwise in `t`** (`graph_lift`). The orbit is a graph, so every nonnegative function on it is the restriction of a single square with a coefficient depending on `t` alone. That certificate is
  tautological: it says nothing beyond the sign it certifies.
* **Frozen on a window** (`frozen_certificate_costs_size`). If a certificate is positive on a window `[T, T + L]` longer than the Kronecker time of the primes up to `y`, its base must pay the size of those
  columns up to the Fejér loss. A coefficient that is slow against the Kronecker time sees the torus, so it costs size, and a sum of squares in any form is no help.
* **Prime by prime** (`column_outer_factor`, `sum_of_squares_iff_mass_le`). Above the size curve the certificate exists and is explicit. Each column has an outer factorization
  `b − ℓ·colShape r c = |(u − v w)/(1 − r w)|²` as soon as `b ≥ ℓ r/(1 − r)`, and a prime-by-prime allocation of the base exists iff the base pays the mass.

So every nontrivial certificate past size must use coefficients varying *faster* than the Kronecker time of its primes. The current's own base is constant on a window of length `εt`, and the Kronecker
time of the primes up to `y` is `exp(c y)`. So columns up to `y ≍ log t` are paid by size, for every certificate that is slow at the scale of the base, and the first gain is past the Kronecker scale.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

open GaloisForLFunctions.ArithmeticInnerFunctionTheory (colShape colShape_den_pos)

/-- The orbit is a graph: a nonnegative function of the height alone is a square that restricts to it. -/
theorem graph_lift {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) :
    ∃ h : ℝ → ℝ, ∀ t, h t ^ 2 = f t :=
  ⟨fun t => Real.sqrt (f t), fun t => Real.sq_sqrt (hf t)⟩

/-- The norm square of `u − v w` on the unit circle. -/
theorem normSq_sub_mul {u v : ℝ} {w : ℂ} (hw : ‖w‖ = 1) :
    ‖(u : ℂ) - v * w‖ ^ 2 = u ^ 2 + v ^ 2 - 2 * u * v * w.re := by
  have hre : (w.re) ^ 2 + (w.im) ^ 2 = 1 := by
    have h := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h
    nlinarith
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_im, Complex.mul_im, add_zero, zero_sub]
  nlinarith

/-- **The column has an outer factor.** Above its maximum, a column minus the base is the square of an explicit
holomorphic function of the phase, zero-free on the disc. -/
theorem column_outer_factor {r ℓ b : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hℓ : 0 ≤ ℓ)
    (hb : ℓ * (r / (1 - r)) ≤ b) :
    ∃ u v : ℝ, 0 ≤ v ∧ v ≤ u ∧ ∀ w : ℂ, ‖w‖ = 1 →
      b - ℓ * colShape r w.re = ‖((u : ℂ) - v * w) / (1 - r * w)‖ ^ 2 := by
  have h1r : 0 < 1 - r := by linarith
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  set α : ℝ := b * (1 + r ^ 2) + ℓ * r ^ 2 with hα
  set β : ℝ := (2 * b + ℓ) * r with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hαβ : β ≤ α := by
    have h2 : ℓ * r ≤ b * (1 - r) := by
      rw [mul_div_assoc', div_le_iff₀ h1r] at hb
      exact hb
    rw [hα, hβ]
    nlinarith
  have hdisc : 0 ≤ α ^ 2 - β ^ 2 := by nlinarith
  set δ := Real.sqrt (α ^ 2 - β ^ 2) with hδ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ 2 = α ^ 2 - β ^ 2 := Real.sq_sqrt hdisc
  have hδα : δ ≤ α := by
    have hα0 : 0 ≤ α := hβ0.trans hαβ
    refine abs_le_of_sq_le_sq' ?_ hα0 |>.2
    nlinarith
  -- `u² = (α + δ)/2`, `v² = (α − δ)/2`, so `u² + v² = α` and `2uv = β`.
  refine ⟨Real.sqrt ((α + δ) / 2), Real.sqrt ((α - δ) / 2), Real.sqrt_nonneg _,
    Real.sqrt_le_sqrt (by linarith), fun w hw => ?_⟩
  have hu2 : Real.sqrt ((α + δ) / 2) ^ 2 = (α + δ) / 2 :=
    Real.sq_sqrt (by have := hβ0.trans hαβ; linarith)
  have hv2 : Real.sqrt ((α - δ) / 2) ^ 2 = (α - δ) / 2 := Real.sq_sqrt (by linarith)
  have huv : 2 * Real.sqrt ((α + δ) / 2) * Real.sqrt ((α - δ) / 2) = β := by
    have hprod : Real.sqrt ((α + δ) / 2) * Real.sqrt ((α - δ) / 2) =
        Real.sqrt ((α + δ) / 2 * ((α - δ) / 2)) :=
      (Real.sqrt_mul (by have := hβ0.trans hαβ; linarith) _).symm
    have e : (α + δ) / 2 * ((α - δ) / 2) = (β / 2) ^ 2 := by
      nlinarith [hδsq]
    rw [mul_assoc, hprod, e, Real.sqrt_sq (by positivity)]
    ring
  have hnum := normSq_sub_mul (u := Real.sqrt ((α + δ) / 2)) (v := Real.sqrt ((α - δ) / 2)) hw
  have hden := normSq_sub_mul (u := 1) (v := r) hw
  rw [norm_div, div_pow]
  have hc1 : w.re ≤ 1 := by
    have := Complex.re_le_norm w
    rwa [hw] at this
  have hdpos := colShape_den_pos hr0 hr1 hc1
  have hdenval : ‖(1 : ℂ) - r * w‖ ^ 2 = 1 - 2 * r * w.re + r ^ 2 := by
    have e : ((1 : ℝ) : ℂ) = (1 : ℂ) := Complex.ofReal_one
    rw [e] at hden
    rw [hden]
    ring
  have hsq : (α + δ) / 2 + (α - δ) / 2 - 2 * Real.sqrt ((α + δ) / 2) * Real.sqrt ((α - δ) / 2) * w.re =
      α - β * w.re := by
    rw [huv]
    ring
  rw [hnum, hdenval, hu2, hv2, hsq]
  unfold colShape
  rw [eq_div_iff hdpos.ne', sub_mul, mul_assoc ℓ, div_mul_cancel₀ _ hdpos.ne', hα, hβ]
  ring

/-- **A prime-by-prime allocation exists iff the base pays the mass.** -/
theorem sum_of_squares_iff_mass_le {ι : Type*} [Fintype ι] [Nonempty ι] (m : ι → ℝ) (B : ℝ) :
    (∃ b : ι → ℝ, (∑ i, b i = B) ∧ ∀ i, m i ≤ b i) ↔ ∑ i, m i ≤ B := by
  classical
  constructor
  · rintro ⟨b, hb, hm⟩
    rw [← hb]
    exact Finset.sum_le_sum fun i _ => hm i
  · intro hB
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨fun i => m i + if i = i₀ then B - ∑ j, m j else 0, ?_, fun i => ?_⟩
    · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i₀]
      simp
    · have : 0 ≤ if i = i₀ then B - ∑ j, m j else 0 := by
        split_ifs <;> linarith
      linarith

/-- **A frozen certificate costs size.** If `B` dominates the column sum on a window longer than the Kronecker time of the primes up to `y`, then `B` pays the mass of those primes up to the Fejér
loss, whatever certificate is used. -/
theorem frozen_certificate_costs_size {y N m : ℕ} (hyN : y ≤ N) (hm : 1 ≤ m) {a : ℕ → ℝ}
    (ha : ∀ r ∈ primesUpTo N, 0 ≤ a r) {η B T L : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) < η * L)
    (hB : ∀ t ∈ Set.Icc T (T + L), ∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r) ≤ B) :
    (m : ℝ) / (m + 1) * ∑ p ∈ primesUpTo y, a p - η * ∑ r ∈ primesUpTo N, a r ≤ B := by
  obtain ⟨t, ht, hle⟩ := exists_column_ge_of_primesUpTo hyN hm ha (fun _ => 0) hη hη1 T hL
  simp only [sub_zero] at hle
  exact hle.trans (hB t ht)

/-- **The same at the corner `−1`.** A lower bound on a window costs size as well. -/
theorem frozen_lower_certificate_costs_size {y N m : ℕ} (hyN : y ≤ N) (hm : 1 ≤ m) {a : ℕ → ℝ}
    (ha : ∀ r ∈ primesUpTo N, 0 ≤ a r) {η B T L : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hL : 2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) < η * L)
    (hB : ∀ t ∈ Set.Icc T (T + L), -B ≤ ∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r)) :
    (m : ℝ) / (m + 1) * ∑ p ∈ primesUpTo y, a p - η * ∑ r ∈ primesUpTo N, a r ≤ B := by
  obtain ⟨t, ht, hle⟩ := exists_column_ge_of_primesUpTo hyN hm ha (fun _ => Real.pi) hη hη1 T hL
  have hflip : ∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r - Real.pi) =
      -∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.cos_sub_pi]
    ring
  rw [hflip] at hle
  have := hB t ht
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
