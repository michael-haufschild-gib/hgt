import GaloisForLFunctions.RHTower.ArcGammaMultiplier

/-!
# The arc multiplier at the odd integers: an even-type test for the twisted-arc null family

The twisted-arc null family of the corpus has spectral density `Ξ² R` with
`R(s) = Σ_j w_j Q_j(z) Q_j(−z)`, `z = −i(s − ½)` (`arcGammaMultiplier`), and arc weights
`w_j = 4√2 · 4^j m_j/(2j)!` (`arcGammaWeight`), where `m_j = ∫ ρ(u) u^{2j} dν(u)` are the weighted
even moments of the arc measure.  The family is *even-type*, i.e. a nonnegative combination of
autocorrelations of even tests `F̂ = Ξ·p` with `p` real and even, only if `R(s) ≥ 0` for every
real `s`.  An even-type null family is the missing input for the equivalence of the Riemann
hypothesis with prime-blind positivity restricted to even tests.

At the real points `s = 2k + 1` the `k`-th factor `k + ¼ − (2k + ½)/2` of `Q_j(i(s − ½))` vanishes,
so `Q_j(z) Q_j(−z) = 0` for `j > k` and `R(2k + 1)` is a finite combination of the first moments:

* `arcGammaMultiplier_three`: `R(3) = 4√2 (m₀ − 3 m₁)`;
* `arcGammaMultiplier_five`: `R(5) = 4√2 (m₀ − 10 m₁ + (35/3) m₂)`.

In terms of the arc measure these are `4√2 ∫ ρ(u) P_{2k}(u)/P_{2k}(0) dν(u)` with the even Legendre
polynomials `P₂(u)/P₂(0) = 1 − 3u²` and `P₄(u)/P₄(0) = 1 − 10u² + (35/3)u⁴`.

* On the arc `|u| ≤ ½` the first kernel is positive (`arcKernelThree_pos`).  So `R(3) > 0`
  automatically.
* The second kernel is negative for `u² ∈ [3/20, 1/4]` (`arcKernelFive_neg`), for instance near the
  corners `u = ±½` of the arc.  So `R(5) < 0` whenever the moments come from an arc measure carried
  by `|u|² ≥ 3/20` (`arcGammaMultiplier_five_neg_of_moments`).

In particular, an arc null family is even-type only if its arc measure charges the central part
`u² < 3/20` of the arc enough to make `m₀ − 10m₁ + (35/3)m₂ ≥ 0`.
-/

open Complex

noncomputable section

namespace RHTower.WeilSpectral

/-- The product `Q_j(−i(s−½)) Q_j(i(s−½))` at `s = 2k + 1` vanishes for `j > k`. -/
theorem shiftedGammaPoly_mul_eq_zero_of_lt {k j : ℕ} (hkj : k < j) :
    shiftedGammaPoly j (-I * (((2 * k + 1 : ℕ) : ℂ) - 1 / 2)) *
        shiftedGammaPoly j (I * (((2 * k + 1 : ℕ) : ℂ) - 1 / 2)) = 0 := by
  apply mul_eq_zero_of_right
  unfold shiftedGammaPoly
  rw [Finset.prod_eq_zero_iff]
  refine ⟨k, Finset.mem_range.mpr hkj, ?_⟩
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- At `s = 2k + 1` the arc multiplier is the finite sum over `j ≤ k`. -/
theorem arcGammaMultiplier_odd_eq_sum (w : ℕ → ℝ) (k : ℕ) :
    arcGammaMultiplier w ((2 * k + 1 : ℕ) : ℂ) = ∑ j ∈ Finset.range (k + 1), (w j : ℂ) *
      (shiftedGammaPoly j (-I * (((2 * k + 1 : ℕ) : ℂ) - 1 / 2)) *
        shiftedGammaPoly j (I * (((2 * k + 1 : ℕ) : ℂ) - 1 / 2))) := by
  unfold arcGammaMultiplier
  refine tsum_eq_sum fun j hj => ?_
  have hkj : k < j := by simpa [Nat.lt_succ_iff] using hj
  rw [shiftedGammaPoly_mul_eq_zero_of_lt hkj, mul_zero]

/-- **`R(3) = 4√2 (m₀ − 3 m₁)`.** -/
theorem arcGammaMultiplier_three (m : ℕ → ℝ) :
    arcGammaMultiplier (fun j => arcGammaWeight (m j) j) 3 =
      ((4 * Real.sqrt 2 * (m 0 - 3 * m 1) : ℝ) : ℂ) := by
  have h := arcGammaMultiplier_odd_eq_sum (fun j => arcGammaWeight (m j) j) 1
  rw [show ((2 * 1 + 1 : ℕ) : ℂ) = 3 by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, shiftedGammaPoly,
    Finset.prod_range_succ, arcGammaWeight, Nat.factorial]
  push_cast
  ring_nf
  simp only [Complex.I_pow_four]
  ring

/-- **`R(5) = 4√2 (m₀ − 10 m₁ + (35/3) m₂)`.** -/
theorem arcGammaMultiplier_five (m : ℕ → ℝ) :
    arcGammaMultiplier (fun j => arcGammaWeight (m j) j) 5 =
      ((4 * Real.sqrt 2 * (m 0 - 10 * m 1 + 35 / 3 * m 2) : ℝ) : ℂ) := by
  have h := arcGammaMultiplier_odd_eq_sum (fun j => arcGammaWeight (m j) j) 2
  rw [show ((2 * 2 + 1 : ℕ) : ℂ) = 5 by norm_num] at h
  rw [h]
  have hI8 : I ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, Complex.I_pow_four, one_pow]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, shiftedGammaPoly,
    Finset.prod_range_succ, arcGammaWeight, Nat.factorial]
  push_cast
  ring_nf
  simp only [Complex.I_pow_four, hI8]
  ring

/-- The kernel `1 − 3u²` of `R(3)` is positive on the arc. -/
theorem arcKernelThree_pos {u : ℝ} (hu : u ^ 2 ≤ 1 / 4) : 0 < 1 - 3 * u ^ 2 := by linarith

/-- The kernel `1 − 10u² + (35/3)u⁴` of `R(5)` is negative for `3/20 ≤ u² ≤ 1/4`. -/
theorem arcKernelFive_neg {u : ℝ} (h1 : 3 / 20 ≤ u ^ 2) (h2 : u ^ 2 ≤ 1 / 4) :
    1 - 10 * u ^ 2 + 35 / 3 * (u ^ 2) ^ 2 < 0 := by
  nlinarith

/-- **`R(5) < 0` for moments of a measure carried by `u² ∈ [3/20, 1/4]`.**  If
`m_j = Σ_i c_i (u_i²)^j` with `c_i ≥ 0`, not all zero, and every `u_i² ∈ [3/20, 1/4]`, then the arc
multiplier is negative at `s = 5`, so the family is not even-type. -/
theorem arcGammaMultiplier_five_neg_of_moments {ι : Type*} (S : Finset ι) (c v : ι → ℝ)
    (hc : ∀ i ∈ S, 0 ≤ c i) (hpos : ∃ i ∈ S, 0 < c i)
    (hv : ∀ i ∈ S, 3 / 20 ≤ v i ∧ v i ≤ 1 / 4) :
    (arcGammaMultiplier (fun j => arcGammaWeight (∑ i ∈ S, c i * v i ^ j) j) 5).re < 0 := by
  rw [arcGammaMultiplier_five, Complex.ofReal_re]
  have hsum : (∑ i ∈ S, c i * v i ^ 0) - 10 * (∑ i ∈ S, c i * v i ^ 1) +
      35 / 3 * (∑ i ∈ S, c i * v i ^ 2) =
      ∑ i ∈ S, c i * (1 - 10 * v i + 35 / 3 * v i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  have hneg : ∑ i ∈ S, c i * (1 - 10 * v i + 35 / 3 * v i ^ 2) < 0 := by
    obtain ⟨i₀, hi₀, hci₀⟩ := hpos
    have hlt := Finset.sum_lt_sum (s := S) (f := fun i => c i * (1 - 10 * v i + 35 / 3 * v i ^ 2))
      (g := fun _ => (0 : ℝ)) (fun i hi => ?_) ⟨i₀, hi₀, ?_⟩
    · simpa using hlt
    · have hk : 1 - 10 * v i + 35 / 3 * v i ^ 2 < 0 := by
        obtain ⟨h1, h2⟩ := hv i hi; nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos (hc i hi) hk.le
    · have hk : 1 - 10 * v i₀ + 35 / 3 * v i₀ ^ 2 < 0 := by
        obtain ⟨h1, h2⟩ := hv i₀ hi₀; nlinarith
      exact mul_neg_of_pos_of_neg hci₀ hk
  have hs : 0 < 4 * Real.sqrt 2 := by positivity
  nlinarith

end RHTower.WeilSpectral
