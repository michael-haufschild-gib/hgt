import GaloisForLFunctions.RHTower.Suzuki.SuzukiHatanoNelsonWall
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrbitWeightSummability

/-!
# `(23)`--`(24)`: the rank-`d` Hatano--Nelson limit symbol leaves the real axis

On boxes receding into the positive orthant the radially weighted prime adjacency has the limit
Laurent symbol `c₀ + Σ_q c_q [e^{κ|q|₁ + i⟨q,θ⟩} + e^{-κ|q|₁ - i⟨q,θ⟩}]`, i.e. a positive
combination of rank-one Hatano--Nelson symbols.  Its imaginary part is the sinh-weighted
trigonometric polynomial `2 Σ_q c_q sinh(κ|q|₁) sin⟨q,θ⟩`, which on steps with nonnegative
coordinates is strictly positive along a short diagonal ray: distinct valuation steps cannot cancel
there.  So the approximate spectrum contains a nonreal point and the rank-one wall applies.
-/

open Complex Finset

noncomputable section

namespace RHTower

/-- `(23)`: the limit Laurent symbol of the radially weighted adjacency on the receding orthant. -/
def latticeLimitSymbol {d : ℕ} (c₀ : ℝ) (Q : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ)
    (κ : ℝ) (θ : Fin d → ℝ) : ℂ :=
  (c₀ : ℂ) + ∑ q ∈ Q, (c q : ℂ) *
    hatanoNelsonSymbol (κ * (orbitLength q : ℝ)) (∑ i, ((q i : ℤ) : ℝ) * θ i)

/-- **`(24)`: the imaginary part of the limit symbol is the sinh-weighted trigonometric
polynomial.** -/
theorem im_latticeLimitSymbol {d : ℕ} (c₀ : ℝ) (Q : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ)
    (κ : ℝ) (θ : Fin d → ℝ) :
    (latticeLimitSymbol c₀ Q c κ θ).im
      = 2 * ∑ q ∈ Q, c q * Real.sinh (κ * (orbitLength q : ℝ))
          * Real.sin (∑ i, ((q i : ℤ) : ℝ) * θ i) := by
  rw [latticeLimitSymbol, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    hatanoNelsonSymbol_im]
  ring

/-- **`(24)`: the limit symbol genuinely leaves the real axis.**  Positive couplings on steps with
nonnegative coordinates make the trigonometric polynomial strictly positive along a short diagonal
ray, so distinct valuation characters cannot cancel. -/
theorem exists_im_latticeLimitSymbol_ne_zero {d : ℕ} {c₀ κ : ℝ} {Q : Finset (Fin d → ℤ)}
    {c : (Fin d → ℤ) → ℝ} (hκ : 0 < κ) (hQ : Q.Nonempty) (hc : ∀ q ∈ Q, 0 < c q)
    (hq0 : ∀ q ∈ Q, ∀ i, 0 ≤ q i) (hqne : ∀ q ∈ Q, q ≠ 0) :
    ∃ θ : Fin d → ℝ, (latticeLimitSymbol c₀ Q c κ θ).im ≠ 0 := by
  classical
  set N : ℕ := Q.sup orbitLength with hNdef
  have hlen : ∀ q ∈ Q, 1 ≤ orbitLength q := by
    intro q hq
    by_contra hcon
    have hzero : orbitLength q = 0 := by omega
    refine hqne q hq (funext fun i => ?_)
    have hsum : ∑ p, (q p).natAbs = 0 := hzero
    have := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    exact Int.natAbs_eq_zero.mp this
  have hN1 : 1 ≤ N := by
    obtain ⟨q, hq⟩ := hQ
    exact le_trans (hlen q hq) (Finset.le_sup hq)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  set t : ℝ := Real.pi / (2 * (N : ℝ)) with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    positivity
  refine ⟨fun _ => t, ?_⟩
  rw [im_latticeLimitSymbol]
  have hterm : ∀ q ∈ Q, 0 < c q * Real.sinh (κ * (orbitLength q : ℝ))
      * Real.sin (∑ i, ((q i : ℤ) : ℝ) * t) := by
    intro q hq
    have hlq : (1 : ℝ) ≤ (orbitLength q : ℝ) := by exact_mod_cast hlen q hq
    have hsum : (∑ i, ((q i : ℤ) : ℝ) * t) = (orbitLength q : ℝ) * t := by
      rw [← Finset.sum_mul]
      congr 1
      rw [orbitLength]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      have habs : |((q i : ℤ) : ℝ)| = (((q i).natAbs : ℕ) : ℝ) := by simp [Int.cast_abs]
      rw [← habs, abs_of_nonneg (by exact_mod_cast hq0 q hq i : (0 : ℝ) ≤ ((q i : ℤ) : ℝ))]
    have hle : (orbitLength q : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Finset.le_sup (f := orbitLength) hq
    have hupper : (orbitLength q : ℝ) * t ≤ Real.pi / 2 := by
      have hstep : (orbitLength q : ℝ) * (Real.pi / (2 * (N : ℝ)))
          ≤ (N : ℝ) * (Real.pi / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have heq : (N : ℝ) * (Real.pi / (2 * (N : ℝ))) = Real.pi / 2 := by
        field_simp
      rw [htdef]
      linarith [hstep, heq]
    have hlower : 0 < (orbitLength q : ℝ) * t := by positivity
    have hsin : 0 < Real.sin ((orbitLength q : ℝ) * t) := by
      refine Real.sin_pos_of_pos_of_lt_pi hlower ?_
      have := Real.pi_pos
      linarith [hupper]
    rw [hsum]
    have hsinh : 0 < Real.sinh (κ * (orbitLength q : ℝ)) := by
      refine sinh_pos_of_pos_suzukiHatanoNelsonWall ?_
      have hL : (0 : ℝ) < (orbitLength q : ℝ) := by linarith
      positivity
    have := hc q hq
    positivity
  have hpos : 0 < ∑ q ∈ Q, c q * Real.sinh (κ * (orbitLength q : ℝ))
      * Real.sin (∑ i, ((q i : ℤ) : ℝ) * t) := Finset.sum_pos hterm hQ
  intro hcon
  nlinarith [hpos]

end RHTower
