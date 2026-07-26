import GaloisForLFunctions.RHTower.ReverseBesselFixedFrequencyBlindness
import GaloisForLFunctions.RHTower.XiSquaredRadialOddResolvedSourceUniversalityLaw

/-!
# Xi squared-radial odd Euler sinh-response universality

The odd parity projection of the normalized reverse-Bessel radial polynomial converges to `sinh`.
Thus the odd prime--Gamma--polar sector retains an antisymmetric fixed Euler-frequency response,
while its finite-depth Xi radial jet is exactly the negative resolved source.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Odd parity projection of the reverse-Bessel radial polynomial. -/
def reverseBesselOddPoly (n : ℕ) (x : ℝ) : ℝ :=
  (reverseBesselPoly n x - reverseBesselPoly n (-x)) / 2

private theorem reverseBesselRatio_nonneg_all (n j : ℕ) :
    0 ≤ reverseBesselRatio n j := by
  rw [reverseBesselRatio]
  exact div_nonneg (by positivity) (weight_zero_pos n).le

private theorem reverseBesselRatio_le_factorial_all (n j : ℕ) :
    reverseBesselRatio n j ≤ 1 / (j.factorial : ℝ) := by
  rcases le_or_gt j n with hj | hj
  · rw [reverseBesselRatio, div_le_iff₀ (weight_zero_pos n)]
    have hle := weight_le_div (n := n) (j := j) hj
    rw [show (1 : ℝ) / (j.factorial : ℝ) *
        (squaredRadialJetWeight n 0 : ℝ) =
      (squaredRadialJetWeight n 0 : ℝ) / (j.factorial : ℝ) by ring]
    exact hle
  · rw [reverseBesselRatio, squaredRadialJetWeight_eq_zero_of_lt n j hj]
    simp

/-- The normalized reverse-Bessel polynomial converges to `exp` at every real argument. -/
theorem reverseBesselPoly_div_tendsto_exp_all (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ))
      atTop (nhds (Real.exp x)) := by
  have hFtsum : ∀ n,
      reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ) =
        ∑' k, reverseBesselRatio n k * x ^ k := by
    intro n
    have hsum_eq :
        reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ) =
          ∑ k ∈ Finset.range (n + 1), reverseBesselRatio n k * x ^ k := by
      rw [reverseBesselPoly, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by
        rw [reverseBesselRatio]
        ring
    rw [hsum_eq, tsum_eq_sum (s := Finset.range (n + 1))]
    intro k hk
    have hkn : n < k := by
      simpa [Nat.lt_succ_iff] using hk
    rw [reverseBesselRatio, squaredRadialJetWeight_eq_zero_of_lt n k hkn]
    simp
  have hlim (k : ℕ) :
      Tendsto (fun n : ℕ => reverseBesselRatio n k * x ^ k) atTop
        (nhds (x ^ k / (k.factorial : ℝ))) := by
    have h := (reverseBesselRatio_tendsto k).mul_const (x ^ k)
    simpa only [one_div, inv_mul_eq_div] using h
  have hbound : ∀ n k : ℕ,
      ‖reverseBesselRatio n k * x ^ k‖ ≤
        |x| ^ k / (k.factorial : ℝ) := by
    intro n k
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (reverseBesselRatio_nonneg_all n k), abs_pow]
    calc
      reverseBesselRatio n k * |x| ^ k
          ≤ (1 / (k.factorial : ℝ)) * |x| ^ k := by
            gcongr
            exact reverseBesselRatio_le_factorial_all n k
      _ = |x| ^ k / (k.factorial : ℝ) := by ring
  have hsummable :
      Summable (fun k : ℕ => |x| ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial |x|
  have htan :=
    tendsto_tsum_of_dominated_convergence hsummable hlim
      (Filter.Eventually.of_forall hbound)
  have hexp : (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp] at htan
  exact htan.congr' (Filter.Eventually.of_forall fun n => (hFtsum n).symm)

/-- The odd reverse-Bessel channel converges to the odd exponential projection `sinh`. -/
theorem reverseBesselOddPoly_div_tendsto_sinh (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        reverseBesselOddPoly n x /
          (squaredRadialJetWeight n 0 : ℝ))
      atTop (nhds (Real.sinh x)) := by
  have hlim :=
    (reverseBesselPoly_div_tendsto_exp_all x).sub
      (reverseBesselPoly_div_tendsto_exp_all (-x))
  have hlim' := hlim.div_const 2
  rw [← Real.sinh_eq] at hlim'
  refine hlim'.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold reverseBesselOddPoly
  have hb : (squaredRadialJetWeight n 0 : ℝ) ≠ 0 :=
    (weight_zero_pos n).ne'
  field_simp

/-- Fixed Euler-frequency response of the odd reverse-Bessel source channel. -/
theorem reverseBesselOdd_fixedEulerFrequency_response
    (w : ℝ) (m : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (m : ℝ) ^ (-(1 / 2 : ℝ) - w) *
          (reverseBesselOddPoly n (w * Real.log m) /
            (squaredRadialJetWeight n 0 : ℝ)))
      atTop
      (nhds ((m : ℝ) ^ (-(1 / 2 : ℝ) - w) *
        Real.sinh (w * Real.log m))) := by
  exact
    (reverseBesselOddPoly_div_tendsto_sinh (w * Real.log m)).const_mul
      ((m : ℝ) ^ (-(1 / 2 : ℝ) - w))

/--
**Xi squared-radial odd Euler sinh-response universality.**

The same odd reverse-Bessel coefficients have a `sinh` fixed-frequency limit and give the exact
negative prime--Gamma--polar resolution of every finite odd Xi radial sector.
-/
theorem xi_squaredRadialOdd_eulerSinhResponseUniversality :
    (∀ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          reverseBesselOddPoly n x /
            (squaredRadialJetWeight n 0 : ℝ))
        atTop (nhds (Real.sinh x))) ∧
    (∀ w : ℝ, 0 < w → ∀ m : ℕ, 2 ≤ m →
      Tendsto
        (fun n : ℕ =>
          (m : ℝ) ^ (-(1 / 2 : ℝ) - w) *
            (reverseBesselOddPoly n (w * Real.log m) /
              (squaredRadialJetWeight n 0 : ℝ)))
        atTop
        (nhds ((m : ℝ) ^ (-(1 / 2 : ℝ) - w) *
          Real.sinh (w * Real.log m)))) ∧
    ∀ x : ℝ, 1 < x → ∀ n : ℕ,
      squaredXiOddRadialJetPolynomial n x =
        -squaredXiOddRadialResolvedSourcePolynomial n x := by
  exact ⟨reverseBesselOddPoly_div_tendsto_sinh,
    fun w _ m _ => reverseBesselOdd_fixedEulerFrequency_response w m,
    fun _ hx n => squaredXiOddRadialJetPolynomial_eq_neg_resolvedSource hx n⟩

end

end RHTower
