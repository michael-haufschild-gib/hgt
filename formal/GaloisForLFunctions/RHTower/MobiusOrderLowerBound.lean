import GaloisForLFunctions.RHTower.MobiusDecayZeroObstruction
import GaloisForLFunctions.RHTower.XiZeroHalfPlaneWitness

/-!
# The unconditional order lower bound

The functional equation supplies a Xi zero with real part at least `1/2`, and inside the open unit
strip the Xi zeros are exactly the zeta zeros.  Feeding that zero into the Mellin obstruction gives
the unconditional statement: no subpower bound with exponent below `k - 1` can hold for the
Hermitian mixed `2k`-fold convolution of the Möbius coefficients.

Nothing here assumes anything about the location of the zeros beyond their existence and the
reflection symmetry, so the bound is unconditional; it is the conductor-one case of the raw-Möbius
order law with `Θ ≥ 1/2`.
-/

namespace RHTower

/-- Every abscissa strictly below the critical line is exceeded by a zeta zero different from `1`.
Inside the open unit strip the Xi zeros are precisely the zeta zeros. -/
theorem exists_riemannZeta_eq_zero_lt_re {b : ℝ} (hb : b < 1 / 2) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ b < ρ.re := by
  obtain ⟨ρ, hρ, hre⟩ := exists_xiZeroSet_lt_re hb
  obtain ⟨hpos, hlt⟩ := xiZeroSet_mem_openUnitStrip hρ
  have h1 : ρ ≠ 1 := by
    intro h
    rw [h] at hlt
    simp at hlt
  exact ⟨ρ, (xi_eq_zero_iff hpos h1).mp hρ, h1, hre⟩

/-- **The unconditional order lower bound.**  If `α + 1 < k` then no bound
`Re R_k(N) ≤ C (N+1)^α` can hold: the Hermitian mixed `2k`-fold convolution of the Möbius
coefficients has order at least `k - 1`. -/
theorem not_mixedSubpower_of_lt_sub_one
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 < (k : ℝ)) :
    ¬ (∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ C * ((N : ℝ) + 1) ^ α) := by
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hb : (α + 1) / (2 * (k : ℝ)) < 1 / 2 := by
    rw [div_lt_div_iff₀ hkR (by norm_num)]
    linarith
  obtain ⟨ρ, hzero, h1, hre⟩ := exists_riemannZeta_eq_zero_lt_re hb
  exact not_mixedSubpower_of_riemannZeta_eq_zero hk hα hC h1 hzero hre

/-- The same statement as an exceeded bound: below the threshold every admissible constant is beaten
at some index. -/
theorem exists_lt_mixedAdditiveConvolutionPower_re_of_lt_sub_one
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hαk : α + 1 < (k : ℝ)) :
    ∃ N : ℕ, C * ((N : ℝ) + 1) ^ α <
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re := by
  by_contra hcon
  refine not_mixedSubpower_of_lt_sub_one hk hα hC hαk fun N => ?_
  exact not_lt.mp fun h => hcon ⟨N, h⟩

end RHTower
