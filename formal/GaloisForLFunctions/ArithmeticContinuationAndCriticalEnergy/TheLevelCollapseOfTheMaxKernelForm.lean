import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePolarCalibrationOfTheMaxKernelForm

/-!
# The level collapse of the max-kernel form

The Nyman–Beurling kernel `1/max(j,k)` is constant on the levels `max(j,k) = M`, and each level is
one row plus one column with the corner counted once.  So the double sum over prime-power pairs is
*not* a genuinely bilinear object: it collapses to a single sum over scales,

`Σ_{j,k ≤ T} a_j b_k / max(j,k) = Σ_{M ≤ T} (a_M B_M + A_M b_M − a_M b_M)/M`,

with `A_M, B_M` the prefixes of the two rows (`sum_sum_div_max_eq_level_sum`).  Applied to the
damping autocorrelation this removes the last double sum from the continuation obstruction:

`K_T(η, ε) = Σ_{M ≤ T} (a_M(η) E_ε(M) + E_η(M) a_M(ε) − a_M(η) a_M(ε))/M
              − E_η(T) E_ε(T)/(T+1)`,

where `a_M(η) = Λ_η(M) − m(η)` is the increment and `E_η` the centred damped Chebyshev function
(`tangentCorrelation_eq_level_sum`).  The sign the continuation layer needs is therefore the sign
of one scale sum whose terms pair an increment at scale `M` with the centred prefix at the same
scale — a cross-correlation at equal scales, weighted by `1/M`, against the quadratic diagonal
`a_M(η) a_M(ε)/M` whose prime part is a slowly growing prime-square sum.

On the diagonal the same identity is an exact energy balance
(`pronicNorm_dampedChebyshevError_sq_eq_level_sum`): the pronic tangent energy plus its horizon
boundary term equals `Σ_{M ≤ T} (2 a_M E(M) − a_M²)/M`, the discrete analogue of
`d(E²) = 2E dE − (dE)²`.  So every quantity the continuation layer needs is a single prime-weighted
sum against the centred prefix at the same scale.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The collapse for arbitrary rows -/

/-- **The level collapse.**  The level `max(j,k) = M` is a row plus a column with one shared
corner, so the double kernel sum is a single sum over scales. -/
theorem sum_sum_div_max_eq_level_sum (T : ℕ) (a b : ℕ → ℝ) :
    (∑ j ∈ Icc 1 T, ∑ k ∈ Icc 1 T, a j * b k / ((max j k : ℕ) : ℝ)) =
      ∑ M ∈ Icc 1 T, (a M * (∑ k ∈ Icc 1 M, b k) + (∑ j ∈ Icc 1 M, a j) * b M - a M * b M) /
        (M : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hT1 : (1 : ℕ) ≤ T + 1 := by omega
    -- the new column: `k = T+1` against every `j ≤ T`, all at level `T+1`
    have hinner : ∀ j ∈ Icc 1 T, (∑ k ∈ Icc 1 (T + 1), a j * b k / ((max j k : ℕ) : ℝ)) =
        (∑ k ∈ Icc 1 T, a j * b k / ((max j k : ℕ) : ℝ)) +
          a j * b (T + 1) / ((T : ℝ) + 1) := by
      intro j hj
      rw [mem_Icc] at hj
      rw [Finset.sum_Icc_succ_top hT1, max_eq_right (by omega : j ≤ T + 1)]
      push_cast
      ring
    -- the new row: `j = T+1` against every `k ≤ T+1`, all at level `T+1`
    have hlast : (∑ k ∈ Icc 1 (T + 1), a (T + 1) * b k / ((max (T + 1) k : ℕ) : ℝ)) =
        a (T + 1) * (∑ k ∈ Icc 1 (T + 1), b k) / ((T : ℝ) + 1) := by
      have hconst : ∀ k ∈ Icc 1 (T + 1), a (T + 1) * b k / ((max (T + 1) k : ℕ) : ℝ) =
          a (T + 1) * b k / ((T : ℝ) + 1) := by
        intro k hk
        rw [mem_Icc] at hk
        rw [max_eq_left hk.2]
        push_cast
        ring
      rw [Finset.sum_congr rfl hconst, ← Finset.sum_div, ← Finset.mul_sum]
    rw [Finset.sum_Icc_succ_top hT1, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih,
      hlast, Finset.sum_Icc_succ_top (f := fun M => (a M * (∑ k ∈ Icc 1 M, b k) +
        (∑ j ∈ Icc 1 M, a j) * b M - a M * b M) / (M : ℝ)) hT1]
    have hprefix : (∑ j ∈ Icc 1 (T + 1), a j) = (∑ j ∈ Icc 1 T, a j) + a (T + 1) :=
      Finset.sum_Icc_succ_top hT1 _
    have hcol : (∑ j ∈ Icc 1 T, a j * b (T + 1) / ((T : ℝ) + 1)) =
        (∑ j ∈ Icc 1 T, a j) * b (T + 1) / ((T : ℝ) + 1) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [hcol, hprefix]
    push_cast
    ring

/-! ## §2. The autocorrelation as a single scale sum -/

/-- **The damping autocorrelation as one scale sum.**  Each term pairs the increment at a scale
with the centred prefix at the same scale. -/
theorem tangentCorrelation_eq_level_sum (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε =
      (∑ M ∈ Icc 1 T, (dampedChebyshevIncrement η M * dampedChebyshevError ε M +
          dampedChebyshevError η M * dampedChebyshevIncrement ε M -
          dampedChebyshevIncrement η M * dampedChebyshevIncrement ε M) / (M : ℝ)) -
        dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1) := by
  rw [tangentCorrelation_eq_maxKernel,
    sum_sum_div_max_eq_level_sum T (dampedChebyshevIncrement η) (dampedChebyshevIncrement ε)]
  congr 1
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← dampedChebyshevError_eq_sum_increment, ← dampedChebyshevError_eq_sum_increment]

/-- **The diagonal energy balance.**  The pronic tangent energy plus its horizon boundary term is
the scale sum of `2 a_M E(M) − a_M²`: the discrete form of `d(E²) = 2E dE − (dE)²`. -/
theorem pronicNorm_dampedChebyshevError_sq_eq_level_sum (T : ℕ) (ε : ℝ) :
    pronicNorm T (dampedChebyshevError ε) ^ 2 +
        dampedChebyshevError ε T ^ 2 / ((T : ℝ) + 1) =
      ∑ M ∈ Icc 1 T, (2 * dampedChebyshevIncrement ε M * dampedChebyshevError ε M -
        dampedChebyshevIncrement ε M ^ 2) / (M : ℝ) := by
  have h := tangentCorrelation_eq_level_sum T ε ε
  rw [tangentCorrelation_self] at h
  have hterm : ∀ M ∈ Icc 1 T,
      (dampedChebyshevIncrement ε M * dampedChebyshevError ε M +
          dampedChebyshevError ε M * dampedChebyshevIncrement ε M -
          dampedChebyshevIncrement ε M * dampedChebyshevIncrement ε M) / (M : ℝ) =
        (2 * dampedChebyshevIncrement ε M * dampedChebyshevError ε M -
          dampedChebyshevIncrement ε M ^ 2) / (M : ℝ) :=
    fun M _ => by ring
  rw [Finset.sum_congr rfl hterm] at h
  rw [← sq] at h
  linarith

/-- **The scale-sum criterion for the Riemann hypothesis.**  A sign for one prime-weighted scale
sum — increments against the centred prefix at the same scale, less the quadratic diagonal — gives
RH.  No double sum and no norm appears. -/
theorem riemannHypothesis_of_nonneg_levelSum
    (h : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 →
      dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1) ≤
        ∑ M ∈ Icc 1 T, (dampedChebyshevIncrement η M * dampedChebyshevError ε M +
          dampedChebyshevError η M * dampedChebyshevIncrement ε M -
          dampedChebyshevIncrement η M * dampedChebyshevIncrement ε M) / (M : ℝ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonneg_tangentCorrelation fun T η ε hη hηε hε => by
    rw [tangentCorrelation_eq_level_sum]
    linarith [h T η ε hη hηε hε]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
