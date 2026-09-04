import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCesaroCriterion
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCofinalScheduleNoGo

/-!
# Diagonal Cesàro source no-go

Cesàro averaging alone is nonlocal enough to evade the raw bounded-partial-sum implication.
However, synchronizing cutoff `N` with Cayley pole-factor degree `N` is too aggressive. At the
fixed point `6/11`, the pole factor grows at least as `5^(N-24)`. Local boundedness of the
pole-cleared product would force the Cesàro average to decay exponentially.

One discrete derivative recovers the raw Dirichlet partial sum from adjacent Cesàro averages.
Exponential Cesàro decay therefore makes the raw partial sums eventually bounded, contradicting
their unconditional arithmetic unboundedness. This closes only diagonal synchronization; slower
independent pole-factor schedules remain outside the theorem.
-/

open Complex Filter Metric Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Multiplying a Cesàro average by its length recovers its defining cutoff sum. -/
theorem natCast_mul_squarefreeHalfCesaroSum (N : ℕ) (s : ℂ) :
    (N : ℂ) * squarefreeHalfCesaroSum N s =
      ∑ M ∈ Finset.range N, squarefreeHalfDirichletPartialSum M s := by
  rcases N with _ | N
  · simp [squarefreeHalfCesaroSum]
  · rw [squarefreeHalfCesaroSum]
    have hne : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero N
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- Cesàro averages recover raw partial sums by one discrete derivative. -/
theorem squarefreeHalfDirichletPartialSum_eq_cesaro_discreteDerivative
    (N : ℕ) (s : ℂ) :
    squarefreeHalfDirichletPartialSum N s =
      ((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) s -
        (N : ℂ) * squarefreeHalfCesaroSum N s := by
  rw [natCast_mul_squarefreeHalfCesaroSum,
    natCast_mul_squarefreeHalfCesaroSum, Finset.sum_range_succ]
  ring

private theorem nat_le_twentyFour_mul_five_pow_sub (N : ℕ) (hN : 24 ≤ N) :
    (N : ℝ) ≤ 24 * (5 : ℝ) ^ (N - 24) := by
  let m := N - 24
  have hNm : N = m + 24 := by
    dsimp [m]
    omega
  rw [hNm]
  change ((m + 24 : ℕ) : ℝ) ≤ 24 * (5 : ℝ) ^ m
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hpow : (1 : ℝ) ≤ (5 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      push_cast at ih ⊢
      rw [pow_succ]
      nlinarith

/-- **Diagonal Cesàro no-go.** The canonical Cesàro-smoothed family cannot be locally bounded
after synchronizing Cayley pole-factor degree with arithmetic cutoff. -/
theorem no_poleClearedFirstTraceCesaroLocallyBounded :
    ¬ PoleClearedFirstTraceCesaroLocallyBounded := by
  intro hloc
  obtain ⟨R, hR, hball, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceCesaroApprox N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hC0 : 0 ≤ C :=
    (norm_nonneg (poleClearedFirstTraceCesaroApprox 0 boundaryExteriorPoint)).trans (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hweighted : ∀ N : ℕ, 24 ≤ N →
      (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ 24 * K := by
    intro N hN
    have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow hN
    have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
      norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
    have hsource := hbound N
    have hprod :
        ‖poleFactorSqrtApprox N boundaryExteriorPoint‖ *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K := by
      rw [poleClearedFirstTraceCesaroApprox, norm_div, norm_mul] at hsource
      exact (div_le_iff₀ hdetpos).mp hsource
    have hpowprod :
        (5 : ℝ) ^ (N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤ K :=
      (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hprod
    calc
      (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          (24 * (5 : ℝ) ^ (N - 24)) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ :=
        mul_le_mul_of_nonneg_right (nat_le_twentyFour_mul_five_pow_sub N hN) (norm_nonneg _)
      _ = 24 * ((5 : ℝ) ^ (N - 24) *
            ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖) := by ring
      _ ≤ 24 * K := mul_le_mul_of_nonneg_left hpowprod (by norm_num)
  have hpartial : ∀ N : ℕ, 24 ≤ N →
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ ≤ 48 * K := by
    intro N hN
    rw [squarefreeHalfDirichletPartialSum_eq_cesaro_discreteDerivative]
    calc
      ‖((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint -
          (N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint‖ ≤
          ‖((N + 1 : ℕ) : ℂ) * squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint‖ +
            ‖(N : ℂ) * squarefreeHalfCesaroSum N boundaryExteriorPoint‖ := norm_sub_le _ _
      _ = ((N + 1 : ℕ) : ℝ) *
            ‖squarefreeHalfCesaroSum (N + 1) boundaryExteriorPoint‖ +
          (N : ℝ) * ‖squarefreeHalfCesaroSum N boundaryExteriorPoint‖ := by
        simp only [norm_mul, norm_natCast]
      _ ≤ 24 * K + 24 * K := add_le_add
        (hweighted (N + 1) (by omega)) (hweighted N hN)
      _ = 48 * K := by ring
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨48 * K, 24, hpartial⟩

end

end RHTower
