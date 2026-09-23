import GaloisForLFunctions.HTGeometry.FiniteClockStarKadison

/-!
# Finite-clock orbit asymmetry

For an arbitrary finite-period isometric clock, the total squared symmetry-breaking of an
observable along the complete clock orbit is exactly `2N` times its star-Kadison observability
loss.  On a stationary state this becomes an orbit-averaged commutator Parseval law.

The identity interprets clock observability as asymmetry under the family of available clock
readings.  The orbit indexes observational perspectives; it is not a temporal trajectory.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The expectation of a self-adjoint idempotent is the squared norm of its retained component. -/
theorem re_inner_selfAdjointIdempotent_apply_eq_normSq
    (P : E →L[𝕜] E) (hPadj : P.adjoint = P) (hP2 : P * P = P) (x : E) :
    RCLike.re (inner 𝕜 x (P x)) = ‖P x‖ ^ (2 : ℕ) := by
  have hfixed : P (P x) = P x := by
    rw [← mul_apply_eq_comp, hP2]
  calc
    RCLike.re (inner 𝕜 x (P x)) =
        RCLike.re (inner 𝕜 (P.adjoint x) x) := by
          rw [ContinuousLinearMap.adjoint_inner_left]
    _ = RCLike.re (inner 𝕜 (P x) x) := by rw [hPadj]
    _ = RCLike.re (inner 𝕜 (P (P x)) x) := by rw [hfixed]
    _ = RCLike.re (inner 𝕜 (P x) (P.adjoint x)) := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = RCLike.re (inner 𝕜 (P x) (P x)) := by rw [hPadj]
    _ = ‖P x‖ ^ (2 : ℕ) := inner_self_eq_norm_sq _

/-- Every power of an isometry preserves squared vector norm. -/
theorem norm_pow_apply_sq_eq_of_adjoint_mul_self
    (U : E →L[𝕜] E) (k : ℕ) (hadjoint_mul : U.adjoint * U = 1) (x : E) :
    ‖(U ^ k) x‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) := by
  have hk : (U ^ k).adjoint * U ^ k = 1 :=
    adjoint_pow_mul_pow_eq_one_of_adjoint_mul_self U k hadjoint_mul
  calc
    ‖(U ^ k) x‖ ^ (2 : ℕ) =
        RCLike.re (inner 𝕜 x (((U ^ k).adjoint * U ^ k) x)) := by
          simpa only [mul_apply_eq_comp] using!
            (U ^ k).apply_norm_sq_eq_inner_adjoint_right x
    _ = ‖x‖ ^ (2 : ℕ) := by rw [hk]; simp

/-- Summing the real orbit overlaps gives `N` times the squared norm retained by the finite-clock
projection. -/
theorem sum_re_inner_finiteClockOrbit_eq
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) (x : E) :
    ∑ k ∈ Finset.range N, RCLike.re (inner 𝕜 ((U ^ k) x) x) =
      (N : ℝ) * ‖finiteCyclicGaugeAverage U N x‖ ^ (2 : ℕ) := by
  let P : E →L[𝕜] E := finiteCyclicGaugeAverage U N
  have hPadj : P.adjoint = P := by
    simpa only [P, ContinuousLinearMap.star_eq_adjoint] using
      (finiteCyclicGaugeAverage_isSelfAdjoint_of_periodic_isometry
        U N hN hadjoint_mul hperiod).star_eq
  have hP2 : P * P = P := finiteCyclicGaugeAverage_idempotent U N hN hperiod
  have hproj := re_inner_selfAdjointIdempotent_apply_eq_normSq P hPadj hP2 x
  have hsum : finiteCyclicGaugeSum U N x = (N : 𝕜) • P x := by
    simp [P, finiteCyclicGaugeAverage, Nat.cast_ne_zero.mpr hN]
  have hreSum :
      ∀ s : Finset ℕ,
        ∑ k ∈ s, RCLike.re (inner 𝕜 ((U ^ k) x) x) =
          RCLike.re (inner 𝕜 (∑ k ∈ s, (U ^ k) x) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, inner_add_left,
          map_add, ih]
  calc
    ∑ k ∈ Finset.range N, RCLike.re (inner 𝕜 ((U ^ k) x) x) =
        RCLike.re (inner 𝕜 (finiteCyclicGaugeSum U N x) x) := by
          rw [hreSum]
          simp [finiteCyclicGaugeSum]
    _ = RCLike.re (inner 𝕜 ((N : 𝕜) • P x) x) := by rw [hsum]
    _ = (N : ℝ) * RCLike.re (inner 𝕜 (P x) x) := by
      rw [inner_smul_left]
      simp
    _ = (N : ℝ) * RCLike.re (inner 𝕜 x (P x)) := by rw [inner_re_symm]
    _ = (N : ℝ) * ‖P x‖ ^ (2 : ℕ) := by rw [hproj]

/-- **Finite-orbit asymmetry Parseval law.**  Total squared displacement across all clock
perspectives is exactly `2N` times the squared component erased by averaging. -/
theorem sum_finiteClockOrbitDeviation_sq_eq
    (U : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1) (x : E) :
    ∑ k ∈ Finset.range N, ‖(U ^ k) x - x‖ ^ (2 : ℕ) =
      2 * (N : ℝ) * ‖(1 - finiteCyclicGaugeAverage U N) x‖ ^ (2 : ℕ) := by
  have hinner := sum_re_inner_finiteClockOrbit_eq U N hN hadjoint_mul hperiod x
  have hsplit :=
    norm_finiteCyclicGaugeAverage_sq_add_complement_sq_of_periodic_isometry
      U N hN hadjoint_mul hperiod x
  calc
    ∑ k ∈ Finset.range N, ‖(U ^ k) x - x‖ ^ (2 : ℕ) =
        ∑ k ∈ Finset.range N,
          (2 * ‖x‖ ^ (2 : ℕ) - 2 * RCLike.re (inner 𝕜 ((U ^ k) x) x)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [@norm_sub_sq 𝕜,
              norm_pow_apply_sq_eq_of_adjoint_mul_self U k hadjoint_mul x]
            ring
    _ = 2 * (N : ℝ) * ‖x‖ ^ (2 : ℕ) -
        2 * ∑ k ∈ Finset.range N,
          RCLike.re (inner 𝕜 ((U ^ k) x) x) := by
            simp only [Finset.sum_sub_distrib,
              Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            rw [← Finset.mul_sum]
            ring
    _ = 2 * (N : ℝ) * ‖x‖ ^ (2 : ℕ) -
        2 * ((N : ℝ) * ‖finiteCyclicGaugeAverage U N x‖ ^ (2 : ℕ)) := by rw [hinner]
    _ = 2 * (N : ℝ) * ‖(1 - finiteCyclicGaugeAverage U N) x‖ ^ (2 : ℕ) := by
      nlinarith

/-- **Arbitrary-period clock commutator energy.**  On a stationary state, the sum of squared
commutator values over the complete finite clock orbit is exactly `2N` times the star-Kadison
observability energy.  No self-adjointness premise on `X` is needed. -/
theorem sum_finiteClockCommutator_sq_eq_starObservability
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0)
    (hadjoint_mul : U.adjoint * U = 1) (hperiod : U ^ N = 1)
    {ψ : E} (hψ : U ψ = ψ) :
    ∑ k ∈ Finset.range N, ‖(U ^ k * X - X * U ^ k) ψ‖ ^ (2 : ℕ) =
      2 * (N : ℝ) * RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) := by
  have hpowfix : ∀ k : ℕ, (U ^ k) ψ = ψ :=
    fun k => pow_apply_eq_self_of_apply_eq_self U hψ k
  calc
    ∑ k ∈ Finset.range N, ‖(U ^ k * X - X * U ^ k) ψ‖ ^ (2 : ℕ) =
        ∑ k ∈ Finset.range N, ‖(U ^ k) (X ψ) - X ψ‖ ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [_root_.sub_apply, mul_apply_eq_comp, hpowfix]
    _ = 2 * (N : ℝ) *
        ‖(1 - finiteCyclicGaugeAverage U N) (X ψ)‖ ^ (2 : ℕ) :=
      sum_finiteClockOrbitDeviation_sq_eq U N hN hadjoint_mul hperiod (X ψ)
    _ = 2 * (N : ℝ) * RCLike.re
        (inner 𝕜 ψ
          (finiteCyclicObservableTwirlStarKadisonDefect U X N ψ)) := by
      rw [re_inner_finiteCyclicObservableTwirlStarKadisonDefect_eq_erasedNormSq
        U X N hN hadjoint_mul hperiod hψ]

end

end HTGeometry
