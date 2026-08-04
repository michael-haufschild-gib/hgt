import GaloisForLFunctions.HTGeometry.FirstEdgeSeparation
import GaloisForLFunctions.HTGeometry.SphereMaxModulus
import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation

/-!
# The growth separation from a circle carrying a floor

A step separation asks for a point at which the new state outgrows a multiple of the joint scale of
the earlier ones, with a floor for a prescribed polynomial in those states.  The point may be taken to
be a maximiser of the new state on a circle: a circle carrying a *uniform* floor for the polynomial
supplies the floor at every one of its points, and the maximiser of the new state on it dominates the
whole closed disc, so the two requirements are met simultaneously.

The datum this leaves is a comparison on one circle, with the floor part of the datum rather than a
free parameter.  That distinction is essential: a floor quantified universally may be taken
arbitrarily small, and `log⁺ ε⁻¹` then exceeds every bound, so an interface quantifying it that way is
unsatisfiable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The comparison on one circle: a positive floor for the coefficient valid at every point of the
circle, and the growth comparison at every point of it that dominates the enclosed disc. -/
def CircleComparison {m : ℕ} (X : Fin m → ℂ → ℂ) (F : ℂ → ℂ) : Prop :=
  ∀ A : MvPolynomial (Fin m) ℂ, A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
    ∃ (cen : ℂ) (s ε : ℝ), 0 < s ∧ 0 < ε ∧
      (∀ z : ℂ, ‖z - cen‖ = s → ε ≤ ‖MvPolynomial.eval (fun j => X j z) A‖) ∧
      (∀ z : ℂ, ‖z - cen‖ = s → (∀ w : ℂ, ‖w - cen‖ ≤ s → ‖F w‖ ≤ ‖F z‖) →
        c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖) + Real.posLog ε⁻¹)
          < Real.posLog ‖F z‖)

/-- **The separation from a circle comparison.**  The maximiser of the new state on the circle
carries both the floor and the domination, so it is the point the separation asks for. -/
theorem stepSeparation_of_circleComparison {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hFd : Differentiable ℂ F) (hcirc : CircleComparison X F) :
    StepSeparation X F := by
  intro A hA c hc
  obtain ⟨cen, s, ε, hs, hε, hfloor, hcomp⟩ := hcirc A hA c hc
  obtain ⟨z, hz, hmax⟩ := exists_sphere_isMaxOn_at hFd cen hs
  exact ⟨z, ε, hε, hfloor z hz, hcomp z hz hmax⟩

/-- **State independence from circle comparisons.** -/
theorem noRelation_prefixFamily_of_circleComparison (Y : ℕ → ℂ → ℂ)
    (hYd : ∀ m : ℕ, Differentiable ℂ (Y m))
    (hcirc : ∀ m : ℕ, CircleComparison (prefixFamily Y m) (Y m)) (m : ℕ) :
    ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval (fun j => prefixFamily Y m j z) P = 0) :=
  noRelation_prefixFamily Y
    (fun k => stepSeparation_of_circleComparison (hYd k) (hcirc k)) m

variable {f : ℕ → ℂ → ℂ}

/-- **The unit-cost law from circle comparisons.**  The paper's hypotheses, one comparison on a
circle per level, and the elimination step. -/
theorem exactDifferentialOrder_entireCascade_of_circleComparison {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hcirc : ∀ m : ℕ,
      CircleComparison (prefixFamily (entireCascade f) m) (entireCascade f m))
    (helim : ∀ m, m < n → DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n := by
  have hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) (Set.univ : Set ℂ) :=
    fun i => analyticOnNhd_of_transcendentalEntire (hall i)
  have hYd : ∀ m : ℕ, Differentiable ℂ (entireCascade f m) := by
    intro m z
    exact (analyticOnNhd_entireCascade hfan m z (Set.mem_univ z)).differentiableAt
  exact exactDifferentialOrder_entireCascade_of_separation' hall h1
    (fun m => stepSeparation_of_circleComparison (hYd m) (hcirc m)) helim

/-! ## The interface is inhabited: the two lowest edges -/

/-- **The circle comparison at the zeroth edge.**  There are no earlier states, so a nonzero
coefficient is a nonzero constant and floors itself; the coordinate then outgrows any prescribed
multiple of that constant on a large enough circle. -/
theorem circleComparison_zeroth_edge {Y : ℕ → ℂ → ℂ} (hY0 : ∀ z : ℂ, Y 0 z = z) :
    CircleComparison (prefixFamily Y 0) (Y 0) := by
  intro A hA c hc
  have hval : ∀ z : ℂ, MvPolynomial.eval (fun j => prefixFamily Y 0 j z) A
      = MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) A := by
    intro z
    exact DFunLike.congr_fun (eval_empty_eq (fun j => prefixFamily Y 0 j z)) A
  have ha : MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) A ≠ 0 := by
    intro h0
    exact hA ((MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective (by simpa using h0))
  set ε : ℝ := ‖MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) A‖ with hε
  have hε0 : 0 < ε := norm_pos_iff.mpr ha
  set t : ℝ := c * (1 + Real.posLog ε⁻¹) with ht
  set s : ℝ := Real.exp t + 1 with hs
  have hs1 : 1 < s := by
    rw [hs]
    linarith [Real.exp_pos t]
  refine ⟨0, s, ε, by linarith, hε0, ?_, ?_⟩
  · intro z _
    rw [hval z]
  · intro z hz _
    have hznorm : ‖z‖ = s := by simpa using hz
    have hYz : ‖Y 0 z‖ = s := by rw [hY0 z, hznorm]
    have hlogs : t < Real.log s := by
      have h1 : Real.log (Real.exp t) < Real.log s := by
        refine Real.log_lt_log (Real.exp_pos t) ?_
        rw [hs]; linarith
      rwa [Real.log_exp] at h1
    have hpos : Real.log s ≤ Real.posLog ‖Y 0 z‖ := by
      rw [hYz, Real.posLog_apply]
      exact le_max_right _ _
    have hsum : (∑ j : Fin 0, Real.posLog ‖prefixFamily Y 0 j z‖) = 0 := by
      simp
    rw [hsum]
    have : c * (1 + 0 + Real.posLog ε⁻¹) = t := by rw [ht]; ring
    rw [this]
    linarith

/-! ## The interface is inhabited: the first edge -/

/-- **The circle comparison at the first edge.**  For `Y 0` the coordinate and `Y 1` transcendental
entire, a circle carrying the comparison exists at every level.

The coefficient is a univariate polynomial, so it has the *uniform* floor `‖lead‖/2` at every point
beyond `growthRadius`; the circle is taken through a point where `Y 1` beats a chosen polynomial
bound, which is necessarily outside that radius since a transcendental entire function is bounded on
compacts. -/
theorem circleComparison_first_edge {Y : ℕ → ℂ → ℂ} (hY0 : ∀ z : ℂ, Y 0 z = z)
    (hf : TranscendentalEntire (Y 1)) :
    CircleComparison (prefixFamily Y 1) (Y 1) := by
  intro A hA c hc
  set q : Polynomial ℂ := toPoly A with hq
  have hq0 : q ≠ 0 := toPoly_ne_zero hA
  have hlc : 0 < ‖q.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq0)
  set ε : ℝ := ‖q.leadingCoeff‖ / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]; linarith
  set R : ℝ := growthRadius q with hR
  have hR1 : (1 : ℝ) ≤ R := one_le_growthRadius q
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  set L : ℝ := Real.posLog ε⁻¹ with hL
  have hL0 : 0 ≤ L := Real.posLog_nonneg
  set d : ℕ := ⌈c⌉₊ + 1 with hd
  have hcd : c ≤ (d : ℝ) := by
    rw [hd]; push_cast; linarith [Nat.le_ceil c]
  set K : ℝ := Real.exp (c + c * L + 1) with hK
  have hK0 : 0 < K := Real.exp_pos _
  set Mbig : ℝ := max K M₀ with hM
  have hMbig : 0 < Mbig := lt_of_lt_of_le hK0 (le_max_left _ _)
  obtain ⟨z₀, hz₀⟩ := exists_norm_gt_of_not_polynomial hf.1 hf.2 Mbig d
  -- the witness lies outside the disc on which `Y 1` is bounded
  have hzR : R < ‖z₀‖ := by
    by_contra hcon
    have hmem : z₀ ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using not_lt.mp hcon
    have hle : ‖Y 1 z₀‖ ≤ M₀ := hM₀ z₀ hmem
    have hpow : (1 : ℝ) ≤ (1 + ‖z₀‖) ^ d := one_le_pow₀ (by linarith [norm_nonneg z₀])
    have hMle : Mbig ≤ Mbig * (1 + ‖z₀‖) ^ d := by nlinarith [hMbig, hpow]
    have hM0le : M₀ ≤ Mbig := le_max_right K M₀
    linarith [hz₀, hMle, hle, hM0le]
  refine ⟨0, ‖z₀‖, ε, lt_of_lt_of_le (by linarith) hzR.le, hε0, ?_, ?_⟩
  · -- the floor holds at every point of the circle
    intro z hz
    have hznorm : ‖z‖ = ‖z₀‖ := by simpa using hz
    have hzR' : R ≤ ‖z‖ := by rw [hznorm]; exact hzR.le
    have hfloor : ε ≤ ‖q.eval z‖ := by
      obtain ⟨hz1, hz2⟩ := hyps_of_growthRadius_le hq0 hzR'
      have hge := norm_eval_ge_of_large hq0 hz1 hz2
      have hpow : (1 : ℝ) ≤ ‖z‖ ^ q.natDegree := one_le_pow₀ hz1
      have hstep : ‖q.leadingCoeff‖ / 2 * 1 ≤ ‖q.leadingCoeff‖ / 2 * ‖z‖ ^ q.natDegree :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      rw [hε]; linarith [hge, hstep]
    have hxfun : (fun j : Fin 1 => prefixFamily Y 1 j z) = fun _ : Fin 1 => z := by
      funext j
      refine Fin.cases ?_ (fun i => i.elim0) j
      exact hY0 z
    rw [hxfun, ← eval_toPoly, ← hq]
    exact hfloor
  · -- the comparison at every dominating point of the circle
    intro z hz hdom
    have hznorm : ‖z‖ = ‖z₀‖ := by simpa using hz
    have hbig : Mbig * (1 + ‖z‖) ^ d < ‖Y 1 z‖ := by
      have hle : ‖Y 1 z₀‖ ≤ ‖Y 1 z‖ := hdom z₀ (by simp)
      rw [hznorm]
      linarith [hz₀, hle]
    have hsum : (∑ j : Fin 1, Real.posLog ‖prefixFamily Y 1 j z‖) = Real.posLog ‖z‖ := by
      rw [Fin.sum_univ_one]
      have hz0 : prefixFamily Y 1 0 z = z := hY0 z
      rw [hz0]
    rw [hsum]
    have hP0 : (0 : ℝ) ≤ Real.posLog ‖z‖ := Real.posLog_nonneg
    have hpos : (0 : ℝ) < Mbig * (1 + ‖z‖) ^ d := by positivity
    have hlog : Real.log (Mbig * (1 + ‖z‖) ^ d) < Real.log ‖Y 1 z‖ :=
      Real.log_lt_log hpos hbig
    have hexp : Real.log (Mbig * (1 + ‖z‖) ^ d)
        = Real.log Mbig + d * Real.log (1 + ‖z‖) := by
      rw [Real.log_mul (ne_of_gt hMbig) (by positivity), Real.log_pow]
    have hKle : c + c * L + 1 ≤ Real.log Mbig := by
      have h1 : Real.log K = c + c * L + 1 := by rw [hK, Real.log_exp]
      have h2 : K ≤ Mbig := le_max_left _ _
      have := Real.log_le_log hK0 h2
      linarith [h1]
    have hPlog : Real.posLog ‖z‖ ≤ Real.log (1 + ‖z‖) :=
      posLog_le_log_one_add (norm_nonneg z)
    have hfinal : Real.log ‖Y 1 z‖ ≤ Real.posLog ‖Y 1 z‖ := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    nlinarith [hlog, hexp, hKle, hPlog, hfinal, hP0, hcd, hL0, hc]


/-- **The unit-cost law with the comparison required only from the second edge on.**  The two lowest
edges are theorems, so the analytic obligation begins where the earlier states are no longer just the
coordinate. -/
theorem exactDifferentialOrder_entireCascade_of_circleComparison_ge_two {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hcirc : ∀ m : ℕ, 2 ≤ m →
      CircleComparison (prefixFamily (entireCascade f) m) (entireCascade f m))
    (helim : ∀ m, m < n → DifferentiallyAlgebraicOfOrder (entireCascade f n) m →
      ∃ P : MvPolynomial (Fin n) (Polynomial ℂ), P ≠ 0 ∧
        ∀ z : ℂ, statePoly (cascadeFamily f n) P z = 0) :
    ExactDifferentialOrder (entireCascade f n) n := by
  have hone : entireCascade f 1 = f 0 := by
    funext z; simp
  refine exactDifferentialOrder_entireCascade_of_circleComparison hall h1 (fun m => ?_) helim
  match m with
  | 0 => exact circleComparison_zeroth_edge (fun z => rfl)
  | 1 =>
      refine circleComparison_first_edge (fun z => rfl) ?_
      rw [hone]
      exact hall 0
  | (k + 2) => exact hcirc _ (by omega)

end GaloisForLFunctions.HTGeometry
