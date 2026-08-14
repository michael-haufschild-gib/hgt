import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum

/-!
# Route P: the post-subquantum trace-capacity gate is exactly RH

P-G175 proves that the complete primitive Euler collision budget is smaller than the least cubic
charge of one strict-right Xi copy.  This module audits the logical status of the proposed
source-to-zero trace contraction after that estimate.

For every finite packet of actual strict-right multiplicity copies, form the full non-diagonal
collision Gram using their centered horizontal displacements and ordinates.  Its trace is the sum
of their exact cubic charges.  The assertion that every such target trace fits inside the primitive
Euler budget is equivalent to RH: under RH the packet type is empty, while one strict-right copy
already costs more than the entire source.

Thus trace capacity is a terminal receiver, not the missing arithmetic producer.  Any successful
continuation of Route P must construct an earlier coefficient-faithful source mechanism whose
capacity consequence follows as a theorem; it cannot take this law as an independent premise.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Cubic collision Gram on a finite packet of actual strict-right Xi copies. -/
def routePStrictRightZeroCollisionCubicKernelMatrix {N : ℕ}
    (q : Fin N → XiRightZeroCopy) : Matrix (Fin N) (Fin N) ℂ :=
  routePCollisionCubicKernelMatrix 1
    (fun i => (xiRightCenteredZero (q i)).re)
    (fun i => (xiRightCenteredZero (q i)).im)

/-- Exact target trace, retaining every strict-right multiplicity copy. -/
theorem re_trace_routePStrictRightZeroCollisionCubicKernelMatrix
    {N : ℕ} (q : Fin N → XiRightZeroCopy) :
    (routePStrictRightZeroCollisionCubicKernelMatrix q).trace.re =
      ∑ i : Fin N,
        115 / (864 * (xiRightCenteredZero (q i)).re ^ 3) := by
  have h := trace_routePCollisionCubicKernelMatrix
    (N := N) (R := 1)
    (a := fun i => (xiRightCenteredZero (q i)).re)
    (kappa := fun i => (xiRightCenteredZero (q i)).im)
    (by norm_num) (fun i => xiRightCenteredZero_re_pos (q i))
  change (routePStrictRightZeroCollisionCubicKernelMatrix q).trace = _ at h
  rw [h]
  change Complex.reCLM (∑ i : Fin N,
      ((115 / (864 * (xiRightCenteredZero (q i)).re ^ 3) : ℝ) : ℂ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  norm_cast

/-- Trace-capacity consequence required from any proposed P-G175 contraction. -/
def RoutePPrimitiveCollisionTraceCapacityLaw : Prop :=
  ∀ {N : ℕ} (q : Fin N → XiRightZeroCopy),
    (routePStrictRightZeroCollisionCubicKernelMatrix q).trace.re ≤
      routePPrimitiveCollisionCubicTraceBudget

/-- **P-G176.** After the subquantum estimate, the remaining trace-capacity law is exactly RH. -/
theorem routePPrimitiveCollisionTraceCapacityLaw_iff_riemannHypothesis :
    RoutePPrimitiveCollisionTraceCapacityLaw ↔ RiemannHypothesis := by
  constructor
  · intro hcapacity
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    have hcap := hcapacity (N := 1) (fun _ => q)
    rw [re_trace_routePStrictRightZeroCollisionCubicKernelMatrix] at hcap
    simp only [Fin.sum_univ_one] at hcap
    have ha : 0 < (xiRightCenteredZero q).re :=
      xiRightCenteredZero_re_pos q
    have hhalf : (xiRightCenteredZero q).re ≤ 1 / 2 :=
      le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
    have hquant :=
      cubicLogMomentHellingerHorizontalKernel_self_ge ha hhalf
    rw [cubicLogMomentHellingerHorizontalKernel_self ha] at hquant
    linarith [routePPrimitiveCollisionCubicTraceBudget_lt_quantum]
  · intro hRH N q
    letI : IsEmpty XiRightZeroCopy := by
      constructor
      intro x
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH x.1
      have hpos := x.2
      rw [ht] at hpos
      simp at hpos
    letI : IsEmpty (Fin N) := ⟨fun i => isEmptyElim (q i)⟩
    rw [re_trace_routePStrictRightZeroCollisionCubicKernelMatrix]
    simpa using routePPrimitiveCollisionCubicTraceBudget_nonneg

end

end RHTower
