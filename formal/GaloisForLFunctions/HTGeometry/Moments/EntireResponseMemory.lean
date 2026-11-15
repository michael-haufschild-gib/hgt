import GaloisForLFunctions.HTGeometry.Moments.AnalyticLeadingMinors
import GaloisForLFunctions.HTGeometry.Moments.DelayedGeometricMemory

/-!
# Entire realizations of finite Hankel memory

A sequence whose leading Hankel determinants eventually vanish has an entire
exponential generating function. Its derivatives recover the original sequence,
and the function is an exponential polynomial. Thus finite state-space responses
have canonical entire realizations without an extra convergence assumption.

For a geometric sequence delayed by `d`, the last nonzero derivative Hankel block
has size `d + 1`. Its entire realization satisfies `f^(d+1) = q f^d`, and no nonzero
constant-coefficient differential operator of smaller order annihilates even its
germ at zero. This includes `q = 0` and every delay.
-/

open Filter Topology
open scoped BigOperators Matrix
open _root_.HTGeometry.FiniteHankel

namespace GaloisForLFunctions.HTGeometry

/-- A leading-minor cutoff implies infinite radius for the exponential generating series. -/
theorem responseTaylor_radius_top_of_leading_tail {s : ℕ → ℂ} {B : ℕ}
    (ht : ∀ n, B < n → leadingDet s n = 0) :
    (FormalMultilinearSeries.ofScalars ℂ (responseTaylorCoeff s)).radius = ⊤ := by
  have hr := (seqConstantRecurrence_iff_leading_tail s).mpr ⟨B, ht⟩
  obtain ⟨C, R, hC, hR, hbound⟩ := exists_geometric_bound_of_seqConstantRecurrence hr
  exact radius_ofScalars_taylorCoeff_eq_top hC hR hbound

/-- The canonical response is entire whenever its sequence has finite Hankel memory. -/
theorem responseTaylor_entire_of_leading_tail {s : ℕ → ℂ} {B : ℕ}
    (ht : ∀ n, B < n → leadingDet s n = 0) :
    ∀ z, AnalyticAt ℂ (responseTaylorFun s) z := by
  have hrad := responseTaylor_radius_top_of_leading_tail ht
  intro z
  exact (hasFPowerSeriesOnBall_taylorFun hrad).analyticOnNhd z (by
    rw [Metric.mem_eball]
    exact edist_lt_top _ _)

/-- All derivatives at zero recover the prescribed finite-memory sequence. -/
theorem respSeq_responseTaylor_of_leading_tail {s : ℕ → ℂ} {B : ℕ}
    (ht : ∀ n, B < n → leadingDet s n = 0) : respSeq (responseTaylorFun s) = s := by
  funext n
  exact iteratedDeriv_taylorFun (responseTaylor_radius_top_of_leading_tail ht) n

/-- The entire finite-memory response is an exponential polynomial. -/
theorem responseTaylor_mem_expPolySpaceC_of_leading_tail {s : ℕ → ℂ} {B : ℕ}
    (ht : ∀ n, B < n → leadingDet s n = 0) : responseTaylorFun s ∈ expPolySpaceC := by
  apply (mem_expPolySpaceC_iff_entire_leading_tail _).mpr
  refine ⟨responseTaylor_entire_of_leading_tail ht, B, ?_⟩
  rw [respSeq_responseTaylor_of_leading_tail ht]
  exact ht

/-- Finite Hankel memory is equivalent to exact realization by the canonical exponential polynomial. -/
theorem leading_tail_iff_responseTaylor_expPoly (s : ℕ → ℂ) :
    (∃ B, ∀ n, B < n → leadingDet s n = 0) ↔
      responseTaylorFun s ∈ expPolySpaceC ∧ respSeq (responseTaylorFun s) = s := by
  constructor
  · rintro ⟨B, ht⟩
    exact ⟨responseTaylor_mem_expPolySpaceC_of_leading_tail ht,
      respSeq_responseTaylor_of_leading_tail ht⟩
  · rintro ⟨hf, hjet⟩
    have ht := (mem_expPolySpaceC_iff_entire_leading_tail _).mp hf |>.2
    rwa [hjet] at ht

/-- Every finite matrix observation has an entire exponential-polynomial realization with the same jets. -/
theorem finiteState_responseTaylor_expPoly {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (input output : Fin d → ℂ) :
    responseTaylorFun (_root_.HTGeometry.algebraicStateSpaceResponse A input output) ∈ expPolySpaceC ∧
      respSeq (responseTaylorFun (_root_.HTGeometry.algebraicStateSpaceResponse A input output)) =
        _root_.HTGeometry.algebraicStateSpaceResponse A input output := by
  have hs : _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost d
      (_root_.HTGeometry.algebraicStateSpaceResponse A input output) := ⟨A, input, output, rfl⟩
  exact (leading_tail_iff_responseTaylor_expPoly _).mp
    ⟨d, leading_tail_zero_of_stateSpace hs⟩

/-- A `d`-state observation has a global monic differential equation of order at most `d`. -/
theorem finiteState_responseTaylor_globalODE {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (input output : Fin d → ℂ) :
    ∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree ≤ d ∧
      ∀ z, odeSum p.coeff p.natDegree
        (responseTaylorFun (_root_.HTGeometry.algebraicStateSpaceResponse A input output)) z = 0 := by
  have hs : _root_.HTGeometry.AlgebraicStateSpaceDimensionAtMost d
      (_root_.HTGeometry.algebraicStateSpaceResponse A input output) := ⟨A, input, output, rfl⟩
  have ht := leading_tail_zero_of_stateSpace hs
  obtain ⟨E, horder, hE⟩ := (leading_tail_zero_iff_recurrence _ d).mp ht
  refine ⟨E.charPoly, E.charPoly_monic, (charPoly_natDegree E).le.trans horder, ?_⟩
  apply (polynomial_response_relation_iff_globalODE (responseTaylor_entire_of_leading_tail ht) _).mp
  rw [respSeq_responseTaylor_of_leading_tail ht]
  exact charPoly_relation E hE

/-- Entire realization of a geometric derivative sequence delayed by `d`. -/
noncomputable def delayedEntireResponse (q : ℂ) (d : ℕ) : ℂ → ℂ :=
  responseTaylorFun (delayedGeometric q d)

/-- The delayed geometric response is an exponential polynomial for every ratio and delay. -/
theorem delayedEntireResponse_mem_expPolySpaceC (q : ℂ) (d : ℕ) :
    delayedEntireResponse q d ∈ expPolySpaceC :=
  responseTaylor_mem_expPolySpaceC_of_leading_tail (delayedGeometric_leading_tail_zero q d)

/-- Delayed geometric response series converge to entire functions. -/
theorem delayedEntireResponse_entire (q : ℂ) (d : ℕ) (z : ℂ) :
    AnalyticAt ℂ (delayedEntireResponse q d) z :=
  responseTaylor_entire_of_leading_tail (delayedGeometric_leading_tail_zero q d) z

/-- The derivatives are zero before the delay and geometric from the delay onward. -/
theorem delayedEntireResponse_jets (q : ℂ) (d : ℕ) :
    respSeq (delayedEntireResponse q d) = delayedGeometric q d :=
  respSeq_responseTaylor_of_leading_tail (delayedGeometric_leading_tail_zero q d)

/-- Only the empty block and the block of size `d + 1` have nonzero leading determinants. -/
theorem delayedEntireResponse_hankel_pattern (q : ℂ) (d n : ℕ) :
    leadingDet (respSeq (delayedEntireResponse q d)) n ≠ 0 ↔ n = 0 ∨ n = d + 1 := by
  rw [delayedEntireResponse_jets]
  exact delayedGeometric_leadingDet_ne_zero_iff q d n

/-- The exact minimum constant-coefficient ODE order is `d + 1`, even locally. -/
theorem delayedEntireResponse_minimalODE (q : ℂ) (d : ℕ) :
    (∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = d + 1 ∧
      ∀ z, odeSum p.coeff p.natDegree (delayedEntireResponse q d) z = 0) ∧
    (∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ᶠ z in 𝓝 (0 : ℂ), odeSum p.coeff p.natDegree (delayedEntireResponse q d) z = 0) →
      d + 1 ≤ p.natDegree) := by
  have hm : leadingDet (respSeq (delayedEntireResponse q d)) (d + 1) ≠ 0 := by
    rw [delayedEntireResponse_jets]
    exact delayedGeometric_leadingDet_onset_ne_zero q d
  have ht : ∀ n, d + 1 < n → leadingDet (respSeq (delayedEntireResponse q d)) n = 0 := by
    rw [delayedEntireResponse_jets]
    exact delayedGeometric_leading_tail_zero q d
  obtain ⟨⟨p, hp, hdeg, hnear⟩, hmin⟩ :=
    localODE_minimalDegree_of_last_leading_det (delayedEntireResponse_entire q d 0) (d + 1) hm ht
  refine ⟨⟨p, hp, hdeg, ?_⟩, hmin⟩
  exact (polynomial_response_relation_iff_globalODE (delayedEntireResponse_entire q d) p).mp
    ((polynomial_response_relation_iff_localODE (delayedEntireResponse_entire q d 0) p).mpr hnear)

/-- The delayed response satisfies the global equation `f^(d+1) = q f^d`. -/
theorem delayedEntireResponse_ode (q : ℂ) (d : ℕ) (z : ℂ) :
    iteratedDeriv (d + 1) (delayedEntireResponse q d) z =
      q * iteratedDeriv d (delayedEntireResponse q d) z := by
  have hrec := charPoly_relation (delayedGeometricRecurrence q d) (delayedGeometric_isSolution q d)
  rw [← delayedEntireResponse_jets q d] at hrec
  have hzero := (polynomial_response_relation_iff_globalODE
    (delayedEntireResponse_entire q d) (delayedGeometricRecurrence q d).charPoly).mp hrec z
  have he := charPoly_sum_eq (delayedGeometricRecurrence q d)
    (fun k => iteratedDeriv k (delayedEntireResponse q d) z) 0
  simp only [Nat.zero_add] at he
  dsimp only [odeSum] at hzero
  rw [he] at hzero
  have h := sub_eq_zero.mp hzero
  simpa only [delayedGeometricRecurrence, Pi.single_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_last] using h

#print axioms leading_tail_iff_responseTaylor_expPoly
#print axioms finiteState_responseTaylor_expPoly
#print axioms finiteState_responseTaylor_globalODE
#print axioms delayedEntireResponse_minimalODE
#print axioms delayedEntireResponse_ode

end GaloisForLFunctions.HTGeometry
