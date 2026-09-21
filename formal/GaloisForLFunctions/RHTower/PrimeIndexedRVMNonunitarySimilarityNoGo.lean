import GaloisForLFunctions.RHTower.PrimeIndexedRVMSourceUnitaryNoGo

/-!
# Prime-source RVM bounded-similarity obstruction

The Route K cubic trace obstruction does not depend on preservation of the
Hilbert metric.  It excludes every bounded invertible similarity that would
send a literal cofinal prime triangle tail to its negative.  Indeed, cyclicity
of the trace preserves the ordinary trace of every trace-class operator under
such a similarity; applying this to the cubic tail contradicts its nonzero
trace.

Thus a viable nonorthogonal K-RVM correction cannot be an isospectral bounded
similarity of the literal source tail.  It must alter the carrier or use a
non-similarity assembly while retaining a nonvanishing Xi divisor.
-/

namespace RHTower

noncomputable section

/-- Push an operator through a bounded invertible continuous linear change of
coordinates. -/
def routeKBoundedSimilarityPush
    (u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert)
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  u.toContinuousLinearMap ∘L T ∘L u.symm.toContinuousLinearMap

@[simp] theorem routeKBoundedSimilarityPush_apply
    (u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert)
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (x : RouteKPrimeHilbert) :
    routeKBoundedSimilarityPush u T x = u (T (u.symm x)) := by
  rfl

/-- Bounded similarities preserve products of Route K endomorphisms. -/
@[simp] theorem routeKBoundedSimilarityPush_mul
    (u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert)
    (A B : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) :
    routeKBoundedSimilarityPush u (A * B) =
      routeKBoundedSimilarityPush u A * routeKBoundedSimilarityPush u B := by
  ext x
  simp [routeKBoundedSimilarityPush, mul_apply_eq_comp]

/-- Ordinary trace is invariant under every bounded Route K similarity of a
trace-class operator. -/
theorem opTrace_routeKBoundedSimilarityPush_of_memSchattenClass_one
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hT : MemSchattenClass 1 T)
    (u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert) :
    ContinuousLinearMap.opTrace (routeKBoundedSimilarityPush u T) =
      ContinuousLinearMap.opTrace T := by
  rw [routeKBoundedSimilarityPush]
  let U : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    u.toContinuousLinearMap
  let V : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    u.symm.toContinuousLinearMap
  change ContinuousLinearMap.opTrace (U ∘L (T ∘L V)) =
    ContinuousLinearMap.opTrace T
  calc
    ContinuousLinearMap.opTrace (U ∘L (T ∘L V)) =
        ContinuousLinearMap.opTrace ((T ∘L V) ∘L U) := by
      exact (memSchattenClass_one_comp_right hT V).one_opTrace_comp_comm U
    _ = ContinuousLinearMap.opTrace T := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp [U, V]

/-- A trace-class Route K carrier with nonzero trace cannot be carried to its
negative by any bounded invertible similarity. -/
theorem not_exists_routeKBoundedSimilarityPush_eq_neg_of_memSchattenClass_one_opTrace_ne_zero
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hT : MemSchattenClass 1 T)
    (htrace : ContinuousLinearMap.opTrace T ≠ 0) :
    ¬ ∃ u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert,
      routeKBoundedSimilarityPush u T = -T := by
  rintro ⟨u, hu⟩
  have hinvariant :=
    opTrace_routeKBoundedSimilarityPush_of_memSchattenClass_one T hT u
  rw [hu, opTrace_neg] at hinvariant
  apply htrace
  have hdouble : (2 : ℂ) * ContinuousLinearMap.opTrace T = 0 := by
    calc
      (2 : ℂ) * ContinuousLinearMap.opTrace T =
          ContinuousLinearMap.opTrace T + ContinuousLinearMap.opTrace T := by ring
      _ = ContinuousLinearMap.opTrace T + (-ContinuousLinearMap.opTrace T) := by
        rw [hinvariant]
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

/-- No bounded invertible similarity can reverse a complete literal cofinal
prime-triangle tail: its nonzero cubic trace is similarity invariant. -/
theorem not_exists_routeKBoundedSimilarityPush_neg_routeKCofinalTriangleNuclearCarrierFrom
    (K : ℕ) :
    ¬ ∃ u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert,
      routeKBoundedSimilarityPush u (routeKCofinalTriangleNuclearCarrierFrom K) =
        -routeKCofinalTriangleNuclearCarrierFrom K := by
  rintro ⟨u, hu⟩
  have hcube :
      routeKBoundedSimilarityPush u
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          (routeKCofinalTriangleNuclearCarrierFrom K ∘L
            routeKCofinalTriangleNuclearCarrierFrom K)) =
        -(routeKCofinalTriangleNuclearCarrierFrom K ∘L
          (routeKCofinalTriangleNuclearCarrierFrom K ∘L
            routeKCofinalTriangleNuclearCarrierFrom K)) := by
    change routeKBoundedSimilarityPush u
      (routeKCofinalTriangleNuclearCarrierFrom K *
        (routeKCofinalTriangleNuclearCarrierFrom K *
          routeKCofinalTriangleNuclearCarrierFrom K)) =
      -(routeKCofinalTriangleNuclearCarrierFrom K *
        (routeKCofinalTriangleNuclearCarrierFrom K *
          routeKCofinalTriangleNuclearCarrierFrom K))
    rw [routeKBoundedSimilarityPush_mul, routeKBoundedSimilarityPush_mul, hu]
    noncomm_ring
  apply
    not_exists_routeKBoundedSimilarityPush_eq_neg_of_memSchattenClass_one_opTrace_ne_zero
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K))
      (memSchattenClass_one_comp_left
        (memSchattenClass_one_comp_left
          (routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one K)
          (routeKCofinalTriangleNuclearCarrierFrom K))
        (routeKCofinalTriangleNuclearCarrierFrom K))
      (opTrace_routeKCofinalTriangleNuclearCarrierFrom_cube_ne_zero K)
  exact ⟨u, hcube⟩

/-- Every cofinal Route K cut excludes bounded-similarity sign reversal of a
literal source tail. -/
theorem exists_cofinal_routeKCofinalTriangleNuclearCarrierFrom_no_boundedSimilarityPush_neg
    (N : ℕ) :
    ∃ K : ℕ, N ≤ K ∧
      ¬ ∃ u : RouteKPrimeHilbert ≃L[ℂ] RouteKPrimeHilbert,
        routeKBoundedSimilarityPush u (routeKCofinalTriangleNuclearCarrierFrom K) =
          -routeKCofinalTriangleNuclearCarrierFrom K := by
  exact ⟨N, le_rfl,
    not_exists_routeKBoundedSimilarityPush_neg_routeKCofinalTriangleNuclearCarrierFrom N⟩

end

end RHTower
