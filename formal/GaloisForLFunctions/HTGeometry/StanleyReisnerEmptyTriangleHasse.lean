import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.StanleyReisnerEmptyTriangleRank

/-!
# An ABHN-style exact sequence for an empty Stanley--Reisner triangle

Three local syzygy coefficients have one complete obstruction: their sum.  The two-parameter
global map parametrizes every zero-sum coefficient packet, and the empty-triangle rank theorem
identifies those packets exactly with first Koszul boundaries.  Consequently local coefficient
packets modulo boundaries form one copy of the coefficient ring's additive group.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- Two global parameters generate a zero-sum triple of local coefficients. -/
def srEmptyTriangleGlobalCoefficients : (R × R) →+ (Fin 3 → R) where
  toFun p := ![-(p.1 + p.2), p.1, p.2]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' p q := by
    funext i
    fin_cases i
    · simp
      ring
    · simp
    · simp

@[simp]
theorem srEmptyTriangleGlobalCoefficients_zero (p : R × R) :
    srEmptyTriangleGlobalCoefficients (R := R) p 0 = -(p.1 + p.2) := rfl

@[simp]
theorem srEmptyTriangleGlobalCoefficients_one (p : R × R) :
    srEmptyTriangleGlobalCoefficients (R := R) p 1 = p.1 := rfl

@[simp]
theorem srEmptyTriangleGlobalCoefficients_two (p : R × R) :
    srEmptyTriangleGlobalCoefficients (R := R) p 2 = p.2 := rfl

/-- Coefficient sum is the empty-triangle obstruction. -/
def srEmptyTriangleCoefficientObstruction : (Fin 3 → R) →+ R where
  toFun l := l 0 + l 1 + l 2
  map_zero' := by simp
  map_add' x y := by simp; ring

@[simp]
theorem srEmptyTriangleCoefficientObstruction_apply (l : Fin 3 → R) :
    srEmptyTriangleCoefficientObstruction (R := R) l = l 0 + l 1 + l 2 := rfl

/-- The global coefficient map and coefficient-sum obstruction are exact. -/
theorem srEmptyTriangleCoefficient_exact :
    Function.Exact (srEmptyTriangleGlobalCoefficients (R := R))
      (srEmptyTriangleCoefficientObstruction (R := R)) := by
  apply AddMonoidHom.exact_iff.mpr
  ext l
  constructor
  · intro hl
    change l 0 + l 1 + l 2 = 0 at hl
    refine ⟨(l 1, l 2), ?_⟩
    funext i
    fin_cases i
    · change -(l 1 + l 2) = l 0
      linear_combination -hl
    · rfl
    · rfl
  · rintro ⟨p, rfl⟩
    change srEmptyTriangleCoefficientObstruction (R := R)
      (srEmptyTriangleGlobalCoefficients (R := R) p) = 0
    simp

/-- Every obstruction value is represented by a local coefficient packet. -/
theorem srEmptyTriangleCoefficientObstruction_surjective :
    Function.Surjective
      (srEmptyTriangleCoefficientObstruction (R := R) : (Fin 3 → R) → R) := by
  intro r
  refine ⟨![r, 0, 0], ?_⟩
  simp

/-- Local coefficient triples modulo globally generated zero-sum triples equal the obstruction
group. -/
noncomputable def srEmptyTriangleHasseQuotientEquiv :
    ((Fin 3 → R) ⧸ (srEmptyTriangleGlobalCoefficients (R := R)).range) ≃+ R :=
  addHasseQuotientEquiv (srEmptyTriangleGlobalCoefficients (R := R))
    (srEmptyTriangleCoefficientObstruction (R := R))
    (srEmptyTriangleCoefficient_exact (R := R))
    (srEmptyTriangleCoefficientObstruction_surjective (R := R))

@[simp]
theorem srEmptyTriangleHasseQuotientEquiv_mk (l : Fin 3 → R) :
    srEmptyTriangleHasseQuotientEquiv (R := R) (QuotientAddGroup.mk l) =
      srEmptyTriangleCoefficientObstruction (R := R) l :=
  addHasseQuotientEquiv_mk (srEmptyTriangleGlobalCoefficients (R := R))
    (srEmptyTriangleCoefficientObstruction (R := R))
    (srEmptyTriangleCoefficient_exact (R := R))
    (srEmptyTriangleCoefficientObstruction_surjective (R := R)) l

/-- Empty-triangle local packets are congruent modulo global packets exactly when their obstruction
sums agree. -/
theorem srEmptyTriangleCoefficient_congr_hasse_iff (x y : Fin 3 → R) :
    x - y ∈ (srEmptyTriangleGlobalCoefficients (R := R)).range ↔
      srEmptyTriangleCoefficientObstruction (R := R) x =
        srEmptyTriangleCoefficientObstruction (R := R) y :=
  addHasse_congr_iff (srEmptyTriangleGlobalCoefficients (R := R))
    (srEmptyTriangleCoefficientObstruction (R := R))
    (srEmptyTriangleCoefficient_exact (R := R)) x y

variable {alpha : Type*} [DecidableEq alpha] [Fintype alpha]

/-- **Koszul Hasse criterion.**  On an empty triangle, a local syzygy coefficient packet is a
first Koszul boundary exactly when its obstruction class vanishes. -/
theorem srEmptyTriangleSyzygyVec_boundary_iff_obstruction_zero
    (facets : Finset (Finset alpha)) {a b c : alpha}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset alpha)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset alpha)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset alpha)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset alpha)) {a})
    (hb : IsFaceOf (↑facets : Set (Finset alpha)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset alpha)) {c}) (la lb lc : R) :
    (∃ cc : alpha → alpha → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc = srEmptyTriangleSyzygyVec R facets a b c la lb lc) ↔
      srEmptyTriangleCoefficientObstruction (R := R) ![la, lb, lc] = 0 := by
  simpa using srEmptyTriangleSyzygyVec_boundary_iff facets hab hac hbc hfab hfbc hfac
    ha hb hc la lb lc

/-- The same Koszul criterion expressed as membership in the globally generated coefficient range. -/
theorem srEmptyTriangleSyzygyVec_boundary_iff_mem_global_range
    (facets : Finset (Finset alpha)) {a b c : alpha}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset alpha)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset alpha)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset alpha)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset alpha)) {a})
    (hb : IsFaceOf (↑facets : Set (Finset alpha)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset alpha)) {c}) (la lb lc : R) :
    (∃ cc : alpha → alpha → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc = srEmptyTriangleSyzygyVec R facets a b c la lb lc) ↔
      (![la, lb, lc] : Fin 3 → R) ∈
        (srEmptyTriangleGlobalCoefficients (R := R)).range := by
  rw [srEmptyTriangleSyzygyVec_boundary_iff_obstruction_zero facets hab hac hbc
    hfab hfbc hfac ha hb hc]
  rw [AddMonoidHom.mem_range]
  constructor
  · intro hzero
    have hker : (![la, lb, lc] : Fin 3 → R) ∈
        (srEmptyTriangleCoefficientObstruction (R := R)).ker :=
      hzero
    rw [AddMonoidHom.exact_iff.mp (srEmptyTriangleCoefficient_exact (R := R))] at hker
    exact hker
  · rintro ⟨p, hp⟩
    have hrange : (![la, lb, lc] : Fin 3 → R) ∈
        (srEmptyTriangleGlobalCoefficients (R := R)).range :=
      ⟨p, hp⟩
    rw [← AddMonoidHom.exact_iff.mp (srEmptyTriangleCoefficient_exact (R := R))] at hrange
    exact hrange

end GaloisForLFunctions.HTGeometry
