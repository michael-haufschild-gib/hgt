import GaloisForLFunctions.HTGeometry.EigenBlockSupport

/-!
# A parameter-independent product frame

If a family of product frames all diagonalise one fixed operator with simple spectrum, then the
local factor lines do not depend on the parameter: every left frame vector at one parameter is
proportional to a left frame vector at any other, and likewise on the right.

Two facts combine.  Every eigenvalue of the operator is realised in every eigenbasis — otherwise an
eigenvector would have all coordinates zero — so the grid point of one frame can be matched to a
grid point of the other carrying the same eigenvalue.  A simple eigenvalue then has a unique
eigenline, and a decomposable tensor determines its two factor lines, so the matched vectors have
proportional factors.

The correspondence between grid points is not claimed to be the identity; only the lines are
matched, which is what a diagonalising product frame requires.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K : Type*} [Field K]

/-! ### Every eigenvalue is realised in every eigenbasis -/

variable {V ι : Type*} [AddCommGroup V] [Module K V]

/-- A nonzero eigenvector forces its eigenvalue to occur among the eigenvalues of any eigenbasis. -/
theorem exists_index_eigenvalue_eq [DecidableEq ι] (e : Basis ι K V)
    {T : Module.End K V} {ν : ι → K} (hT : ∀ q, T (e q) = ν q • e q)
    {lam : K} {v : V} (hv0 : v ≠ 0) (hv : T v = lam • v) :
    ∃ q, ν q = lam := by
  by_contra hcon
  refine hv0 ?_
  have hrepr : e.repr v = 0 := by
    ext q
    have hq : ν q ≠ lam := fun h => hcon ⟨q, h⟩
    simpa using repr_eq_zero_of_eigenvalue_ne e hT hv hq
  have := congrArg e.repr.symm hrepr
  simpa using this

/-! ### The factor lines do not depend on the parameter -/

variable {I J : Type*}

/-- **Parameter-independent factor lines.**  Let one operator be diagonalised by two product frames,
the second with simple spectrum.  Then every left vector of the first frame is proportional to a
left vector of the second, and likewise on the right. -/
theorem productFrame_factors_matched [DecidableEq I] [DecidableEq J]
    {T : Module.End K (Matrix I J K)}
    {a : I → (I → K)} {b : J → (J → K)} {a' : I → (I → K)} {b' : J → (J → K)}
    (e' : Basis (I × J) K (Matrix I J K))
    (he' : ∀ q, e' q = criticalHorizonSegreTensor (a' q.1) (b' q.2))
    {ν' : I × J → K} (hT' : ∀ q, T (e' q) = ν' q • e' q) (hν' : Function.Injective ν')
    {p : I × J} {lam : K}
    (hp0 : criticalHorizonSegreTensor (a p.1) (b p.2) ≠ 0)
    (hp : T (criticalHorizonSegreTensor (a p.1) (b p.2)) =
      lam • criticalHorizonSegreTensor (a p.1) (b p.2)) :
    ∃ q : I × J, (∃ α : K, α ≠ 0 ∧ a p.1 = α • a' q.1) ∧
      (∃ β : K, β ≠ 0 ∧ b p.2 = β • b' q.2) := by
  obtain ⟨q, hq⟩ := exists_index_eigenvalue_eq e' hT' hp0 hp
  refine ⟨q, ?_⟩
  have hane : a p.1 ≠ 0 := by
    intro h
    exact hp0 ((criticalHorizonSegreTensor_eq_zero_iff _ _).mpr (Or.inl h))
  have hbne : b p.2 ≠ 0 := by
    intro h
    exact hp0 ((criticalHorizonSegreTensor_eq_zero_iff _ _).mpr (Or.inr h))
  have hq0 : criticalHorizonSegreTensor (a' q.1) (b' q.2) ≠ 0 := by
    rw [← he' q]
    exact e'.ne_zero q
  have ha'ne : a' q.1 ≠ 0 := by
    intro h
    exact hq0 ((criticalHorizonSegreTensor_eq_zero_iff _ _).mpr (Or.inl h))
  have hb'ne : b' q.2 ≠ 0 := by
    intro h
    exact hq0 ((criticalHorizonSegreTensor_eq_zero_iff _ _).mpr (Or.inr h))
  have hpq : T (criticalHorizonSegreTensor (a p.1) (b p.2)) =
      ν' q • criticalHorizonSegreTensor (a p.1) (b p.2) := by
    rw [hq]
    exact hp
  have hq' : T (criticalHorizonSegreTensor (a' q.1) (b' q.2)) =
      ν' q • criticalHorizonSegreTensor (a' q.1) (b' q.2) := by
    have := hT' q
    rwa [he' q] at this
  exact decomposableEigenvector_factors_proportional e' hT' hν' hane hbne ha'ne hb'ne hpq hq'

/-! ### The degenerate branch

Without simple spectrum the eigenline of a decomposable eigenvector need not be unique, so the two
factors cannot both be matched.  What survives is the axis dichotomy: any grid point of the second
frame carrying a different eigenvalue forces one of the two factors onto an axis of that frame. -/

/-- **Parameter-independence, degenerate branch.**  One operator diagonalised by two product frames,
with no assumption on the multiplicities of the second.  If some grid point of the second frame
carries an eigenvalue different from that of a decomposable eigenvector of the first, then one of
the eigenvector's factors lies on an axis of the second frame, away from that grid point. -/
theorem productFrame_factor_on_axis_of_basis
    (fa' fb' : Basis (Fin 2) K (Fin 2 → K))
    (e' : Basis (Fin 2 × Fin 2) K (Matrix (Fin 2) (Fin 2) K))
    (he' : ∀ q, e' q = criticalHorizonSegreTensor (fa' q.1) (fb' q.2))
    {T : Module.End K (Matrix (Fin 2) (Fin 2) K)} {ν' : Fin 2 × Fin 2 → K}
    (hT' : ∀ q, T (e' q) = ν' q • e' q)
    {u w : Fin 2 → K} (hu0 : u ≠ 0) (hw0 : w ≠ 0) {lam : K}
    (hv : T (criticalHorizonSegreTensor u w) = lam • criticalHorizonSegreTensor u w)
    {q : Fin 2 × Fin 2} (hq : ν' q ≠ lam) :
    (∃ (i : Fin 2) (c : K), c ≠ 0 ∧ i ≠ q.1 ∧ u = c • fa' i) ∨
      (∃ (j : Fin 2) (d : K), d ≠ 0 ∧ j ≠ q.2 ∧ w = d • fb' j) := by
  have hu : u = ∑ i, (fa'.repr u i) • fa' i := (fa'.sum_repr u).symm
  have hw : w = ∑ j, (fb'.repr w j) • fb' j := (fb'.sum_repr w).symm
  exact productFrame_factor_on_axis e' he' hT' hu hw hu0 hw0 hv hq

end GaloisForLFunctions.HTGeometry
