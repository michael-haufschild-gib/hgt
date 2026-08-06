import GaloisForLFunctions.HTGeometry.TwistedGaugeAction
import GaloisForLFunctions.HTGeometry.SourceCoboundaryOperatorBridge

/-!
# Diagonal curved families are flat after logarithmic differentiation

A homogeneous scalar twisted observable — one transformed in every source direction by
multiplication by a base element — has a logarithmic derivative which shifts *additively*, by the
logarithmic derivative of the twist.  Applied coordinatewise to a family whose adjoint local
system has been gauged to a diagonal one, this turns a curved datum into a flat one without any
cocycle equation: the boundary classes of the curved family are the classes of the logarithmic
derivatives of its twists.

The passage loses no differential rank, because an element and its logarithmic derivative are
mutually differentially algebraic.  So the whole flat source-boundary theory computes the rank of
a diagonalizable homogeneous curved family, with the logarithmic derivatives of the diagonal
twists as its boundary data.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

variable {κ : Type u} [Fintype κ]

/-- The logarithmic derivative of a family. -/
def logDerivFamily (y : κ → L) (p : κ) : L := (y p)′ / y p

/-- The logarithmic derivative of a family of twists. -/
def logDerivTwist (m : I → κ → K) (i : I) (p : κ) : K := (m i p)′ / m i p

/-! ### The curved scalar law becomes flat -/

omit [Fintype κ] in
/-- **A homogeneous diagonal curved family is flat after logarithmic differentiation.**  Its
increments are the logarithmic derivatives of the diagonal twists. -/
theorem logDerivFamily_shift {y : κ → L} {m : I → κ → K}
    (hderiv : ∀ i w, sigma i w′ = (sigma i w)′)
    (hy : ∀ p, y p ≠ 0) (hm : ∀ i p, m i p ≠ 0)
    (hmul : ∀ i p, sigma i (y p) = algebraMap K L (m i p) * y p) (i : I) (p : κ) :
    sigma i (logDerivFamily y p)
      = logDerivFamily y p + algebraMap K L (logDerivTwist m i p) :=
  GaloisForLFunctions.ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i) (y p) (m i p)
    (hy p) (hm i p) (hmul i p)

/-! ### The passage keeps the differential rank -/

omit [Fintype κ] in
theorem differentialClosure_logDerivFamily [CharZero L] (y : κ → L) :
    differentialClosure K (Set.range (logDerivFamily y))
      = differentialClosure K (Set.range y) := by
  have hlog : Set.range (logDerivFamily y) ⊆ differentialClosure K (Set.range y) := by
    rintro - ⟨p, rfl⟩
    have hmem := (GaloisForLFunctions.HTGeometry.raw_logCoordinate_mutuallyDifferentialAlgebraic
      (F := K) (y p)).2
    exact GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_mono_differentialAdjoin
      (differentialAdjoin K (Set.range y)) (derivationClosed_differentialAdjoin K _)
      (by rintro - rfl; exact subset_differentialAdjoin K _ ⟨p, rfl⟩) hmem
  have hraw : Set.range y ⊆ differentialClosure K (Set.range (logDerivFamily y)) := by
    rintro - ⟨p, rfl⟩
    have hmem := (GaloisForLFunctions.HTGeometry.raw_logCoordinate_mutuallyDifferentialAlgebraic
      (F := K) (y p)).1
    exact GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_mono_differentialAdjoin
      (differentialAdjoin K (Set.range (logDerivFamily y)))
      (derivationClosed_differentialAdjoin K _)
      (by rintro - rfl; exact subset_differentialAdjoin K _ ⟨p, rfl⟩) hmem
  refine subset_antisymm ?_ ?_
  · have := differentialClosure_mono (F := K) hlog
    rwa [differentialClosure_idempotent] at this
  · have := differentialClosure_mono (F := K) hraw
    rwa [differentialClosure_idempotent] at this

omit [Fintype κ] in
/-- The logarithmic derivative family has the same differential rank. -/
theorem eRk_logDerivFamily [CharZero L] (y : κ → L) :
    (differentialMatroid K L).eRk (Set.range (logDerivFamily y))
      = (differentialMatroid K L).eRk (Set.range y) := by
  rw [← Matroid.eRk_closure_eq, ← Matroid.eRk_closure_eq (X := Set.range y),
    differentialMatroid_closure_eq_differentialClosure,
    differentialMatroid_closure_eq_differentialClosure,
    differentialClosure_logDerivFamily y]

/-! ### The curved rank law for a diagonal homogeneous family -/

omit [Fintype κ] in
/-- **The curved source-boundary criterion for a diagonal homogeneous family.**  The logarithmic
derivatives are differentially independent exactly when the boundary classes of the logarithmic
derivatives of the twists are independent over the constant-coefficient differential operators. -/
theorem twistedDiagonal_differentialIndependent_iff
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i w, sigma i w′ = (sigma i w)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] {y : κ → L} {m : I → κ → K}
    (hy : ∀ p, y p ≠ 0) (hm : ∀ i p, m i p ≠ 0)
    (hmul : ∀ i p, sigma i (y p) = algebraMap K L (m i p) * y p) :
    DifferentialIndependent K (logDerivFamily y) ↔
      LinearIndependent (Polynomial C)
        (fun p : κ => boundaryClass tau hC hfix hderiv fun i => logDerivTwist m i p) :=
  differentialIndependent_iff_linearIndependent_boundaryClass tau sigma hcomp hderivL hCfixed
    hfixed hC hfix hderiv (logDerivFamily y) (logDerivTwist m)
    (fun i p => logDerivFamily_shift sigma hderivL hy hm hmul i p)

/-- **The curved rank law for a diagonal homogeneous family.**  The differential rank of the
family itself is the rank of the span of the boundary classes of the logarithmic derivatives of
its twists. -/
theorem twistedDiagonal_eRk_eq_rank_span_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i w, sigma i w′ = (sigma i w)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] [CharZero L] [DecidableEq κ] {y : κ → L} {m : I → κ → K}
    (hy : ∀ p, y p ≠ 0) (hm : ∀ i p, m i p ≠ 0)
    (hmul : ∀ i p, sigma i (y p) = algebraMap K L (m i p) * y p) :
    ∃ r : ℕ,
      (differentialMatroid K L).eRk (Set.range y) = r ∧
      Module.rank (Polynomial C) (Submodule.span (Polynomial C)
        (Set.range fun p : κ =>
          boundaryClass tau hC hfix hderiv fun i => logDerivTwist m i p)) = r := by
  obtain ⟨r, hrk, hrank⟩ := eRk_eq_rank_span_boundaryClass tau sigma hcomp hderivL hCfixed hfixed
    hC hfix hderiv (logDerivFamily y) (logDerivTwist m)
    (fun i p => logDerivFamily_shift sigma hderivL hy hm hmul i p)
  exact ⟨r, (eRk_logDerivFamily y).symm.trans hrk, hrank⟩

end

end GaloisForLFunctions.HTGeometry
