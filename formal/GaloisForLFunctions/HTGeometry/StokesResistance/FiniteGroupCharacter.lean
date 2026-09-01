import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Character
import GaloisForLFunctions.HTGeometry.HaarAveragingExactness

/-!
# Finite-group character projection for Stokes resistance

This module formalizes the representation-theoretic core of Moreau,
*The Stokes resistance of an arbitrary particle: a classification of hydrodynamic symmetries*,
arXiv:2608.23907v1, equations (41)--(43), (58), (124)--(125), and (127).

For any finite complex representation, its normalized Reynolds average is a projection onto the
fixed subspace. Its trace is therefore the fixed-space dimension and, by trace linearity, that
dimension is the average of the representation character. Stacking all equations
`rho g v - v = 0` gives a single exact defect map whose kernel is the fixed subspace. Applying the
same result to `Representation.linHom` counts equivariant response maps.

Everything is exact and algebraic: no numerical nullspace, singular-value decomposition, or
hydrodynamic premise enters these theorems.
-/

open MonoidAlgebra Representation

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

variable {G V : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V]

/-- Moreau equation (41): normalized finite-group Reynolds average. -/
def finiteGroupAverage (rho : Representation ℂ G V) : V →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, rho g

@[simp] theorem finiteGroupAverage_apply (rho : Representation ℂ G V) (v : V) :
    finiteGroupAverage rho v =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, rho g v := by
  simp [finiteGroupAverage]

/-- Moreau equation (41): the Reynolds average projects onto the fixed subspace. -/
theorem finiteGroupAverage_isProj (rho : Representation ℂ G V) :
    LinearMap.IsProj rho.invariants (finiteGroupAverage rho) := by
  letI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by simp [Fintype.card_ne_zero])
  have heq : finiteGroupAverage rho = rho.averageMap := by
    ext v
    rw [finiteGroupAverage_apply, GaloisForLFunctions.averageMap_apply]
    simp
  rw [heq]
  exact rho.isProj_averageMap

theorem finiteGroupAverage_mem_invariants (rho : Representation ℂ G V) (v : V) :
    finiteGroupAverage rho v ∈ rho.invariants :=
  (finiteGroupAverage_isProj rho).map_mem v

theorem mem_invariants_iff_finiteGroupAverage_eq_self
    (rho : Representation ℂ G V) (v : V) :
    v ∈ rho.invariants ↔ finiteGroupAverage rho v = v :=
  (finiteGroupAverage_isProj rho).mem_iff_map_id

theorem range_finiteGroupAverage (rho : Representation ℂ G V) :
    LinearMap.range (finiteGroupAverage rho) = rho.invariants :=
  (finiteGroupAverage_isProj rho).range

theorem finiteGroupAverage_idempotent (rho : Representation ℂ G V) :
    finiteGroupAverage rho * finiteGroupAverage rho = finiteGroupAverage rho :=
  (finiteGroupAverage_isProj rho).isIdempotentElem.eq

section FiniteDimension

variable [Module.Free ℂ V] [Module.Finite ℂ V]

omit [Module.Free ℂ V] in
/-- Moreau equation (42), first equality: projector trace is fixed-space dimension. -/
theorem trace_finiteGroupAverage_eq_finrank_invariants (rho : Representation ℂ G V) :
    LinearMap.trace ℂ V (finiteGroupAverage rho) =
      (Module.finrank ℂ rho.invariants : ℂ) :=
  (finiteGroupAverage_isProj rho).trace

omit [Module.Free ℂ V] in
/-- Moreau equation (42): fixed-space dimension is the average of the character. -/
theorem finrank_invariants_eq_character_average (rho : Representation ℂ G V) :
    (Module.finrank ℂ rho.invariants : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ V (rho g) := by
  rw [← trace_finiteGroupAverage_eq_finrank_invariants rho]
  rw [finiteGroupAverage, map_smul, map_sum]
  simp [smul_eq_mul]

/-- Moreau equations (43) and (124): all invariance defects as one linear map. -/
def invarianceDefect (rho : Representation ℂ G V) : V →ₗ[ℂ] (G → V) :=
  LinearMap.pi fun g => rho g - LinearMap.id

omit [Fintype G] [Module.Free ℂ V] [Module.Finite ℂ V] in
@[simp] theorem invarianceDefect_apply (rho : Representation ℂ G V) (v : V) (g : G) :
    invarianceDefect rho v g = rho g v - v := by
  simp [invarianceDefect]

omit [Fintype G] [Module.Free ℂ V] [Module.Finite ℂ V] in
theorem ker_invarianceDefect (rho : Representation ℂ G V) :
    LinearMap.ker (invarianceDefect rho) = rho.invariants := by
  ext v
  simp only [LinearMap.mem_ker, Representation.mem_invariants]
  constructor
  · intro hv g
    have h := congrFun hv g
    exact sub_eq_zero.mp (by simpa using h)
  · intro hv
    funext g
    simp [invarianceDefect_apply, hv g]

omit [Fintype G] [Module.Free ℂ V] in
/-- Moreau equations (43) and (125): exact nullity-rank count for stacked constraints. -/
theorem finrank_invariants_add_finrank_defectRange (rho : Representation ℂ G V) :
    Module.finrank ℂ rho.invariants + Module.finrank ℂ (LinearMap.range (invarianceDefect rho)) =
      Module.finrank ℂ V := by
  rw [← ker_invarianceDefect rho, add_comm]
  exact (invarianceDefect rho).finrank_range_add_finrank_ker

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Module.Free ℂ W] [Module.Finite ℂ W]

omit [Module.Free ℂ W] in
/-- Moreau equations (58), (75), and (127): equivariant-map parameter count by character average. -/
theorem finrank_intertwiningMap_eq_character_average
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
        LinearMap.trace ℂ (V →ₗ[ℂ] W) ((Representation.linHom rho sigma) g) := by
  rw [← LinearEquiv.finrank_eq (Representation.invariantsEquivIntertwiningMap rho sigma)]
  exact finrank_invariants_eq_character_average (Representation.linHom rho sigma)

omit [Module.Free ℂ W] in
/-- Moreau's equivariant-response count in ordinary character coordinates. This is also the
finite-group character pairing used by Artin-representation modules in the corpus. -/
theorem finrank_intertwiningMap_eq_character_product_average
    (rho : Representation ℂ G V) (sigma : Representation ℂ G W) :
    (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g : G,
        rho.character g⁻¹ * sigma.character g := by
  rw [finrank_intertwiningMap_eq_character_average]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact Representation.char_linHom rho sigma g

end FiniteDimension

end GaloisForLFunctions.HTGeometry.StokesResistance
