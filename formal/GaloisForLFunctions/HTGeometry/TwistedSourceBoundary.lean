import GaloisForLFunctions.HTGeometry.SourceBoundaryRankCardinal

/-!
# The curved source boundary in the flat case

For a possibly noncommutative `D`-group the logarithmic source law is affine rather than additive:
the observables shift by the adjoint action of the source multiplier followed by its logarithmic
derivative.  Such a datum is an affine local system over the base field.

When the adjoint local system is trivializable — when the cocycle equation `τ_i(P) M_i = P` has an
invertible base-valued solution — the gauge transform of the family satisfies the flat additive
source law, and the gauge is invertible over the base, so it changes neither the generated
differential field nor the differential rank.  The flat source-boundary theory therefore applies
verbatim to a twisted family with trivial adjoint holonomy: the curvature of the affine local
system, not the presence of an adjoint action, is what can obstruct the linear law.
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

/-! ### Gauge transforms of an affine source local system -/

/-- The gauge transform of a family of observables by a base-valued matrix. -/
def gaugeFamily {κ : Type u} [Fintype κ] (P : κ → κ → K) (z : κ → L) (p : κ) : L :=
  ∑ q, algebraMap K L (P p q) * z q

/-- The gauge transform of the source increments. -/
def gaugeIncrement {κ : Type u} [Fintype κ] (P : κ → κ → K) (om : I → κ → K)
    (i : I) (p : κ) : K :=
  ∑ q, tau i (P p q) * om i q

variable {κ : Type u} [Fintype κ]

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- **A trivial adjoint local system flattens the source law.**  If the gauge matrix solves the
cocycle equation `τ_i(P) M_i = P`, the gauge transform of an affine source family satisfies the
flat additive source law. -/
theorem gauge_shift {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (P : κ → κ → K) (hcocycle : ∀ i p q, (∑ r, tau i (P p r) * M i r q) = P p q)
    (i : I) (p : κ) :
    sigma i (gaugeFamily P z p)
      = gaugeFamily P z p + algebraMap K L (gaugeIncrement tau P om i p) := by
  classical
  have hexpand : sigma i (gaugeFamily P z p)
      = ∑ q, algebraMap K L (tau i (P p q)) *
          ((∑ r, algebraMap K L (M i q r) * z r) + algebraMap K L (om i q)) := by
    rw [gaugeFamily, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, hcomp, hshift i q]
  have hsplit : ∀ q : κ, algebraMap K L (tau i (P p q)) *
        ((∑ r, algebraMap K L (M i q r) * z r) + algebraMap K L (om i q))
      = (∑ r, algebraMap K L (tau i (P p q) * M i q r) * z r)
        + algebraMap K L (tau i (P p q) * om i q) := by
    intro q
    rw [mul_add, Finset.mul_sum, map_mul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun r _ => ?_) rfl
    rw [map_mul, mul_assoc]
  rw [hexpand, Finset.sum_congr rfl fun q _ => hsplit q, Finset.sum_add_distrib]
  have hlin : (∑ q, ∑ r, algebraMap K L (tau i (P p q) * M i q r) * z r)
      = gaugeFamily P z p := by
    rw [Finset.sum_comm, gaugeFamily]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hpull : (∑ q, algebraMap K L (tau i (P p q) * M i q r) * z r)
        = algebraMap K L (∑ q, tau i (P p q) * M i q r) * z r := by
      rw [map_sum, Finset.sum_mul]
    rw [hpull, hcocycle i p r]
  have hinc : (∑ q, algebraMap K L (tau i (P p q) * om i q))
      = algebraMap K L (gaugeIncrement tau P om i p) := by
    rw [gaugeIncrement, map_sum]
  rw [hlin, hinc]

/-! ### The gauge does not move the differential field -/

omit [Differential K] [DifferentialAlgebra K L] in
theorem gaugeFamily_mem_adjoin (P : κ → κ → K) (z : κ → L) (p : κ) :
    gaugeFamily P z p ∈ differentialAdjoin K (Set.range z) := by
  classical
  refine (differentialAdjoin K (Set.range z)).sum_mem fun q _ => ?_
  refine (differentialAdjoin K (Set.range z)).mul_mem
    ((differentialAdjoin K (Set.range z)).algebraMap_mem _) ?_
  exact subset_differentialAdjoin K _ ⟨q, rfl⟩

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
theorem eq_gauge_combination [DecidableEq κ] {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0) (z : κ → L) (p : κ) :
    z p = ∑ q, algebraMap K L (Q p q) * gaugeFamily P z q := by
  classical
  have hterm : ∀ q : κ, algebraMap K L (Q p q) * gaugeFamily P z q
      = ∑ r, algebraMap K L (Q p q * P q r) * z r := by
    intro q
    rw [gaugeFamily, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_comm]
  have hinner : ∀ r : κ, (∑ q, algebraMap K L (Q p q * P q r) * z r)
      = algebraMap K L (if p = r then 1 else 0) * z r := by
    intro r
    rw [← Finset.sum_mul, ← map_sum, hinv p r]
  rw [Finset.sum_congr rfl fun r _ => hinner r, Finset.sum_eq_single p]
  · rw [if_pos rfl, map_one, one_mul]
  · intro b _ hb
    rw [if_neg fun h => hb h.symm, map_zero, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

omit [Differential K] [DifferentialAlgebra K L] in
theorem mem_adjoin_gaugeFamily [DecidableEq κ] {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0) (z : κ → L) (p : κ) :
    z p ∈ differentialAdjoin K (Set.range (gaugeFamily P z)) := by
  classical
  rw [eq_gauge_combination hinv z p]
  refine (differentialAdjoin K (Set.range (gaugeFamily P z))).sum_mem fun q _ => ?_
  refine (differentialAdjoin K (Set.range (gaugeFamily P z))).mul_mem
    ((differentialAdjoin K (Set.range (gaugeFamily P z))).algebraMap_mem _) ?_
  exact subset_differentialAdjoin K _ ⟨q, rfl⟩

/-- **An invertible base gauge generates the same differential field.** -/
theorem differentialAdjoin_gaugeFamily [DecidableEq κ] {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0) (z : κ → L) :
    differentialAdjoin K (Set.range (gaugeFamily P z)) = differentialAdjoin K (Set.range z) := by
  refine le_antisymm ?_ ?_
  · refine differentialAdjoin_le K ?_ (derivationClosed_differentialAdjoin K _)
    rintro - ⟨p, rfl⟩
    exact gaugeFamily_mem_adjoin P z p
  · refine differentialAdjoin_le K ?_ (derivationClosed_differentialAdjoin K _)
    rintro - ⟨p, rfl⟩
    exact mem_adjoin_gaugeFamily hinv z p

/-- The gauge transform has the same differential rank. -/
theorem eRk_gaugeFamily [CharZero L] [DecidableEq κ] {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0) (z : κ → L) :
    (differentialMatroid K L).eRk (Set.range (gaugeFamily P z))
      = (differentialMatroid K L).eRk (Set.range z) := by
  rw [← Matroid.eRk_closure_eq, ← Matroid.eRk_closure_eq (X := Set.range z),
    differentialMatroid_closure_eq_differentialClosure,
    differentialMatroid_closure_eq_differentialClosure]
  unfold differentialClosure
  rw [differentialAdjoin_gaugeFamily hinv z]

/-! ### The curved law with trivial adjoint holonomy -/

/-- **The curved source-boundary law, flat case.**  For an affine source family whose adjoint
local system is trivialized by a base gauge, the gauge transform is differentially independent
exactly when the boundary classes of the gauged increments are independent over the
constant-coefficient differential operators. -/
theorem twisted_differentialIndependent_iff
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    (P : κ → κ → K) (hcocycle : ∀ i p q, (∑ r, tau i (P p r) * M i r q) = P p q) :
    DifferentialIndependent K (gaugeFamily P z) ↔
      LinearIndependent (Polynomial C)
        (fun p : κ =>
          boundaryClass tau hC hfix hderiv fun i => gaugeIncrement tau P om i p) :=
  differentialIndependent_iff_linearIndependent_boundaryClass tau sigma hcomp hderivL hCfixed
    hfixed hC hfix hderiv (gaugeFamily P z) (gaugeIncrement tau P om)
    (fun i p => gauge_shift tau sigma hshift hcomp P hcocycle i p)

/-- **The curved rank law, flat case.**  The differential rank of an affine source family with
trivial adjoint holonomy is the rank of the span of the boundary classes of its gauged
increments. -/
theorem twisted_eRk_eq_rank_span_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] [CharZero L] [DecidableEq κ]
    {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    (hcocycle : ∀ i p q, (∑ r, tau i (P p r) * M i r q) = P p q) :
    ∃ r : ℕ,
      (differentialMatroid K L).eRk (Set.range z) = r ∧
      Module.rank (Polynomial C) (Submodule.span (Polynomial C)
        (Set.range fun p : κ =>
          boundaryClass tau hC hfix hderiv fun i => gaugeIncrement tau P om i p)) = r := by
  obtain ⟨r, hrk, hrank⟩ := eRk_eq_rank_span_boundaryClass tau sigma hcomp hderivL hCfixed hfixed
    hC hfix hderiv (gaugeFamily P z) (gaugeIncrement tau P om)
    (fun i p => gauge_shift tau sigma hshift hcomp P hcocycle i p)
  exact ⟨r, (eRk_gaugeFamily hinv z).symm.trans hrk, hrank⟩

/-! ### The commutative case is the identity gauge -/

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- A flat source family is the affine family with identity adjoint part. -/
theorem flat_shift_of_identity [DecidableEq κ] {z : κ → L} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p) = z p + algebraMap K L (om i p)) (i : I) (p : κ) :
    sigma i (z p)
      = (∑ q, algebraMap K L (if p = q then (1 : K) else 0) * z q)
        + algebraMap K L (om i p) := by
  classical
  rw [hshift i p]
  congr 1
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, map_one, one_mul]
  · intro b _ hb
    rw [if_neg fun h => hb h.symm, map_zero, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
/-- The identity matrix solves the cocycle equation of the identity adjoint local system: the
commutative theory is the trivial-adjoint case of the curved one. -/
theorem identity_cocycle [DecidableEq κ] (hfixOne : ∀ i : I, tau i 1 = 1)
    (hfixZero : ∀ i : I, tau i 0 = 0) (i : I) (p q : κ) :
    (∑ r, tau i (if p = r then (1 : K) else 0) * (if r = q then (1 : K) else 0))
      = if p = q then (1 : K) else 0 := by
  classical
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl, hfixOne, one_mul]
  · intro b _ hb
    rw [if_neg fun h => hb h.symm, hfixZero, zero_mul]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

end

end GaloisForLFunctions.HTGeometry
