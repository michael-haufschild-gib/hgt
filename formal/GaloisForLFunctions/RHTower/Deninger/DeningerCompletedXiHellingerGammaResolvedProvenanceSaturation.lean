import GaloisForLFunctions.RHTower.Deninger.DeningerCompletedXiHellingerGammaResolvedProvenanceCoface

/-!
# Saturation rigidity of the resolved Hellinger--Gamma provenance quotient

The ordinary completed adjacent cofaces fill both Hodge channels at every
nonzero modular displacement.  Resolving each vertex by its unchanged
Calderón--Witt incidence provenance does not change those cofaces: their
provenance coordinate is zero.

This file proves the missing reverse inclusion.  Off axis, the closed span
of resolved cofaces is exactly the kernel of provenance projection.  Hence
the resolved relative quotient is canonically, and exhaustively, the
completed incidence provenance carrier.  The previously proved source map
was split injective; the result here proves that it is the whole quotient.

No zero-location, positivity, or Riemann-hypothesis premise is used.
-/

open Complex Set Topology

namespace RHTower

noncomputable section

open CompletedXiHellingerGammaPureHodgeCoface

/-- Insert the two completed Hodge channels with zero provenance. -/
def hellingerGammaResolvedProvenanceHodgeInsertion
    {p q : Nat.Primes} {hpq : p ≠ q} :
    HellingerGammaPureHodgeXiCofaceCompletion p q hpq →L[ℂ]
      HellingerGammaResolvedProvenanceCofaceCompletion p q hpq :=
  ContinuousLinearMap.inl ℂ
    (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
    (DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)

@[simp]
theorem hellingerGammaResolvedProvenanceHodgeInsertion_coface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    hellingerGammaResolvedProvenanceHodgeInsertion
        (hellingerGammaCompletedAdjacentCoface hpq a n x) =
      hellingerGammaResolvedProvenanceAdjacentCoface hpq a n x := by
  rw [hellingerGammaResolvedProvenanceAdjacentCoface_eq]
  rfl

/-- The zero-provenance insertion carries the whole ordinary closed coface
span into the resolved closed coface span. -/
theorem hellingerGammaResolvedProvenanceHodgeInsertion_mem_closedSpan
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (z : HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
    (hz : z ∈ hellingerGammaCompletedAdjacentCofaceClosedSpan hpq a) :
    hellingerGammaResolvedProvenanceHodgeInsertion z ∈
      hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a := by
  let T : Submodule ℂ
      (HellingerGammaPureHodgeXiCofaceCompletion p q hpq) :=
    (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).comap
      hellingerGammaResolvedProvenanceHodgeInsertion.toLinearMap
  have hTclosed : IsClosed (T : Set
      (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)) := by
    change IsClosed
      (hellingerGammaResolvedProvenanceHodgeInsertion ⁻¹'
        (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a :
          Set (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq)))
    exact
      (Submodule.isClosed_topologicalClosure
        (Submodule.span ℂ
          (hellingerGammaResolvedProvenanceAdjacentCofaceSet hpq a))).preimage
        hellingerGammaResolvedProvenanceHodgeInsertion.continuous
  have hspan : Submodule.span ℂ
      (hellingerGammaCompletedAdjacentCofaceSet hpq a) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨n, x, rfl⟩
    change hellingerGammaResolvedProvenanceHodgeInsertion
        (hellingerGammaCompletedAdjacentCoface hpq a n x) ∈
      hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a
    rw [hellingerGammaResolvedProvenanceHodgeInsertion_coface]
    exact
      (Submodule.span ℂ
          (hellingerGammaResolvedProvenanceAdjacentCofaceSet hpq a)).le_topologicalClosure
        (Submodule.subset_span ⟨n, x, rfl⟩)
  have hclosure :
      hellingerGammaCompletedAdjacentCofaceClosedSpan hpq a ≤ T := by
    exact Submodule.topologicalClosure_minimal _ hspan hTclosed
  exact hclosure hz

/-- **Off-axis saturation rigidity.**  At nonzero modular displacement,
resolved adjacent cofaces fill exactly the zero-provenance hyperplane. -/
theorem
    hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_eq_ker_of_ne
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a =
      LinearMap.ker hellingerGammaResolvedProvenanceProjection.toLinearMap := by
  apply le_antisymm
  · exact hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_le_ker hpq a
  · intro z hz
    change z.2 = 0 at hz
    have hfirst : z.1 ∈
        hellingerGammaCompletedAdjacentCofaceClosedSpan hpq a := by
      rw [hellingerGammaCompletedAdjacentCofaceClosedSpan_eq_top hpq ha]
      exact Submodule.mem_top
    have hinsertion :=
      hellingerGammaResolvedProvenanceHodgeInsertion_mem_closedSpan
        hpq a z.1 hfirst
    have hzpair : z = (z.1, 0) := by
      exact Prod.ext rfl hz
    rw [hzpair]
    simpa [hellingerGammaResolvedProvenanceHodgeInsertion] using hinsertion

/-- At zero displacement, the candidate resolved saturation is the ordinary
Hodge diagonal together with zero provenance. -/
def hellingerGammaResolvedProvenanceZeroCofaceSubmodule
    {p q : Nat.Primes} (hpq : p ≠ q) :
    Submodule ℂ (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq) :=
  (hellingerGammaCompletedCofaceDiagonal (p := p) (q := q) (hpq := hpq)).comap
      (ContinuousLinearMap.fst ℂ
        (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
        (DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)).toLinearMap ⊓
    LinearMap.ker hellingerGammaResolvedProvenanceProjection.toLinearMap

theorem mem_hellingerGammaResolvedProvenanceZeroCofaceSubmodule
    {p q : Nat.Primes} (hpq : p ≠ q)
    (z : HellingerGammaResolvedProvenanceCofaceCompletion p q hpq) :
    z ∈ hellingerGammaResolvedProvenanceZeroCofaceSubmodule hpq ↔
      z.1 ∈ hellingerGammaCompletedCofaceDiagonal (p := p) (q := q) (hpq := hpq) ∧
        z.2 = 0 := by
  rfl

theorem hellingerGammaResolvedProvenanceZeroCofaceSubmodule_isClosed
    {p q : Nat.Primes} (hpq : p ≠ q) :
    IsClosed (hellingerGammaResolvedProvenanceZeroCofaceSubmodule hpq :
      Set (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq)) := by
  change IsClosed
    (((ContinuousLinearMap.fst ℂ
        (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
        (DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)) ⁻¹'
      (hellingerGammaCompletedCofaceDiagonal (p := p) (q := q) (hpq := hpq) :
        Set (HellingerGammaPureHodgeXiCofaceCompletion p q hpq))) ∩
      (hellingerGammaResolvedProvenanceProjection ⁻¹' {0}))
  exact
    ((hellingerGammaCompletedCofaceDiagonal_isClosed
        (p := p) (q := q) (hpq := hpq)).preimage
      (ContinuousLinearMap.fst ℂ
        (HellingerGammaPureHodgeXiCofaceCompletion p q hpq)
        (DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq)).continuous).inter
      hellingerGammaResolvedProvenanceProjection.isClosed_ker

/-- **Zero-displacement phase.**  At the critical Cartan value, resolved
cofaces fill exactly the ordinary Hodge diagonal and still have zero
provenance. -/
theorem hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_zero
    {p q : Nat.Primes} (hpq : p ≠ q) :
    hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq 0 =
      hellingerGammaResolvedProvenanceZeroCofaceSubmodule hpq := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨n, x, rfl⟩
      rw [hellingerGammaResolvedProvenanceAdjacentCoface_eq]
      apply
        (mem_hellingerGammaResolvedProvenanceZeroCofaceSubmodule hpq _).2
      exact
        ⟨hellingerGammaCompletedAdjacentCoface_zero_mem_diagonal hpq n x, rfl⟩
    · exact hellingerGammaResolvedProvenanceZeroCofaceSubmodule_isClosed hpq
  · intro z hz
    rw [mem_hellingerGammaResolvedProvenanceZeroCofaceSubmodule] at hz
    have hfirst : z.1 ∈
        hellingerGammaCompletedAdjacentCofaceClosedSpan hpq 0 := by
      rw [hellingerGammaCompletedAdjacentCofaceClosedSpan_zero]
      exact hz.1
    have hinsertion :=
      hellingerGammaResolvedProvenanceHodgeInsertion_mem_closedSpan
        hpq 0 z.1 hfirst
    have hzpair : z = (z.1, 0) := Prod.ext rfl hz.2
    rw [hzpair]
    simpa [hellingerGammaResolvedProvenanceHodgeInsertion] using hinsertion

/-- Off axis, the descended provenance projection is injective: its kernel
has already been quotiented out completely. -/
theorem hellingerGammaResolvedProvenanceQuotientProjection_injective_of_ne
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    Function.Injective
      (hellingerGammaResolvedProvenanceQuotientProjection hpq a) := by
  intro x y hxy
  have hzero :
      hellingerGammaResolvedProvenanceQuotientProjection hpq a (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ :=
      Submodule.Quotient.mk_surjective
        (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a)
        (x - y)
  rw [← hz] at hzero
  change hellingerGammaResolvedProvenanceProjection z = 0 at hzero
  have hzmem : z ∈
      hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a := by
    rw [hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan_eq_ker_of_ne
      hpq ha]
    exact hzero
  have hmkzero :
      (Submodule.Quotient.mk z :
        HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
          hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hzmem
  apply sub_eq_zero.mp
  rw [← hz, hmkzero]

/-- The descended provenance projection is always onto, with the resolved
source insertion as an explicit section. -/
theorem hellingerGammaResolvedProvenanceQuotientProjection_surjective
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    Function.Surjective
      (hellingerGammaResolvedProvenanceQuotientProjection hpq a) := by
  intro x
  exact ⟨hellingerGammaResolvedProvenanceQuotientSource hpq a x,
    hellingerGammaResolvedProvenanceQuotientProjection_source hpq a x⟩

/-- **Exact off-axis quotient classification.**  The resolved relative
Hellinger--Gamma quotient is precisely completed Calderón--Witt incidence
provenance; no Hodge-channel quotient remains. -/
def hellingerGammaResolvedProvenanceQuotientEquivOfNe
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
        hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) ≃ₗ[ℂ]
      DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  LinearEquiv.ofBijective
    (hellingerGammaResolvedProvenanceQuotientProjection hpq a)
    ⟨hellingerGammaResolvedProvenanceQuotientProjection_injective_of_ne hpq ha,
      hellingerGammaResolvedProvenanceQuotientProjection_surjective hpq a⟩

@[simp]
theorem hellingerGammaResolvedProvenanceQuotientEquivOfNe_apply
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0)
    (z : HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
      hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) :
    hellingerGammaResolvedProvenanceQuotientEquivOfNe hpq ha z =
      hellingerGammaResolvedProvenanceQuotientProjection hpq a z :=
  rfl

@[simp]
theorem hellingerGammaResolvedProvenanceQuotientEquivOfNe_symm_apply
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    (hellingerGammaResolvedProvenanceQuotientEquivOfNe hpq ha).symm x =
      hellingerGammaResolvedProvenanceQuotientSource hpq a x := by
  apply (hellingerGammaResolvedProvenanceQuotientEquivOfNe hpq ha).injective
  rw [LinearEquiv.apply_symm_apply,
    hellingerGammaResolvedProvenanceQuotientEquivOfNe_apply,
    hellingerGammaResolvedProvenanceQuotientProjection_source]

end

end RHTower
