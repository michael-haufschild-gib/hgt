import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleCoordinates

/-!
# Explicit bases of prime-cutoff cycles

Bounded odd prime supports index a basis of the odd cutoff submodule.
Transporting it through the natural cycle-coordinate equivalence gives an
actual basis of cycles: each vector is the boundary of its prime-two cone.
The empty exterior degree is the ordinary cutoff space, since it has no
prime-two coordinate. All constructions work over every commutative ring.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Odd prime supports of a specified cardinality and bounded product. -/
def OddPrimeFace (k N : ℕ) :=
  {s : Set.powersetCard Nat.Primes k // primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val}

/-- The ambient exterior vector of an odd face. -/
def oddPrimeFaceVector (k N : ℕ) (s : OddPrimeFace k N) : PrimeChainSpace R k :=
  primeChainBasis R k s.val

theorem oddPrimeFaceVector_linearIndependent (k N : ℕ) :
    LinearIndependent R (oddPrimeFaceVector R k N) :=
  (primeChainBasis R k).linearIndependent.comp
    (fun s : OddPrimeFace k N => s.val) Subtype.val_injective

theorem oddPrimeFaceVector_range (k N : ℕ) :
    Set.range (oddPrimeFaceVector R k N) =
      primeChainBasis R k '' {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val} := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s.val,s.property,rfl⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨⟨s,hs⟩,rfl⟩

theorem oddPrimeFaceVector_span (k N : ℕ) :
    Submodule.span R (Set.range (oddPrimeFaceVector R k N)) = primeOddCutoff R k N := by
  rw [oddPrimeFaceVector_range,primeOddCutoff_eq_span_basis]

/-- The actual basis of the odd cutoff submodule. -/
def oddPrimeCutoffBasis (k N : ℕ) :
    Module.Basis (OddPrimeFace k N) R (primeOddCutoff R k N) :=
  (Module.Basis.span (oddPrimeFaceVector_linearIndependent R k N)).map
    (LinearEquiv.ofEq _ _ (oddPrimeFaceVector_span R k N))

theorem oddPrimeCutoffBasis_val (k N : ℕ) (s : OddPrimeFace k N) :
    (oddPrimeCutoffBasis R k N s).val = primeChainBasis R k s.val := by
  rw [oddPrimeCutoffBasis,Module.Basis.map_apply,Module.Basis.span_apply]
  rfl

/-- A basis of cutoff cycles, indexed by bounded odd prime faces. -/
def primeCutoffCycleBasis (k N : ℕ) :
    Module.Basis (OddPrimeFace (k+1) N) R (primeCutoffCycles R k N) :=
  (oddPrimeCutoffBasis R (k+1) N).map (primeCutoffCycleOddEquiv R k N).symm

/-- Each basis cycle is the boundary of the corresponding prime-two cone. -/
theorem primeCutoffCycleBasis_val (k N : ℕ) (s : OddPrimeFace (k+1) N) :
    (primeCutoffCycleBasis R k N s).val = primeCycleProjector R k (primeChainBasis R (k+1) s.val) := by
  rw [primeCutoffCycleBasis,Module.Basis.map_apply]
  change primeCycleProjector R k (oddPrimeCutoffBasis R (k+1) N s).val = _
  rw [oddPrimeCutoffBasis_val]

/-- The empty exterior face has no prime-two coordinate to discard. -/
theorem oddChainProjection_zero : oddChainProjection R 0 = LinearMap.id := by
  apply (primeChainBasis R 0).ext
  intro s
  have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property
  exact oddChainProjection_basis_of_odd R s (by rw [hs]; exact Finset.notMem_empty _)

theorem primeOddCutoff_zero (N : ℕ) : primeOddCutoff R 0 N = primeChainCutoff R 0 N := by
  rw [primeOddCutoff,oddChainProjection_zero,LinearMap.range_id,inf_top_eq]

#print axioms oddPrimeCutoffBasis
#print axioms primeCutoffCycleBasis_val
#print axioms primeOddCutoff_zero
end GaloisForLFunctions.EffectiveScalingGeometry
