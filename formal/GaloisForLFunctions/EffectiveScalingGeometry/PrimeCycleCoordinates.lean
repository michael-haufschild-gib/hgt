import GaloisForLFunctions.EffectiveScalingGeometry.OddPrimeChainProjection

/-!
# Natural odd coordinates for prime cycles

In each positive exterior degree, forgetting the prime-two coordinate gives
an equivalence between cutoff cycles and cutoff odd chains. Its inverse sends
an odd chain to the boundary of its prime-two cone. The equivalences commute
with height inclusions, and odd chains are the coordinate submodules spanned
by the bounded odd prime supports. All maps are defined over any commutative ring.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Positive-degree reduced cycles at a prime-product cutoff. -/
def primeCutoffCycles (k N : ℕ) : Submodule R (PrimeChainSpace R (k+1)) :=
  primeChainCutoff R (k+1) N ⊓ (primeChainBoundary R k).ker

/-- Chains below the cutoff whose support uses only odd primes. -/
def primeOddCutoff (k N : ℕ) : Submodule R (PrimeChainSpace R k) :=
  primeChainCutoff R k N ⊓ (oddChainProjection R k).range

theorem oddChainProjection_fixes_range (k : ℕ) (x : (oddChainProjection R k).range) :
    oddChainProjection R k x.val = x.val := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (oddChainProjection_idempotent R k) y

/-- Odd coordinates of a cycle, with the same height bound. -/
def primeCycleToOdd (k N : ℕ) :
    primeCutoffCycles R k N →ₗ[R] primeOddCutoff R (k+1) N :=
  (oddChainProjection R (k+1)).restrict (fun x hx =>
    ⟨oddChainProjection_cutoff R (k+1) N hx.1, ⟨x,rfl⟩⟩)

/-- The odd face is lifted to the boundary of its prime-two cone. -/
def primeOddToCycle (k N : ℕ) :
    primeOddCutoff R (k+1) N →ₗ[R] primeCutoffCycles R k N :=
  (primeCycleProjector R k).restrict (fun x hx =>
    ⟨primeCycleProjector_cutoff R k N hx.1, primeCycleProjector_cycle R k x⟩)

/-- Cycles are exactly freely chosen odd coordinates within the same height. -/
def primeCutoffCycleOddEquiv (k N : ℕ) :
    primeCutoffCycles R k N ≃ₗ[R] primeOddCutoff R (k+1) N :=
  LinearEquiv.ofLinear (primeCycleToOdd R k N) (primeOddToCycle R k N)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change oddChainProjection R (k+1) (primeCycleProjector R k x.val) = x.val
      exact (LinearMap.congr_fun (oddChainProjection_comp_cycleProjector R k) x.val).trans
        (oddChainProjection_fixes_range R (k+1) ⟨x.val,x.property.2⟩))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change primeCycleProjector R k (oddChainProjection R (k+1) x.val) = x.val
      exact (LinearMap.congr_fun (primeCycleProjector_comp_oddProjection R k) x.val).trans
        (primeCycleProjector_fixes_cycles R k ⟨x.val,x.property.2⟩))

/-- Odd cutoff chains form the coordinate submodule on bounded odd faces. -/
theorem primeOddCutoff_eq_span_basis (k N : ℕ) :
    primeOddCutoff R k N = Submodule.span R
      (primeChainBasis R k '' {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val}) := by
  classical
  apply le_antisymm
  · have hmap : primeChainCutoff R k N ≤
        (Submodule.span R (primeChainBasis R k ''
          {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val})).comap
          (oddChainProjection R k) := by
      rw [primeChainCutoff_eq_span_basis]
      apply Submodule.span_le.mpr
      rintro x ⟨s,hs,rfl⟩
      change oddChainProjection R k (primeChainBasis R k s) ∈ Submodule.span R
        (primeChainBasis R k '' {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val})
      by_cases he : primeTwoLabel ∈ s.val
      · rw [oddChainProjection_basis_of_even R s he]
        exact Submodule.zero_mem _
      · rw [oddChainProjection_basis_of_odd R s he]
        exact Submodule.subset_span ⟨s,⟨hs,he⟩,rfl⟩
    intro x hx
    have hx' := hmap hx.1
    change oddChainProjection R k x ∈ Submodule.span R
      (primeChainBasis R k '' {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val}) at hx'
    have he : oddChainProjection R k x = x :=
      oddChainProjection_fixes_range R k ⟨x,hx.2⟩
    simpa only [he] using hx'
  · apply Submodule.span_le.mpr
    rintro x ⟨s,hs,rfl⟩
    exact ⟨primeChainBasis_mem_cutoff R s hs.1,
      ⟨primeChainBasis R k s,oddChainProjection_basis_of_odd R s hs.2⟩⟩

theorem primeCutoffCycles_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeCutoffCycles R k N ≤ primeCutoffCycles R k M :=
  inf_le_inf (primeChainCutoff_mono R (k+1) h) le_rfl

theorem primeOddCutoff_mono (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    primeOddCutoff R k N ≤ primeOddCutoff R k M :=
  inf_le_inf (primeChainCutoff_mono R k h) le_rfl

/-- The cycle-coordinate isomorphisms commute with height inclusions. -/
theorem primeCycleToOdd_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeCycleToOdd R k M).comp (Submodule.inclusion (primeCutoffCycles_mono R k h)) =
      (Submodule.inclusion (primeOddCutoff_mono R (k+1) h)).comp (primeCycleToOdd R k N) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

#print axioms primeCutoffCycleOddEquiv
#print axioms primeOddCutoff_eq_span_basis
#print axioms primeCycleToOdd_natural
end GaloisForLFunctions.EffectiveScalingGeometry
