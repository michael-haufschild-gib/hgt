import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCutoffComplex

/-!
# Projection to cycles without increasing prime height

Coning the boundary of a prime face replaces one removed prime by two.
Its product cannot increase. Cartan's identity therefore makes `d(2∧·)`
a projection to cycles within the same prime-product cutoff, over any
commutative ring and in every positive exterior degree. The retractions
commute with height inclusions. This splits cycles before taking homology;
it does not assert that the cutoff complex is contractible.
-/

noncomputable section
open RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Coning a boundary replaces a removed prime by two, so costs no height. -/
theorem primeConeBoundary_cutoff (k N : ℕ) :
    primeChainCutoff R (k+1) N ≤ (primeChainCutoff R (k+1) N).comap
      ((primeChainCone R k ⟨2,Nat.prime_two⟩).comp (primeChainBoundary R k)) := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  change primeChainCone R k ⟨2,Nat.prime_two⟩
    (primeChainBoundary R k (primeChainAtom R v)) ∈ primeChainCutoff R (k+1) N
  rw [primeChainBoundary_atom, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_zsmul, primeChainCone_atom]
  apply (primeChainCutoff R (k+1) N).toAddSubgroup.zsmul_mem
  apply Submodule.subset_span
  refine ⟨Fin.cons ⟨2,Nat.prime_two⟩ (fun j => v (i.succAbove j)), ?_, rfl⟩
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  calc
    2 * ∏ j, (v (i.succAbove j) : ℕ) ≤
        (v i : ℕ) * ∏ j, (v (i.succAbove j) : ℕ) :=
      Nat.mul_le_mul_right _ (v i).property.two_le
    _ = ∏ j, (v j : ℕ) := (Fin.prod_univ_succAbove (fun j => (v j : ℕ)) i).symm
    _ ≤ N := hv

/-- Project a chain to a cycle by taking the boundary of its prime-two cone. -/
def primeCycleProjector (k : ℕ) : PrimeChainSpace R (k+1) →ₗ[R] PrimeChainSpace R (k+1) :=
  (primeChainBoundary R (k+1)).comp (primeChainCone R (k+1) ⟨2,Nat.prime_two⟩)

theorem primeCycleProjector_add_coneBoundary (k : ℕ) :
    primeCycleProjector R k +
      (primeChainCone R k ⟨2,Nat.prime_two⟩).comp (primeChainBoundary R k) = LinearMap.id :=
  primeChainCone_contracts R k ⟨2,Nat.prime_two⟩

theorem primeCycleProjector_cycle (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeChainBoundary R k (primeCycleProjector R k x) = 0 :=
  LinearMap.congr_fun (primeChainBoundary_sq R k)
    (primeChainCone R (k+1) ⟨2,Nat.prime_two⟩ x)

theorem primeCycleProjector_cutoff (k N : ℕ) :
    primeChainCutoff R (k+1) N ≤
      (primeChainCutoff R (k+1) N).comap (primeCycleProjector R k) := by
  intro x hx
  have hc := LinearMap.congr_fun (primeCycleProjector_add_coneBoundary R k) x
  have heq : primeCycleProjector R k x =
      x - primeChainCone R k ⟨2,Nat.prime_two⟩ (primeChainBoundary R k x) :=
    eq_sub_iff_add_eq.mpr hc
  change primeCycleProjector R k x ∈ primeChainCutoff R (k+1) N
  rw [heq]
  exact Submodule.sub_mem _ hx (primeConeBoundary_cutoff R k N hx)

theorem primeCycleProjector_fixes_cycles (k : ℕ)
    (x : (primeChainBoundary R k).ker) : primeCycleProjector R k x = x := by
  have hc := LinearMap.congr_fun (primeCycleProjector_add_coneBoundary R k) x.val
  have hx : primeChainBoundary R k x.val = 0 := x.property
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hx, map_zero, add_zero] using hc

/-- The cycle projection restricts to the original cutoff. -/
def primeCutoffCycleRetraction (k N : ℕ) :
    primeChainCutoff R (k+1) N →ₗ[R]
      ↥(primeChainCutoff R (k+1) N ⊓ (primeChainBoundary R k).ker) :=
  (primeCycleProjector R k).restrict (fun x hx =>
    ⟨primeCycleProjector_cutoff R k N hx, primeCycleProjector_cycle R k x⟩)

theorem primeCutoffCycleRetraction_inclusion (k N : ℕ) :
    (primeCutoffCycleRetraction R k N).comp
      (Submodule.inclusion (show primeChainCutoff R (k+1) N ⊓
        (primeChainBoundary R k).ker ≤ primeChainCutoff R (k+1) N from inf_le_left)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact primeCycleProjector_fixes_cycles R k ⟨x.val,x.property.2⟩

/-- The same ambient projection commutes with every increase of height. -/
theorem primeCutoffCycleRetraction_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (Submodule.inclusion (inf_le_inf (primeChainCutoff_mono R (k+1) h) le_rfl)).comp
      (primeCutoffCycleRetraction R k N) =
    (primeCutoffCycleRetraction R k M).comp
      (Submodule.inclusion (primeChainCutoff_mono R (k+1) h)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem primeCycleProjector_idempotent (k : ℕ) :
    (primeCycleProjector R k).comp (primeCycleProjector R k) = primeCycleProjector R k := by
  apply LinearMap.ext
  intro x
  exact primeCycleProjector_fixes_cycles R k
    ⟨primeCycleProjector R k x, primeCycleProjector_cycle R k x⟩

#print axioms primeConeBoundary_cutoff
#print axioms primeCutoffCycleRetraction_inclusion
#print axioms primeCutoffCycleRetraction_natural
#print axioms primeCycleProjector_idempotent
end GaloisForLFunctions.EffectiveScalingGeometry
