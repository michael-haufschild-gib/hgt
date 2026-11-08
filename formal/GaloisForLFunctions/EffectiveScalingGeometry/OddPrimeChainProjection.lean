import GaloisForLFunctions.EffectiveScalingGeometry.PrimeChainBasis
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleProjection

/-!
# Odd coordinates of prime chains

Forgetting the prime-two vertex induces a cutoff-preserving exterior projection.
Coning reads only odd coordinates, while its image has zero odd projection.
Together with the cycle projector these identities identify cycles with odd
chains, without changing height or requiring division in the coefficient ring.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Numerical prime two, as a prime label. -/
abbrev primeTwoLabel : Nat.Primes := ⟨2,Nat.prime_two⟩

/-- Forget the prime-two coordinate. -/
def oddVertexProjection : (Nat.Primes →₀ R) →ₗ[R] (Nat.Primes →₀ R) :=
  Finsupp.linearCombination R (fun p : Nat.Primes =>
    if p = primeTwoLabel then 0 else Finsupp.single p (1 : R))

theorem oddVertexProjection_single (p : Nat.Primes) (c : R) :
    oddVertexProjection R (Finsupp.single p c) =
      if p = primeTwoLabel then 0 else Finsupp.single p c := by
  classical
  by_cases h : p = primeTwoLabel
  · simp only [oddVertexProjection, Finsupp.linearCombination_single, if_pos h, smul_zero]
  · simp only [oddVertexProjection, Finsupp.linearCombination_single, if_neg h,
      Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Exterior projection onto the chains with odd prime support. -/
def oddChainProjection (k : ℕ) : PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k :=
  exteriorPower.map k (oddVertexProjection R)

theorem oddChainProjection_atom_of_odd {k : ℕ} (v : Fin k → Nat.Primes)
    (hv : ∀ i, v i ≠ primeTwoLabel) :
    oddChainProjection R k (primeChainAtom R v) = primeChainAtom R v := by
  unfold oddChainProjection primeChainAtom
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  simp only [Function.comp_apply, oddVertexProjection_single, if_neg (hv i)]

theorem oddChainProjection_atom_of_even {k : ℕ} (v : Fin k → Nat.Primes)
    (i : Fin k) (hi : v i = primeTwoLabel) :
    oddChainProjection R k (primeChainAtom R v) = 0 := by
  unfold oddChainProjection primeChainAtom
  rw [exteriorPower.map_apply_ιMulti]
  apply AlternatingMap.map_coord_zero _ i
  simp only [Function.comp_apply, oddVertexProjection_single, if_pos hi]

theorem oddChainProjection_basis_of_odd {k : ℕ} (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) :
    oddChainProjection R k (primeChainBasis R k s) = primeChainBasis R k s := by
  rw [primeChainBasis_eq_atom]
  apply oddChainProjection_atom_of_odd
  intro i hi
  apply hs
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mp ⟨i,hi⟩

theorem oddChainProjection_basis_of_even {k : ℕ} (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∈ s.val) :
    oddChainProjection R k (primeChainBasis R k s) = 0 := by
  obtain ⟨i,hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mpr hs
  rw [primeChainBasis_eq_atom]
  exact oddChainProjection_atom_of_even R _ i hi

theorem primeChainCone_basis_of_even {k : ℕ} (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∈ s.val) :
    primeChainCone R k primeTwoLabel (primeChainBasis R k s) = 0 := by
  obtain ⟨i,hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mpr hs
  rw [primeChainBasis_eq_atom, primeChainCone_atom]
  unfold primeChainAtom
  apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ)
  · simp only [Fin.cons_zero,Fin.cons_succ,hi]
  · exact (Fin.succ_ne_zero i).symm

theorem primeChainCone_comp_oddProjection (k : ℕ) :
    (primeChainCone R k primeTwoLabel).comp (oddChainProjection R k) =
      primeChainCone R k primeTwoLabel := by
  classical
  apply (primeChainBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply]
  by_cases hs : primeTwoLabel ∈ s.val
  · rw [oddChainProjection_basis_of_even R s hs, map_zero, primeChainCone_basis_of_even R s hs]
  · rw [oddChainProjection_basis_of_odd R s hs]

theorem oddChainProjection_comp_cone (k : ℕ) :
    (oddChainProjection R (k+1)).comp (primeChainCone R k primeTwoLabel) = 0 := by
  apply (primeChainBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [primeChainBasis_eq_atom, primeChainCone_atom]
  exact oddChainProjection_atom_of_even R _ 0 rfl

theorem oddChainProjection_cutoff (k N : ℕ) :
    primeChainCutoff R k N ≤
      (primeChainCutoff R k N).comap (oddChainProjection R k) := by
  classical
  rw [primeChainCutoff_eq_span_basis R k N]
  apply Submodule.span_le.mpr
  rintro x ⟨s, hs, rfl⟩
  change oddChainProjection R k (primeChainBasis R k s) ∈
    Submodule.span R (primeChainBasis R k '' {s | primeFaceProduct s ≤ N})
  by_cases he : primeTwoLabel ∈ s.val
  · rw [oddChainProjection_basis_of_even R s he]
    exact Submodule.zero_mem _
  · rw [oddChainProjection_basis_of_odd R s he]
    exact Submodule.subset_span ⟨s,hs,rfl⟩

theorem oddChainProjection_idempotent (k : ℕ) :
    (oddChainProjection R k).comp (oddChainProjection R k) = oddChainProjection R k := by
  classical
  apply (primeChainBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply]
  by_cases hs : primeTwoLabel ∈ s.val
  · rw [oddChainProjection_basis_of_even R s hs, map_zero]
  · rw [oddChainProjection_basis_of_odd R s hs, oddChainProjection_basis_of_odd R s hs]

/-- A prime-two cone only reads the odd component of its input. -/
theorem primeCycleProjector_comp_oddProjection (k : ℕ) :
    (primeCycleProjector R k).comp (oddChainProjection R (k+1)) = primeCycleProjector R k := by
  rw [primeCycleProjector, LinearMap.comp_assoc, primeChainCone_comp_oddProjection]

/-- Taking a cycle representative retains exactly its original odd coordinates. -/
theorem oddChainProjection_comp_cycleProjector (k : ℕ) :
    (oddChainProjection R (k+1)).comp (primeCycleProjector R k) = oddChainProjection R (k+1) := by
  apply LinearMap.ext
  intro x
  have hc := congrArg (oddChainProjection R (k+1))
    (LinearMap.congr_fun (primeCycleProjector_add_coneBoundary R k) x)
  have hz : oddChainProjection R (k+1)
      (primeChainCone R k primeTwoLabel (primeChainBoundary R k x)) = 0 :=
    LinearMap.congr_fun (oddChainProjection_comp_cone R k) (primeChainBoundary R k x)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    map_add, hz, add_zero] using hc

#print axioms primeChainCone_comp_oddProjection
#print axioms oddChainProjection_comp_cone
#print axioms oddChainProjection_cutoff
#print axioms primeCycleProjector_comp_oddProjection
#print axioms oddChainProjection_comp_cycleProjector
end GaloisForLFunctions.EffectiveScalingGeometry
