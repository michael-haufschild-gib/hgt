import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleCoordinates

/-!
# Coordinate kernels of prime cones

Adjoining a prime kills exactly the exterior faces already containing it.
This remains exact inside each odd product cutoff over every commutative ring.
Contraction by that prime's coordinate recovers the projection onto faces
omitting it, and the complementary projection identifies the bounded kernel.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Erase one prime coordinate before taking exterior powers. -/
def primeErasedVertexProjection (p : Nat.Primes) : (Nat.Primes →₀ R) →ₗ[R] (Nat.Primes →₀ R) :=
  Finsupp.linearCombination R (fun q => if q = p then 0 else Finsupp.single q 1)

theorem primeErasedVertexProjection_single (p q : Nat.Primes) :
    primeErasedVertexProjection R p (Finsupp.single q 1) =
      if q = p then 0 else Finsupp.single q 1 := by
  simp only [primeErasedVertexProjection,Finsupp.linearCombination_single,one_smul]

/-- Project onto faces omitting a specified prime. -/
def primeErasedChainProjection (p : Nat.Primes) (k : ℕ) : PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k :=
  exteriorPower.map k (primeErasedVertexProjection R p)

theorem primeErasedChainProjection_basis_of_absent (p : Nat.Primes) {k : ℕ}
    (s : Set.powersetCard Nat.Primes k) (hp : p ∉ s.val) :
    primeErasedChainProjection R p k (primeChainBasis R k s) = primeChainBasis R k s := by
  rw [primeChainBasis_eq_atom]
  unfold primeErasedChainProjection primeChainAtom
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  have hi : Set.powersetCard.ofFinEmbEquiv.symm s i ≠ p := fun h =>
    hp ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s p).mp ⟨i,h⟩)
  simp only [Function.comp_apply,primeErasedVertexProjection_single,if_neg hi]

theorem primeErasedChainProjection_basis_of_present (p : Nat.Primes) {k : ℕ}
    (s : Set.powersetCard Nat.Primes k) (hp : p ∈ s.val) :
    primeErasedChainProjection R p k (primeChainBasis R k s) = 0 := by
  obtain ⟨i,hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s p).mpr hp
  rw [primeChainBasis_eq_atom]
  unfold primeErasedChainProjection primeChainAtom
  rw [exteriorPower.map_apply_ιMulti]
  apply AlternatingMap.map_coord_zero _ i
  simp only [Function.comp_apply,primeErasedVertexProjection_single,if_pos hi]

/-- A cone vanishes on a face already containing its vertex. -/
theorem primeChainCone_basis_of_present (p : Nat.Primes) {k : ℕ}
    (s : Set.powersetCard Nat.Primes k) (hp : p ∈ s.val) :
    primeChainCone R k p (primeChainBasis R k s) = 0 := by
  obtain ⟨i,hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s p).mpr hp
  rw [primeChainBasis_eq_atom,primeChainCone_atom]
  unfold primeChainAtom
  apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := i.succ)
  · simp only [Fin.cons_zero,Fin.cons_succ,hi]
  · exact (Fin.succ_ne_zero i).symm

/-- Every prime cone squares to zero. -/
theorem primeChainCone_sq (p : Nat.Primes) (k : ℕ) :
    (primeChainCone R (k+1) p).comp (primeChainCone R k p) = 0 := by
  apply (primeChainBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply,LinearMap.zero_apply]
  rw [primeChainBasis_eq_atom,primeChainCone_atom,primeChainCone_atom]
  unfold primeChainAtom
  apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := (0 : Fin (k+1)).succ)
  · simp only [Fin.cons_zero,Fin.cons_succ]
  · exact (Fin.succ_ne_zero _).symm

/-- The coordinate functional dual to a specified prime vertex. -/
def primeCoordinateFunctional (p : Nat.Primes) : (Nat.Primes →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun q => if q = p then 1 else 0)

theorem primeCoordinateFunctional_single (p q : Nat.Primes) :
    primeCoordinateFunctional R p (Finsupp.single q 1) = if q = p then 1 else 0 := by
  simp only [primeCoordinateFunctional,Finsupp.linearCombination_single,one_smul]

theorem primeCoordinateFunctional_self (p : Nat.Primes) :
    primeCoordinateFunctional R p (Finsupp.single p 1) = 1 := by
  rw [primeCoordinateFunctional_single,if_pos rfl]

/-- Delete only the specified prime coordinate. -/
abbrev primeCoordinateDeletion (p : Nat.Primes) (k : ℕ) :=
  physicalKoszulDifferential k (primeCoordinateFunctional R p)

theorem primeCoordinateDeletion_basis_of_absent (p : Nat.Primes) (k : ℕ)
    (s : Set.powersetCard Nat.Primes (k+1)) (hp : p ∉ s.val) :
    primeCoordinateDeletion R p k (primeChainBasis R (k+1) s) = 0 := by
  rw [primeChainBasis_eq_atom,primeChainAtom,physicalKoszulDifferential_ιMulti]
  apply Finset.sum_eq_zero
  intro i _
  have hi : Set.powersetCard.ofFinEmbEquiv.symm s i ≠ p := fun h =>
    hp ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s p).mp ⟨i,h⟩)
  simp only [primeCoordinateFunctional_single,if_neg hi,zero_smul,smul_zero]

/-- Deleting a cone retains exactly the faces originally omitting its vertex. -/
theorem primeCoordinateDeletion_comp_cone (p : Nat.Primes) (k : ℕ) :
    (primeCoordinateDeletion R p k).comp (primeChainCone R k p) = primeErasedChainProjection R p k := by
  classical
  apply (primeChainBasis R k).ext
  intro s
  simp only [LinearMap.comp_apply]
  by_cases hp : p ∈ s.val
  · rw [primeChainCone_basis_of_present R p s hp,map_zero,
      primeErasedChainProjection_basis_of_present R p s hp]
  · rw [primeErasedChainProjection_basis_of_absent R p s hp]
    cases k with
    | zero =>
      simpa only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
        primeCoordinateFunctional_self,one_smul] using
        LinearMap.congr_fun
          (koszul_cartan_zero_map (primeCoordinateFunctional R p) (Finsupp.single p (1 : R)))
          (primeChainBasis R 0 s)
    | succ k =>
      have h := LinearMap.congr_fun
        (koszul_cartan_succ k (primeCoordinateFunctional R p) (Finsupp.single p (1 : R)))
        (primeChainBasis R (k+1) s)
      simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
        primeCoordinateFunctional_self,one_smul,
        primeCoordinateDeletion_basis_of_absent R p k s hp,map_zero,add_zero] using h

/-- Within odd cutoff chains, a cone's kernel consists exactly of faces containing its vertex. -/
theorem primeOddConeKernel_eq_span_basis (p : Nat.Primes) (k N : ℕ) :
    primeOddCutoff R k N ⊓ (primeChainCone R k p).ker =
      Submodule.span R (primeChainBasis R k ''
        {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ p ∈ s.val}) := by
  classical
  apply le_antisymm
  · have hm : primeOddCutoff R k N ≤
        (Submodule.span R (primeChainBasis R k ''
          {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ p ∈ s.val})).comap
          (LinearMap.id - primeErasedChainProjection R p k) := by
      rw [primeOddCutoff_eq_span_basis]
      apply Submodule.span_le.mpr
      rintro x ⟨s,hs,rfl⟩
      change primeChainBasis R k s - primeErasedChainProjection R p k (primeChainBasis R k s) ∈
        Submodule.span R (primeChainBasis R k ''
          {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ p ∈ s.val})
      by_cases hp : p ∈ s.val
      · rw [primeErasedChainProjection_basis_of_present R p s hp,sub_zero]
        exact Submodule.subset_span ⟨s,⟨hs.1,hs.2,hp⟩,rfl⟩
      · rw [primeErasedChainProjection_basis_of_absent R p s hp,sub_self]
        exact Submodule.zero_mem _
    intro x hx
    have hz : primeChainCone R k p x = 0 := hx.2
    have he := LinearMap.congr_fun (primeCoordinateDeletion_comp_cone R p k) x
    have hk : primeErasedChainProjection R p k x = 0 := by
      simpa only [LinearMap.comp_apply,hz,map_zero] using he.symm
    have hh := hm hx.1
    change x - primeErasedChainProjection R p k x ∈
      Submodule.span R (primeChainBasis R k ''
        {s | primeFaceProduct s ≤ N ∧ primeTwoLabel ∉ s.val ∧ p ∈ s.val}) at hh
    simpa only [hk,sub_zero] using hh
  · apply Submodule.span_le.mpr
    rintro x ⟨s,hs,rfl⟩
    exact ⟨⟨primeChainBasis_mem_cutoff R s hs.1,
      ⟨primeChainBasis R k s,oddChainProjection_basis_of_odd R s hs.2.1⟩⟩,
      primeChainCone_basis_of_present R p s hs.2.2⟩

#print axioms primeChainCone_sq
#print axioms primeCoordinateDeletion_comp_cone
#print axioms primeOddConeKernel_eq_span_basis
end GaloisForLFunctions.EffectiveScalingGeometry
