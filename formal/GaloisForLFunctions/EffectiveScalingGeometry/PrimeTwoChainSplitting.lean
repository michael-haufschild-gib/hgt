import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleBasis
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeBoundaryHeight

/-!
# Splitting off the prime-two vertex

Contraction by the prime-two coordinate splits an actual cutoff chain into
its odd component and a prime-two cone. The latter component has half the
product height. This is a linear equivalence of the actual cutoff modules
over every commutative ring, independent of the chosen boundary functional.
-/

noncomputable section
open RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- The coordinate functional of prime two. -/
def primeTwoFunctional : (Nat.Primes →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun p : Nat.Primes => if p = primeTwoLabel then 1 else 0)

theorem primeTwoFunctional_single (p : Nat.Primes) :
    primeTwoFunctional R (Finsupp.single p 1) = if p = primeTwoLabel then 1 else 0 := by
  simp only [primeTwoFunctional,Finsupp.linearCombination_single,one_smul]

/-- Contract only the prime-two coordinate. -/
abbrev primeTwoDeletion (k : ℕ) := physicalKoszulDifferential k (primeTwoFunctional R)

theorem primeTwoDeletion_atom_of_odd {k : ℕ} (v : Fin (k+1) → Nat.Primes)
    (hv : ∀ i, v i ≠ primeTwoLabel) :
    primeTwoDeletion R k (primeChainAtom R v) = 0 := by
  rw [primeChainAtom,physicalKoszulDifferential_ιMulti]
  apply Finset.sum_eq_zero
  intro i _
  simp only [primeTwoFunctional_single,if_neg (hv i),zero_smul,smul_zero]

theorem primeTwoDeletion_comp_oddProjection (k : ℕ) :
    (primeTwoDeletion R k).comp (oddChainProjection R (k+1)) = 0 := by
  classical
  apply (primeChainBasis R (k+1)).ext
  intro s
  simp only [LinearMap.comp_apply,LinearMap.zero_apply]
  by_cases hs : primeTwoLabel ∈ s.val
  · rw [oddChainProjection_basis_of_even R s hs,map_zero]
  · rw [oddChainProjection_basis_of_odd R s hs,primeChainBasis_eq_atom]
    apply primeTwoDeletion_atom_of_odd
    intro i hi
    exact hs ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mp ⟨i,hi⟩)

theorem primeTwoDeletion_cartan (k : ℕ) :
    (primeTwoDeletion R (k+1)).comp (primeChainCone R (k+1) primeTwoLabel) +
      (primeChainCone R k primeTwoLabel).comp (primeTwoDeletion R k) = LinearMap.id := by
  simpa only [primeTwoFunctional_single,if_pos rfl,ite_true,one_smul] using
    koszul_cartan_succ k (primeTwoFunctional R) (Finsupp.single primeTwoLabel (1 : R))

/-- Splitting a chain into the faces omitting and containing two. -/
theorem oddProjection_add_cone_twoDeletion (k : ℕ) :
    oddChainProjection R (k+1) +
      (primeChainCone R k primeTwoLabel).comp (primeTwoDeletion R k) = LinearMap.id := by
  classical
  apply (primeChainBasis R (k+1)).ext
  intro s
  simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply]
  by_cases hs : primeTwoLabel ∈ s.val
  · have h := LinearMap.congr_fun (primeTwoDeletion_cartan R k) (primeChainBasis R (k+1) s)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,
      primeChainCone_basis_of_even R s hs,map_zero,zero_add,
      oddChainProjection_basis_of_even R s hs] using h
  · have hz := LinearMap.congr_fun (primeTwoDeletion_comp_oddProjection R k)
      (primeChainBasis R (k+1) s)
    rw [LinearMap.comp_apply,oddChainProjection_basis_of_odd R s hs,LinearMap.zero_apply] at hz
    rw [oddChainProjection_basis_of_odd R s hs,hz,map_zero,add_zero]

/-- Deleting two from its cone retains precisely the odd component. -/
theorem primeTwoDeletion_comp_cone (k : ℕ) :
    (primeTwoDeletion R k).comp (primeChainCone R k primeTwoLabel) = oddChainProjection R k := by
  cases k with
  | zero =>
    rw [oddChainProjection_zero]
    simpa only [primeTwoFunctional_single,if_pos rfl,ite_true,one_smul] using
      koszul_cartan_zero_map (primeTwoFunctional R) (Finsupp.single primeTwoLabel (1 : R))
  | succ k =>
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (primeTwoDeletion_cartan R k) x
    have g := LinearMap.congr_fun (oddProjection_add_cone_twoDeletion R k) x
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply] at h g
    exact add_right_cancel (h.trans g.symm)

/-- The two-deletion lands in odd chains. -/
theorem oddProjection_comp_twoDeletion (k : ℕ) :
    (oddChainProjection R k).comp (primeTwoDeletion R k) = primeTwoDeletion R k := by
  cases k with
  | zero => rw [oddChainProjection_zero,LinearMap.id_comp]
  | succ k =>
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (oddProjection_add_cone_twoDeletion R k)
      (primeTwoDeletion R (k+1) x)
    have hz : primeTwoDeletion R k (primeTwoDeletion R (k+1) x) = 0 :=
      LinearMap.congr_fun (physicalKoszulDifferential_sq k (primeTwoFunctional R)) x
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,
      hz,map_zero,add_zero] using h

/-- Two-deletion lowers the cutoff by two and removes its even support. -/
theorem primeTwoDeletion_half_odd (k N : ℕ) :
    primeChainCutoff R (k+1) N ≤ (primeOddCutoff R k (N/2)).comap (primeTwoDeletion R k) := by
  intro x hx
  exact ⟨primeChainDifferential_half_cutoff R (primeTwoFunctional R) k N hx,
    ⟨primeTwoDeletion R k x,LinearMap.congr_fun (oddProjection_comp_twoDeletion R k) x⟩⟩

/-- Actual chains split into an odd chain and the two-cone of a half-height odd chain. -/
def primeCutoffTwoSplit (k N : ℕ) :
    primeChainCutoff R (k+1) N ≃ₗ[R]
      primeOddCutoff R (k+1) N × primeOddCutoff R k (N/2) where
  toFun x := (⟨oddChainProjection R (k+1) x.val,
    oddChainProjection_cutoff R (k+1) N x.property,⟨x.val,rfl⟩⟩,
    ⟨primeTwoDeletion R k x.val,primeTwoDeletion_half_odd R k N x.property⟩)
  invFun x := ⟨x.1.val + primeChainCone R k primeTwoLabel x.2.val,
    Submodule.add_mem _ x.1.property.1
      (primeChainCutoff_mono R (k+1) (show 2*(N/2) ≤ N by omega)
        (primeChainCone_cutoff R k (N/2) primeTwoLabel x.2.property.1))⟩
  left_inv x := Subtype.ext (LinearMap.congr_fun (oddProjection_add_cone_twoDeletion R k) x.val)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change oddChainProjection R (k+1) (x.1.val + primeChainCone R k primeTwoLabel x.2.val) = x.1.val
      rw [map_add]
      have hz := LinearMap.congr_fun (oddChainProjection_comp_cone R k) x.2.val
      rw [show oddChainProjection R (k+1) (primeChainCone R k primeTwoLabel x.2.val) = 0 from hz,
        add_zero]
      exact oddChainProjection_fixes_range R (k+1) ⟨x.1.val,x.1.property.2⟩
    · apply Subtype.ext
      change primeTwoDeletion R k (x.1.val + primeChainCone R k primeTwoLabel x.2.val) = x.2.val
      rw [map_add]
      have ho := oddChainProjection_fixes_range R (k+1) ⟨x.1.val,x.1.property.2⟩
      have hz := LinearMap.congr_fun (primeTwoDeletion_comp_oddProjection R k) x.1.val
      have he : primeTwoDeletion R k x.1.val = 0 := by
        simpa only [LinearMap.comp_apply,LinearMap.zero_apply,ho] using hz
      rw [he,zero_add]
      exact (LinearMap.congr_fun (primeTwoDeletion_comp_cone R k) x.2.val).trans
        (oddChainProjection_fixes_range R k ⟨x.2.val,x.2.property.2⟩)
  map_add' x y := by apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ _ _
  map_smul' a x := by apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ _ _

#print axioms oddProjection_add_cone_twoDeletion
#print axioms primeCutoffTwoSplit
end GaloisForLFunctions.EffectiveScalingGeometry
