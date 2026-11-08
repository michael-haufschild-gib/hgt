import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCutoffComplex
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeChainBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.Homotopy

/-!
# Sharp tripled-height contraction for integral prime weights

Give each prime vertex boundary coefficient equal to that prime. The difference
of the prime-three and prime-two cones contracts this weighted complex, since
`3−2=1`, and increases prime-product height by at most three. The actual cutoff
inclusion from `N` to `3N` is nullhomotopic, so every augmented homology map
vanishes. The construction works over every commutative ring and is natural
under height inclusions. Over the integers, parity of the empty-chain
coefficient prevents filling the height-one generator at height two. Thus
three is the least uniform integer dilation for augmented fillings.
-/

noncomputable section
open CategoryTheory RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Prime-labelled vertices have their actual integer values as boundary coefficients. -/
def primeValueFunctional : (Nat.Primes →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun p : Nat.Primes => (p.val : R))

theorem primeValueFunctional_single (p : Nat.Primes) :
    primeValueFunctional R (Finsupp.single p 1) = (p.val : R) := by
  simp only [primeValueFunctional,Finsupp.linearCombination_single,one_smul]

abbrev primeValueBoundary (k : ℕ) := physicalKoszulDifferential k (primeValueFunctional R)

/-- The difference of the prime-three and prime-two cones uses the identity `3−2=1`. -/
def primeBezoutCone (k : ℕ) : PrimeChainSpace R k →ₗ[R] PrimeChainSpace R (k+1) :=
  primeChainCone R k ⟨3,Nat.prime_three⟩ - primeChainCone R k ⟨2,Nat.prime_two⟩

/-- Adjoining either two or three increases the cutoff by at most three. -/
theorem primeBezoutCone_cutoff (k N : ℕ) :
    primeChainCutoff R k N ≤ (primeChainCutoff R (k+1) (3*N)).comap (primeBezoutCone R k) := by
  intro x hx
  change primeChainCone R k ⟨3,Nat.prime_three⟩ x - primeChainCone R k ⟨2,Nat.prime_two⟩ x ∈ primeChainCutoff R (k+1) (3*N)
  apply Submodule.sub_mem
  · exact primeChainCone_cutoff R k N ⟨3,Nat.prime_three⟩ hx
  · exact primeChainCutoff_mono R (k+1) (Nat.mul_le_mul_right N (show (2 : ℕ) ≤ 3 by omega))
      (primeChainCone_cutoff R k N ⟨2,Nat.prime_two⟩ hx)

/-- Cartan's identity for the prime-valued boundary and one prime cone. -/
theorem primeValueBoundary_cartan (k : ℕ) (p : Nat.Primes) :
    (primeValueBoundary R (k+1)).comp (primeChainCone R (k+1) p) +
      (primeChainCone R k p).comp (primeValueBoundary R k) = (p.val : R) • LinearMap.id := by
  simpa only [primeValueFunctional_single] using
    koszul_cartan_succ k (primeValueFunctional R) (Finsupp.single p (1 : R))

/-- The integer Bézout relation contracts the weighted complex in positive degrees. -/
theorem primeBezoutCone_contracts (k : ℕ) :
    (primeValueBoundary R (k+1)).comp (primeBezoutCone R (k+1)) +
      (primeBezoutCone R k).comp (primeValueBoundary R k) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h3 := LinearMap.congr_fun (primeValueBoundary_cartan R k ⟨3,Nat.prime_three⟩) x
  have h2 := LinearMap.congr_fun (primeValueBoundary_cartan R k ⟨2,Nat.prime_two⟩) x
  simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,Nat.cast_ofNat] at h3 h2
  change primeValueBoundary R (k+1)
    (primeChainCone R (k+1) ⟨3,Nat.prime_three⟩ x - primeChainCone R (k+1) ⟨2,Nat.prime_two⟩ x) +
      (primeChainCone R k ⟨3,Nat.prime_three⟩ (primeValueBoundary R k x) -
        primeChainCone R k ⟨2,Nat.prime_two⟩ (primeValueBoundary R k x)) = x
  rw [map_sub]
  calc
    _ = (primeValueBoundary R (k+1) (primeChainCone R (k+1) ⟨3,Nat.prime_three⟩ x) +
          primeChainCone R k ⟨3,Nat.prime_three⟩ (primeValueBoundary R k x)) -
        (primeValueBoundary R (k+1) (primeChainCone R (k+1) ⟨2,Nat.prime_two⟩ x) +
          primeChainCone R k ⟨2,Nat.prime_two⟩ (primeValueBoundary R k x)) := by abel
    _ = (3 : R) • x - (2 : R) • x := by rw [h3,h2]
    _ = x := by
      have hs : (3 : R) - (2 : R) = 1 := by ring
      exact (sub_smul (3 : R) (2 : R) x).symm.trans (by rw [hs,one_smul])

/-- The same contraction includes the empty augmented degree. -/
theorem primeBezoutCone_contracts_zero :
    (primeValueBoundary R 0).comp (primeBezoutCone R 0) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h3 := LinearMap.congr_fun
    (koszul_cartan_zero_map (primeValueFunctional R) (Finsupp.single ⟨3,Nat.prime_three⟩ 1)) x
  have h2 := LinearMap.congr_fun
    (koszul_cartan_zero_map (primeValueFunctional R) (Finsupp.single ⟨2,Nat.prime_two⟩ 1)) x
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,
    primeValueFunctional_single] at h3 h2
  change primeValueBoundary R 0
    (primeChainCone R 0 ⟨3,Nat.prime_three⟩ x - primeChainCone R 0 ⟨2,Nat.prime_two⟩ x) = x
  rw [map_sub,h3,h2,← sub_smul]
  norm_num

/-- Every actual weighted cycle at height `N` has a filling at height `3N`. -/
theorem primeValueCycle_fills_triple (k N : ℕ)
    (x : ↥(primeChainCutoff R (k+1) N ⊓ (primeValueBoundary R k).ker)) :
    ∃ y : primeChainCutoff R (k+2) (3*N), primeValueBoundary R (k+1) y.val = x.val := by
  refine ⟨⟨primeBezoutCone R (k+1) x.val,primeBezoutCone_cutoff R (k+1) N x.property.1⟩,?_⟩
  have he := LinearMap.congr_fun (primeBezoutCone_contracts R k) x.val
  have hx : primeValueBoundary R k x.val = 0 := x.property.2
  simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,hx,map_zero,add_zero] using he

/-- The empty augmented chain is filled by the same arithmetic cone. -/
theorem primeValueZero_fills_triple (N : ℕ) (x : primeChainCutoff R 0 N) :
    ∃ y : primeChainCutoff R 1 (3*N), primeValueBoundary R 0 y.val = x.val :=
  ⟨⟨primeBezoutCone R 0 x.val,primeBezoutCone_cutoff R 0 N x.property⟩,
    LinearMap.congr_fun (primeBezoutCone_contracts_zero R) x.val⟩

/-- The arithmetic contraction restricts to the actual height modules. -/
def primeBezoutCutoffCone (k N : ℕ) :
    primeChainCutoff R k N →ₗ[R] primeChainCutoff R (k+1) (3*N) :=
  (primeBezoutCone R k).restrict (fun _ hx => primeBezoutCone_cutoff R k N hx)

/-- Raising height and taking the arithmetic cone commute exactly. -/
theorem primeBezoutCutoffCone_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (Submodule.inclusion (primeChainCutoff_mono R (k+1) (Nat.mul_le_mul_left 3 h))).comp
      (primeBezoutCutoffCone R k N) =
    (primeBezoutCutoffCone R k M).comp (Submodule.inclusion (primeChainCutoff_mono R k h)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The arithmetic cone in each adjacent degree of the actual cutoff complexes. -/
def primeBezoutHomotopyComponent (N i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    (primeCutoffComplex R (primeValueFunctional R) N).X i ⟶
      (primeCutoffComplex R (primeValueFunctional R) (3*N)).X j := by
  have hj : i+1=j := h
  subst j
  exact ModuleCat.ofHom (primeBezoutCutoffCone R i N)

/-- The map `dh+hd` supplied by the actual bounded arithmetic cone. -/
def primeBezoutNullMap (N : ℕ) :
    primeCutoffComplex R (primeValueFunctional R) N ⟶
      primeCutoffComplex R (primeValueFunctional R) (3*N) :=
  Homotopy.nullHomotopicMap' (primeBezoutHomotopyComponent R N)

/-- The cone homotopy's chain map is precisely the original height inclusion. -/
theorem primeBezoutNullMap_eq_inclusion (N : ℕ) :
    primeBezoutNullMap R N = primeCutoffInclusion R (primeValueFunctional R) (show N ≤ 3*N by omega) := by
  apply HomologicalComplex.Hom.ext
  funext k
  cases k with
  | zero =>
    rw [primeBezoutNullMap,Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (fun l => by simp [ComplexShape.down_Rel])]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change primeValueBoundary R 0 (primeBezoutCone R 0 x.val) = x.val
    exact LinearMap.congr_fun (primeBezoutCone_contracts_zero R) x.val
  | succ k =>
    rw [primeBezoutNullMap,Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (k+2) (k+1) from rfl)
      (show (ComplexShape.down ℕ).Rel (k+1) k from rfl)]
    rw [show (primeCutoffComplex R (primeValueFunctional R) N).d (k+1) k =
      ModuleCat.ofHom (primeCutoffDifferential R (primeValueFunctional R) k N) from by
        simp only [primeCutoffComplex,ChainComplex.of_d]]
    rw [show (primeCutoffComplex R (primeValueFunctional R) (3*N)).d (k+2) (k+1) =
      ModuleCat.ofHom (primeCutoffDifferential R (primeValueFunctional R) (k+1) (3*N)) from by
        change (primeCutoffComplex R (primeValueFunctional R) (3*N)).d ((k+1)+1) (k+1) = _
        simp only [primeCutoffComplex,ChainComplex.of_d]]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change primeBezoutCone R k (primeValueBoundary R k x.val) +
      primeValueBoundary R (k+1) (primeBezoutCone R (k+1) x.val) = x.val
    exact (add_comm _ _).trans (LinearMap.congr_fun (primeBezoutCone_contracts R k) x.val)

/-- The actual weighted inclusion from `N` to `3N` is nullhomotopic. -/
def primeValueInclusionNullhomotopy (N : ℕ) :
    Homotopy (primeCutoffInclusion R (primeValueFunctional R) (show N ≤ 3*N by omega)) 0 :=
  (Homotopy.ofEq (primeBezoutNullMap_eq_inclusion R N).symm).trans
    (Homotopy.nullHomotopy' (primeBezoutHomotopyComponent R N))

/-- Every actual augmented weighted homology persistence map vanishes after tripling height. -/
theorem primeValueHomology_triple_zero (k N : ℕ) :
    (primeCutoffHomology R (primeValueFunctional R) k).map (homOfLE (show N ≤ 3*N by omega)) = 0 := by
  change HomologicalComplex.homologyMap
    (primeCutoffInclusion R (primeValueFunctional R) (show N ≤ 3*N by omega)) k = 0
  exact ((primeValueInclusionNullhomotopy R N).homologyMap_eq k).trans
    (HomologicalComplex.homologyMap_zero _ _ k)

/-- The weighted boundary is the alternating deletion sum with the removed prime as coefficient. -/
theorem primeValueBoundary_atom {k : ℕ} (v : Fin (k+1) → Nat.Primes) :
    primeValueBoundary R k (primeChainAtom R v) =
      ∑ i : Fin (k+1), ((-1 : ℤ) ^ (i : ℕ)) •
        ((v i).val : R) • primeChainAtom R (fun j => v (i.succAbove j)) := by
  rw [primeChainAtom,physicalKoszulDifferential_ιMulti]
  simp only [primeValueFunctional_single]
  rfl

/-- The empty prime support. -/
def primeEmptyFace : Set.powersetCard Nat.Primes 0 := ⟨∅,Finset.card_empty⟩

local instance primeWeightedIntegerChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- The parity of the empty-chain coefficient detects the first weighted torsion. -/
def primeEmptyParity : PrimeChainSpace ℤ 0 →ₗ[ℤ] ZMod 2 :=
  (Finsupp.linearCombination ℤ (fun _ : Set.powersetCard Nat.Primes 0 => (1 : ZMod 2))).comp
    (primeChainBasis ℤ 0).repr.toLinearMap

theorem primeEmptyParity_basis : primeEmptyParity (primeChainBasis ℤ 0 primeEmptyFace) = 1 := by
  change Finsupp.linearCombination ℤ (fun _ : Set.powersetCard Nat.Primes 0 => (1 : ZMod 2))
    ((primeChainBasis ℤ 0).repr (primeChainBasis ℤ 0 primeEmptyFace)) = _
  rw [Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

/-- At height two every weighted vertex boundary has even empty-chain coefficient. -/
theorem primeValueBoundary_two_parity :
    primeChainCutoff ℤ 1 2 ≤ (primeEmptyParity.comp (primeValueBoundary ℤ 0)).ker := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  have hv' : (v 0).val ≤ 2 := by simpa only [Fin.prod_univ_one] using hv
  have hp : (v 0).val = 2 := le_antisymm hv' (v 0).property.two_le
  change primeEmptyParity (primeValueBoundary ℤ 0 (primeChainAtom ℤ v)) = 0
  rw [primeValueBoundary_atom,Fin.sum_univ_one]
  simp only [Fin.val_zero,pow_zero,one_smul,hp,Nat.cast_ofNat]
  rw [map_smul,zsmul_eq_mul]
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [show ((2 : ℤ) : ZMod 2) = (2 : ZMod 2) from rfl,hz,zero_mul]

/-- The empty generator at height one cannot be filled at height two over the integers. -/
theorem primeValueEmpty_not_filled_at_two :
    ∃ x : primeChainCutoff ℤ 0 1,
      ∀ y : primeChainCutoff ℤ 1 2, primeValueBoundary ℤ 0 y.val ≠ x.val := by
  refine ⟨⟨primeChainBasis ℤ 0 primeEmptyFace,primeChainBasis_mem_cutoff ℤ primeEmptyFace ?_⟩,?_⟩
  · exact le_rfl
  · intro y he
    have hz := primeValueBoundary_two_parity y.property
    change primeEmptyParity (primeValueBoundary ℤ 0 y.val) = 0 at hz
    rw [he,primeEmptyParity_basis] at hz
    exact one_ne_zero hz

#print axioms primeValueInclusionNullhomotopy
#print axioms primeValueHomology_triple_zero
#print axioms primeValueCycle_fills_triple
#print axioms primeValueZero_fills_triple
#print axioms primeBezoutCutoffCone_natural
#print axioms primeValueEmpty_not_filled_at_two
end GaloisForLFunctions.EffectiveScalingGeometry
