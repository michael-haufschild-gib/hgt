import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCycleCoordinates

/-!
# The odd-prime cutoff complex

Deleting the prime-two vertex gives an actual subcomplex for every weighted
boundary. Every remaining prime is at least three, so deletion lowers product
height by a factor of three. Literal inclusions make this subcomplex natural
in height, with its own homology persistence functor.
-/

noncomputable section
open CategoryTheory RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- A vertex functional weights each deletion by its value on the removed prime. -/
theorem primeFunctionalBoundary_atom (phi : (Nat.Primes →₀ R) →ₗ[R] R)
    {k : ℕ} (v : Fin (k+1) → Nat.Primes) :
    physicalKoszulDifferential k phi (primeChainAtom R v) =
      ∑ i : Fin (k+1), ((-1 : ℤ) ^ (i : ℕ)) •
        (phi (Finsupp.single (v i) 1) • primeChainAtom R (fun j => v (i.succAbove j))) := by
  rw [primeChainAtom,physicalKoszulDifferential_ιMulti]
  rfl

/-- An odd prime tuple is an actual odd-cutoff chain at its product height. -/
theorem primeOddChainAtom_mem_cutoff {k N : ℕ} (v : Fin k → Nat.Primes)
    (hv : (∏ i, (v i : ℕ)) ≤ N) (ho : ∀ i, v i ≠ primeTwoLabel) :
    primeChainAtom R v ∈ primeOddCutoff R k N :=
  ⟨Submodule.subset_span ⟨v,hv,rfl⟩,
    ⟨primeChainAtom R v,oddChainProjection_atom_of_odd R v ho⟩⟩

/-- Every boundary in the odd-prime complex lowers product height by at least three. -/
theorem primeOddDifferential_third_cutoff
    (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    primeOddCutoff R (k+1) N ≤
      (primeOddCutoff R k (N/3)).comap (physicalKoszulDifferential k phi) := by
  rw [primeOddCutoff_eq_span_basis R (k+1) N]
  apply Submodule.span_le.mpr
  rintro x ⟨s,hs,rfl⟩
  let v : Fin (k+1) → Nat.Primes := Set.powersetCard.ofFinEmbEquiv.symm s
  have ho : ∀ i, v i ≠ primeTwoLabel := by
    intro i hi
    exact hs.2 ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s primeTwoLabel).mp ⟨i,hi⟩)
  have hv : (∏ i, (v i : ℕ)) ≤ N := (primeFaceProduct_eq_prod_enum s) ▸ hs.1
  change physicalKoszulDifferential k phi (primeChainBasis R (k+1) s) ∈ primeOddCutoff R k (N/3)
  rw [primeChainBasis_eq_atom]
  change physicalKoszulDifferential k phi (primeChainAtom R v) ∈ primeOddCutoff R k (N/3)
  rw [primeFunctionalBoundary_atom]
  apply Submodule.sum_mem
  intro i _
  apply (primeOddCutoff R k (N/3)).toAddSubgroup.zsmul_mem
  apply Submodule.smul_mem
  apply primeOddChainAtom_mem_cutoff R
  · have hpne : (v i : ℕ) ≠ 2 := fun h => ho i (Subtype.ext h)
    have hp3 : 3 ≤ (v i : ℕ) := by
      have hp2 := (v i).property.two_le
      omega
    have hprod : 3 * ∏ j, (v (i.succAbove j) : ℕ) ≤ N := calc
      _ ≤ (v i : ℕ) * ∏ j, (v (i.succAbove j) : ℕ) := Nat.mul_le_mul_right _ hp3
      _ = ∏ j, (v j : ℕ) := (Fin.prod_univ_succAbove (fun j => (v j : ℕ)) i).symm
      _ ≤ N := hv
    omega
  · intro j
    exact ho (i.succAbove j)

/-- The actual weighted deletion differential on odd cutoff modules. -/
def primeOddCutoffDifferential (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    primeOddCutoff R (k+1) N →ₗ[R] primeOddCutoff R k N :=
  (physicalKoszulDifferential k phi).restrict (fun _ hx =>
    primeOddCutoff_mono R k (Nat.div_le_self N 3) (primeOddDifferential_third_cutoff R phi k N hx))

theorem primeOddCutoffDifferential_sq (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    (primeOddCutoffDifferential R phi k N).comp (primeOddCutoffDifferential R phi (k+1) N) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (physicalKoszulDifferential_sq k phi) x.val

/-- Actual augmented prime-cutoff chains after deleting the prime-two vertex. -/
def primeOddCutoffComplex (phi : (Nat.Primes →₀ R) →ₗ[R] R) (N : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (primeOddCutoff R k N))
    (fun k => ModuleCat.ofHom (primeOddCutoffDifferential R phi k N))
    (fun k => ModuleCat.hom_ext (primeOddCutoffDifferential_sq R phi k N))

/-- Literal inclusions give the odd-prime height maps. -/
def primeOddCutoffInclusion (phi : (Nat.Primes →₀ R) →ₗ[R] R) {N M : ℕ} (h : N ≤ M) :
    primeOddCutoffComplex R phi N ⟶ primeOddCutoffComplex R phi M :=
  ChainComplex.ofHom
    (fun k => ModuleCat.ofHom (Submodule.inclusion (primeOddCutoff_mono R k h)))
    (fun k => by
      simp only [primeOddCutoffComplex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

theorem primeOddCutoffInclusion_refl (phi : (Nat.Primes →₀ R) →ₗ[R] R) (N : ℕ) :
    primeOddCutoffInclusion R phi (le_refl N) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

theorem primeOddCutoffInclusion_trans (phi : (Nat.Primes →₀ R) →ₗ[R] R)
    {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    primeOddCutoffInclusion R phi h ≫ primeOddCutoffInclusion R phi g =
      primeOddCutoffInclusion R phi (h.trans g) := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

/-- The actual odd-prime chain persistence functor. -/
def primeOddCutoffPersistence (phi : (Nat.Primes →₀ R) →ₗ[R] R) :
    ℕ ⥤ ChainComplex (ModuleCat R) ℕ where
  obj N := primeOddCutoffComplex R phi N
  map h := primeOddCutoffInclusion R phi h.le
  map_id N := primeOddCutoffInclusion_refl R phi N
  map_comp h g := (primeOddCutoffInclusion_trans R phi h.le g.le).symm

/-- Actual homology persistence of the prime-two-deleted complex. -/
def primeOddCutoffHomology (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k : ℕ) : ℕ ⥤ ModuleCat R :=
  primeOddCutoffPersistence R phi ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k

/-- Forgetting the odd-support restriction is an actual inclusion of complexes. -/
def primeOddCutoffToFull (phi : (Nat.Primes →₀ R) →ₗ[R] R) (N : ℕ) :
    primeOddCutoffComplex R phi N ⟶ primeCutoffComplex R phi N :=
  ChainComplex.ofHom
    (fun k => ModuleCat.ofHom (Submodule.inclusion
      (show primeOddCutoff R k N ≤ primeChainCutoff R k N from inf_le_left)))
    (fun k => by
      simp only [primeOddCutoffComplex,primeCutoffComplex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- The odd-support inclusion commutes with every height map. -/
theorem primeOddCutoffToFull_natural (phi : (Nat.Primes →₀ R) →ₗ[R] R)
    {N M : ℕ} (h : N ≤ M) :
    primeOddCutoffInclusion R phi h ≫ primeOddCutoffToFull R phi M =
      primeOddCutoffToFull R phi N ≫ primeCutoffInclusion R phi h := by
  apply HomologicalComplex.Hom.ext
  funext k
  rfl

/-- Odd chains form a subfunctor of the actual prime-height complex. -/
def primeOddPersistenceToFull (phi : (Nat.Primes →₀ R) →ₗ[R] R) :
    primeOddCutoffPersistence R phi ⟶ primeCutoffPersistence R phi where
  app N := primeOddCutoffToFull R phi N
  naturality _ _ h := primeOddCutoffToFull_natural R phi h.le

#print axioms primeOddDifferential_third_cutoff
#print axioms primeOddCutoffComplex
#print axioms primeOddCutoffHomology
#print axioms primeOddPersistenceToFull
end GaloisForLFunctions.EffectiveScalingGeometry
