import GaloisForLFunctions.HTGeometry.HollowSimplexBouquet

/-!
# Hasse reconstruction on hollow-simplex bouquet homology

For pairwise disjoint hollow simplices, descended face detectors are independent local places.
Base Koszul classes assemble arbitrary local packets, so first homology modulo classes invisible at
every hollow component is exactly finite coordinate space.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F α : Type*} [Field F] [DecidableEq α] [Fintype α]

/-- First Koszul homology containing hollow-simplex classes. -/
abbrev SRFirstKoszulHomology (F : Type*) [Field F] (facets : Finset (Finset α)) :=
  (α → stanleyReisnerRing F facets) ⧸ srKoszulBoundaries (R := F) facets

/-- Assemble one global homology class from coefficients on a finite hollow-simplex bouquet. -/
noncomputable def hollowBouquetHasseAssembly
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α) :
    (Fin k → F) →ₗ[F] SRFirstKoszulHomology F facets :=
  Fintype.linearCombination F fun m => srHollowBaseClass F facets (σ m) (i₀ m)

theorem hollowBouquetHasseAssembly_apply
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α) (c : Fin k → F) :
    hollowBouquetHasseAssembly facets σ i₀ c =
      ∑ m, c m • srHollowBaseClass F facets (σ m) (i₀ m) := by
  exact Fintype.linearCombination_apply F _ c

/-- Simultaneous descended hollow-face detectors, one local place per bouquet component. -/
noncomputable def hollowBouquetHasseProfile
    (facets : Finset (Finset α)) {k : ℕ} (σ : Fin k → Finset α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v)) :
    SRFirstKoszulHomology F facets →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun m => srHollowDetectorTor F facets (σ m) (hface m)

@[simp] theorem hollowBouquetHasseProfile_apply
    (facets : Finset (Finset α)) {k : ℕ} (σ : Fin k → Finset α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (x : SRFirstKoszulHomology F facets) (m : Fin k) :
    hollowBouquetHasseProfile facets σ hface x m =
      srHollowDetectorTor F facets (σ m) (hface m) x :=
  rfl

/-- Local detectors form a Kronecker family on pairwise-disjoint base classes. -/
theorem hollowBouquetHasseProfile_base
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n))
    (m n : Fin k) :
    hollowBouquetHasseProfile facets σ hface
        (srHollowBaseClass F facets (σ n) (i₀ n)) m =
      if m = n then 1 else 0 := by
  classical
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl]
    exact srHollowDetectorTor_base facets (σ m) (hface m) (hmem m)
  · rw [if_neg hmn]
    change srHollowDetectorₗ F facets (σ m)
      (srHollowSimplexSyzygyVec F facets (σ n)
        (fun i => if i = i₀ n then (1 : F) else 0)) = 0
    exact srHollowDetectorₗ_disjoint facets (σ m) (σ n) (hdisj m n hmn) _

/-- Local detection is a right inverse to assembly: every finite local packet glues globally. -/
theorem hollowBouquetHasseProfile_assembly
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n))
    (c : Fin k → F) :
    hollowBouquetHasseProfile (F := F) facets σ hface
        (hollowBouquetHasseAssembly (F := F) facets σ i₀ c) = c := by
  classical
  funext m
  rw [hollowBouquetHasseAssembly_apply, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    hollowBouquetHasseProfile_base facets σ i₀ hface hmem hdisj]
  simp

/-- Every local detector packet is realized by a global bouquet class. -/
theorem hollowBouquetHasseProfile_surjective
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n)) :
    Function.Surjective (hollowBouquetHasseProfile (F := F) facets σ hface) := by
  intro c
  exact ⟨hollowBouquetHasseAssembly (F := F) facets σ i₀ c,
    hollowBouquetHasseProfile_assembly (F := F) facets σ i₀ hface hmem hdisj c⟩

/-- Assembly is faithful because local detectors recover every coefficient. -/
theorem hollowBouquetHasseAssembly_injective
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n)) :
    Function.Injective (hollowBouquetHasseAssembly (F := F) facets σ i₀) := by
  intro c d hcd
  rw [← hollowBouquetHasseProfile_assembly (F := F) facets σ i₀ hface hmem hdisj c,
    ← hollowBouquetHasseProfile_assembly (F := F) facets σ i₀ hface hmem hdisj d, hcd]

/-- Global homology modulo classes invisible at every bouquet place is full local coordinate space. -/
noncomputable def hollowBouquetHasseQuotientEquiv
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n)) :
    (SRFirstKoszulHomology F facets ⧸
        LinearMap.ker (hollowBouquetHasseProfile (F := F) facets σ hface)) ≃ₗ[F]
      (Fin k → F) :=
  LinearMap.quotKerEquivOfSurjective _
    (hollowBouquetHasseProfile_surjective (F := F) facets σ i₀ hface hmem hdisj)

@[simp] theorem hollowBouquetHasseQuotientEquiv_mk
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α) (i₀ : Fin k → α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (hmem : ∀ m, i₀ m ∈ σ m)
    (hdisj : ∀ m n, m ≠ n → Disjoint (σ m) (σ n))
    (x : SRFirstKoszulHomology F facets) :
    hollowBouquetHasseQuotientEquiv (F := F) facets σ i₀ hface hmem hdisj
        (Submodule.Quotient.mk x) =
      hollowBouquetHasseProfile (F := F) facets σ hface x := by
  rfl

/-- Two homology classes agree modulo invisible classes iff all bouquet detectors agree. -/
theorem hollowBouquet_congr_hasse_iff
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (x y : SRFirstKoszulHomology F facets) :
    x - y ∈ LinearMap.ker (hollowBouquetHasseProfile (F := F) facets σ hface) ↔
      ∀ m, srHollowDetectorTor F facets (σ m) (hface m) x =
        srHollowDetectorTor F facets (σ m) (hface m) y := by
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h m
    exact congrFun h m
  · intro h
    funext m
    exact h m

/-- Every nonzero local-global homology class has a hollow-simplex detector witness. -/
theorem hollowBouquetClass_ne_zero_iff_exists_localWitness
    (facets : Finset (Finset α)) {k : ℕ}
    (σ : Fin k → Finset α)
    (hface : ∀ m, ∀ v ∈ σ m,
      IsFaceOf (↑facets : Set (Finset α)) ((σ m).erase v))
    (x : SRFirstKoszulHomology F facets) :
    Submodule.Quotient.mk x ≠
        (0 : SRFirstKoszulHomology F facets ⧸
          LinearMap.ker (hollowBouquetHasseProfile (F := F) facets σ hface)) ↔
      ∃ m, srHollowDetectorTor F facets (σ m) (hface m) x ≠ 0 := by
  rw [ne_eq, Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  constructor
  · intro h
    by_contra hn
    apply h
    funext m
    exact not_ne_iff.mp (not_exists.mp hn m)
  · rintro ⟨m, hm⟩ hzero
    exact hm (congrFun hzero m)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every codimension-one face of a concrete bouquet block belongs to the bouquet complex. -/
theorem hbSigma_erase_isFace {k n : ℕ} (m : Fin k) {v : Fin k × Fin (n + 1)}
    (hv : v ∈ hbSigma k n m) :
    IsFaceOf (↑(hbFacets k n) : Set (Finset (Fin k × Fin (n + 1))))
      ((hbSigma k n m).erase v) :=
  ⟨(hbSigma k n m).erase v,
    Finset.mem_coe.mpr (hbFacets_erase_mem m hv), Finset.Subset.refl _⟩

/-- Explicit assembly of arbitrary coordinates into concrete bouquet homology. -/
noncomputable def concreteHollowBouquetHasseAssembly
    (F : Type*) [Field F] {k n : ℕ} :
    (Fin k → F) →ₗ[F] SRFirstKoszulHomology F (hbFacets k n) :=
  hollowBouquetHasseAssembly (hbFacets k n) (hbSigma k n) fun m => (m, 0)

/-- Explicit detector packet on concrete disjoint hollow simplices. -/
noncomputable def concreteHollowBouquetHasseProfile
    (F : Type*) [Field F] {k n : ℕ} :
    SRFirstKoszulHomology F (hbFacets k n) →ₗ[F] (Fin k → F) :=
  hollowBouquetHasseProfile (hbFacets k n) (hbSigma k n) fun m _v hv =>
    hbSigma_erase_isFace m hv

/-- Concrete local detectors recover every assembled coordinate packet. -/
theorem concreteHollowBouquetHasseProfile_assembly
    (F : Type*) [Field F] {k n : ℕ} (c : Fin k → F) :
    concreteHollowBouquetHasseProfile F (k := k) (n := n)
        (concreteHollowBouquetHasseAssembly F (n := n) c) = c := by
  exact hollowBouquetHasseProfile_assembly
    (F := F) (hbFacets k n) (hbSigma k n) (fun m => (m, 0))
    (fun m v hv => hbSigma_erase_isFace m hv)
    (fun m => Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self m, Finset.mem_univ 0⟩)
    (fun _ _ h => hbSigma_disjoint h) c

/-- Every concrete finite detector packet has an explicit global homology realization. -/
theorem concreteHollowBouquetHasseProfile_surjective
    (F : Type*) [Field F] {k n : ℕ} :
    Function.Surjective (concreteHollowBouquetHasseProfile F (k := k) (n := n)) := by
  intro c
  exact ⟨concreteHollowBouquetHasseAssembly F (n := n) c,
    concreteHollowBouquetHasseProfile_assembly F (n := n) c⟩

/-- Concrete bouquet homology modulo simultaneous detector invisibility is `F^k`. -/
noncomputable def concreteHollowBouquetHasseQuotientEquiv
    (F : Type*) [Field F] {k n : ℕ} :
    (SRFirstKoszulHomology F (hbFacets k n) ⧸
      LinearMap.ker (concreteHollowBouquetHasseProfile F (n := n))) ≃ₗ[F] (Fin k → F) :=
  LinearMap.quotKerEquivOfSurjective _
    (concreteHollowBouquetHasseProfile_surjective F (n := n))

@[simp] theorem concreteHollowBouquetHasseQuotientEquiv_mk
    (F : Type*) [Field F] {k n : ℕ}
    (x : SRFirstKoszulHomology F (hbFacets k n)) :
    concreteHollowBouquetHasseQuotientEquiv F (n := n) (Submodule.Quotient.mk x) =
      concreteHollowBouquetHasseProfile F (n := n) x := by
  rfl

end

end GaloisForLFunctions.HTGeometry
