import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlocks
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeFaces

/-!
# Actual two-prime block coordinates

Bounded core/tag labels index a basis of the original prime-valued cutoff
chains. Its coordinate equivalence is natural in height: inclusion extends
the same coefficients by zero at newly born labels. Ordering the two small
primes before each core identifies the actual tagged basis vectors with the
transformed exterior cones. Their differential is exactly the row `(2,3)`
and the column `(-3,2)` over every commutative coefficient ring.
-/

noncomputable section
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- Adjoining a prime smaller than every face vertex gives the increasing exterior basis vector. -/
theorem primeChainCone_basis_of_lt {k : ℕ} (s : Set.powersetCard Nat.Primes k)
    (p : Nat.Primes) (hp : ∀ q ∈ s.val, p < q) :
    primeChainCone R k p (primeChainBasis R k s) =
      primeChainBasis R (k+1) ⟨insert p s.val,by
        change (insert p s.val).card = k+1
        rw [Finset.card_insert_of_notMem (fun h => (lt_irrefl p) (hp p h)),s.property]⟩ := by
  let v : Fin k ↪o Nat.Primes := Set.powersetCard.ofFinEmbEquiv.symm s
  have hm : StrictMono (Fin.cons p v : Fin (k+1) → Nat.Primes) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (lt_irrefl _ hij)
      | succ j =>
        change p < v j
        exact hp (v j) ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j,rfl⟩)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (Fin.not_lt_zero _ hij)
      | succ j =>
        change v i < v j
        exact v.strictMono (Fin.succ_lt_succ_iff.mp hij)
  rw [primeChainBasis_eq_atom,primeChainBasis_eq_atom,primeChainCone_atom]
  congr 1
  apply Finset.orderEmbOfFin_unique
  · intro i
    cases i using Fin.cases with
    | zero => exact Finset.mem_insert_self _ _
    | succ i =>
      apply Finset.mem_insert_of_mem
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i,rfl⟩
  · exact hm


/-- The transformed vector of a bounded original prime face. -/
def twoPrimeBoundedFaceVector (k N : ℕ) (s : TwoPrimeBoundedFace k N) : PrimeChainSpace R k :=
  primeTwoPrimeBasis R k s.val

theorem twoPrimeBoundedFaceVector_linearIndependent (k N : ℕ) :
    LinearIndependent R (twoPrimeBoundedFaceVector R k N) :=
  (primeTwoPrimeBasis R k).linearIndependent.comp
    (fun s : TwoPrimeBoundedFace k N => s.val) Subtype.val_injective

theorem twoPrimeBoundedFaceVector_span (k N : ℕ) :
    Submodule.span R (Set.range (twoPrimeBoundedFaceVector R k N)) = primeChainCutoff R k N := by
  rw [primeChainCutoff_eq_span_twoPrimeBasis]
  congr 1
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s.val,s.property,rfl⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨⟨s,hs⟩,rfl⟩

/-- A genuine basis of the original cutoff module, with transformed face representatives. -/
def twoPrimeBoundedBasis (k N : ℕ) :
    Module.Basis (TwoPrimeBoundedFace k N) R (primeChainCutoff R k N) :=
  (Module.Basis.span (twoPrimeBoundedFaceVector_linearIndependent R k N)).map
    (LinearEquiv.ofEq _ _ (twoPrimeBoundedFaceVector_span R k N))

theorem twoPrimeBoundedBasis_val (k N : ℕ) (s : TwoPrimeBoundedFace k N) :
    (twoPrimeBoundedBasis R k N s).val = primeTwoPrimeBasis R k s.val := by
  rw [twoPrimeBoundedBasis,Module.Basis.map_apply,Module.Basis.span_apply]
  rfl

/-- Actual cutoff chains split into the core-indexed two-prime block coordinates. -/
def twoPrimeBlockBasis (k N : ℕ) :
    Module.Basis (TwoPrimeBlockIndex k N) R (primeChainCutoff R k N) :=
  (twoPrimeBoundedBasis R k N).reindex (twoPrimeBoundedFaceEquiv k N)

/-- Each block coordinate is the transformed vector of its reconstructed prime face. -/
theorem twoPrimeBlockBasis_val (k N : ℕ) (ct : TwoPrimeBlockIndex k N) :
    (twoPrimeBlockBasis R k N ct).val = primeTwoPrimeBasis R k
      ⟨twoPrimeTaggedFace ct.val.1 ct.val.2,
        (twoPrimeTaggedFace_card ct.val.1 ct.val.2).trans ct.property.1⟩ := by
  rw [twoPrimeBlockBasis,Module.Basis.reindex_apply,twoPrimeBoundedBasis_val]
  rfl

/-- Height extension keeps the identical core and tag. -/
def twoPrimeBlockIndexInclusion (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (ct : TwoPrimeBlockIndex k N) : TwoPrimeBlockIndex k M :=
  ⟨ct.val,ct.property.1,ct.property.2.trans h⟩

/-- The block basis represents literal height inclusion on every generator. -/
theorem twoPrimeBlockBasis_natural (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (ct : TwoPrimeBlockIndex k N) :
    Submodule.inclusion (primeChainCutoff_mono R k h) (twoPrimeBlockBasis R k N ct) =
      twoPrimeBlockBasis R k M (twoPrimeBlockIndexInclusion k h ct) := by
  apply Subtype.ext
  change (twoPrimeBlockBasis R k N ct).val = _
  rw [twoPrimeBlockBasis_val,twoPrimeBlockBasis_val]
  rfl

/-- Finitely supported block coefficients represent every actual cutoff chain uniquely. -/
def twoPrimeBlockCoordinates (k N : ℕ) :
    primeChainCutoff R k N ≃ₗ[R] (TwoPrimeBlockIndex k N →₀ R) :=
  (twoPrimeBlockBasis R k N).repr

/-- Extend block coefficients by zero at the newly born labels. -/
def twoPrimeBlockCoordinateInclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (TwoPrimeBlockIndex k N →₀ R) →ₗ[R] (TwoPrimeBlockIndex k M →₀ R) :=
  Finsupp.linearCombination R (fun ct => Finsupp.single (twoPrimeBlockIndexInclusion k h ct) 1)

/-- The coordinate equivalence is natural for the actual chain persistence maps. -/
theorem twoPrimeBlockCoordinates_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (twoPrimeBlockCoordinates R k M).toLinearMap.comp
      (Submodule.inclusion (primeChainCutoff_mono R k h)) =
    (twoPrimeBlockCoordinateInclusion R k h).comp (twoPrimeBlockCoordinates R k N).toLinearMap := by
  apply (twoPrimeBlockBasis R k N).ext
  intro ct
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,
    twoPrimeBlockCoordinates,Module.Basis.repr_self,twoPrimeBlockCoordinateInclusion,
    Finsupp.linearCombination_single,one_smul]
  rw [twoPrimeBlockBasis_natural R k h ct,Module.Basis.repr_self]

#print axioms primeChainCone_basis_of_lt
#print axioms twoPrimeBlockBasis
#print axioms twoPrimeBlockCoordinates
#print axioms twoPrimeBlockCoordinates_natural

/-- The canonical increasing face of a block core. -/
def twoPrimeCoreBasisFace (c : TwoPrimeCoreFace) : Set.powersetCard Nat.Primes c.val.card :=
  ⟨c.val,rfl⟩

theorem twoPrimeCore_gt_three (c : TwoPrimeCoreFace) (p : Nat.Primes) (hp : p ∈ c.val) :
    3 < p.val := by
  have h2 := p.property.two_le
  have hn2 : p.val ≠ 2 := fun h => c.property.1 (by simpa only [show p = primeTwoLabel from Subtype.ext h] using hp)
  have hn3 : p.val ≠ 3 := fun h => c.property.2 (by simpa only [show p = primeThreeLabel from Subtype.ext h] using hp)
  omega

/-- The actual transformed chain vector for one tag of a block core. -/
def twoPrimeBlockVector (c : TwoPrimeCoreFace) (t : TwoPrimeFaceTag) :
    PrimeChainSpace R (c.val.card + t.degree) :=
  primeTwoPrimeBasis R _ ⟨twoPrimeTaggedFace c t,twoPrimeTaggedFace_card c t⟩

theorem twoPrimeBlockVector_base (c : TwoPrimeCoreFace) :
    twoPrimeBlockVector R c .base =
      primeTwoPrimeAtom R (Set.powersetCard.ofFinEmbEquiv.symm (twoPrimeCoreBasisFace c)) := by
  exact primeTwoPrimeBasis_eq_atom R (twoPrimeCoreBasisFace c)

theorem twoPrimeBlockVector_small (c : TwoPrimeCoreFace) (p : Nat.Primes)
    (hp : p.val = 2 ∨ p.val = 3) :
    primeTwoPrimeGauge R (c.val.card+1)
      (primeChainBasis R (c.val.card+1)
        ⟨insert p c.val,by
          change (insert p c.val).card = c.val.card+1
          rw [Finset.card_insert_of_notMem]
          intro h
          have hg := twoPrimeCore_gt_three c p h
          omega⟩) =
      primeTwoPrimeAtom R (Fin.cons p
        (Set.powersetCard.ofFinEmbEquiv.symm (twoPrimeCoreBasisFace c))) := by
  have hb := primeChainCone_basis_of_lt R (twoPrimeCoreBasisFace c) p (by
    intro q hq
    have hg := twoPrimeCore_gt_three c q hq
    change p.val < q.val
    omega)
  refine (congrArg (primeTwoPrimeGauge R (c.val.card+1)) hb.symm).trans ?_
  rw [primeChainBasis_eq_atom,primeChainCone_atom]
  rfl

/-- The two-tag generator has scalar boundary two times its core. -/
theorem twoPrimeBlockVector_boundary_two (c : TwoPrimeCoreFace) :
    primeValueBoundary R c.val.card (twoPrimeBlockVector R c .two) =
      (2 : R) • twoPrimeBlockVector R c .base := by
  have h := twoPrimeBlockVector_small R c primeTwoLabel (Or.inl rfl)
  change twoPrimeBlockVector R c .two = _ at h
  rw [h,twoPrimeBlockVector_base]
  apply primeTwoPrimeAtom_boundary_cons
  · intro i
    exact twoPrimeCore_gt_three c _
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (twoPrimeCoreBasisFace c) _).mp ⟨i,rfl⟩)
  · exact Or.inl rfl

/-- The three-tag generator has scalar boundary three times its core. -/
theorem twoPrimeBlockVector_boundary_three (c : TwoPrimeCoreFace) :
    primeValueBoundary R c.val.card (twoPrimeBlockVector R c .three) =
      (3 : R) • twoPrimeBlockVector R c .base := by
  have h := twoPrimeBlockVector_small R c primeThreeLabel (Or.inr rfl)
  change twoPrimeBlockVector R c .three = _ at h
  rw [h,twoPrimeBlockVector_base]
  apply primeTwoPrimeAtom_boundary_cons
  · intro i
    exact twoPrimeCore_gt_three c _
      ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (twoPrimeCoreBasisFace c) _).mp ⟨i,rfl⟩)
  · exact Or.inr rfl

/-- The joint-tag basis vector is the ordered two-cone of the three-cone. -/
theorem twoPrimeBlockVector_both (c : TwoPrimeCoreFace) :
    twoPrimeBlockVector R c .both = primeTwoPrimeAtom R
      (Fin.cons primeTwoLabel (Fin.cons primeThreeLabel
        (Set.powersetCard.ofFinEmbEquiv.symm (twoPrimeCoreBasisFace c)))) := by
  let s3 : Set.powersetCard Nat.Primes (c.val.card+1) :=
    ⟨twoPrimeTaggedFace c .three,twoPrimeTaggedFace_card c .three⟩
  have h3 := primeChainCone_basis_of_lt R (twoPrimeCoreBasisFace c) primeThreeLabel (by
    intro q hq
    exact twoPrimeCore_gt_three c q hq)
  have h2 := primeChainCone_basis_of_lt R s3 primeTwoLabel (by
    intro q hq
    change q ∈ insert primeThreeLabel c.val at hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · change (2 : ℕ) < 3
      omega
    · have hg := twoPrimeCore_gt_three c q hq
      change (2 : ℕ) < q.val
      omega)
  refine (congrArg (primeTwoPrimeGauge R (c.val.card+2)) h2.symm).trans ?_
  refine (congrArg (fun x : PrimeChainSpace R (c.val.card+1) =>
    primeTwoPrimeGauge R (c.val.card+2) (primeChainCone R (c.val.card+1) primeTwoLabel x))
      h3.symm).trans ?_
  rw [primeChainBasis_eq_atom,primeChainCone_atom,primeChainCone_atom]
  rfl

/-- The actual tagged top boundary is the column `(-3,2)`. -/
theorem twoPrimeBlockVector_boundary_both (c : TwoPrimeCoreFace) :
    primeValueBoundary R (c.val.card+1) (twoPrimeBlockVector R c .both) =
      Sub.sub (α := PrimeChainSpace R (c.val.card+1))
        ((2 : R) • twoPrimeBlockVector R c .three)
        ((3 : R) • twoPrimeBlockVector R c .two) := by
  have h2 := twoPrimeBlockVector_small R c primeTwoLabel (Or.inl rfl)
  have h3 := twoPrimeBlockVector_small R c primeThreeLabel (Or.inr rfl)
  change twoPrimeBlockVector R c .two = _ at h2
  change twoPrimeBlockVector R c .three = _ at h3
  rw [twoPrimeBlockVector_both,h2,h3]
  apply primeTwoPrimeAtom_topBoundary
  intro i
  exact twoPrimeCore_gt_three c _
    ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (twoPrimeCoreBasisFace c) _).mp ⟨i,rfl⟩)

#print axioms twoPrimeBlockVector_boundary_two
#print axioms twoPrimeBlockVector_boundary_three
#print axioms twoPrimeBlockVector_boundary_both

end GaloisForLFunctions.EffectiveScalingGeometry
