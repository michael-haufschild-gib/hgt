import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedAugmentedHomology
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeSquarefreeIndices

/-!
# The nonsplit free-to-parity extension of weighted persistence

An odd face omitting three has a free generator at its birth height. At twice
that height its parity coefficient is one, while its free quotient has died.
Every lift of the free generator has the same transition, since that label
has no torsion coefficient at birth. Naturality therefore prevents a section
of the free quotient. The empty face gives an unconditional obstruction, and
the actual homology comparison transports it to the original weighted complex.
-/

noncomputable section
open scoped Classical
open CategoryTheory RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder

/-- The free generator belonging to an odd face at its birth height. -/
def primeValueBirthGenerator (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) : primeValueCoordinates k (primeFaceProduct s) :=
  (⟨Finsupp.single s 1,Finsupp.single_mem_supported ℤ 1
    ⟨le_refl _,hs,by have hp := (primeFaceProduct_squarefree s).ne_zero; omega⟩⟩,0)

/-- At double height, the born free generator has parity coefficient one if three is absent. -/
theorem primeValueBirthGenerator_double (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) (h3 : primeThreeLabel ∉ s.val) :
    (primeValueCoordinateMap k (primeFaceProduct s) (2*primeFaceProduct s)
      (primeValueBirthGenerator k s hs)).2.val s = 1 := by
  have ht : s ∈ primeTorsionFaces k (2*primeFaceProduct s) :=
    ⟨hs,h3,le_refl _,by have hp := (primeFaceProduct_squarefree s).ne_zero; omega⟩
  rw [primeValueCoordinateMap_torsion,if_pos ht]
  change ((Finsupp.single s (1 : ℤ)) s : ZMod 2) + 0 = 1
  simp only [Finsupp.single_eq_same,Int.cast_one,add_zero]

/-- A prime-weighted height map genuinely carries a free class into torsion. -/
theorem primeValueCoordinateMap_double_ne_zero (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) (h3 : primeThreeLabel ∉ s.val) :
    primeValueCoordinateMap k (primeFaceProduct s) (2*primeFaceProduct s) ≠ 0 := by
  intro h
  have hz := congrArg (fun z : primeValueCoordinates k (2*primeFaceProduct s) => z.2.val s)
    (LinearMap.congr_fun h (primeValueBirthGenerator k s hs))
  have he := primeValueBirthGenerator_double k s hs h3
  exact one_ne_zero (he.symm.trans hz)

/-- Forgetting parity gives the ordinary free interval quotient. -/
def primeValueFreeProjection (k : ℕ) :
    primeValueCoordinatePersistence k ⟶ primeCriticalPersistence ℤ k where
  app N := ModuleCat.ofHom (LinearMap.fst ℤ _ _)
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The free birth generator has died in the free quotient at double height. -/
theorem primeValueBirthGenerator_free_dies (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) :
    primeCriticalMap ℤ k (primeFaceProduct s) (2*primeFaceProduct s)
      (primeValueBirthGenerator k s hs).1 = 0 := by
  apply Subtype.ext
  ext t
  rw [primeCriticalMap_apply]
  by_cases ht : t ∈ primeCriticalFaces k (2*primeFaceProduct s)
  · rw [if_pos ht]
    have hst : s ≠ t := by
      intro he
      subst t
      exact (lt_irrefl _) ht.2.2
    change (Finsupp.single s (1 : ℤ)) t = 0
    rw [Finsupp.single_apply,if_neg hst]
  · rw [if_neg ht]
    rfl

/-- Every lift of a free birth generator has the same nonzero parity transition. -/
theorem primeValueBirthLift_double (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) (h3 : primeThreeLabel ∉ s.val)
    (x : primeValueCoordinates k (primeFaceProduct s))
    (hx : x.1 = (primeValueBirthGenerator k s hs).1) :
    (primeValueCoordinateMap k (primeFaceProduct s) (2*primeFaceProduct s) x).2.val s = 1 := by
  have hp := (primeFaceProduct_squarefree s).ne_zero
  have ht : s ∈ primeTorsionFaces k (2*primeFaceProduct s) :=
    ⟨hs,h3,le_refl _,by omega⟩
  have hn : s ∉ primeTorsionFaces k (primeFaceProduct s) := by
    intro h
    have hh := h.2.2.1
    omega
  have hz := (Finsupp.mem_supported' ℤ x.2.val).mp x.2.property s hn
  rw [primeValueCoordinateMap_torsion,if_pos ht,hx,hz]
  change ((Finsupp.single s (1 : ℤ)) s : ZMod 2)+0 = 1
  simp only [Finsupp.single_eq_same,Int.cast_one,add_zero]

/-- A free-to-parity block prevents a natural section of the free quotient. -/
theorem primeValueFreeProjection_no_section (k : ℕ) (s : Set.powersetCard Nat.Primes k)
    (hs : primeTwoLabel ∉ s.val) (h3 : primeThreeLabel ∉ s.val) :
    ¬ ∃ τ : primeCriticalPersistence ℤ k ⟶ primeValueCoordinatePersistence k,
      τ ≫ primeValueFreeProjection k = 𝟙 (primeCriticalPersistence ℤ k) := by
  rintro ⟨τ,hτ⟩
  let m := primeFaceProduct s
  let g := (primeValueBirthGenerator k s hs).1
  have hx : (τ.app m g).1 = g := by
    have he := congrArg (fun α : primeCriticalPersistence ℤ k ⟶ primeCriticalPersistence ℤ k => α.app m) hτ
    exact congrArg (fun f : (primeCriticalPersistence ℤ k).obj m ⟶
      (primeCriticalPersistence ℤ k).obj m => f g) he
  have hn := congrArg (fun f : (primeCriticalPersistence ℤ k).obj m ⟶
      (primeValueCoordinatePersistence k).obj (2*m) => f g)
    (τ.naturality (homOfLE (show m ≤ 2*m by omega)))
  change τ.app (2*m) (primeCriticalMap ℤ k m (2*m) g) =
    primeValueCoordinateMap k m (2*m) (τ.app m g) at hn
  rw [primeValueBirthGenerator_free_dies] at hn
  have hn0 : 0 = primeValueCoordinateMap k m (2*m) (τ.app m g) :=
    (τ.app (2*m)).hom.map_zero.symm.trans hn
  have hz := congrArg (fun x : primeValueCoordinates k (2*m) => x.2.val s) hn0.symm
  have he := primeValueBirthLift_double k s hs h3 (τ.app m g) hx
  exact one_ne_zero (he.symm.trans hz)

/-- Even the empty-degree free quotient admits no natural section. -/
theorem primeValueFreeProjection_zero_no_section :
    ¬ ∃ τ : primeCriticalPersistence ℤ 0 ⟶ primeValueCoordinatePersistence 0,
      τ ≫ primeValueFreeProjection 0 = 𝟙 (primeCriticalPersistence ℤ 0) :=
  primeValueFreeProjection_no_section 0 ⟨∅,Finset.card_empty⟩
    (Finset.notMem_empty _) (Finset.notMem_empty _)

/-- The canonical free quotient of actual integral weighted homology. -/
def primeValueActualFreeProjection (k : ℕ) :
    primeCutoffHomology ℤ (primeValueFunctional ℤ) k ⟶ primeCriticalPersistence ℤ k :=
  (primeValueHomologyCoordinateIso k).hom ≫ primeValueFreeProjection k

/-- Actual integral weighted homology does not naturally split into its free quotient and torsion. -/
theorem primeValueActualFreeProjection_zero_no_section :
    ¬ ∃ τ : primeCriticalPersistence ℤ 0 ⟶ primeCutoffHomology ℤ (primeValueFunctional ℤ) 0,
      τ ≫ primeValueActualFreeProjection 0 = 𝟙 (primeCriticalPersistence ℤ 0) := by
  rintro ⟨τ,hτ⟩
  apply primeValueFreeProjection_zero_no_section
  refine ⟨τ ≫ (primeValueHomologyCoordinateIso 0).hom,?_⟩
  simpa only [Category.assoc,primeValueActualFreeProjection] using hτ

#print axioms primeValueCoordinateMap_double_ne_zero
#print axioms primeValueFreeProjection_no_section
#print axioms primeValueActualFreeProjection_zero_no_section
end GaloisForLFunctions.EffectiveScalingGeometry
