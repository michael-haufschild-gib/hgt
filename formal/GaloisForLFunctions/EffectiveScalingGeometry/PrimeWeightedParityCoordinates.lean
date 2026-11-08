import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedBoundaryCoordinates
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeCriticalCoordinates
import Mathlib.Data.ZMod.Basic

/-!
# Free and parity coordinates of integral prime-weighted relations

The arithmetic boundary lattice consists precisely of odd half-height chains
whose coefficients are even on faces omitting three in the window
`2m ≤ N < 3m`. Joint projection onto free faces `m ≤ N < 2m` and these parity
faces is surjective and has exactly that lattice as kernel. Surjectivity lifts
finitely supported parity coefficients to integers and separates the two
support windows. The statement includes every exterior degree.
-/

noncomputable section
open scoped Classical
open RHTower
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
local instance primeParityIntegerChainModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- Odd faces without three whose double, but not triple, lies below the cutoff. -/
def primeTorsionFaces (k N : ℕ) : Set (Set.powersetCard Nat.Primes k) :=
  {s | primeTwoLabel ∉ s.val ∧ primeThreeLabel ∉ s.val ∧
    2 * primeFaceProduct s ≤ N ∧ N < 3 * primeFaceProduct s}

/-- Parity coefficients on the arithmetic torsion window. -/
abbrev primeTorsionCoordinates (k N : ℕ) :=
  Finsupp.supported (ZMod 2) ℤ (primeTorsionFaces k N)

/-- Reduce exterior coefficients modulo two and retain the torsion window. -/
def primeParityProjection (k N : ℕ) :
    PrimeChainSpace ℤ k →ₗ[ℤ] primeTorsionCoordinates k N :=
  (Finsupp.restrictDom (ZMod 2) ℤ (primeTorsionFaces k N)).comp
    ((Finsupp.mapRange.linearMap ((Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap)).comp
      (primeChainBasis ℤ k).repr.toLinearMap)

theorem primeParityProjection_eq_zero_iff (k N : ℕ) (x : PrimeChainSpace ℤ k) :
    primeParityProjection k N x = 0 ↔
      ∀ s ∈ primeTorsionFaces k N, ((primeChainBasis ℤ k).repr x s : ZMod 2) = 0 := by
  change ((Finsupp.restrictDom (ZMod 2) ℤ (primeTorsionFaces k N))
    (Finsupp.mapRange.linearMap ((Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap) ((primeChainBasis ℤ k).repr x))) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact Finsupp.filter_eq_zero_iff _ _

/-- A basis face outside the torsion window contributes no parity coordinate. -/
theorem primeParityProjection_basis_of_absent (k N : ℕ)
    (s : Set.powersetCard Nat.Primes k) (hs : s ∉ primeTorsionFaces k N) :
    primeParityProjection k N (primeChainBasis ℤ k s) = 0 := by
  apply (primeParityProjection_eq_zero_iff k N _).mpr
  intro t ht
  have hts : t ≠ s := fun h => hs (h ▸ ht)
  simp only [Module.Basis.repr_self,Finsupp.single_apply,if_neg (Ne.symm hts),Int.cast_zero]

/-- Doubling an integral chain kills every parity coordinate. -/
theorem primeParityProjection_double (k N : ℕ) (x : PrimeChainSpace ℤ k) :
    primeParityProjection k N (x+x) = 0 := by
  apply (primeParityProjection_eq_zero_iff k N _).mpr
  intro s _
  rw [map_add,Finsupp.add_apply,Int.cast_add]
  simpa only [Int.cast_add] using
    (ZMod.intCast_eq_zero_iff_even.mpr ⟨(primeChainBasis ℤ k).repr x s,rfl⟩)

/-- Every coordinate boundary is supported at half the original height. -/
theorem primeValueCoordinateLattice_le_half (k N : ℕ) :
    primeValueCoordinateLattice k N ≤ primeOddCutoff ℤ k (N/2) := by
  apply sup_le
  · apply sup_le
    · exact primeOddCutoff_mono ℤ k (by omega)
    · rintro x ⟨y,hy,rfl⟩
      exact Submodule.add_mem _ hy hy
  · exact inf_le_left

/-- The coordinate boundary lattice has zero torsion-window parity. -/
theorem primeValueCoordinateLattice_le_parityKer (k N : ℕ) :
    primeValueCoordinateLattice k N ≤ (primeParityProjection k N).ker := by
  apply sup_le
  · apply sup_le
    · rw [primeOddCutoff_eq_span_basis]
      apply Submodule.span_le.mpr
      rintro x ⟨s,hs,rfl⟩
      apply primeParityProjection_basis_of_absent
      intro ht
      have hl := hs.1
      have hu := ht.2.2.2
      omega
    · rintro x ⟨y,_,rfl⟩
      exact primeParityProjection_double k N y
  · rw [primeOddConeKernel_eq_span_basis]
    apply Submodule.span_le.mpr
    rintro x ⟨s,hs,rfl⟩
    exact primeParityProjection_basis_of_absent k N s (fun ht => ht.2.1 hs.2.2)

/-- Half-height chains with even surviving coefficients are precisely boundaries. -/
theorem primeValueCoordinateLattice_of_half_parity (k N : ℕ)
    (x : PrimeChainSpace ℤ k) (hx : x ∈ primeOddCutoff ℤ k (N/2))
    (hz : primeParityProjection k N x = 0) : x ∈ primeValueCoordinateLattice k N := by
  have hh := (primeOddCutoff_iff_repr_support ℤ k (N/2) x).mp hx
  have hp := (primeParityProjection_eq_zero_iff k N x).mp hz
  rw [← (primeChainBasis ℤ k).linearCombination_repr x,
    Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro s hs
  have hsb : primeChainBasis ℤ k s ∈ primeOddCutoff ℤ k (N/2) :=
    ⟨primeChainBasis_mem_cutoff ℤ s (hh hs).1,
      ⟨_,oddChainProjection_basis_of_odd ℤ s (hh hs).2⟩⟩
  by_cases hl : primeFaceProduct s ≤ N/3
  · apply primeValueCoordinateLattice_low k N
    apply Submodule.smul_mem
    exact ⟨primeChainBasis_mem_cutoff ℤ s hl,
      ⟨_,oddChainProjection_basis_of_odd ℤ s (hh hs).2⟩⟩
  · by_cases h3 : primeThreeLabel ∈ s.val
    · apply primeValueCoordinateLattice_three k N
      apply Submodule.smul_mem
      exact ⟨hsb,primeChainCone_basis_of_present ℤ primeThreeLabel s h3⟩
    · have ht : s ∈ primeTorsionFaces k N :=
        ⟨(hh hs).2,h3,by have hm := (hh hs).1; omega,by omega⟩
      obtain ⟨a,ha⟩ := ZMod.intCast_eq_zero_iff_even.mp (hp s ht)
      rw [ha,add_smul]
      exact primeValueCoordinateLattice_double k N (Submodule.smul_mem _ a hsb)

/-- Exact integral boundary criterion: half-height support and even torsion coordinates. -/
theorem primeValueCoordinateLattice_iff (k N : ℕ) (x : PrimeChainSpace ℤ k) :
    x ∈ primeValueCoordinateLattice k N ↔
      x ∈ primeOddCutoff ℤ k (N/2) ∧ primeParityProjection k N x = 0 := by
  constructor
  · intro h
    exact ⟨primeValueCoordinateLattice_le_half k N h,primeValueCoordinateLattice_le_parityKer k N h⟩
  · rintro ⟨h,hz⟩
    exact primeValueCoordinateLattice_of_half_parity k N x h hz

/-- Joint free and parity coordinates of the integral quotient. -/
def primeValueHomologyProjection (k N : ℕ) :
    primeOddCutoff ℤ k N →ₗ[ℤ]
      (primeCriticalCoordinates ℤ k N × primeTorsionCoordinates k N) :=
  (primeCriticalProjection ℤ k N).prod
    ((primeParityProjection k N).comp (primeOddCutoff ℤ k N).subtype)

/-- The joint coordinate map kills exactly the actual coordinate boundary lattice. -/
theorem primeValueHomologyProjection_eq_zero_iff (k N : ℕ) (x : primeOddCutoff ℤ k N) :
    primeValueHomologyProjection k N x = 0 ↔ x.val ∈ primeValueCoordinateLattice k N := by
  change (primeCriticalProjection ℤ k N x,primeParityProjection k N x.val) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  have hf : primeCriticalProjection ℤ k N x = 0 ↔ x.val ∈ primeOddCutoff ℤ k (N/2) := by
    change x ∈ (primeCriticalProjection ℤ k N).ker ↔ _
    rw [primeCriticalProjection_ker]
    rfl
  rw [hf,primeValueCoordinateLattice_iff]

theorem primeParityProjection_apply (k N : ℕ) (x : PrimeChainSpace ℤ k)
    (s : Set.powersetCard Nat.Primes k) :
    (primeParityProjection k N x).val s =
      if s ∈ primeTorsionFaces k N then ((primeChainBasis ℤ k).repr x s : ZMod 2) else 0 :=
  Finsupp.filter_apply _ _ _

/-- Free representatives have disjoint support from the torsion window. -/
theorem primeParityProjection_freeLift (k N : ℕ) (f : primeCriticalCoordinates ℤ k N) :
    primeParityProjection k N (primeCriticalLift ℤ k N f).val = 0 := by
  apply (primeParityProjection_eq_zero_iff k N _).mpr
  intro s hs
  change (((primeChainBasis ℤ k).repr ((primeChainBasis ℤ k).repr.symm f.val)) s : ZMod 2) = 0
  rw [LinearEquiv.apply_symm_apply]
  have hn : s ∉ primeCriticalFaces k N := by
    intro hc
    have hl := hs.2.2.1
    have hu := hc.2.2
    omega
  rw [(Finsupp.mem_supported' ℤ f.val).mp f.property s hn,Int.cast_zero]

/-- Every finitely supported parity vector has an integral lift with the same allowed support. -/
theorem primeTorsionCoordinates_integralLift (k N : ℕ) (t : primeTorsionCoordinates k N) :
    ∃ f : Finsupp.supported ℤ ℤ (primeTorsionFaces k N),
      ∀ s, (f.val s : ZMod 2) = t.val s := by
  obtain ⟨f,hf⟩ := (Finsupp.mapRange_surjective
    ((Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap)
    (map_zero _) ZMod.intCast_surjective) t.val
  refine ⟨Finsupp.restrictDom ℤ ℤ (primeTorsionFaces k N) f,?_⟩
  intro s
  change ((f.filter (· ∈ primeTorsionFaces k N)) s : ZMod 2) = t.val s
  by_cases hs : s ∈ primeTorsionFaces k N
  · rw [Finsupp.filter_apply_pos _ _ hs]
    exact congrArg (fun g => g s) hf
  · rw [Finsupp.filter_apply_neg _ _ hs,Int.cast_zero]
    exact ((Finsupp.mem_supported' ℤ t.val).mp t.property s hs).symm

/-- An integral vector on the torsion window represents an odd half-height chain. -/
theorem primeTorsionCoordinates_halfLift (k N : ℕ)
    (f : Finsupp.supported ℤ ℤ (primeTorsionFaces k N)) :
    (primeChainBasis ℤ k).repr.symm f.val ∈ primeOddCutoff ℤ k (N/2) := by
  rw [primeOddCutoff_iff_repr_support,LinearEquiv.apply_symm_apply]
  intro s hs
  have h := f.property hs
  exact ⟨by have hm := h.2.2.1; omega,h.1⟩

/-- Every parity vector is represented by a chain with zero free coordinates. -/
theorem primeValueHomologyProjection_torsion_surjective (k N : ℕ)
    (t : primeTorsionCoordinates k N) :
    ∃ x : primeOddCutoff ℤ k N, primeValueHomologyProjection k N x = (0,t) := by
  obtain ⟨f,hf⟩ := primeTorsionCoordinates_integralLift k N t
  have hh := primeTorsionCoordinates_halfLift k N f
  let x : primeOddCutoff ℤ k N :=
    ⟨(primeChainBasis ℤ k).repr.symm f.val,primeOddCutoff_mono ℤ k (by omega) hh⟩
  refine ⟨x,Prod.ext ?_ ?_⟩
  · change primeCriticalProjection ℤ k N x = 0
    change x ∈ (primeCriticalProjection ℤ k N).ker
    rw [primeCriticalProjection_ker]
    exact hh
  · apply Subtype.ext
    ext s
    change (primeParityProjection k N x.val).val s = t.val s
    rw [primeParityProjection_apply]
    by_cases hs : s ∈ primeTorsionFaces k N
    · rw [if_pos hs]
      change (((primeChainBasis ℤ k).repr ((primeChainBasis ℤ k).repr.symm f.val)) s : ZMod 2) = _
      rw [LinearEquiv.apply_symm_apply]
      exact hf s
    · rw [if_neg hs]
      exact ((Finsupp.mem_supported' ℤ t.val).mp t.property s hs).symm

/-- Free and parity coordinates can be prescribed independently at any fixed height. -/
theorem primeValueHomologyProjection_surjective (k N : ℕ) :
    Function.Surjective (primeValueHomologyProjection k N) := by
  rintro ⟨f,t⟩
  obtain ⟨x,hx⟩ := primeValueHomologyProjection_torsion_surjective k N t
  refine ⟨primeCriticalLift ℤ k N f+x,?_⟩
  rw [map_add,hx]
  have hfree : primeValueHomologyProjection k N (primeCriticalLift ℤ k N f) = (f,0) :=
    Prod.ext (LinearMap.congr_fun (primeCriticalProjection_lift ℤ k N) f)
      (primeParityProjection_freeLift k N f)
  rw [hfree]
  exact Prod.ext (add_zero f) (zero_add t)

#print axioms primeValueCoordinateLattice_iff
#print axioms primeValueHomologyProjection_eq_zero_iff
#print axioms primeValueHomologyProjection_surjective
end GaloisForLFunctions.EffectiveScalingGeometry
