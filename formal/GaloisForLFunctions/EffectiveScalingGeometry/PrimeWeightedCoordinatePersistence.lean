import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedParityCoordinates

/-!
# Integral free-to-parity persistence maps

Raising height retains free coefficients until their doubled birth height.
A coefficient then reduces modulo two precisely when its odd face omits
three, and the parity class disappears at triple height. The explicit maps
commute with odd-chain inclusions. Surjectivity of the coordinate projection
transfers the inclusion identities to a persistence functor, retaining the
nonzero transition from free to torsion classes.
-/

noncomputable section
open scoped Classical
open RHTower CategoryTheory
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder

/-- Integral free coefficients together with surviving parity coefficients. -/
abbrev primeValueCoordinates (k N : ℕ) :=
  primeCriticalCoordinates ℤ k N × primeTorsionCoordinates k N

/-- Height transition: retain free coefficients and reduce them into the new torsion window. -/
def primeValueCoordinateMap (k N M : ℕ) :
    primeValueCoordinates k N →ₗ[ℤ] primeValueCoordinates k M :=
  ((primeCriticalMap ℤ k N M).comp (LinearMap.fst ℤ _ _)).prod
    ((Finsupp.restrictDom (ZMod 2) ℤ (primeTorsionFaces k M)).comp
      (((Finsupp.mapRange.linearMap (Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap).comp
        ((Finsupp.supported ℤ ℤ (primeCriticalFaces k N)).subtype.comp (LinearMap.fst ℤ _ _)) +
        (Finsupp.supported (ZMod 2) ℤ (primeTorsionFaces k N)).subtype.comp (LinearMap.snd ℤ _ _))))

theorem primeValueCoordinateMap_free (k N M : ℕ) (x : primeValueCoordinates k N) :
    (primeValueCoordinateMap k N M x).1 = primeCriticalMap ℤ k N M x.1 := rfl

theorem primeValueCoordinateMap_torsion (k N M : ℕ) (x : primeValueCoordinates k N)
    (s : Set.powersetCard Nat.Primes k) :
    (primeValueCoordinateMap k N M x).2.val s =
      if s ∈ primeTorsionFaces k M then (x.1.val s : ZMod 2) + x.2.val s else 0 :=
  Finsupp.filter_apply _ _ _

/-- A born face alive in the target torsion window was previously free or torsion, exclusively. -/
theorem primeValueCoordinateMap_projection_torsion (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (x : primeOddCutoff ℤ k N) (s : Set.powersetCard Nat.Primes k) :
    (primeValueCoordinateMap k N M (primeValueHomologyProjection k N x)).2.val s =
      (primeParityProjection k M x.val).val s := by
  rw [primeValueCoordinateMap_torsion,primeParityProjection_apply]
  have hf : (primeCriticalProjection ℤ k N x).val s =
      if s ∈ primeCriticalFaces k N then (primeChainBasis ℤ k).repr x.val s else 0 :=
    Finsupp.filter_apply _ _ _
  change (if s ∈ primeTorsionFaces k M then
      ((primeCriticalProjection ℤ k N x).val s : ZMod 2) +
        (primeParityProjection k N x.val).val s else 0) = _
  rw [hf,primeParityProjection_apply]
  by_cases hm : s ∈ primeTorsionFaces k M
  · rw [if_pos hm,if_pos hm]
    by_cases hz : (primeChainBasis ℤ k).repr x.val s = 0
    · simp only [hz,ite_self,Int.cast_zero,add_zero]
    · have hb := (primeOddCutoff_iff_repr_support ℤ k N x.val).mp x.property
        (Finsupp.mem_support_iff.mpr hz)
      by_cases hn : N < 2 * primeFaceProduct s
      · have hc : s ∈ primeCriticalFaces k N := ⟨hb.1,hb.2,hn⟩
        have ht : s ∉ primeTorsionFaces k N := fun ht => (not_le_of_gt hn) ht.2.2.1
        rw [if_pos hc,if_neg ht,add_zero]
      · have ht : s ∈ primeTorsionFaces k N :=
          ⟨hm.1,hm.2.1,by omega,lt_of_le_of_lt h hm.2.2.2⟩
        have hc : s ∉ primeCriticalFaces k N := fun hc => hn hc.2.2
        rw [if_neg hc,Int.cast_zero,if_pos ht,zero_add]
  · rw [if_neg hm,if_neg hm]

/-- The explicit free-to-parity transition commutes with actual odd-chain inclusions. -/
theorem primeValueHomologyProjection_natural (k : ℕ) {N M : ℕ} (h : N ≤ M) :
    (primeValueCoordinateMap k N M).comp (primeValueHomologyProjection k N) =
      (primeValueHomologyProjection k M).comp
        (Submodule.inclusion (primeOddCutoff_mono ℤ k h)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact LinearMap.congr_fun (primeCriticalProjection_natural ℤ k h) x
  · apply Subtype.ext
    ext s
    exact primeValueCoordinateMap_projection_torsion k h x s

theorem primeValueCoordinateMap_refl (k N : ℕ) :
    primeValueCoordinateMap k N N = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := primeValueHomologyProjection_surjective k N x
  exact LinearMap.congr_fun (primeValueHomologyProjection_natural k (le_refl N)) y

theorem primeValueCoordinateMap_comp (k : ℕ) {N M L : ℕ} (h : N ≤ M) (g : M ≤ L) :
    (primeValueCoordinateMap k M L).comp (primeValueCoordinateMap k N M) =
      primeValueCoordinateMap k N L := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := primeValueHomologyProjection_surjective k N x
  have h₁ := LinearMap.congr_fun (primeValueHomologyProjection_natural k h) y
  have h₂ := LinearMap.congr_fun (primeValueHomologyProjection_natural k g)
    (Submodule.inclusion (primeOddCutoff_mono ℤ k h) y)
  have h₃ := LinearMap.congr_fun (primeValueHomologyProjection_natural k (h.trans g)) y
  simp only [LinearMap.comp_apply] at h₁ h₂ h₃
  change primeValueCoordinateMap k M L (primeValueCoordinateMap k N M
    (primeValueHomologyProjection k N y)) = _
  rw [h₁,h₂,h₃]
  rfl

/-- Full integral coordinate persistence, including reduction from free to torsion classes. -/
def primeValueCoordinatePersistence (k : ℕ) : ℕ ⥤ ModuleCat ℤ where
  obj N := ModuleCat.of ℤ (primeValueCoordinates k N)
  map {N M} _ := ModuleCat.ofHom (primeValueCoordinateMap k N M)
  map_id N := ModuleCat.hom_ext (primeValueCoordinateMap_refl k N)
  map_comp h g := ModuleCat.hom_ext (primeValueCoordinateMap_comp k h.le g.le).symm

#print axioms primeValueHomologyProjection_natural
#print axioms primeValueCoordinatePersistence
end GaloisForLFunctions.EffectiveScalingGeometry
