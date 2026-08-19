import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilators and localization

For a finite module, the annihilator of a localized module is the extension of the annihilator:

```text
annihilator_le_map_annihilator_of_isLocalizedModule
    Ann_B (localized module)  ≤  (Ann_S M) · B
```

The reverse containment is immediate, so the two ideals agree.  Clearing a denominator reduces the
statement to an element of the base, and the finitely many generators each contribute one element
of the multiplicative set; their product pushes the witness back into the base.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The annihilator of a localized module is the extension of the annihilator**, for a finite
module.  A denominator can be cleared, and the finitely many generators supply a single element of
the multiplicative set that pushes the witness back into the base. -/
theorem annihilator_le_map_annihilator_of_isLocalizedModule
    {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (T : Submonoid S) (B : Type*) [CommRing B] [Algebra S B] [IsLocalization T B]
    {N : Type*} [AddCommGroup N] [Module S N] [Module B N] [IsScalarTower S B N]
    (f : M →ₗ[S] N) [IsLocalizedModule T f] :
    Module.annihilator B N ≤ (Module.annihilator S M).map (algebraMap S B) := by
  classical
  intro y hy
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj T y
  have hs : algebraMap S B s ∈ Module.annihilator B N := by
    rw [← hst]; exact Ideal.mul_mem_right _ _ hy
  obtain ⟨k, G, hG⟩ := Module.Finite.exists_fin (R := S) (M := M)
  have hzero : ∀ i : Fin k, f (s • G i) = 0 := by
    intro i
    rw [map_smul, ← IsScalarTower.algebraMap_smul B s (f (G i))]
    exact (Module.mem_annihilator.mp hs) (f (G i))
  choose ts hts using fun i : Fin k => (IsLocalizedModule.eq_zero_iff T f).mp (hzero i)
  set t' : T := ∏ i : Fin k, ts i with ht'
  have hts' : ∀ i : Fin k, ((ts i : S) * s) • G i = 0 := by
    intro i
    rw [mul_smul]
    exact hts i
  have hkill : ∀ i : Fin k, ((t' : S) * s) • G i = 0 := by
    intro i
    have hsplit : (t' : S) * s
        = (∏ j ∈ Finset.univ.erase i, (ts j : S)) * ((ts i : S) * s) := by
      rw [ht', Submonoid.coe_finsetProd,
        ← Finset.prod_erase_mul Finset.univ (fun j : Fin k => (ts j : S)) (Finset.mem_univ i)]
      ring
    rw [hsplit, mul_smul, hts' i, smul_zero]
  have hann : (t' : S) * s ∈ Module.annihilator S M := by
    rw [Module.mem_annihilator]
    intro x
    have hx : x ∈ Submodule.span S (Set.range G) := by rw [hG]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact hkill i
    · exact smul_zero _
    · intro u v _ _ hu hv; rw [smul_add, hu, hv, add_zero]
    · intro a u _ hu; rw [smul_comm, hu, smul_zero]
  have hunit : IsUnit (algebraMap S B ((t : S) * (t' : S))) :=
    IsLocalization.map_units (M := T) B (t * t')
  obtain ⟨w, hw⟩ := hunit.exists_left_inv
  have hkey : y * algebraMap S B ((t : S) * (t' : S))
      = algebraMap S B ((t' : S) * s) := by
    rw [map_mul, ← mul_assoc, hst, ← map_mul]
    congr 1
    ring
  have hmem : y * algebraMap S B ((t : S) * (t' : S))
      ∈ (Module.annihilator S M).map (algebraMap S B) := by
    rw [hkey]; exact Ideal.mem_map_of_mem _ hann
  have hin := Ideal.mul_mem_left ((Module.annihilator S M).map (algebraMap S B)) w hmem
  have heq : w * (y * algebraMap S B ((t : S) * (t' : S))) = y := by
    rw [mul_comm y _, ← mul_assoc, hw, one_mul]
  rwa [heq] at hin

end GaloisForLFunctions.HTGeometry
