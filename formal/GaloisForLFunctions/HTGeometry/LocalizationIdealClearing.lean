import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Clearing a finite ideal inclusion from a localization

An inclusion of localized ideals can be cleared by one denominator when the source ideal is
finitely generated.  This is the algebraic step which turns equality at a local ring into equality
on one principal open neighborhood.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- If the image of a finitely generated ideal `I` is contained in the image of `J` after
localization, one denominator sends every element of `I` into `J`. -/
theorem exists_denominator_mul_le_of_localized_ideal_le
    {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (I J : Ideal R) (hIfg : I.FG)
    (hmap : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ s : M, ∀ x ∈ I, (s : R) * x ∈ J := by
  classical
  obtain ⟨G, hGfin, hGspan⟩ := Submodule.fg_def.mp hIfg
  letI : Fintype G := hGfin.fintype
  have hden : ∀ g : G, ∃ s : M, (s : R) * g.1 ∈ J := by
    intro g
    have hgI : g.1 ∈ I := by
      rw [← hGspan]
      exact Submodule.subset_span g.2
    have hgmap : algebraMap R S g.1 ∈ J.map (algebraMap R S) :=
      hmap (Ideal.mem_map_of_mem (algebraMap R S) hgI)
    obtain ⟨s, hsM, hsJ⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J g.1).mp hgmap
    exact ⟨⟨s, hsM⟩, hsJ⟩
  choose den hdenJ using hden
  let s : M := ∏ g : G, den g
  refine ⟨s, ?_⟩
  intro x hx
  rw [← hGspan] at hx
  refine Submodule.span_induction
    (p := fun y _ ↦ (s : R) * y ∈ J) ?_ ?_ ?_ ?_ hx
  · intro g hg
    let g' : G := ⟨g, hg⟩
    have hdvd : (den g' : R) ∣ (s : R) := by
      simpa [s] using
        (Finset.dvd_prod_of_mem (fun i : G ↦ (den i : R))
          (Finset.mem_univ g'))
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_assoc]
    convert J.mul_mem_left c (hdenJ g') using 1
    ring
  ·
    rw [mul_zero]
    exact J.zero_mem
  · intro y z _ _ hy hz
    simpa [mul_add] using J.add_mem hy hz
  · intro r y _ hy
    simpa [mul_assoc, mul_comm r] using J.mul_mem_left r hy

end

end GaloisForLFunctions.HTGeometry
