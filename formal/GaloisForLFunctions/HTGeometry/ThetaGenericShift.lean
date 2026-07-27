import GaloisForLFunctions.HTGeometry.JacobiThetaDifferentialOrbitObstruction

/-!
# Generic shifts for the rank-three resonance conditions

The resonance conditions of the rank-three period group exclude only a countable set of shifts, so
a shift avoiding any prescribed finite family of resonance conditions always exists.  This is the
combinatorial input of the free-block replication argument, which needs a fresh shift separated
from a given finite family.

* `thetaResonanceSet` — the enlarged lattice `Z + Z tau + Z q`, and its countability;
* **`exists_thetaGenericShift`** — a shift `w` with `w + s` nonresonant for every element `s` of a
  prescribed finite set of offsets.
-/

open Set

namespace GaloisForLFunctions

noncomputable section

instance complexUncountable : Uncountable ℂ :=
  Complex.ofReal_injective.uncountable

/-- The enlarged lattice `Z + Z tau + Z q` of resonant shifts. -/
def thetaResonanceSet (τ q : ℂ) : Set ℂ :=
  {x : ℂ | ∃ a b n : ℤ, x = a + b * τ + n * q}

theorem thetaTranslationNonresonant_iff_notMem (τ q h : ℂ) :
    ThetaTranslationNonresonant τ q h ↔ h ∉ thetaResonanceSet τ q := Iff.rfl

theorem thetaResonanceSet_countable (τ q : ℂ) : (thetaResonanceSet τ q).Countable := by
  have hrange : thetaResonanceSet τ q =
      Set.range fun p : ℤ × ℤ × ℤ => (p.1 : ℂ) + (p.2.1 : ℂ) * τ + (p.2.2 : ℂ) * q := by
    ext x
    constructor
    · rintro ⟨a, b, n, rfl⟩
      exact ⟨(a, b, n), rfl⟩
    · rintro ⟨⟨a, b, n⟩, rfl⟩
      exact ⟨a, b, n, rfl⟩
  rw [hrange]
  exact Set.countable_range _

/-- **A generic shift exists.**  For any finite set of offsets there is a shift whose translate by
every offset is nonresonant. -/
theorem exists_thetaGenericShift (τ q : ℂ) (S : Finset ℂ) :
    ∃ w : ℂ, ∀ s ∈ S, ThetaTranslationNonresonant τ q (w + s) := by
  classical
  set bad : Set ℂ := ⋃ s ∈ (S : Set ℂ), (fun x : ℂ => x - s) '' thetaResonanceSet τ q with hbaddef
  have hbad : bad.Countable := by
    rw [hbaddef]
    exact Set.Countable.biUnion S.countable_toSet
      fun s _ => (thetaResonanceSet_countable τ q).image _
  have hex : ∃ w : ℂ, w ∉ bad := by
    by_contra hcon
    push Not at hcon
    have huniv : bad = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv] at hbad
    exact Set.not_countable_univ hbad
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, fun s hs hres => hw ?_⟩
  rw [hbaddef]
  refine Set.mem_biUnion (show s ∈ (S : Set ℂ) from hs) ?_
  exact ⟨w + s, hres, by ring⟩

end

end GaloisForLFunctions
