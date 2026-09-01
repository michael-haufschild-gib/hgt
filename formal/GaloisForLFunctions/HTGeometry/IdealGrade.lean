import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.Height

/-!
# Grade, and its dependence on the radical only

```text
HasGradeGE                  an `M`-regular sequence of a given length inside an ideal
hasGradeGE_of_radical_eq    ** grade depends on the ideal only through its radical **
```

Rees's theorem characterises the existence of an `M`-regular sequence of length `n` inside `I` by
the vanishing of `Ext^i (N, M)` for `i < n` and every finite nontrivial `N` supported inside the
zero locus of `I`.  That condition mentions `I` only through `PrimeSpectrum.zeroLocus I`, which is
the same for two ideals with the same radical — so the two conditions are literally the same
statement and the transfer is immediate.

This is what lets a system of parameters be replaced by any other ideal with the same radical: the
maximal ideal of a local ring and any ideal it is minimal over have the same grade.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

universe u v

variable {R : Type u} [CommRing R]

/-- An `M`-regular sequence of length `n` inside `I`. -/
def HasGradeGE (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs

theorem hasGradeGE_zero (I : Ideal R) (M : ModuleCat.{v} R)
    (h : I • (⊤ : Submodule R M) < ⊤) : HasGradeGE I M 0 := by
  refine ⟨[], rfl, by simp, ⟨⟨fun i hi => absurd hi (by simp)⟩, ?_⟩⟩
  intro htop
  rw [show (Ideal.ofList ([] : List R)) = ⊥ by simp [Ideal.ofList], Submodule.bot_smul] at htop
  have hbot : (⊤ : Submodule R M) ≤ I • ⊤ := by rw [htop]; exact bot_le
  exact absurd (le_antisymm h.le hbot) h.ne

/-- **Grade depends on the ideal only through its radical.** -/
theorem hasGradeGE_of_radical_eq [IsNoetherianRing R] {I J : Ideal R}
    (hIJ : I.radical = J.radical) (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) < ⊤) (hJ : J • (⊤ : Submodule R M) < ⊤)
    (h : HasGradeGE I M n) : HasGradeGE J M n := by
  have tI := ModuleCat.exists_isRegular_tfae I n M hI
  have tJ := ModuleCat.exists_isRegular_tfae J n M hJ
  have h1 := (tI.out 3 0).mp h
  have hz : PrimeSpectrum.zeroLocus (J : Set R) = PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical, ← PrimeSpectrum.zeroLocus_radical (I := I), hIJ]
  refine (tJ.out 0 3).mp ?_
  intro N hN1 hN2 hsupp i hi
  exact h1 N hN1 hN2 (by rwa [hz] at hsupp) i hi

end GaloisForLFunctions.HTGeometry
