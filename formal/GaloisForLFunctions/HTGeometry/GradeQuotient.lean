import GaloisForLFunctions.HTGeometry.IdealGrade
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.RingTheory.Regular.Category

/-!
# Grade drops by at most one modulo a regular element

```text
subsingleton_ext_smulShortComplex_X₃   ** the middle of the long exact sequence vanishes when both
                                          neighbours do **
hasGradeGE_quotSMulTop                 ** so an `M`-regular sequence of length `n+1` in `I` gives
                                          one of length `n` on `M ⧸ xM` **
```

The short complex `0 → M →ˣ M → M ⧸ xM → 0` is exact for an `M`-regular `x`, so the covariant long
exact sequence of `Ext (N, -)` reads

```text
Ext^i (N, M) → Ext^i (N, M ⧸ xM) → Ext^{i+1} (N, M).
```

With the two ends vanishing the middle vanishes, which is exactly the Rees criterion for the
quotient one degree lower.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Abelian Pointwise RingTheory.Sequence

universe v u

variable {R : Type u} [CommRing R]

/-- **The middle of the long exact sequence vanishes when both neighbours do.** -/
theorem subsingleton_ext_smulShortComplex_X₃ [Small.{v} R] (M : ModuleCat.{v} R) {x : R}
    (hx : IsSMulRegular M x) (N : ModuleCat.{v} R) (i : ℕ)
    (h0 : Subsingleton (Ext N M i)) (h1 : Subsingleton (Ext N M (i + 1))) :
    Subsingleton (Ext N (ModuleCat.smulShortComplex M x).X₃ i) := by
  have key : ∀ z : Ext N (ModuleCat.smulShortComplex M x).X₃ i, z = 0 := by
    intro z
    have hz : z.comp hx.smulShortComplex_shortExact.extClass rfl = 0 := h1.elim _ _
    obtain ⟨y, hy⟩ :=
      Ext.covariant_sequence_exact₃ N hx.smulShortComplex_shortExact z rfl hz
    have h0' : Subsingleton (Ext N (ModuleCat.smulShortComplex M x).X₂ i) := h0
    rw [← hy, h0'.elim y 0]
    simp
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **Grade drops by at most one modulo a regular element.** -/
theorem hasGradeGE_quotSMulTop [IsNoetherianRing R] {I : Ideal R} (M : ModuleCat.{u} R)
    [Module.Finite R M] {x : R} (hx : IsSMulRegular M x) {n : ℕ}
    (hI : I • (⊤ : Submodule R M) < ⊤)
    (hIq : I • (⊤ : Submodule R ((ModuleCat.smulShortComplex M x).X₃)) < ⊤)
    (h : HasGradeGE I M (n + 1)) :
    HasGradeGE I ((ModuleCat.smulShortComplex M x).X₃) n := by
  haveI : Module.Finite R ((ModuleCat.smulShortComplex M x).X₃) :=
    Module.Finite.of_surjective (Submodule.mkQ (x • (⊤ : Submodule R M)))
      (Submodule.mkQ_surjective _)
  have tM := ModuleCat.exists_isRegular_tfae I (n + 1) M hI
  have tQ := ModuleCat.exists_isRegular_tfae I n ((ModuleCat.smulShortComplex M x).X₃) hIq
  have h1 := (tM.out 3 0).mp h
  refine (tQ.out 0 3).mp ?_
  intro N hN1 hN2 hsupp i hi
  exact subsingleton_ext_smulShortComplex_X₃ M hx N i
    (h1 N hN1 hN2 hsupp i (by omega)) (h1 N hN1 hN2 hsupp (i + 1) (by omega))

end GaloisForLFunctions.HTGeometry
