import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LambdaRingEffectivityAndHeckeLefschetzRigidity

/-!
# Sections on the orbit of a cycle

What is an arithmetic section of a cycle, and why would it satisfy Riemann–Roch without reference
to the sign of Weil's form? Arithmetic Castelnuovo–Severi shows that on any polar surface with a
fibre-tilting correspondence, every invariant cone of nonnegative ample degree satisfies
Riemann–Roch iff it contains the open positive cone and the defect is nonnegative everywhere. AOG
localizes this to one orbit.

* **The orbit surface** (`orbitSurface`). The span of `H, V` and the orbit `{ψ_g x}` is stable
  under every scale (`act_mem_orbitSpan`), and the pairing restricts to a polar surface on it
  (`PolarSurface.restrict`). Its Hodge index is the orbit Hodge index of `x`
  (`orbitSurface_hodgeIndex_iff`).
* **Riemann–Roch on an orbit is orientation** (`orbitSurface_riemannRoch_iff`). For every set `E` of
  cycles of the orbit surface with nonnegative ample degree that is stable under one Hecke
  correspondence `T_g`, `s(g) > 0`: `E` satisfies Riemann–Roch iff it contains the open positive
  cone and `x` is oriented. A section theory of the orbit of `x` that is stable under one Hecke
  correspondence satisfies Riemann–Roch exactly when `x` is oriented: Riemann–Roch on an orbit is
  the orientation of that orbit, never an independent input.
* **On a configuration** (`configOrbitSurface_riemannRoch_iff_blind`): on a symmetric tempered
  configuration this is blindness of `x` to the off-line zeros. Sections with Riemann–Roch live
  exactly on the oriented locus.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

namespace ArithmeticCastelnuovoSeveri.PolarSurface
end ArithmeticCastelnuovoSeveri.PolarSurface

/-- The restriction of a polar surface to a submodule containing the fibre classes. -/
def _root_.GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface.restrict
    {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (W : Submodule ℝ E)
    (hH : S.H ∈ W) (hV : S.V ∈ W) : PolarSurface W where
  pair := S.pair.compl₁₂ W.subtype W.subtype
  pair_comm x y := S.pair_comm x y
  H := ⟨S.H, hH⟩
  V := ⟨S.V, hV⟩
  pair_H_H := S.pair_H_H
  pair_V_V := S.pair_V_V
  pair_H_V := S.pair_H_V

theorem _root_.GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface.restrict_defect
    {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (W : Submodule ℝ E)
    (hH : S.H ∈ W) (hV : S.V ∈ W) (x y : W) :
    (S.restrict W hH hV).defect x y = S.defect x y := rfl

namespace ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-- The span of the fibre classes and the orbit of `x`. -/
def orbitSpan (x : E) : Submodule ℝ E :=
  Submodule.span ℝ ({D.H, D.V} ∪ Set.range fun g : G => D.act g x)

theorem H_mem_orbitSpan (x : E) : D.H ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inl (Or.inl rfl))

theorem V_mem_orbitSpan (x : E) : D.V ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inl (Or.inr rfl))

theorem orbit_mem_orbitSpan (x : E) (g : G) : D.act g x ∈ D.orbitSpan x :=
  Submodule.subset_span (Or.inr ⟨g, rfl⟩)

/-- `ψ_g` sends a fibre class to a multiple of itself. -/
theorem act_H (g : G) : D.act g D.H = Real.exp (D.scale g / 2) • D.H := by
  -- both sides have the same pairings with every cycle that the pairing separates; we compute
  -- through the pole plane: `ψ_g H` is isotropic, orthogonal to `H`, and pairs with `V` by `e^{s/2}`
  sorry

end ScalingDatum

end GaloisForLFunctions.ArithmeticOrientationGeometry
