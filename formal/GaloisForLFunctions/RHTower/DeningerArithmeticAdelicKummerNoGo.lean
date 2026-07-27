import Mathlib.Topology.Algebra.Module.Basic

/-!
# Adelic Kummer Hilbert-completion no-go

Two unconditional abstract consequences used by the source-native
Deninger program:

* a continuous map into a Hausdorff space that vanishes on a dense
  Kummer subspace vanishes everywhere;
* a square-root Tate action scales any bilinear pairing by its degree,
  and its centered action is the identity.

Allcock--Vaaler's arithmetic theorem supplies the dense Kummer subspace
when this abstract result is specialized to their adelic `L²` space.
-/

open Set

namespace GaloisForLFunctions.RHTower

/--
A product-formula functional that vanishes on a dense Kummer subspace
has only the zero continuous extension.
-/
theorem deningerAdelicKummer_continuous_eq_zero_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [Zero Y]
    (trace : X → Y)
    (htrace : Continuous trace)
    (kummer : Set X)
    (hkummer : Dense kummer)
    (hzero : ∀ x ∈ kummer, trace x = 0) :
    trace = 0 := by
  apply Continuous.ext_on hkummer htrace continuous_const
  intro x hx
  simpa using hzero x hx

section HalfTate

variable {R V : Type*}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/--
If `root * root = degree`, the square-root Tate action scales a
bilinear pairing by `degree`.
-/
theorem deningerAdelicKummer_halfTate_pairing_scale
    (B : V → V → R)
    (hleft : ∀ c x y, B (c • x) y = c * B x y)
    (hright : ∀ x c y, B x (c • y) = c * B x y)
    (degree root : R)
    (hroot : root * root = degree)
    (x y : V) :
    B (root • x) (root • y) = degree * B x y := by
  calc
    B (root • x) (root • y) =
        root * B x (root • y) := hleft _ _ _
    _ = root * (root * B x y) := by rw [hright]
    _ = (root * root) * B x y := by rw [mul_assoc]
    _ = degree * B x y := by rw [hroot]

/--
After inverse square-root centering, the scalar half-Tate action is the
identity.  Hence this sector alone cannot carry nontrivial centered
spectrum.
-/
theorem deningerAdelicKummer_centered_halfTate_eq
    (root invRoot : R)
    (hinv : invRoot * root = 1)
    (x : V) :
    invRoot • (root • x) = x := by
  rw [smul_smul, hinv, one_smul]

end HalfTate

end GaloisForLFunctions.RHTower
