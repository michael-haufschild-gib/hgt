import GaloisForLFunctions.HTGeometry.ReducedH0Components

/-!
# The degree-0 simplicial coboundary and its kernel

To exhibit the reduced zeroth cohomology `H̃⁰` of the previous file as genuine simplicial cohomology,
this file introduces the explicit degree-`0` coboundary of the `1`-skeleton of a finite complex,

```text
(δ⁰ f)(u,v) = f v − f u   on edges `u ∼ v`,   0 off edges,
```

as an `F`-linear map, and identifies its kernel with the component-constant `0`-cochains:

`ker δ⁰ = componentConstant G F`.

Hence `H⁰ = ker δ⁰` really is the component-constant space, and `reduced H̃⁰ = ker δ⁰ / ⟨1⟩` (previous
file) is honest reduced simplicial cohomology.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (F : Type*) [Field F]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Membership in the component-constant submodule is adjacency-invariance. -/
theorem mem_componentConstant {f : V → F} :
    f ∈ componentConstant G F ↔ ∀ u v, G.Adj u v → f u = f v := Iff.rfl

/-- The degree-`0` simplicial coboundary `(δ⁰ f)(u,v) = f v − f u` on edges, `0` off edges. -/
def graphCoboundary : (V → F) →ₗ[F] (V → V → F) where
  toFun f := fun u v => if G.Adj u v then f v - f u else 0
  map_add' f g := by
    funext u v; by_cases h : G.Adj u v <;> simp only [Pi.add_apply, h, if_true, if_false] <;> ring
  map_smul' r f := by
    funext u v
    by_cases h : G.Adj u v <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, if_true, if_false] <;> ring

omit [Fintype V] [DecidableEq V] in
theorem graphCoboundary_apply (f : V → F) (u v : V) :
    graphCoboundary G F f u v = if G.Adj u v then f v - f u else 0 := rfl

omit [Fintype V] [DecidableEq V] in
/-- **The kernel of the degree-`0` coboundary is the component-constant cochains.**  Thus `H⁰` of the
`1`-skeleton is exactly `componentConstant G F`. -/
theorem graphCoboundary_ker :
    LinearMap.ker (graphCoboundary G F) = componentConstant G F := by
  ext f
  rw [LinearMap.mem_ker, mem_componentConstant]
  constructor
  · intro hf u v huv
    have h0 : graphCoboundary G F f u v = 0 := by rw [hf]; rfl
    rw [graphCoboundary_apply, if_pos huv] at h0
    exact (sub_eq_zero.mp h0).symm
  · intro hf
    funext u v
    show graphCoboundary G F f u v = 0
    rw [graphCoboundary_apply]
    by_cases huv : G.Adj u v
    · rw [if_pos huv, sub_eq_zero]; exact (hf u v huv).symm
    · rw [if_neg huv]

end

end GaloisForLFunctions
