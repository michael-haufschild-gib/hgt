import GaloisForLFunctions.HTGeometry.SteinbergSymbolSwap

/-!
# The torus elements commute up to the centre

The swap law identifies the commutator of two torus elements with a ratio of Steinberg symbols,

```text
h(u) h(v) h(u)⁻¹ h(v)⁻¹ = {v,u}⁻¹ {u,v} ,
```

and both symbols lie in `K₂`, which is central.  So the torus elements of the Steinberg group
commute modulo the centre: the subgroup they generate is abelian in `St(R)/K₂`, which is exactly the
statement that `u ↦ h(u)` is a homomorphism to `E(R)` — its image is the diagonal `d(u)`, and those
do commute.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The commutator of two torus elements lies in `K₂`.** -/
theorem torus_commutator_mem_KTwo {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
        * (steinbergTorus hij v)⁻¹ ∈ KTwo R n := by
  rw [← steinbergSymbol_swap hij u v]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (steinbergSymbol_mem_KTwo hij v u))
    (steinbergSymbol_mem_KTwo hij u v)

/-- **The commutator of two torus elements is central**, as soon as a third index is available. -/
theorem torus_commutator_mem_center {i j : n} (hij : i ≠ j) (u v : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
        * (steinbergTorus hij v)⁻¹ ∈ Subgroup.center (SteinbergGroup R n) := by
  rw [← steinbergSymbol_swap hij u v]
  exact Subgroup.mul_mem _
    (Subgroup.inv_mem _ (steinbergSymbol_mem_center hij v u hhi hhj))
    (steinbergSymbol_mem_center hij u v hhi hhj)

/-- **The torus elements commute modulo `K₂`.**  Their commutator maps to the identity, because the
diagonal units commute. -/
theorem steinbergToGL_torus_commutator {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergToGL (steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
      * (steinbergTorus hij v)⁻¹) = 1 :=
  (mem_KTwo_iff _).1 (torus_commutator_mem_KTwo hij u v)

end GaloisForLFunctions.HTGeometry

end
