import GaloisForLFunctions.HTGeometry.SteinbergSymbolCocycle

/-!
# The asymmetry of the Steinberg symbol is the torus commutator

Over a commutative ring the two orders of a product agree, `uv = vu`, so the two expressions

```text
h(uv) = {u,v} h(v) h(u) ,      h(vu) = {v,u} h(u) h(v)
```

describe the same element.  Comparing them isolates the failure of the symbol to be symmetric:

```text
{v,u}⁻¹ {u,v}  =  h(u) h(v) h(u)⁻¹ h(v)⁻¹ .
```

In particular the symbol is symmetric exactly when the two torus elements commute — and their
images `d(u), d(v)` always do, so the discrepancy lies in `K₂` and is therefore central.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- **The asymmetry of the symbol is the commutator of the torus elements.** -/
theorem steinbergSymbol_swap {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    (steinbergSymbol hij v u)⁻¹ * steinbergSymbol hij u v
      = steinbergTorus hij u * steinbergTorus hij v
        * (steinbergTorus hij u)⁻¹ * (steinbergTorus hij v)⁻¹ := by
  have h1 := steinbergTorus_mul hij u v
  have h2 := steinbergTorus_mul hij v u
  rw [mul_comm v u, h1] at h2
  refine mul_right_cancel (b := steinbergTorus hij v * steinbergTorus hij u) ?_
  calc (steinbergSymbol hij v u)⁻¹ * steinbergSymbol hij u v
        * (steinbergTorus hij v * steinbergTorus hij u)
      = (steinbergSymbol hij v u)⁻¹ * (steinbergSymbol hij u v
          * steinbergTorus hij v * steinbergTorus hij u) := by group
    _ = (steinbergSymbol hij v u)⁻¹ * (steinbergSymbol hij v u
          * steinbergTorus hij u * steinbergTorus hij v) := by rw [h2]
    _ = steinbergTorus hij u * steinbergTorus hij v := by group
    _ = steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
          * (steinbergTorus hij v)⁻¹ * (steinbergTorus hij v * steinbergTorus hij u) := by group

omit [DecidableEq n] [Fintype n] in
/-- **The symbol is symmetric exactly when the torus elements commute.** -/
theorem steinbergSymbol_comm_of_torus_commute {i j : n} (hij : i ≠ j) {u v : Rˣ}
    (hc : Commute (steinbergTorus hij u) (steinbergTorus hij v)) :
    steinbergSymbol hij u v = steinbergSymbol hij v u := by
  have h := steinbergSymbol_swap hij u v
  have hone : steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
      * (steinbergTorus hij v)⁻¹ = 1 := by
    rw [hc.eq]
    group
  rw [hone] at h
  have h2 : (steinbergSymbol hij v u)⁻¹ * steinbergSymbol hij u v = 1 := h
  exact (inv_mul_eq_one.1 h2).symm

omit [DecidableEq n] [Fintype n] in
/-- The converse: if the symbol is symmetric then the torus elements commute. -/
theorem torus_commute_of_steinbergSymbol_comm {i j : n} (hij : i ≠ j) {u v : Rˣ}
    (hs : steinbergSymbol hij u v = steinbergSymbol hij v u) :
    Commute (steinbergTorus hij u) (steinbergTorus hij v) := by
  have h := steinbergSymbol_swap hij u v
  rw [hs, inv_mul_cancel] at h
  have h2 : steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
      * (steinbergTorus hij v)⁻¹ = 1 := h.symm
  show steinbergTorus hij u * steinbergTorus hij v
      = steinbergTorus hij v * steinbergTorus hij u
  calc steinbergTorus hij u * steinbergTorus hij v
      = steinbergTorus hij u * steinbergTorus hij v * (steinbergTorus hij u)⁻¹
        * (steinbergTorus hij v)⁻¹ * (steinbergTorus hij v * steinbergTorus hij u) := by group
    _ = steinbergTorus hij v * steinbergTorus hij u := by rw [h2, one_mul]

end GaloisForLFunctions.HTGeometry

end
