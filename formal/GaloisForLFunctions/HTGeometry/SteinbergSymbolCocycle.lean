import GaloisForLFunctions.HTGeometry.SteinbergSymbolNormalization

/-!
# The Steinberg symbol is a cocycle

The torus elements fail to be multiplicative exactly by the symbol,

```text
h(uv) = {u,v} · h(v) · h(u) ,
```

and the symbol is central, because it lies in `K₂` and its word uses only the two indices of the
Weyl element.  Computing `h(uvw)` in the two possible ways and cancelling the common tail therefore
gives the two-cocycle identity

```text
{uv, w} · {u, v}  =  {u, vw} · {v, w} .
```

This is the associativity constraint that Matsumoto's presentation imposes on the symbol; with
bimultiplicativity and the Steinberg relation it is what makes the symbol descend from `K₂^M`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-! ## The symbol uses only two indices -/

omit [Fintype n] in
theorem steinbergWeyl_mem_indexClosure {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergWeyl hij u ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
  rw [steinbergWeyl]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure ⟨i, j, hij, by simp, by simp, _, rfl⟩
  · exact Subgroup.subset_closure ⟨j, i, Ne.symm hij, by simp, by simp, _, rfl⟩
  · exact Subgroup.subset_closure ⟨i, j, hij, by simp, by simp, _, rfl⟩

omit [Fintype n] in
theorem steinbergTorus_mem_indexClosure {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergTorus hij u ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
  rw [steinbergTorus]
  exact Subgroup.mul_mem _ (steinbergWeyl_mem_indexClosure hij u)
    (steinbergWeyl_mem_indexClosure hij (-1 : Rˣ))

omit [Fintype n] in
theorem steinbergSymbol_mem_indexClosure {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergSymbol hij u v ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
  rw [steinbergSymbol]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact steinbergTorus_mem_indexClosure hij (u * v)
  · exact Subgroup.inv_mem _ (steinbergTorus_mem_indexClosure hij u)
  · exact Subgroup.inv_mem _ (steinbergTorus_mem_indexClosure hij v)

/-- **The Steinberg symbol is central**, as soon as a third index is available. -/
theorem steinbergSymbol_mem_center {i j : n} (hij : i ≠ j) (u v : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergSymbol hij u v ∈ Subgroup.center (SteinbergGroup R n) := by
  refine KTwo_mem_center (h := h) (steinbergSymbol_mem_KTwo hij u v)
    (steinbergSymbol_mem_indexClosure hij u v) ?_
  simp [hhi, hhj]

/-! ## The cocycle identity -/

omit [DecidableEq n] [Fintype n] in
/-- The torus elements multiply up to the symbol. -/
theorem steinbergTorus_mul {i j : n} (hij : i ≠ j) (u v : Rˣ) :
    steinbergTorus hij (u * v)
      = steinbergSymbol hij u v * steinbergTorus hij v * steinbergTorus hij u := by
  rw [steinbergSymbol]
  group

/-- **The two-cocycle identity of the Steinberg symbol.** -/
theorem steinbergSymbol_cocycle {i j : n} (hij : i ≠ j) (u v w : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergSymbol hij (u * v) w * steinbergSymbol hij u v
      = steinbergSymbol hij u (v * w) * steinbergSymbol hij v w := by
  have hcuv := Subgroup.mem_center_iff.1 (steinbergSymbol_mem_center hij u v hhi hhj)
    (steinbergTorus hij w)
  have e1 : steinbergTorus hij (u * v * w)
      = (steinbergSymbol hij (u * v) w * steinbergSymbol hij u v)
        * (steinbergTorus hij w * (steinbergTorus hij v * steinbergTorus hij u)) := by
    rw [steinbergTorus_mul hij (u * v) w, steinbergTorus_mul hij u v]
    rw [show steinbergSymbol hij (u * v) w * steinbergTorus hij w
        * (steinbergSymbol hij u v * steinbergTorus hij v * steinbergTorus hij u)
        = steinbergSymbol hij (u * v) w * (steinbergTorus hij w * steinbergSymbol hij u v)
          * (steinbergTorus hij v * steinbergTorus hij u) by group]
    rw [hcuv]
    group
  have e2 : steinbergTorus hij (u * (v * w))
      = (steinbergSymbol hij u (v * w) * steinbergSymbol hij v w)
        * (steinbergTorus hij w * (steinbergTorus hij v * steinbergTorus hij u)) := by
    rw [steinbergTorus_mul hij u (v * w), steinbergTorus_mul hij v w]
    group
  rw [mul_assoc u v w, e2] at e1
  exact (mul_right_cancel e1).symm

end GaloisForLFunctions.HTGeometry

end
