import GaloisForLFunctions.HTGeometry.SteinbergWeylSquare

/-!
# The two orientations of a root, modulo `K₂`

Reversing the index pair reverses the root.  On matrices this is exact and needs no computation
beyond rearranging a sum:

```text
weylMatrix j i (−u⁻¹) = weylMatrix i j u ,      diagMatrix j i u⁻¹ = diagMatrix i j u .
```

Lifting to the Steinberg group, the corresponding differences map to the identity, hence lie in `K₂`
and — their words using only the two indices — are central.  So the Weyl and torus elements of the
two orientations agree modulo the centre, with the unit inverted and, for the Weyl element,
negated.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [Fintype n] in
/-- **Reversing the index pair reverses the root.** -/
theorem weylMatrix_swap {i j : n} (u : Rˣ) :
    weylMatrix j i (-u⁻¹) = (weylMatrix i j u : Matrix n n R) := by
  rw [weylMatrix, weylMatrix]
  have h1 : (((-u⁻¹ : Rˣ)) : R) = -(((u⁻¹ : Rˣ)) : R) := by simp
  have h2 : -((((-u⁻¹ : Rˣ)⁻¹ : Rˣ)) : R) = ((u : Rˣ) : R) := by simp
  rw [h1, h2]
  abel

omit [Fintype n] in
/-- **Reversing the index pair inverts the torus parameter.** -/
theorem diagMatrix_swap {i j : n} (u : Rˣ) :
    diagMatrix j i u⁻¹ = (diagMatrix i j u : Matrix n n R) := by
  rw [diagMatrix, diagMatrix]
  have h : ((((u⁻¹ : Rˣ)⁻¹ : Rˣ)) : R) = ((u : Rˣ) : R) := by simp
  rw [h]
  abel

/-- **The two orientations of the Weyl element agree modulo `K₂`.** -/
theorem steinbergWeyl_swap_mem_KTwo {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergWeyl (Ne.symm hij) (-u⁻¹) * (steinbergWeyl hij u)⁻¹ ∈ KTwo R n := by
  have h : steinbergToGL (steinbergWeyl (Ne.symm hij) (-u⁻¹))
      = steinbergToGL (steinbergWeyl hij u) := by
    refine Units.ext ?_
    rw [steinbergToGL_weyl, steinbergToGL_weyl]
    exact weylMatrix_swap u
  rw [mem_KTwo_iff, map_mul, map_inv, h, mul_inv_cancel]

/-- **The two orientations of the torus element agree modulo `K₂`.** -/
theorem steinbergTorus_swap_mem_KTwo {i j : n} (hij : i ≠ j) (u : Rˣ) :
    steinbergTorus (Ne.symm hij) u⁻¹ * (steinbergTorus hij u)⁻¹ ∈ KTwo R n := by
  have h : steinbergToGL (steinbergTorus (Ne.symm hij) u⁻¹)
      = steinbergToGL (steinbergTorus hij u) := by
    rw [steinbergToGL_torus, steinbergToGL_torus]
    refine Units.ext ?_
    exact diagMatrix_swap u
  rw [mem_KTwo_iff, map_mul, map_inv, h, mul_inv_cancel]

omit [Fintype n] in
theorem indexGens_pair_comm (i j : n) :
    indexGens (R := R) (n := n) {j, i} = indexGens (R := R) (n := n) {i, j} := by
  congr 1
  exact Finset.pair_comm j i

/-- **The Weyl orientation discrepancy is central**, as soon as a third index is available. -/
theorem steinbergWeyl_swap_mem_center {i j : n} (hij : i ≠ j) (u : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergWeyl (Ne.symm hij) (-u⁻¹) * (steinbergWeyl hij u)⁻¹
      ∈ Subgroup.center (SteinbergGroup R n) := by
  have hcl : steinbergWeyl (Ne.symm hij) (-u⁻¹) * (steinbergWeyl hij u)⁻¹
      ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (steinbergWeyl_mem_indexClosure hij u))
    rw [← indexGens_pair_comm (R := R) i j]
    exact steinbergWeyl_mem_indexClosure (Ne.symm hij) (-u⁻¹)
  refine KTwo_mem_center (h := h) (steinbergWeyl_swap_mem_KTwo hij u) hcl ?_
  simp [hhi, hhj]

/-- **The torus orientation discrepancy is central**, as soon as a third index is available. -/
theorem steinbergTorus_swap_mem_center {i j : n} (hij : i ≠ j) (u : Rˣ)
    {h : n} (hhi : h ≠ i) (hhj : h ≠ j) :
    steinbergTorus (Ne.symm hij) u⁻¹ * (steinbergTorus hij u)⁻¹
      ∈ Subgroup.center (SteinbergGroup R n) := by
  have hcl : steinbergTorus (Ne.symm hij) u⁻¹ * (steinbergTorus hij u)⁻¹
      ∈ Subgroup.closure (indexGens (R := R) (n := n) {i, j}) := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (steinbergTorus_mem_indexClosure hij u))
    rw [← indexGens_pair_comm (R := R) i j]
    exact steinbergTorus_mem_indexClosure (Ne.symm hij) u⁻¹
  refine KTwo_mem_center (h := h) (steinbergTorus_swap_mem_KTwo hij u) hcl ?_
  simp [hhi, hhj]

end GaloisForLFunctions.HTGeometry

end
