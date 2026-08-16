import Mathlib

/-!
# The support of a corank-one kernel is read off the adjugate

A square matrix over a field whose kernel is one-dimensional has a kernel spanned by any nonzero
column of its adjugate: the identity `M · adj M = (det M) · 1` makes every such column a kernel
vector, and one dimension leaves no room for anything else.  Consequently the *support* of a kernel
vector — which coordinates are nonzero — does not depend on the vector, and a single nonvanishing
cofactor certifies that every kernel vector has a nonzero entry in the matching coordinate.

This is the shape in which a generic corank-one statement plus a nonvanishing corner cofactor pins
the leading coefficients of the associated polynomial pair.
-/

noncomputable section

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]

/-- Every column of the adjugate lies in the kernel once the determinant vanishes. -/
theorem mulVec_adjugate_col {M : Matrix N N K} (hdet : M.det = 0) (j : N) :
    M.mulVec (fun k => M.adjugate k j) = 0 := by
  have h : ∀ i : N, (∑ k : N, M i k * M.adjugate k j) = 0 := by
    intro i
    have hmul := congrArg (fun A : Matrix N N K => A i j) (Matrix.mul_adjugate M)
    simpa [Matrix.mul_apply, hdet] using hmul
  funext i
  simpa [Matrix.mulVec, dotProduct] using h i

omit [DecidableEq N] in
/-- **A one-dimensional kernel is spanned by any of its nonzero vectors.** -/
theorem ker_proportional_of_finrank_one {M : Matrix N N K}
    (hrank : Module.finrank K (LinearMap.ker M.mulVecLin) = 1)
    {v w : N → K} (hv : M.mulVec v = 0) (hw : M.mulVec w = 0) (hwne : w ≠ 0) :
    ∃ c : K, ∀ k, v k = c * w k := by
  have hvmem : v ∈ LinearMap.ker M.mulVecLin := by
    simpa [LinearMap.mem_ker] using hv
  have hwmem : w ∈ LinearMap.ker M.mulVecLin := by
    simpa [LinearMap.mem_ker] using hw
  have hwS : (⟨w, hwmem⟩ : LinearMap.ker M.mulVecLin) ≠ 0 := by
    simpa [Subtype.ext_iff] using hwne
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hwS).1 hrank ⟨v, hvmem⟩
  refine ⟨c, fun k => ?_⟩
  have := congrArg (fun x : LinearMap.ker M.mulVecLin => (x : N → K) k) hc
  simpa [eq_comm] using this

/-- **A nonvanishing cofactor certifies a nonvanishing kernel coordinate.**  If the kernel is
one-dimensional and the adjugate entry at `(i, j)` is nonzero, then every nonzero kernel vector has
a nonzero `i`-th coordinate. -/
theorem ker_coord_ne_zero_of_adjugate_ne_zero {M : Matrix N N K}
    (hrank : Module.finrank K (LinearMap.ker M.mulVecLin) = 1)
    {v : N → K} (hv : M.mulVec v = 0) (hvne : v ≠ 0)
    {i j : N} (hcof : M.adjugate i j ≠ 0) :
    v i ≠ 0 := by
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hvne, hv⟩
  have hw : M.mulVec (fun k => M.adjugate k j) = 0 := mulVec_adjugate_col hdet j
  have hwne : (fun k => M.adjugate k j) ≠ 0 := by
    intro h
    exact hcof (congrFun h i)
  obtain ⟨c, hc⟩ := ker_proportional_of_finrank_one hrank hv hw hwne
  intro h0
  have hc0 : c = 0 := by
    have hi := hc i
    rw [h0] at hi
    exact (mul_eq_zero.1 hi.symm).resolve_right hcof
  refine hvne (funext fun k => ?_)
  have := hc k
  rw [hc0, zero_mul] at this
  simpa using this

omit [DecidableEq N] in
/-- **The support of a corank-one kernel is independent of the vector.** -/
theorem ker_coord_ne_zero_iff {M : Matrix N N K}
    (hrank : Module.finrank K (LinearMap.ker M.mulVecLin) = 1)
    {v w : N → K} (hv : M.mulVec v = 0) (hvne : v ≠ 0)
    (hw : M.mulVec w = 0) (hwne : w ≠ 0) (i : N) :
    v i ≠ 0 ↔ w i ≠ 0 := by
  obtain ⟨c, hc⟩ := ker_proportional_of_finrank_one hrank hv hw hwne
  obtain ⟨d, hd⟩ := ker_proportional_of_finrank_one hrank hw hv hvne
  constructor
  · intro hvi hwi
    exact hvi (by rw [hc i, hwi, mul_zero])
  · intro hwi hvi
    exact hwi (by rw [hd i, hvi, mul_zero])

end GaloisForLFunctions.HTGeometry

end
