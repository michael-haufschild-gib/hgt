import GaloisForLFunctions.HTGeometry.CommutativeOperatorSystem
import GaloisForLFunctions.HTGeometry.ChoquetBoundaryFunctionSystem

/-!
# Every boundary of a function system is a complete boundary

A boundary condition is a statement about the *scalar* level: it says `F` sees the sup-norm of
every element of `S`.  In the commutative model this already forces the matrix levels: positivity
of a matrix over `S` is detected on `F` alone.

The mechanism is that positivity of a scalar matrix is a family of sandwich inequalities
`0 ≤ v* A v`, and the sandwich of a matrix over `S` is itself an element of `S`
(`sandwich_mem`) — self-adjoint when the matrix is (`star_sandwich`).  The upgrade of the boundary
condition to real parts then transfers the inequality from `F` to all of `X`.

So the Shilov ideal computed at the scalar level is already the *complete* Shilov ideal: no
separate matricial boundary theory is needed in the commutative case.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Matrix

open scoped ComplexOrder

universe u

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The sandwich `v* x v` of a matrix of continuous functions by a vector of scalars. -/
noncomputable def sandwich {n : Type u} [Fintype n] (v : n → ℂ) (x : Matrix n n C(X, ℂ)) :
    C(X, ℂ) :=
  ∑ i, ∑ j, (star (v i) * v j) • x i j

omit [CompactSpace X] in
theorem sandwich_mem {S : Submodule ℂ C(X, ℂ)} {n : Type u} [Fintype n] (v : n → ℂ)
    {x : Matrix n n C(X, ℂ)} (hxS : ∀ i j, x i j ∈ S) : sandwich v x ∈ S :=
  Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => S.smul_mem _ (hxS i j)

omit [CompactSpace X] in
theorem sandwich_apply {n : Type u} [Fintype n] (v : n → ℂ) (x : Matrix n n C(X, ℂ)) (p : X) :
    sandwich v x p = star v ⬝ᵥ ((Matrix.of fun i j => x i j p) *ᵥ v) := by
  simp only [sandwich, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [CompactSpace X] in
theorem star_sandwich {n : Type u} [Fintype n] (v : n → ℂ) {x : Matrix n n C(X, ℂ)}
    (hxsa : xᴴ = x) : star (sandwich v x) = sandwich v x := by
  have hstar : ∀ i j, star (x i j) = x j i := by
    intro i j
    have h := congrFun (congrFun hxsa j) i
    rw [Matrix.conjTranspose_apply] at h
    exact h
  simp only [sandwich, star_sum, star_smul, star_mul, star_star, hstar]
  rw [Finset.sum_comm]

/-- **Every boundary is a complete boundary.**  Positivity of a matrix with entries in `S` is
detected on any boundary of `S`. -/
theorem mem_cstarCone_of_forall_mem {S : Submodule ℂ C(X, ℂ)} (hone : (1 : C(X, ℂ)) ∈ S)
    {F : Set X} (hF : IsBoundarySet S F) {n : Type u} [Fintype n] {x : Matrix n n C(X, ℂ)}
    (hxS : ∀ i j, x i j ∈ S) (hxsa : xᴴ = x)
    (hFpos : ∀ p ∈ F, (Matrix.of fun i j => x i j p).PosSemidef) :
    x ∈ cstarCone.{u} X n := by
  intro p
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · have hstar : ∀ i j, star (x i j) = x j i := by
      intro i j
      have h := congrFun (congrFun hxsa j) i
      rw [Matrix.conjTranspose_apply] at h
      exact h
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    have := congrFun (congrArg (fun f : C(X, ℂ) => (f : X → ℂ)) (hstar j i)) p
    simpa using this
  · -- the sandwich is an element of `S`, self-adjoint, and nonnegative on `F`
    set g : C(X, ℂ) := sandwich v x with hg
    have hgS : g ∈ S := sandwich_mem v hxS
    have hgsa : star g = g := star_sandwich v hxsa
    have hgim : ∀ q : X, (g q).im = 0 := by
      intro q
      have h := congrFun (congrArg (fun f : C(X, ℂ) => (f : X → ℂ)) hgsa) q
      simp only [ContinuousMap.star_apply, Complex.star_def] at h
      have h2 := congrArg Complex.im h
      simp only [Complex.conj_im] at h2
      linarith
    have hFle : ∀ q ∈ F, ((-g) q).re ≤ 0 := by
      intro q hq
      have hpos := (hFpos q hq).dotProduct_mulVec_nonneg v
      rw [← sandwich_apply v x q] at hpos
      rw [Complex.le_def] at hpos
      simp only [Complex.zero_re] at hpos
      simp only [ContinuousMap.neg_apply, Complex.neg_re]
      linarith [hpos.1]
    have hneg : ((-g) p).re ≤ 0 :=
      hF.re_le_of_forall_le hone (S.neg_mem hgS)
        (fun q => by simp [hgim q]) hFle p
    rw [← sandwich_apply v x p, Complex.le_def]
    simp only [ContinuousMap.neg_apply, Complex.neg_re] at hneg
    refine ⟨by simpa using by linarith, ?_⟩
    exact (hgim p).symm

/-- **The order-unit form.**  If a self-adjoint matrix over `S` is dominated by `t · 1ₙ ⊗ 1` at
every point of a boundary, it is dominated everywhere. -/
theorem sub_mem_cstarCone_of_forall_mem {S : Submodule ℂ C(X, ℂ)} (hone : (1 : C(X, ℂ)) ∈ S)
    {F : Set X} (hF : IsBoundarySet S F) {n : Type u} [Fintype n] [DecidableEq n]
    {x : Matrix n n C(X, ℂ)} (hxS : ∀ i j, x i j ∈ S) (hxsa : xᴴ = x) (t : ℝ)
    (hFpos : ∀ p ∈ F,
      (Matrix.of fun i j => ((t : ℂ) • amplifyUnit n (1 : C(X, ℂ)) - x) i j p).PosSemidef) :
    (t : ℂ) • amplifyUnit n (1 : C(X, ℂ)) - x ∈ cstarCone.{u} X n := by
  refine mem_cstarCone_of_forall_mem hone hF (fun i j => ?_) ?_ hFpos
  · refine S.sub_mem ?_ (hxS i j)
    by_cases hij : i = j
    · have he : ((t : ℂ) • amplifyUnit n (1 : C(X, ℂ))) i j = (t : ℂ) • (1 : C(X, ℂ)) := by
        simp [amplifyUnit_apply, hij]
      rw [he]
      exact S.smul_mem _ hone
    · have he : ((t : ℂ) • amplifyUnit n (1 : C(X, ℂ))) i j = 0 := by
        simp [amplifyUnit_apply, hij]
      rw [he]
      exact S.zero_mem
  · rw [Matrix.conjTranspose_sub, hxsa]
    congr 1
    ext i j
    rw [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · subst hij
      simp [amplifyUnit_apply]
    · simp [amplifyUnit_apply, hij, Ne.symm hij]

end ShilovLocal

end GaloisForLFunctions.HTGeometry
