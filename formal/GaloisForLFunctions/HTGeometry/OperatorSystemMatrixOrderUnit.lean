import GaloisForLFunctions.HTGeometry.MatrixOrderedSpace

/-!
# An order unit is automatically a matrix order unit

An operator system is usually defined as a matrix-ordered `*`-vector space carrying an *Archimedean
matrix order unit*: a vector `e` whose amplifications `1ₙ ⊗ e` dominate every self-adjoint element
of every matrix level.  This module shows that the matrix requirement is redundant: an order unit
for the scalar level is automatically an order unit for every level, so only the scalar-level
condition has to be checked.

The mechanism is that the compression axiom already produces every *rank-one tensor*
`(conj wᵢ · wⱼ) • u` of a scalar-level positive `u`, hence every `A ⊗ u` with `A` positive
semidefinite.  Polarising the four vectors `δ₀ ± δ₁` and `δ₀ ± i δ₁` inside a single `2 × 2` level
bounds the symmetrised pair `[[0, u], [u*, 0]]`; one further compression transports that bound into
an arbitrary pair of positions, and summing over all pairs bounds the matrix itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix MatrixModule

universe u v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The rank-one tensor `(conj wᵢ · wⱼ) • u`. -/
def rankOneTensor {n : Type u} (w : n → ℂ) (u : V) : Matrix n n V :=
  Matrix.of fun i j => (star (w i) * w j) • u

@[simp]
theorem rankOneTensor_apply {n : Type u} (w : n → ℂ) (u : V) (i j : n) :
    rankOneTensor w u i j = (star (w i) * w j) • u := rfl

/-- A rank-one tensor is a compression of the scalar level. -/
theorem rankOneTensor_eq_compress {n : Type u} (w : n → ℂ) (u : V) :
    compress (Matrix.of fun (_ : PUnit.{u + 1}) (i : n) => w i)
        (Matrix.of fun (_ _ : PUnit.{u + 1}) => u) = rankOneTensor w u := by
  ext i j
  rw [compress_apply]
  simp only [Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, rankOneTensor_apply,
    smul_smul]
  rw [mul_comm]

variable [StarAddMonoid V] [StarModule ℂ V]

/-- Positivity at the scalar level. -/
def LevelOne (C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)) (u : V) : Prop :=
  (Matrix.of fun (_ _ : PUnit.{u + 1}) => u) ∈ C PUnit.{u + 1}

namespace IsMatrixOrdering

variable {C : ∀ (n : Type u) [Fintype n], Set (Matrix n n V)} (hC : IsMatrixOrdering C)

include hC

omit [StarModule ℂ V] in
/-- **Every rank-one tensor of a scalar-level positive is positive.** -/
theorem rankOneTensor_mem {n : Type u} [Fintype n] (w : n → ℂ) {u : V} (hu : LevelOne C u) :
    rankOneTensor w u ∈ C n := by
  have h := hC.compress_mem PUnit.{u + 1} n (Matrix.of fun (_ : PUnit.{u + 1}) (i : n) => w i) _ hu
  rwa [rankOneTensor_eq_compress] at h

omit [StarModule ℂ V] in
/-- A nonnegatively weighted diagonal tensor is positive. -/
theorem diagWeight_mem {n : Type u} [Fintype n] [DecidableEq n] (c : n → ℝ) (hc : ∀ k, 0 ≤ c k)
    {u : V} (hu : LevelOne C u) :
    (Matrix.of fun a b => if a = b then ((c a : ℂ)) • u else 0) ∈ C n := by
  classical
  have hsum : ∀ s : Finset n,
      (∑ k ∈ s, rankOneTensor (fun a => if a = k then ((Real.sqrt (c k) : ℝ) : ℂ) else 0) u)
        = Matrix.of fun a b => if a = b then (if a ∈ s then ((c a : ℂ)) • u else 0) else 0 := by
    intro s
    induction s using Finset.induction with
    | empty => ext a b; simp
    | insert k s hk ih =>
        rw [Finset.sum_insert hk, ih]
        ext a b
        by_cases hab : a = b
        · subst hab
          by_cases hak : a = k
          · subst hak
            have : ((Real.sqrt (c a) : ℝ) : ℂ) * ((Real.sqrt (c a) : ℝ) : ℂ) = ((c a : ℂ)) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc a)]
            simp [rankOneTensor, hk, this]
          · simp [rankOneTensor, hak, Finset.mem_insert]
        · by_cases hbk : b = k
          · have hak : a ≠ k := by rintro rfl; exact hab hbk.symm
            simp [rankOneTensor, hab, hak]
          · simp [rankOneTensor, hab, hbk]
  have hmem : ∀ s : Finset n,
      (Matrix.of fun a b => if a = b then (if a ∈ s then ((c a : ℂ)) • u else 0) else 0) ∈ C n := by
    intro s
    rw [← hsum s]
    induction s using Finset.induction with
    | empty =>
        have : (∑ k ∈ (∅ : Finset n),
            rankOneTensor (fun a => if a = k then ((Real.sqrt (c k) : ℝ) : ℂ) else 0) u)
              = (0 : Matrix n n V) := by simp
        rw [this]
        exact hC.zero_mem n
    | insert k s hk ih =>
        rw [Finset.sum_insert hk]
        exact hC.add_mem n _ (hC.rankOneTensor_mem _ hu) _ ih
  have := hmem Finset.univ
  simpa using this

end IsMatrixOrdering

/-! ## Matrix units and polarisation -/

variable {n : Type u} [DecidableEq n]

/-- The matrix with `u` in position `(i, j)` and zeros elsewhere. -/
def unitEntry (i j : n) (u : V) : Matrix n n V :=
  Matrix.of fun a b => if a = i ∧ b = j then u else 0

/-- The vector `δᵢ + θ δⱼ`. -/
def polVec (i j : n) (θ : ℂ) : n → ℂ :=
  fun p => (if p = i then (1 : ℂ) else 0) + (if p = j then θ else 0)

/-- **The polarisation identity.**  Averaging the four rank-one tensors along `δᵢ ± δⱼ` and
`δᵢ ± i δⱼ` cancels every diagonal contribution except the order-unit terms and leaves exactly the
symmetrised entry pair. -/
theorem polarization_identity (i j : n) (e a b : V) (t s : ℝ) :
    (2 : ℂ)⁻¹ • (rankOneTensor (polVec i j 1) ((t : ℂ) • e - a)
        + rankOneTensor (polVec i j (-1)) ((t : ℂ) • e + a)
        + rankOneTensor (polVec i j Complex.I) ((s : ℂ) • e - b)
        + rankOneTensor (polVec i j (-Complex.I)) ((s : ℂ) • e + b))
      = unitEntry i i (((t + s : ℝ) : ℂ) • e) + unitEntry j j (((t + s : ℝ) : ℂ) • e)
        - unitEntry i j (a + Complex.I • b) - unitEntry j i (a - Complex.I • b) := by
  ext p q
  by_cases hij : i = j
  · subst hij
    by_cases hpi : p = i <;> by_cases hqi : q = i <;>
      simp [rankOneTensor, unitEntry, polVec, hpi, hqi, Complex.ofReal_add] <;> match_scalars <;>
      (try simp only [Complex.I_sq]) <;> ring
  · have hji : j ≠ i := Ne.symm hij
    by_cases hpi : p = i <;> by_cases hpj : p = j <;> by_cases hqi : q = i <;>
        by_cases hqj : q = j <;>
      simp_all [rankOneTensor, unitEntry, polVec, Complex.ofReal_add] <;> match_scalars <;>
      (try simp only [Complex.I_sq]) <;> ring

end GaloisForLFunctions.HTGeometry
