/-
# Maximal real diagonal operators are self-adjoint

For an arbitrary index type `ι` and arbitrary real energy function `energy : ι → ℝ`, this file
constructs multiplication by `energy` on `ℓ²(ι)` with its maximal square-summability domain.  The
operator is densely defined and self-adjoint.

The maximal-domain statement matters: symmetry on finitely supported vectors alone would not
identify the physical Hamiltonian.  The adjoint-domain proof tests against every canonical basis
vector and recovers the weighted coordinate sequence exactly.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Analysis.InnerProductSpace.LinearPMap

open scoped InnerProductSpace LinearPMap

noncomputable section

namespace RHTower

open HilbertSchmidt

universe u

variable {ι : Type u}

/-- The Hilbert space `ℓ²(ι)` on which a real diagonal energy acts. -/
abbrev DiagonalL2 (ι : Type u) := lp (fun _ : ι => ℂ) 2

/-- Maximal domain of coordinatewise multiplication by a real energy function. -/
def maximalRealDiagonalDomain (energy : ι → ℝ) :
    Submodule ℂ (DiagonalL2 ι) where
  carrier := {x | Memℓp (fun i => (energy i : ℂ) * x i) 2}
  zero_mem' := by
    change Memℓp (fun i => (energy i : ℂ) * (0 : DiagonalL2 ι) i) 2
    rw [show (fun i => (energy i : ℂ) * (0 : DiagonalL2 ι) i) =
        (0 : ι → ℂ) by
      funext i
      change (energy i : ℂ) * 0 = 0
      simp]
    exact zero_memℓp
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun i => (energy i : ℂ) * (x + y) i) 2
    rw [show (fun i => (energy i : ℂ) * (x + y) i) =
        (fun i => (energy i : ℂ) * x i) +
          fun i => (energy i : ℂ) * y i by
      funext i
      change (energy i : ℂ) *
          ((x : DiagonalL2 ι) i + (y : DiagonalL2 ι) i) =
        (energy i : ℂ) * (x : DiagonalL2 ι) i +
          (energy i : ℂ) * (y : DiagonalL2 ι) i
      ring]
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    change Memℓp (fun i => (energy i : ℂ) * (c • x) i) 2
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      hx.const_smul c

/-- Coordinatewise multiplication by `energy`, on its maximal domain. -/
def maximalRealDiagonal (energy : ι → ℝ) :
    DiagonalL2 ι →ₗ.[ℂ] DiagonalL2 ι where
  domain := maximalRealDiagonalDomain energy
  toFun :=
    { toFun := fun x =>
        ⟨fun i => (energy i : ℂ) * (x : DiagonalL2 ι) i,
          x.property⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        change (energy i : ℂ) *
            ((x : DiagonalL2 ι) i + (y : DiagonalL2 ι) i) =
          (energy i : ℂ) * (x : DiagonalL2 ι) i +
            (energy i : ℂ) * (y : DiagonalL2 ι) i
        ring
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change (energy i : ℂ) * (c * (x : DiagonalL2 ι) i) =
          c * ((energy i : ℂ) * (x : DiagonalL2 ι) i)
        ring }

@[simp] theorem maximalRealDiagonal_apply
    (energy : ι → ℝ) (x : (maximalRealDiagonal energy).domain)
    (i : ι) :
    maximalRealDiagonal energy x i =
      (energy i : ℂ) * (x : DiagonalL2 ι) i :=
  rfl

/-- A real maximal diagonal operator is formally self-adjoint. -/
theorem maximalRealDiagonal_formalSelfAdjoint
    (energy : ι → ℝ) :
    (maximalRealDiagonal energy).IsFormalAdjoint
      (maximalRealDiagonal energy) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [maximalRealDiagonal_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal]
  ring

variable [DecidableEq ι]

/-- Every canonical coordinate vector belongs to the maximal domain. -/
theorem lpBasis_mem_maximalRealDiagonalDomain
    (energy : ι → ℝ) (i : ι) :
    lpBasis ι i ∈ maximalRealDiagonalDomain energy := by
  let y : DiagonalL2 ι :=
    (energy i : ℂ) • lpBasis ι i
  change Memℓp
    (fun j => (energy j : ℂ) * (lpBasis ι i) j) 2
  rw [show (fun j => (energy j : ℂ) * (lpBasis ι i) j) =
      fun j => y j by
    funext j
    change (energy j : ℂ) * (lpBasis ι i) j =
      (energy i : ℂ) * (lpBasis ι i) j
    by_cases hji : j = i
    · subst j
      rfl
    · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hji]
      simp]
  exact lp.memℓp y

/-- The maximal diagonal domain is dense because it contains the canonical basis. -/
theorem maximalRealDiagonal_dense (energy : ι → ℝ) :
    Dense ((maximalRealDiagonal energy).domain :
      Set (DiagonalL2 ι)) := by
  have hbasis :
      Dense (Submodule.span ℂ (Set.range (lpBasis ι)) :
        Set (DiagonalL2 ι)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (lpBasis ι).dense_span
  apply hbasis.mono
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact lpBasis_mem_maximalRealDiagonalDomain energy i

/-- The adjoint is forced to have the same coordinate action on its entire domain. -/
theorem maximalRealDiagonal_adjoint_apply
    (energy : ι → ℝ)
    (y : (maximalRealDiagonal energy)†.domain)
    (i : ι) :
    (maximalRealDiagonal energy)† y i =
      (energy i : ℂ) * (y : DiagonalL2 ι) i := by
  let e : (maximalRealDiagonal energy).domain :=
    ⟨lpBasis ι i,
      lpBasis_mem_maximalRealDiagonalDomain energy i⟩
  have hformal :=
    (LinearPMap.adjoint_isFormalAdjoint
      (maximalRealDiagonal_dense energy)).symm e y
  have heval :
      maximalRealDiagonal energy e =
        (energy i : ℂ) • lpBasis ι i := by
    apply lp.ext
    funext j
    rw [maximalRealDiagonal_apply]
    change (energy j : ℂ) * (lpBasis ι i) j =
      (energy i : ℂ) * (lpBasis ι i) j
    by_cases hji : j = i
    · subst j
      rfl
    · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hji]
      simp
  change
    inner ℂ (maximalRealDiagonal energy e) (y : DiagonalL2 ι) =
      inner ℂ (lpBasis ι i)
        ((maximalRealDiagonal energy)† y) at hformal
  rw [heval, inner_smul_left, Complex.conj_ofReal,
    lpBasis_apply, lp.inner_single_left] at hformal
  simpa [lp.inner_single_left, RCLike.inner_apply] using hformal.symm

/-- **Maximal real diagonal self-adjointness.**

For every index type and every real energy function, coordinate multiplication on its maximal
square-summability domain equals its Hilbert-space adjoint.
-/
theorem maximalRealDiagonal_isSelfAdjoint
    (energy : ι → ℝ) :
    IsSelfAdjoint (maximalRealDiagonal energy) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let y' : (maximalRealDiagonal energy)†.domain := ⟨y, hy⟩
      let z : DiagonalL2 ι := (maximalRealDiagonal energy)† y'
      change Memℓp (fun i => (energy i : ℂ) * y i) 2
      rw [show (fun i => (energy i : ℂ) * y i) = fun i => z i by
        funext i
        exact (maximalRealDiagonal_adjoint_apply energy y' i).symm]
      exact lp.memℓp z
    · intro x y hxy
      apply lp.ext
      funext i
      rw [maximalRealDiagonal_adjoint_apply,
        maximalRealDiagonal_apply]
      exact congrArg (fun z : DiagonalL2 ι =>
        (energy i : ℂ) * z i) hxy
  · exact
      (maximalRealDiagonal_formalSelfAdjoint energy).le_adjoint
        (maximalRealDiagonal_dense energy)

end RHTower
