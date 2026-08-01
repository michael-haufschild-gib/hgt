import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# Complex polynomial complements are path connected

For a multivariate complex polynomial `P`, any two points where `P` is
nonzero can be joined by a path on which `P` remains nonzero.

The proof is elementary and constructive at the level needed for spectral
transport.  Restrict `P` to the complex affine line through the two points.
The restriction is a nonzero univariate polynomial because it is nonzero at
the first endpoint, hence has finitely many roots.  The complex plane minus
that finite set is path connected, so a parameter path from `0` to `1`
avoids every root.  Composing with the affine line gives the desired path.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- Restriction of a multivariate polynomial to the complex affine line
`x + t (y-x)`. -/
noncomputable def complexMvPolynomialAffineLine {θ : Type*}
    (P : MvPolynomial θ ℂ)
    (x y : θ → ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i =>
      Polynomial.C (x i) +
        Polynomial.C (y i - x i) * Polynomial.X) P

theorem complexMvPolynomialAffineLine_eval {θ : Type*}
    (P : MvPolynomial θ ℂ)
    (x y : θ → ℂ) (t : ℂ) :
    (complexMvPolynomialAffineLine P x y).eval t =
      MvPolynomial.eval
        (fun i => x i + (y i - x i) * t) P := by
  change
    (((Polynomial.evalRingHom t).comp
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i =>
          Polynomial.C (x i) +
            Polynomial.C (y i - x i) * Polynomial.X))) P) =
      ((MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i => x i + (y i - x i) * t)) P)
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

theorem complexMvPolynomialAffineLine_ne_zero_of_left {θ : Type*}
    (P : MvPolynomial θ ℂ)
    (x y : θ → ℂ)
    (hx : MvPolynomial.eval x P ≠ 0) :
    complexMvPolynomialAffineLine P x y ≠ 0 := by
  intro hzero
  have heval :=
    complexMvPolynomialAffineLine_eval P x y 0
  rw [hzero] at heval
  simp at heval
  exact hx heval.symm

/-- Any two points in the nonzero locus of one complex multivariate
polynomial are joined inside that nonzero locus. -/
theorem exists_path_avoiding_complexMvPolynomial_zero {θ : Type*}
    (P : MvPolynomial θ ℂ)
    {x y : θ → ℂ}
    (hx : MvPolynomial.eval x P ≠ 0)
    (hy : MvPolynomial.eval y P ≠ 0) :
    ∃ path : Path x y,
      ∀ s : I, MvPolynomial.eval (path s) P ≠ 0 := by
  let q : Polynomial ℂ :=
    complexMvPolynomialAffineLine P x y
  have hq : q ≠ 0 :=
    complexMvPolynomialAffineLine_ne_zero_of_left P x y hx
  let bad : Set ℂ := {t | q.IsRoot t}
  have hbadFinite : bad.Finite := by
    exact Polynomial.finite_setOf_isRoot hq
  have hbadPathConnected : IsPathConnected badᶜ := by
    apply
      hbadFinite.countable.isPathConnected_compl_of_one_lt_rank
    rw [Complex.rank_real_complex]
    norm_num
  have hzeroGood : (0 : ℂ) ∈ badᶜ := by
    intro hzero
    apply hx
    have heval :=
      complexMvPolynomialAffineLine_eval P x y 0
    change q.eval 0 = 0 at hzero
    rw [hzero] at heval
    simpa using heval.symm
  have honeGood : (1 : ℂ) ∈ badᶜ := by
    intro hone
    apply hy
    have heval :=
      complexMvPolynomialAffineLine_eval P x y 1
    change q.eval 1 = 0 at hone
    rw [hone] at heval
    simpa [sub_add_cancel] using heval.symm
  have joined :
      JoinedIn badᶜ (0 : ℂ) 1 :=
    hbadPathConnected.joinedIn 0 hzeroGood 1 honeGood
  let parameter : Path (0 : ℂ) 1 := joined.somePath
  let path : Path x y :=
    { toFun := fun s i =>
        x i + (y i - x i) * parameter s
      continuous_toFun := by
        fun_prop
      source' := by
        funext i
        rw [parameter.source]
        ring
      target' := by
        funext i
        rw [parameter.target]
        ring }
  refine ⟨path, ?_⟩
  intro s hzero
  have hroot :
      q.IsRoot (parameter s) := by
    rw [Polynomial.IsRoot,
      complexMvPolynomialAffineLine_eval]
    exact hzero
  exact (joined.somePath_mem s) hroot

/-- Path-connectedness packaging for the complement of one complex
polynomial hypersurface.  Nonemptiness is supplied by one nonzero point. -/
theorem isPathConnected_complexMvPolynomial_nonzeroLocus {θ : Type*}
    (P : MvPolynomial θ ℂ)
    {x₀ : θ → ℂ}
    (hx₀ : MvPolynomial.eval x₀ P ≠ 0) :
    IsPathConnected
      {x : θ → ℂ | MvPolynomial.eval x P ≠ 0} := by
  refine ⟨x₀, hx₀, ?_⟩
  intro y hy
  obtain ⟨path, hpath⟩ :=
    exists_path_avoiding_complexMvPolynomial_zero
      P hx₀ hy
  exact ⟨path, hpath⟩

end GaloisForLFunctions.HTGeometry
