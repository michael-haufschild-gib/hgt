/-
# Rational interpolation

A complex polynomial of degree at most `N` that takes rational values at `N + 1` distinct rational
points has rational coefficients.  This is `Exercise 1` of Coleman--Zwald, and it is the device that
disposes of the *polynomial* branch in the trichotomy of Hilbert's irreducibility theorem: a
polynomial with one irrational coefficient can only take rational values at finitely many integers.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Interpolation descent.**  A polynomial over `L` of degree `< s.card` whose values at the
`K`-rational nodes `v i` are `K`-rational is the image of a polynomial over `K`. -/
theorem exists_map_eq_of_eval_mem_range {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → K)
    (hv : Set.InjOn (fun i => algebraMap K L (v i)) s) (r : ι → K) {g : L[X]}
    (hdeg : g.degree < s.card)
    (heval : ∀ i ∈ s, g.eval (algebraMap K L (v i)) = algebraMap K L (r i)) :
    g = (Lagrange.interpolate s v r).map (algebraMap K L) := by
  classical
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hvK : Set.InjOn v s := fun a ha b hb hab => hv ha hb (by simp only [hab])
  set p : K[X] := Lagrange.interpolate s v r with hp
  have hpdeg : p.degree < s.card := Lagrange.degree_interpolate_lt r hvK
  have hmapdeg : (p.map (algebraMap K L)).degree < s.card := by
    refine lt_of_le_of_lt (degree_map_le) hpdeg
  have hmapeval : ∀ i ∈ s, (p.map (algebraMap K L)).eval (algebraMap K L (v i))
      = algebraMap K L (r i) := by
    intro i hi
    rw [eval_map, eval₂_at_apply, Lagrange.eval_interpolate_at_node r hvK hi]
  have h1 : g = Lagrange.interpolate s (fun i => algebraMap K L (v i))
      (fun i => algebraMap K L (r i)) :=
    Lagrange.eq_interpolate_of_eval_eq _ hv hdeg heval
  have h2 : p.map (algebraMap K L) = Lagrange.interpolate s (fun i => algebraMap K L (v i))
      (fun i => algebraMap K L (r i)) :=
    Lagrange.eq_interpolate_of_eval_eq _ hv hmapdeg hmapeval
  rw [h1, h2]

/-- **Rational coefficients from rational values.**  If a complex polynomial of degree at most `N`
takes rational values at `N + 1` distinct rational points, every coefficient is rational. -/
theorem coeff_mem_range_ratCast {N : ℕ} {g : ℂ[X]} (hdeg : g.degree < (N + 1 : ℕ))
    (v : Fin (N + 1) → ℚ) (hv : Function.Injective v) (r : Fin (N + 1) → ℚ)
    (heval : ∀ i, g.eval ((v i : ℚ) : ℂ) = ((r i : ℚ) : ℂ)) (k : ℕ) :
    ∃ q : ℚ, g.coeff k = (q : ℂ) := by
  classical
  have hcard : (Finset.univ : Finset (Fin (N + 1))).card = N + 1 := by simp
  have hvinj : Set.InjOn (fun i => algebraMap ℚ ℂ (v i)) (Finset.univ : Finset (Fin (N + 1))) := by
    intro a _ b _ hab
    have : ((v a : ℚ) : ℂ) = ((v b : ℚ) : ℂ) := by
      simpa [eq_ratCast (algebraMap ℚ ℂ)] using hab
    exact hv (by exact_mod_cast this)
  have hdeg' : g.degree < ((Finset.univ : Finset (Fin (N + 1))).card : ℕ) := by
    rw [hcard]; exact hdeg
  have := exists_map_eq_of_eval_mem_range (K := ℚ) (L := ℂ) Finset.univ v hvinj r hdeg'
    (by intro i _; simpa using heval i)
  refine ⟨(Lagrange.interpolate Finset.univ v r).coeff k, ?_⟩
  rw [this, coeff_map]
  simp

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
