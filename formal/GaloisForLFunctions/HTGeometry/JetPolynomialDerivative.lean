import GaloisForLFunctions.HTGeometry.ImplicitLipschitzGraph
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Jet polynomials and their derivatives

An algebraic differential relation is a polynomial in the jet coordinates.  Its Fréchet derivative is
the sum, over monomials and coordinates, of the monomial with one coordinate differentiated, and its
`k`-th partial derivative is the corresponding coordinate sum.

The separation step of the phase-rank bound is driven by the top partial derivative of the relation,
so these formulas are what turns an explicit relation into an admissible regularity region.
-/

open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions

variable {N M : ℕ}

/-- The polynomial map on jet space defined by a finite family of monomials with coefficients. -/
noncomputable def jetPoly (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) : (Fin M → ℂ) → ℂ :=
  fun y => ∑ α, d α * ∏ j, (y j) ^ (e α j)

/-- The Fréchet derivative of `jetPoly`: the sum over monomials and coordinates of the monomial
with one coordinate differentiated. -/
noncomputable def jetPolyDeriv (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (y : Fin M → ℂ) :
    (Fin M → ℂ) →L[ℂ] ℂ :=
  ∑ α : Fin N, d α • ∑ j : Fin M,
    (∏ i ∈ (Finset.univ : Finset (Fin M)).erase j, (y i) ^ (e α i)) •
      (((e α j) • (y j) ^ (e α j - 1)) •
        (ContinuousLinearMap.proj j : (Fin M → ℂ) →L[ℂ] ℂ))

/-- A jet polynomial is continuous. -/
theorem continuous_jetPoly (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) :
    Continuous (jetPoly d e) := by
  refine continuous_finsetSum _ fun α _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun j _ => ((continuous_apply j).pow (e α j))

/-- **A jet polynomial is Fréchet differentiable, with derivative `jetPolyDeriv`.** -/
theorem hasFDerivAt_jetPoly (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (y : Fin M → ℂ) :
    HasFDerivAt (jetPoly d e) (jetPolyDeriv d e y) y := by
  classical
  have hcoord : ∀ (α : Fin N) (j : Fin M), HasFDerivAt (fun z : Fin M → ℂ => (z j) ^ (e α j))
      (((e α j) • (y j) ^ (e α j - 1)) •
        (ContinuousLinearMap.proj j : (Fin M → ℂ) →L[ℂ] ℂ)) y := by
    intro α j
    have hp : HasFDerivAt (fun z : Fin M → ℂ => z j)
        (ContinuousLinearMap.proj j : (Fin M → ℂ) →L[ℂ] ℂ) y :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin M => ℂ) j).hasFDerivAt
    exact HasFDerivAt.pow hp (e α j)
  have hmono : ∀ α : Fin N, HasFDerivAt (fun z : Fin M → ℂ => ∏ j, (z j) ^ (e α j))
      (∑ j : Fin M, (∏ i ∈ (Finset.univ : Finset (Fin M)).erase j, (y i) ^ (e α i)) •
        (((e α j) • (y j) ^ (e α j - 1)) •
          (ContinuousLinearMap.proj j : (Fin M → ℂ) →L[ℂ] ℂ))) y := fun α =>
    HasFDerivAt.finsetProd (fun j _ => hcoord α j)
  have h := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin N)))
    fun α _ => (hmono α).const_smul (d α)
  have hfun : (∑ α : Fin N, d α • fun z : Fin M → ℂ => ∏ j, (z j) ^ (e α j)) = jetPoly d e := by
    funext z
    simp [jetPoly, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rwa [hfun] at h

/-- The partial derivative of a jet polynomial in the `k`-th coordinate. -/
theorem partialCoeff_jetPolyDeriv (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (y : Fin M → ℂ)
    (k : Fin M) :
    partialCoeff (jetPolyDeriv d e y) k
      = ∑ α : Fin N, d α * (∏ i ∈ (Finset.univ : Finset (Fin M)).erase k, (y i) ^ (e α i)) *
          ((e α k : ℂ) * (y k) ^ (e α k - 1)) := by
  classical
  rw [partialCoeff, jetPolyDeriv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single k]
  · simp only [Pi.single_eq_same]
    ring
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The derivative of a jet polynomial depends continuously on the jet. -/
theorem continuous_jetPolyDeriv (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) :
    Continuous (jetPolyDeriv d e) := by
  refine continuous_finsetSum _ fun α _ => Continuous.const_smul ?_ (d α)
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun y : Fin M → ℂ =>
      ∏ i ∈ (Finset.univ : Finset (Fin M)).erase j, (y i) ^ (e α i) :=
    continuous_finsetProd _ fun i _ => (continuous_apply i).pow (e α i)
  have h2 : Continuous fun y : Fin M → ℂ => (e α j) • (y j) ^ (e α j - 1) :=
    ((continuous_apply j).pow (e α j - 1)).const_smul (e α j)
  exact h1.smul (h2.smul continuous_const)

/-- A jet polynomial is differentiable within any set, as a map of real Banach spaces. -/
theorem hasFDerivWithinAt_jetPoly (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (S : Set (Fin M → ℂ))
    (y : Fin M → ℂ) :
    HasFDerivWithinAt (jetPoly d e) ((jetPolyDeriv d e y).restrictScalars ℝ) S y :=
  ((hasFDerivAt_jetPoly d e y).restrictScalars ℝ).hasFDerivWithinAt

/-- A jet polynomial evaluated on the jet of a function is the corresponding monomial sum. -/
theorem jetPoly_jet (d : Fin N → ℂ) (e : Fin N → Fin M → ℕ) (F : ℂ → ℂ) (z : ℂ) :
    jetPoly d e (fun j : Fin M => iteratedDeriv (j : ℕ) F z)
      = ∑ α, d α * ∏ j : Fin M, (iteratedDeriv (j : ℕ) F z) ^ (e α j) := rfl

end GaloisForLFunctions
