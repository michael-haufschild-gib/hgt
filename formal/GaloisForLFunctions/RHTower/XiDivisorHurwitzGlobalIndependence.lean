import GaloisForLFunctions.RHTower.XiZeroHurwitzDifferentialIndependence
import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionMatroid
import GaloisForLFunctions.HTGeometry.UpperEndRationalGauge
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra
import GaloisForLFunctions.HTGeometry.UpperEndConstantField

/-!
# Global Hurwitz differential independence over the whole Xi divisor

Every finite injective family of Xi-divisor points indexes a differentially independent family of
continued Hurwitz functions.  Differential independence is a finitary property, so the finite law
upgrades to the entire divisor at once: the Hurwitz functions indexed by *all* nontrivial zeros of
the Riemann zeta function admit no joint algebraic differential relation over `ℂ(a)` whatsoever.

The statement is unconditional.  It assumes neither the Riemann Hypothesis nor simplicity nor any
correlation hypothesis.  The only input is that every nontrivial zero lies in an open strip of width
one, which is exactly the period of the Hurwitz monodromy character `s ↦ exp (2 π i s)`; that
coincidence makes the zeros automatically monodromy-separated however they are distributed.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

local instance globalXiRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance globalXiUpperEndCharZero :
    letI := isDomain_upperEndAnalyticSubring
    CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

/-- The rational coordinate field embeds into the upper-end meromorphic field as a differential
subfield: the embedding intertwines the formal derivative with the analytic one. -/
local instance globalXiRatFuncDifferentialAlgebra :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  refine ⟨fun r => ?_⟩
  induction r using RatFunc.induction_on with
  | f p q hq =>
      set pR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p with hpR
      set qR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q with hqRdef
      have hmapp : upperEndRatfuncToMero pR = upperEndPolyToMero p :=
        upperEndRatfuncToMero_algebraMap_polynomial p
      have hmapq : upperEndRatfuncToMero qR = upperEndPolyToMero q :=
        upperEndRatfuncToMero_algebraMap_polynomial q
      change (upperEndRatfuncToMero (pR / qR))′ = upperEndRatfuncToMero ((pR / qR)′)
      rw [map_div₀ upperEndRatfuncToMero, Derivation.leibniz_div]
      have hdiv : ((pR / qR)′ : RatFunc ℂ)
          = qR⁻¹ ^ 2 * (qR * (pR)′ - pR * (qR)′) := by
        change ratFuncCoordinateDerivation ℂ (pR / qR) = _
        rw [Derivation.leibniz_div]
        rfl
      rw [hdiv]
      simp only [map_mul, map_sub, map_pow, map_inv₀]
      have hp' : ((pR)′ : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative := by
        change ratFuncCoordinateDerivation ℂ pR = _
        rw [hpR, ratFuncCoordinateDerivation_algebraMap]
      have hq' : ((qR)′ : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative := by
        change ratFuncCoordinateDerivation ℂ qR = _
        rw [hqRdef, ratFuncCoordinateDerivation_algebraMap]
      rw [hp', hq', hmapp, hmapq, upperEndMero_deriv_polyEval, upperEndMero_deriv_polyEval,
        upperEndRatfuncToMero_algebraMap_polynomial,
        upperEndRatfuncToMero_algebraMap_polynomial]
      simp only [smul_eq_mul]

/-- **Global Xi-divisor Hurwitz independence.**  The analytically continued Hurwitz functions
indexed by the entire Xi divisor -- that is, by *all* nontrivial zeros of the Riemann zeta function
simultaneously -- are jointly differentially independent over `ℂ(a)`.  No algebraic differential
relation holds among any collection of them.

Unconditional: no Riemann Hypothesis, no simplicity, no correlation hypothesis. -/
theorem xi_divisor_hurwitz_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero ((ρ : XiDivisorSupport) : ℂ)) := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  refine differentialIndependent_of_forall_finite_subfamily _ ?_
  intro I hI
  haveI : Fintype I := hI.fintype
  exact xi_zero_hurwitz_differentialIndependent
    (fun i : I => (i : XiDivisorSupport)) Subtype.val_injective

/-- **Critical-strip Hurwitz independence law.**  For *any* set `S` of points in the open critical
strip, the analytically continued Hurwitz functions indexed by `S` are jointly differentially
independent over `ℂ(a)`.

Nothing arithmetic is used: the strip has width one, which is exactly the period of the Hurwitz
monodromy character `s ↦ exp (2 π i s)`, so strip points are automatically monodromy-separated, and
`0 < Re s < 1` automatically excludes the integers.  Every arithmetic instance -- the nontrivial
zeros of the Riemann zeta function, of any Dirichlet `L`-function, of any Dedekind zeta function, of
any member of the Selberg class -- is a corollary, since all such zeros lie in this strip. -/
theorem openCriticalStrip_hurwitz_differentialIndependent
    (S : Set ℂ) (hS : ∀ s ∈ S, 0 < s.re ∧ s.re < 1) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun s : S => continuedHzetaUpperEndMero ((s : ℂ))) := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  refine differentialIndependent_of_forall_finite_subfamily _ ?_
  intro J hJ
  haveI : Fintype J := hJ.fintype
  have hstrip : ∀ j : J, 0 < (((j : S) : ℂ)).re ∧ (((j : S) : ℂ)).re < 1 := by
    intro j
    exact hS _ (j : S).2
  have hnon : ∀ j : J, ∀ m : ℤ, ((j : S) : ℂ) ≠ (m : ℂ) := by
    intro j m
    exact openCriticalStrip_point_ne_int (hstrip j) m
  rw [continued_hurwitz_intrinsic_residue_differentialMatroid_law _ hnon]
  intro i j hmono
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference ((i : S) : ℂ) ((j : S) : ℂ)).mp hmono
  exact openCriticalStrip_eq_of_sub_eq_int (hstrip i) (hstrip j) m hm

end

end RHTower

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- Two points of a common open strip of width one that differ by an integer are equal. -/
theorem widthOneStrip_eq_of_sub_eq_int {a : ℝ} {s t : ℂ}
    (hs : a < s.re ∧ s.re < a + 1) (ht : a < t.re ∧ t.re < a + 1)
    (m : ℤ) (h : s - t = (m : ℂ)) : s = t := by
  have hre : s.re - t.re = (m : ℝ) := by
    have := congrArg Complex.re h
    simpa using this
  have hlt : (-1 : ℝ) < (m : ℝ) := by rw [← hre]; linarith [hs.1, hs.2, ht.1, ht.2]
  have hgt : (m : ℝ) < 1 := by rw [← hre]; linarith [hs.1, hs.2, ht.1, ht.2]
  have hm0 : m = 0 := by
    have h1 : (-1 : ℤ) < m := by exact_mod_cast hlt
    have h2 : m < 1 := by exact_mod_cast hgt
    omega
  subst hm0
  have : s - t = 0 := by simpa using h
  exact sub_eq_zero.mp this

/-- **The monodromy coordinate is injective on any open strip of width one.**  This is the engine of
the whole vein: the period of `mu` equals the width of the strip, so no two distinct strip points can
share a monodromy scalar. -/
theorem monoScalar_injOn_widthOneStrip {a : ℝ} :
    Set.InjOn monoScalar {s : ℂ | a < s.re ∧ s.re < a + 1} := by
  intro s hs t ht hmono
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference s t).mp hmono
  exact widthOneStrip_eq_of_sub_eq_int hs ht m hm

end

end RHTower
