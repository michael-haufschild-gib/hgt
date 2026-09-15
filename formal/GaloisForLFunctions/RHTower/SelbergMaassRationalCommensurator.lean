import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
import Mathlib.NumberTheory.HeckeRing.Defs

/-!
# Rational commensurators of principal-congruence Maass sources

A Maass source at principal level `N + 1` has a natural arithmetic ambient group:
its integral matrices, viewed in `GL(2, ℝ)`. Every element of `GL(2, ℚ)`
commensurates that group. Together with the positive-real Möbius covariance in
`SelbergMaassCuspTransport`, this supplies the group-theoretic input for a finite
Hecke trace.

This file does not construct that trace or assert its preservation of the source's
integral-cusp decay. Those are the remaining analytic steps before a Hecke action
on the bundled Maass source exists.
-/

namespace GaloisForLFunctions.RHTower

open scoped MatrixGroups Pointwise
open Matrix SpecialLinearGroup Subgroup

noncomputable section

/-- The principal congruence group at the source's positive level, embedded in `GL(2, ℝ)`. -/
abbrev principalCongruenceGL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma (N + 1) : Subgroup (GL (Fin 2) ℝ))

/-- The embedded principal congruence group at every source level is arithmetic. -/
theorem principalCongruenceGL_isArithmetic (N : ℕ) :
    (principalCongruenceGL N).IsArithmetic := by
  apply Subgroup.isArithmetic_iff_finiteIndex.mpr
  infer_instance

/-- Every rational invertible matrix commensurates the embedded principal congruence group. -/
theorem rationalGL_mem_commensurator_principalCongruenceGL (N : ℕ) (g : GL (Fin 2) ℚ) :
    g.map (Rat.castHom ℝ) ∈
      Subgroup.Commensurable.commensurator (principalCongruenceGL N) := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have hH : (principalCongruenceGL N).IsArithmetic := principalCongruenceGL_isArithmetic N
  have hconj :
      (ConjAct.toConjAct (g.map (Rat.castHom ℝ)) • principalCongruenceGL N).IsArithmetic := by
    letI : (principalCongruenceGL N).IsArithmetic := hH
    exact Subgroup.IsArithmetic.conj (principalCongruenceGL N) g
  exact hconj.is_commensurable.trans hH.is_commensurable.symm

end

end GaloisForLFunctions.RHTower
