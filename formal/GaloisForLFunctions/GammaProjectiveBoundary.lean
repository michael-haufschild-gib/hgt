import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.OrbitBalanceAdditive

open Filter Finset

namespace GaloisForLFunctions

/-!
# Gamma projective-boundary infrastructure

This file starts the unconditional formalization of the Gamma projective-boundary theorem.
It records two load-bearing pieces without replacing the analytic theorem by an assumption:

* the order-two pole datum in the differentiated digamma shift equation has nonzero orbit mass,
  hence cannot be a finite shift coboundary;
* a finite relation whose normalized coefficients and jet monomials converge has the corresponding
  constant-coefficient limiting relation.

The remaining card work is the actual Gamma-field valuation and the holomorphic Bohr recurrence
theory needed to instantiate the second theorem.
-/

noncomputable section

/-- The order-two principal-part datum of
`ψ'(s + 1) - ψ'(s) = -1 / s²` on the integer translation orbit of `0`.

The coefficient is `-1` at the unique pole and zero elsewhere. -/
def digammaShiftDerivativePoleDatum : ℤ →₀ ℂ :=
  Finsupp.single 0 (-1)

/-- The differentiated digamma shift has nonzero total order-two pole mass. -/
@[simp]
theorem additiveOrbitSum_digammaShiftDerivativePoleDatum :
    additiveOrbitSum digammaShiftDerivativePoleDatum = -1 := by
  unfold digammaShiftDerivativePoleDatum
  exact additiveOrbitSum_single 0 (-1)

/-- The differentiated digamma shift datum is not the finite coboundary of any order-two
principal-part datum.  This is the orbit-mass obstruction behind the non-rationality step in the
Gamma projective-boundary proof. -/
theorem digammaShiftDerivativePoleDatum_ne_shiftCoboundary
    (E : ℤ →₀ ℂ) :
    digammaShiftDerivativePoleDatum ≠ additiveIntShiftCoboundary E := by
  exact single_ne_additiveIntShiftCoboundary 0 (by norm_num) E

/-- Finite projective coefficient limits turn translated finite relations into
constant-coefficient limiting relations.

Here `a n i` is the normalized coefficient of the `i`-th differential monomial after the `n`-th
vertical return, and `x n i` is that monomial evaluated on the returned jet.  The hypotheses are
the two genuine convergence statements; the conclusion is the autonomous relation used in the
Gamma boundary argument. -/
theorem finiteProjectiveRelationCollapse
    {ι : Type*} (S : Finset ι)
    (a x : ℕ → ι → ℂ) (da dx : ι → ℂ)
    (ha : ∀ i ∈ S, Tendsto (fun n => a n i) atTop (nhds (da i)))
    (hx : ∀ i ∈ S, Tendsto (fun n => x n i) atTop (nhds (dx i)))
    (hzero : ∀ n, ∑ i ∈ S, a n i * x n i = 0) :
    ∑ i ∈ S, da i * dx i = 0 := by
  have hlim :
      Tendsto (fun n => ∑ i ∈ S, a n i * x n i) atTop
        (nhds (∑ i ∈ S, da i * dx i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (ha i hi).mul (hx i hi)
  have hzeroLim :
      Tendsto (fun n => ∑ i ∈ S, a n i * x n i) atTop (nhds 0) := by
    rw [show (fun n => ∑ i ∈ S, a n i * x n i) = (fun _ => 0) by
      funext n
      exact hzero n]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzeroLim

end

end GaloisForLFunctions
