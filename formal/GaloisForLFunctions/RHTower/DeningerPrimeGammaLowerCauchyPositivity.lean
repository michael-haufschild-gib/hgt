import GaloisForLFunctions.RHTower.DeningerPrimeGammaLowerCauchyTotality
import GaloisForLFunctions.RHTower.XiHurwitzOrientationCauchyClosure

/-!
# Lower absolute-Euler Cauchy positivity is an RH gate

The literal lower prime--Gamma Cauchy atoms are Hilbert-total in the full Xi--Weil Cauchy core.
Consequently, nonnegativity of the Weil quadratic form on their algebraic span extends by
continuity to the entire Cauchy core and forces RH.  This removes continuation and arbitrary
regular-Cauchy parameters from the source-sign obligation: it remains to establish the sign on
finite packets supported in the strict lower absolute-Euler sector.
-/

open Set Topology

namespace RHTower

noncomputable section

/-- Lower absolute-Euler prime--Gamma packet positivity extends to the full algebraic
Xi--Weil Cauchy core. -/
theorem cauchyCore_nonnegative_of_deningerPrimeGammaLowerCauchy_nonnegative
    (hpos : ∀ v ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v) :
    ∀ v ∈ xiWeilCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  have hvh : v ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace.topologicalClosure := by
    rw [deningerPrimeGammaLowerCauchyHilbertSubspace_eq_xiWeilCauchyHilbertSubspace]
    exact xiWeilCauchyAlgebraicSubspace.le_topologicalClosure hv
  let S : Set (lp (fun _ : XiZeroCopy => ℂ) 2) :=
    xiWeilHilbertQuadratic ⁻¹' Set.Ici 0
  have hSclosed : IsClosed S := by
    exact isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
  have hlower : (↑deningerPrimeGammaLowerCauchyAlgebraicSubspace :
      Set (lp (fun _ : XiZeroCopy => ℂ) 2)) ⊆ S := by
    intro x hx
    exact hpos x hx
  exact (closure_minimal hlower hSclosed) hvh

/-- **Lower-source RH gate.**  It suffices to prove Weil nonnegativity for finite Cauchy packets
in the strict lower absolute-Euler prime--Gamma sector. -/
theorem riemannHypothesis_of_deningerPrimeGammaLowerCauchy_nonnegative
    (hpos : ∀ v ∈ deningerPrimeGammaLowerCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v) : RiemannHypothesis :=
  riemannHypothesis_of_cauchyCore_nonnegative
    (cauchyCore_nonnegative_of_deningerPrimeGammaLowerCauchy_nonnegative hpos)

end

end RHTower
