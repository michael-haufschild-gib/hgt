import GaloisForLFunctions.HTGeometry.StokesFinitePuiseuxDendrogram
import GaloisForLFunctions.HTGeometry.StokesGaloisMicrolocalCoarea

/-!
# Coefficient-generated orbit descent and the one-port law

Finite Puiseux coefficients generate their canonical threshold cuts.  A surjective branch-orbit
map then descends those cuts to mixed Hom irregularities.  Thus the exact one-port coarea identity
and positivity on the physical-rank-zero hyperplane follow from coefficient data, without a rooted
realization or cut family among the hypotheses.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

noncomputable section

/-- Finite common-cover Puiseux branches grouped into irregular-class orbits. -/
structure PuiseuxOrbitCoareaDatum (n m K N : ℕ) where
  branches : FinitePuiseuxFamily m K N
  orbit : Fin m → Fin n
  orbit_surjective : Function.Surjective orbit

namespace PuiseuxOrbitCoareaDatum

variable {n m K N : ℕ}

/-- Number of canonical threshold-class cuts. -/
def edgeCount (d : PuiseuxOrbitCoareaDatum n m K N) : ℕ :=
  Fintype.card d.branches.toNatContactDendrogram.ThresholdEdge

/-- Orbit coarea datum constructed from coefficients, rather than supplied independently. -/
noncomputable def toOrbitCoareaDatum (d : PuiseuxOrbitCoareaDatum n m K N) :
    OrbitCoareaDatum n m d.edgeCount where
  cuts := d.branches.canonicalCuts
  orbit := d.orbit
  orbit_surjective := d.orbit_surjective

@[simp] theorem toOrbit_root (d : PuiseuxOrbitCoareaDatum n m K N) :
    d.toOrbitCoareaDatum.cuts.root = (K + 1 : ℕ) / (N : ℝ) := rfl

/-- Mixed Hom irregularity written directly as a normalized branch highest-difference sum. -/
def normalizedHomIrregularity (d : PuiseuxOrbitCoareaDatum n m K N)
    (i j : Fin n) : ℝ :=
  ∑ a ∈ Finset.univ with d.orbit a = i,
    ∑ b ∈ Finset.univ with d.orbit b = j,
      d.branches.contactNumerator a b / (N : ℝ)

/-- Orbit Hom irregularity is exactly the coefficient-level branch sum. -/
theorem homIrregularity_eq_normalizedCoefficientSum
    (d : PuiseuxOrbitCoareaDatum n m K N) (i j : Fin n) :
    d.toOrbitCoareaDatum.homIrregularity i j = d.normalizedHomIrregularity i j := by
  simp only [OrbitCoareaDatum.homIrregularity, OrbitCoareaDatum.fiberSum,
    normalizedHomIrregularity, toOrbitCoareaDatum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact d.branches.canonicalCuts_contact_eq a b

/-- **Coefficient-generated one-port coarea law.** The sole potentially negative channel is the
square of total branch charge; all threshold-class channels and terminal orbit channels are
positive squares. -/
theorem cartanQuadratic_eq_coefficient_onePort
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.toOrbitCoareaDatum.cartanQuadratic x =
      d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.blockEnergy x -
      (((K + 1 : ℕ) : ℝ) / N - 1) *
        d.toOrbitCoareaDatum.physicalRank x ^ 2 := by
  rw [d.toOrbitCoareaDatum.cartanQuadratic_eq_positive_sub_onePort]
  rw [d.toOrbit_root]

/-- The coefficient-generated Cartan form is strictly positive on rank-zero charges. -/
theorem cartanQuadratic_pos_of_physicalRank_eq_zero
    (d : PuiseuxOrbitCoareaDatum n m K N) {x : Fin n → ℝ}
    (hrank : d.toOrbitCoareaDatum.physicalRank x = 0) (hx : x ≠ 0) :
    0 < d.toOrbitCoareaDatum.cartanQuadratic x :=
  d.toOrbitCoareaDatum.cartanQuadratic_pos_of_physicalRank_eq_zero hrank hx

end PuiseuxOrbitCoareaDatum
end
end IrregularStokes
end GaloisForLFunctions
