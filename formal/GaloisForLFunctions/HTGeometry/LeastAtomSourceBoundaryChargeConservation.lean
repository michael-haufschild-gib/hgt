import GaloisForLFunctions.HTGeometry.LeastAtomModularTransferLaw
import GaloisForLFunctions.HTGeometry.CayleyPoleResidueTransport

/-!
# Source--boundary charge conservation

A least-atom modular character carries a base-normalized logarithmic
entropy.  Reflection about its self-dual line reverses that entropy.
The reflected entropy jump is exactly twice the signed transverse
displacement, independently of the atom scale.

Consequently, the horizontal component of every multiplicity-weighted
centered affine charge is recovered from any admissible atom clock.
This is the abstract conservation law later specialized to the Riemann
source and the centered Xi divisor current.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reflection difference of the base-normalized least-atom entropy is
twice the signed transverse displacement.  Atom scale cancels. -/
theorem leastAtomTransferEntropy_reflectionDifference
    {q : ℝ} (hq : 1 < q) (c : ℝ) (s : ℂ) :
    leastAtomTransferEntropy q c s -
        leastAtomTransferEntropy q c
          (leastAtomSourceReflection c s) =
      -2 * (s.re - c / 2) := by
  rw [leastAtomTransferEntropy_eq hq,
    leastAtomTransferEntropy_eq hq]
  simp only [leastAtomSourceReflection, sub_re, ofReal_re]
  have hstarRe : (star s).re = s.re := by simp
  rw [hstarRe]
  ring

/-- **Universal source--boundary charge conservation.**  For every atom
clock and reflection center, the horizontal component of a centered
affine charge is multiplicity times one half of the reflected entropy
jump.  The right-hand side is independent of atom scale. -/
theorem centeredAffineCharge_real_eq_reflectedLeastAtomEntropy
    {q : ℝ} (hq : 1 < q) (c : ℝ) (s : ℂ) (m : ℕ) :
    (-((s - ((c / 2 : ℝ) : ℂ)) * (m : ℂ))).re =
      (m : ℝ) / 2 *
        (leastAtomTransferEntropy q c s -
          leastAtomTransferEntropy q c
            (leastAtomSourceReflection c s)) := by
  rw [leastAtomTransferEntropy_reflectionDifference hq]
  have hcharge :
      (-((s - ((c / 2 : ℝ) : ℂ)) * (m : ℂ))).re =
        -(s.re - c / 2) * (m : ℝ) := by
    simp only [neg_re, mul_re, sub_re, ofReal_re]
    norm_num
    ring
  rw [hcharge]
  ring

/-- The source-Cayley escape rate is the negative reflected entropy
jump for every admissible atom clock.  The real source point `c` selects
the self-dual coordinate `2 Re c - 1`. -/
theorem sourceCayleyTransverseRate_eq_neg_reflectedLeastAtomEntropy
    {q : ℝ} (hq : 1 < q) (c rho : ℂ) :
    sourceCayleyTransverseRate c rho =
      -(leastAtomTransferEntropy q (2 * c.re - 1) rho -
        leastAtomTransferEntropy q (2 * c.re - 1)
          (leastAtomSourceReflection (2 * c.re - 1) rho)) := by
  rw [leastAtomTransferEntropy_reflectionDifference hq]
  simp only [sourceCayleyTransverseRate, sub_re]
  ring

/-- The horizontal centered affine charge is minus one half of the
source-Cayley escape rate, weighted by multiplicity. -/
theorem centeredCayleyAffineCharge_real_eq_sourceCayleyRate
    (c rho : ℂ) (m : ℕ) :
    (-((rho - ((((2 * c.re - 1) / 2 : ℝ)) : ℂ)) *
          (m : ℂ))).re =
      -(m : ℝ) / 2 * sourceCayleyTransverseRate c rho := by
  simp only [neg_re, mul_re, sub_re, ofReal_re,
    sourceCayleyTransverseRate]
  norm_num
  ring

/-- **Entropy form of source-horizon conservation.**  At canonical
observation time, the exponential tilt of every transported residue
packet is the negative reflected least-atom entropy jump.  This exact
form is independent of atom scale. -/
theorem sourceCayleyResidueMode_horizonConservation_entropy
    {q : ℝ} (hq : 1 < q)
    (m c rho : ℂ) (tau : ℝ) (r : ℕ) (hrho : rho ≠ c) :
    let x := sourceCayleyObservationTime c rho tau
    x ^ r / r.factorial *
        ‖iteratedDeriv r
          (cayleyPoleResidueMode m c rho) (x : ℂ)‖ ^ 2 =
      ‖m‖ ^ 2 *
        Real.exp
          (-(leastAtomTransferEntropy q (2 * c.re - 1) rho -
              leastAtomTransferEntropy q (2 * c.re - 1)
                (leastAtomSourceReflection (2 * c.re - 1) rho)) *
            tau) *
          poissonOrderWeight tau r := by
  dsimp only
  rw [sourceCayleyResidueMode_horizon_conservation
    m c rho tau r hrho]
  rw [sourceCayleyTransverseRate_eq_neg_reflectedLeastAtomEntropy
    hq c rho]

end

end GaloisForLFunctions.HTGeometry
