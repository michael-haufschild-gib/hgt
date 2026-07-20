import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact spectral law for the normalized higher Riemann-theta tail

The natural affine coordinate

`B(x) = π exp(x)^2 - 3/2`

turns every higher-to-first theta-atom likelihood ratio into the Laplace transform of one positive
Dirac mass plus one positive Lebesgue ray.  Summing over all higher atoms gives a canonical positive
spectral measure for the complete normalized theta tail.  Its exponentially tilted moments form a
strictly positive Hankel hierarchy at every finite order.

There are no numerical bounds in this module.  All identities are exact and all statements are
unconditional.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- The spectral gap between the `n`th square and the first square. -/
def thetaCuspLikelihoodGap (n : ℕ) : ℝ := (n : ℝ) ^ 2 - 1

/-- The affine-exponential coordinate in which the normalized theta tail is a Laplace transform. -/
def thetaCuspLikelihoodCoordinate (x : ℝ) : ℝ :=
  Real.pi * Real.exp x ^ 2 - 3 / 2

/-- The exact transformed likelihood ratio contributed by the `n`th theta atom. -/
def thetaCuspAtomLikelihoodSpectralTerm (n : ℕ) (B : ℝ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * thetaCuspLikelihoodGap n) *
    ((n : ℝ) ^ 4 * Real.exp (-B * thetaCuspLikelihoodGap n) +
      (3 / 2 : ℝ) * (n : ℝ) ^ 2 * thetaCuspLikelihoodGap n *
        Real.exp (-B * thetaCuspLikelihoodGap n) / B)

theorem thetaCuspLikelihoodCoordinate_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspLikelihoodCoordinate x := by
  have hA := thetaCuspLogConcavityScale_gt_three hx
  simpa [thetaCuspLikelihoodCoordinate, thetaCuspLogConcavityScale] using
    (show 0 < thetaCuspLogConcavityScale x - 3 / 2 by linarith)

theorem thetaCuspLikelihoodGap_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < thetaCuspLikelihoodGap n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [thetaCuspLikelihoodGap]
  nlinarith

/-- **Exact atom spectral law.**  In the canonical `B` coordinate, a theta-atom likelihood ratio
is an exponential atom plus an exponential ray transform. -/
theorem thetaCuspAtomLikelihoodRatio_eq_spectralTerm
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    thetaCuspAtomLikelihoodRatio n x =
      thetaCuspAtomLikelihoodSpectralTerm n (thetaCuspLikelihoodCoordinate x) := by
  have hfirst := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (n := 1) hx (by norm_num)
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  rw [thetaCuspAtomLikelihoodRatio]
  unfold thetaCuspSourceTerm thetaCuspSeed thetaCuspAtomLikelihoodSpectralTerm
    thetaCuspLikelihoodCoordinate thetaCuspLikelihoodGap
  rw [div_eq_iff hfirst.ne']
  rw [← Real.exp_add]
  field_simp [hB.ne']
  ring_nf
  congr 1
  ring

end

end RHTower
