import GaloisForLFunctions.HTGeometry.AbstractSpectralVerticalHyperbolicPair
import GaloisForLFunctions.RHTower.XiMassShiftedFamily

/-!
# Line-conjugate pairing does not reduce the mass-Xi vertical exponential type

This module specializes the abstract hyperbolic-pair law to the mass-shifted Xi family.  It closes a
natural escape route from the exact absolute entropy wall: pairing a zero copy with its
critical-line conjugate before taking a norm does not create an exponentially smaller object.

For every mass-shifted point with positive displacement, the paired norm divided by the dominant
arm tends to one along positive vertical frequency.  Thus any cancellation capable of paying the
critical corona entropy must couple more than one line-conjugate orbit or retain arithmetic phase
information from the literal prime source.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Exact cosine factorization of a mass-Xi point and its critical-line conjugate. -/
theorem xiMassTerm_add_lineConj_eq_two_exp_mul_cos
    {a : ℝ} (ha : 1 / 2 ≤ a) (τ : ℂ) (q : XiZeroCopy) :
    (xiMassFamily ha).term τ q +
        (xiMassFamily ha).term τ (xiZeroCopyLineConjEquiv q) =
      2 * Complex.exp (-τ * (((xiMassFamily ha).pt q).re : ℂ)) *
        Complex.cos (τ * (((xiMassFamily ha).pt q).im : ℂ)) := by
  exact (xiMassFamily ha).term_add_inv_eq_two_exp_mul_cos τ q

/-- Quantitative no-go: normalized Xi line-conjugate pairing can save at most the exponentially
small ratio of the opposite arm. -/
theorem abs_norm_xiMassTerm_add_lineConj_div_dominant_sub_one_le
    {a : ℝ} (ha : 1 / 2 ≤ a) (σ u : ℝ) (q : XiZeroCopy) :
    |‖(xiMassFamily ha).term ((σ : ℂ) + (u : ℂ) * I) q +
          (xiMassFamily ha).term ((σ : ℂ) + (u : ℂ) * I)
            (xiZeroCopyLineConjEquiv q)‖ /
        Real.exp (-σ * ((xiMassFamily ha).pt q).re +
          u * ((xiMassFamily ha).pt q).im) - 1| ≤
      Real.exp (-2 * (u * ((xiMassFamily ha).pt q).im)) := by
  exact (xiMassFamily ha).abs_norm_term_add_inv_div_dominant_sub_one_le σ u q

/-- **Mass-Xi line-conjugate cancellation no-go.**  An upper-half-plane mass point and its line
conjugate have paired norm asymptotic to the growing arm itself. -/
theorem tendsto_norm_xiMassTerm_add_lineConj_div_dominant_atTop_one
    {a : ℝ} (ha : 1 / 2 ≤ a) (σ : ℝ) (q : XiZeroCopy)
    (hq : 0 < ((xiMassFamily ha).pt q).im) :
    Tendsto
      (fun u : ℝ =>
        ‖(xiMassFamily ha).term ((σ : ℂ) + (u : ℂ) * I) q +
            (xiMassFamily ha).term ((σ : ℂ) + (u : ℂ) * I)
              (xiZeroCopyLineConjEquiv q)‖ /
          Real.exp (-σ * ((xiMassFamily ha).pt q).re +
            u * ((xiMassFamily ha).pt q).im))
      atTop (nhds 1) := by
  exact (xiMassFamily ha).tendsto_norm_term_add_inv_div_dominant_atTop_one σ q hq

end

end RHTower
