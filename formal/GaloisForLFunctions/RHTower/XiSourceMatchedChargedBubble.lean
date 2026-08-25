import GaloisForLFunctions.RHTower.CompactOpenKolchinWardChargeEscape
import GaloisForLFunctions.RHTower.RouteRResolutionCoreNoetherCharge

/-!
# Xi divisors canonically source-match charged bubbles at infinity

Every hypothetical off-line Xi divisor supplies two intrinsic parameters: its absolute transverse
source rate and its analytic multiplicity.  This file feeds those actual divisor parameters into
the compact-open Ward escape construction.

The result is an exact source-matching law.  The escaping divisor has the same absolute Noether
charge as the original Xi divisor; all holomorphic jets converge back to Xi and bounded Ward
windows lose the defect; nevertheless the boundary retains `8π` per multiplicity and the marked
source mode remains a simple pole.

This is a structural no-go, not an RH proof.  It proves that compactness arguments blind to the
source-marked boundary cannot exclude a charge already present in the actual Xi divisor.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Horizontal bubble parameter canonically extracted from an Xi divisor. -/
def xiDivisorBubbleDisplacement (rho : XiDivisorSupport) : ℝ :=
  |(rho : ℂ).re - 1 / 2|

/-- Every off-line Xi divisor supplies an admissible nonzero escape displacement. -/
theorem xiDivisorBubbleDisplacement_pos_lt_half
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    0 < xiDivisorBubbleDisplacement rho ∧
      xiDivisorBubbleDisplacement rho < 1 / 2 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  constructor
  · exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  · rw [xiDivisorBubbleDisplacement, abs_lt]
    constructor <;> linarith

/-- The canonical escaping quartet has exactly the absolute transverse source rate of `rho`. -/
theorem abs_sourceCayleyTransverseRate_quartetPoint_xiDivisorBubbleDisplacement
    (rho : XiDivisorSupport) (n : ℕ) :
    |sourceCayleyTransverseRate 1
        (quartetPoint (xiDivisorBubbleDisplacement rho)
          (escapingQuartetHeight n))| =
      |sourceCayleyTransverseRate 1 (rho : ℂ)| := by
  rw [sourceCayleyTransverseRate_one_eq_centeredGrade,
    sourceCayleyTransverseRate_one_eq_centeredGrade]
  simp only [quartetPoint, add_re, ofReal_re, mul_re, I_re, I_im,
    ofReal_im, mul_zero, zero_mul, sub_zero]
  norm_num [xiDivisorBubbleDisplacement]
  rw [show 2 * (1 / 2 + |(rho : ℂ).re - 1 / 2|) - 1 =
    2 * |(rho : ℂ).re - 1 / 2| by ring]
  rw [abs_of_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))]
  rw [show 2 * ((rho : ℂ).re) - 1 =
    2 * ((rho : ℂ).re - 1 / 2) by ring]
  simp [abs_mul]

/-- The escaping quartet is source-matched to the absolute Noether charge of `rho`. -/
theorem abs_centeredCharge_quartetPoint_xiDivisorBubbleDisplacement
    (rho : XiDivisorSupport) (n : ℕ) :
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    |(-((quartetPoint (xiDivisorBubbleDisplacement rho)
          (escapingQuartetHeight n) - 1 / 2) * (m : ℂ))).re| =
      |routeRPrimeGammaXiNoetherOrientationCharge rho| := by
  dsimp only
  rw [routeRPrimeGammaXiNoetherOrientationCharge,
    centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate,
    centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate,
    abs_mul, abs_mul,
    abs_sourceCayleyTransverseRate_quartetPoint_xiDivisorBubbleDisplacement]

/-- **Source-matched charged-bubble law.** Every hypothetical off-line Xi divisor canonically
generates a multiplicity-matched sequence whose inserted source mode has the same absolute
Noether charge. Every holomorphic jet returns compact-open to Xi and every bounded Ward window
loses the mode, while the boundary retains exactly one `8π` quantum per Xi multiplicity and the
source mark remains an exact simple pole. -/
theorem offLineXiDivisor_sourceMatchedChargedBubble
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    let a := xiDivisorBubbleDisplacement rho
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    (∀ n,
      |(-((quartetPoint a (escapingQuartetHeight n) - 1 / 2) *
          (m : ℂ))).re| =
        |routeRPrimeGammaXiNoetherOrientationCharge rho|) ∧
    (∀ n,
      multiplicityEscapingQuartetGaugedXi a m n
        (quartetPoint a (escapingQuartetHeight n)) = 0) ∧
    (∀ j, TendstoLocallyUniformly
      (fun n => iteratedDeriv j
        (multiplicityEscapingQuartetGaugedXi a m n))
      (iteratedDeriv j xi) atTop) ∧
    (∀ R, 0 ≤ R → TendstoUniformlyOn
      (fun n => multiplicityEscapingQuartetWardDensity a m n)
      (fun _ : ℝ => 0) atTop {t : ℝ | |t| ≤ R}) ∧
    (∀ n, multiplicityEscapingQuartetWardMass a m n =
      m • ENNReal.ofReal (8 * π)) ∧
    (∀ n, meromorphicOrderAt
      (logDeriv (multiplicityEscapingQuartetGauge a m n))
      (quartetPoint a (escapingQuartetHeight n)) =
        ((-1 : ℤ) : WithTop ℤ)) := by
  dsimp only
  have ha := xiDivisorBubbleDisplacement_pos_lt_half rho hoff
  have hm : 0 < (analyticOrderAt xi (rho : ℂ)).toNat :=
    Nat.pos_of_ne_zero
      (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho))
  have hescape := unboundedCompactOpenKolchinWardChargeEscape_law
    ha.1 ha.2 (analyticOrderAt xi (rho : ℂ)).toNat hm
  exact ⟨
    abs_centeredCharge_quartetPoint_xiDivisorBubbleDisplacement rho,
    fun n => (hescape.2.2.2.2.1 n).2,
    hescape.2.2.2.2.2.1,
    hescape.2.2.2.2.2.2.1,
    hescape.2.2.2.2.2.2.2.1,
    hescape.2.2.2.2.2.2.2.2⟩

end

end RHTower
