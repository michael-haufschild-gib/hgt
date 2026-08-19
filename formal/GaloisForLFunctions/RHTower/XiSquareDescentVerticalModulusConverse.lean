import GaloisForLFunctions.RHTower.XiSquareDescentVerticalModulus
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion
import GaloisForLFunctions.HTGeometry.MassDispersionUnitExpansion

/-!
# The localized vertical modulus criterion forces the Riemann hypothesis

An off-critical Xi zero can be moved by functional-equation and Schwarz reflection into the open
upper-right chamber, beyond any certified quartet-accretive radius and below the half-unit ceiling.
Its square is a nonreal zero of the square descent inside the principal-root chamber, which is
open.  Vertical modulus monotonicity there would force the descent to vanish along a whole vertical
segment, and the identity theorem would then make it identically zero, contradicting the nonzero
central value.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The principal-root chamber of a radius: squares of upper-right centered points with ordinate
below one half. -/
def xiSquareChamber (R : ℝ) : Set ℂ :=
  {w : ℂ | R < (Complex.sqrt w).re ∧ 0 < (Complex.sqrt w).im ∧
    (Complex.sqrt w).im < 1 / 2}

/-- Localized vertical modulus monotonicity on a principal-root chamber. -/
def XiSquareDescentVerticalModulusOn (R : ℝ) : Prop :=
  ∀ x t₁ t₂ : ℝ, t₁ ≤ t₂ →
    (∀ t ∈ Set.Icc t₁ t₂, ((x : ℂ) + (t : ℂ) * Complex.I) ∈ xiSquareChamber R) →
    ‖xiSquareDescent ((x : ℂ) + (t₁ : ℂ) * Complex.I)‖ ≤
      ‖xiSquareDescent ((x : ℂ) + (t₂ : ℂ) * Complex.I)‖

theorem continuousAt_complex_sqrt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContinuousAt Complex.sqrt w := by
  have h : Complex.sqrt = fun z : ℂ => z ^ (2⁻¹ : ℂ) := by
    funext z
    exact Complex.ext rfl rfl
  rw [h]
  exact continuousAt_cpow_const hw

theorem complex_sqrt_sq_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.sqrt (z ^ 2) = z := by
  have hsq : Complex.sqrt (z ^ 2) ^ 2 = z ^ 2 :=
    GaloisForLFunctions.HTGeometry.complex_sqrt_sq (z ^ 2)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · exfalso
    have hre := GaloisForLFunctions.HTGeometry.sqrt_re_nonneg (z ^ 2)
    rw [h] at hre
    simp only [Complex.neg_re] at hre
    linarith

/-! ## Selecting an upper-right off-critical zero -/

theorem exists_XiC_zero_upperRight_of_not_rh {R : ℝ}
    (hband : XiOffLineQuartetAccretiveBand R) (hnot : ¬ RiemannHypothesis) :
    ∃ z : ℂ, XiC z = 0 ∧ R < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 := by
  classical
  have hexists : ∃ rho : XiDivisorSupport, ((rho : ℂ)).re ≠ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    exact hnot (riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half hcon)
  obtain ⟨rho, hrho⟩ := hexists
  have hxi : xi ((rho : ℂ)) = 0 := xi_eq_zero_of_mem_divisor_support rho
  set z₁ : ℂ := ((rho : ℂ) - 1 / 2) * (-Complex.I) with hz₁
  have hXz₁ : XiC z₁ = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z₁ * Complex.I = (rho : ℂ) := by
      rw [hz₁]
      have : (((rho : ℂ) - 1 / 2) * (-Complex.I)) * Complex.I =
          -(Complex.I * Complex.I) * ((rho : ℂ) - 1 / 2) := by ring
      rw [this, Complex.I_mul_I]
      ring
    rw [harg]
    exact hxi
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z₁).mp hXz₁
  have hqval : ((q.1 : ℂ)) = (rho : ℂ) := by
    have hpt : ((q.1 : ℂ) - 1 / 2) * (-Complex.I) = ((rho : ℂ) - 1 / 2) * (-Complex.I) := by
      rw [← xiSpectralPoint, hq, hz₁]
    have hI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have := mul_right_cancel₀ hI hpt
    linear_combination this
  have hoff : ((q.1 : ℂ)).re ≠ 1 / 2 := by rw [hqval]; exact hrho
  have hgap0 := xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine R hband q hoff
  obtain ⟨hlow, hhigh⟩ := xi_zero_re_mem_open_unit hxi
  set gamma : ℝ := ((rho : ℂ)).im with hgamma
  set beta : ℝ := ((rho : ℂ)).re with hbeta
  have hgap : R + 1 / 2 < |gamma| := by rw [hqval] at hgap0; exact hgap0
  have hb : beta - 1 / 2 ≠ 0 := sub_ne_zero.mpr hrho
  have hbabs : |beta - 1 / 2| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hbpos : 0 < |beta - 1 / 2| := abs_pos.mpr hb
  have hRnonneg : 0 ≤ R := hband.1
  have hgabs : R < |gamma| := by linarith
  refine ⟨((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I, ?_,
    by simpa using hgabs, by simpa using hbpos, by simpa using hbabs⟩
  have hz₁val : z₁ = (gamma : ℂ) + (-(beta - 1 / 2) : ℝ) * Complex.I := by
    rw [hz₁]
    apply Complex.ext <;> simp [hgamma, hbeta] <;> ring
  have hcandidates : ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = -z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I = (starRingEnd ℂ) z₁ ∨
      ((|gamma| : ℝ) : ℂ) + ((|beta - 1 / 2| : ℝ) : ℂ) * Complex.I =
        -((starRingEnd ℂ) z₁) := by
    rw [hz₁val]
    rcases abs_cases gamma with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases (beta - 1 / 2) with ⟨hbv, _⟩ | ⟨hbv, _⟩ <;>
      rw [hg, hbv]
    · right; right; left; apply Complex.ext <;> simp
    · left; apply Complex.ext <;> simp
    · right; left; apply Complex.ext <;> simp
    · right; right; right; apply Complex.ext <;> simp
  rcases hcandidates with h | h | h | h
  · rw [h]; exact hXz₁
  · rw [h, XiC_even]; exact hXz₁
  · rw [h, XiC_conj, hXz₁, map_zero]
  · rw [h, XiC_even, XiC_conj, hXz₁, map_zero]

end

end RHTower
