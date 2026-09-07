import GaloisForLFunctions.RHTower.WeightedScrewPoleContradictionThreshold
import GaloisForLFunctions.RHTower.SuzukiScrewPointwiseNonnegativityCriterion
import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection

/-!
# Sub-exponential one-sided criterion for Suzuki's screw function

Suzuki's screw function `Psi(t) = Σ'_q (1 - cos(z_q t)) / z_q²` over the Xi zero copies is real,
and on the source half-line it equals the explicit smooth part minus the prime hinge sum
`Σ_{2 ≤ n ≤ e^t} Λ(n) n^{-1/2} (t - log n)`.  Feeding the constant weight `W ≡ 1` into the
threshold Widder--Landau engine shows that a one-sided lower bound `Psi(t) ≥ -C₀ exp(ε t)` of
rate `ε < 1/2` confines every Xi zero copy to the strip `|Im z_q| ≤ ε`.  Consequently RH is
equivalent to `Psi` being not exponentially negative at any positive rate, and equivalently to the
one-sided prime-side inequality `hinge sum ≤ smooth part + C_ε exp(ε t)` for every `ε > 0`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The constant weight `1` reproduces the unweighted Xi screw divisor. -/
theorem weightedXiScrewDivisor_one (t : ℝ) :
    weightedXiScrewDivisor (fun _ => (1 : ℂ)) t = xiScrewDivisor t := by
  simp [weightedXiScrewDivisor, xiScrewDivisor]

/-- **Strip law for Suzuki's screw function.**  A one-sided exponential lower bound of rate
`ε < 1/2` on `Psi` over the source half-line confines every Xi zero copy to `|Im z_q| ≤ ε`. -/
theorem abs_im_xiSpectralPoint_le_of_suzukiPsi_ge {C₀ ε : ℝ}
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ suzukiPsi t)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  refine abs_im_le_of_thr (fun _ => (1 : ℂ)) C₀ ε (C := 1) zero_le_one
    (fun _ => by simp) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => one_ne_zero)
    ?_ ?_ hε0 hε q
  · intro t ht
    rw [weightedXiScrewDivisor_one, ← suzukiPsi_eq_xiScrewDivisor_re ht]
    exact hlow t ht
  · intro t
    rw [weightedXiScrewDivisor_one]
    exact xiScrewDivisor_im_eq_zero t

/-- The strip law at every rate `ε ≥ 0`, using the unconditional bound `|Im z_q| < 1/2`. -/
theorem abs_im_xiSpectralPoint_le_of_suzukiPsi_ge' {C₀ ε : ℝ}
    (hlow : ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ suzukiPsi t)
    (hε0 : 0 ≤ ε) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  rcases le_or_gt (1 / 2 : ℝ) ε with hε | hε
  · exact (abs_xiSpectralPoint_im_lt_half q).le.trans hε
  · exact abs_im_xiSpectralPoint_le_of_suzukiPsi_ge hlow hε0 hε q

/-- Suzuki's screw function is not exponentially negative at any positive rate. -/
def SuzukiPsiSubexponentialBelow : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, ∀ t : ℝ, 0 ≤ t → -(C₀ * Real.exp (ε * t)) ≤ suzukiPsi t

/-- **Sub-exponential negativity of Suzuki's screw function implies RH.** -/
theorem riemannHypothesis_of_suzukiPsiSubexponentialBelow
    (h : SuzukiPsiSubexponentialBelow) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have him : (xiSpectralPoint q).im = 0 := by
    have hle : |(xiSpectralPoint q).im| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨C₀, hB⟩ := h ε hε
      have := abs_im_xiSpectralPoint_le_of_suzukiPsi_ge' hB hε.le q
      linarith
    exact abs_nonpos_iff.mp hle
  exact ⟨(xiSpectralPoint q).re, by apply Complex.ext <;> simp [him]⟩

/-- Under RH the screw function is nonnegative, hence trivially sub-exponential below. -/
theorem suzukiPsiSubexponentialBelow_of_riemannHypothesis (hRH : RiemannHypothesis) :
    SuzukiPsiSubexponentialBelow := by
  intro ε _
  refine ⟨0, fun t ht => ?_⟩
  have := suzukiPsiPointwiseNonnegative_of_riemannHypothesis hRH t ht
  simpa using this

/-- **RH is equivalent to sub-exponential negativity of Suzuki's screw function.** -/
theorem riemannHypothesis_iff_suzukiPsiSubexponentialBelow :
    RiemannHypothesis ↔ SuzukiPsiSubexponentialBelow :=
  ⟨suzukiPsiSubexponentialBelow_of_riemannHypothesis,
    riemannHypothesis_of_suzukiPsiSubexponentialBelow⟩

/-- **Prime-side strip law.**  If the prime hinge sum exceeds its explicit smooth part by at
most `C₀ exp(ε t)` on the source half-line, every Xi zero copy satisfies `|Im z_q| ≤ ε`. -/
theorem abs_im_xiSpectralPoint_le_of_screwPrimeSum_le {C₀ ε : ℝ}
    (hle : ∀ t : ℝ, 0 ≤ t →
      GaloisForLFunctions.RHTower.screwPrimeSum t ≤ ccmGuinandWeilXiScrewSmoothPart t + C₀ * Real.exp (ε * t))
    (hε0 : 0 ≤ ε) (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  refine abs_im_xiSpectralPoint_le_of_suzukiPsi_ge' (C₀ := C₀) (ε := ε) ?_ hε0 q
  intro t ht
  rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht]
  linarith [hle t ht]

/-- **RH from one-sided sub-exponential control of the prime hinge sum.**  RH holds if and only
if for every `ε > 0` the hinge sum `Σ_{2 ≤ n ≤ e^t} Λ(n) n^{-1/2} (t - log n)` exceeds its
explicit smooth part by at most `C_ε exp(ε t)` on the source half-line. -/
theorem riemannHypothesis_iff_screwPrimeSum_subexponential :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, ∀ t : ℝ, 0 ≤ t →
      GaloisForLFunctions.RHTower.screwPrimeSum t ≤ ccmGuinandWeilXiScrewSmoothPart t + C₀ * Real.exp (ε * t) := by
  rw [riemannHypothesis_iff_suzukiPsiSubexponentialBelow]
  constructor
  · intro h ε hε
    obtain ⟨C₀, hB⟩ := h ε hε
    refine ⟨C₀, fun t ht => ?_⟩
    have := hB t ht
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht] at this
    linarith
  · intro h ε hε
    obtain ⟨C₀, hB⟩ := h ε hε
    refine ⟨C₀, fun t ht => ?_⟩
    rw [suzukiPsi_eq_smoothPart_sub_screwPrimeSum ht]
    linarith [hB t ht]

end

end RHTower
