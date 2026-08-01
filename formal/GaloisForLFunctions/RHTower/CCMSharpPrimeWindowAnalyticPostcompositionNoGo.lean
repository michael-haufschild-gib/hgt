import GaloisForLFunctions.HTGeometry.DirichletAnalyticPostcompositionSignRigidity
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPassiveNoGo

/-!
# Analytic scalar postcomposition no-go for the sharp dyadic prime source

Every nonconstant analytic scalar germ that is real on a real neighborhood of the limiting
constant coefficient still takes both imaginary signs arbitrarily high after postcomposition with
Route I's literal impedance. Thus no such local scalar repair can be Herglotz or anti-Herglotz on
an upper tail. The proof is unconditional and uses only the first nonconstant Dirichlet coefficient.
-/

open Complex Filter Real LSeries Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-- General positive-line impedance identity at horizontal offset `tau`. -/
theorem dyadicSharpPrimeImpedance_posLine_general (tau x : ℝ) :
    dyadicSharpPrimeImpedance
        ((tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) - (tau : ℂ) * Complex.I) := by
  rw [dyadicSharpPrimeImpedance]
  congr 1
  rw [mul_add]
  have hmid : Complex.I * (((x - 1 : ℝ) : ℂ) * Complex.I) =
      ((x - 1 : ℝ) : ℂ) * (Complex.I * Complex.I) := by ring
  rw [hmid, Complex.I_mul_I]
  push_cast
  ring

/-- General negative-line impedance identity at horizontal offset `-tau`. -/
theorem dyadicSharpPrimeImpedance_negLine_general (tau x : ℝ) :
    dyadicSharpPrimeImpedance
        ((-tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
      dyadicSharpPrimeContinuedSource ((x : ℂ) + (tau : ℂ) * Complex.I) := by
  rw [dyadicSharpPrimeImpedance]
  congr 1
  rw [mul_add]
  have hmid : Complex.I * (((x - 1 : ℝ) : ℂ) * Complex.I) =
      ((x - 1 : ℝ) : ℂ) * (Complex.I * Complex.I) := by ring
  rw [hmid, Complex.I_mul_I]
  push_cast
  ring

/-- The first nonconstant real sharp-window source coefficient is nonzero. -/
theorem dyadicSharpPrimeSourceCoefficient_two_ne_zero :
    dyadicSharpPrimeSourceCoefficient 2 ≠ 0 := by
  intro hzero
  have hpos := dyadicSharpPrimeSourceComplexCoeff_two_pos
  simp [dyadicSharpPrimeSourceComplexCoeff, hzero] at hpos

/-- **Full analytic scalar-germ no-go.** Every nonconstant analytic postcomposition that is real
on a real neighborhood of the limiting constant coefficient takes both imaginary signs above
every prescribed impedance height. -/
theorem exists_high_dyadicSharpPrimeImpedance_analyticPostcomp_both_signs
    {Phi : ℂ → ℂ}
    (hPhi : AnalyticAt ℂ Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (hreal : ∀ᶠ x : ℝ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1),
      (Phi (x : ℂ)).im = 0)
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1 : ℂ),
      Phi z = Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (Y : ℝ) :
    (∃ z : ℂ, Y < z.im ∧ 0 < (Phi (dyadicSharpPrimeImpedance z)).im) ∧
      (∃ z : ℂ, Y < z.im ∧ (Phi (dyadicSharpPrimeImpedance z)).im < 0) := by
  have habscissa :
      LSeries.abscissaOfAbsConv
          (fun m => ((dyadicSharpPrimeSourceCoefficient m : ℝ) : ℂ)) < ⊤ := by
    simpa [dyadicSharpPrimeSourceComplexCoeff] using
      dyadicSharpPrimeSourceComplexCoeff_abscissa_lt_top
  have hzero : ∀ m : ℕ, 2 ≤ m → m ≤ 1 → dyadicSharpPrimeSourceCoefficient m = 0 := by
    omega
  have hsigns := realLSeriesPostcomp_hasOppositeHighLineSigns_of_eventually_real
    (f := dyadicSharpPrimeSourceCoefficient) 1 (by omega) habscissa hzero
      dyadicSharpPrimeSourceCoefficient_two_ne_zero hPhi hreal hnonconst
  rcases hsigns with ⟨tau, htau, horient⟩
  have hsourceMinus {x : ℝ} (hx : 3 / 2 < x) :
      LSeries (fun m => ((dyadicSharpPrimeSourceCoefficient m : ℝ) : ℂ))
          ((x : ℂ) - (tau : ℂ) * Complex.I) =
        dyadicSharpPrimeContinuedSource ((x : ℂ) - (tau : ℂ) * Complex.I) := by
    apply LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource
    simpa using hx
  have hsourcePlus {x : ℝ} (hx : 3 / 2 < x) :
      LSeries (fun m => ((dyadicSharpPrimeSourceCoefficient m : ℝ) : ℂ))
          ((x : ℂ) + (tau : ℂ) * Complex.I) =
        dyadicSharpPrimeContinuedSource ((x : ℂ) + (tau : ℂ) * Complex.I) := by
    apply LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource
    simpa using hx
  rcases horient with ⟨hminusPos, hplusNeg⟩ | ⟨hminusNeg, hplusPos⟩
  · constructor
    · have hevent := hminusPos.and (eventually_gt_atTop (Y + 1)) |>.and
        (eventually_gt_atTop (3 / 2 : ℝ))
      obtain ⟨x, ⟨hpos, hheight⟩, hx⟩ := hevent.exists
      refine ⟨(tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_add, mul_one,
          zero_mul, add_zero]
        linarith
      · rw [dyadicSharpPrimeImpedance_posLine_general]
        rw [← hsourceMinus hx]
        exact hpos
    · have hevent := hplusNeg.and (eventually_gt_atTop (Y + 1)) |>.and
        (eventually_gt_atTop (3 / 2 : ℝ))
      obtain ⟨x, ⟨hneg, hheight⟩, hx⟩ := hevent.exists
      refine ⟨(-tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
      · simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
          zero_add, mul_one, zero_mul, add_zero]
        linarith
      · rw [dyadicSharpPrimeImpedance_negLine_general]
        rw [← hsourcePlus hx]
        exact hneg
  · constructor
    · have hevent := hplusPos.and (eventually_gt_atTop (Y + 1)) |>.and
        (eventually_gt_atTop (3 / 2 : ℝ))
      obtain ⟨x, ⟨hpos, hheight⟩, hx⟩ := hevent.exists
      refine ⟨(-tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
      · simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
          zero_add, mul_one, zero_mul, add_zero]
        linarith
      · rw [dyadicSharpPrimeImpedance_negLine_general]
        rw [← hsourcePlus hx]
        exact hpos
    · have hevent := hminusNeg.and (eventually_gt_atTop (Y + 1)) |>.and
        (eventually_gt_atTop (3 / 2 : ℝ))
      obtain ⟨x, ⟨hneg, hheight⟩, hx⟩ := hevent.exists
      refine ⟨(tau : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_add, mul_one,
          zero_mul, add_zero]
        linarith
      · rw [dyadicSharpPrimeImpedance_posLine_general]
        rw [← hsourceMinus hx]
        exact hneg

/-- No nonconstant analytic scalar germ real on the local real axis makes the sharp-window
impedance upper-half-plane valued on an upper tail. -/
theorem dyadicSharpPrimeImpedance_analyticPostcomp_not_upperHalfPlaneValued_above
    {Phi : ℂ → ℂ}
    (hPhi : AnalyticAt ℂ Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (hreal : ∀ᶠ x : ℝ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1),
      (Phi (x : ℂ)).im = 0)
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1 : ℂ),
      Phi z = Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im → 0 ≤ (Phi (dyadicSharpPrimeImpedance z)).im) := by
  intro hupper
  obtain ⟨_, z, hz, hneg⟩ :=
    exists_high_dyadicSharpPrimeImpedance_analyticPostcomp_both_signs
      hPhi hreal hnonconst Y
  exact hneg.not_ge (hupper z hz)

/-- No nonconstant analytic scalar germ real on the local real axis makes the sharp-window
impedance lower-half-plane valued on an upper tail. -/
theorem dyadicSharpPrimeImpedance_analyticPostcomp_not_lowerHalfPlaneValued_above
    {Phi : ℂ → ℂ}
    (hPhi : AnalyticAt ℂ Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (hreal : ∀ᶠ x : ℝ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1),
      (Phi (x : ℂ)).im = 0)
    (hnonconst : ¬ ∀ᶠ z : ℂ in 𝓝 (dyadicSharpPrimeSourceCoefficient 1 : ℂ),
      Phi z = Phi (dyadicSharpPrimeSourceCoefficient 1 : ℂ))
    (Y : ℝ) :
    ¬ (∀ z : ℂ, Y < z.im → (Phi (dyadicSharpPrimeImpedance z)).im ≤ 0) := by
  intro hlower
  obtain ⟨⟨z, hz, hpos⟩, _⟩ :=
    exists_high_dyadicSharpPrimeImpedance_analyticPostcomp_both_signs
      hPhi hreal hnonconst Y
  exact hpos.not_ge (hlower z hz)

end RHTower
