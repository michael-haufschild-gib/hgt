import GaloisForLFunctions.RHTower.XiMassJetFourierIdentity
import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderSymmetry

/-!
# Conjugation reduction for the jet-modified atom series

The jet multiplier is a real polynomial on the source axis and is even there, so reflecting the
vertical time is exactly complex conjugation for the modified receiver, for its prime-log atoms and
for the whole atom series.  One vertical half-line therefore carries all the information.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

theorem conj_jetPow_ofReal (a : ℝ) (k : ℕ) (x : ℝ) :
    conj (((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k) = ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) ^ k := by
  have hcast : ((x : ℂ) ^ 2 + 4 * (a : ℂ) ^ 4) = ((x ^ 2 + 4 * a ^ 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_pow, Complex.conj_ofReal]

/-- Conjugating vertical time reflects its sign in the real-axis jet test. -/
theorem conj_xiMassJetAnalyticTest_ofReal {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (sigma u x : ℝ) :
    conj (xiMassJetAnalyticTest a N ((sigma : ℂ) + (u : ℂ) * I) (x : ℂ)) =
      xiMassJetAnalyticTest a N ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) (x : ℂ) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  rw [xiMassJetAnalyticTest_eq_pow ha, xiMassJetAnalyticTest_eq_pow ha, map_mul,
    conj_jetPow_ofReal a (2 * N) x, conj_xiMassAnalyticTest_ofReal ha0]

/-- The jet test is even on the source axis. -/
theorem xiMassJetAnalyticTest_neg {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (τ z : ℂ) :
    xiMassJetAnalyticTest a N τ (-z) = xiMassJetAnalyticTest a N τ z := by
  rw [xiMassJetAnalyticTest_eq_pow ha, xiMassJetAnalyticTest_eq_pow ha, neg_pow,
    xiMassAnalyticTest_neg]
  norm_num

/-- **The modified strip Fourier integral at reflected vertical time is the conjugate.** -/
theorem conj_stripFourier_xiMassJetAnalyticTest {a : ℝ} (ha : 1 / 2 < a) (N : ℕ)
    (sigma u h : ℝ) :
    conj (stripFourier
      (xiMassJetAnalyticTest a N ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)) =
      stripFourier
        (xiMassJetAnalyticTest a N ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I)) (h : ℂ) := by
  rw [stripFourier, ← integral_conj, stripFourier]
  have href := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ =>
      xiMassJetAnalyticTest a N ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) x *
        Complex.exp (-(I * (h : ℂ) * x))) volume
  calc
    (∫ x : ℝ, conj
        (xiMassJetAnalyticTest a N ((sigma : ℂ) + (u : ℂ) * I) x *
          Complex.exp (-(I * (h : ℂ) * x)))) =
        ∫ x : ℝ,
          xiMassJetAnalyticTest a N ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) (-x) *
            Complex.exp (-(I * (h : ℂ) * (-x))) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [map_mul, conj_xiMassJetAnalyticTest_ofReal ha, ← Complex.exp_conj]
      push_cast
      rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_ofReal, xiMassJetAnalyticTest_neg ha]
      ring_nf
    _ = _ := by simpa only [Complex.ofReal_neg] using href

/-- The filtered centred prime atom at reflected vertical time is the conjugate. -/
theorem conj_xiMassPolyCenteredPrimeAtom_jet {a : ℝ} (ha : 1 / 2 < a) (N : ℕ)
    (sigma u : ℝ) (n : ℕ) :
    conj (xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
        ((sigma : ℂ) + (u : ℂ) * I) n)
      = xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) n := by
  have htest : ∀ v : ℝ, xiMassPolyAnalyticTest (xiMassJetPoly a N) a
      ((sigma : ℂ) + (v : ℂ) * I) = xiMassJetAnalyticTest a N ((sigma : ℂ) + (v : ℂ) * I) := by
    intro v
    funext z
    exact (xiMassJetAnalyticTest_eq_poly ha N _ z).symm
  rw [xiMassPolyCenteredPrimeAtom, xiMassPolyCenteredPrimeAtom, htest, htest, map_mul,
    conj_stripFourier_xiMassJetAnalyticTest ha N]
  congr 1
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, if_neg hn]
    have hreal : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ (1 / 2 : ℂ)
        = (((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n : ℝ))]
      norm_num
    rw [hreal, Complex.conj_ofReal]

/-- **One vertical half-line suffices.**  The jet atom series at reflected vertical time has the
same modulus. -/
theorem norm_tsum_xiMassPolyCenteredPrimeAtom_jet_neg {a : ℝ} (ha : 1 / 2 < a)
    {sigma u : ℝ} (N : ℕ) :
    ‖∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
        ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) n‖
      = ‖∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((sigma : ℂ) + (u : ℂ) * I) n‖ := by
  have hconj : (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
      ((sigma : ℂ) + ((-u : ℝ) : ℂ) * I) n)
      = conj (∑' n : ℕ, xiMassPolyCenteredPrimeAtom (xiMassJetPoly a N) a
          ((sigma : ℂ) + (u : ℂ) * I) n) := by
    rw [Complex.conj_tsum]
    exact (tsum_congr fun n => (conj_xiMassPolyCenteredPrimeAtom_jet ha N sigma u n)).symm
  rw [hconj, RCLike.norm_conj]

end

end RHTower
