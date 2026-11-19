import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering

/-!
# The scattering coefficient determined by the KP residual

Shi (arXiv:2611.22194, Lemma 2.2 and Theorem 6.2(a)) identifies the
two-soliton phase by evaluating the symbol on the sum and difference
of the momenta. Here the division-free test is obtained from the
differential residual of the existing KP jet. A transverse slope mismatch
can make normalization impossible. At a common slope the phase is exactly
the two-point Cauchy coherence determinant.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE
open HilbertMetric.CauchyDephasing

/-- Unit constant coefficient, with independently chosen interaction amplitude. -/
def scatteringJet (δ ρ A k v s l w t : ℝ) : RealEvolutionJetKP :=
  mondalTwoExponentialTauJet 1 A
    (mondalFrequency δ ρ k v) k (k*v) s (mondalFrequency δ ρ l w) l (l*w) t

/-- The two interaction channels differ by the sign of the second momentum. -/
def pairSymbol (δ ρ k l v w : ℝ) : ℝ := 3*δ*(k+l)^2 - ρ*(v-w)^2

/-- The residual has a single exponential and an affine dependence on the amplitude. -/
theorem scattering_residual (δ ρ A k v s l w t τ x y : ℝ) :
    hirotaKPResidual δ ρ (scatteringJet δ ρ A k v s l w t) τ x y =
      2*k*l * mondalExpWave (mondalFrequency δ ρ k v) k (k*v) s τ x y *
        mondalExpWave (mondalFrequency δ ρ l w) l (l*w) t τ x y *
        (A * pairSymbol δ ρ k l v w - pairSymbol δ ρ k (-l) v w) := by
  rw [scatteringJet, mondalTwoExponentialTau_hirotaResidual, mondalExpWave_add]
  simp only [mondalCorrectFrequency_symbol_zero, mul_zero, add_zero, zero_add]
  unfold mondalHirotaSymbol mondalFrequency pairSymbol
  ring

/-- Exact solution locus, including zero momenta and singular dispersion parameters. -/
theorem scattering_solves_iff (δ ρ A k v s l w t : ℝ) :
    SolvesHirotaKP δ ρ (scatteringJet δ ρ A k v s l w t) ↔
      k = 0 ∨ l = 0 ∨ A * pairSymbol δ ρ k l v w = pairSymbol δ ρ k (-l) v w := by
  have h (τ x y : ℝ) : hirotaKPResidual δ ρ (scatteringJet δ ρ A k v s l w t) τ x y = 0 ↔
      k = 0 ∨ l = 0 ∨ A * pairSymbol δ ρ k l v w = pairSymbol δ ρ k (-l) v w := by
    rw [scattering_residual]
    simp only [mul_eq_zero, mondalExpWave, Real.exp_ne_zero, or_false, sub_eq_zero,
      or_assoc, OfNat.ofNat_ne_zero, false_or]
  exact ⟨fun hs => (h 0 0 0).mp (hs 0 0 0), fun hs τ x y => (h τ x y).mpr hs⟩

/-- Positive momenta and nonzero dispersion make a pole of the phase a genuine
obstruction to a tau with constant coefficient one. -/
theorem scattering_exists_iff (ρ a v s b w t : ℝ) :
    (∃ A, SolvesHirotaKP 1 ρ (scatteringJet 1 ρ A (Real.exp a) v s (Real.exp b) w t)) ↔
      pairSymbol 1 ρ (Real.exp a) (Real.exp b) v w ≠ 0 := by
  simp only [scattering_solves_iff, Real.exp_ne_zero, false_or]
  constructor
  · rintro ⟨A, h⟩ hz
    rw [hz, mul_zero] at h
    have hd : pairSymbol 1 ρ (Real.exp a) (Real.exp b) v w -
        pairSymbol 1 ρ (Real.exp a) (-(Real.exp b)) v w =
        12 * Real.exp a * Real.exp b := by unfold pairSymbol; ring
    rw [hz, ← h, sub_self] at hd
    exact (ne_of_gt (by positivity : 0 < 12 * Real.exp a * Real.exp b)) hd.symm
  · intro h
    exact ⟨_, div_mul_cancel₀ _ h⟩

/-- The deformation by transverse separation disappears on each common-slope
cubic graph. The normalized solution determines its Cauchy coherence loss uniquely. -/
theorem common_slope_solves_iff (ρ a b v s t A : ℝ) :
    SolvesHirotaKP 1 ρ (scatteringJet 1 ρ A (Real.exp a) v s (Real.exp b) v t) ↔
      A = 1 - coherence a b ^ 2 := by
  rw [scattering_solves_iff, ← contrast_sq_eq_coherence_loss]
  simp only [Real.exp_ne_zero, false_or, pairSymbol, sub_self, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, sub_zero, mul_one, ← sub_eq_add_neg, contrast, div_pow]
  have hd : Real.exp a + Real.exp b ≠ 0 := (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  rw [eq_div_iff (pow_ne_zero _ hd)]
  constructor <;> intro h <;> linarith only [show A*(3*(Real.exp a+Real.exp b)^2) =
    3*(A*(Real.exp a+Real.exp b)^2) by ring, h]

/-- The shared-slope tau function is strictly positive, even at coincident momenta. -/
theorem common_slope_tau_positive (ρ a b v s t τ x y : ℝ) :
    0 < (scatteringJet 1 ρ (1 - coherence a b ^ 2) (Real.exp a) v s (Real.exp b) v t).u τ x y := by
  rw [← contrast_sq_eq_coherence_loss]
  have wave (ω k l h : ℝ) : (mondalExpWaveJet ω k l h).u τ x y =
      mondalExpWave ω k l h τ x y := by
    change 1 + _ + (-1) = _
    ring
  simp only [scatteringJet,mondalTwoExponentialTauJet,realEvolutionJetKPAdd,
    realEvolutionJetKPScale,realEvolutionJetKPConst,wave,mondalExpWave]
  positivity

end GaloisForLFunctions.HTGeometry.DispersivePDE
