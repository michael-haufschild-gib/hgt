import GaloisForLFunctions.RHTower.XiMassFaithfulTransfer
import GaloisForLFunctions.RHTower.XiMassCausticNullJet
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.HTGeometry.PolynomialSpectralWeight

/-!
# The jet-modified trace is an exact criterion

The caustic-null jet `P_N(w) = (w² + Ω_B²)^{2N}` is a polynomial without a zero in the open right
half plane, hence a spectral weight.  Weighting the mass-shifted trace by it therefore changes
nothing about what a bounded vertical line certifies: the modified trace is bounded on one vertical
line exactly when the mass-shifted divisor is real, which is exactly the Riemann hypothesis.

This is the spectral half of the caustic-null jet hierarchy: no coefficient of the trace is
destroyed, and the shell argument that reads reality off a bounded line survives the weight because
phase-robust dominance only needs the regrouped shell coefficients to have positive moduli.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The caustic-null jet is a spectral weight.**  It is a polynomial of degree `4N` in the
spectral variable and has no zero in the open right half plane. -/
def xiMassCausticJetWeight {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) : HTGeometry.SpectralWeight :=
  HTGeometry.SpectralWeight.ofPolyBound (fun z => xiMassCausticJet a N z)
    ((1 + xiMassCausticFrequency a ^ 2) ^ (2 * N)) (4 * N)
    (fun _ hz => xiMassCausticJet_ne_zero ha N hz)
    (by
      intro z hzim hzre
      have hOm : (0 : ℝ) ≤ xiMassCausticFrequency a ^ 2 := sq_nonneg _
      have hz : ‖z‖ ≤ 1 + z.re := by
        have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        have h2 : |z.re| = z.re := abs_of_nonneg hzre
        rw [h2] at h1
        linarith
      have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have hrnn : (0 : ℝ) ≤ 1 + z.re := by linarith
      have hbase : ‖z ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2‖
          ≤ (1 + xiMassCausticFrequency a ^ 2) * (1 + z.re) ^ 2 := by
        have hsplit : ‖z ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2‖
            ≤ ‖z‖ ^ 2 + xiMassCausticFrequency a ^ 2 := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        refine hsplit.trans ?_
        have hsq : ‖z‖ ^ 2 ≤ (1 + z.re) ^ 2 := by nlinarith
        have hge1 : (1 : ℝ) ≤ (1 + z.re) ^ 2 := by nlinarith
        have hOmstep : xiMassCausticFrequency a ^ 2 * 1
            ≤ xiMassCausticFrequency a ^ 2 * (1 + z.re) ^ 2 :=
          mul_le_mul_of_nonneg_left hge1 hOm
        nlinarith [hsq, hOmstep]
      have hstep : ‖z ^ 2 + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2‖ ^ (2 * N)
          ≤ ((1 + xiMassCausticFrequency a ^ 2) * (1 + z.re) ^ 2) ^ (2 * N) :=
        pow_le_pow_left₀ (norm_nonneg _) hbase _
      rw [xiMassCausticJet, norm_pow]
      refine hstep.trans (le_of_eq ?_)
      rw [mul_pow, ← pow_mul]
      congr 2
      ring)

theorem xiMassCausticJetWeight_toFun {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (z : ℂ) :
    (xiMassCausticJetWeight ha N).toFun z = xiMassCausticJet a N z := rfl

/-- **(22.5) The jet-modified mass trace is an exact criterion for the Riemann hypothesis.**
For every mass above one half and every jet order, RH is equivalent to boundedness of the
jet-weighted mass-shifted trace on one vertical line of the open right half plane. -/
theorem riemannHypothesis_iff_exists_xiMassCausticJetTrace_line_bound {a : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) :
    RiemannHypothesis ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ,
        ‖(xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N)
          ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  have hiff : ∀ q : XiZeroCopy,
      ((xiMassFamily ha.le).pt q).im = 0 ↔ (xiPoissonPoint q).im = 0 := by
    intro q
    rw [xiMassFamily_pt_eq_mass_pt ha.le q]
    exact xiPoissonAbstract.mass_im_eq_zero_iff ha.le q
  constructor
  · intro hRH
    exact ((xiMassFamily ha.le).im_eq_zero_iff_exists_weightedLine_bound
      (xiMassCausticJetWeight ha N)).mp fun q =>
        (hiff q).mpr (xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · rintro ⟨σ, C, hσ, hline⟩
    have hall := (xiMassFamily ha.le).im_eq_zero_of_weightedLine_bound_all
      (xiMassCausticJetWeight ha N) hσ hline
    exact riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero fun q => (hiff q).mp (hall q))

end

end RHTower
