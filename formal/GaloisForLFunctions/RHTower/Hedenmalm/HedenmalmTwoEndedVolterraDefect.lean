import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace

/-!
# The two-ended Volterra defect of the Hedenmalm source

At a spectral parameter in the strip `|im alpha| < 1` the theta source has two source-pointed
one-sided inverses: the causal (left Volterra) one and the anti-causal (right Volterra) one.  They
differ by the free mode `exp (-i alpha x)` weighted by the completed theta transform, and the
weight is exactly `XiC alpha`.

Consequently a zero of `XiC` is precisely a coincidence of the two source-pointed inverses.  The
proof needs no operator theory: the difference of the two one-sided integrals is the full-line
Fourier--Laplace integral of the theta cusp source, which the corpus identifies with `XiC` on that
strip.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The two-ended Hedenmalm Volterra integrand at spectral parameter `alpha`. -/
def hedenmalmVolterraIntegrand (α : ℂ) (x t : ℝ) : ℂ :=
  (thetaCuspFullSource t : ℂ) * Complex.exp (-I * α * ((x : ℂ) - (t : ℂ)))

theorem hedenmalmVolterraIntegrand_eq (α : ℂ) (x t : ℝ) :
    hedenmalmVolterraIntegrand α x t =
      Complex.exp (-I * α * (x : ℂ)) * thetaCuspFourierLaplaceIntegrand (-α) t := by
  rw [hedenmalmVolterraIntegrand, thetaCuspFourierLaplaceIntegrand,
    show Complex.exp (-I * α * ((x : ℂ) - (t : ℂ))) =
        Complex.exp (-I * α * (x : ℂ)) * Complex.exp (-I * -α * (t : ℂ)) from by
      rw [← Complex.exp_add]; congr 1; ring]
  ring

theorem integrable_hedenmalmVolterraIntegrand {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    Integrable (hedenmalmVolterraIntegrand α x) := by
  have hneg : |(-α).im| < 1 := by
    rw [Complex.neg_im, abs_neg]
    exact hα
  have hbase := integrable_thetaCuspFourierLaplaceIntegrand hneg
  have := hbase.const_mul (Complex.exp (-I * α * (x : ℂ)))
  exact this.congr (Filter.Eventually.of_forall fun t =>
    (hedenmalmVolterraIntegrand_eq α x t).symm)

/-- The source-pointed **causal** (left Volterra) inverse. -/
def hedenmalmCausalVolterra (α : ℂ) (x : ℝ) : ℂ :=
  -I * ∫ t in Iic x, hedenmalmVolterraIntegrand α x t

/-- The source-pointed **anti-causal** (right Volterra) inverse. -/
def hedenmalmAntiCausalVolterra (α : ℂ) (x : ℝ) : ℂ :=
  I * ∫ t in Ici x, hedenmalmVolterraIntegrand α x t

/-- **The two-ended Volterra defect.**  The causal and anti-causal source-pointed inverses differ
by the free mode `exp (-i alpha x)` weighted by the completed theta transform `XiC alpha`. -/
theorem hedenmalmCausalVolterra_sub_antiCausal {α : ℂ} (hα : |α.im| < 1) (x : ℝ) :
    hedenmalmCausalVolterra α x - hedenmalmAntiCausalVolterra α x =
      -I * Complex.exp (-I * α * (x : ℂ)) * XiC α := by
  have hint := integrable_hedenmalmVolterraIntegrand hα x
  have hIci : (∫ t in Ici x, hedenmalmVolterraIntegrand α x t) =
      ∫ t in Ioi x, hedenmalmVolterraIntegrand α x t :=
    MeasureTheory.integral_Ici_eq_integral_Ioi
  have hsplit : (∫ t in Iic x, hedenmalmVolterraIntegrand α x t) +
      (∫ t in Ioi x, hedenmalmVolterraIntegrand α x t) =
      ∫ t : ℝ, hedenmalmVolterraIntegrand α x t :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  have hfull : (∫ t : ℝ, hedenmalmVolterraIntegrand α x t) =
      Complex.exp (-I * α * (x : ℂ)) * XiC α := by
    have hrw : (∫ t : ℝ, hedenmalmVolterraIntegrand α x t) =
        Complex.exp (-I * α * (x : ℂ)) * ∫ t : ℝ, thetaCuspFourierLaplaceIntegrand (-α) t := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
        hedenmalmVolterraIntegrand_eq α x t)
    rw [hrw, ← thetaCuspFourierLaplace]
    congr 1
    have hmem : (-α) ∈ thetaCuspFourierLaplaceStrip := by
      rw [thetaCuspFourierLaplaceStrip]
      constructor
      · rw [Complex.neg_im]
        have := abs_lt.mp hα
        linarith [this.2]
      · rw [Complex.neg_im]
        have := abs_lt.mp hα
        linarith [this.1]
    rw [thetaCuspFourierLaplace_eq_XiC_on_strip hmem, XiC_even]
  rw [hedenmalmCausalVolterra, hedenmalmAntiCausalVolterra, hIci]
  have : (-I * ∫ t in Iic x, hedenmalmVolterraIntegrand α x t) -
      I * (∫ t in Ioi x, hedenmalmVolterraIntegrand α x t) =
      -I * ((∫ t in Iic x, hedenmalmVolterraIntegrand α x t) +
        ∫ t in Ioi x, hedenmalmVolterraIntegrand α x t) := by ring
  rw [this, hsplit, hfull]
  ring

/-- **A Xi zero is exactly a coincidence of the causal and anti-causal source-pointed inverses.** -/
theorem hedenmalmCausalVolterra_eq_antiCausal_iff {α : ℂ} (hα : |α.im| < 1) :
    (∀ x : ℝ, hedenmalmCausalVolterra α x = hedenmalmAntiCausalVolterra α x) ↔ XiC α = 0 := by
  constructor
  · intro hall
    have h0 := hedenmalmCausalVolterra_sub_antiCausal hα 0
    rw [hall 0, sub_self] at h0
    have hexp : Complex.exp (-I * α * ((0 : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hfac : (-I : ℂ) ≠ 0 := by simp
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h (mul_ne_zero hfac hexp)
    · exact h
  · intro hz x
    have h := hedenmalmCausalVolterra_sub_antiCausal hα x
    rw [hz, mul_zero] at h
    exact sub_eq_zero.mp h

end RHTower
