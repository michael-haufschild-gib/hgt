import GaloisForLFunctions.EulerFETransportTheory.LocalThetaDataDetermineTheDefect
import GaloisForLFunctions.EulerFETransportTheory.IntegrableFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyRigidityAnnihilatesTheDefect

/-!
# Integrable arithmetic rigidity annihilates the actual defect

Rational-prime classification identifies the theta measure. Jacobi's exact law
then annihilates its Hamburger defect kernel. Local identification of polynomial
defects recovers almost-everywhere vanishing of the uncompleted defect, and the
original strip identity rules out changes on null sets.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- In the original Hamburger strip class, an integrable defect vanishes pointwise.
No square-integrability or extra continuity assumption is imposed on the defect. -/
theorem beurling_integrable_strip_defect_eq_zero
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (HTGeometry.verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng)
    (hgi : Integrable g) : ∀ t, g t = 0 := by
  obtain ⟨hb, hν, _⟩ := beurlingSystem_rigidity_of_integrable_defect B hBsum
    hEc hEd hdecay hR hC hgm hgb hgi
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet (beurlingSystemIntegerMeasure B) s =
        E s + β * Complex.Gammaℝ (s - 1) := by
    simpa only [measureDirichlet_beurlingSystemIntegerMeasure] using hR
  have hθ := measureTheta_defect_relation hsupp hmom hEc hEd hdecay hR' hC hgm hgb
  have hzero : ∀ x : ℝ, 0 < x → defectKernel g x = 0 := by
    intro x hx
    have hd := hθ x hx
    rw [hν, beurlingIntegerMeasure_riemannPrimeMeasure, hb] at hd
    have he := GaloisForLFunctions.ArithmeticCastelnuovoSeveri.measureTheta_nat_sum_relation hx
    linear_combination he - hd
  have hgae : g =ᵐ[volume] 0 := ae_eq_zero_of_defectKernel_eq_zero_on_interval
    hgm hgb (a := 1) (b := 2) (by norm_num) (by norm_num)
    (fun x hx => hzero x (lt_trans (by norm_num) hx.1))
  have hg2 : MemLp g 2 (volume : Measure ℝ) :=
    (memLp_congr_ae hgae).mpr MemLp.zero
  exact beurling_finiteEnergy_strip_defect_eq_zero B hBsum
    hEc hEd hdecay hR hC hgm hgb hg2

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_integrable_strip_defect_eq_zero
