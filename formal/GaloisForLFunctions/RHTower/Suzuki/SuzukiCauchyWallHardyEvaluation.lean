import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyWallUnitRieszIsometry
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszSharpPoleClassification

/-!
# Lower Hardy evaluation of the completed Suzuki Cauchy wall

The completed wall carrier constructed on the real height axis admits a meromorphic complex-height
continuation.  Its lower Hardy value at `-I` is exactly the outgoing CCM charge, hence half the
critical Mellin--Chebyshev resolvent.  This gives a source-faithful point-evaluation classification
of RH without discarding the polar continuum.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

/-- Entire half-log wall character before restricting height to the real axis. -/
def suzukiCauchyWallPhaseComplex (x : ℝ) (z : ℂ) : ℂ :=
  suzukiOscillatoryKernel z (x / 2)

theorem suzukiCauchyWallPhaseComplex_ofReal
    (x t : ℝ) :
    suzukiCauchyWallPhaseComplex x (t : ℂ) = suzukiCauchyWallPhase x t := by
  rfl

@[simp] theorem suzukiCauchyWallPhaseComplex_neg_I
    (x : ℝ) :
    suzukiCauchyWallPhaseComplex x (-I) = (Real.exp (x / 2) : ℂ) := by
  rw [suzukiCauchyWallPhaseComplex, suzukiOscillatoryKernel, Complex.ofReal_exp]
  congr 1
  push_cast
  rw [mul_neg, Complex.I_mul_I]
  ring

/-- Meromorphic continuation of the polar counterterm.  Its only pole is at `2 * I`. -/
def suzukiCauchyWallPolarCountertermComplex (z : ℂ) : ℂ :=
  (I * (z / 2)) / (1 + I * (z / 2))

theorem suzukiCauchyWallPolarCountertermComplex_ofReal
    (t : ℝ) :
    suzukiCauchyWallPolarCountertermComplex (t : ℂ) =
      suzukiCauchyWallPolarCounterterm t := by
  rfl

@[simp] theorem suzukiCauchyWallPolarCountertermComplex_neg_I :
    suzukiCauchyWallPolarCountertermComplex (-I) = (1 / 3 : ℂ) := by
  rw [suzukiCauchyWallPolarCountertermComplex]
  have hnum : I * (-I / 2) = (1 / 2 : ℂ) := by
    rw [neg_div, mul_neg, ← mul_div_assoc, Complex.I_mul_I]
    norm_num
  rw [hnum]
  norm_num

/-- Meromorphic completed prime-minus-polar wall symbol. -/
def suzukiUnitRieszCompletedCauchyWallSymbolComplex (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 2 N,
      (ArithmeticFunction.vonMangoldt k / Real.sqrt N : ℂ) *
        (1 - suzukiCauchyWallPhaseComplex
          (-(Real.log N - Real.log k)) z) -
    (Real.sqrt N : ℂ) * suzukiCauchyWallPolarCountertermComplex z

theorem suzukiUnitRieszCompletedCauchyWallSymbolComplex_ofReal
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszCompletedCauchyWallSymbolComplex N (t : ℂ) =
      suzukiUnitRieszCompletedCauchyWallSymbol N t := by
  rfl

/-- The lower Hardy value is exactly the literal completed outgoing coherent charge. -/
theorem suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge
    (N : ℕ) :
    suzukiUnitRieszCompletedCauchyWallSymbolComplex N (-I) =
      (unitRieszCoherentCompletedOutgoingCharge N : ℂ) := by
  rw [suzukiUnitRieszCompletedCauchyWallSymbolComplex,
    unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPrimeOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq]
  simp only [suzukiCauchyWallPhaseComplex_neg_I,
    suzukiCauchyWallPolarCountertermComplex_neg_I]
  push_cast
  ring

/-- At every nondegenerate natural aperture, the lower Hardy value is half the critical
Mellin--Chebyshev resolvent. -/
theorem suzukiUnitRieszCompletedCauchyWallSymbolComplex_add_two_neg_I_eq_resolvent_half
    (N : ℕ) :
    suzukiUnitRieszCompletedCauchyWallSymbolComplex (N + 2) (-I) =
      (criticalMellinChebyshevResolventSource (Real.log (N + 2)) / 2 : ℝ) := by
  rw [suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge,
    unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half (by omega)]
  norm_num

/-- **Hardy point-evaluation classification.**  RH is exactly the uniform four-unit bound on the
lower Hardy value of the literal completed Suzuki wall symbol. -/
theorem riemannHypothesis_iff_suzukiCompletedCauchyWall_neg_I_sq_le_four :
    RiemannHypothesis ↔
      ∀ N : ℕ,
        ‖suzukiUnitRieszCompletedCauchyWallSymbolComplex (N + 2) (-I)‖ ^ (2 : ℕ) ≤ 4 := by
  constructor
  · intro hRH N
    rw [suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge]
    have hcharge :=
      RHTower.abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis
        hRH (by omega : 2 ≤ N + 2)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (unitRieszCoherentCompletedOutgoingCharge (N + 2))]
  · intro hwall
    rw [RHTower.riemannHypothesis_iff_unitRieszCoherentCompletedOutgoingProfile_le_pole]
    intro N hN u hu
    have h := hwall (N - 2)
    have hNshift : N - 2 + 2 = N := Nat.sub_add_cancel hN
    rw [hNshift, suzukiUnitRieszCompletedCauchyWallSymbolComplex_neg_I_eq_outgoingCharge,
      unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN] at h
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_div] at h
    norm_num at h
    have hres : criticalMellinChebyshevResolventSource (Real.log N) ^ (2 : ℕ) ≤ 16 := by
      nlinarith [abs_nonneg (criticalMellinChebyshevResolventSource (Real.log N)),
        sq_abs (criticalMellinChebyshevResolventSource (Real.log N))]
    exact ((unitRieszCoherentCompletedOutgoingProfile_le_pole_iff hN).2 hres) u hu

end

end GaloisForLFunctions.RHTower
