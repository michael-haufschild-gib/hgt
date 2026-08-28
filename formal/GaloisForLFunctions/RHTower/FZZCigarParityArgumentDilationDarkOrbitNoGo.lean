import GaloisForLFunctions.RHTower.FZZCigarParityDeningerInformationWardTransmutation

/-!
# Argument-dilation dark-orbit no-go for FZZ parity modes

Positive argument dilation acts on the literal FZZ Mellin response by a nonzero character, so it
preserves and reflects every zero. All-scale darkness is therefore blind to the shared
FZZ-information/Deninger-Ward charge.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Literal Mellin response after positive argument dilation of the FZZ parity-delay source. -/
def fzzCigarParityArgumentDilatedMellin (r : ℝ) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ => ((fzzCigarParityDelay (r * t) : ℝ) : ℂ)) s

/-- Exact source covariance under positive argument dilation. -/
theorem fzzCigarParityArgumentDilatedMellin_eq
    {r : ℝ} (hr : 0 < r) (s : ℂ) :
    fzzCigarParityArgumentDilatedMellin r s =
      (r : ℂ) ^ (-s) * fzzCigarParityMellin s := by
  simpa only [fzzCigarParityArgumentDilatedMellin, fzzCigarParityMellin,
    smul_eq_mul] using
      (mellin_comp_mul_left
        (fun t : ℝ => ((fzzCigarParityDelay t : ℝ) : ℂ)) s hr)

theorem fzzCigarParityArgumentDilationCharacter_ne_zero
    {r : ℝ} (hr : 0 < r) (s : ℂ) :
    (r : ℂ) ^ (-s) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hr.ne'))

/-- A positive argument dilation preserves and reflects the complete literal FZZ zero set. -/
theorem fzzCigarParityArgumentDilatedMellin_eq_zero_iff
    {r : ℝ} (hr : 0 < r) (s : ℂ) :
    fzzCigarParityArgumentDilatedMellin r s = 0 ↔
      FZZCigarParityMellinMode s := by
  rw [fzzCigarParityArgumentDilatedMellin_eq hr, FZZCigarParityMellinMode]
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (fzzCigarParityArgumentDilationCharacter_ne_zero hr s)
  · intro hzero
    rw [hzero, mul_zero]

/-- Darkness at every positive argument dilation. -/
def FZZCigarParityAllArgumentDilationMode (s : ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → fzzCigarParityArgumentDilatedMellin r s = 0

/-- One source zero and its entire positive-dilation dark orbit contain exactly the same data. -/
theorem fzzCigarParityAllArgumentDilationMode_iff (s : ℂ) :
    FZZCigarParityAllArgumentDilationMode s ↔ FZZCigarParityMellinMode s := by
  constructor
  · intro hall
    exact (fzzCigarParityArgumentDilatedMellin_eq_zero_iff one_pos s).mp
      (hall 1 one_pos)
  · intro hmode r hr
    exact (fzzCigarParityArgumentDilatedMellin_eq_zero_iff hr s).mpr hmode

/-- Every actual Xi divisor copy has a literal all-positive-scale FZZ dark orbit,
unconditionally and independently of its horizontal position. -/
theorem fzzCigarParityAllArgumentDilationMode_deningerDivisorThetaEigen
    (q : XiZeroCopy) :
    FZZCigarParityAllArgumentDilationMode (deningerDivisorThetaEigen q) :=
  (fzzCigarParityAllArgumentDilationMode_iff _).mpr
    (fzzCigarParityMellinMode_deningerDivisorThetaEigen q)

/-- Proposal that every already-dark dilation orbit cancels the shared FZZ/Deninger Ward charge. -/
def FZZCigarParityAllArgumentDilationWardCancellation : Prop :=
  ∀ q : XiZeroCopy,
    FZZCigarParityAllArgumentDilationMode (deningerDivisorThetaEigen q) →
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0

/-- No-go boundary: adding Ward cancellation to universal dilation darkness is exactly RH. -/
theorem fzzCigarParityAllArgumentDilationWardCancellation_iff_riemannHypothesis :
    FZZCigarParityAllArgumentDilationWardCancellation ↔ RiemannHypothesis := by
  constructor
  · intro hcancel
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    exact (fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff q).mp
      (hcancel q
        (fzzCigarParityAllArgumentDilationMode_deningerDivisorThetaEigen q))
  · intro hRH q _hall
    have heq :=
      (fzzCigarParityDeningerInformationWardEquilibrium_iff_riemannHypothesis.mpr hRH) q
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
    have hre :=
      (fzzCigarParityReflectedFermiInformationForce_eq_zero_iff h0 h1).mp heq
    exact (fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff q).mpr hre

theorem riemannHypothesis_iff_fzzCigarParityAllArgumentDilationWardCancellation :
    RiemannHypothesis ↔ FZZCigarParityAllArgumentDilationWardCancellation :=
  fzzCigarParityAllArgumentDilationWardCancellation_iff_riemannHypothesis.symm

end

end RHTower
