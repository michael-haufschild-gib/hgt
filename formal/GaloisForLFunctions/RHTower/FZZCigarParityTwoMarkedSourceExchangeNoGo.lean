import GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedSourceContact

/-!
# FZZ-P two-marked source exchange no-go

FZZ-P requires a source-fixed exchange-antisymmetric ordered depth kernel to retain the
orientation of the literal cross-depth covariance.  The independently marked FZZ OPE contact is
not such a source: its exponent is exchange-symmetric, hence so are both its positive pair
kernel and its compact-annular integrated realization.  Their exchange defects vanish exactly.

This kills the FZZ-P subroute

`two-marked local OPE/contact alone → exchange-antisymmetric ordered kernel → oriented Ward
term`.

The sharp survivor is source structure absent from this two-mark contact: a genuinely temporal or
ordered term, an external BRST product, or a complex counterterm coupling.  This file does not
assert that any survivor is physically present.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The literal independently marked FZZ OPE exponent is exchange-symmetric in its two marks. -/
theorem fzzTwoMarkedOPEExponent_exchange
    (k q δ ε : ℝ) :
    fzzTwoMarkedOPEExponent k q δ ε = fzzTwoMarkedOPEExponent k q ε δ := by
  unfold fzzTwoMarkedOPEExponent
  ring

/-- The literal positive two-mark pair kernel is exchange-symmetric. -/
theorem fzzTwoMarkedPairKernel_exchange
    (u q L δ ε : ℝ) :
    fzzTwoMarkedPairKernel u q L δ ε = fzzTwoMarkedPairKernel u q L ε δ := by
  unfold fzzTwoMarkedPairKernel
  rw [fzzTwoMarkedOPEExponent_exchange]

/-- The literal compact-annular two-mark source integral is exchange-symmetric. -/
theorem fzzTwoMarkedAnnularIntegral_exchange
    (u L δ ε : ℝ) :
    fzzTwoMarkedAnnularIntegral u L δ ε = fzzTwoMarkedAnnularIntegral u L ε δ := by
  unfold fzzTwoMarkedAnnularIntegral
  rw [fzzTwoMarkedOPEExponent_exchange]

/-- Exchange-antisymmetric component of the literal positive two-mark pair kernel. -/
def fzzTwoMarkedPairKernelExchangeDefect (u q L δ ε : ℝ) : ℝ :=
  fzzTwoMarkedPairKernel u q L δ ε - fzzTwoMarkedPairKernel u q L ε δ

/-- The literal two-mark pair kernel has no exchange-antisymmetric component. -/
theorem fzzTwoMarkedPairKernelExchangeDefect_eq_zero
    (u q L δ ε : ℝ) :
    fzzTwoMarkedPairKernelExchangeDefect u q L δ ε = 0 := by
  unfold fzzTwoMarkedPairKernelExchangeDefect
  rw [fzzTwoMarkedPairKernel_exchange]
  ring

/-- Exchange-antisymmetric component of the literal compact-annular two-mark source. -/
def fzzTwoMarkedAnnularExchangeDefect (u L δ ε : ℝ) : ℝ :=
  fzzTwoMarkedAnnularIntegral u L δ ε - fzzTwoMarkedAnnularIntegral u L ε δ

/-- The compact-annular realization likewise has no exchange-antisymmetric component. -/
theorem fzzTwoMarkedAnnularExchangeDefect_eq_zero
    (u L δ ε : ℝ) :
    fzzTwoMarkedAnnularExchangeDefect u L δ ε = 0 := by
  unfold fzzTwoMarkedAnnularExchangeDefect
  rw [fzzTwoMarkedAnnularIntegral_exchange]
  ring

/-- **FZZ-P source-candidate no-go.** No literal two-mark pair kernel can supply a nonzero
exchange-antisymmetric source coefficient. -/
theorem not_exists_fzzTwoMarkedPairKernelExchangeDefect_ne_zero :
    ¬ ∃ (u q L δ ε : ℝ), fzzTwoMarkedPairKernelExchangeDefect u q L δ ε ≠ 0 := by
  rintro ⟨u, q, L, δ, ε, h⟩
  exact h (fzzTwoMarkedPairKernelExchangeDefect_eq_zero u q L δ ε)

/-- **FZZ-P compact source-candidate no-go.** No literal compact-annular two-mark realization
can supply a nonzero exchange-antisymmetric source coefficient. -/
theorem not_exists_fzzTwoMarkedAnnularExchangeDefect_ne_zero :
    ¬ ∃ (u L δ ε : ℝ), fzzTwoMarkedAnnularExchangeDefect u L δ ε ≠ 0 := by
  rintro ⟨u, L, δ, ε, h⟩
  exact h (fzzTwoMarkedAnnularExchangeDefect_eq_zero u L δ ε)

end

end GaloisForLFunctions.RHTower
