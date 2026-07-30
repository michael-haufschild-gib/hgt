import GaloisForLFunctions.RHTower.HighExponentShellPrimeSpectrum
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation

/-!
# Xi modular residue transgression

The local source-normal-cone residue and the cofinal
hypertranscendental shell drift carry the same signed horizontal
divisor charge.  For Xi order `n` at `rho`,

`Re(-((rho - 1/2) n)) =
  n / log 2 * log ‖2^(1/2-rho)‖`.

Thus the Julia normal coordinate, shell Lyapunov exponent, and divisor
multiplicity are three exact charts of one invariant.
-/

open Complex Filter Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Shell-transfer entropy, normalized to equal signed horizontal
displacement. -/
def shellTransferEntropy (s : ℂ) : ℝ :=
  Real.log ‖shellTransferCharacter s‖ / Real.log 2

/-- The normalized shell-transfer entropy is exactly displacement
toward the left of the critical line. -/
theorem shellTransferEntropy_eq (s : ℂ) :
    shellTransferEntropy s = 1 / 2 - s.re := by
  rw [shellTransferEntropy, log_norm_shellTransferCharacter]
  have hlog : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-- Transfer entropy vanishes exactly on the critical line. -/
theorem shellTransferEntropy_eq_zero_iff (s : ℂ) :
    shellTransferEntropy s = 0 ↔ s.re = 1 / 2 := by
  rw [shellTransferEntropy_eq]
  constructor <;> intro h <;> linarith

/-- Functional-equation reflection reverses shell-transfer entropy. -/
theorem shellTransferEntropy_reflection (s : ℂ) :
    shellTransferEntropy (1 - star s) =
      -shellTransferEntropy s := by
  rw [shellTransferEntropy_eq, shellTransferEntropy_eq]
  simp only [Complex.sub_re, Complex.one_re, Complex.star_def,
    Complex.conj_re]
  ring

/-- **Local--cofinal residue transgression.**  The real part of the
centered affine Xi boundary residue equals multiplicity times the
normalized logarithmic modulus of the hypertranscendental shell
transfer. -/
theorem re_centeredXiAffineResidue_eq_shellTransferEntropy
    (rho : ℂ) (n : ℤ) :
    (-((rho - 1 / 2) * (n : ℂ))).re =
      (n : ℝ) * shellTransferEntropy rho := by
  rw [shellTransferEntropy_eq]
  norm_num [Complex.mul_re, Complex.sub_re]
  ring

/-- The source-normal-cone current converges to the same modular
transfer charge at every Xi divisor point. -/
theorem tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy
    {rho : ℂ} {n : ℤ}
    (horder : meromorphicOrderAt xi rho = n) :
    Tendsto
      (fun s =>
        ((s - rho) * xiExceptionalAffineDivisorCurrent s).re)
      (𝓝[≠] rho)
      (nhds ((n : ℝ) * shellTransferEntropy rho)) := by
  have hres :=
    xiExceptionalAffineDivisorCurrent_residue horder
  have hre :=
    (Complex.continuous_re.tendsto
      (-((rho - 1 / 2) * (n : ℂ)))).comp hres
  rw [re_centeredXiAffineResidue_eq_shellTransferEntropy] at hre
  exact hre

/-- For nonzero divisor order, vanishing local/cofinal charge is
equivalent to critical-line location. -/
theorem centeredXiModularCharge_eq_zero_iff
    {rho : ℂ} {n : ℤ} (hn : n ≠ 0) :
    (n : ℝ) * shellTransferEntropy rho = 0 ↔
      rho.re = 1 / 2 := by
  rw [mul_eq_zero]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [hnreal, false_or]
  exact shellTransferEntropy_eq_zero_iff rho

/-- The residue transgression is independent of the chosen atom base:
every scale `q > 1` gives the same signed Xi divisor charge. -/
theorem re_centeredXiAffineResidue_eq_leastAtomTransferEntropy
    {q : ℝ} (hq : 1 < q) (rho : ℂ) (n : ℤ) :
    (-((rho - 1 / 2) * (n : ℂ))).re =
      (n : ℝ) *
        HTGeometry.leastAtomTransferEntropy q 1 rho := by
  rw [HTGeometry.leastAtomTransferEntropy_eq hq]
  norm_num [Complex.mul_re, Complex.sub_re]
  ring

/-- The local source-normal-cone current transgresses to the modular
entropy of every admissible cofinal atom scale. -/
theorem tendsto_re_xiExceptionalAffineDivisorCurrent_eq_atomEntropy
    {q : ℝ} (hq : 1 < q) {rho : ℂ} {n : ℤ}
    (horder : meromorphicOrderAt xi rho = n) :
    Tendsto
      (fun s =>
        ((s - rho) * xiExceptionalAffineDivisorCurrent s).re)
      (𝓝[≠] rho)
      (nhds
        ((n : ℝ) *
          HTGeometry.leastAtomTransferEntropy q 1 rho)) := by
  have hres :=
    xiExceptionalAffineDivisorCurrent_residue horder
  have hre :=
    (Complex.continuous_re.tendsto
      (-((rho - 1 / 2) * (n : ℂ)))).comp hres
  rw [re_centeredXiAffineResidue_eq_leastAtomTransferEntropy
    hq] at hre
  exact hre

/-- The prime-two and prime-three cofinal charts report the identical
local Xi modular charge. -/
theorem xiModularCharge_prime_two_eq_prime_three
    (rho : ℂ) (n : ℤ) :
    (n : ℝ) *
        HTGeometry.leastAtomTransferEntropy 2 1 rho =
      (n : ℝ) *
        HTGeometry.leastAtomTransferEntropy 3 1 rho := by
  rw [HTGeometry.leastAtomTransferEntropy_base_independent
    (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (1 : ℝ) < 3)]

/-- Exact theorem package identifying the local normal residue, cofinal
shell entropy, reflection orientation, and critical-line neutral phase. -/
structure XiHypertranscendentalModularResidueTransgressionCertificate :
    Prop where
  entropyFormula :
    ∀ s : ℂ, shellTransferEntropy s = 1 / 2 - s.re
  reflectionOdd :
    ∀ s : ℂ,
      shellTransferEntropy (1 - star s) =
        -shellTransferEntropy s
  localCofinalResidue :
    ∀ {rho : ℂ} {n : ℤ}, meromorphicOrderAt xi rho = n →
      Tendsto
        (fun s =>
          ((s - rho) * xiExceptionalAffineDivisorCurrent s).re)
        (𝓝[≠] rho)
        (nhds ((n : ℝ) * shellTransferEntropy rho))
  neutralPhase :
    ∀ {rho : ℂ} {n : ℤ}, n ≠ 0 →
      ((n : ℝ) * shellTransferEntropy rho = 0 ↔
        rho.re = 1 / 2)
  atomBaseTransgression :
    ∀ {q : ℝ}, 1 < q → ∀ {rho : ℂ} {n : ℤ},
      meromorphicOrderAt xi rho = n →
        Tendsto
          (fun s =>
            ((s - rho) *
              xiExceptionalAffineDivisorCurrent s).re)
          (𝓝[≠] rho)
          (nhds
            ((n : ℝ) *
              HTGeometry.leastAtomTransferEntropy q 1 rho))
  twoPrimeTomography :
    Function.Injective twoPrimeShellTransferSpectrum

/-- **Xi hypertranscendental modular-residue transgression law.** -/
theorem xiHypertranscendentalModularResidueTransgression_law :
    XiHypertranscendentalModularResidueTransgressionCertificate where
  entropyFormula := shellTransferEntropy_eq
  reflectionOdd := shellTransferEntropy_reflection
  localCofinalResidue :=
    tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy
  neutralPhase := centeredXiModularCharge_eq_zero_iff
  atomBaseTransgression :=
    fun hq _ _ horder =>
      tendsto_re_xiExceptionalAffineDivisorCurrent_eq_atomEntropy
        hq horder
  twoPrimeTomography := twoPrimeShellTransferSpectrum_injective

end

end RHTower
