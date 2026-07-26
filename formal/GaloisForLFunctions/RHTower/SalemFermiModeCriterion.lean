import GaloisForLFunctions.RHTower.RiemannTower
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The 2026 Salem Fermi-mode criterion

Gonzalez--Negrin (`arXiv:2604.15396`) specialize Salem's integral equation to the bounded
Mellin modes `t^(i gamma)`.  The classical Fermi--Dirac Mellin evaluation is

`integral t^(s-1)/(exp(x*t)+1) dt = x^(-s) * Gamma(s) * (1-2^(1-s)) * zeta(s)`.

This file formalizes the exact closed-form spectral endpoint of that evaluation.  In the strip
`1/2 < Re s < 1`, all factors other than zeta are proved nonzero, so a mode solves the equation
for every `x > 0` exactly when zeta vanishes at its spectral parameter.  Excluding all such modes
is then proved equivalent to mathlib's `RiemannHypothesis`.

This file isolates the evaluated spectral multiplier.  The downstream module
`SalemFermiModeIntegral` proves the literal improper-integral evaluation and identifies its
integral-defined solution predicate with the one below.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The spectral parameter `delta + i*gamma` of a Salem bounded Mellin mode. -/
def salemSpectralParameter (delta gamma : ℝ) : ℂ :=
  (delta : ℂ) + I * (gamma : ℂ)

@[simp] theorem salemSpectralParameter_re (delta gamma : ℝ) :
    (salemSpectralParameter delta gamma).re = delta := by
  simp [salemSpectralParameter]

@[simp] theorem salemSpectralParameter_im (delta gamma : ℝ) :
    (salemSpectralParameter delta gamma).im = gamma := by
  simp [salemSpectralParameter]

/-- Every complex number is its real/imaginary Salem spectral coordinate. -/
theorem salemSpectralParameter_re_im (s : ℂ) :
    salemSpectralParameter s.re s.im = s := by
  apply Complex.ext <;> simp

/-- The evaluated Fermi--Dirac Mellin transform of the mode `t^(i*gamma)`, with the
power, Gamma, eta-to-zeta, and zeta factors kept separate. -/
def salemFermiModeTransform (delta gamma x : ℝ) : ℂ :=
  let s := salemSpectralParameter delta gamma
  (x : ℂ) ^ (-s) * Complex.Gamma s *
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- A Salem Mellin mode solves the evaluated integral equation at every positive scale. -/
def SalemFermiModeSolution (delta gamma : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → salemFermiModeTransform delta gamma x = 0

/-- In the Salem strip, the eta-to-zeta factor `1 - 2^(1-s)` cannot vanish.  Its norm is
strictly greater than one because `Re(1-s) = 1-delta > 0`. -/
theorem salemDyadicFactor_ne_zero {delta gamma : ℝ} (hdelta : delta < 1) :
    1 - (2 : ℂ) ^ (1 - salemSpectralParameter delta gamma) ≠ 0 := by
  intro hzero
  have hpow : (2 : ℂ) ^ (1 - salemSpectralParameter delta gamma) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hpow
  have hnorm' :
      ‖((2 : ℕ) : ℂ) ^ (1 - salemSpectralParameter delta gamma)‖ = 1 := by
    simpa using hnorm
  rw [Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < (2 : ℕ))] at hnorm'
  have hgt : 1 < (2 : ℝ) ^ (1 - delta) :=
    Real.one_lt_rpow (by norm_num) (sub_pos.mpr hdelta)
  have hre : (1 - salemSpectralParameter delta gamma).re = 1 - delta := by simp
  rw [hre] at hnorm'
  have heq : (2 : ℝ) ^ (1 - delta) = 1 := by simpa using hnorm'
  exact (ne_of_gt hgt) heq

/-- At a positive scale and in `0 < delta < 1`, the complete non-zeta prefactor of the
Salem spectral multiplier is nonzero. -/
theorem salemFermiModePrefactor_ne_zero {delta gamma x : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hx : 0 < x) :
    (x : ℂ) ^ (-salemSpectralParameter delta gamma) *
        Complex.Gamma (salemSpectralParameter delta gamma) *
        (1 - (2 : ℂ) ^ (1 - salemSpectralParameter delta gamma)) ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hx.ne'))
    · exact Complex.Gamma_ne_zero_of_re_pos (by simpa using hdelta0)
  · exact salemDyadicFactor_ne_zero hdelta1

/-- **Exact Salem mode endpoint.**  In the open critical strip, the evaluated Fermi mode
solves the equation at every positive scale exactly when zeta vanishes at its spectral point. -/
theorem salemFermiModeSolution_iff_riemannZeta_eq_zero
    {delta gamma : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    SalemFermiModeSolution delta gamma ↔
      riemannZeta (salemSpectralParameter delta gamma) = 0 := by
  constructor
  · intro hmode
    have hone := hmode 1 zero_lt_one
    rw [salemFermiModeTransform] at hone
    exact (mul_eq_zero.mp hone).resolve_left
      (salemFermiModePrefactor_ne_zero hdelta0 hdelta1 zero_lt_one)
  · intro hzeta x hx
    simp [salemFermiModeTransform, hzeta]

/-- The exact wall in the 2026 Salem formulation: no bounded pure Mellin mode with
`1/2 < delta < 1` solves the evaluated integral equation at every scale. -/
def SalemFermiModeExclusion : Prop :=
  ∀ delta gamma : ℝ, 1 / 2 < delta → delta < 1 →
    ¬ SalemFermiModeSolution delta gamma

/-- **Gonzalez--Negrin/Salem criterion, unconditional Lean form.**  Exclusion of all pure
Mellin-mode solutions in the right half of the critical strip is exactly RH. -/
theorem salemFermiModeExclusion_iff_riemannHypothesis :
    SalemFermiModeExclusion ↔ RiemannHypothesis := by
  constructor
  · intro hexclusion
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hxis
    have hhalf : 1 / 2 < s.re := mem_rightHalf.mp hs
    have hs1 : s ≠ 1 := by
      intro hsone
      subst s
      rw [xi_one] at hxis
      norm_num at hxis
    have hspos : 0 < s.re := lt_trans (by norm_num) hhalf
    have hzeta : riemannZeta s = 0 := (xi_eq_zero_iff hspos hs1).mp hxis
    have hslt1 : s.re < 1 := by
      by_contra hnot
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hnot) hzeta
    have hmode : SalemFermiModeSolution s.re s.im :=
      (salemFermiModeSolution_iff_riemannZeta_eq_zero hspos hslt1).mpr (by
        rwa [salemSpectralParameter_re_im])
    exact hexclusion s.re s.im hhalf hslt1 hmode
  · intro hRH delta gamma hhalf hdelta1 hmode
    have hdelta0 : 0 < delta := lt_trans (by norm_num) hhalf
    have hzeta : riemannZeta (salemSpectralParameter delta gamma) = 0 :=
      (salemFermiModeSolution_iff_riemannZeta_eq_zero hdelta0 hdelta1).mp hmode
    have htriv :
        ¬ ∃ n : ℕ, salemSpectralParameter delta gamma = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      norm_num [salemSpectralParameter, Complex.mul_re] at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs1 : salemSpectralParameter delta gamma ≠ 1 := by
      intro hsone
      have hre := congrArg Complex.re hsone
      simp at hre
      linarith
    have hline := hRH (salemSpectralParameter delta gamma) hzeta htriv hs1
    simp only [salemSpectralParameter_re] at hline
    linarith

end

end RHTower
