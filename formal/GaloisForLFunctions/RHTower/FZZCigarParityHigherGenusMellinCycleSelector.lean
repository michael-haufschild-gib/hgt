import GaloisForLFunctions.HTGeometry.FZZCigarHigherGenusTwistRedshift
import GaloisForLFunctions.HTGeometry.FZZCigarReplicaTwoLevelKreinSelector
import GaloisForLFunctions.RHTower.FZZCigarParityMellinCharacterCrossingReflection

/-!
# Same-cigar higher-genus cycles realize the dyadic Mellin wall selector

The previous finite FZZ selector used replica levels `k=4,3` to obtain response scales `1,2`.
Changing `k`, however, changes the CFT and leaves a cross-level state-transport premise.  The
higher-genus FZZ path integral already contains an exact scale-doubling representation inside one
fixed CFT: the reciprocal first-order-field holonomies at integer homology cycles `n,2n`.

Their normalized odd part is exactly `sinh z,sinh (2z)`.  The sharp two-scale selector therefore
proves, for every nonzero `n`, that cycle-`n` reality plus cycle-`2n` passivity is equivalent to real
twist, zero radial monodromy, and unit beta-holonomy.

A universal torus-twist coordinate sends the centered Mellin parameter `rho - 1/2` to this
higher-genus twist.  At cycles one and two the beta-holonomies are respectively the corpus's
dyadic Mellin character and its square.  Hence the same-CFT two-cycle chamber is equivalent to
`rho.re = 1/2`.

## RH-chain scope

`literal parity-Mellin Gamma-zeta divisor mode`
→ `canonical torus twist`
→ `same-CFT cycles 1,2`
→ `two-cycle chamber`
→ `critical line`
→ `reflected FZZ-P incidence`
→ `RH`.

This closes the common-mode/scale-transport arrow without varying cigar level.  The remaining
physical premise is the source-specific torus replica-area Ward law putting literal divisor modes
in the two holonomy chambers; no such sign law is assumed here.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- Odd response of the reciprocal higher-genus first-order holonomies. -/
def fzzHigherGenusOddHolonomy (n : ℤ) (twist : ℂ) : ℂ :=
  (higherGenusBetaTwistMultiplier n twist -
    higherGenusGammaTwistMultiplier n twist) / 2

private def fzzHigherGenusTwistExponent (n : ℤ) (twist : ℂ) : ℂ :=
  (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I * twist)

/-- The physical beta/gamma reciprocal pair has exactly hyperbolic-sine odd part. -/
theorem fzzHigherGenusOddHolonomy_eq_sinh (n : ℤ) (twist : ℂ) :
    fzzHigherGenusOddHolonomy n twist =
      Complex.sinh (fzzHigherGenusTwistExponent n twist) := by
  rfl

private lemma fzzHigherGenusTwistExponent_two_mul (n : ℤ) (twist : ℂ) :
    fzzHigherGenusTwistExponent (2 * n) twist =
      2 * fzzHigherGenusTwistExponent n twist := by
  simp only [fzzHigherGenusTwistExponent, Int.cast_mul, Int.cast_ofNat]
  push_cast
  ring

private theorem sinh_cycle_double_chamber_iff_re_eq_zero (z : ℂ) :
    ((Complex.sinh z) ^ 2).im = 0 ∧
        ((Complex.sinh (2 * z)) ^ 2).re ≤ 0 ↔
      z.re = 0 := by
  have h :=
    fzzReplicaLevelFourRealityLevelThreeNonpositive_iff_re_eq_zero (2 * z)
  rw [FZZReplicaLevelFourRealityLevelThreeNonpositive,
    replicaLinearizedDressingScale_one_fourth,
    replicaLinearizedDressingScale_one_third] at h
  simpa using h

/-- Joint reality/passivity chamber at two homology cycle numbers in one fixed cigar CFT. -/
def FZZHigherGenusCyclePairKreinSign (n : ℤ) (twist : ℂ) : Prop :=
  ((fzzHigherGenusOddHolonomy n twist) ^ 2).im = 0 ∧
    ((fzzHigherGenusOddHolonomy (2 * n) twist) ^ 2).re ≤ 0

/-- **Same-CFT two-cycle selector.** Two nonzero homology cycles `n,2n` select exactly real
higher-genus twist. -/
theorem fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero
    {n : ℤ} (hn : n ≠ 0) (twist : ℂ) :
    FZZHigherGenusCyclePairKreinSign n twist ↔ twist.im = 0 := by
  rw [FZZHigherGenusCyclePairKreinSign,
    fzzHigherGenusOddHolonomy_eq_sinh,
    fzzHigherGenusOddHolonomy_eq_sinh,
    fzzHigherGenusTwistExponent_two_mul,
    sinh_cycle_double_chamber_iff_re_eq_zero]
  rw [fzzHigherGenusTwistExponent]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : 2 * Real.pi * (n : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hnR
  constructor
  · intro h
    have hz : (2 * Real.pi * (n : ℝ)) * twist.im = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hc
  · intro h
    rw [h]
    ring

/-- The same two-cycle chamber is exactly absence of radial black-hole monodromy. -/
theorem fzzHigherGenusCyclePairKreinSign_iff_radialMonodromy_eq_zero
    {b : ℝ} (hb : 0 < b) {n : ℤ} (hn : n ≠ 0) (twist : ℂ) :
    FZZHigherGenusCyclePairKreinSign n twist ↔
      higherGenusRadialMonodromy b n twist = 0 := by
  rw [fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  constructor
  · intro h
    simp [higherGenusRadialMonodromy, h]
  · intro h
    rw [higherGenusRadialMonodromy] at h
    have hnum : 2 * Real.pi * (n : ℝ) * twist.im = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hb.ne'
    rcases mul_eq_zero.mp hnum with hcoef | htwist
    · exfalso
      exact (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hnR hcoef).elim
    · exact htwist

/-- Equivalently, the physical beta holonomy is unitary. -/
theorem fzzHigherGenusCyclePairKreinSign_iff_norm_beta_eq_one
    {b : ℝ} (hb : 0 < b) {n : ℤ} (hn : n ≠ 0) (twist : ℂ) :
    FZZHigherGenusCyclePairKreinSign n twist ↔
      ‖higherGenusBetaTwistMultiplier n twist‖ = 1 := by
  rw [fzzHigherGenusCyclePairKreinSign_iff_radialMonodromy_eq_zero hb hn]
  exact (norm_higherGenusBetaTwistMultiplier_eq_one_iff hb n twist).symm

/-- Universal torus-twist coordinate of the centered dyadic Mellin character. -/
def fzzCigarParityMellinTorusTwist (rho : ℂ) : ℂ :=
  ((-(Real.log 2 / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I * (rho - 1 / 2)

private theorem fzzCigarParityMellinTorusTwist_exponent (rho : ℂ) :
    fzzHigherGenusTwistExponent 1 (fzzCigarParityMellinTorusTwist rho) =
      (Real.log 2 : ℂ) * (rho - 1 / 2) := by
  rw [fzzHigherGenusTwistExponent, fzzCigarParityMellinTorusTwist]
  norm_num
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]
  rw [Complex.I_sq]
  ring

/-- Cycle one is exactly the centered dyadic Mellin character already used by the FZZ-P route. -/
theorem higherGenusBetaTwistMultiplier_mellinTorusTwist_eq_dyadicCharacter
    (rho : ℂ) :
    higherGenusBetaTwistMultiplier 1
        (fzzCigarParityMellinTorusTwist rho) =
      fzzCigarParityDyadicMellinCharacter rho := by
  rw [higherGenusBetaTwistMultiplier,
    fzzCigarParityDyadicMellinCharacter,
    centeredComplexModularCharacter,
    ← fzzCigarParityMellinTorusTwist_exponent]
  rfl

/-- Cycle two is the square of that dyadic character inside the same CFT. -/
theorem higherGenusBetaTwistMultiplier_two_mellinTorusTwist_eq_dyadicCharacter_sq
    (rho : ℂ) :
    higherGenusBetaTwistMultiplier 2
        (fzzCigarParityMellinTorusTwist rho) =
      fzzCigarParityDyadicMellinCharacter rho ^ 2 := by
  calc
    higherGenusBetaTwistMultiplier 2 (fzzCigarParityMellinTorusTwist rho) =
        higherGenusBetaTwistMultiplier 1 (fzzCigarParityMellinTorusTwist rho) ^ 2 := by
      rw [higherGenusBetaTwistMultiplier, higherGenusBetaTwistMultiplier,
        pow_two, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = fzzCigarParityDyadicMellinCharacter rho ^ 2 := by
      rw [higherGenusBetaTwistMultiplier_mellinTorusTwist_eq_dyadicCharacter]

/-- The radial component of the canonical twist is the centered horizontal Mellin weight. -/
theorem fzzCigarParityMellinTorusTwist_im (rho : ℂ) :
    (fzzCigarParityMellinTorusTwist rho).im =
      -(Real.log 2 / (2 * Real.pi)) * (rho.re - 1 / 2) := by
  rw [fzzCigarParityMellinTorusTwist]
  simp only [Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- The canonical twist has no radial monodromy exactly on the critical line. -/
theorem fzzCigarParityMellinTorusTwist_im_eq_zero_iff (rho : ℂ) :
    (fzzCigarParityMellinTorusTwist rho).im = 0 ↔ rho.re = 1 / 2 := by
  rw [fzzCigarParityMellinTorusTwist_im]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : 0 < Real.log 2 / (2 * Real.pi) :=
    div_pos hlog (mul_pos (by norm_num) Real.pi_pos)
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- **Dyadic Mellin same-CFT selector.** The physical cycle-`1,2` holonomy chamber is exactly the
critical line. This removes the former cross-level common-mode transport premise from FZZ-P. -/
theorem fzzCigarParityMellinCyclePairKreinSign_iff_re_eq_half (rho : ℂ) :
    FZZHigherGenusCyclePairKreinSign 1
        (fzzCigarParityMellinTorusTwist rho) ↔
      rho.re = 1 / 2 := by
  rw [fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero (by norm_num),
    fzzCigarParityMellinTorusTwist_im_eq_zero_iff]

end

end RHTower
