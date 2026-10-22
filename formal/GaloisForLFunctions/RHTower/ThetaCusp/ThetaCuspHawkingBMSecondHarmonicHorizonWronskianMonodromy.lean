import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicProjectiveCausalNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonFrobeniusMonodromy

/-!
# BM second-harmonic horizon Wronskian and monodromy

The complementary `++` Frobenius branch has exponent `4n + 3 + 2iχ`. Its exact BM integrating
factor cancels the singular radial power in the leading Wronskian, leaving
`λ * sqrt (1 - z)` and horizon limit `λ`.

Counterclockwise and clockwise continuations multiply this branch by `exp (-4πχ)` and
`exp (4πχ)`. Their oriented difference is nonzero whenever `χ.re ≠ 0`, hence on every Xi fibre.
This closes a possible false endpoint: second-harmonic monodromy is causal horizon data, not an RH
selector.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Complementary Frobenius exponent of the causal BM `++` second harmonic. -/
def d4BMPlusPlusComplementaryFrobeniusExponent
    (n : ℕ) (chi : ℂ) : ℂ :=
  1 - d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)

/-- Exact affine form of the complementary `++` Frobenius exponent. -/
theorem d4BMPlusPlusComplementaryFrobeniusExponent_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryFrobeniusExponent n chi =
      4 * (n : ℂ) + 3 + 2 * Complex.I * chi := by
  simp [d4BMPlusPlusComplementaryFrobeniusExponent,
    d4BMCausalRadialC, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Leading complementary `++` Frobenius branch on the positive radial interval. -/
def d4BMPlusPlusLeadingComplementaryFrobeniusBranch
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  Complex.exp
    (d4BMPlusPlusComplementaryFrobeniusExponent n chi * (Real.log z : ℂ))

/-- Algebraic derivative assigned to the leading complementary Frobenius branch. -/
def d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusComplementaryFrobeniusExponent n chi *
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi z / (z : ℂ)

/-- The assigned branch derivative is the actual real derivative away from the horizon. -/
theorem hasDerivAt_d4BMPlusPlusLeadingComplementaryFrobeniusBranch
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (d4BMPlusPlusLeadingComplementaryFrobeniusBranch n chi)
      (d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z) z := by
  have hlogR : HasDerivAt Real.log z⁻¹ z := Real.hasDerivAt_log hz
  have hlogC : HasDerivAt (fun x : ℝ => (Real.log x : ℂ))
      ((z⁻¹ : ℝ) : ℂ) z := hlogR.ofReal_comp
  have h := (hlogC.const_mul
    (d4BMPlusPlusComplementaryFrobeniusExponent n chi)).cexp
  rw [d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative]
  change HasDerivAt
    (fun x : ℝ => Complex.exp
      (d4BMPlusPlusComplementaryFrobeniusExponent n chi * (Real.log x : ℂ)))
    (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
      Complex.exp
        (d4BMPlusPlusComplementaryFrobeniusExponent n chi * (Real.log z : ℂ)) /
      (z : ℂ)) z
  apply h.congr_deriv
  push_cast
  field_simp

/-- Integrating-factor Wronskian of the regular and complementary leading horizon branches. -/
def d4BMPlusPlusLeadingFrobeniusWronskian
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingFactor n chi z *
    d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative n chi z

/-- Exact cancellation of the Frobenius powers in the normalized `++` horizon Wronskian. -/
theorem d4BMPlusPlusLeadingFrobeniusWronskian_eq
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz : 0 < z) :
    d4BMPlusPlusLeadingFrobeniusWronskian n chi z =
      d4BMPlusPlusComplementaryFrobeniusExponent n chi *
        (Real.sqrt (1 - z) : ℂ) := by
  rw [d4BMPlusPlusLeadingFrobeniusWronskian,
    d4BMPlusPlusIntegratingFactor,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranchDerivative,
    d4BMPlusPlusLeadingComplementaryFrobeniusBranch]
  have hsum :
      d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
          (Real.log z : ℂ) +
        d4BMPlusPlusComplementaryFrobeniusExponent n chi *
          (Real.log z : ℂ) = (Real.log z : ℂ) := by
    rw [d4BMPlusPlusComplementaryFrobeniusExponent]
    ring
  have hexp :
      Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        Complex.exp
          (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
            (Real.log z : ℂ)) = (z : ℂ) := by
    rw [← Complex.exp_add, hsum, ← Complex.ofReal_exp, Real.exp_log hz]
  calc
    Complex.exp
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
            (Real.log z : ℂ)) *
        (Real.sqrt (1 - z) : ℂ) *
          (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
            Complex.exp
              (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
                (Real.log z : ℂ)) / (z : ℂ)) =
      d4BMPlusPlusComplementaryFrobeniusExponent n chi *
        (Real.sqrt (1 - z) : ℂ) *
          (Complex.exp
              (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
                (Real.log z : ℂ)) *
            Complex.exp
              (d4BMPlusPlusComplementaryFrobeniusExponent n chi *
                (Real.log z : ℂ))) / (z : ℂ) := by ring
    _ = d4BMPlusPlusComplementaryFrobeniusExponent n chi *
        (Real.sqrt (1 - z) : ℂ) * (z : ℂ) / (z : ℂ) := by rw [hexp]
    _ = _ := by field_simp [ne_of_gt hz]

/-- The normalized leading `++` Wronskian tends to its complementary exponent at the horizon. -/
theorem tendsto_d4BMPlusPlusLeadingFrobeniusWronskian_zero
    (n : ℕ) (chi : ℂ) :
    Tendsto (d4BMPlusPlusLeadingFrobeniusWronskian n chi)
      (𝓝[>] 0)
      (𝓝 (d4BMPlusPlusComplementaryFrobeniusExponent n chi)) := by
  let lam := d4BMPlusPlusComplementaryFrobeniusExponent n chi
  have heq : d4BMPlusPlusLeadingFrobeniusWronskian n chi =ᶠ[𝓝[Set.Ioi 0] 0]
      fun z : ℝ => lam * (Real.sqrt (1 - z) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact d4BMPlusPlusLeadingFrobeniusWronskian_eq n chi hz
  have ht : Tendsto (fun z : ℝ => lam * (Real.sqrt (1 - z) : ℂ))
      (𝓝 0) (𝓝 lam) := by
    simpa using (show ContinuousAt
      (fun z : ℝ => lam * (Real.sqrt (1 - z) : ℂ)) 0 by fun_prop).tendsto
  exact (ht.mono_left inf_le_left).congr' heq.symm

/-- Counterclockwise lateral multiplier of the complementary `++` horizon branch. -/
def d4BMPlusPlusCounterclockwiseFrobeniusMultiplier
    (n : ℕ) (chi : ℂ) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      d4BMPlusPlusComplementaryFrobeniusExponent n chi)

/-- Clockwise lateral multiplier of the complementary `++` horizon branch. -/
def d4BMPlusPlusClockwiseFrobeniusMultiplier
    (n : ℕ) (chi : ℂ) : ℂ :=
  Complex.exp
    (-(2 * (Real.pi : ℂ) * Complex.I *
      d4BMPlusPlusComplementaryFrobeniusExponent n chi))

/-- Oriented lateral monodromy jump of the complementary `++` horizon branch. -/
def d4BMPlusPlusFrobeniusMonodromyJump
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi -
    d4BMPlusPlusClockwiseFrobeniusMultiplier n chi

/-- Counterclockwise `++` multiplier is the explicit nonunit exponential `exp (-4πχ)`. -/
theorem d4BMPlusPlusCounterclockwiseFrobeniusMultiplier_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi =
      Complex.exp (-4 * (Real.pi : ℂ) * chi) := by
  rw [d4BMPlusPlusCounterclockwiseFrobeniusMultiplier,
    d4BMPlusPlusComplementaryFrobeniusExponent_eq]
  have hsplit :
      2 * (Real.pi : ℂ) * Complex.I *
          (4 * (n : ℂ) + 3 + 2 * Complex.I * chi) =
        (((4 * n + 3 : ℕ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I)) +
          (-4 * (Real.pi : ℂ) * chi) := by
    push_cast
    calc
      2 * (Real.pi : ℂ) * Complex.I *
          (4 * (n : ℂ) + 3 + 2 * Complex.I * chi) =
        2 * (Real.pi : ℂ) * Complex.I * (4 * (n : ℂ) + 3) +
          4 * (Real.pi : ℂ) * (Complex.I * Complex.I) * chi := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hsplit, Complex.exp_add]
  have hint :
      Complex.exp
          (((4 * n + 3 : ℕ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa only [mul_assoc] using
      Complex.exp_nat_mul_two_pi_mul_I (4 * n + 3)
  rw [hint, one_mul]

/-- Clockwise `++` multiplier is the opposite exponential `exp (4πχ)`. -/
theorem d4BMPlusPlusClockwiseFrobeniusMultiplier_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusClockwiseFrobeniusMultiplier n chi =
      Complex.exp (4 * (Real.pi : ℂ) * chi) := by
  change
    Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I *
          d4BMPlusPlusComplementaryFrobeniusExponent n chi)) = _
  rw [Complex.exp_neg]
  change (d4BMPlusPlusCounterclockwiseFrobeniusMultiplier n chi)⁻¹ = _
  rw [d4BMPlusPlusCounterclockwiseFrobeniusMultiplier_eq, ← Complex.exp_neg]
  congr 1
  ring

/-- Exact oriented lateral monodromy jump of the complementary `++` branch. -/
theorem d4BMPlusPlusFrobeniusMonodromyJump_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusFrobeniusMonodromyJump n chi =
      Complex.exp (-4 * (Real.pi : ℂ) * chi) -
        Complex.exp (4 * (Real.pi : ℂ) * chi) := by
  rw [d4BMPlusPlusFrobeniusMonodromyJump,
    d4BMPlusPlusCounterclockwiseFrobeniusMultiplier_eq,
    d4BMPlusPlusClockwiseFrobeniusMultiplier_eq]

/-- Nonresonant `++` monodromy never vanishes when the momentum has nonzero real part. -/
theorem d4BMPlusPlusFrobeniusMonodromyJump_ne_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusFrobeniusMonodromyJump n chi ≠ 0 := by
  rw [d4BMPlusPlusFrobeniusMonodromyJump_eq]
  intro hzero
  have hexp :
      Complex.exp (-4 * (Real.pi : ℂ) * chi) =
        Complex.exp (4 * (Real.pi : ℂ) * chi) := sub_eq_zero.mp hzero
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, Complex.norm_exp] at hnorm
  have hre := Real.exp_injective hnorm
  norm_num [Complex.mul_re] at hre
  apply hchi
  nlinarith [Real.pi_pos]

/-- Every actual Xi fibre has nontrivial complementary `++` horizon monodromy. -/
theorem d4BMXiPlusPlusFrobeniusMonodromyJump_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMPlusPlusFrobeniusMonodromyJump
      n (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
  exact d4BMPlusPlusFrobeniusMonodromyJump_ne_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

end

end RHTower
