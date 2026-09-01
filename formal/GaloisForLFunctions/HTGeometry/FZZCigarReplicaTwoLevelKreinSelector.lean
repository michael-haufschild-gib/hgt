import GaloisForLFunctions.HTGeometry.FZZCigarReplicaKreinScale

/-!
# Two finite FZZ cigar levels select imaginary-axis frequency

The finite-level replica response scale is `β(a)=2a/(1-2a)`, with `a=1/k`.  The integer
cigar levels `k=4` and `k=3` therefore produce the exact scales `1` and `2`.

The existing selector used the passive Krein chamber at every physical level, while the sharp
fixed-level theorem gave an off-axis blind point at each single level.  This file proves the exact
finite replacement: level-four reality and level-three nonpositivity already force `ω.re = 0`.
Thus full passive chambers at these two levels are equivalent to imaginary-axis frequency and are
cardinality-minimal among level families.

The mechanism is scale doubling.  Reality of `sinh(ω/2)^2` implies
`sinh(ω.re) * sin(ω.im)=0`.  Off axis this forces `sin(ω.im)=0`, after which
`sinh(ω)^2` is strictly positive real, contradicting level-three passivity.

## RH-chain scope

For FZZ-P this replaces the premise “one common divisor mode is transported through every finite
cigar level” by the two explicit levels `k=3,4`.  The remaining physical premise is a
source-faithful common-mode transport/crossing law between those two CFTs; no such transport is
assumed here.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry.FZZCigar

noncomputable section

private lemma real_sinh_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.sinh x ≠ 0 := by
  intro hs
  rw [Real.sinh_eq] at hs
  have he : Real.exp x = Real.exp (-x) := by linarith
  have hxneg : x = -x := Real.exp_injective he
  apply hx
  linarith

private lemma complex_sinh_re_local (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_sinh_im_local (z : ℂ) :
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have h : Complex.sinh z
      = ((Real.sinh z.re * Real.cos z.im : ℝ) : ℂ)
        + ((Real.cosh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    push_cast
    ring
  rw [h, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private lemma complex_sinh_sq_im_local (z : ℂ) :
    ((Complex.sinh z) ^ 2).im =
      Real.sinh (2 * z.re) * Real.sin (2 * z.im) / 2 := by
  rw [pow_two, Complex.mul_im, complex_sinh_re_local, complex_sinh_im_local,
    Real.sinh_two_mul, Real.sin_two_mul]
  ring

/-- Passive square chamber at one finite FZZ replica level. -/
def FZZReplicaLevelKreinSign (a : ℝ) (ω : ℂ) : Prop :=
  ((Complex.sinh
    (((replicaLinearizedDressingScale a : ℝ) : ℂ) * ω / 2)) ^ 2).im = 0 ∧
  ((Complex.sinh
    (((replicaLinearizedDressingScale a : ℝ) : ℂ) * ω / 2)) ^ 2).re ≤ 0

/-- Cigar level `k=3` has replica response scale `2`. -/
theorem replicaLinearizedDressingScale_one_third :
    replicaLinearizedDressingScale (1 / 3 : ℝ) = 2 := by
  norm_num [replicaLinearizedDressingScale]

/-- Cigar level `k=4` has replica response scale `1`. -/
theorem replicaLinearizedDressingScale_one_fourth :
    replicaLinearizedDressingScale (1 / 4 : ℝ) = 1 := by
  norm_num [replicaLinearizedDressingScale]

/-- Minimal asymmetric selector: level four supplies reality and level three supplies the sign. -/
def FZZReplicaLevelFourRealityLevelThreeNonpositive (ω : ℂ) : Prop :=
  ((Complex.sinh
    (((replicaLinearizedDressingScale (1 / 4 : ℝ) : ℝ) : ℂ) * ω / 2)) ^ 2).im = 0 ∧
  ((Complex.sinh
    (((replicaLinearizedDressingScale (1 / 3 : ℝ) : ℝ) : ℂ) * ω / 2)) ^ 2).re ≤ 0

/-- Joint passive chamber at the two integer cigar levels `k=3,4`. -/
def FZZReplicaLevelsThreeFourKreinSign (ω : ℂ) : Prop :=
  FZZReplicaLevelKreinSign (1 / 3 : ℝ) ω ∧
    FZZReplicaLevelKreinSign (1 / 4 : ℝ) ω

/-- **Minimal two-level FZZ selector.** Level-four reality plus level-three nonpositivity is
equivalent to imaginary-axis frequency. -/
theorem fzzReplicaLevelFourRealityLevelThreeNonpositive_iff_re_eq_zero (ω : ℂ) :
    FZZReplicaLevelFourRealityLevelThreeNonpositive ω ↔ ω.re = 0 := by
  constructor
  · rintro ⟨hfourReality, hthreeNonpositive⟩
    rw [replicaLinearizedDressingScale_one_fourth] at hfourReality
    rw [replicaLinearizedDressingScale_one_third] at hthreeNonpositive
    by_contra hre
    have hsinh_ne : Real.sinh ω.re ≠ 0 :=
      real_sinh_ne_zero_of_ne_zero hre
    have harg_one : ((((1 : ℝ) : ℂ) * ω) / 2) = ω / 2 := by
      norm_num
    have hhalf_im :
        ((Complex.sinh ((((1 : ℝ) : ℂ) * ω) / 2)) ^ 2).im =
          Real.sinh ω.re * Real.sin ω.im / 2 := by
      rw [harg_one, complex_sinh_sq_im_local]
      norm_num [Complex.div_re, Complex.div_im]
      congr 2 <;> ring
    have hprod : Real.sinh ω.re * Real.sin ω.im = 0 := by
      rw [hhalf_im] at hfourReality
      linarith
    have hsin : Real.sin ω.im = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hsinh_ne
    have harg_two : ((((2 : ℝ) : ℂ) * ω) / 2) = ω := by norm_num
    rw [harg_two] at hthreeNonpositive
    have hsre : (Complex.sinh ω).re =
        Real.sinh ω.re * Real.cos ω.im := complex_sinh_re_local ω
    have hsim : (Complex.sinh ω).im = 0 := by
      rw [complex_sinh_im_local, hsin, mul_zero]
    have hsqre : ((Complex.sinh ω) ^ 2).re = Real.sinh ω.re ^ 2 := by
      rw [pow_two, Complex.mul_re, hsre, hsim]
      have htrig := Real.sin_sq_add_cos_sq ω.im
      rw [hsin] at htrig
      nlinarith
    have hpos : 0 < ((Complex.sinh ω) ^ 2).re := by
      rw [hsqre]
      positivity
    exact (not_lt_of_ge hthreeNonpositive hpos).elim
  · intro hre
    have hall :=
      (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mpr hre
    rw [FZZReplicaLevelFourRealityLevelThreeNonpositive,
      replicaLinearizedDressingScale_one_fourth,
      replicaLinearizedDressingScale_one_third]
    exact ⟨(hall 1 (by norm_num)).1, (hall 2 (by norm_num)).2⟩

/-- **Two-level FZZ selection.** Full passive chambers at levels `k=3,4` are equivalent to
imaginary-axis frequency. Together with the fixed-level blind-point theorem, two levels are
cardinality-minimal. -/
theorem fzzReplicaLevelsThreeFourKreinSign_iff_re_eq_zero (ω : ℂ) :
    FZZReplicaLevelsThreeFourKreinSign ω ↔ ω.re = 0 := by
  constructor
  · rintro ⟨hthree, hfour⟩
    apply (fzzReplicaLevelFourRealityLevelThreeNonpositive_iff_re_eq_zero ω).mp
    exact ⟨hfour.1, hthree.2⟩
  · intro hre
    have hall :=
      (GaloisForLFunctions.hawkingTemperatureUniversalKreinSign_iff_re_eq_zero ω).mpr hre
    constructor
    · rw [FZZReplicaLevelKreinSign,
        replicaLinearizedDressingScale_one_third]
      exact hall 2 (by norm_num)
    · rw [FZZReplicaLevelKreinSign,
        replicaLinearizedDressingScale_one_fourth]
      exact hall 1 (by norm_num)

end

end GaloisForLFunctions.HTGeometry.FZZCigar
