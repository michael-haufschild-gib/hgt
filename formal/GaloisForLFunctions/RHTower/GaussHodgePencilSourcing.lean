import GaloisForLFunctions.RHTower.GaussHodgeVerticalExtraction

/-!
# Sourcing the vertical pencil: the FE companion, and sourcing ⟺ RH

The last unproven step of the Hodge mass programme asks for the values of the vertical pencil
`Σ_ρ v_ρ · char_p(ρ) · e^{i n Im ρ}` from prime-side data.  The vertical mode `e^{i Im ρ}` is
non-holomorphic; but it has a holomorphic **FE companion** `e^{ρ - 1/2}`, and the companion
pencil is exactly prime-side data:

`char_p(ρ) · (e^{ρ-1/2})^n = char_{p·eⁿ}(ρ)` — the one-variable zero current at the flowed
scale `p·eⁿ`, the object the explicit formula evaluates.  The companion factors as the
vertical mode times the radial factor `e^{t/2}` at the centered rate `t = 2·Re - 1`: the
discrepancy between the sourced pencil and the wanted pencil is *again the mass rate*, and it
vanishes at a copy exactly on the critical line.  Consequently:

**RH ⟺ the FE companion equals the vertical mode at every copy ⟺ the companion is unimodular
on the divisor** — the sourcing problem is itself the Riemann hypothesis, in exact pointwise
mode form.  Under RH the whole vertical pencil collapses to the flowed-scale zero currents:
every value the extraction machine needs is then explicit-formula data.

This closes the programme into a single equivalence loop, every link an unconditional
theorem: sign, mass = seam energy, prime-side moment-curve evaluation, ℓ¹ extraction and
truncation, positivity, and now sourcing ⟺ RH.  The one non-circular entry point that
remains is an independent evaluation of the vertical pencil — which, by the formalized
information-gap and interface firewalls, must consume bilinear (conjugate-pair) input.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The holomorphic FE companion of the vertical mode of a divisor copy. -/
def xiZeroCopyFEMode (q : XiZeroCopy) : ℂ :=
  Complex.exp ((q.1 : ℂ) - 1 / 2)

/-- The companion's modulus is the exponentiated half centered rate: the radial sourcing
defect is the mass rate. -/
theorem norm_xiZeroCopyFEMode (q : XiZeroCopy) :
    ‖xiZeroCopyFEMode q‖ =
      Real.exp (primeDepthBVWoldXiCenteredRate q.1 / 2) := by
  rw [xiZeroCopyFEMode, Complex.norm_exp]
  congr 1
  have h : ((q.1 : ℂ) - 1 / 2).re = ((q.1 : ℂ)).re - 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by norm_num, Complex.sub_re,
      Complex.ofReal_re]
  rw [h, primeDepthBVWoldXiCenteredRate]
  ring

/-- Polar factorization of the companion: vertical mode times the radial mass factor. -/
theorem xiZeroCopyFEMode_polar (q : XiZeroCopy) :
    xiZeroCopyFEMode q =
      ((Real.exp (primeDepthBVWoldXiCenteredRate q.1 / 2) : ℝ) : ℂ) *
        xiZeroCopyVerticalMode q := by
  rw [xiZeroCopyFEMode, xiZeroCopyVerticalMode, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [primeDepthBVWoldXiCenteredRate]
  apply Complex.ext
  · push_cast
    simp [Complex.add_re, Complex.mul_re]
    ring
  · push_cast
    simp [Complex.add_im, Complex.mul_im]

/-- **The sourcing identity.**  The FE-flowed character is the character at the flowed scale:
the companion pencil is the one-variable zero current at `p·eⁿ` — prime-side data. -/
theorem burnolPrimeCharacter_mul_feFlow {p : ℝ} (hp : 0 < p) (s : ℂ) (n : ℕ) :
    burnolPrimeCharacter p s * Complex.exp (s - 1 / 2) ^ n =
      burnolPrimeCharacter (p * Real.exp n) s := by
  have hpe : (0 : ℝ) < p * Real.exp n := mul_pos hp (Real.exp_pos _)
  rw [burnolPrimeCharacter_eq_exp p hp s, burnolPrimeCharacter_eq_exp _ hpe s,
    ← Complex.exp_nat_mul, ← Complex.exp_add,
    Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 1
  push_cast
  ring

/-- The sourcing identity at a divisor copy. -/
theorem burnolPrimeCharacter_mul_feMode_pow {p : ℝ} (hp : 0 < p)
    (q : XiZeroCopy) (n : ℕ) :
    burnolPrimeCharacter p ((q.1 : ℂ)) * xiZeroCopyFEMode q ^ n =
      burnolPrimeCharacter (p * Real.exp n) ((q.1 : ℂ)) :=
  burnolPrimeCharacter_mul_feFlow hp ((q.1 : ℂ)) n

/-- **Sourcing ⟺ RH, pointwise mode form.**  The FE companion agrees with the vertical mode
at every copy exactly when the Riemann hypothesis holds: the last unproven step of the chain
is itself RH. -/
theorem riemannHypothesis_iff_feMode_eq_verticalMode :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy, xiZeroCopyFEMode q = xiZeroCopyVerticalMode q := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  refine forall_congr' fun q => ?_
  rw [orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two]
  constructor
  · intro h
    rw [xiZeroCopyFEMode_polar]
    have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 := by
      rw [primeDepthBVWoldXiCenteredRate, h]
      ring
    rw [hrate]
    norm_num
  · intro h
    have hnorm := congrArg norm h
    rw [norm_xiZeroCopyFEMode, norm_xiZeroCopyVerticalMode] at hnorm
    rw [← Real.exp_zero] at hnorm
    have hzero : primeDepthBVWoldXiCenteredRate q.1 / 2 = 0 := Real.exp_eq_exp.mp hnorm
    have := hzero
    rw [primeDepthBVWoldXiCenteredRate] at this
    linarith

/-- **Sourcing ⟺ RH, unimodularity form.** -/
theorem riemannHypothesis_iff_feMode_unimodular :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, ‖xiZeroCopyFEMode q‖ = 1 := by
  rw [riemannHypothesis_iff_feMode_eq_verticalMode]
  refine forall_congr' fun q => ?_
  constructor
  · intro h
    rw [h, norm_xiZeroCopyVerticalMode]
  · intro h
    rw [norm_xiZeroCopyFEMode, ← Real.exp_zero] at h
    have hzero : primeDepthBVWoldXiCenteredRate q.1 / 2 = 0 := Real.exp_eq_exp.mp h
    rw [xiZeroCopyFEMode_polar, hzero]
    norm_num

/-- **Under RH the vertical pencil is prime-sourced.**  Every value of the vertical pencil is
the weighted one-variable zero current at the flowed scale `p·eⁿ` — explicit-formula data. -/
theorem verticalPencil_eq_flowedScaleCurrent_of_riemannHypothesis
    (hRH : RiemannHypothesis) {p : ℝ} (hp : 0 < p)
    (v : XiZeroCopy → ℂ) (n : ℕ) :
    (∑' q : XiZeroCopy,
        v q * burnolPrimeCharacter p ((q.1 : ℂ)) * xiZeroCopyVerticalMode q ^ n) =
      ∑' q : XiZeroCopy, v q * burnolPrimeCharacter (p * Real.exp n) ((q.1 : ℂ)) := by
  apply tsum_congr
  intro q
  rw [← (riemannHypothesis_iff_feMode_eq_verticalMode.mp hRH q), mul_assoc,
    burnolPrimeCharacter_mul_feMode_pow hp q n]

end

end RHTower
