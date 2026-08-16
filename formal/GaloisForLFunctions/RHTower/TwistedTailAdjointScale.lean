import GaloisForLFunctions.RHTower.AdjointCellQuotientScale
import GaloisForLFunctions.RHTower.GaugeCovariantPrimitiveLadder
import GaloisForLFunctions.HTGeometry.CpowHarmonicTailAsymptotic

/-!
# The twisted tail of a displaced mode against the adjoint cell quotient

A constant-frequency phase gauge multiplies a power source into a single complex power:
`e^{i(τ log x + c)}·x^β = e^{ic}·x^{β + iτ}`.  So the covariant source tail of a displaced mode
against a Mellin twist is the oscillatory harmonic tail at the complex exponent `s = β + iτ`, and
the sharp tail asymptotic gives

`(H(g R))_n ∼ -c·g(n)·n^{β-1}/(1 - β - iτ)`.

Only the constant is rotated: the real decay exponent stays `β - 1`.  Multiplied by the adjoint
cell quotient, whose modulus is `(1+o(1))√n·|S(log n)|`, the product carries the exponent
`β - 1/2` exactly, as in the untwisted case.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The Mellin twist turns a real power into a complex power. -/
theorem mellinTwistGauge_mul_cpow {tau cph beta x : ℝ} (hx : 0 < x) :
    mellinTwistGauge tau cph x * ((x : ℝ) : ℂ) ^ ((beta : ℝ) : ℂ)
      = Complex.exp (Complex.I * (cph : ℂ))
        * ((x : ℝ) : ℂ) ^ (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx)
  have hlog : Complex.log ((x : ℝ) : ℂ) = ((Real.log x : ℝ) : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  have htwist : ((x : ℝ) : ℂ) ^ (((tau : ℝ) : ℂ) * Complex.I)
      = Complex.exp (Complex.I * ((tau * Real.log x : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hxne, hlog]
    congr 1
    push_cast
    ring
  rw [Complex.cpow_add _ _ hxne, htwist, mellinTwistGauge]
  have hsum : Complex.I * ((tau * Real.log x + cph : ℝ) : ℂ)
      = Complex.I * ((tau * Real.log x : ℝ) : ℂ) + Complex.I * ((cph : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum, Complex.exp_add]
  ring

/-- The covariant source tail of a displaced power mode against a Mellin twist. -/
def twistedDisplacedTail (beta tau cph : ℝ) (amp : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, mellinTwistGauge tau cph ((N : ℝ) + 1 + (k : ℝ))
    * (amp * (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ ((beta : ℝ) : ℂ))
    * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)

theorem twistedDisplacedTail_eq {beta tau cph : ℝ} (amp : ℂ) (N : ℕ) :
    twistedDisplacedTail beta tau cph amp N
      = amp * Complex.exp (Complex.I * (cph : ℂ))
        * GaloisForLFunctions.HTGeometry.cpowHarmonicTail
            (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I) N := by
  rw [twistedDisplacedTail, GaloisForLFunctions.HTGeometry.cpowHarmonicTail, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx : (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by linarith
  have h := mellinTwistGauge_mul_cpow (tau := tau) (cph := cph) (beta := beta) hx
  calc mellinTwistGauge tau cph ((N : ℝ) + 1 + (k : ℝ))
        * (amp * (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ ((beta : ℝ) : ℂ))
        * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)
      = amp * ((mellinTwistGauge tau cph ((N : ℝ) + 1 + (k : ℝ))
          * (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ ((beta : ℝ) : ℂ))
          * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)) := by
        ring
    _ = amp * Complex.exp (Complex.I * (cph : ℂ))
          * ((((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ)
              ^ (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I)
            * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)) := by
        rw [h]
        ring

theorem mellinTwistGauge_natCast {tau cph : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    mellinTwistGauge tau cph (N : ℝ)
      = Complex.exp (Complex.I * (cph : ℂ)) * ((N : ℝ) : ℂ) ^ (((tau : ℝ) : ℂ) * Complex.I) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h := mellinTwistGauge_mul_cpow (tau := tau) (cph := cph) (beta := (0 : ℝ)) hN0
  simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one, zero_add] at h
  exact h

/-- **(24.84) The twisted tail of a displaced mode.**  The Mellin twist only rotates the constant:
`n^{1-β}·(H(gR))_n/g(n) → amp/(1 - β - iτ)`. -/
theorem tendsto_twistedDisplacedTail {beta tau cph : ℝ} (hbeta : beta < 1) (amp : ℂ) :
    Tendsto (fun N : ℕ => (((N : ℝ) ^ (1 - beta) : ℝ) : ℂ)
        * (twistedDisplacedTail beta tau cph amp N / mellinTwistGauge tau cph (N : ℝ)))
      atTop (𝓝 (amp / (1 - (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I)))) := by
  set s : ℂ := ((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I with hsdef
  have hsre : s.re = beta := by
    rw [hsdef]
    simp
  have hmain := (GaloisForLFunctions.HTGeometry.tendsto_cpowHarmonicTail
    (s := s) (by rw [hsre]; exact hbeta)).const_mul amp
  have hval : amp * (1 / (1 - s)) = amp / (1 - s) := by ring
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hN0)
  have hexpne : Complex.exp (Complex.I * (cph : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have htwne : ((N : ℝ) : ℂ) ^ (((tau : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hNne]
    exact Complex.exp_ne_zero _
  rw [twistedDisplacedTail_eq, mellinTwistGauge_natCast hN, Complex.ofReal_cpow hN0.le]
  have hsplit : ((1 - beta : ℝ) : ℂ) = (1 - s) + ((tau : ℝ) : ℂ) * Complex.I := by
    rw [hsdef]
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ hNne]
  field_simp
  ring

/-- **(24.84) The twisted tail against the adjoint cell quotient carries the exponent `β - 1/2`.**
The Mellin twist rotates the constant only, so the scale of the product is exactly the untwisted
one: smooth receiver-phase adaptation merely moves the oscillation from receiver to source. -/
theorem tendsto_norm_twistedDisplacedTail_mul_adjointCellQuotient
    {beta tau cph : ℝ} (hbeta : beta < 1) (amp : ℂ)
    {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hunif : UniformContinuous fun h => F h / 2 - F' h)
    {cf : ℝ} (hcf : 0 < cf)
    (hfloor : ∀ᶠ n : ℕ in atTop, cf ≤ |F (Real.log (n : ℝ)) / 2 - F' (Real.log (n : ℝ))|) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 2 - beta)
        / |F (Real.log (N : ℝ)) / 2 - F' (Real.log (N : ℝ))|
        * (‖twistedDisplacedTail beta tau cph amp N‖
            * |adjointCellQuotient
                (fun m => Real.exp (-Real.log (m : ℝ) / 2) * F (Real.log (m : ℝ))) N|))
      atTop (𝓝 (‖amp‖ / ‖1 - (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I)‖)) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - beta)
      * ‖twistedDisplacedTail beta tau cph amp N‖) atTop
      (𝓝 (‖amp‖ / ‖1 - (((beta : ℝ) : ℂ) + ((tau : ℝ) : ℂ) * Complex.I)‖)) := by
    have h := (tendsto_twistedDisplacedTail (beta := beta) (tau := tau) (cph := cph)
      hbeta amp).norm
    rw [norm_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [norm_mul, norm_div, norm_mellinTwistGauge, div_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
  have h2 : Tendsto (fun N : ℕ =>
      |adjointCellQuotient
          (fun m => Real.exp (-Real.log (m : ℝ) / 2) * F (Real.log (m : ℝ))) N|
        / (Real.sqrt (N : ℝ) * |F (Real.log (N : ℝ)) / 2 - F' (Real.log (N : ℝ))|)) atTop
      (𝓝 1) := by
    have h := (tendsto_adjointCellQuotient_div_sqrt hF hunif hcf hfloor).abs
    rw [abs_one] at h
    refine h.congr fun N => ?_
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hprod := h1.mul h2
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hfloor] with N hN hfl
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs0 : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN0
  have hSne : |F (Real.log (N : ℝ)) / 2 - F' (Real.log (N : ℝ))| ≠ 0 := by
    intro h
    rw [h] at hfl
    linarith
  have hkey : (N : ℝ) ^ (1 - beta) / Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 - beta) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN0]
    congr 1
    ring
  have halg : ∀ a t A r sh : ℝ, r ≠ 0 → sh ≠ 0 →
      a * t * (A / (r * sh)) = a / r / sh * (t * A) := by
    intro a t A r sh hr hsh
    field_simp
  rw [halg _ _ _ _ _ (ne_of_gt hs0) hSne, hkey]


end

end RHTower
