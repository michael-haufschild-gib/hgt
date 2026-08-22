import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The uncompleted local Euler ratio carries a singular Blaschke factor

Write `L = log p` and `t = p^c`, so that the deformed local Euler ratio at a prime `p` is

`ρ(z) = (1 - t p^{z-1}) / (1 - t p^{-z}) = (1 - e^{L(z+c-1)}) / (1 - e^{L(c-z)})`

and the associated hyperbolic factor is

`B(z) = sinh(L(z-c)/2) / sinh(L(z+c-1)/2)`.

Their product is the singular inner function `-p^{z-1/2}`, exactly and for every parameter:

`(1 - e^{L(z+c-1)}) · sinh(L(z-c)/2) = -e^{L(z-1/2)} · (1 - e^{L(c-z)}) · sinh(L(z+c-1)/2)`.

Hence as the local parameter degenerates the hyperbolic factor tends to `-p^{z-1/2}`, not to `1`:
the kernel of the *uncompleted* local Hankel operator does not furnish the empty-parameter tangent.
-/

namespace RHTower

open Complex

noncomputable section

/-- The numerator `1 - t p^{z-1}` of the deformed local Euler ratio. -/
def localEulerNumerator (L c z : ℂ) : ℂ := 1 - Complex.exp (L * (z + c - 1))

/-- The denominator `1 - t p^{-z}` of the deformed local Euler ratio. -/
def localEulerDenominator (L c z : ℂ) : ℂ := 1 - Complex.exp (L * (c - z))

/-- The hyperbolic factor `B(z) = sinh(L(z-c)/2)/sinh(L(z+c-1)/2)`. -/
def localEulerBlaschke (L c z : ℂ) : ℂ :=
  Complex.sinh (L * (z - c) / 2) / Complex.sinh (L * (z + c - 1) / 2)

private theorem exp_two_mul (w : ℂ) : Complex.exp (2 * w) = Complex.exp w ^ 2 := by
  rw [two_mul, Complex.exp_add]; ring

/-- **`(18)`: the exact local Euler--Blaschke identity, in division-free form.** -/
theorem localEuler_blaschke_identity (L c z : ℂ) :
    localEulerNumerator L c z * Complex.sinh (L * (z - c) / 2)
      = -Complex.exp (L * (z - 1 / 2)) * localEulerDenominator L c z *
        Complex.sinh (L * (z + c - 1) / 2) := by
  set a : ℂ := Complex.exp (L * z / 2) with ha
  set b : ℂ := Complex.exp (L * c / 2) with hb
  set g : ℂ := Complex.exp (L / 2) with hg
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have hb0 : b ≠ 0 := Complex.exp_ne_zero _
  have hg0 : g ≠ 0 := Complex.exp_ne_zero _
  have E1 : Complex.exp (L * (z + c - 1)) = a ^ 2 * b ^ 2 / g ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hg0), ha, hb, hg, ← exp_two_mul, ← exp_two_mul, ← exp_two_mul,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have E2 : Complex.exp (L * (c - z)) = b ^ 2 / a ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 ha0), ha, hb, ← exp_two_mul, ← exp_two_mul, ← Complex.exp_add]
    congr 1
    ring
  have E3 : Complex.exp (L * (z - 1 / 2)) = a ^ 2 / g := by
    rw [eq_div_iff hg0, ha, hg, ← exp_two_mul, ← Complex.exp_add]
    congr 1
    ring
  have S1 : Complex.sinh (L * (z - c) / 2) = (a / b - b / a) / 2 := by
    rw [Complex.sinh, ha, hb, ← Complex.exp_sub, ← Complex.exp_sub]
    congr 2 <;> [skip; skip] <;> ring_nf
  have S2 : Complex.sinh (L * (z + c - 1) / 2) = (a * b / g - g / (a * b)) / 2 := by
    have hab : a * b = Complex.exp (L * z / 2 + L * c / 2) := by
      rw [ha, hb, Complex.exp_add]
    rw [Complex.sinh, hab, hg, ← Complex.exp_sub, ← Complex.exp_sub]
    congr 2 <;> ring_nf
  rw [localEulerNumerator, localEulerDenominator, E1, E2, E3, S1, S2]
  field_simp
  ring

/-- The complex hyperbolic sine vanishes only on the imaginary axis. -/
theorem sinh_ne_zero_of_re_ne_zero {w : ℂ} (h : w.re ≠ 0) : Complex.sinh w ≠ 0 := by
  intro hzero
  rw [Complex.sinh, div_eq_zero_iff] at hzero
  rcases hzero with hz | hz
  · have heq : Complex.exp w = Complex.exp (-w) := sub_eq_zero.mp hz
    have hnorm : Real.exp w.re = Real.exp (-w.re) := by
      have := congrArg (fun u : ℂ => ‖u‖) heq
      simpa [Complex.norm_exp] using this
    exact h (by linarith [Real.exp_injective hnorm])
  · exact absurd hz (by norm_num)

/-- The divided form of the identity. -/
theorem localEulerBlaschke_eq (L c z : ℂ)
    (hnum : localEulerNumerator L c z ≠ 0)
    (hsinh : Complex.sinh (L * (z + c - 1) / 2) ≠ 0) :
    localEulerBlaschke L c z
      = -Complex.exp (L * (z - 1 / 2)) * localEulerDenominator L c z /
          localEulerNumerator L c z := by
  have hid := localEuler_blaschke_identity L c z
  rw [localEulerBlaschke, div_eq_div_iff hsinh hnum]
  rw [eq_comm, ← sub_eq_zero]
  have : Complex.sinh (L * (z - c) / 2) * localEulerNumerator L c z
      = -Complex.exp (L * (z - 1 / 2)) * localEulerDenominator L c z *
        Complex.sinh (L * (z + c - 1) / 2) := by
    rw [mul_comm]; exact hid
  rw [this]
  ring

/-- The deformed exponential vanishes in the degenerate limit. -/
theorem tendsto_exp_localEuler_atBot (L : ℝ) (hL : 0 < L) (w : ℂ) :
    Filter.Tendsto (fun c : ℝ => Complex.exp ((L : ℂ) * ((c : ℂ) + w))) Filter.atBot (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hre : ∀ c : ℝ, ‖Complex.exp ((L : ℂ) * ((c : ℂ) + w))‖ = Real.exp (L * (c + w.re)) := by
    intro c
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.add_re]
  simp only [hre]
  have hlin : Filter.Tendsto (fun c : ℝ => L * (c + w.re)) Filter.atBot Filter.atBot := by
    have h1 : Filter.Tendsto (fun c : ℝ => c + w.re) Filter.atBot Filter.atBot :=
      Filter.tendsto_atBot_add_const_right _ _ Filter.tendsto_id
    exact h1.const_mul_atBot hL
  exact Real.tendsto_exp_atBot.comp hlin

/-- **The degenerate limit of the hyperbolic factor is the singular inner function
`-p^{z-1/2}`, not `1`.** -/
theorem tendsto_localEulerBlaschke_atBot (L : ℝ) (hL : 0 < L) (z : ℂ) :
    Filter.Tendsto (fun c : ℝ => localEulerBlaschke (L : ℂ) (c : ℂ) z) Filter.atBot
      (nhds (-Complex.exp ((L : ℂ) * (z - 1 / 2)))) := by
  have hnumexp : Filter.Tendsto
      (fun c : ℝ => Complex.exp ((L : ℂ) * (z + (c : ℂ) - 1))) Filter.atBot (nhds 0) := by
    have := tendsto_exp_localEuler_atBot L hL (z - 1)
    refine this.congr fun c => ?_
    congr 1
    ring
  have hdenexp : Filter.Tendsto
      (fun c : ℝ => Complex.exp ((L : ℂ) * ((c : ℂ) - z))) Filter.atBot (nhds 0) := by
    have := tendsto_exp_localEuler_atBot L hL (-z)
    refine this.congr fun c => ?_
    congr 1
  have hnum : Filter.Tendsto (fun c : ℝ => localEulerNumerator (L : ℂ) (c : ℂ) z)
      Filter.atBot (nhds 1) := by
    simpa [localEulerNumerator] using (tendsto_const_nhds (x := (1 : ℂ))).sub hnumexp
  have hden : Filter.Tendsto (fun c : ℝ => localEulerDenominator (L : ℂ) (c : ℂ) z)
      Filter.atBot (nhds 1) := by
    simpa [localEulerDenominator] using (tendsto_const_nhds (x := (1 : ℂ))).sub hdenexp
  have hnumne : ∀ᶠ c : ℝ in Filter.atBot, localEulerNumerator (L : ℂ) (c : ℂ) z ≠ 0 :=
    hnum.eventually_ne one_ne_zero
  have hsinhne : ∀ᶠ c : ℝ in Filter.atBot,
      Complex.sinh ((L : ℂ) * (z + (c : ℂ) - 1) / 2) ≠ 0 := by
    filter_upwards [Filter.eventually_lt_atBot (1 - z.re)] with c hc
    refine sinh_ne_zero_of_re_ne_zero ?_
    have hre : (((L : ℂ) * (z + (c : ℂ) - 1) / 2)).re = L * (z.re + c - 1) / 2 := by
      simp [Complex.mul_re, Complex.add_re, Complex.sub_re]
    rw [hre]
    have : z.re + c - 1 < 0 := by linarith
    nlinarith
  have hcongr : ∀ᶠ c : ℝ in Filter.atBot,
      localEulerBlaschke (L : ℂ) (c : ℂ) z
        = -Complex.exp ((L : ℂ) * (z - 1 / 2)) * localEulerDenominator (L : ℂ) (c : ℂ) z /
            localEulerNumerator (L : ℂ) (c : ℂ) z := by
    filter_upwards [hnumne, hsinhne] with c h1 h2
    exact localEulerBlaschke_eq _ _ _ h1 h2
  have hlimit : Filter.Tendsto
      (fun c : ℝ => -Complex.exp ((L : ℂ) * (z - 1 / 2)) * localEulerDenominator (L : ℂ) (c : ℂ) z /
        localEulerNumerator (L : ℂ) (c : ℂ) z) Filter.atBot
      (nhds (-Complex.exp ((L : ℂ) * (z - 1 / 2)))) := by
    have := ((tendsto_const_nhds
      (x := -Complex.exp ((L : ℂ) * (z - 1 / 2)))).mul hden).div hnum one_ne_zero
    simpa [Pi.div_def] using this
  exact hlimit.congr' (hcongr.mono fun c h => h.symm)

end

end RHTower
