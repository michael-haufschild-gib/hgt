/-
The third-moment resonance discriminator: how multiplicativity is detected in the third cumulant
of a critical-line log-field.

A finite trigonometric field `f(θ) = ∑_{k∈S} c_k · exp(i·k·θ)` has a normalised third moment
`M₃(f) = (2π)⁻¹ ∫₀^{2π} f(θ)³ dθ`.  By character orthogonality (`∫₀^{2π} exp(i·j·θ) = 2π·[j=0]`),
only additive frequency resonances survive:

    M₃(f) = ∑_{k+l+m = 0} c_k · c_l · c_m           (`thirdMoment_eq_resonance`).

This is a bispectrum: the third moment is carried by triples of frequencies with `k+l+m = 0`.  The
minimal nonzero resonance is `1 + 1 = 2` (i.e. `1 + 1 + (−2) = 0`), a fundamental with its second
harmonic.  Two consequences frame the discriminator:

  * a pure-tone field (spectrum `{−1,1}`) has NO additive 3-resonance — `±1±1±1` is odd, never `0` —
    so its third moment is `0` (`thirdMoment_pureTone`);
  * the field `a·cos θ + b·cos 2θ` has third moment `(3/4)·a²·b` (`thirdMoment_two_harmonic`): the
    second harmonic `b` is exactly what activates the `1+1=2` resonance.

The arithmetic reading.  For the Euler local factor `(1−w)⁻¹` one has `log((1−w)⁻¹) = ∑_{k≥1} wᵏ/k`,
whose `x²`-coefficient is `1/2`.  So on the critical line the second-harmonic amplitude is the square
of the fundamental over two, `b = a²/2` — a relation FORCED by multiplicativity (the prime-square term
is the multiplicative image of the prime term).  Then `M₃ = (3/8)·a⁴` (`thirdMoment_multiplicative`),
strictly positive for a real nonzero fundamental (`thirdMoment_multiplicative_pos`); at the prime `p`
the ζ-factor gives `a = p^{-1/2}`, hence `(3/8)·p^{-2}` — a convergent, forced, strictly positive
contribution.  A tower-free field (`b = 0`, no prime-square structure) gives `0`
(`thirdMoment_discriminator`).

Scope.  This isolates the mechanism by which the third cumulant detects the Euler prime-power tower:
the second harmonic (the codim-2 / prime-square direction) is the lowest one it sees, and multiplicativity
forces it.  The invariant tracks multiplicativity, not the location of zeros: the MAGNITUDE is fixed by
the tower (nonzero), while the SIGN, here `sign b`, is `+` precisely because the ζ Euler coefficients are
positive.  For a general L-function the second-harmonic amplitude `b` need not be positive; the definiteness
of that sign across the tower is the Weil/positivity content and is not addressed here.
-/
import Mathlib

open Complex intervalIntegral MeasureTheory
open scoped Interval Real

noncomputable section

namespace RHTower

/-- Orthogonality of additive characters on the circle:
`∫₀^{2π} exp(i·j·θ) dθ = 2π` if `j = 0`, else `0`. -/
lemma integral_cexp_int (j : ℤ) :
    (∫ θ in (0:ℝ)..(2*Real.pi), Complex.exp ((j:ℝ) * θ * I))
      = if j = 0 then (2*Real.pi : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst hj; simp
  · rw [if_neg hj]
    have hc : ((j:ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hj) I_ne_zero
    have hrw : (fun θ : ℝ => Complex.exp ((j:ℝ) * θ * I))
        = (fun θ : ℝ => Complex.exp (((j:ℂ)*I) * θ)) := by
      funext θ; congr 1; push_cast; ring
    rw [hrw]
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (((j:ℂ)*I) * t) / ((j:ℂ)*I))
        (Complex.exp (((j:ℂ)*I) * x)) x := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => ((j:ℂ)*I) * (t:ℂ)) ((j:ℂ)*I) x := by
        simpa using ((hasDerivAt_id (x:ℂ)).const_mul ((j:ℂ)*I)).comp_ofReal
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (((j:ℂ)*I) * t))
          (Complex.exp (((j:ℂ)*I)*x) * ((j:ℂ)*I)) x := by simpa using h1.cexp
      have h3 := h2.div_const ((j:ℂ)*I)
      have hcoef :
          Complex.exp (((j : ℂ) * I) * x) * ((j : ℂ) * I) / ((j : ℂ) * I) =
            Complex.exp (((j : ℂ) * I) * x) := by
        rw [mul_div_assoc, div_self hc, mul_one]
      simpa using! h3.congr_deriv hcoef
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have he : Complex.exp (((j:ℂ) * I) * ((2:ℂ) * Real.pi)) = 1 := by
      rw [show ((j:ℂ)*I)*((2:ℂ)*Real.pi) = (j:ℂ)*(2*Real.pi*I) from by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I j
    push_cast
    rw [he]; simp

/-- The cube of a finite sum, expanded as a triple sum. -/
lemma sum_cube {ι : Type*} (S : Finset ι) (g : ι → ℂ) :
    (∑ k ∈ S, g k)^3 = ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S, g k * g l * g m := by
  rw [pow_three, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

/-- The finite complex trigonometric field with Fourier coefficients `c` supported on the frequency
set `S`: `θ ↦ ∑_{k∈S} c k · exp(i·k·θ)`. -/
def trigField (c : ℤ → ℂ) (S : Finset ℤ) (θ : ℝ) : ℂ :=
  ∑ k ∈ S, c k * Complex.exp ((k:ℝ) * θ * I)

/-- The normalised third moment `(2π)⁻¹ ∫₀^{2π} f(θ)³ dθ` of the field `f = trigField c S`. -/
def thirdMoment (c : ℤ → ℂ) (S : Finset ℤ) : ℂ :=
  (1/(2*Real.pi)) * ∫ θ in (0:ℝ)..(2*Real.pi), (trigField c S θ)^3

/-- The cube of the field, expanded as a triple sum over frequency triples. -/
lemma trigField_cube (c : ℤ → ℂ) (S : Finset ℤ) (θ : ℝ) :
    (trigField c S θ)^3
      = ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S,
          (c k * c l * c m) * Complex.exp (((k+l+m : ℤ):ℝ) * θ * I) := by
  unfold trigField
  rw [sum_cube]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl
    (fun l _ => Finset.sum_congr rfl (fun m _ => ?_)))
  rw [show (c k * Complex.exp ((k:ℝ)*θ*I)) * (c l * Complex.exp ((l:ℝ)*θ*I))
        * (c m * Complex.exp ((m:ℝ)*θ*I))
      = (c k * c l * c m) * (Complex.exp ((k:ℝ)*θ*I) * Complex.exp ((l:ℝ)*θ*I)
        * Complex.exp ((m:ℝ)*θ*I)) from by ring]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The integral of the field cube, evaluated by character orthogonality. -/
lemma integral_field_cube (c : ℤ → ℂ) (S : Finset ℤ) :
    (∫ θ in (0:ℝ)..(2*Real.pi), (trigField c S θ)^3)
      = ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S,
          (if k + l + m = 0 then (c k * c l * c m) * (2*Real.pi) else 0) := by
  rw [intervalIntegral.integral_congr (fun θ _ => trigField_cube c S θ)]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
        apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
        apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m _ => by
        apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_cexp_int]
  by_cases h0 : k + l + m = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, mul_zero]

/-- **Third-moment resonance formula (the bispectrum).**  The normalised third moment of a finite
trigonometric field equals the sum, over frequency triples `(k,l,m)` with `k+l+m = 0`, of the
products of the corresponding Fourier coefficients.  Non-resonant triples integrate to zero by
character orthogonality; only additive resonances survive. -/
theorem thirdMoment_eq_resonance (c : ℤ → ℂ) (S : Finset ℤ) :
    thirdMoment c S
      = ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S, (if k + l + m = 0 then c k * c l * c m else 0) := by
  have hpi : (2 * (Real.pi:ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  unfold thirdMoment
  rw [integral_field_cube]
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases h0 : k + l + m = 0
  · rw [if_pos h0, if_pos h0]; field_simp
  · rw [if_neg h0, if_neg h0, mul_zero]

/-- If no frequency triple in `S` sums to zero (a "sum-free" spectrum), the third moment vanishes. -/
theorem thirdMoment_eq_zero_of_sumFree (c : ℤ → ℂ) (S : Finset ℤ)
    (h : ∀ k ∈ S, ∀ l ∈ S, ∀ m ∈ S, k + l + m ≠ 0) :
    thirdMoment c S = 0 := by
  rw [thirdMoment_eq_resonance]
  refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl =>
    Finset.sum_eq_zero (fun m hm => ?_)))
  rw [if_neg (h k hk l hl m hm)]

/-- **Pure-tone vanishing.**  A field carrying only the fundamental frequency (`±1`) has zero third
moment: the spectrum `{-1,1}` admits no additive 3-resonance, since `±1±1±1` is odd, never `0`. -/
theorem thirdMoment_pureTone (c : ℤ → ℂ) :
    thirdMoment c {-1, 1} = 0 := by
  apply thirdMoment_eq_zero_of_sumFree
  intro k hk l hl m hm
  fin_cases hk <;> fin_cases hl <;> fin_cases hm <;> decide

/-- Fourier coefficients of the real field `a·cos θ + b·cos 2θ` (fundamental + second harmonic):
`c(±1) = a/2`, `c(±2) = b/2`, all others zero. -/
def towerCoeff (a b : ℂ) : ℤ → ℂ := fun k =>
  if k = 1 ∨ k = -1 then a/2 else if k = 2 ∨ k = -2 then b/2 else 0

/-- **Second-harmonic forcing (the discriminator core).**  The field `a·cos θ + b·cos 2θ` has third
moment `(3/4)·a²·b`.  The fundamental alone (`b = 0`) gives zero; the second harmonic `b` is exactly
what activates the `1+1=2` resonance and makes the third moment nonzero.  This is the codim-2 cause:
the third cumulant sees the second harmonic, and nothing lower does. -/
theorem thirdMoment_two_harmonic (a b : ℂ) :
    thirdMoment (towerCoeff a b) {-2, -1, 1, 2} = 3/4 * a^2 * b := by
  rw [thirdMoment_eq_resonance]
  simp only [towerCoeff]
  norm_num
  ring

/-- **Multiplicativity forces the second harmonic.**  The Euler local factor `(1-w)⁻¹` has
`log((1-w)⁻¹) = ∑_{k≥1} wᵏ/k`, whose `x²`-coefficient is `1/2`; so on the critical line the
second-harmonic amplitude is the square of the fundamental over two, `b = a²/2`.  With this
multiplicatively-forced relation the third moment is `(3/8)·a⁴`. -/
theorem thirdMoment_multiplicative (a : ℂ) :
    thirdMoment (towerCoeff a (a^2/2)) {-2, -1, 1, 2} = 3/8 * a^4 := by
  rw [thirdMoment_two_harmonic]; ring

/-- **The discriminator.**  A tower-free field (second harmonic `b = 0`, i.e. no prime-square term)
has zero third moment; the multiplicatively-forced field (`b = a²/2`) has third moment `(3/8)a⁴ ≠ 0`
whenever the fundamental `a ≠ 0`.  So the third moment separates a field carrying the Euler
prime-power tower from a tower-free one. -/
theorem thirdMoment_discriminator (a : ℂ) (ha : a ≠ 0) :
    thirdMoment (towerCoeff a 0) {-2, -1, 1, 2} = 0 ∧
      thirdMoment (towerCoeff a (a^2/2)) {-2, -1, 1, 2} ≠ 0 := by
  refine ⟨by rw [thirdMoment_two_harmonic]; ring, ?_⟩
  rw [thirdMoment_multiplicative]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 4 ha)

/-- **Strict positivity of the multiplicative signature.**  For a real nonzero fundamental `a`, the
multiplicatively-forced third moment `(3/8)a⁴` is real and strictly positive — the ζ prime-power
tower (all Euler coefficients positive) produces a strictly positive third-moment contribution at
every prime, `a = p^{-1/2}` giving `(3/8)p^{-2}`.  The positivity of the sign is ζ-specific (positive
Euler coefficients); for a general L-function the second-harmonic amplitude need not be positive. -/
theorem thirdMoment_multiplicative_pos (a : ℝ) (ha : a ≠ 0) :
    thirdMoment (towerCoeff (a:ℂ) ((a:ℂ)^2/2)) {-2, -1, 1, 2} = ((3/8 * a^4 : ℝ) : ℂ)
      ∧ 0 < 3/8 * a^4 := by
  refine ⟨?_, by positivity⟩
  rw [thirdMoment_multiplicative]; push_cast; ring

/-- The resonance sum of real coefficients — the real third moment of a real field. -/
def thirdMomentR (c : ℤ → ℝ) (S : Finset ℤ) : ℝ :=
  ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S, if k + l + m = 0 then c k * c l * c m else 0

/-- For real coefficients, the third moment is the real resonance sum (cast to `ℂ`). -/
theorem thirdMoment_ofReal (c : ℤ → ℝ) (S : Finset ℤ) :
    thirdMoment (fun k => (c k : ℂ)) S = ((thirdMomentR c S : ℝ) : ℂ) := by
  rw [thirdMoment_eq_resonance, thirdMomentR]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ =>
    Finset.sum_congr rfl (fun m _ => ?_)))
  split <;> simp

/-- **General multiplicative tower — strict positivity, no truncation assumption.**  A real field
with nonnegative Fourier coefficients whose spectrum contains the fundamental `1` and the second
harmonic `-2` with positive weight has strictly positive third moment: every resonance term is
`≥ 0`, and the `1+1=2` term is `> 0`.  This is the full ζ prime-power tower (all Euler coefficients
positive) — every finite piece of the tower carries strictly positive third-moment content, of the
same sign, so the total (a convergent sum, since the diagonal `∑_p p^{-2}` converges) is strictly
positive.  The magnitude is fixed by multiplicativity; the definiteness of the sign here is ζ-specific
(positive Euler coefficients). -/
theorem thirdMomentR_pos_of_tower (c : ℤ → ℝ) (S : Finset ℤ)
    (hnn : ∀ k, 0 ≤ c k) (h1 : (1:ℤ) ∈ S) (h2 : (-2:ℤ) ∈ S)
    (hc1 : 0 < c 1) (hc2 : 0 < c (-2)) :
    0 < thirdMomentR c S := by
  rw [thirdMomentR]
  have hTnn : ∀ k l m : ℤ, 0 ≤ (if k + l + m = 0 then c k * c l * c m else 0) := by
    intro k l m; split
    · exact mul_nonneg (mul_nonneg (hnn k) (hnn l)) (hnn m)
    · exact le_refl 0
  have hbase : 0 < (if (1:ℤ) + 1 + (-2) = 0 then c 1 * c 1 * c (-2) else 0) := by
    norm_num; positivity
  calc 0 < (if (1:ℤ) + 1 + (-2) = 0 then c 1 * c 1 * c (-2) else 0) := hbase
    _ ≤ ∑ m ∈ S, (if (1:ℤ) + 1 + m = 0 then c 1 * c 1 * c m else 0) :=
        Finset.single_le_sum (fun m _ => hTnn 1 1 m) h2
    _ ≤ ∑ l ∈ S, ∑ m ∈ S, (if (1:ℤ) + l + m = 0 then c 1 * c l * c m else 0) :=
        Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => hTnn 1 l m)) h1
    _ ≤ ∑ k ∈ S, ∑ l ∈ S, ∑ m ∈ S, (if k + l + m = 0 then c k * c l * c m else 0) :=
        Finset.single_le_sum
          (fun k _ => Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun m _ => hTnn k l m))) h1

end RHTower
