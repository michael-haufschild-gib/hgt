import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWallOfASourceClassIsTheLargestAbscissaItRealizes
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerCompletion
import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerZeros

/-!
# The multiplicative twins realize every abscissa above the zeros

The twin `ζ(s) (1 + A p⁻ˢ + p p⁻²ˢ)`, `A = r + p/r`, is a degree-one member of the extended Selberg
class of conductor `p²`: it has a functional equation, multiplicative coefficients, and its
coefficients lie in `[1, 1 + A + p]` (`zetaTwin_isExtendedSelberg`). The added local factor has
its zeros on the lines `Re s = log r / log p` and `Re s = 1 − log r / log p`
(`re_of_localFactor_eq_zero`), so for `r = p^b` with `b ≥ Θ` the twin has abscissa exactly `b`
(`zeroSupRe_zetaTwin`).

Consequently levers that are valid on the twins of one prime leave every seed `s ≥ Θ` where it is
(`wall_eq_seed_of_zetaTwins`): a functional equation, an Euler product and bounded coefficients
together move no seed. What the twins lack is the level one of `ζ` and the square-root bound for
the prime-power coefficients of the Euler logarithm.
-/

open Complex Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.SelbergClass.PositiveFiniteEuler
open _root_.RHTower (zetaZeroAbscissa re_le_zetaZeroAbscissa half_le_zetaZeroAbscissa)

/-- The **twin** of `ζ` at `p` with local roots of size `r` and `p/r`:
`ζ(s) (1 + A p⁻ˢ + p p⁻²ˢ)` with `A = r + p/r`. -/
noncomputable def zetaTwin (p : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  localFactor p (reciprocalParameter p r) s * riemannZeta s

/-- The twin continues a degree-one member of the extended Selberg class with multiplicative,
real, bounded coefficients. -/
theorem zetaTwin_isExtendedSelberg {p : ℕ} (hp : p.Prime) {r : ℝ} (hr : 0 < r) :
    ∃ F : RHTower.ExtendedSelbergClass, F.presentationDegree = 1 ∧ F.coeff.IsMultiplicative ∧
      (∃ C : ℝ, ∀ n : ℕ, n ≠ 0 →
        (F.coeff n).im = 0 ∧ 1 ≤ (F.coeff n).re ∧ (F.coeff n).re ≤ C) ∧
      ∀ s : ℂ, s ≠ 1 → F s = zetaTwin p r s := by
  have hA : 0 ≤ reciprocalParameter p r :=
    add_nonneg hr.le (div_nonneg (Nat.cast_nonneg p) hr.le)
  refine ⟨extendedClass hp (reciprocalParameter p r), extendedClass_degree hp _,
    arithmeticCoeffs_isMultiplicative hp _, ⟨1 + reciprocalParameter p r + p, fun n hn => ?_⟩,
    fun s hs => ?_⟩
  · change ((coeff p (reciprocalParameter p r) n : ℝ) : ℂ).im = 0 ∧
      1 ≤ ((coeff p (reciprocalParameter p r) n : ℝ) : ℂ).re ∧
      ((coeff p (reciprocalParameter p r) n : ℝ) : ℂ).re ≤ 1 + reciprocalParameter p r + p
    exact ⟨Complex.ofReal_im _, coeff_bounds hA hn⟩
  · change (continuation hp.ne_zero (reciprocalParameter p r)).value s = zetaTwin p r s
    exact continuation_eq hp.ne_zero _ hs

/-- **The zeros of the local factor lie on two lines.** A zero of `1 + A p⁻ˢ + p p⁻²ˢ` with
`A = r + p/r` has real part `log r / log p` or `1 − log r / log p`. -/
theorem re_of_localFactor_eq_zero {p : ℕ} (hp : 1 < p) {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : localFactor p (reciprocalParameter p r) s = 0) :
    s.re = Real.log r / Real.log p ∨ s.re = 1 - Real.log r / Real.log p := by
  have hp0 : p ≠ 0 := by omega
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hppos : (0 : ℝ) < p := by linarith
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hz := (localFactor_zero_iff hp0 (reciprocalParameter p r) s).mp hs
  have hA : ((reciprocalParameter p r : ℝ) : ℂ) = (r : ℂ) + (p : ℂ) / (r : ℂ) := by
    simp [reciprocalParameter]
  rw [hA] at hz
  -- the reciprocal quadratic is (t + r)(t + p/r) at t = pˢ
  have hrp : (r : ℂ) * ((p : ℂ) / (r : ℂ)) = p := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hrC]
  have hfac : ((p : ℂ) ^ s + (r : ℂ)) * ((p : ℂ) ^ s + (p : ℂ) / (r : ℂ)) = 0 := by
    linear_combination hz + hrp
  have hnorm : ‖(p : ℂ) ^ s‖ = Real.exp (Real.log p * s.re) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hp0), ← Complex.natCast_log, Complex.norm_exp,
      Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rcases mul_eq_zero.1 hfac with h | h
  · left
    -- pˢ = -r, so p^(Re s) = r
    have hexp : Real.exp (Real.log p * s.re) = r := by
      rw [← hnorm, eq_neg_of_add_eq_zero_left h, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    have hlog := congrArg Real.log hexp
    rw [Real.log_exp] at hlog
    rw [eq_div_iff hl.ne']
    linarith
  · right
    -- pˢ = -p/r, so p^(Re s) = p/r
    have hexp : Real.exp (Real.log p * s.re) = p / r := by
      rw [← hnorm, eq_neg_of_add_eq_zero_left h, norm_neg, norm_div, Complex.norm_natCast,
        Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hlog := congrArg Real.log hexp
    rw [Real.log_exp, Real.log_div hppos.ne' hr.ne'] at hlog
    have hre : s.re = (Real.log p - Real.log r) / Real.log p := by
      rw [eq_div_iff hl.ne']
      linarith
    rw [hre, sub_div, div_self hl.ne']

/-- **The twins realize every abscissa at or above `Θ`.** With local roots of size `p^b` and
`p^(1 − b)`, `b ≥ Θ`, the twin has abscissa `b`. -/
theorem zeroSupRe_zetaTwin {p : ℕ} (hp : 1 < p) {b : ℝ} (hb : zetaZeroAbscissa ≤ b) :
    zeroSupRe (zetaTwin p (Real.exp (b * Real.log p))) = b := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hr : 0 < Real.exp (b * Real.log p) := Real.exp_pos _
  have hlog : Real.log (Real.exp (b * Real.log p)) / Real.log p = b := by
    rw [Real.log_exp, mul_div_assoc, div_self hl.ne', mul_one]
  have hhalf : 1 / 2 ≤ b := half_le_zetaZeroAbscissa.trans hb
  -- the first zero of the local factor has real part b
  have hmem : b ∈ re '' {s | zetaTwin p (Real.exp (b * Real.log p)) s = 0} := by
    refine ⟨factorZero p (Real.exp (b * Real.log p)), ?_, (factorZero_re _ _).trans hlog⟩
    show localFactor p _ _ * riemannZeta _ = 0
    rw [localFactor_factorZero hp hr, zero_mul]
  -- zeros of the local factor lie on Re s = b or 1 - b, zeros of ζ at or left of Θ
  have hub : ∀ x ∈ re '' {s | zetaTwin p (Real.exp (b * Real.log p)) s = 0}, x ≤ b := by
    rintro _ ⟨s, hs, rfl⟩
    rcases mul_eq_zero.1 (show localFactor p _ s * riemannZeta s = 0 from hs) with h | h
    · rcases re_of_localFactor_eq_zero hp hr h with h1 | h1
      · exact (h1.trans hlog).le
      · rw [hlog] at h1
        linarith
    · exact (re_le_zetaZeroAbscissa h).trans hb
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨b, hub⟩ hmem)

/-- **A functional equation, an Euler product and bounded coefficients move no seed.** Levers
valid on the twins of one prime have wall `s` below every seed `s ≥ Θ`. -/
theorem wall_eq_seed_of_zetaTwins {𝒯 : Set (ℝ → ℝ)} {p : ℕ} (hp : 1 < p)
    (h : ∀ T ∈ 𝒯, ∀ r : ℝ, 0 < r → IsLever (zeroSupRe (zetaTwin p r)) T) {s : ℝ}
    (hs : zetaZeroAbscissa ≤ s) : wall 𝒯 s = s := by
  have hmem : s ∈ allowed 𝒯 s := by
    refine ⟨le_rfl, fun T hT => ?_⟩
    have hT' := (h T hT _ (Real.exp_pos (s * Real.log p))).le_apply_self
    rwa [zeroSupRe_zetaTwin hp hs] at hT'
  exact le_antisymm (csSup_le ⟨s, hmem⟩ fun _ hb => hb.1) (le_csSup (bddAbove_allowed 𝒯 s) hmem)

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
