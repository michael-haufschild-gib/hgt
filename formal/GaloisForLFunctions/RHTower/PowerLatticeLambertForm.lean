import GaloisForLFunctions.RHTower.LambertSeriesConvergence

/-!
# The Lambert form of a moment-Borel transform

Assembling the pieces: the coefficients of the transform are values of `ζ` above the abscissa
`1 + s`, geometrically small in `k`; the Dirichlet series of those values may therefore be summed
in the other order; the scale identity regroups each term into the `k`-th power of a single
variable `ξ/(2π n)^s`; and the resulting inner geometric-sine series has the closed form whose
denominator is the quadratic factor.

The outcome is the Lambert series: a sum over `n` of `1/n` times a rational function of
`ξ/(2π n)^s`, whose poles are the two power lattices.

* `GaloisForLFunctions.RHTower.lambertVar`;
* `GaloisForLFunctions.RHTower.norm_lambertVar_lt_one`;
* `GaloisForLFunctions.RHTower.tsum_zeta_coeff_eq_lambert`;
* `GaloisForLFunctions.RHTower.eventually_norm_lambertVar_le_half`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- The Lambert variable `ξ/(2π(n+1))^s`. -/
noncomputable def lambertVar (s : ℝ) (ξ : ℂ) (n : ℕ) : ℂ :=
  ξ / (((2 * Real.pi * ((n : ℝ) + 1)) ^ s : ℝ) : ℂ)

/-- Inside the disc of radius `(2π)^s` every Lambert variable lies in the open unit disc. -/
theorem norm_lambertVar_lt_one {s : ℝ} (hs : 0 < s) {ξ : ℂ}
    (hξ : ‖ξ‖ < (2 * Real.pi) ^ s) (n : ℕ) : ‖lambertVar s ξ n‖ < 1 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : (2 * Real.pi) ^ s ≤ (2 * Real.pi * ((n : ℝ) + 1)) ^ s := by
    refine Real.rpow_le_rpow hpi.le ?_ hs.le
    nlinarith
  have hpos : (0 : ℝ) < (2 * Real.pi * ((n : ℝ) + 1)) ^ s := by
    refine Real.rpow_pos_of_pos ?_ s
    nlinarith
  rw [lambertVar, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    div_lt_one hpos]
  exact lt_of_lt_of_le hξ hle

/-- **The Lambert form.**  The `ζ`-weighted power series in `ξ` equals a Lambert series in the
variables `ξ/(2π n)^s`. -/
theorem tsum_zeta_coeff_eq_lambert {s : ℝ} (hs : 0 < s) (α : ℝ) {ξ : ℂ}
    (hξ : ‖ξ‖ < (2 * Real.pi) ^ s) :
    ∑' k : ℕ, ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * ξ ^ (k + 1)
          / (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ))
        * riemannZeta (((1 + s * (k + 1) : ℝ) : ℝ) : ℂ)
      = ∑' n : ℕ, (1 / ((n : ℂ) + 1)) *
          (lambertVar s ξ n * (Real.sin α : ℂ)
            / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2)) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbase : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos hpi s
  set r : ℝ := ‖ξ‖ / (2 * Real.pi) ^ s with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hbase]
    exact hξ
  set c : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * ξ ^ (k + 1)
    / (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ) with hcdef
  set e : ℕ → ℂ := fun k => (((1 + s * (k + 1) : ℝ) : ℝ) : ℂ) with hedef
  -- the coefficients are geometrically small
  have hpowsplit : ∀ k : ℕ, ((2 * Real.pi) ^ (s * (k + 1)) : ℝ) = ((2 * Real.pi) ^ s) ^ (k + 1) := by
    intro k
    rw [← Real.rpow_natCast ((2 * Real.pi) ^ s) (k + 1), ← Real.rpow_mul hpi.le]
    push_cast
    ring_nf
  have hc : ∀ k, ‖c k‖ ≤ r ^ k := by
    intro k
    have hsin : ‖((Real.sin ((k + 1) * α) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hden : ‖(((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ)‖ = ((2 * Real.pi) ^ s) ^ (k + 1) := by
      rw [Complex.norm_real, Real.norm_eq_abs, hpowsplit k, abs_of_pos (by positivity)]
    have hnum : ‖(-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * ξ ^ (k + 1)‖ ≤ ‖ξ‖ ^ (k + 1) := by
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) hsin
    have hstep : ‖c k‖ ≤ r ^ (k + 1) := by
      rw [hcdef]
      simp only [norm_div, hden]
      rw [div_le_iff₀ (by positivity)]
      have hrpow : r ^ (k + 1) * ((2 * Real.pi) ^ s) ^ (k + 1) = ‖ξ‖ ^ (k + 1) := by
        rw [hrdef, div_pow, div_mul_cancel₀]
        positivity
      rw [hrpow]
      exact hnum
    refine le_trans hstep ?_
    calc r ^ (k + 1) = r ^ k * r := by ring
      _ ≤ r ^ k * 1 := by
          refine mul_le_mul_of_nonneg_left hr1.le (by positivity)
      _ = r ^ k := by ring
  have he : ∀ k, (1 + s) ≤ (e k).re := by
    intro k
    rw [hedef]
    simp only [Complex.ofReal_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  -- interchange
  have hinter := tsum_mul_riemannZeta_eq_tsum_comm (a := 1 + s) (by linarith) hr0 hr1 hc he
  rw [hinter]
  refine tsum_congr fun n => ?_
  -- regroup the inner series
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcastN : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hinner : ∀ k : ℕ, c k / ((n : ℂ) + 1) ^ (e k)
      = (1 / ((n : ℂ) + 1)) *
        ((-1 : ℂ) ^ k * (Real.sin ((k + 1) * α) : ℂ) * (lambertVar s ξ n) ^ (k + 1)) := by
    intro k
    have hden : ((n : ℂ) + 1) ^ (e k) = ((((n : ℝ) + 1) ^ (1 + s * (k + 1)) : ℝ) : ℂ) := by
      rw [hcastN, hedef, Complex.ofReal_cpow hN.le]
    have hscale := rpow_scale_identity hpi s n k
    have hprod : (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ) * ((((n : ℝ) + 1)
        ^ (1 + s * (k + 1)) : ℝ) : ℂ)
        = (((n : ℝ) + 1 : ℝ) : ℂ) * ((((2 * Real.pi * ((n : ℝ) + 1)) ^ s : ℝ) : ℂ)) ^ (k + 1) := by
      rw [← Complex.ofReal_mul, hscale]
      push_cast
      ring
    have hscalene : ((((2 * Real.pi * ((n : ℝ) + 1)) ^ s : ℝ) : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < (2 * Real.pi * ((n : ℝ) + 1)) ^ s := by
        refine Real.rpow_pos_of_pos ?_ s
        nlinarith
      exact Complex.ofReal_ne_zero.2 (ne_of_gt this)
    have hNne : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hN)
    have hpowne : (((2 * Real.pi) ^ (s * (k + 1)) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
      exact Real.rpow_pos_of_pos hpi _
    rw [hcdef, hden, hcastN, lambertVar, div_pow, div_div]
    rw [hprod]
    field_simp
  rw [tsum_congr hinner, tsum_mul_left,
    tsum_alternating_sine_geometric_complex α (norm_lambertVar_lt_one hs hξ n)]

/-- **All but finitely many Lambert variables are small, uniformly on a bounded set.**  This is the
"after finitely many terms are removed" of the normal-convergence statement: on `‖ξ‖ ≤ M` every
`‖u_n‖` is at most `1/2` once `n` is large, so the tail is dominated and only the finitely many
remaining terms carry poles. -/
theorem eventually_norm_lambertVar_le_half {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ ξ : ℂ, ‖ξ‖ ≤ M → ‖lambertVar s ξ n‖ ≤ 1 / 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set K : ℝ := max M 1 with hK
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set T : ℝ := (2 * K) ^ (1 / s) with hT
  have hT0 : (0 : ℝ) < T := Real.rpow_pos_of_pos (by positivity) _
  have hTs : T ^ s = 2 * K := by
    rw [hT, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * K), one_div,
      inv_mul_cancel₀ hs.ne', Real.rpow_one]
  obtain ⟨N, hN⟩ := exists_nat_gt (T / (2 * Real.pi))
  refine Filter.eventually_atTop.2 ⟨N, fun n hn ξ hξ => ?_⟩
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hTle : T ≤ 2 * Real.pi * ((n : ℝ) + 1) := by
    have h1 : T / (2 * Real.pi) < (N : ℝ) := hN
    have h2 : T < 2 * Real.pi * (N : ℝ) := by
      rw [div_lt_iff₀ hpi] at h1
      linarith
    nlinarith
  have hxpos : (0 : ℝ) < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
  have hmono : T ^ s ≤ (2 * Real.pi * ((n : ℝ) + 1)) ^ s :=
    Real.rpow_le_rpow hT0.le hTle hs.le
  have hscale : 2 * K ≤ (2 * Real.pi * ((n : ℝ) + 1)) ^ s := by rw [← hTs]; exact hmono
  have hden : (0 : ℝ) < (2 * Real.pi * ((n : ℝ) + 1)) ^ s := Real.rpow_pos_of_pos hxpos s
  rw [lambertVar, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden,
    div_le_iff₀ hden]
  have hξK : ‖ξ‖ ≤ K := le_trans hξ (le_max_left _ _)
  nlinarith

end GaloisForLFunctions.RHTower
