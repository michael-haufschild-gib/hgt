import Mathlib

/-!
# Dirichlet-series backbone of the prime–polar moving-tent tomography

The arithmetic backbone of `prime-polar-moving-tent-divisor-tomography` §4: the ordinary Dirichlet
series of the polar sequence `(21)` and the von Mangoldt logarithmic-derivative identity feeding the
double-series continuation `(20)`.

Two reusable pieces first: a `cpow`-shift of the Dirichlet series (`∑ nᵃ·n⁻ˢ = ∑ n⁻⁽ˢ⁻ᵃ⁾`), which turns
a power weight into an argument shift of `ζ`, and its summability form.  The polar series is then the
three-shift combination

`∑ (c₁·N^{1/2} + c₂ + c₃·N^{-1/2}) N⁻ˢ = c₁·ζ(s-½) + c₂·ζ(s) + c₃·ζ(s+½)`   (Re s > 3/2),

and the prime side is `∑ Λ(k) k^{-(s-½)} = -ζ'/ζ(s-½)` for Re s > 3/2, the exact `-ζ'/ζ` charge that
`(20)` cancels against the polar term at `s = 3/2`.
-/

open scoped Real
open ArithmeticFunction Filter Topology

namespace RHTower

/-- **Per-term power shift.**  The `L`-series term of `n ↦ nᵃ` at `s` equals the term of the constant
`1` at the shifted argument `s − a`: `nᵃ / nˢ = 1 / n^{s-a}`. -/
theorem term_cpow_eq (a s : ℂ) (n : ℕ) :
    LSeries.term (fun m => (m : ℂ) ^ a) s n = LSeries.term (1 : ℕ → ℂ) (s - a) n := by
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero h, LSeries.term_of_ne_zero h, Pi.one_apply, one_div]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast h
    rw [← Complex.cpow_neg, ← Complex.cpow_sub _ _ hn0, neg_sub]

/-- A power weight `nᵃ` is an argument shift of the Dirichlet series: `∑ nᵃ n⁻ˢ = ∑ 1·n^{-(s-a)}`. -/
theorem lseries_cpow (a s : ℂ) : LSeries (fun n => (n : ℂ) ^ a) s = LSeries 1 (s - a) :=
  tsum_congr (term_cpow_eq a s)

/-- Summability transfers across the same shift. -/
theorem lseriesSummable_cpow (a s : ℂ) :
    LSeriesSummable (fun n => (n : ℂ) ^ a) s ↔ LSeriesSummable (1 : ℕ → ℂ) (s - a) :=
  summable_congr (term_cpow_eq a s)

/-- The shifted power series is `ζ(s − a)` whenever `Re(s − a) > 1`. -/
theorem lseries_cpow_eq_zeta (a s : ℂ) (h : 1 < (s - a).re) :
    LSeries (fun n => (n : ℂ) ^ a) s = riemannZeta (s - a) := by
  rw [lseries_cpow, LSeries_one_eq_riemannZeta h]

/-- **The three-shift polar Dirichlet series** (§4, eq. 21).  For `Re s > 3/2`,
`∑ (c₁·N^{1/2} + c₂·N⁰ + c₃·N^{-1/2}) N⁻ˢ = c₁·ζ(s-½) + c₂·ζ(s) + c₃·ζ(s+½)`.  The polar sequence
`P_L(N) = 8α²N^{1/2} + 16αβ + 8β²N^{-1/2}` of `(5)` is the instance `c₁ = 8α²`, `c₂ = 16αβ`,
`c₃ = 8β²`. -/
theorem polar_lseries (c₁ c₂ c₃ : ℂ) (s : ℂ) (hs : 3 / 2 < s.re) :
    LSeries (fun N => c₁ * (N : ℂ) ^ (1 / 2 : ℂ) + c₂ * (N : ℂ) ^ (0 : ℂ)
        + c₃ * (N : ℂ) ^ (-(1 / 2) : ℂ)) s
      = c₁ * riemannZeta (s - 1 / 2) + c₂ * riemannZeta s + c₃ * riemannZeta (s + 1 / 2) := by
  have e2 : ((1 : ℂ) / 2).re = 1 / 2 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  have h1 : 1 < (s - (1 / 2 : ℂ)).re := by rw [Complex.sub_re, e2]; linarith
  have h2 : 1 < (s - (0 : ℂ)).re := by rw [Complex.sub_re]; simp; linarith
  have h3 : 1 < (s - (-(1 / 2) : ℂ)).re := by rw [Complex.sub_re, Complex.neg_re, e2]; linarith
  have b1 : Summable (LSeries.term (fun n => (n : ℂ) ^ (1 / 2 : ℂ)) s) :=
    (lseriesSummable_cpow _ s).mpr (LSeriesSummable_one_iff.mpr h1)
  have b2 : Summable (LSeries.term (fun n => (n : ℂ) ^ (0 : ℂ)) s) :=
    (lseriesSummable_cpow _ s).mpr (LSeriesSummable_one_iff.mpr h2)
  have b3 : Summable (LSeries.term (fun n => (n : ℂ) ^ (-(1 / 2) : ℂ)) s) :=
    (lseriesSummable_cpow _ s).mpr (LSeriesSummable_one_iff.mpr h3)
  have hterm : ∀ n, LSeries.term
      (fun N => c₁ * (N : ℂ) ^ (1 / 2 : ℂ) + c₂ * (N : ℂ) ^ (0 : ℂ)
        + c₃ * (N : ℂ) ^ (-(1 / 2) : ℂ)) s n
      = c₁ * LSeries.term (fun n => (n : ℂ) ^ (1 / 2 : ℂ)) s n
        + c₂ * LSeries.term (fun n => (n : ℂ) ^ (0 : ℂ)) s n
        + c₃ * LSeries.term (fun n => (n : ℂ) ^ (-(1 / 2) : ℂ)) s n := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h; simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero h, LSeries.term_of_ne_zero h, LSeries.term_of_ne_zero h,
        LSeries.term_of_ne_zero h]; ring
  have hlin : LSeries (fun N => c₁ * (N : ℂ) ^ (1 / 2 : ℂ) + c₂ * (N : ℂ) ^ (0 : ℂ)
        + c₃ * (N : ℂ) ^ (-(1 / 2) : ℂ)) s
      = c₁ * LSeries (fun n => (n : ℂ) ^ (1 / 2 : ℂ)) s + c₂ * LSeries (fun n => (n : ℂ) ^ (0 : ℂ)) s
        + c₃ * LSeries (fun n => (n : ℂ) ^ (-(1 / 2) : ℂ)) s := by
    unfold LSeries
    rw [tsum_congr hterm,
      Summable.tsum_add ((b1.mul_left c₁).add (b2.mul_left c₂)) (b3.mul_left c₃),
      Summable.tsum_add (b1.mul_left c₁) (b2.mul_left c₂),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hlin, lseries_cpow_eq_zeta _ _ h1, lseries_cpow_eq_zeta _ _ h2, lseries_cpow_eq_zeta _ _ h3,
    sub_zero, sub_neg_eq_add]

/-- **The prime-side logarithmic-derivative identity** (§4, eq. 20).  For `Re s > 3/2` the shifted
von Mangoldt Dirichlet series is `∑ Λ(k) k^{-(s-½)} = -ζ'/ζ(s-½)` — the exact charge that the polar
term of `(20)` cancels at `s = 3/2`. -/
theorem vonMangoldt_shifted_logDeriv (s : ℂ) (hs : 3 / 2 < s.re) :
    LSeries (fun n => (Λ n : ℂ)) (s - 1 / 2)
      = -deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2) := by
  apply LSeries_vonMangoldt_eq_deriv_riemannZeta_div
  have e2 : ((1 : ℂ) / 2).re = 1 / 2 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  rw [Complex.sub_re, e2]; linarith

/-- **The weighted-error majorant** (§4, eq. 18).  For `σ > 1/2` the series `∑ Λ(k) k^{-(σ+½)}`
converges absolutely.  This is the `Λ(k)/√k`-weighted Euler bound at `σ+½ > 1` that dominates the
error series `(19)` and makes `H_L` holomorphic on `Re s > 1/2`.  It is the real absolute-convergence
extract of `LSeriesSummable_vonMangoldt` at the shifted real argument. -/
theorem vonMangoldt_shifted_summable (σ : ℝ) (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => (Λ n : ℝ) * (n : ℝ) ^ (-(σ + 1 / 2))) := by
  have hw : (1 : ℝ) < ((σ + 1 / 2 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have hs : Summable (fun n => ‖LSeries.term (fun m => (Λ m : ℂ)) ((σ + 1 / 2 : ℝ) : ℂ) n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hw)
  refine hs.congr (fun n => ?_)
  rw [LSeries.norm_term_eq, Complex.ofReal_re]
  rcases eq_or_ne n 0 with h | h
  · subst h; simp
  · rw [if_neg h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv]

/-- The half-shift `s ↦ s − ½` carries the punctured neighbourhood of `3/2` to the punctured
neighbourhood of `1` — the change of variable that moves the polar point `s = 3/2` onto the `ζ`-pole. -/
theorem shift_half_tendsto :
    Tendsto (fun s : ℂ => s - (1 / 2 : ℂ)) (𝓝[≠] (3 / 2)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h1 : Tendsto (fun s : ℂ => s - (1 / 2 : ℂ)) (𝓝 (3 / 2)) (𝓝 (1 : ℂ)) :=
      (continuous_id.sub continuous_const).tendsto' (3 / 2) 1 (by norm_num)
    exact h1.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; apply hs; rw [Set.mem_singleton_iff]; linear_combination h

/-- **The polar-term residue** (§5, eq. 23, source half).  The polar summand `8α²·ζ(s−½)` of `(21)`
has a simple pole at `s = 3/2` with residue exactly `8α²` (`α = 1 − e^{-L/2}`), inherited from `ζ`'s
residue `1` at its pole `s = 1` through the half-shift.  This is the `+8α²` that the prime term's
`−2·I_L(3/2) = −8α²` cancels. -/
theorem polar_term_residue (L : ℝ) :
    Tendsto (fun s : ℂ => (s - 3 / 2) *
        ((8 * (1 - Real.exp (-(L / 2))) ^ 2 : ℂ) * riemannZeta (s - 1 / 2)))
      (𝓝[≠] (3 / 2)) (𝓝 ((8 * (1 - Real.exp (-(L / 2))) ^ 2 : ℂ))) := by
  have hz : Tendsto (fun s : ℂ => ((s - 1 / 2) - 1) * riemannZeta (s - 1 / 2))
      (𝓝[≠] (3 / 2)) (𝓝 1) := riemannZeta_residue_one.comp shift_half_tendsto
  have hc := (tendsto_const_nhds (x := (8 * (1 - Real.exp (-(L / 2))) ^ 2 : ℂ))).mul hz
  simp only [mul_one] at hc
  exact hc.congr (fun s => by ring)

end RHTower
