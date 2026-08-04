import GaloisForLFunctions.RHTower.Sieve.RouteEAveraged

/-!
# The square-root window law

The card's growth condition `h/log log(3x) → ∞` holds for the largest admissible window law
`h = √x`, and the verification is elementary: applying `log y ≤ 2√y` twice,

    log log (3x)  ≤  2√(log 3x)  ≤  2√(2√(3x))  =  2√2 · ⁴√3 · ⁴√x,

so `√x / log log(3x) ≥ ⁴√x / (2√2·⁴√3) → ∞`.  No asymptotic library is needed — the corpus's
`MertensFirst.log_le_two_mul_sqrt`, used twice.

With this the card's Theorem `(3)` becomes an unconditional statement with no hypotheses at all
beyond the sign: for the window `[x, x + x]` both coprime sign classes keep a positive density.
-/

namespace RHTower.Sieve

open Filter Topology
open scoped ArithmeticFunction.Moebius

/-- **The square-root window law satisfies the card's growth condition.** -/
theorem tendsto_sqrt_div_logLog_atTop :
    Tendsto (fun x : ℝ => Real.sqrt x / Real.log (Real.log (3 * x))) atTop atTop := by
  set c : ℝ := 1 / (2 * Real.sqrt 2 * Real.sqrt (Real.sqrt 3)) with hc
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt (Real.sqrt 3) :=
    Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))
  have hc0 : (0 : ℝ) < c := by
    rw [hc]
    positivity
  have hlow : Tendsto (fun x : ℝ => c * Real.sqrt (Real.sqrt x)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).const_mul_atTop hc0
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have h3x : (0 : ℝ) < 3 * x := by linarith
  have hlog3x : (1 : ℝ) < Real.log (3 * x) := by
    have hexp : Real.exp 1 < 3 * x := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hL0 : (0 : ℝ) < Real.log (Real.log (3 * x)) := Real.log_pos hlog3x
  -- the double square-root bound
  have hstep1 : Real.log (Real.log (3 * x)) ≤ 2 * Real.sqrt (Real.log (3 * x)) :=
    log_le_two_mul_sqrt (by linarith)
  have hstep2 : Real.log (3 * x) ≤ 2 * Real.sqrt (3 * x) := log_le_two_mul_sqrt h3x
  have hstep3 : Real.sqrt (Real.log (3 * x)) ≤ Real.sqrt (2 * Real.sqrt (3 * x)) :=
    Real.sqrt_le_sqrt hstep2
  have hval : Real.sqrt (2 * Real.sqrt (3 * x))
      = Real.sqrt 2 * (Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt x)) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3),
      Real.sqrt_mul (Real.sqrt_nonneg 3)]
  have hLup : Real.log (Real.log (3 * x))
      ≤ 2 * Real.sqrt 2 * Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt x) := by
    calc Real.log (Real.log (3 * x)) ≤ 2 * Real.sqrt (Real.log (3 * x)) := hstep1
      _ ≤ 2 * Real.sqrt (2 * Real.sqrt (3 * x)) := by linarith
      _ = 2 * (Real.sqrt 2 * (Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt x))) := by
          rw [hval]
      _ = 2 * Real.sqrt 2 * Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt x) := by ring
  -- and the conclusion
  have hv0 : (0 : ℝ) < Real.sqrt (Real.sqrt x) :=
    Real.sqrt_pos.2 (Real.sqrt_pos.2 hx0)
  have hvsq : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
    Real.mul_self_sqrt (Real.sqrt_nonneg x)
  rw [le_div_iff₀ hL0]
  have hmul : c * Real.sqrt (Real.sqrt x) * Real.log (Real.log (3 * x))
      ≤ c * Real.sqrt (Real.sqrt x)
        * (2 * Real.sqrt 2 * Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt x)) := by
    refine mul_le_mul_of_nonneg_left hLup (by positivity)
  refine le_trans hmul (le_of_eq ?_)
  rw [hc]
  field_simp
  linarith [hvsq]

/-- **The card's Theorem `(3)` for the square-root window, with no hypotheses.**  Both coprime sign
classes keep a density at least the margin, unconditionally. -/
theorem route_e_sign_density_sqrt_window {s : ℤ} (hs : s = 1 ∨ s = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (Real.sqrt x) s
            / (Real.sqrt x * Real.sqrt x * Real.log 2) := by
  refine route_e_sign_density_long_window (K := 1) hs one_pos tendsto_sqrt_div_logLog_atTop
    ?_ ?_ hε
  · filter_upwards with x
    exact le_refl _
  · filter_upwards with x
    rw [div_one]

/-- **The card's stated consequence, unconditionally, for the square-root window.**  Every large
balanced window `[x, x + x]` carries a coprime squarefree pair of each product sign. -/
theorem route_e_signClass_nonempty_sqrt_window {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x in atTop, (coprimeSignClass x (Real.sqrt x) s).Nonempty := by
  have hmargin := route_e_margin_pos
  have hbound := route_e_sign_density_sqrt_window hs
    (ε := (squarefreeDensity ^ 2 / 2
      - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity) / 2) (by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hbound] with x hx0 hb
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < Real.sqrt x * Real.sqrt x * Real.log 2 := by positivity
  have hpos : 0 < coprimeSignClassCount x (Real.sqrt x) s
      / (Real.sqrt x * Real.sqrt x * Real.log 2) := by linarith
  have hcard : 0 < coprimeSignClassCount x (Real.sqrt x) s := by
    rcases lt_or_ge 0 (coprimeSignClassCount x (Real.sqrt x) s) with hc | hc
    · exact hc
    · exact absurd hpos (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hc hden.le))
  rw [coprimeSignClassCount] at hcard
  refine Finset.card_pos.1 ?_
  exact_mod_cast hcard

end RHTower.Sieve
