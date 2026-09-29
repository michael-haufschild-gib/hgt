import GaloisForLFunctions.HTGeometry.HamburgerLaplaceIdentity
import GaloisForLFunctions.HTGeometry.ConverseThetaRelation

/-!
# Hamburger's theorem

A Dirichlet series with the functional equation of `ζ` is a multiple of `ζ`.  Precisely: let
`f(s) = Σ a_n n^{-s}` and `g(s) = Σ b_n n^{-s}` converge absolutely for `Re s > 1`, and suppose
that `Γ_ℝ(s) f(s)` on `Re s = 3/2` and `ε Γ_ℝ(1-s) g(1-s)` on `Re s = -1/2` both equal
`E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)`.  Here `E` is holomorphic on the strip `-1/2 ≤ Re s ≤ 3/2` and
`O(1/(1 + t²))` there.  Then `a_n = -2α` for every `n` (`coeff_eq_of_completed_functional_equation`).

Three steps give this:
* the converse theta relation `θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}`
  (`converse_theta_relation`);
* its Laplace transform, which makes `L_a(t) = Σ a_n t/(π(n² + t²))` `i`-periodic up to
  `α/(π t)` on `Re t > 0` (`hamburgerSeries_periodic_of_coeffTheta_relation`);
* the residues of `L_a` along the imaginary axis (`coeff_eq_of_hamburgerSeries_periodic_re_pos`).

For the odd sign `ε = -1` with `g = f`, the theta relation at `x = 4`, `1/4` and `1` also forces
`α = 0`, so `f = 0` (`coeff_eq_zero_of_odd_completed_functional_equation`): no nonzero Dirichlet
series has the reflection law `Λ(s) = -Λ(1 - s)`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Under the theta relation the Hamburger series is `i`-periodic up to the pole of `α/(π t)`. -/
theorem hamburgerSeries_periodic_of_coeffTheta_relation (a b : ℕ → ℂ)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {ε α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    hamburgerSeries a (t + I) - hamburgerSeries a t =
      α / Real.pi / (t + I) - α / Real.pi / t := by
  have ht' : 0 < (t + I).re := by simpa using ht
  rw [hamburgerSeries_eq_of_coeffTheta_relation a b ha hb htheta ht',
    hamburgerSeries_eq_of_coeffTheta_relation a b ha hb htheta ht]
  have hper : ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (t + I))) =
      ∑' n : ℕ, b (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * t)) := by
    refine tsum_congr fun n => ?_
    rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (t + I)) =
      -(2 * Real.pi * ((n : ℂ) + 1) * t) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, div_div, div_div]
  ring

/-- **Hamburger's theorem.**  Let `f(s) = Σ a_n n^{-s}` and `g(s) = Σ b_n n^{-s}` converge
absolutely for `Re s > 1`.  Suppose there are constants `α, β, ε` and a function `E`,
holomorphic on `-1/2 ≤ Re s ≤ 3/2` with `‖E(s)‖ ≤ C/(1 + (Im s)²)` there, such that
`Γ_ℝ(s) f(s) = E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and
`ε Γ_ℝ(1-s) g(1-s) = E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)` on `Re s = -1/2`.  Then every
coefficient of `f` equals `-2α`, i.e. `f = -2α ζ`.

The functional equation gives the theta relation (`converse_theta_relation`).  Its Laplace
transform makes the partial-fraction series `Σ a_n t/(π(n² + t²))` `i`-periodic up to
`α/(π t)` on `Re t > 0`, and comparing residues along the imaginary axis gives `a_n = -2α`. -/
theorem coeff_eq_of_completed_functional_equation {a b : ℕ → ℂ} {E : ℂ → ℂ} {α β ε : ℂ} {C : ℝ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * coeffDirichlet a s =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → ε * (Complex.Gammaℝ (1 - s) * coeffDirichlet b (1 - s)) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (n : ℕ) : a (n + 1) = -(2 * α) := by
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    refine converse_theta_relation (continuousOn_coeffTheta a (ha 2 (by norm_num)))
      (continuousOn_coeffTheta b (hb 2 (by norm_num)))
      (mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num))
      (mellinConvergent_coeffTheta b hb (by norm_num) (by norm_num)) hE hdecay
      (fun s hs => ?_) (fun s hs => ?_) hx
    · rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
      exact hR s hs
    · rw [mellin_coeffTheta b hb (s := 1 - s) (by simp [hs]; norm_num)]
      exact hL s hs
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos ha2 (α / Real.pi)
    (fun t ht => hamburgerSeries_periodic_of_coeffTheta_relation a b ha hb htheta ht) n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem ofReal_sq_cpow_neg_half {c : ℝ} (hc : 0 < c) :
    ((c ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = ((c⁻¹ : ℝ) : ℂ) := by
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc.le,
    show ((2 : ℕ) : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one]

/-- **No Dirichlet series has an odd completed functional equation.**  If
`Γ_ℝ(s) f(s)` and `-Γ_ℝ(1-s) f(1-s)` differ from one strip-holomorphic, `O(1/(1 + t²))`
function `E` by the same polar part `α Γ_ℝ(s) + β Γ_ℝ(s - 1)`, on the lines `Re s = 3/2` and
`Re s = -1/2` respectively, then `f = 0`.

By Hamburger's theorem all coefficients equal `-2α`.  The theta relation at `x = 4` and
`x = 1/4` forces `α = β`.  At `x = 1` it gives `θ(1) = α`, while `θ(1) = -2α Σ e^{-π n²}`, so
`α (1 + 2 Σ e^{-π n²}) = 0`. -/
theorem coeff_eq_zero_of_odd_completed_functional_equation {a : ℕ → ℂ} {E : ℂ → ℂ} {α β : ℂ}
    {C : ℝ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * coeffDirichlet a s =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → -(Complex.Gammaℝ (1 - s) * coeffDirichlet a (1 - s)) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (n : ℕ) : a (n + 1) = 0 := by
  have hL' : ∀ s : ℂ, s.re = -1 / 2 → (-1) * (Complex.Gammaℝ (1 - s) * coeffDirichlet a (1 - s)) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
    intro s hs
    rw [neg_one_mul]
    exact hL s hs
  have hcoeff : ∀ m : ℕ, a (m + 1) = -(2 * α) :=
    coeff_eq_of_completed_functional_equation ha ha hE hdecay hR hL'
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    refine converse_theta_relation (continuousOn_coeffTheta a (ha 2 (by norm_num)))
      (continuousOn_coeffTheta a (ha 2 (by norm_num)))
      (mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num))
      (mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)) hE hdecay
      (fun s hs => ?_) (fun s hs => ?_) hx
    · rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
      exact hR s hs
    · rw [mellin_coeffTheta a ha (s := 1 - s) (by simp [hs]; norm_num)]
      exact hL' s hs
  -- `α = β` from `x = 4` and `x = 1/4`
  have h4 : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 / 2 := by
    have := ofReal_sq_cpow_neg_half (c := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h14 : ((1 / 4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 2 := by
    have := ofReal_sq_cpow_neg_half (c := 1 / 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have E4 := htheta 4 (by norm_num)
  have E14 := htheta (1 / 4) (by norm_num)
  rw [h4, show ((4 : ℝ))⁻¹ = 1 / 4 by norm_num] at E4
  rw [h14, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at E14
  have hαβ : α = β := by linear_combination E14 - 2 * E4
  -- `θ(1) = α`
  have E1 := htheta 1 one_pos
  rw [Complex.ofReal_one, Complex.one_cpow, inv_one] at E1
  rw [← hαβ] at E1
  have hθ1 : coeffTheta a 1 = α := by linear_combination E1 / 2
  -- `θ(1) = -2α S` with `S ≥ 0`
  set S : ℝ := ∑' m : ℕ, Real.exp (-Real.pi * ((m : ℝ) + 1) ^ 2 * 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => (Real.exp_pos _).le
  have hθS : coeffTheta a 1 = -(2 * α) * (S : ℂ) := by
    rw [coeffTheta, hS, Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [hcoeff m]
  have hα : α = 0 := by
    have h1 : α * (1 + 2 * (S : ℂ)) = 0 := by linear_combination hθS - hθ1
    have h2 : (1 + 2 * (S : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + 2 * S := by linarith
      exact_mod_cast this.ne'
    exact (mul_eq_zero.mp h1).resolve_right h2
  rw [hcoeff n, hα]
  ring

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
/-- **Hamburger's conclusion from the theta relation.**  If the theta series of `a` satisfies
`θ_a(x) = ε x^{-1/2} θ_b(1/x) + α + β x^{-1/2}` for all `x > 0`, then every coefficient of `a`
equals `-2α`.  This is the Laplace–periodicity half of Hamburger's theorem, with the theta relation
as hypothesis. -/
theorem coeff_eq_of_coeffTheta_relation {a b : ℕ → ℂ} {α β ε : ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hb : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖b (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta b x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    (n : ℕ) : a (n + 1) = -(2 * α) := by
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos ha2 (α / Real.pi)
    (fun t ht => hamburgerSeries_periodic_of_coeffTheta_relation a b ha hb htheta ht) n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **The odd theta relation forces vanishing.**  If `θ_a(x) = -x^{-1/2} θ_a(1/x) + α + β x^{-1/2}`
for all `x > 0`, then `a_n = 0` for every `n ≥ 1`.  All coefficients equal `-2α` by Hamburger's
periodicity argument.  The relation at `x = 4` and `x = 1/4` forces `α = β`, and at `x = 1` it
gives `α (1 + 2 Σ e^{-π n²}) = 0`. -/
theorem coeff_eq_zero_of_odd_coeffTheta_relation {a : ℕ → ℂ} {α β : ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    (n : ℕ) : a (n + 1) = 0 := by
  have hcoeff : ∀ m : ℕ, a (m + 1) = -(2 * α) :=
    coeff_eq_of_coeffTheta_relation ha ha htheta
  have h4 : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 / 2 := by
    have := ofReal_sq_cpow_neg_half (c := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h14 : ((1 / 4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 2 := by
    have := ofReal_sq_cpow_neg_half (c := 1 / 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have E4 := htheta 4 (by norm_num)
  have E14 := htheta (1 / 4) (by norm_num)
  rw [h4, show ((4 : ℝ))⁻¹ = 1 / 4 by norm_num] at E4
  rw [h14, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at E14
  have hαβ : α = β := by linear_combination E14 - 2 * E4
  have E1 := htheta 1 one_pos
  rw [Complex.ofReal_one, Complex.one_cpow, inv_one] at E1
  rw [← hαβ] at E1
  have hθ1 : coeffTheta a 1 = α := by linear_combination E1 / 2
  set S : ℝ := ∑' m : ℕ, Real.exp (-Real.pi * ((m : ℝ) + 1) ^ 2 * 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => (Real.exp_pos _).le
  have hθS : coeffTheta a 1 = -(2 * α) * (S : ℂ) := by
    rw [coeffTheta, hS, Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun m => by rw [hcoeff m]
  have hα : α = 0 := by
    have h1 : α * (1 + 2 * (S : ℂ)) = 0 := by linear_combination hθS - hθ1
    have h2 : (1 + 2 * (S : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + 2 * S := by linarith
      exact_mod_cast this.ne'
    exact (mul_eq_zero.mp h1).resolve_right h2
  rw [hcoeff n, hα]
  ring

end GaloisForLFunctions.HTGeometry
