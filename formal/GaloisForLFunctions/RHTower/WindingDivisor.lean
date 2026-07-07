/-
The argument principle for a divisor: the winding number counts all enclosed zeros.

Extending `WindingArgumentPrinciple` (a zero at the *centre* winds `m` times) to zeros anywhere
inside the circle: an enclosed simple zero winds the boundary loop exactly once
(`windingNumber_linear_enclosing`) — its linear factor factors as `(r e^{iθ})·u` with `u` a loop
staying in the unit ball about `1` (winding `0`).  Summed over a finite divisor, the winding number of
`θ ↦ ∏ᵢ (γ(θ) − ρᵢ)^{mᵢ}` around the circle `γ(θ) = c + r e^{iθ}` is the total enclosed order
`Σᵢ mᵢ` (`windingNumber_divisor`).

Hence the loop deck charge of a boundary circle is the reduction of the enclosed order
(`loopCharge_divisor`) — the topological winding realisation of the multi-zero deck charge, the
argument-principle twin of the algebraic `box_charge_eq_deckRed`.
-/
import GaloisForLFunctions.RHTower.WindingArgumentPrinciple

open Complex Set

namespace RHTower

/-- A loop landing in the open unit ball about `1` has winding number `0`: it has a single-valued
continuous logarithm (`Complex.log`, continuous on the slit plane ⊇ that ball). -/
theorem windingNumber_eq_zero_of_ball1 {γ : ℝ → ℂ} {a b : ℝ}
    (hγc : Continuous γ) (hclosed : γ a = γ b) (hball : ∀ t, ‖γ t - 1‖ < 1) :
    windingNumber γ a b = 0 := by
  have hslit : ∀ t, γ t ∈ slitPlane := fun t => by
    have h := mem_slitPlane_of_norm_lt_one (hball t)
    rwa [show (1 : ℂ) + (γ t - 1) = γ t by ring] at h
  have hnz : ∀ t, γ t ≠ 0 := fun t => slitPlane_ne_zero (hslit t)
  have hL : IsLoop γ a b := ⟨hγc, hnz, hclosed⟩
  have hlogc : Continuous (fun t => Complex.log (γ t)) := hγc.clog hslit
  have hloge : ∀ t, exp (Complex.log (γ t)) = γ t := fun t => Complex.exp_log (hnz t)
  rw [windingNumber_eq_zero_iff hL hlogc hloge, hclosed]

/-- The scaled circle `θ ↦ r e^{iθ}` (`r > 0`) winds once. -/
theorem windingNumber_scaled_circle {r : ℝ} (hr : 0 < r) :
    windingNumber (fun θ => ↑r * exp (I * ↑θ)) 0 (2 * Real.pi) = 1 := by
  simpa using windingNumber_center_zero 1 r hr

/-- **An enclosed simple zero winds once.**  For `‖ρ − c‖ < r`, the linear factor `θ ↦ (c + r e^{iθ})
− ρ` winds the boundary circle exactly once about the origin. -/
theorem windingNumber_linear_enclosing {c ρ : ℂ} {r : ℝ} (hr : 0 < r) (hin : ‖ρ - c‖ < r) :
    windingNumber (fun θ => (c + ↑r * exp (I * ↑θ)) - ρ) 0 (2 * Real.pi) = 1 := by
  have hrne : (↑r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let u : ℝ → ℂ := fun s => 1 + (c - ρ) / ↑r * exp (-(I * ↑s))
  have he : ∀ θ : ℝ, exp (I * ↑θ) * exp (-(I * ↑θ)) = 1 := fun θ => by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hfact : ∀ θ : ℝ, (c + ↑r * exp (I * ↑θ)) - ρ
      = (↑r * exp (I * ↑θ)) * (1 + (c - ρ) / ↑r * exp (-(I * ↑θ))) := by
    intro θ
    have hstep : (↑r * exp (I * ↑θ)) * ((c - ρ) / ↑r * exp (-(I * ↑θ)))
        = (c - ρ) * (exp (I * ↑θ) * exp (-(I * ↑θ))) := by field_simp
    rw [mul_add, mul_one, hstep, he θ, mul_one]; ring
  have hucont : Continuous u := by fun_prop
  have hunz : ∀ θ, ‖u θ - 1‖ < 1 := by
    intro θ
    have hnexp : ‖exp (-(I * (↑θ : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]; norm_num [Complex.neg_re, Complex.mul_re]
    have hsub : u θ - 1 = (c - ρ) / ↑r * exp (-(I * ↑θ)) := by show _ = _; ring
    rw [hsub, norm_mul, hnexp, mul_one, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, div_lt_one hr]
    calc ‖c - ρ‖ = ‖ρ - c‖ := by rw [← norm_neg, neg_sub]
      _ < r := hin
  have huclosed : u 0 = u (2 * Real.pi) := by
    show (1 : ℂ) + (c - ρ) / ↑r * exp (-(I * ((0 : ℝ) : ℂ)))
       = 1 + (c - ρ) / ↑r * exp (-(I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)))
    rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      show (-(I * (((2 : ℝ) * Real.pi : ℝ) : ℂ))) = -(2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hLc : IsLoop (fun θ : ℝ => ↑r * exp (I * ↑θ)) 0 (2 * Real.pi) :=
    ⟨by fun_prop, fun θ => mul_ne_zero hrne (Complex.exp_ne_zero _), by
      show (↑r : ℂ) * exp (I * ((0 : ℝ) : ℂ)) = ↑r * exp (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ))
      rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        show (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
        Complex.exp_two_pi_mul_I]⟩
  have hLu : IsLoop u 0 (2 * Real.pi) :=
    ⟨hucont, fun θ h0 => by
      have := hunz θ; rw [h0, zero_sub, norm_neg, norm_one] at this; exact lt_irrefl 1 this,
      huclosed⟩
  have hweq : (fun θ : ℝ => (c + ↑r * exp (I * ↑θ)) - ρ)
      = (fun θ : ℝ => (↑r * exp (I * ↑θ)) * u θ) := funext hfact
  rw [hweq, windingNumber_mul hLc hLu, windingNumber_scaled_circle hr]
  show (1 : ℤ) + windingNumber u 0 (2 * Real.pi) = 1
  rw [windingNumber_eq_zero_of_ball1 hucont huclosed hunz, add_zero]

/-- The boundary circle `θ ↦ c + r e^{iθ}` misses a strictly interior point `ρ`, so its linear factor
is a loop. -/
theorem isLoop_linear_enclosing {c ρ : ℂ} {r : ℝ} (hr : 0 < r) (hin : ‖ρ - c‖ < r) :
    IsLoop (fun θ => (c + ↑r * exp (I * ↑θ)) - ρ) 0 (2 * Real.pi) := by
  refine ⟨by fun_prop, fun θ => ?_, ?_⟩
  · have hnorm : ‖(c + ↑r * exp (I * ↑θ)) - ρ‖ ≥ r - ‖ρ - c‖ := by
      have h1 : (c + ↑r * exp (I * ↑θ)) - ρ = ↑r * exp (I * ↑θ) - (ρ - c) := by ring
      rw [h1]
      calc ‖↑r * exp (I * ↑θ) - (ρ - c)‖ ≥ ‖(↑r : ℂ) * exp (I * ↑θ)‖ - ‖ρ - c‖ :=
            norm_sub_norm_le _ _
        _ = r - ‖ρ - c‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp]
            simp [Complex.mul_re]
    intro h0
    rw [h0, norm_zero] at hnorm
    linarith [hnorm, sub_pos.mpr hin]
  · show (c + ↑r * exp (I * ((0 : ℝ) : ℂ))) - ρ = (c + ↑r * exp (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ))) - ρ
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]

/-- The winding number of a finite product of loops is the sum of the winding numbers. -/
theorem windingNumber_prod {ι : Type*} (s : Finset ι) (γ : ι → ℝ → ℂ) {a b : ℝ}
    (hL : ∀ i ∈ s, IsLoop (γ i) a b) :
    windingNumber (fun θ => ∏ i ∈ s, γ i θ) a b = ∑ i ∈ s, windingNumber (γ i) a b := by
  classical
  induction s using Finset.induction with
  | empty => simpa using windingNumber_const (one_ne_zero) a b
  | @insert j t hjt ih =>
    have hLt : ∀ i ∈ t, IsLoop (γ i) a b := fun i hi => hL i (Finset.mem_insert_of_mem hi)
    have hLj : IsLoop (γ j) a b := hL j (Finset.mem_insert_self j t)
    have hLprod : IsLoop (fun θ => ∏ i ∈ t, γ i θ) a b := by
      refine ⟨continuous_finsetProd t (fun i hi => (hLt i hi).continuous), fun θ => ?_,
        Finset.prod_congr rfl (fun i hi => (hLt i hi).closed)⟩
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => (hLt i hi).nonzero θ)
    have hfun : (fun θ => ∏ i ∈ insert j t, γ i θ)
        = (fun θ => γ j θ * ∏ i ∈ t, γ i θ) := by
      funext θ; rw [Finset.prod_insert hjt]
    rw [hfun, windingNumber_mul hLj hLprod, ih hLt, Finset.sum_insert hjt]

/-- **The argument principle for a divisor.**  The winding number of `θ ↦ ∏ᵢ (γ(θ) − ρᵢ)^{mᵢ}` around
the circle `γ(θ) = c + r e^{iθ}`, all `ρᵢ` strictly inside, is the total enclosed order `Σᵢ mᵢ`. -/
theorem windingNumber_divisor {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hin : ∀ i ∈ s, ‖ρ i - c‖ < r) :
    windingNumber (fun θ => ∏ i ∈ s, ((c + ↑r * exp (I * ↑θ)) - ρ i) ^ m i) 0 (2 * Real.pi)
      = ∑ i ∈ s, (m i : ℤ) := by
  have hLfac : ∀ i ∈ s, IsLoop (fun θ => ((c + ↑r * exp (I * ↑θ)) - ρ i) ^ m i) 0 (2 * Real.pi) := by
    intro i hi
    obtain ⟨hc, hnz, hcl⟩ := isLoop_linear_enclosing hr (hin i hi)
    exact ⟨hc.pow (m i), fun θ => pow_ne_zero _ (hnz θ), by simp only [hcl]⟩
  rw [windingNumber_prod s _ hLfac]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [windingNumber_pow (isLoop_linear_enclosing hr (hin i hi)) (m i),
    windingNumber_linear_enclosing hr (hin i hi), mul_one]

/-- **The loop deck charge counts the enclosed order.**  The rung-`k` deck charge of the boundary
circle is `wCharge (2^k) (Σᵢ mᵢ)` — the reduction of the total enclosed order.  This is the
topological winding realisation of the multi-zero deck charge (the argument-principle twin of the
algebraic `box_charge_eq_deckRed`). -/
theorem loopCharge_divisor {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hin : ∀ i ∈ s, ‖ρ i - c‖ < r) (k : ℕ) :
    loopCharge k (fun θ => ∏ i ∈ s, ((c + ↑r * exp (I * ↑θ)) - ρ i) ^ m i) 0 (2 * Real.pi)
      = wCharge (2 ^ k) (∑ i ∈ s, (m i : ℤ)) := by
  rw [loopCharge, windingNumber_divisor s ρ m c r hr hin]

end RHTower
