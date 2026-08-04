import GaloisForLFunctions.RHTower.Sieve.MellinAbscissaDecay

/-!
# The decay constant, uniform in the cutoff

`exists_bound_mellin_smoothWeight_abscissa` fixes the cutoff `(N, H)` before producing its constant.
That is enough while `N` is fixed and only the contour parameter moves, but the final statement lets
`N` tend to infinity, and then a constant depending on `N` says nothing.

The dependence is in fact explicit: the only genuinely unknown quantity is the bound on the
iterated derivatives of the cutoff profile, and `exists_bound_iteratedDeriv_smoothWeight_uniform`
already provides that uniformly in `N` and `H`.  Everything else is the factor
`H^{-(j+1)}·(N+H+1)^{j+1}`, which for `H ≍ N` is bounded.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **Decay of the cutoff's transform, uniform in the cutoff.**  The constant depends only on the
order; the cutoff enters through the explicit factor `H^{-(j+1)}·(N+H+1)^{j+1}`. -/
theorem exists_bound_mellin_smoothWeight_uniform_all (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N H : ℝ, 0 < N → 0 < H → ∀ s : ℂ, 0 < s.re →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ Cj / H ^ (j + 1) * (N + H + 1) ^ (j + 1 : ℕ) * (N + H + 1) ^ s.re := by
  obtain ⟨Cj, hCj, hbound⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform (j + 1)
  refine ⟨Cj, hCj, fun N H hN hH s hs => ?_⟩
  have hb1 : (1 : ℝ) ≤ N + H + 1 := by linarith
  have hb0 : (0 : ℝ) < N + H + 1 := by linarith
  have him : ∀ i : ℕ, |s.im| ≤ ‖s + 1 + (i : ℂ)‖ := by
    intro i
    have himeq : (s + 1 + (i : ℂ)).im = s.im := by simp
    calc |s.im| = |(s + 1 + (i : ℂ)).im| := by rw [himeq]
      _ ≤ ‖s + 1 + (i : ℂ)‖ := Complex.abs_im_le_norm _
  have hprod : |s.im| ^ j ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    calc |s.im| ^ j = ∏ _i ∈ Finset.range j, |s.im| := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => him i)
  have hs0 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hstep : |s.im| ^ (j + 1) ≤ ‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    rw [pow_succ']
    exact mul_le_mul hs0 hprod (by positivity) (norm_nonneg _)
  have hsplit : (N + H + 1) ^ (s.re + (j : ℝ))
      = (N + H + 1) ^ s.re * (N + H + 1) ^ (j : ℕ) := by
    rw [Real.rpow_add hb0, Real.rpow_natCast]
  have hCjH : (0 : ℝ) ≤ Cj / H ^ (j + 1) := by positivity
  have hkey : ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ (Cj / H ^ (j + 1) * ((N + H + 1) ^ s.re * (N + H + 1) ^ (j : ℕ)))
          * |N + H + 1 - N / 2| := by
    rw [mellin_smoothWeight_eq s, norm_mellin_smoothWeight_mul_eq hN hH hs j]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have hxmem : x ∈ Set.Ioc (N / 2) (N + H + 1) := by
      rw [Set.uIoc_of_le (by linarith)] at hx
      exact hx
    have hx0 : (0 : ℝ) < x := lt_trans (by linarith : (0 : ℝ) < N / 2) hxmem.1
    have hxb : x ≤ N + H + 1 := hxmem.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (s + 1 + (j : ℂ) - 1).re = s.re + (j : ℝ) := by
      simp
      ring
    rw [hre]
    have hderiv : |iteratedDeriv j (deriv (smoothWeight N H)) x| ≤ Cj / H ^ (j + 1) := by
      rw [← iteratedDeriv_succ']
      exact hbound N H hH x
    have hexp1 : x ^ (s.re + (j : ℝ)) ≤ (N + H + 1) ^ (s.re + (j : ℝ)) := by
      refine Real.rpow_le_rpow hx0.le hxb ?_
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hpowpos : (0 : ℝ) < x ^ (s.re + (j : ℝ)) := Real.rpow_pos_of_pos hx0 _
    calc |iteratedDeriv j (deriv (smoothWeight N H)) x| * x ^ (s.re + (j : ℝ))
        ≤ (Cj / H ^ (j + 1)) * x ^ (s.re + (j : ℝ)) :=
          mul_le_mul_of_nonneg_right hderiv hpowpos.le
      _ ≤ (Cj / H ^ (j + 1)) * (N + H + 1) ^ (s.re + (j : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp1 hCjH
      _ = Cj / H ^ (j + 1) * ((N + H + 1) ^ s.re * (N + H + 1) ^ (j : ℕ)) := by rw [hsplit]
  have hlen : |N + H + 1 - N / 2| ≤ N + H + 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcoef : (0 : ℝ) ≤ Cj / H ^ (j + 1) * ((N + H + 1) ^ s.re * (N + H + 1) ^ (j : ℕ)) := by
    have : (0 : ℝ) < (N + H + 1) ^ s.re := Real.rpow_pos_of_pos hb0 _
    positivity
  have hfinal : (Cj / H ^ (j + 1) * ((N + H + 1) ^ s.re * (N + H + 1) ^ (j : ℕ)))
      * |N + H + 1 - N / 2|
      ≤ Cj / H ^ (j + 1) * (N + H + 1) ^ (j + 1 : ℕ) * (N + H + 1) ^ s.re := by
    have hstep2 := mul_le_mul_of_nonneg_left hlen hcoef
    refine le_trans hstep2 (le_of_eq ?_)
    rw [pow_succ]
    ring
  calc |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ (‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ ≤ _ := le_trans hkey hfinal

/-- The form the contour argument consumes: valid up to a given abscissa, uniform in the cutoff. -/
theorem exists_bound_mellin_smoothWeight_uniform_upto (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N H : ℝ, 0 < N → 0 < H → ∀ σ : ℝ, ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ Cj / H ^ (j + 1) * (N + H + 1) ^ (j + 1 : ℕ) * (N + H + 1) ^ σ := by
  obtain ⟨Cj, hCj, hbd⟩ := exists_bound_mellin_smoothWeight_uniform_all j
  refine ⟨Cj, hCj, fun N H hN hH σ s hs hsσ => ?_⟩
  have hb1 : (1 : ℝ) ≤ N + H + 1 := by linarith
  refine le_trans (hbd N H hN hH s hs) ?_
  have hcoef : (0 : ℝ) ≤ Cj / H ^ (j + 1) * (N + H + 1) ^ (j + 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 hsσ) hcoef

end RHTower.Sieve
