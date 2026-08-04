import GaloisForLFunctions.RHTower.Sieve.HorizontalEdgeBound

/-!
# The decay constant, with its abscissa dependence exposed

`exists_bound_mellin_smoothWeight` bounds the decay of the cutoff's transform uniformly on
`0 < Re s ≤ σmax`, with a constant that hides a factor `(N+H+1)^{σmax}`.  Hiding it is what made the
constant unusable when the abscissa varies with the contour parameter.

The bound below keeps the abscissa dependence explicit and in the only form it can take: the
integrand of the Mellin transform carries `x^{Re s}`, and `x` is at most `N+H+1` on the support, so

    |Im s|^{j+1}·‖W(s)‖ ≤ C · (N+H+1)^{Re s}

with `C` depending on the cutoff and the order only.  Every constant the contour argument needs is
an instance of this with `Re s` at the relevant abscissa.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **Decay of the cutoff's transform, abscissa dependence explicit.** -/
theorem exists_bound_mellin_smoothWeight_abscissa {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ C * (N + H + 1) ^ s.re := by
  obtain ⟨Cj, hCj, hbound⟩ := exists_bound_iteratedDeriv_smoothWeight hH N (j + 1)
  have hb1 : (1 : ℝ) ≤ N + H + 1 := by linarith
  have hb0 : (0 : ℝ) < N + H + 1 := by linarith
  set M : ℝ := Cj / H ^ (j + 1) * (N + H + 1) ^ (j : ℕ) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ Cj / H ^ (j + 1) := by positivity
    positivity
  refine ⟨M * |N + H + 1 - N / 2|, by positivity, fun s hs => ?_⟩
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
  have hkey : ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
      ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ M * (N + H + 1) ^ s.re * |N + H + 1 - N / 2| := by
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
      exact hbound x
    have hexp1 : x ^ (s.re + (j : ℝ)) ≤ (N + H + 1) ^ (s.re + (j : ℝ)) := by
      refine Real.rpow_le_rpow hx0.le hxb ?_
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hpowpos : (0 : ℝ) < x ^ (s.re + (j : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hCjH : (0 : ℝ) ≤ Cj / H ^ (j + 1) := by positivity
    calc |iteratedDeriv j (deriv (smoothWeight N H)) x| * x ^ (s.re + (j : ℝ))
        ≤ (Cj / H ^ (j + 1)) * x ^ (s.re + (j : ℝ)) :=
          mul_le_mul_of_nonneg_right hderiv hpowpos.le
      _ ≤ (Cj / H ^ (j + 1)) * (N + H + 1) ^ (s.re + (j : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp1 hCjH
      _ = M * (N + H + 1) ^ s.re := by rw [hsplit, hM]; ring
  calc |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ (‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ ≤ M * (N + H + 1) ^ s.re * |N + H + 1 - N / 2| := hkey
    _ = M * |N + H + 1 - N / 2| * (N + H + 1) ^ s.re := by ring

/-- The form the contour argument consumes: a decay constant valid up to a given abscissa, with the
abscissa dependence a single explicit power. -/
theorem exists_bound_mellin_smoothWeight_upto {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 0 < σ → ∀ s : ℂ, 0 < s.re → s.re ≤ σ →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ C * (N + H + 1) ^ σ := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_abscissa hN hH j
  have hb1 : (1 : ℝ) ≤ N + H + 1 := by linarith
  refine ⟨C, hC, fun σ _ s hs hsσ => ?_⟩
  refine le_trans (hbd s hs) ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 hsσ) hC

end RHTower.Sieve
