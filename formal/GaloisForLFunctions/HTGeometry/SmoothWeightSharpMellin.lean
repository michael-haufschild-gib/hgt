import GaloisForLFunctions.HTGeometry.SmoothWeightMellin

/-!
# Sharp support-length decay for smooth-cutoff Mellin transforms

The generic iterated integration-by-parts identity expresses the Mellin transform through a
derivative of the cutoff.  Bounding that derivative on the larger auxiliary integration interval
loses a factor comparable to the cutoff location.  Every positive-order derivative is actually
supported on the transition window `[N, N + H]`, whose length is exactly `H`.

The theorem below records the resulting scale law uniformly in `N` and `H`.  For the first two
orders it gives, respectively, a first-derivative bound independent of `H` and a second-derivative
bound proportional to `H⁻¹`; together these are the two estimates needed for weighted vertical
Mellin mass bounds.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **Sharp support-length Mellin decay.**  The `j`-fold derivative integral is supported on an
interval of length exactly `H`, rather than the larger auxiliary interval used to justify
integration by parts.  The constant depends only on the derivative order. -/
theorem exists_bound_mellin_smoothWeight_uniform_support (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ N H : ℝ, 0 < N → 0 < H → ∀ s : ℂ, 0 < s.re →
      ‖s‖ * (∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ Cj / H ^ (j + 1) * (N + H) ^ (s.re + (j : ℝ)) * H := by
  obtain ⟨Cj, hCj, hbound⟩ := exists_bound_iteratedDeriv_smoothWeight_uniform (j + 1)
  refine ⟨Cj, hCj, fun N H hN hH s hs => ?_⟩
  let f : ℝ → ℂ := fun x =>
    ((iteratedDeriv j (deriv (smoothWeight N H)) x : ℝ) : ℂ) *
      (x : ℂ) ^ (s + 1 + (j : ℂ) - 1)
  have hfcont : ContinuousOn f (Ioi (0 : ℝ)) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuous_ofReal.continuousAt.comp_of_eq
        ((contDiff_top_iteratedDeriv (contDiff_deriv_smoothWeight N H) j).continuous.continuousAt)
        rfl
    · exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Or.inl (by simpa using hx))
  have hIleft : IntervalIntegrable f volume (N / 2) N := by
    refine (hfcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < N / 2) hx.1
  have hImid : IntervalIntegrable f volume N (N + H) := by
    refine (hfcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact lt_of_lt_of_le hN hx.1
  have hIright : IntervalIntegrable f volume (N + H) (N + H + 1) := by
    refine (hfcont.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < N + H) hx.1
  have hleft : (∫ x in (N / 2)..N, f x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ N := by
      rw [ae_iff]
      rw [show {a : ℝ | ¬a ≠ N} = {N} by ext x; simp]
      exact measure_singleton N
    filter_upwards [hne] with x hxne hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxlt : x < N := lt_of_le_of_ne hx.2 hxne
    change ((iteratedDeriv j (deriv (smoothWeight N H)) x : ℝ) : ℂ) *
      (x : ℂ) ^ (s + 1 + (j : ℂ) - 1) = 0
    rw [← iteratedDeriv_succ',
      iteratedDeriv_smoothWeight_eq_zero_of_lt hH (Nat.succ_ne_zero j) hxlt]
    simp
  have hright : (∫ x in (N + H)..(N + H + 1), f x) = 0 := by
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [] with x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    change ((iteratedDeriv j (deriv (smoothWeight N H)) x : ℝ) : ℂ) *
      (x : ℂ) ^ (s + 1 + (j : ℂ) - 1) = 0
    rw [← iteratedDeriv_succ',
      iteratedDeriv_smoothWeight_eq_zero_of_gt hH (Nat.succ_ne_zero j) hx.1]
    simp
  have hsupport : (∫ x in (N / 2)..(N + H + 1), f x) = ∫ x in N..(N + H), f x := by
    have h₁ := intervalIntegral.integral_add_adjacent_intervals hIleft hImid
    have h₂ := intervalIntegral.integral_add_adjacent_intervals (hIleft.trans hImid) hIright
    rw [hleft, zero_add] at h₁
    rw [← h₁, hright, add_zero] at h₂
    exact h₂.symm
  rw [mellin_smoothWeight_eq s, norm_mellin_smoothWeight_mul_eq hN hH hs j]
  change ‖∫ x in (N / 2)..(N + H + 1), f x‖ ≤ _
  rw [hsupport]
  have hmidbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Cj / H ^ (j + 1) * (N + H) ^ (s.re + (j : ℝ))) (f := f)
    (a := N) (b := N + H) (fun x hx => by
      rw [Set.uIoc_of_le (by linarith)] at hx
      have hx0 : (0 : ℝ) < x := lt_trans hN hx.1
      have hxb : x ≤ N + H := hx.2
      change ‖((iteratedDeriv j (deriv (smoothWeight N H)) x : ℝ) : ℂ) *
        (x : ℂ) ^ (s + 1 + (j : ℂ) - 1)‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (s + 1 + (j : ℂ) - 1).re = s.re + (j : ℝ) := by simp; ring
      rw [hre]
      have hderiv : |iteratedDeriv j (deriv (smoothWeight N H)) x|
          ≤ Cj / H ^ (j + 1) := by
        rw [← iteratedDeriv_succ']
        exact hbound N H hH x
      have hexp : x ^ (s.re + (j : ℝ)) ≤ (N + H) ^ (s.re + (j : ℝ)) := by
        refine Real.rpow_le_rpow hx0.le hxb ?_
        exact add_nonneg hs.le (Nat.cast_nonneg j)
      exact mul_le_mul hderiv hexp (Real.rpow_pos_of_pos hx0 _).le (by positivity))
  rw [show N + H - N = H by ring, abs_of_pos hH] at hmidbound
  exact hmidbound

/-- **Two-scale vertical-line form.**  Uniform constants control the Mellin transform by one power
of the height independently of `H`, and by two powers at the exact transition-scale cost
`(N + H) / H`.  Interpolating these inequalities yields every fractional decay order between one
and two without losing a full power of the window ratio. -/
theorem exists_mellin_smoothWeight_two_scale_bounds :
    ∃ C₀ C₁ : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ s : ℂ, 0 < s.re →
        |s.im| * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
            ≤ C₀ * (N + H) ^ s.re ∧
          |s.im| ^ 2 * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
            ≤ C₁ * ((N + H) / H) * (N + H) ^ s.re := by
  obtain ⟨A₀, hA₀, hb₀⟩ := exists_bound_mellin_smoothWeight_uniform_support 0
  obtain ⟨A₁, hA₁, hb₁⟩ := exists_bound_mellin_smoothWeight_uniform_support 1
  refine ⟨A₀ + 1, A₁ + 1, by linarith, by linarith, fun N H hN hH s hs => ?_⟩
  have hX : (0 : ℝ) < N + H := by linarith
  have hz := hb₀ N H hN hH s hs
  simp only [Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, add_zero,
    pow_one] at hz
  have hfirstBase : ‖s‖ * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ A₀ * (N + H) ^ s.re := by
    calc
      ‖s‖ * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
          ≤ A₀ / H * (N + H) ^ s.re * H := hz
      _ = A₀ * (N + H) ^ s.re := by field_simp
  have hfirst : |s.im| * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ (A₀ + 1) * (N + H) ^ s.re := by
    calc
      |s.im| * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
          ≤ ‖s‖ * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ :=
            mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg _)
      _ ≤ A₀ * (N + H) ^ s.re := hfirstBase
      _ ≤ (A₀ + 1) * (N + H) ^ s.re :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hX _).le
  have ho := hb₁ N H hN hH s hs
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, mul_one,
    Nat.cast_zero, add_zero, Nat.cast_one, pow_two] at ho
  have him1 : |s.im| ≤ ‖s + 1‖ := by
    calc |s.im| = |(s + 1).im| := by simp
      _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
  have himprod : |s.im| ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [pow_two]
    exact mul_le_mul (Complex.abs_im_le_norm s) him1 (abs_nonneg _) (norm_nonneg _)
  have hpow : (N + H) ^ (s.re + 1) = (N + H) ^ s.re * (N + H) := by
    rw [Real.rpow_add hX.le, Real.rpow_one]
  have hsecondBase : ‖s‖ * ‖s + 1‖ *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ A₁ * ((N + H) / H) * (N + H) ^ s.re := by
    rw [hpow] at ho
    calc
      ‖s‖ * ‖s + 1‖ * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
          ≤ A₁ / H ^ 2 * ((N + H) ^ s.re * (N + H)) * H := ho
      _ = A₁ * ((N + H) / H) * (N + H) ^ s.re := by
        field_simp
        ring
  refine ⟨hfirst, ?_⟩
  calc
    |s.im| ^ 2 * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
        ≤ (‖s‖ * ‖s + 1‖) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ :=
          mul_le_mul_of_nonneg_right himprod (norm_nonneg _)
    _ ≤ A₁ * ((N + H) / H) * (N + H) ^ s.re := hsecondBase
    _ ≤ (A₁ + 1) * ((N + H) / H) * (N + H) ^ s.re := by
      have hratio : 0 ≤ (N + H) / H := by positivity
      have hpowpos : 0 ≤ (N + H) ^ s.re := (Real.rpow_pos_of_pos hX _).le
      nlinarith

end GaloisForLFunctions.HTGeometry
