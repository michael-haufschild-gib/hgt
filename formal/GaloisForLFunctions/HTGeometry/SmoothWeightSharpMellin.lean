import GaloisForLFunctions.HTGeometry.SmoothWeightMellin
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

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
  norm_num at hz
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
  norm_num [Finset.prod_range_succ] at ho
  have him1 : |s.im| ≤ ‖s + 1‖ := by
    calc |s.im| = |(s + 1).im| := by simp
      _ ≤ ‖s + 1‖ := Complex.abs_im_le_norm _
  have himprod : |s.im| ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [pow_two]
    exact mul_le_mul (Complex.abs_im_le_norm s) him1 (abs_nonneg _) (norm_nonneg _)
  have hpow : (N + H) ^ (s.re + 1) = (N + H) ^ s.re * (N + H) := by
    rw [Real.rpow_add hX, Real.rpow_one]
  have hsecondBase : ‖s‖ * ‖s + 1‖ *
        ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ A₁ * ((N + H) / H) * (N + H) ^ s.re := by
    rw [hpow] at ho
    calc
      ‖s‖ * ‖s + 1‖ * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
          ≤ A₁ / H ^ 2 * ((N + H) ^ s.re * (N + H)) * H := ho
      _ = A₁ * ((N + H) / H) * (N + H) ^ s.re := by
        field_simp
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

/-- Interpolation between a linear and a quadratic weighted bound. -/
theorem rpow_interpolation_of_linear_quadratic_bounds {t w A B q : ℝ} (ht : 0 < t) (hw : 0 < w)
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h₁ : t * w ≤ A) (h₂ : t ^ 2 * w ≤ B) :
    t ^ (1 + q) * w ≤ A ^ (1 - q) * B ^ q := by
  have hp₁ := Real.rpow_le_rpow (mul_nonneg ht.le hw.le) h₁ (sub_nonneg.mpr hq1)
  have hp₂ := Real.rpow_le_rpow (mul_nonneg (sq_nonneg t) hw.le) h₂ hq0
  have hmul := mul_le_mul hp₁ hp₂
    (Real.rpow_nonneg (mul_nonneg (sq_nonneg t) hw.le) q)
    (Real.rpow_nonneg hA (1 - q))
  calc
    t ^ (1 + q) * w = (t * w) ^ (1 - q) * (t ^ 2 * w) ^ q := by
      rw [Real.mul_rpow ht.le hw.le, Real.mul_rpow (sq_nonneg t) hw.le,
        ← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
      calc
        t ^ (1 + q) * w =
            (t ^ (1 - q) * t ^ ((2 : ℝ) * q)) * (w ^ (1 - q) * w ^ q) := by
              rw [← Real.rpow_add ht, ← Real.rpow_add hw]
              have ht_exp : 1 - q + 2 * q = 1 + q := by ring
              have hw_exp : 1 - q + q = 1 := by ring
              rw [ht_exp, hw_exp, Real.rpow_one]
        _ = t ^ (1 - q) * w ^ (1 - q) * (t ^ ((2 : ℝ) * q) * w ^ q) := by ring
    _ ≤ A ^ (1 - q) * B ^ q := hmul

/-- **Fractional vertical decay at exact window cost.**  Every order `1 + q`, `0 ≤ q ≤ 1`, costs
only the fractional window ratio `((N + H) / H)^q`.  This is the scale-compatible form needed to
absorb a reciprocal Dirichlet-series bound of any smaller power order. -/
theorem exists_mellin_smoothWeight_fractional_scale_bounds :
    ∃ C₀ C₁ : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ s : ℂ, 0 < s.re →
        ∀ q : ℝ, 0 ≤ q → q ≤ 1 → 1 ≤ |s.im| →
          |s.im| ^ (1 + q) *
              ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
            ≤ (C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ s.re := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hscale⟩ := exists_mellin_smoothWeight_two_scale_bounds
  refine ⟨C₀, C₁, hC₀, hC₁, fun N H hN hH s hs q hq0 hq1 him => ?_⟩
  have hX : (0 : ℝ) < N + H := by linarith
  have hR : (0 : ℝ) < (N + H) / H := by positivity
  obtain ⟨hlinear, hquadratic⟩ := hscale N H hN hH s hs
  set w : ℝ := ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ with hwdef
  by_cases hw0 : w = 0
  · rw [hw0, mul_zero]
    positivity
  have hw : 0 < w := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  have ht : 0 < |s.im| := zero_lt_one.trans_le him
  have hC₀0 : 0 ≤ C₀ := zero_le_one.trans hC₀
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  have hinterp := rpow_interpolation_of_linear_quadratic_bounds ht hw
    (mul_nonneg hC₀0 (Real.rpow_pos_of_pos hX _).le) hq0 hq1 hlinear hquadratic
  refine hinterp.trans_eq ?_
  rw [Real.mul_rpow hC₀0 (Real.rpow_nonneg hX.le s.re),
    Real.mul_rpow (mul_nonneg hC₁0 hR.le) (Real.rpow_nonneg hX.le s.re),
    Real.mul_rpow hC₁0 hR.le,
    ← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le]
  calc
    C₀ ^ (1 - q) * (N + H) ^ (s.re * (1 - q)) *
        (C₁ ^ q * ((N + H) / H) ^ q * (N + H) ^ (s.re * q)) =
      C₀ ^ (1 - q) * C₁ ^ q * ((N + H) / H) ^ q *
        ((N + H) ^ (s.re * (1 - q)) * (N + H) ^ (s.re * q)) := by ring
    _ = C₀ ^ (1 - q) * C₁ ^ q * ((N + H) / H) ^ q * (N + H) ^ s.re := by
      rw [← Real.rpow_add hX]
      congr 2
      ring
    _ = (C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q *
        (N + H) ^ s.re := by ring

/-- **Weighted vertical Mellin mass from fractional decay.**  If a factor grows like
`(2 + |y|)^A` and `A < q ≤ 1`, then the smooth cutoff absorbs that growth with window cost only
`((N + H) / H)^q`.  The bound is uniform over every factor satisfying the stated line estimate;
integrability is separated as an input so contour-shift theorems can supply it directly. -/
theorem exists_integral_norm_mul_mellin_smoothWeight_fractional_bound :
    ∃ C₀ C₁ : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧
      ∀ N H c A q K : ℝ, 0 < N → 0 < H → 0 < c → 0 ≤ A → A < q → q ≤ 1 → 0 ≤ K →
        ∀ F : ℂ → ℂ,
          (∀ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * I)‖ ≤ K * (2 + |y|) ^ A) →
          Integrable (fun y : ℝ => F ((c : ℂ) + (y : ℝ) * I) *
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * I)) →
          ∫ y : ℝ, ‖F ((c : ℂ) + (y : ℝ) * I) *
              mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * I)‖
            ≤ 2 * (K * 3 ^ A * ((N + H) ^ c / c)) +
              2 * (K * 3 ^ A *
                ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c)) *
                (1 / (q - A)) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hfrac⟩ :=
    exists_mellin_smoothWeight_fractional_scale_bounds
  refine ⟨C₀, C₁, hC₀, hC₁, fun N H c A q K hN hH hc hA hAq hq1 hK F hF hprod => ?_⟩
  have hq0 : 0 ≤ q := by linarith
  have hX : (0 : ℝ) < N + H := by linarith
  let W : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
      ((c : ℂ) + (y : ℝ) * I)
  let g : ℝ → ℝ := fun y => ‖F ((c : ℂ) + (y : ℝ) * I) * W y‖
  have hgint : Integrable g := by
    simpa [g, W] using hprod.norm
  let tail : Set ℝ := {y : ℝ | 1 ≤ |y|}
  have htailmeas : MeasurableSet tail := measurableSet_centralTail 1
  have htailpoint : ∀ y : ℝ, 1 ≤ |y| →
      g y ≤ (K * 3 ^ A *
          ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c)) *
        |y| ^ (-(1 + q - A)) := by
    intro y hy
    have ht : (0 : ℝ) < |y| := zero_lt_one.trans_le hy
    have hsre : (((c : ℂ) + (y : ℝ) * I)).re = c := by simp
    have hsim : (((c : ℂ) + (y : ℝ) * I)).im = y := by simp
    have hfrac' := hfrac N H hN hH ((c : ℂ) + (y : ℝ) * I)
      (by rw [hsre]; exact hc) q hq0 hq1 (by rwa [hsim])
    rw [hsre, hsim] at hfrac'
    have hden : (0 : ℝ) < |y| ^ (1 + q) := Real.rpow_pos_of_pos ht _
    have hW : ‖W y‖ ≤
        ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c) *
          |y| ^ (-(1 + q)) := by
      change ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * I)‖ ≤ _
      rw [Real.rpow_neg ht.le, ← div_eq_mul_inv, le_div_iff₀ hden]
      simpa [mul_comm] using hfrac'
    have hgrowth : (2 + |y|) ^ A ≤ 3 ^ A * |y| ^ A := by
      have hbase : 2 + |y| ≤ 3 * |y| := by linarith
      calc
        (2 + |y|) ^ A ≤ (3 * |y|) ^ A :=
          Real.rpow_le_rpow (by positivity) hbase hA
        _ = 3 ^ A * |y| ^ A := Real.mul_rpow (by norm_num) (abs_nonneg y)
    change ‖F ((c : ℂ) + (y : ℝ) * I) * W y‖ ≤ _
    rw [norm_mul]
    calc
      ‖F ((c : ℂ) + (y : ℝ) * I)‖ * ‖W y‖
          ≤ (K * (2 + |y|) ^ A) *
              (((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c) *
                |y| ^ (-(1 + q))) :=
            mul_le_mul (hF y) hW (norm_nonneg _) (by positivity)
      _ ≤ (K * (3 ^ A * |y| ^ A)) *
              (((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c) *
                |y| ^ (-(1 + q))) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth hK) (by positivity)
      _ = (K * 3 ^ A *
          ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c)) *
          |y| ^ (-(1 + q - A)) := by
            have hpowcombine : |y| ^ A * |y| ^ (-(1 + q)) =
                |y| ^ (-(1 + q - A)) := by
              rw [← Real.rpow_add ht]
              congr 1
              ring
            calc
              (K * (3 ^ A * |y| ^ A)) *
                    (((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c) *
                      |y| ^ (-(1 + q))) =
                  (K * 3 ^ A *
                    ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c)) *
                    (|y| ^ A * |y| ^ (-(1 + q))) := by ring
              _ = _ := by rw [hpowcombine]
  have hp : 1 < 1 + q - A := by linarith
  have htailbound := setIntegral_le_of_le_powerTail (f := g)
    (K := K * 3 ^ A *
      ((C₀ ^ (1 - q) * C₁ ^ q) * ((N + H) / H) ^ q * (N + H) ^ c))
    (t := 1) (p := 1 + q - A) (fun y => norm_nonneg _) zero_lt_one hp htailpoint
  rw [Real.one_rpow] at htailbound
  have hpden : 1 + q - A - 1 = q - A := by ring
  rw [hpden] at htailbound
  have hcompl : tailᶜ = Ioo (-1 : ℝ) 1 := by
    ext y
    simp only [tail, mem_compl_iff, mem_setOf_eq, mem_Ioo]
    rw [not_le, abs_lt]
  have hcenterpoint : ∀ y ∈ Ioo (-1 : ℝ) 1,
      g y ≤ K * 3 ^ A * ((N + H) ^ c / c) := by
    intro y hy
    have hyabs : |y| < 1 := (abs_lt).2 hy
    have hsre : (((c : ℂ) + (y : ℝ) * I)).re = c := by simp
    have hWtriv := norm_mellin_smoothWeight_le_pow (N := N) (H := H) hN.le hH
      (s := (c : ℂ) + (y : ℝ) * I) (by rw [hsre]; exact hc)
    rw [hsre] at hWtriv
    have hWtriv' : ‖W y‖ ≤ (N + H) ^ c / c := by
      simpa [W] using hWtriv
    have hgrowth : (2 + |y|) ^ A ≤ 3 ^ A := by
      exact Real.rpow_le_rpow (by positivity) (by linarith) hA
    change ‖F ((c : ℂ) + (y : ℝ) * I) * W y‖ ≤ _
    rw [norm_mul]
    calc
      ‖F ((c : ℂ) + (y : ℝ) * I)‖ * ‖W y‖
          ≤ (K * (2 + |y|) ^ A) * ((N + H) ^ c / c) := by
            exact mul_le_mul (hF y) hWtriv' (norm_nonneg _) (by positivity)
      _ ≤ (K * 3 ^ A) * ((N + H) ^ c / c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth hK) (by positivity)
      _ = K * 3 ^ A * ((N + H) ^ c / c) := by ring
  have hcenterNorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := g)
    (s := Ioo (-1 : ℝ) 1) measure_Ioo_lt_top (fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hcenterpoint y hy
      · dsimp [g]
        positivity)
  have hmeasure : volume.real (Ioo (-1 : ℝ) 1) = 2 := by
    rw [Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - (-1))]
    norm_num
  rw [hmeasure] at hcenterNorm
  have hcenter : ∫ y in Ioo (-1 : ℝ) 1, g y
      ≤ 2 * (K * 3 ^ A * ((N + H) ^ c / c)) := by
    calc
      (∫ y in Ioo (-1 : ℝ) 1, g y) ≤ ‖∫ y in Ioo (-1 : ℝ) 1, g y‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      _ ≤ (K * 3 ^ A * ((N + H) ^ c / c)) * 2 := hcenterNorm
      _ = 2 * (K * 3 ^ A * ((N + H) ^ c / c)) := by ring
  have hsplit := integral_add_compl htailmeas hgint
  rw [hcompl] at hsplit
  change (∫ y : ℝ, g y) ≤ _
  rw [← hsplit]
  simpa [add_comm] using add_le_add htailbound hcenter

end GaloisForLFunctions.HTGeometry
