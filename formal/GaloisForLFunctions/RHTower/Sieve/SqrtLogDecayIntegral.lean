import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO

/-!
# Integrating a `exp(−c√(log t))` weight

A weight decaying like `exp(−c√(log t))` integrates over `[2,x]` to at most
`x·exp(−(c/2)√(log x))`.  The proof splits at `√x`: below the split the weight is at most `1` and
the interval is only `√x` long, above it the weight is already at most
`exp(−(c/√2)√(log x))` and the interval is at most `x` long.  The halving of the constant is
exactly the loss `√(log √x) = √(log x)/√2 ≥ √(log x)/2` incurred at the split point.

The bottom piece `[2,T]`, where the decay hypothesis is not yet available, contributes a fixed
constant, and constants are below `x·exp(−(c/2)√(log x))` for the same reason `√x` is.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics MeasureTheory Set

/-- `√(log x)/2 ≤ √(log t)` for `√x ≤ t`: the split point costs a factor `√2`, and `2` is worse. -/
theorem sqrt_log_sqrt_le {x t : ℝ} (hx : 1 ≤ x) (ht : Real.sqrt x ≤ t) :
    Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log t) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlogs : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0.le
  have hmono : Real.log (Real.sqrt x) ≤ Real.log t := Real.log_le_log hs0 ht
  have hquarter : Real.sqrt (Real.log x / 4) = Real.sqrt (Real.log x) / 2 := by
    rw [show Real.log x / 4 = Real.log x * (1 / 2 : ℝ) ^ 2 by ring, Real.sqrt_mul hL0,
      Real.sqrt_sq (by norm_num)]
    ring
  calc Real.sqrt (Real.log x) / 2 = Real.sqrt (Real.log x / 4) := hquarter.symm
    _ ≤ Real.sqrt (Real.log t) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hlogs] at hmono
        linarith

/-- **The integral of a `exp(−c√(log t))` weight over `[2,x]`.**  The decay hypothesis is only
needed eventually; what happens on the initial segment is absorbed into the constant. -/
theorem exists_bound_setIntegral_sqrt_log_decay {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    {g : ℝ → ℝ} (hint : ∀ x : ℝ, 2 ≤ x → IntegrableOn g (Set.Icc 2 x))
    (hbd : ∀ᶠ t : ℝ in atTop, |g t| ≤ K * Real.exp (-c * Real.sqrt (Real.log t))) :
    ∃ C ≥ (0 : ℝ), ∀ᶠ x : ℝ in atTop,
      |∫ t in Set.Icc 2 x, g t| ≤ C * (x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) := by
  rw [eventually_atTop] at hbd
  obtain ⟨T₀, hT₀⟩ := hbd
  set T : ℝ := max T₀ 2 with hTdef
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hTbd : ∀ t : ℝ, T ≤ t → |g t| ≤ K * Real.exp (-c * Real.sqrt (Real.log t)) :=
    fun t ht => hT₀ t (le_trans (le_max_left _ _) ht)
  set D : ℝ := |∫ t in Set.Icc 2 T, g t| with hDdef
  have hD0 : (0 : ℝ) ≤ D := abs_nonneg _
  refine ⟨D + 2 * K, by linarith, ?_⟩
  filter_upwards [sqrt_mul_log_le_shape (show (0 : ℝ) < c / 2 by linarith),
    eventually_ge_atTop (T ^ 2), eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (3 : ℝ)] with x hshape hxT hx4 hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  -- the split point
  have hsxT : T ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hxT
    rwa [Real.sqrt_sq (by linarith)] at h
  have hsx2 : (2 : ℝ) ≤ Real.sqrt x := le_trans hT2 hsxT
  have hsxx : Real.sqrt x ≤ x := by
    have h := Real.sqrt_le_sqrt (show x ≤ x ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hx0.le] at h
  have hsx0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- the three pieces are integrable
  have hint_x : IntegrableOn g (Set.Icc 2 x) := hint x (by linarith)
  have hi1 : IntegrableOn g (Set.Icc 2 T) :=
    hint_x.mono_set (Set.Icc_subset_Icc_right (by linarith))
  have hi2 : IntegrableOn g (Set.Ioc T (Real.sqrt x)) :=
    hint_x.mono_set (fun t ht => ⟨le_trans hT2 ht.1.le, le_trans ht.2 hsxx⟩)
  have hi3 : IntegrableOn g (Set.Ioc (Real.sqrt x) x) :=
    hint_x.mono_set (fun t ht => ⟨le_trans hsx2 ht.1.le, ht.2⟩)
  have hi12 : IntegrableOn g (Set.Icc 2 (Real.sqrt x)) :=
    hint_x.mono_set (Set.Icc_subset_Icc_right hsxx)
  -- decompose the integral
  have hdisj1 : Disjoint (Set.Icc (2 : ℝ) T) (Set.Ioc T (Real.sqrt x)) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht'.1 (not_lt.mpr ht.2)
  have hdisj2 : Disjoint (Set.Icc (2 : ℝ) (Real.sqrt x)) (Set.Ioc (Real.sqrt x) x) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht'.1 (not_lt.mpr ht.2)
  have heq : ∫ t in Set.Icc 2 x, g t
      = ((∫ t in Set.Icc 2 T, g t) + ∫ t in Set.Ioc T (Real.sqrt x), g t)
        + ∫ t in Set.Ioc (Real.sqrt x) x, g t := by
    rw [← Set.Icc_union_Ioc_eq_Icc hsx2 hsxx,
      setIntegral_union hdisj2 measurableSet_Ioc hi12 hi3,
      ← Set.Icc_union_Ioc_eq_Icc hT2 hsxT,
      setIntegral_union hdisj1 measurableSet_Ioc hi1 hi2]
  -- the middle piece: the weight is at most one
  have hb2 : |∫ t in Set.Ioc T (Real.sqrt x), g t| ≤ K * Real.sqrt x := by
    have hbound : ∀ t ∈ Set.Ioc T (Real.sqrt x), ‖g t‖ ≤ K := by
      intro t ht
      have hexp : Real.exp (-c * Real.sqrt (Real.log t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ Real.sqrt (Real.log t) := Real.sqrt_nonneg _
        nlinarith
      rw [Real.norm_eq_abs]
      calc |g t| ≤ K * Real.exp (-c * Real.sqrt (Real.log t)) := hTbd t ht.1.le
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left hexp hK
        _ = K := mul_one K
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Ioc T (Real.sqrt x)) (f := g) (C := K)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hbound
    rw [Real.norm_eq_abs, Real.volume_real_Ioc, max_eq_left (by linarith)] at h
    calc |∫ t in Set.Ioc T (Real.sqrt x), g t| ≤ K * (Real.sqrt x - T) := h
      _ ≤ K * Real.sqrt x := mul_le_mul_of_nonneg_left (by linarith) hK
  -- the top piece: the weight is already small
  have hb3 : |∫ t in Set.Ioc (Real.sqrt x) x, g t|
      ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * x := by
    have hbound : ∀ t ∈ Set.Ioc (Real.sqrt x) x,
        ‖g t‖ ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
      intro t ht
      have hsl := sqrt_log_sqrt_le (x := x) (t := t) (by linarith) ht.1.le
      have hexp : Real.exp (-c * Real.sqrt (Real.log t))
          ≤ Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      rw [Real.norm_eq_abs]
      exact le_trans (hTbd t (by linarith [ht.1.le]))
        (mul_le_mul_of_nonneg_left hexp hK)
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Ioc (Real.sqrt x) x) (f := g)
      (C := K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) hbound
    rw [Real.norm_eq_abs, Real.volume_real_Ioc, max_eq_left (by linarith)] at h
    have hKe : (0 : ℝ) ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by positivity
    calc |∫ t in Set.Ioc (Real.sqrt x) x, g t|
        ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * (x - Real.sqrt x) := h
      _ ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * x :=
          mul_le_mul_of_nonneg_left (by linarith) hKe
  -- constants and `√x` are below the shape
  have hshapepos : (0 : ℝ) ≤ x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by positivity
  have hbig : (1 : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by nlinarith
  have hsmall : D + K * Real.sqrt x ≤ (D + K) * (2 * Real.sqrt x * Real.log x) := by
    have h1 : D ≤ D * (2 * Real.sqrt x * Real.log x) := by nlinarith
    have h2 : K * Real.sqrt x ≤ K * (2 * Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg hsx0 (show (0 : ℝ) ≤ 2 * Real.log x - 1 by linarith)]) hK
    nlinarith
  have hsmall' : D + K * Real.sqrt x
      ≤ (D + K) * (x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) := by
    have := mul_le_mul_of_nonneg_left hshape (by linarith : (0 : ℝ) ≤ D + K)
    linarith [hsmall, this]
  rw [heq]
  have htri1 := abs_add_le ((∫ t in Set.Icc 2 T, g t) + ∫ t in Set.Ioc T (Real.sqrt x), g t)
    (∫ t in Set.Ioc (Real.sqrt x) x, g t)
  have htri2 := abs_add_le (∫ t in Set.Icc 2 T, g t) (∫ t in Set.Ioc T (Real.sqrt x), g t)
  have hfinal : (D + K * Real.sqrt x) + K * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) * x
      ≤ (D + 2 * K) * (x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))) := by
    nlinarith [hsmall', hK]
  linarith [htri1, htri2, hb2, hb3, hfinal]

end RHTower.Sieve
