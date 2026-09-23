import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.PSeries

/-!
# Moving divisors over an arbitrary base sequence

A moving divisor is a strictly increasing sequence of positive reals obtained by displacing a base
sequence of unit asymptotic density inside shrinking intervals.  The clock divisor
`n + 1 + (1/4)·tanh θ_n` is the case of the base `n + 1` and constant radius `1/4`; the divisor
attached to a prescribed gap process is the case of the partial sums of the gap sequence and the
shrinking radii.

This file records the properties that the canonical-product estimates consume: positivity, strict
monotonicity, divergence, the coordinate derivative with positive speed, unit asymptotic density,
and two-sided linear bounds.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- A base sequence with shrinking displacement radii, separated enough for the displaced sequence
to stay strictly increasing, and of unit asymptotic density. -/
structure MovingDivisor where
  /-- The undisplaced locations. -/
  base : ℕ → ℝ
  /-- The displacement radii. -/
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_le_one : ∀ n, radius n ≤ 1
  base_gap : ∀ n, base n + radius n + radius (n + 1) < base (n + 1)
  base_first : radius 0 < base 0
  density : Tendsto (fun n : ℕ => base n / (n + 1)) atTop (𝓝 1)

namespace MovingDivisor

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- The displaced locations. -/
noncomputable def zero (n : ℕ) : ℝ := D.base n + D.radius n * Real.tanh (θ n)

theorem abs_displacement_le (n : ℕ) : |D.radius n * Real.tanh (θ n)| ≤ D.radius n := by
  rw [abs_mul, abs_of_pos (D.radius_pos n)]
  have ht : |Real.tanh (θ n)| ≤ 1 := by
    rw [abs_le]
    exact ⟨le_of_lt (Real.neg_one_lt_tanh _), le_of_lt (Real.tanh_lt_one _)⟩
  nlinarith [D.radius_pos n]

theorem zero_lt_base_add (n : ℕ) : D.zero θ n ≤ D.base n + D.radius n := by
  have := le_of_abs_le (D.abs_displacement_le θ n)
  simp only [zero]
  linarith

theorem base_sub_le_zero (n : ℕ) : D.base n - D.radius n ≤ D.zero θ n := by
  have := neg_le_of_abs_le (D.abs_displacement_le θ n)
  simp only [zero]
  linarith

theorem zero_lt_succ (n : ℕ) : D.zero θ n < D.zero θ (n + 1) := by
  have h1 := D.zero_lt_base_add θ n
  have h2 := D.base_sub_le_zero θ (n + 1)
  have h3 := D.base_gap n
  linarith

theorem strictMono : StrictMono (D.zero θ) := strictMono_nat_of_lt_succ (D.zero_lt_succ θ)

theorem injective : Function.Injective (D.zero θ) := (D.strictMono θ).injective

theorem zero_pos (n : ℕ) : 0 < D.zero θ n := by
  have hzero : 0 < D.zero θ 0 := by
    have h := D.base_sub_le_zero θ 0
    have := D.base_first
    linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hzero
  · exact lt_of_lt_of_le hzero (le_of_lt ((D.strictMono θ) hn))

theorem base_strictMono : StrictMono D.base := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have := D.base_gap n
  have := D.radius_pos n
  have := D.radius_pos (n + 1)
  linarith

theorem base_pos (n : ℕ) : 0 < D.base n := by
  have hbase0 : 0 < D.base 0 := lt_trans (D.radius_pos 0) D.base_first
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hbase0
  · exact lt_trans hbase0 (D.base_strictMono hn)

/-- The displaced locations have unit asymptotic density. -/
theorem tendsto_zero_div : Tendsto (fun n : ℕ => D.zero θ n / (n + 1)) atTop (𝓝 1) := by
  have hpert : Tendsto (fun n : ℕ => D.radius n * Real.tanh (θ n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, ‖D.radius n * Real.tanh (θ n) / ((n : ℝ) + 1)‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
      have hle : |D.radius n * Real.tanh (θ n)| ≤ 1 :=
        le_trans (D.abs_displacement_le θ n) (D.radius_le_one n)
      gcongr
    refine squeeze_zero_norm hbound ?_
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa [one_div] using h
  have hsum := D.density.add hpert
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [zero, add_div]

theorem tendsto_base_atTop : Tendsto D.base atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hnat
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * ((n : ℝ) + 1) ≤ D.base n := by
    have hmem : (fun n : ℕ => D.base n / ((n : ℝ) + 1)) ⁻¹' Set.Ioi (1 / 2 : ℝ) ∈ atTop :=
      D.density (Ioi_mem_nhds (by norm_num))
    filter_upwards [hmem] with n hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn' : (1 / 2 : ℝ) < D.base n / ((n : ℝ) + 1) := hn
    rw [lt_div_iff₀ hpos] at hn'
    linarith
  exact tendsto_atTop_mono' atTop hev hhalf

theorem tendsto_zero_atTop : Tendsto (D.zero θ) atTop atTop := by
  have hsub : Tendsto (fun n : ℕ => D.base n - 1) atTop atTop := by
    have h := Filter.tendsto_atTop_add_const_right atTop (-1 : ℝ) D.tendsto_base_atTop
    exact h.congr fun n => by ring
  have hmid : Tendsto (fun n : ℕ => D.base n - D.radius n) atTop atTop :=
    tendsto_atTop_mono (fun n => by have := D.radius_le_one n; linarith) hsub
  exact tendsto_atTop_mono (fun n => D.base_sub_le_zero θ n) hmid

/-! ### Bounds uniform in the parameter -/

theorem base_sub_radius_pos (n : ℕ) : 0 < D.base n - D.radius n := by
  induction n with
  | zero =>
    have := D.base_first
    linarith
  | succ n ih =>
    have hgap := D.base_gap n
    have hr := D.radius_pos n
    linarith

theorem tendsto_base_sub_radius_div :
    Tendsto (fun n : ℕ => (D.base n - D.radius n) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hrad : Tendsto (fun n : ℕ => D.radius n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa [one_div] using h
    refine squeeze_zero (fun n => le_of_lt (div_pos (D.radius_pos n) (by positivity)))
      (fun n => ?_) hmaj
    have h1 := D.radius_le_one n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    gcongr
  have hsub := D.density.sub hrad
  rw [sub_zero] at hsub
  refine hsub.congr fun n => ?_
  rw [sub_div]

theorem tendsto_base_add_radius_div :
    Tendsto (fun n : ℕ => (D.base n + D.radius n) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hrad : Tendsto (fun n : ℕ => D.radius n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      simpa [one_div] using h
    refine squeeze_zero (fun n => le_of_lt (div_pos (D.radius_pos n) (by positivity)))
      (fun n => ?_) hmaj
    have h1 := D.radius_le_one n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    gcongr
  have hadd := D.density.add hrad
  rw [add_zero] at hadd
  refine hadd.congr fun n => ?_
  rw [add_div]

/-- **A lower linear bound valid for every parameter.** -/
theorem exists_uniform_lower_linear :
    ∃ c : ℝ, 0 < c ∧ ∀ (θ : ℕ → ℝ) (n : ℕ), c * ((n : ℝ) + 1) ≤ D.zero θ n := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < (D.base n - D.radius n) / ((n : ℝ) + 1) :=
    D.tendsto_base_sub_radius_div (Ioi_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  have hc₀pos :
      0 < (Finset.range (N + 1)).inf' hsne
        (fun n => (D.base n - D.radius n) / ((n : ℝ) + 1)) := by
    rw [Finset.lt_inf'_iff]
    intro n _
    exact div_pos (D.base_sub_radius_pos n) (by positivity)
  refine ⟨min (1 / 2)
      ((Finset.range (N + 1)).inf' hsne
        (fun n => (D.base n - D.radius n) / ((n : ℝ) + 1))),
    lt_min (by norm_num) hc₀pos, fun θ n => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine le_trans ?_ (D.base_sub_le_zero θ n)
  rw [← le_div_iff₀ hpos]
  rcases le_or_gt n N with hn | hn
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    exact le_trans (min_le_right _ _)
      (Finset.inf'_le (fun n => (D.base n - D.radius n) / ((n : ℝ) + 1)) hmem)
  · exact le_trans (min_le_left _ _) (le_of_lt (hN n (by omega)))

/-- **An upper linear bound valid for every parameter.** -/
theorem exists_uniform_upper_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℕ → ℝ) (n : ℕ), D.zero θ n ≤ C * ((n : ℝ) + 1) := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, (D.base n + D.radius n) / ((n : ℝ) + 1) < 2 :=
    D.tendsto_base_add_radius_div (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  refine ⟨max 2 ((Finset.range (N + 1)).sup' hsne
      (fun n => (D.base n + D.radius n) / ((n : ℝ) + 1))),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun θ n => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine le_trans (D.zero_lt_base_add θ n) ?_
  rw [← div_le_iff₀ hpos]
  rcases le_or_gt n N with hn | hn
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    exact le_trans (Finset.le_sup' (fun n => (D.base n + D.radius n) / ((n : ℝ) + 1)) hmem)
      (le_max_right _ _)
  · exact le_trans (le_of_lt (hN n (by omega))) (le_max_left _ _)

/-! ### The uniform majorant constant -/

/-- A positive constant with `c (n+1) ≤ Λ_n(θ)` for every parameter. -/
noncomputable def lowerConst : ℝ := (D.exists_uniform_lower_linear).choose

theorem lowerConst_pos : 0 < D.lowerConst := (D.exists_uniform_lower_linear).choose_spec.1

theorem lowerConst_mul_le (θ : ℕ → ℝ) (n : ℕ) :
    D.lowerConst * ((n : ℝ) + 1) ≤ D.zero θ n :=
  (D.exists_uniform_lower_linear).choose_spec.2 θ n

/-- The constant in the reciprocal-square majorant of the divisor. -/
noncomputable def majorantConst : ℝ := 1 / D.lowerConst ^ (2 : ℕ)

theorem majorantConst_pos : 0 < D.majorantConst := by
  have h := D.lowerConst_pos
  rw [majorantConst]
  positivity

theorem inv_sq_le_majorant (θ : ℕ → ℝ) (a : ℕ) :
    1 / ‖((D.zero θ a : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ D.majorantConst / ((a : ℝ) + 1) ^ (2 : ℕ) := by
  have hc := D.lowerConst_pos
  have hzp := D.zero_pos θ a
  have hap : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzp]
  have hl := D.lowerConst_mul_le θ a
  have hsq : (D.lowerConst * ((a : ℝ) + 1)) ^ (2 : ℕ) ≤ (D.zero θ a) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hl 2
  rw [div_le_div_iff₀ (by positivity) (by positivity), majorantConst]
  have hexp : D.lowerConst ^ (2 : ℕ) * ((a : ℝ) + 1) ^ (2 : ℕ) = (D.lowerConst * ((a : ℝ) + 1)) ^ (2 : ℕ) := by
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < D.lowerConst ^ (2 : ℕ))]
  nlinarith [hsq]

end MovingDivisor

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

namespace MovingDivisor

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- The displaced locations grow at least linearly. -/
theorem exists_lower_linear : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * ((n : ℝ) + 1) ≤ D.zero θ n := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) < D.zero θ n / ((n : ℝ) + 1) :=
    (D.tendsto_zero_div θ) (Ioi_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  have hc₀pos :
      0 < (Finset.range (N + 1)).inf' hsne (fun n => D.zero θ n / ((n : ℝ) + 1)) := by
    rw [Finset.lt_inf'_iff]
    intro n _
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos (D.zero_pos θ n) hpos
  refine ⟨min (1 / 2)
      ((Finset.range (N + 1)).inf' hsne (fun n => D.zero θ n / ((n : ℝ) + 1))),
    lt_min (by norm_num) hc₀pos, fun n => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← le_div_iff₀ hpos]
  rcases le_or_gt n N with hn | hn
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    exact le_trans (min_le_right _ _)
      (Finset.inf'_le (fun n => D.zero θ n / ((n : ℝ) + 1)) hmem)
  · exact le_trans (min_le_left _ _) (le_of_lt (hN n (by omega)))

/-- The displaced locations grow at most linearly. -/
theorem exists_upper_linear : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, D.zero θ n ≤ C * ((n : ℝ) + 1) := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, D.zero θ n / ((n : ℝ) + 1) < 2 :=
    (D.tendsto_zero_div θ) (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hsne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos N)⟩
  refine ⟨max 2 ((Finset.range (N + 1)).sup' hsne (fun n => D.zero θ n / ((n : ℝ) + 1))),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun n => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← div_le_iff₀ hpos]
  rcases le_or_gt n N with hn | hn
  · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
    exact le_trans (Finset.le_sup' (fun n => D.zero θ n / ((n : ℝ) + 1)) hmem)
      (le_max_right _ _)
  · exact le_trans (le_of_lt (hN n (by omega))) (le_max_left _ _)

/-- The speed of the coordinate displacement. -/
noncomputable def coordinateSpeed (n : ℕ) (t : ℝ) : ℝ := D.radius n * (1 / Real.cosh t ^ (2 : ℕ))

/-- The coordinate displacement is a smooth strictly increasing reparametrization. -/
theorem coordinate_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => D.base n + D.radius n * Real.tanh s)
      (D.coordinateSpeed n t) t :=
  ((_root_.HTGeometry.hasDerivAt_tanh t).const_mul (D.radius n)).const_add (D.base n)

theorem coordinate_speed_pos (n : ℕ) (t : ℝ) : 0 < D.coordinateSpeed n t := by
  have h1 := D.radius_pos n
  have h2 : (0 : ℝ) < Real.cosh t ^ (2 : ℕ) := by positivity
  rw [coordinateSpeed]
  positivity

theorem continuous_coordinateSpeed (n : ℕ) : Continuous (D.coordinateSpeed n) := by
  refine continuous_const.mul (continuous_const.div ?_ ?_)
  · exact (Real.continuous_cosh.pow 2)
  · intro t
    positivity

/-- The reciprocal squares of the displaced locations are summable. -/
theorem summable_inv_sq : Summable (fun n : ℕ => (D.zero θ n)⁻¹ ^ (2 : ℕ)) := by
  obtain ⟨c, hc, hle⟩ := D.exists_lower_linear θ
  have hcomp : Summable (fun n : ℕ => (c * ((n : ℝ) + 1))⁻¹ ^ (2 : ℕ)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (2 : ℕ)) := by
      have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
      have hshift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
        (summable_nat_add_iff 1).2 h
      exact hshift.congr fun n => by push_cast; ring
    have := hbase.mul_left (c⁻¹ ^ (2 : ℕ))
    refine this.congr fun n => ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hcomp
  have hpos : (0 : ℝ) < c * ((n : ℝ) + 1) := by positivity
  have hz : 0 < D.zero θ n := D.zero_pos θ n
  have h1 : (D.zero θ n)⁻¹ ≤ (c * ((n : ℝ) + 1))⁻¹ := by
    have := one_div_le_one_div_of_le hpos (hle n)
    simpa [one_div] using this
  have h2 : (0 : ℝ) ≤ (D.zero θ n)⁻¹ := le_of_lt (inv_pos.2 hz)
  nlinarith

end MovingDivisor

end GaloisForLFunctions.HTGeometry
