import GaloisForLFunctions.RHTower.EstermannLeftGrowth
import GaloisForLFunctions.RHTower.EstermannEntire

/-!
# Polynomial bounds for the entire Estermann completion on two vertical lines

On `Re s = 2` the Dirichlet series converges absolutely, so the completion `(s-1)² D(s, a/q)`
grows at most quadratically.  On `Re s = -1` the functional equation applies with reflected
abscissa `2`, and the Gamma-squared decay cancels the cosine growth, so the completion again grows
polynomially.  Both bounds are extended across the compact segment `|t| ≤ 1` by continuity, since
the completion is entire.

These are the two sides of the rectangle a Phragmén--Lindelöf interpolation uses.
-/

open Complex

namespace RHTower

noncomputable section

variable {q : ℕ} [NeZero q]

/-- A bound above unit height extends to the whole line when the function is continuous. -/
theorem exists_bound_of_one_le_abs {f : ℂ → ℂ} (hf : Continuous f) (σ : ℝ) {C : ℝ} {N : ℕ}
    (hC0 : 0 ≤ C) (hC : ∀ t : ℝ, 1 ≤ |t| → ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t : ℝ, ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C' * (1 + |t|) ^ N := by
  have hcont : ContinuousOn (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * I)) (Set.Icc (-1 : ℝ) 1) := by
    refine Continuous.continuousOn ?_
    exact hf.comp (by fun_prop)
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  refine ⟨C + max C₂ 0, by positivity, fun t => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow1 : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ hbase
  have hpow0 : (0 : ℝ) ≤ (1 + |t|) ^ N := by positivity
  have hmax0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
  rcases le_total 1 |t| with hbig | hsmall
  · have h1 := hC t hbig
    nlinarith [h1, hmax0, hpow0]
  · have hmem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [Set.mem_Icc, ← abs_le]; exact hsmall
    have h2 : ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 := le_trans (hC₂ t hmem) (le_max_left _ _)
    nlinarith [h2, hpow1, hmax0, hC0, hpow0]

/-- `‖s - 1‖ ≤ (1 + |Im s|)` on the line `Re s = 2`, and generally `‖s-1‖ ≤ |Re s - 1| + |Im s|`. -/
theorem norm_sub_one_le (σ t : ℝ) :
    ‖((σ : ℂ) + (t : ℂ) * I) - 1‖ ≤ |σ - 1| + |t| := by
  have h := Complex.norm_le_abs_re_add_abs_im (((σ : ℂ) + (t : ℂ) * I) - 1)
  have hre : (((σ : ℂ) + (t : ℂ) * I) - 1).re = σ - 1 := by simp
  have him : (((σ : ℂ) + (t : ℂ) * I) - 1).im = t := by simp
  rwa [hre, him] at h

/-- **The right edge.** -/
theorem exists_bound_norm_estermannEntire_right (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖estermannEntire q ((a : ZMod q)) (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  set Z : ℝ := ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ) with hZ
  have hZ0 : 0 ≤ Z := shiftedPSeries_nonneg _
  have key : ∀ t : ℝ, 1 ≤ |t| →
      ‖estermannEntire q ((a : ZMod q)) (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ (Z * Z) * (1 + |t|) ^ 2 := by
    intro t ht
    set s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hre : s.re = 2 := by rw [hs]; simp
    have hne : s ≠ 1 := by
      intro hcon
      have hc := congrArg Complex.re hcon
      rw [hre] at hc
      norm_num at hc
    rw [estermannEntire_eq _ hne, norm_mul, norm_pow]
    have hD : ‖estermannZeta q ((a : ZMod q)) s‖ ≤ Z * Z := by
      have h := norm_estermannZeta_le (a := (a : ZMod q)) (s := s) (by rw [hre]; norm_num)
      rw [hre] at h
      exact h
    have hsm : ‖s - 1‖ ≤ 1 + |t| := by
      have h := norm_sub_one_le 2 t
      rw [← hs] at h
      calc ‖s - 1‖ ≤ |(2 : ℝ) - 1| + |t| := h
        _ = 1 + |t| := by norm_num
    have hnn : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
    calc ‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖
        ≤ (1 + |t|) ^ (2 : ℕ) * (Z * Z) :=
          mul_le_mul (pow_le_pow_left₀ hnn hsm 2) hD (norm_nonneg _) (by positivity)
      _ = Z * Z * (1 + |t|) ^ 2 := by ring
  exact exists_bound_of_one_le_abs (differentiable_estermannEntire a).continuous 2
    (C := Z * Z) (by positivity) key

/-- **The left edge.** -/
theorem exists_bound_norm_estermannEntire_left (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖estermannEntire q ((a : ZMod q)) (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ C * (1 + |t|) ^ N := by
  obtain ⟨C₀, N₀, hC₀0, hC₀⟩ := exists_bound_norm_estermannZeta_one_sub q a 2
  have key : ∀ t : ℝ, 1 ≤ |t| →
      ‖estermannEntire q ((a : ZMod q)) (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ (C₀ * 4) * (1 + |t|) ^ (N₀ + 2) := by
    intro t ht
    set s : ℂ := ((-1 : ℝ) : ℂ) + (t : ℂ) * I with hs
    have hre : s.re = -1 := by rw [hs]; simp
    have hne : s ≠ 1 := by
      intro hcon
      have hc := congrArg Complex.re hcon
      rw [hre] at hc
      norm_num at hc
    have hrefl : (1 : ℂ) - (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = s := by
      rw [hs]; push_cast; ring
    have hD : ‖estermannZeta q ((a : ZMod q)) s‖ ≤ C₀ * |t| ^ N₀ := by
      have h := hC₀ 2 (-t) (le_refl _) (le_refl _) (by rwa [abs_neg])
      rw [hrefl, abs_neg] at h
      exact h
    rw [estermannEntire_eq _ hne, norm_mul, norm_pow]
    have hsm : ‖s - 1‖ ≤ 2 + |t| := by
      have h := norm_sub_one_le (-1 : ℝ) t
      rw [← hs] at h
      calc ‖s - 1‖ ≤ |(-1 : ℝ) - 1| + |t| := h
        _ = 2 + |t| := by norm_num
    have hnn : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
    have hstep : ‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖
        ≤ (2 + |t|) ^ (2 : ℕ) * (C₀ * |t| ^ N₀) :=
      mul_le_mul (pow_le_pow_left₀ hnn hsm 2) hD (norm_nonneg _) (by positivity)
    refine hstep.trans ?_
    have hb : (0 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    calc (2 + |t|) ^ (2 : ℕ) * (C₀ * |t| ^ N₀)
        ≤ (2 * (1 + |t|)) ^ (2 : ℕ) * (C₀ * (1 + |t|) ^ N₀) := by
          gcongr <;> linarith [abs_nonneg t]
      _ = C₀ * 4 * (1 + |t|) ^ (N₀ + 2) := by rw [mul_pow, pow_add]; ring
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_of_one_le_abs (differentiable_estermannEntire a).continuous (-1 : ℝ)
      (C := C₀ * 4) (N := N₀ + 2) (by positivity) key
  exact ⟨C, N₀ + 2, hC0, hC⟩

end

end RHTower
