import GaloisForLFunctions.RHTower.XiMassCausticIterateWindow

/-!
# The caustic iterate on a complex window disc

The window estimate never used reality of the offset: only its norm enters, through the triangle
inequality that keeps every relevant point inside the square-root window of the balance ray.  The
same bound therefore holds at every complex point of that window, which is what a Cauchy estimate
for the height derivative needs.
-/

open Complex Metric

namespace RHTower

noncomputable section

theorem exists_norm_xiCausticIterate_windowC_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ w : ℂ,
      ‖w‖ ≤ Real.sqrt u / 2 →
      ‖xiCausticIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n
          ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + w)‖
        ≤ C / Real.sqrt u ^ (n + 1) := by
  obtain ⟨C₀, u₀, hC₀, hu₀, hzero⟩ := exists_norm_xiCausticCoeffZero_le_window ha hsigma
  obtain ⟨M₀, u₁, hM₀, hu₁, hcar⟩ := exists_norm_conjugatedCarrier_le_window ha hsigma
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  set γ₀ : ℝ := 2 * a * (xiMassSpacelikeSharpSlope a + 1) / xiMassWindowRate a with hγdef
  have hγ0 : (0 : ℝ) < γ₀ := by
    have := xiMassWindowRate_pos ha
    rw [hγdef]
    positivity
  set K₀ : ℝ := C₀ + 2 * γ₀ * ((n : ℝ) + 1) + 8 * ((n : ℝ) + 1) ^ 2 with hKdef
  have hK0 : (0 : ℝ) < K₀ := by rw [hKdef]; positivity
  refine ⟨M₀ * K₀ ^ n, max u₀ u₁, by positivity, le_trans hu₀ (le_max_left _ _), ?_⟩
  intro u hu w ht
  have hu0' : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have hu1' : u₁ ≤ u := le_trans (le_max_right _ _) hu
  have huw : xiMassWindowThreshold a ≤ u := le_trans hu₀ hu0'
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) huw
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set m : ℂ := (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) with hmdef
  set z₀ : ℂ := m + w with hz₀def
  set δ : ℝ := Real.sqrt u / (2 * ((n : ℝ) + 1)) with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hnδ : (n : ℝ) * δ + δ = Real.sqrt u / 2 := by
    rw [hδdef]
    field_simp
  -- every relevant point is within the full window of the balance ray
  have hnear : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ + δ → ‖ζ - m‖ ≤ Real.sqrt u := by
    intro ζ hζ
    have htri : ‖ζ - m‖ ≤ ‖ζ - z₀‖ + ‖w‖ := by
      have hid : ζ - m = (ζ - z₀) + w := by rw [hz₀def]; ring
      rw [hid]
      exact norm_add_le _ _
    linarith [hnδ, ht]
  have hshift : ∀ ζ : ℂ, ζ = m + (ζ - m) := fun ζ => by ring
  have hsub : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → closedBall ζ δ ⊆ xiMassHeightRegion τ := by
    intro ζ hζ v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    have hvz : ‖v - z₀‖ ≤ (n : ℝ) * δ + δ := by
      have htri : ‖v - z₀‖ ≤ ‖v - ζ‖ + ‖ζ - z₀‖ := by
        have := norm_add_le (v - ζ) (ζ - z₀)
        simpa using this
      linarith
    rw [hτdef, hmdef] at *
    exact window_subset_xiMassHeightRegion (sigma := sigma) ha huw (hnear v hvz)
  have hc₀ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖xiCausticCoeffZero a τ ζ‖ ≤ C₀ / Real.sqrt u := by
    intro ζ hζ
    have h := hzero u hu0' (ζ - m) (hnear ζ (by linarith [hδ0.le]))
    rw [← hτdef, ← hmdef] at h
    rwa [← hshift ζ] at h
  have hc₁ : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ → ‖xiCausticCoeffOne a τ ζ‖ ≤ γ₀ := by
    intro ζ hζ
    have h := norm_xiCausticCoeffOne_le_window (sigma := sigma) ha huw
      (hnear ζ (by linarith [hδ0.le]))
    rw [← hτdef, ← hmdef, ← hγdef] at h
    rwa [← hshift ζ] at h
  have hbase : ∀ ζ : ℂ, ‖ζ - z₀‖ ≤ (n : ℝ) * δ →
      ‖xiMassConjugatedCarrier a τ ζ‖ ≤ M₀ / Real.sqrt u := by
    intro ζ hζ
    have h := hcar u hu1' (ζ - m) (hnear ζ (by linarith [hδ0.le]))
    rw [← hτdef, ← hmdef] at h
    rwa [← hshift ζ] at h
  have hiter := norm_xiCausticIterate_le (a := a) ha0 (τ := τ) (z₀ := z₀) (δ := δ)
    (M := M₀ / Real.sqrt u) (ε := C₀ / Real.sqrt u) (γ := γ₀) n hδ0 (by positivity)
    hsub hc₀ hc₁ hbase
  have hsteple : C₀ / Real.sqrt u + γ₀ / δ + 2 / δ ^ 2 ≤ K₀ / Real.sqrt u := by
    have hγval : γ₀ / δ = 2 * γ₀ * ((n : ℝ) + 1) / Real.sqrt u := by
      rw [hδdef]
      field_simp
    have hδsq : (2 : ℝ) / δ ^ 2 = 8 * ((n : ℝ) + 1) ^ 2 / u := by
      rw [hδdef, div_pow, Real.sq_sqrt hu0.le]
      field_simp
      ring
    have hlast : 8 * ((n : ℝ) + 1) ^ 2 / u ≤ 8 * ((n : ℝ) + 1) ^ 2 / Real.sqrt u := by
      refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
      exact sqrt_le_self_of_one_le hu1
    have hsum : K₀ / Real.sqrt u
        = C₀ / Real.sqrt u + 2 * γ₀ * ((n : ℝ) + 1) / Real.sqrt u
          + 8 * ((n : ℝ) + 1) ^ 2 / Real.sqrt u := by
      rw [hKdef]
      field_simp
    rw [hγval, hδsq, hsum]
    linarith [hlast]
  have hpow : (C₀ / Real.sqrt u + γ₀ / δ + 2 / δ ^ 2) ^ n ≤ (K₀ / Real.sqrt u) ^ n :=
    pow_le_pow_left₀ (by positivity) hsteple n
  have hfin : M₀ / Real.sqrt u * (C₀ / Real.sqrt u + γ₀ / δ + 2 / δ ^ 2) ^ n
      ≤ M₀ / Real.sqrt u * (K₀ / Real.sqrt u) ^ n :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  refine le_trans hiter (le_trans hfin (le_of_eq ?_))
  rw [div_pow, pow_succ]
  field_simp

end

end RHTower
