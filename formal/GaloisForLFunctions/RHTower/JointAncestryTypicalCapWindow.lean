import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation

/-!
# Prime windows with prescribed coherent variance

For `0 < 2σ − 2Θ < 1` and `C > 1`, the primes of the multiplicative window `(X, CX]` carry
`X^{2Θ} Σ p^{−2σ} → ∞`, each prime contributing at most `X^{−(2σ−2Θ)} ≤ 1`.  Hence an initial
segment `W` of the window has `V ≤ ¼ X^{2Θ} Σ_{p ∈ W} p^{−2σ} ≤ V + 1` for every target `V > 0`
and all large `X` (`eventually_exists_capWindow`).
-/

open Filter

namespace RHTower

noncomputable section

/-- The coherent variance `¼ X^{2Θ} Σ_{p ∈ W} p^{−2σ}` of a prime set `W`. -/
def capVariance (Θ σ X : ℝ) (W : Finset ℕ) : ℝ :=
  1 / 4 * X ^ (2 * Θ) * ∑ p ∈ W, (p : ℝ) ^ (-(2 * σ))

theorem mem_multiplicativePrimeWindow_bounds {X C : ℝ} {p : ℕ}
    (hp : p ∈ multiplicativePrimeWindow X C) : X < p ∧ (p : ℝ) ≤ C * X ∧ p.Prime := by
  simp only [multiplicativePrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨?_, ?_, hp.2⟩
  · have := Nat.lt_floor_add_one X
    have : ⌊X⌋₊ + 1 ≤ p := hp.1.1
    have : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast this
    push_cast at this; linarith
  · have hC : 0 ≤ C * X ∨ C * X < 0 := le_or_gt 0 (C * X)
    rcases hC with hC | hC
    · exact (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le hC)
    · have : ⌊C * X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have := hp.1.2; omega

/-- **Prime windows with prescribed variance.** -/
theorem eventually_exists_capWindow {Θ σ C V : ℝ} (hΘ : 0 ≤ Θ) (hs0 : 0 < 2 * σ - 2 * Θ)
    (hs1 : 2 * σ - 2 * Θ < 1) (hC : 1 < C) (hV : 0 < V) :
    ∀ᶠ X in atTop, ∃ W ⊆ multiplicativePrimeWindow X C,
      V ≤ capVariance Θ σ X W ∧ capVariance Θ σ X W ≤ V + 1 := by
  set s := 2 * σ - 2 * Θ with hs
  have hC0 : 0 < C := by linarith
  have htend := tendsto_sum_primeWindow_rpow_neg hs0 hs1 hC
  filter_upwards [htend.eventually_ge_atTop (4 * C ^ (2 * Θ) * V), eventually_ge_atTop (1 : ℝ)]
    with X hX hX1
  have hX0 : 0 < X := by linarith
  set win := multiplicativePrimeWindow X C with hwin
  set term : ℕ → ℝ := fun p => 1 / 4 * X ^ (2 * Θ) * (p : ℝ) ^ (-(2 * σ)) with hterm
  have hcap : ∀ W : Finset ℕ, capVariance Θ σ X W = ∑ p ∈ W, term p := by
    intro W; unfold capVariance; rw [Finset.mul_sum]
  -- lower bound on each term, and the total
  have hlow : ∀ p ∈ win, 1 / 4 * C ^ (-(2 * Θ)) * (p : ℝ) ^ (-s) ≤ term p := by
    intro p hp
    obtain ⟨hXp, hpC, -⟩ := mem_multiplicativePrimeWindow_bounds hp
    have hp0 : 0 < (p : ℝ) := by linarith
    have hpX : (p : ℝ) / C ≤ X := by rw [div_le_iff₀ hC0]; linarith
    have hpow : ((p : ℝ) / C) ^ (2 * Θ) ≤ X ^ (2 * Θ) :=
      Real.rpow_le_rpow (by positivity) hpX (by positivity)
    rw [Real.div_rpow hp0.le hC0.le] at hpow
    have hs' : (p : ℝ) ^ (-s) = (p : ℝ) ^ (2 * Θ) * (p : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_add hp0]; congr 1; rw [hs]; ring
    simp only [hterm]
    rw [hs', Real.rpow_neg hC0.le]
    have h1 : 0 ≤ (p : ℝ) ^ (-(2 * σ)) := by positivity
    have h2 : (p : ℝ) ^ (2 * Θ) * (C ^ (2 * Θ))⁻¹ ≤ X ^ (2 * Θ) := by
      rw [← div_eq_mul_inv]; exact hpow
    nlinarith
  have htotal : V ≤ ∑ p ∈ win, term p := by
    have h1 : ∑ p ∈ win, 1 / 4 * C ^ (-(2 * Θ)) * (p : ℝ) ^ (-s) ≤ ∑ p ∈ win, term p :=
      Finset.sum_le_sum hlow
    rw [← Finset.mul_sum] at h1
    have hCpos : 0 < C ^ (2 * Θ) := Real.rpow_pos_of_pos hC0 _
    have h2 : 1 / 4 * C ^ (-(2 * Θ)) * (4 * C ^ (2 * Θ) * V) = V := by
      rw [Real.rpow_neg hC0.le]; field_simp
    have h3 : 1 / 4 * C ^ (-(2 * Θ)) * (4 * C ^ (2 * Θ) * V) ≤
        1 / 4 * C ^ (-(2 * Θ)) * ∑ p ∈ win, (p : ℝ) ^ (-s) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    linarith
  -- each term is at most `1/4`
  have hup : ∀ p ∈ win, term p ≤ 1 / 4 := by
    intro p hp
    obtain ⟨hXp, -, -⟩ := mem_multiplicativePrimeWindow_bounds hp
    have hp0 : 0 < (p : ℝ) := by linarith
    have h1 : (p : ℝ) ^ (-(2 * σ)) ≤ X ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos hX0 hXp.le (by linarith)
    have h2 : X ^ (2 * Θ) * X ^ (-(2 * σ)) = X ^ (-s) := by
      rw [← Real.rpow_add hX0]; congr 1; rw [hs]; ring
    have h3 : X ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
    simp only [hterm]
    have : 0 ≤ X ^ (2 * Θ) := by positivity
    nlinarith
  -- the initial segment
  set F : ℕ → ℝ := fun z => ∑ p ∈ win.filter (· ≤ z), term p with hF
  have hFtop : V ≤ F ⌊C * X⌋₊ := by
    have : win.filter (· ≤ ⌊C * X⌋₊) = win := by
      refine Finset.filter_true_of_mem fun p hp => ?_
      simp only [hwin, multiplicativePrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact hp.1.2
    simp only [hF, this]; exact htotal
  have hex : ∃ z, V ≤ F z := ⟨_, hFtop⟩
  classical
  set z := Nat.find hex with hz
  have hFz : V ≤ F z := Nat.find_spec hex
  have hz0 : z ≠ 0 := by
    intro h0
    have : F 0 = 0 := by
      simp only [hF]
      refine Finset.sum_eq_zero fun p hp => ?_
      exfalso
      obtain ⟨hpw, hp0⟩ := Finset.mem_filter.mp hp
      obtain ⟨hXp, -, -⟩ := mem_multiplicativePrimeWindow_bounds hpw
      have : (p : ℝ) ≤ 0 := by exact_mod_cast hp0
      linarith
    rw [h0] at hFz; linarith
  have hprev : F (z - 1) < V := by
    have := Nat.find_min hex (show z - 1 < z by omega)
    exact lt_of_not_ge this
  have hstep : F z ≤ F (z - 1) + 1 / 4 := by
    have hsplit : win.filter (· ≤ z) ⊆ insert z (win.filter (· ≤ z - 1)) := by
      intro p hp
      obtain ⟨hpw, hpz⟩ := Finset.mem_filter.mp hp
      rcases Nat.lt_or_ge p z with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hpw, by omega⟩)
      · have : p = z := le_antisymm hpz h
        exact this ▸ Finset.mem_insert_self _ _
    have hnn : ∀ p ∈ insert z (win.filter (· ≤ z - 1)), 0 ≤ term p := fun p _ => by
      simp only [hterm]; positivity
    have h1 : F z ≤ ∑ p ∈ insert z (win.filter (· ≤ z - 1)), term p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsplit (fun p hp _ => hnn p hp)
    by_cases hzw : z ∈ win
    · have hnot : z ∉ win.filter (· ≤ z - 1) := by
        intro h; have := (Finset.mem_filter.mp h).2; omega
      rw [Finset.sum_insert hnot] at h1
      have := hup z hzw
      simp only [hF] at h1 ⊢
      linarith
    · have hsub2 : win.filter (· ≤ z) ⊆ win.filter (· ≤ z - 1) := by
        intro p hp
        obtain ⟨hpw, hpz⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨hpw, ?_⟩
        rcases Nat.lt_or_ge p z with h | h
        · omega
        · exact absurd (le_antisymm hpz h ▸ hpw) hzw
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (fun p hp _ => (by simp only [hterm]; positivity : 0 ≤ term p))
      simp only [hF]; linarith
  refine ⟨win.filter (· ≤ z), Finset.filter_subset _ _, ?_, ?_⟩
  · rw [hcap]; exact hFz
  · rw [hcap]; simp only [hF] at hFz hprev hstep ⊢; linarith

end

end RHTower
