import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.LogarithmicWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.AllDelays

/-! # Linear gate budgets at prescribed delays after the first crossing -/
open MeasureTheory Filter Set Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

private theorem floor_budget {κ : ℝ} (hκ : 0 ≤ κ) (hh : κ < 1/2) {k : ℕ} (hk : 64 ≤ k+3) :
    ⌊κ*((k+2:ℕ):ℝ)⌋₊ ≤ nearHilbertContinuousCircuitBudget (k+3)/2 := by
  let s := ⌊κ*((k+2:ℕ):ℝ)⌋₊
  have hs : (s:ℝ) ≤ κ*((k+2:ℕ):ℝ) := Nat.floor_le (by positivity)
  have hc := mul_le_mul_of_nonneg_right hh.le (Nat.cast_nonneg (α:=ℝ) (k+2))
  have h : s*2 ≤ k+2 := by exact_mod_cast (show (s:ℝ)*2 ≤ ((k+2:ℕ):ℝ) by linarith only [hs,hc])
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  exact (Nat.mul_le_mul_right _ h).trans (by
    nlinarith only [ReturnExcursions.dimension_dominates_speed hk,Nat.zero_le k])

/-- At every prescribed delay from the actual first crossing, a window
of length o(log N) excludes all budgets below a fixed density κ < 1/2
with probability tending to one. The delay has no deterministic upper bound. -/
theorem gaussian_sublogarithmic_return_window {κ : ℝ} (hκ : 0 ≤ κ) (hhalf : κ < 1/2) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ (w d : ℕ → ℝ), (∀ k, 0 ≤ w k) →
      (∀ c : ℝ, ∀ᶠ k : ℕ in atTop, c*max 1 (w k) ≤ (Nat.log b (k+1):ℝ)) →
      Tendsto (fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
        hitWindow (k+1) (nearHilbertContinuousCircuitBudget (k+3))
          ⌊κ*((k+2:ℕ):ℝ)⌋₊ (max (d k) 0) (w k))) atTop (𝓝 0) := by
  obtain ⟨A,hA,b,hb,hgap⟩ := SpanningDensity.FixedHorizon.gaussian_logarithmic_occupation hhalf
  refine ⟨b,hb,?_⟩
  intro w d hw hsmall
  let N (k : ℕ) := k+3
  let s (k : ℕ) := ⌊κ*((k+2:ℕ):ℝ)⌋₊
  let L (k : ℕ) := max (max (d k) 0) ((N k:ℝ)^2)
  let W (k : ℕ) := max 1 (w k)
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (N k)
  let E (k : ℕ) := hitWindow (k+1) (P k) (s k) (L k) (w k)
  let a (m k : ℕ) := factor (m:=m) (8*W k) (L k)
  have hW (k : ℕ) : 1 ≤ W k := le_max_left ..
  have hwW (k : ℕ) : w k ≤ W k := le_max_right ..
  have hsize (k : ℕ) : (Nat.log b (k+1):ℝ) ≤ (N k:ℝ) := by
    exact_mod_cast (Nat.log_le_self b (k+1)).trans (show k+1 ≤ N k by dsimp [N]; omega)
  have hg (k : ℕ) : 0 ≤ 8*W k := by linarith only [hW k]
  have price (m : ℕ) : ∀ᶠ k : ℕ in atTop, 16*((m:ℝ)*(8*W k)) ≤ N k := by
    filter_upwards [hsmall (128*m)] with k hk
    exact (by ring : 16*((m:ℝ)*(8*W k))=(128*m)*W k).le.trans (hk.trans (hsize k))
  apply remove_initial_delay_cutoff s w d
  · filter_upwards [eventually_ge_atTop 64] with k hk
    exact floor_budget hκ hhalf (by omega)
  · filter_upwards [hsmall 1] with k hk
    exact (hwW k).trans (by simpa only [one_mul] using hk.trans (hsize k))
  apply prefix_probability_of_isolation E (fun _ => measurable_hitWindow ..) a
  · intro m
    filter_upwards [price m] with k hk
    exact (grid_price (k:=k) (hg k) (le_max_right ..) hk).2
  intro m
  obtain ⟨K,hK⟩ := exists_nat_gt A
  filter_upwards [hgap] with ω hf
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hf,hsmall (8*m+2),price m,
    eventually_ge_atTop K] with k hk hspan hprice hstart
  intro hx
  have hs : (s k:ℝ) ≤ κ*((k+2:ℕ):ℝ) := Nat.floor_le (mul_nonneg hκ (Nat.cast_nonneg _))
  have gap := (hk (s k) hs).1
  let H : selfAdjoint (Matrix (Fin (k+3) → Bool) (Fin (k+3) → Bool) ℂ) :=
    ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  have hit (t : ℝ) (ht : pathGateDistance (k+1) (s k) (prefixPoint k ω) t ≤ 1/10) :
      HasProjectiveCircuitApproximation (k+3) (1/10) (s k) (unitaryEvolution H.val t) := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ (s k) _).mpr
    rwa [pathGateDistance,show numberedGenerator (k+1) (prefixPoint k ω)=H.val from numberedGenerator_shell _] at ht
  have hL : 0 < L k := (sq_pos_of_pos (by dsimp [N]; positivity : 0 < (N k:ℝ))).trans_le (le_max_right ..)
  apply isolated_of_gap (hg k) hL (grid_price (k:=k) (hg k) (le_max_right ..) hprice).1 (hw k) _ hx
  intro t v ht hv hlo hhi
  rcases gap t (hit t ht) v (hit v hv) with h|h
  · have hKA : A ≤ ((k+2:ℕ):ℝ) := hK.le.trans (Nat.cast_le.mpr (by omega))
    have h₁ := (div_le_one (by positivity : 0 < ((k+2:ℕ):ℝ))).mpr hKA
    linarith only [h,h₁,hlo,hwW k,hW k]
  · have hl : (m:ℝ)*(8*W k)+2*w k ≤ (Nat.log b (k+1):ℝ) := by
      change (8*(m:ℝ)+2)*W k ≤ _ at hspan
      linarith only [hspan,hwW k]
    exact h.not_ge (hhi.trans hl)

#print axioms gaussian_sublogarithmic_return_window

/-- For each delay schedule fixed before the draw, the excluded interval
can have length proportional to the square root of the logarithm. -/
theorem gaussian_sqrt_log_return_window {κ : ℝ} (hκ : 0 ≤ κ) (hhalf : κ < 1/2) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ d : ℕ → ℝ,
      Tendsto (fun k => pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
        hitWindow (k+1) (nearHilbertContinuousCircuitBudget (k+3))
          ⌊κ*((k+2:ℕ):ℝ)⌋₊ (max (d k) 0) (sqrt (Nat.log b (k+1))))) atTop (𝓝 0) := by
  obtain ⟨b,hb,h⟩ := gaussian_sublogarithmic_return_window hκ hhalf
  refine ⟨b,hb,fun d => h _ d (fun _ => sqrt_nonneg _) ?_⟩
  intro c
  obtain ⟨K,hK⟩ := exists_nat_gt (max c 1)
  filter_upwards [eventually_ge_atTop (b^(K^2))] with k hk
  have hlen : K^2 ≤ Nat.log b (k+1) :=
    (Nat.le_log_iff_pow_le hb (Nat.succ_ne_zero _)).mpr (hk.trans (Nat.le_succ _))
  have hroot : (K:ℝ) ≤ sqrt (Nat.log b (k+1)) :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast hlen)
  rw [max_eq_right (((le_max_right ..).trans hK.le).trans hroot)]
  exact (mul_le_mul_of_nonneg_right (((le_max_left ..).trans hK.le).trans hroot)
    (sqrt_nonneg _)).trans_eq (mul_self_sqrt (Nat.cast_nonneg _))

#print axioms gaussian_sqrt_log_return_window
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
