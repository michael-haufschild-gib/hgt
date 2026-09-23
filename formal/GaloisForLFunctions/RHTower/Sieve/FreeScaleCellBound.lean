import GaloisForLFunctions.RHTower.Sieve.FreeScaleMarkerBlock

/-!
# The cell bound at a free physical scale

With the marker blocks indexed by their start range, the fit and supply conditions of
`Sieve/MarkerBlockSignCount.cell_bound_of_good_start` become inequalities in the block data alone —
the cell parameter against the block's window — and the physical scale never appears in them.  So
the whole per-marker argument runs at an arbitrary `X`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The cofactor scale of the `k`-th free block. -/
def freeScale (m k : ℕ) : ℝ := ((freeStart m k : ℕ) : ℝ) ^ (2 : ℕ)

theorem sqrt_freeScale (m k : ℕ) :
    Real.sqrt (freeScale m k) = ((freeStart m k : ℕ) : ℝ) := by
  rw [freeScale, Real.sqrt_sq (by positivity)]

/-- The window of the `k`-th free block: the base window shrunk by `2^{-k}`. -/
def freeWindow (β : ℝ) (m k : ℕ) : ℝ :=
  scaledLength (((1 : ℝ) / 2) ^ k) β (freeScale m k)

theorem freeWindow_pos (β : ℝ) (m k : ℕ) : 0 < freeWindow β m k := by
  rw [freeWindow]
  exact scaledLength_pos (by positivity) _ _

/-- **The cell bound at one good marker of a free block.** -/
theorem free_cell_bound {β : ℝ} {X m K₀ k p H : ℕ} {σ : ℤ} {rho : ℝ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hk : k ≤ K₀) (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 < freeStart m (K₀ + 1)) (hmk2 : 2 ≤ freeStart m k)
    (hp : p ∈ freeBlock X m k) (hrho : 0 ≤ rho)
    (hfit : (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1))
    (hnot : X / p ∉ badStart (freeScale m k) (freeWindow β m k)) :
    rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell X H p).filter (fun b => moebius b = -σ)).card : ℕ) : ℝ) := by
  classical
  have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
  have hk1 : 0 < freeStart m (k + 1) := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  obtain ⟨hlowN, hhighN⟩ := start_mem_freeBlock hk1 hp
  have ht1 : 1 ≤ X / p := by omega
  obtain ⟨htlow, hthigh⟩ := freeBlock_start_bounds hdvd hk hpos hp
  have hmk2R : (2 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast hmk2
  have hmk0 : (0 : ℝ) < ((freeStart m k : ℕ) : ℝ) := by linarith
  have hy4 : (4 : ℝ) ≤ freeScale m k := by
    rw [freeScale]
    nlinarith [hmk2R]
  have hy0 : (0 : ℝ) < freeWindow β m k := freeWindow_pos β m k
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- the fit, in the form the fibre lemma wants
  have hfit' : (freeWindow β m k * (((X / p : ℕ) : ℝ) + 1) / ((freeStart m k : ℕ) : ℝ) + 1)
      * (p : ℝ) ≤ (H : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hpR.le) hfit
    have hquot : freeWindow β m k * (((X / p : ℕ) : ℝ) + 1) / ((freeStart m k : ℕ) : ℝ)
        ≤ freeWindow β m k := by
      rw [div_le_iff₀ hmk0]
      exact mul_le_mul_of_nonneg_left hthigh hy0.le
    linarith
  -- the supply, in the form the fibre lemma wants
  have hsup' : rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (freeWindow β m k * ((X / p : ℕ) : ℝ) / ((freeStart m k : ℕ) : ℝ) - 1) := by
    refine le_trans hsup (mul_le_mul_of_nonneg_left ?_ (by
      have := squarefreeDensity_pos
      positivity))
    have hfib : freeWindow β m k / 2
        ≤ freeWindow β m k * ((X / p : ℕ) : ℝ) / ((freeStart m k : ℕ) : ℝ) := by
      rw [le_div_iff₀ hmk0, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [htlow, hy0, hmk0]
    linarith
  exact cell_bound_of_good_start hy4 hy0 (sqrt_freeScale m k) hp0 hσ ht1 htlow hthigh hnot
    hfit' hsup'

end

end RHTower.Sieve
