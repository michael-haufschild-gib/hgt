import GaloisForLFunctions.RHTower.Sieve.FreeScaleWindowCount
import GaloisForLFunctions.RHTower.Sieve.CardLengthDilation

/-!
# The fit and supply conditions at a free scale

Both conditions compare the marker's cell `H/p` with its block's window.  Since a marker of block
`k` satisfies `X/freeStart m k < p ≤ X/freeStart m (k+1)`, both sides are proportional to `X/m`,
and the conditions reduce to inequalities between the cell parameter and the block windows — in
which the physical scale does not appear at all.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem freeScale_le_zero {m k : ℕ} : freeScale m k ≤ freeScale m 0 := by
  rw [freeScale, freeScale]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _)
    (by exact_mod_cast freeStart_anti m (Nat.zero_le k)) 2

theorem one_le_freeScale {m k : ℕ} (h2 : 2 ≤ freeStart m k) : 1 ≤ freeScale m k := by
  have h2R : (2 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast h2
  rw [freeScale]
  nlinarith

/-- The block window is the base one shrunk by `2^{-k}`, and is dominated by the base value. -/
theorem freeWindow_le {β : ℝ} (hβ : 0 < β) {m k : ℕ} (h2 : 2 ≤ freeStart m k) :
    freeWindow β m k ≤ ((1 : ℝ) / 2) ^ k * cardLength β (freeScale m 0) := by
  rw [freeWindow, scaledLength]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact cardLength_mono hβ (one_le_freeScale h2) freeScale_le_zero

/-- **The fit condition at a free scale.**  It only constrains the cell parameter against the base
window: the physical scale cancels. -/
theorem free_fit_of_le {β : ℝ} (hβ : 0 < β) {X m K₀ k H p : ℕ} (hk : k ≤ K₀)
    (hpos : 0 < freeStart m (K₀ + 1)) (hdvd : 2 ^ (K₀ + 1) ∣ m)
    (h2 : 2 ≤ freeStart m k) (hp : p ∈ freeBlock X m k)
    (hH : (2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1)) * (X : ℝ) / (m : ℝ)
      ≤ (H : ℝ)) :
    (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ) := by
  have hk1 : 0 < freeStart m (k + 1) := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  have hm0 : 0 < m := by
    by_contra hc
    have : m = 0 := by omega
    rw [freeStart, this] at hk1
    simp at hk1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  -- the marker is at most `2^{k+1}·X/m`
  have hstep : freeStart m (k + 1) * 2 ^ (k + 1) = m := by
    obtain ⟨w, rfl⟩ := hdvd
    rw [freeStart_pow_mul (by omega : k + 1 ≤ K₀ + 1)]
    rw [show (2 : ℕ) ^ (K₀ + 1 - (k + 1)) * w * 2 ^ (k + 1)
        = 2 ^ (K₀ + 1 - (k + 1)) * 2 ^ (k + 1) * w by ring, ← pow_add]
    congr 2
    omega
  have hple : (p : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (X : ℝ) / (m : ℝ) := by
    rw [freeBlock, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
    have hpn : p ≤ X / freeStart m (k + 1) := hp.1.2
    have hpR : (p : ℝ) ≤ ((X / freeStart m (k + 1) : ℕ) : ℝ) := by exact_mod_cast hpn
    have hdivR : ((X / freeStart m (k + 1) : ℕ) : ℝ)
        ≤ (X : ℝ) / ((freeStart m (k + 1) : ℕ) : ℝ) := Nat.cast_div_le
    have hk1R : (0 : ℝ) < ((freeStart m (k + 1) : ℕ) : ℝ) := by exact_mod_cast hk1
    have hval : (X : ℝ) / ((freeStart m (k + 1) : ℕ) : ℝ)
        = (2 : ℝ) ^ (k + 1) * (X : ℝ) / (m : ℝ) := by
      have hmv : (m : ℝ) = ((freeStart m (k + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (k + 1) := by
        have := congrArg (fun n : ℕ => (n : ℝ)) hstep
        push_cast at this
        linarith [this]
      rw [hmv]
      field_simp
    linarith [hpR, hdivR, hval]
  -- the block window
  have hwin := freeWindow_le hβ (m := m) (k := k) h2
  have hC0 : (0 : ℝ) < cardLength β (freeScale m 0) := cardLength_pos _ _
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (K₀ + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hprod : (freeWindow β m k + 1) * (p : ℝ)
      ≤ (((1 : ℝ) / 2) ^ k * cardLength β (freeScale m 0) + 1)
        * ((2 : ℝ) ^ (k + 1) * (X : ℝ) / (m : ℝ)) := by
    refine mul_le_mul (by linarith [hwin]) hple hp0 (by positivity)
  refine le_trans hprod (le_trans ?_ hH)
  have hpowinv : ((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ (k + 1) = 2 := by
    rw [div_pow, one_pow, pow_succ]
    field_simp
  have hexp : (((1 : ℝ) / 2) ^ k * cardLength β (freeScale m 0) + 1)
        * ((2 : ℝ) ^ (k + 1) * (X : ℝ) / (m : ℝ))
      = (((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ (k + 1) * cardLength β (freeScale m 0)
          + (2 : ℝ) ^ (k + 1)) * (X : ℝ) / (m : ℝ) := by
    ring
  rw [hexp, hpowinv]
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
  gcongr

/-- **The supply condition at a free scale.**  Like the fit, it constrains only the cell parameter
against the block windows. -/
theorem free_supply_of_le {β : ℝ} {X m K₀ k H p : ℕ} {A2 : ℝ} (hk : k ≤ K₀)
    (hpos : 0 < freeStart m (K₀ + 1)) (hdvd : 2 ^ (K₀ + 1) ∣ m)
    (hp : p ∈ freeBlock X m k) (hA2 : 0 < A2)
    (hH : (H : ℝ) ≤ A2 * (X : ℝ) / (m : ℝ))
    (hgap : A2 ≤ 24 * (freeWindow β m k * (2 : ℝ) ^ k) - 48 * (2 : ℝ) ^ k) :
    (squarefreeDensity / 256) * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1) := by
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hk0 : 0 < freeStart m k := lt_of_lt_of_le hpos (freeStart_anti m (by omega))
  have hm0 : 0 < m := by
    by_contra hc
    have : m = 0 := by omega
    rw [freeStart, this] at hk0
    simp at hk0
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- the marker is above `X/freeStart m k`, so its cell is below `2^{-k}·(H·m/X)`
  have hstep : freeStart m k * 2 ^ k = m := by
    obtain ⟨w, rfl⟩ := hdvd
    rw [freeStart_pow_mul (by omega : k ≤ K₀ + 1)]
    rw [show (2 : ℕ) ^ (K₀ + 1 - k) * w * 2 ^ k = 2 ^ (K₀ + 1 - k) * 2 ^ k * w by ring,
      ← pow_add]
    congr 2
    omega
  have hmv : (m : ℝ) = ((freeStart m k : ℕ) : ℝ) * (2 : ℝ) ^ k := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hstep
    push_cast at this
    linarith [this]
  have hk0R : (0 : ℝ) < ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast hk0
  have hplow : (X : ℝ) / ((freeStart m k : ℕ) : ℝ) < (p : ℝ) := by
    rw [freeBlock, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
    have hpn : X / freeStart m k < p := by omega
    have hlt : X < p * freeStart m k := (Nat.div_lt_iff_lt_mul hk0).1 hpn
    have hltR : (X : ℝ) < (p : ℝ) * ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [div_lt_iff₀ hk0R]
    exact hltR
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
  have hnum : (0 : ℝ) < A2 := hA2
  have hfkm : ((freeStart m k : ℕ) : ℝ) / (m : ℝ) = 1 / (2 : ℝ) ^ k := by
    rw [hmv]
    field_simp
  have hcell : (H : ℝ) / (p : ℝ) ≤ A2 / (2 : ℝ) ^ k := by
    rcases eq_or_lt_of_le hX0 with hX | hX
    · have hHz : (H : ℝ) ≤ 0 := by
        refine le_trans hH (le_of_eq ?_)
        rw [← hX]
        simp
      have h1 : (H : ℝ) / (p : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hHz hpR.le
      have h2 : (0 : ℝ) ≤ A2 / (2 : ℝ) ^ k := by positivity
      linarith
    · calc (H : ℝ) / (p : ℝ)
          ≤ (H : ℝ) / ((X : ℝ) / ((freeStart m k : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_left hH0 (div_pos hX hk0R) hplow.le
        _ = (H : ℝ) * ((freeStart m k : ℕ) : ℝ) / (X : ℝ) := by rw [div_div_eq_mul_div]
        _ ≤ (A2 * (X : ℝ) / (m : ℝ)) * ((freeStart m k : ℕ) : ℝ) / (X : ℝ) := by gcongr
        _ = A2 * (((freeStart m k : ℕ) : ℝ) / (m : ℝ)) := by
            field_simp
        _ = A2 / (2 : ℝ) ^ k := by
            rw [hfkm]
            ring
  -- combine with the gap hypothesis
  have hgap' : A2 / (2 : ℝ) ^ k ≤ 24 * freeWindow β m k - 48 := by
    rw [div_le_iff₀ (by positivity)]
    have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    nlinarith [hgap, hpk]
  have hfinal : (squarefreeDensity / 256) * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (squarefreeDensity / 256) * (24 * freeWindow β m k - 48) := by
    refine mul_le_mul_of_nonneg_left (by linarith [hcell, hgap']) (by positivity)
  refine hfinal.trans (le_of_eq ?_)
  ring

/-- The cell parameter of a free-scale construction. -/
def freeCell (β : ℝ) (X m K₀ : ℕ) : ℕ :=
  ⌈(2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1)) * (X : ℝ) / (m : ℝ)⌉₊

/-- **Both conditions hold at the cell parameter.**  The fit needs `H` above
`(2C₀+2^{K₀+1})X/m` and the supply needs it below `(2C₀+2^{K₀+1}+1)X/m`; the ceiling of the first
lies in that band because `X ≥ m`. -/
theorem free_fit_supply_ceil {β : ℝ} (hβ : 0 < β) {X m K₀ : ℕ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hpos : 0 < freeStart m (K₀ + 1)) (hXm : m ≤ X)
    (hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k)
    (hgap : ∀ k, k ≤ K₀ →
      2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1) + 1
        ≤ 24 * (freeWindow β m k * (2 : ℝ) ^ k) - 48 * (2 : ℝ) ^ k) :
    (∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
        (freeWindow β m k + 1) * (p : ℝ) ≤ ((freeCell β X m K₀ : ℕ) : ℝ))
      ∧ (∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
        (squarefreeDensity / 256) * (((freeCell β X m K₀ : ℕ) : ℝ) / (p : ℝ) - 1)
          ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1)) := by
  have hm0 : 0 < m := by
    by_contra hc
    have hm : m = 0 := by omega
    rw [freeStart, hm] at hpos
    simp at hpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hC0 : (0 : ℝ) < cardLength β (freeScale m 0) := cardLength_pos _ _
  set A : ℝ := (2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1)) * (X : ℝ) / (m : ℝ)
    with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    have : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg _
    positivity
  have hAle : A ≤ ((freeCell β X m K₀ : ℕ) : ℝ) := by
    rw [freeCell, ← hA]
    exact Nat.le_ceil A
  have hXmR : (1 : ℝ) ≤ (X : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR, one_mul]
    exact_mod_cast hXm
  have hAge : ((freeCell β X m K₀ : ℕ) : ℝ)
      ≤ (2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1) + 1) * (X : ℝ) / (m : ℝ) := by
    rw [freeCell, ← hA]
    have hceil := Nat.ceil_lt_add_one hA0
    have hval : (2 * cardLength β (freeScale m 0) + (2 : ℝ) ^ (K₀ + 1) + 1) * (X : ℝ) / (m : ℝ)
        = A + (X : ℝ) / (m : ℝ) := by
      rw [hA]
      field_simp
    rw [hval]
    linarith [hceil, hXmR]
  refine ⟨fun k hk p hp => ?_, fun k hk p hp => ?_⟩
  · exact free_fit_of_le hβ hk hpos hdvd (hmk2 k hk) hp (by rw [← hA]; exact hAle)
  · refine free_supply_of_le hk hpos hdvd hp (by positivity) hAge ?_
    exact hgap k hk

end

end RHTower.Sieve
