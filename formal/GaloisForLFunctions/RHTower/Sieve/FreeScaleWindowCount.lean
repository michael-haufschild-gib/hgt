import GaloisForLFunctions.RHTower.Sieve.FreeScaleCellBound
import GaloisForLFunctions.RHTower.Sieve.MarkerHarmonicSupply

/-!
# The sign count of a window at a free physical scale

The free blocks are consecutive and disjoint, every prime of the whole marker range lies in exactly
one of them, and each marker's cell bound depends only on its own block.  So the sign count of
`(X, X+H]` follows from `Sieve/MarkerSignWindowCount.card_sign_window_ge'` at an arbitrary `X`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

open Classical in
/-- The exceptional starts of all the free blocks. -/
def freeBadStartUnion (β : ℝ) (m K₀ : ℕ) : Finset ℕ :=
  (Finset.range (K₀ + 1)).biUnion (fun k => badStart (freeScale m k) (freeWindow β m k))

open Classical in
/-- The good markers of a free-scale construction. -/
def freeGoodMarkers (β : ℝ) (X m K₀ : ℕ) : Finset ℕ :=
  (bigPrimeSet (X / freeStart m 0) (X / freeStart m (K₀ + 1))).filter
    (fun p => X / p ∉ freeBadStartUnion β m K₀)

/-- **The sign count of the physical window at a free scale.** -/
theorem free_card_sign_window_ge {β : ℝ} {X m K₀ H : ℕ} {σ : ℤ} {rho S B : ℝ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < freeStart m (K₀ + 1))
    (hXH : X + H ≤ (X / freeStart m 0) * (X / freeStart m 0)) (hrho : 0 ≤ rho)
    (hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k)
    (hfit : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k, rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1))
    (hS : S ≤ ∑ p ∈ freeGoodMarkers β X m K₀, 1 / (p : ℝ))
    (hB : (((freeGoodMarkers β X m K₀).card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hsub : freeGoodMarkers β X m K₀
      ⊆ bigPrimeSet (X / freeStart m 0) (X / freeStart m (K₀ + 1)) :=
    Finset.filter_subset _ _
  refine card_sign_window_ge' (M₀ := X / freeStart m 0) (freeGoodMarkers β X m K₀)
    (fun p hp => prime_of_mem_bigPrimeSet (hsub hp))
    (fun p hp => lt_of_mem_bigPrimeSet (hsub hp)) hXH hrho ?_ hS hB
  intro p hp
  obtain ⟨k, hk, hmem⟩ := exists_freeBlock hpos (hsub hp)
  have hnot : X / p ∉ freeBadStartUnion β m K₀ := (Finset.mem_filter.1 hp).2
  have hnotk : X / p ∉ badStart (freeScale m k) (freeWindow β m k) := by
    intro hc
    exact hnot (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), hc⟩)
  exact free_cell_bound hdvd hk hσ hpos (hmk2 k hk) hmem hrho (hfit k hk p hmem)
    (hsup k hk p hmem) hnotk

/-! ## The device at a free scale -/

/-- The whole marker range of a free-scale construction. -/
def freeRange (X m K₀ : ℕ) : Finset ℕ :=
  bigPrimeSet (X / freeStart m 0) (X / freeStart m (K₀ + 1))

theorem freeGoodMarkers_eq (β : ℝ) (X m K₀ : ℕ) :
    freeGoodMarkers β X m K₀
      = (freeRange X m K₀).filter (fun p => X / p ∉ freeBadStartUnion β m K₀) := rfl

/-- **Markers of the free range sharing a start are close.**  The minimal start is
`freeStart m (K₀+1)`, so two markers with the same start differ by at most `X/(that)²`. -/
theorem free_separation {X m K₀ : ℕ} (hpos : 0 < freeStart m (K₀ + 1)) :
    ∀ p ∈ freeRange X m K₀, ∀ q ∈ freeRange X m K₀, p < q → X / q = X / p →
      q ≤ p + X / (freeStart m (K₀ + 1) * freeStart m (K₀ + 1)) := by
  intro p hp q _ hpq heq
  have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
  have hk0 : 0 < freeStart m 0 := lt_of_lt_of_le hpos (freeStart_anti m (Nat.zero_le _))
  obtain ⟨hlow, -⟩ := start_mem_of_mem_bigPrimeSet hpos hk0 hp
  exact reciprocal_separation hpos hp0 hpq hlow heq

/-- **The harmonic mass of the good markers at a free scale.** -/
theorem free_sum_inv_goodMarkers_ge {β : ℝ} {X m K₀ K : ℕ} {Pi b : ℝ}
    (hpos : 0 < freeStart m (K₀ + 1)) (hM0 : 0 < X / freeStart m 0)
    (hK : X / (freeStart m (K₀ + 1) * freeStart m (K₀ + 1)) ≤ K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((freeRange X m K₀).filter (fun p => p + d ∈ freeRange X m K₀)).card : ℕ) : ℝ) ≤ Pi)
    (hbthr : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ)
      * ((((freeRange X m K₀).card : ℕ) : ℝ) + 2 * Pi) ≤ b ^ 2) (hb0 : 0 ≤ b) :
    (∑ p ∈ freeRange X m K₀, 1 / (p : ℝ)) - b / ((X / freeStart m 0 : ℕ) : ℝ)
      ≤ ∑ p ∈ freeGoodMarkers β X m K₀, 1 / (p : ℝ) := by
  classical
  have hsep : ∀ p ∈ freeRange X m K₀, ∀ q ∈ freeRange X m K₀, p < q →
      X / q = X / p → q ≤ p + K := by
    intro p hp q hq hpq heq
    have := free_separation hpos p hp q hq hpq heq
    omega
  exact sum_inv_good_markers_ge (X := X) (M₀ := X / freeStart m 0) (K := K)
    (S := freeBadStartUnion β m K₀) (M := freeRange X m K₀) hM0
    (fun p hp => lt_of_mem_bigPrimeSet hp) hsep hpair hbthr hb0

/-- The exceptional starts of a free-scale construction, blockwise. -/
theorem card_freeBadStartUnion_le (β : ℝ) (m K₀ : ℕ) :
    (((freeBadStartUnion β m K₀).card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range (K₀ + 1),
          (((badStart (freeScale m k) (freeWindow β m k)).card : ℕ) : ℝ) := by
  classical
  have h := Finset.card_biUnion_le (s := Finset.range (K₀ + 1))
    (t := fun k => badStart (freeScale m k) (freeWindow β m k))
  have hcast : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ)
      ≤ ((∑ k ∈ Finset.range (K₀ + 1),
          (badStart (freeScale m k) (freeWindow β m k)).card : ℕ) : ℝ) := by
    rw [freeBadStartUnion]
    exact_mod_cast h
  refine hcast.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The free-scale capstone.**  The sign count of `(X, X+H]` from the marker range's own
harmonic mass and count, with the exceptional starts discarded by the device. -/
theorem free_card_sign_window_ge_device {β : ℝ} {X m K₀ H K : ℕ} {σ : ℤ} {rho S B Pi b : ℝ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < freeStart m (K₀ + 1))
    (hM0 : 0 < X / freeStart m 0)
    (hXH : X + H ≤ (X / freeStart m 0) * (X / freeStart m 0)) (hrho : 0 ≤ rho)
    (hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k)
    (hfit : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k, rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1))
    (hK : X / (freeStart m (K₀ + 1) * freeStart m (K₀ + 1)) ≤ K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((freeRange X m K₀).filter (fun p => p + d ∈ freeRange X m K₀)).card : ℕ) : ℝ) ≤ Pi)
    (hbthr : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ)
      * ((((freeRange X m K₀).card : ℕ) : ℝ) + 2 * Pi) ≤ b ^ 2) (hb0 : 0 ≤ b)
    (hS : S ≤ (∑ p ∈ freeRange X m K₀, 1 / (p : ℝ)) - b / ((X / freeStart m 0 : ℕ) : ℝ))
    (hB : (((freeRange X m K₀).card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hgood := free_sum_inv_goodMarkers_ge (β := β) hpos hM0 hK hpair hbthr hb0
  refine free_card_sign_window_ge hdvd hσ hpos hXH hrho hmk2 hfit hsup (le_trans hS hgood) ?_
  refine le_trans ?_ hB
  exact Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset _ _))

/-- **The device threshold from upper bounds.**  A caller supplies an upper bound for the
exceptional starts, the marker count and the pair budget, and a `b` beating their product. -/
theorem free_device_threshold {β : ℝ} {X m K₀ : ℕ} {E N P Pi b : ℝ}
    (hE : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ) ≤ E)
    (hN : (((freeRange X m K₀).card : ℕ) : ℝ) ≤ N) (hP : Pi ≤ P) (hE0 : 0 ≤ E)
    (hPi0 : 0 ≤ Pi) (hthr : E * (N + 2 * P) ≤ b ^ 2) :
    (((freeBadStartUnion β m K₀).card : ℕ) : ℝ)
      * ((((freeRange X m K₀).card : ℕ) : ℝ) + 2 * Pi) ≤ b ^ 2 := by
  have hnn : (0 : ℝ) ≤ (((freeRange X m K₀).card : ℕ) : ℝ) + 2 * Pi := by
    have : (0 : ℝ) ≤ (((freeRange X m K₀).card : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine le_trans (mul_le_mul hE (by linarith) hnn hE0) hthr

/-- **The free-scale count from four upper bounds and a harmonic lower bound.**  This is the
interface a numeric instantiation has to meet: everything is an inequality between named
quantities. -/
theorem free_card_sign_window_ge_bounds {β : ℝ} {X m K₀ H K : ℕ} {σ : ℤ}
    {rho S B E N P Pi b : ℝ}
    (hdvd : 2 ^ (K₀ + 1) ∣ m) (hσ : σ = 1 ∨ σ = -1) (hpos : 0 < freeStart m (K₀ + 1))
    (hM0 : 0 < X / freeStart m 0)
    (hXH : X + H ≤ (X / freeStart m 0) * (X / freeStart m 0)) (hrho : 0 ≤ rho)
    (hmk2 : ∀ k, k ≤ K₀ → 2 ≤ freeStart m k)
    (hfit : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k,
      (freeWindow β m k + 1) * (p : ℝ) ≤ (H : ℝ))
    (hsup : ∀ k, k ≤ K₀ → ∀ p ∈ freeBlock X m k, rho * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β m k / 2 - 1))
    (hK : X / (freeStart m (K₀ + 1) * freeStart m (K₀ + 1)) ≤ K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((freeRange X m K₀).filter (fun p => p + d ∈ freeRange X m K₀)).card : ℕ) : ℝ) ≤ Pi)
    (hE : (((freeBadStartUnion β m K₀).card : ℕ) : ℝ) ≤ E)
    (hN : (((freeRange X m K₀).card : ℕ) : ℝ) ≤ N) (hP : Pi ≤ P) (hE0 : 0 ≤ E)
    (hthr : E * (N + 2 * P) ≤ b ^ 2) (hb0 : 0 ≤ b)
    (hS : S ≤ (∑ p ∈ freeRange X m K₀, 1 / (p : ℝ)) - b / ((X / freeStart m 0 : ℕ) : ℝ))
    (hB : (((freeRange X m K₀).card : ℕ) : ℝ) ≤ B) :
    rho * ((H : ℝ) * S - B)
      ≤ ((((Finset.Ioc X (X + H)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  have hPi0 : (0 : ℝ) ≤ Pi := by
    refine le_trans ?_ hpair
    exact Finset.sum_nonneg fun d _ => Nat.cast_nonneg _
  exact free_card_sign_window_ge_device hdvd hσ hpos hM0 hXH hrho hmk2 hfit hsup hK hpair
    (free_device_threshold hE hN hP hE0 hPi0 hthr) hb0 hS hB

end

end RHTower.Sieve
