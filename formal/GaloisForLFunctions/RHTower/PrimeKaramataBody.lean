import GaloisForLFunctions.RHTower.PrimeKaramataDarboux

/-!
# The body of the prime Karamata sum

The uniform partition of `[v₀, 1]` into `N` blocks decomposes `W_X` into the head `(0, v₀X]` and the
`N` shells `(v_jX, v_{j+1}X]`.  Each shell obeys the sandwich of `PrimeKaramataShell`, so the total
is bracketed by the two Darboux sums, up to the multiplicative error `1 ± ε` of the slowly varying
factor and the additive error `2ε` of the prime number theorem.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The partition points of `[v₀, 1]`. -/
def karamataNode (v₀ : ℝ) (N : ℕ) (j : ℕ) : ℝ := v₀ + (j : ℝ) * ((1 - v₀) / N)

theorem karamataNode_zero (v₀ : ℝ) (N : ℕ) : karamataNode v₀ N 0 = v₀ := by
  simp [karamataNode]

theorem karamataNode_last {v₀ : ℝ} {N : ℕ} (hN : 0 < N) : karamataNode v₀ N N = 1 := by
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast hN.ne'
  rw [karamataNode]
  field_simp
  ring

theorem karamataNode_mono {v₀ : ℝ} (hv₀1 : v₀ < 1) {N : ℕ} {i j : ℕ} (hij : i ≤ j) :
    karamataNode v₀ N i ≤ karamataNode v₀ N j := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [karamataNode, hN]
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hstep : (0 : ℝ) ≤ (1 - v₀) / N := by
    have : (0 : ℝ) < 1 - v₀ := by linarith
    positivity
  have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  rw [karamataNode, karamataNode]
  nlinarith [hcast, hstep]

theorem karamataNode_pos {v₀ : ℝ} (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1) (N j : ℕ) :
    0 < karamataNode v₀ N j := by
  have h := karamataNode_mono (v₀ := v₀) (N := N) hv₀1 (Nat.zero_le j)
  rw [karamataNode_zero] at h
  linarith

theorem karamataNode_le_one {v₀ : ℝ} (hv₀1 : v₀ < 1) {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    karamataNode v₀ N j ≤ 1 := by
  rw [← karamataNode_last (v₀ := v₀) hN]
  exact karamataNode_mono hv₀1 hj

theorem karamataNode_diff {v₀ : ℝ} {N : ℕ} (j : ℕ) :
    karamataNode v₀ N (j + 1) - karamataNode v₀ N j = (1 - v₀) / N := by
  rw [karamataNode, karamataNode]
  push_cast
  ring

/-- **The shell totals.** -/
theorem karamata_shells_bounds {α : ℝ} (hα0 : 0 ≤ α) {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    {v₀ : ℝ} (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) :
    ∀ᶠ X in atTop,
      (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε)
          * ((1 - v₀) / N - 2 * ε)) * (X ^ (1 - α) * L X)
          ≤ ∑ j ∈ Finset.range N, primeLogSum (rvPrimeWeight α L)
              (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)
        ∧ ∑ j ∈ Finset.range N, primeLogSum (rvPrimeWeight α L)
              (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)
          ≤ (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε)
              * ((1 - v₀) / N + 2 * ε)) * (X ^ (1 - α) * L X) := by
  have hall : ∀ j ∈ Finset.range N, ∀ᶠ X in atTop,
      primeLogSum (rvPrimeWeight α L) (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X)
          ≤ (karamataNode v₀ N j ^ (-α) * (1 + ε)
              * ((karamataNode v₀ N (j + 1) - karamataNode v₀ N j) + 2 * ε))
            * (X ^ (1 - α) * L X)
        ∧ (karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε)
              * ((karamataNode v₀ N (j + 1) - karamataNode v₀ N j) - 2 * ε))
            * (X ^ (1 - α) * L X)
          ≤ primeLogSum (rvPrimeWeight α L) (karamataNode v₀ N j * X)
              (karamataNode v₀ N (j + 1) * X) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact karamata_shell_bounds hα0 hL (karamataNode_pos hv₀ hv₀1 N j)
      (karamataNode_mono hv₀1 (Nat.le_succ j))
      (karamataNode_le_one hv₀1 hN hj) hε hε1
  rw [← Filter.eventually_all_finset] at hall
  filter_upwards [hall] with X hX
  constructor
  · calc (∑ j ∈ Finset.range N, karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε)
          * ((1 - v₀) / N - 2 * ε)) * (X ^ (1 - α) * L X)
        = ∑ j ∈ Finset.range N, (karamataNode v₀ N (j + 1) ^ (-α) * (1 - ε)
            * ((karamataNode v₀ N (j + 1) - karamataNode v₀ N j) - 2 * ε))
              * (X ^ (1 - α) * L X) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [karamataNode_diff]
      _ ≤ ∑ j ∈ Finset.range N, primeLogSum (rvPrimeWeight α L)
            (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) :=
          Finset.sum_le_sum fun j hj => (hX j hj).2
  · calc (∑ j ∈ Finset.range N, primeLogSum (rvPrimeWeight α L)
          (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X))
        ≤ ∑ j ∈ Finset.range N, (karamataNode v₀ N j ^ (-α) * (1 + ε)
            * ((karamataNode v₀ N (j + 1) - karamataNode v₀ N j) + 2 * ε))
              * (X ^ (1 - α) * L X) :=
          Finset.sum_le_sum fun j hj => (hX j hj).1
      _ = (∑ j ∈ Finset.range N, karamataNode v₀ N j ^ (-α) * (1 + ε)
            * ((1 - v₀) / N + 2 * ε)) * (X ^ (1 - α) * L X) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [karamataNode_diff]

/-- **The decomposition of `W_X`.** -/
theorem rvWeightSum_decomp {α : ℝ} {L : ℝ → ℝ} {v₀ : ℝ} (hv₀ : 0 < v₀) (hv₀1 : v₀ < 1)
    {N : ℕ} (hN : 0 < N) {X : ℝ} (hX : 0 < X) :
    rvWeightSum α L X
      = primeLogSum (rvPrimeWeight α L) 0 (v₀ * X)
        + ∑ j ∈ Finset.range N, primeLogSum (rvPrimeWeight α L)
            (karamataNode v₀ N j * X) (karamataNode v₀ N (j + 1) * X) := by
  set x : ℕ → ℝ := fun k => if k = 0 then 0 else karamataNode v₀ N (k - 1) * X with hx
  have hx0 : x 0 = 0 := by simp [hx]
  have hxsucc : ∀ k : ℕ, x (k + 1) = karamataNode v₀ N k * X := by
    intro k
    simp [hx]
  have hmono : ∀ k, ⌊x k⌋₊ ≤ ⌊x (k + 1)⌋₊ := by
    intro k
    refine Nat.floor_mono ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [hx0, hxsucc]
      have := karamataNode_pos hv₀ hv₀1 N 0
      positivity
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [hxsucc, hxsucc]
      have hnode := karamataNode_mono (v₀ := v₀) (N := N) hv₀1 (Nat.le_succ m)
      nlinarith [hnode, hX.le]
  have hchain := primeLogSum_chain (rvPrimeWeight α L) x hmono (N + 1)
  rw [hx0, hxsucc] at hchain
  rw [karamataNode_last hN] at hchain
  rw [Finset.sum_range_succ'] at hchain
  rw [one_mul] at hchain
  rw [rvWeightSum, ← hchain]
  have hfirst : primeLogSum (rvPrimeWeight α L) (x 0) (x (0 + 1))
      = primeLogSum (rvPrimeWeight α L) 0 (v₀ * X) := by
    rw [hx0, hxsucc, karamataNode_zero]
  have hrest : ∀ k ∈ Finset.range N, primeLogSum (rvPrimeWeight α L) (x (k + 1)) (x (k + 1 + 1))
      = primeLogSum (rvPrimeWeight α L) (karamataNode v₀ N k * X)
          (karamataNode v₀ N (k + 1) * X) := by
    intro k _
    rw [hxsucc, hxsucc]
  rw [Finset.sum_congr rfl hrest, hfirst]
  ring

end

end RHTower
