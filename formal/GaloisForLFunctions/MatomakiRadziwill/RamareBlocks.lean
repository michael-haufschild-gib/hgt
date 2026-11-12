import GaloisForLFunctions.MatomakiRadziwill.RamareDecomposition

/-!
# Ramaré blocks at one scale: geometry of the cofactor ranges

A scale is a finite set `Pr` of primes `≥ P`; a prime `p` lies in the block `v = ⌊H log p⌋`
(`blk`), so `e^{v/H} ≤ p < e^{(v+1)/H}`.  The cofactors of block `v` are the `m ∈ rest` with
`Xe^{-v/H} < m ≤ 4Xe^{-v/H}` (`cof`).  Then (`lt_mul_of_mem_cof`, `mul_lt_of_mem_cof`,
`div_mem_cof`)

* `p ∈ Pr`, `m ∈ cof (blk p)` ⇒ `X < pm < 4Xe^{1/H}`;
* `Xe^{1/H} < n ≤ 4X`, `p ∈ Pr`, `p ∣ n`, `n ∈ rest` ⇒ `n/p ∈ cof (blk p)`,

when `rest` is stable under multiplication by the primes of the scale.  So on the interior range
every factorisation `n = pm` is seen by exactly one block, and only the two boundary ranges
`(X, Xe^{1/H}]`, `(4X, 4Xe^{1/H})` are distorted.
-/

open Finset

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The block index `⌊H log p⌋`. -/
def blk (H : ℝ) (p : ℕ) : ℕ := ⌊H * Real.log p⌋₊

/-- The lower end `Xe^{-v/H}` of the cofactor range of block `v`. -/
def cofLo (X : ℕ) (H : ℝ) (v : ℕ) : ℝ := (X : ℝ) * Real.exp (-(v : ℝ) / H)

/-- The cofactors of block `v`: `m ∈ rest`, `Xe^{-v/H} < m ≤ 4Xe^{-v/H}`. -/
def cof (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (v : ℕ) : Finset ℕ :=
  (Ioc ⌊cofLo X H v⌋₊ ⌊4 * cofLo X H v⌋₊).filter rest

theorem cofLo_nonneg (X : ℕ) (H : ℝ) (v : ℕ) : 0 ≤ cofLo X H v := by
  unfold cofLo; positivity

theorem mem_cof {rest : ℕ → Prop} [DecidablePred rest] {X : ℕ} {H : ℝ} {v m : ℕ} :
    m ∈ cof rest X H v ↔ cofLo X H v < m ∧ (m : ℝ) ≤ 4 * cofLo X H v ∧ rest m := by
  have h0 := cofLo_nonneg X H v
  rw [cof, mem_filter, mem_Ioc, Nat.floor_lt h0, Nat.le_floor_iff (by linarith)]
  tauto

/-- `e^{v/H} ≤ p < e^{(v+1)/H}` for `v = ⌊H log p⌋`, `p ≥ 1`, `H > 0`. -/
theorem exp_blk_le {H : ℝ} (hH : 0 < H) {p : ℕ} (hp : 1 ≤ p) :
    Real.exp ((blk H p : ℝ) / H) ≤ p ∧ (p : ℝ) < Real.exp (((blk H p : ℝ) + 1) / H) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog0 : 0 ≤ H * Real.log p := mul_nonneg hH.le (Real.log_nonneg (by exact_mod_cast hp))
  have h1 : (blk H p : ℝ) ≤ H * Real.log p := Nat.floor_le hlog0
  have h2 : H * Real.log p < (blk H p : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · rw [← Real.exp_log hp0]
    exact Real.exp_le_exp.mpr (by rw [div_le_iff₀ hH]; linarith)
  · rw [← Real.exp_log hp0]
    exact Real.exp_lt_exp.mpr (by rw [lt_div_iff₀ hH]; linarith)

/-- `e^{v/H} · Xe^{-v/H} = X`. -/
theorem exp_mul_cofLo (X : ℕ) {H : ℝ} (v : ℕ) :
    Real.exp ((v : ℝ) / H) * cofLo X H v = X := by
  rw [cofLo, mul_left_comm, ← Real.exp_add, show (v : ℝ) / H + -(v : ℝ) / H = 0 by ring,
    Real.exp_zero, mul_one]

/-- **Products of a block prime and one of its cofactors exceed `X`.** -/
theorem lt_mul_of_mem_cof {rest : ℕ → Prop} [DecidablePred rest] {X : ℕ} {H : ℝ} (hH : 0 < H)
    {p m : ℕ} (hp : 1 ≤ p) (hm : m ∈ cof rest X H (blk H p)) : (X : ℝ) < (p * m : ℕ) := by
  rw [mem_cof] at hm
  obtain ⟨hpe, -⟩ := exp_blk_le hH hp
  have hlo := cofLo_nonneg X H (blk H p)
  have he := Real.exp_pos ((blk H p : ℝ) / H)
  have h := exp_mul_cofLo X (H := H) (blk H p)
  push_cast
  calc (X : ℝ) = Real.exp ((blk H p : ℝ) / H) * cofLo X H (blk H p) := h.symm
    _ < (p : ℝ) * m := by
        rcases eq_or_lt_of_le hlo with h0 | hpos
        · rw [← h0, mul_zero]
          have : (0 : ℝ) < m := by rw [← h0] at hm; exact hm.1
          have : (0 : ℝ) < p := by exact_mod_cast hp
          positivity
        · exact mul_lt_mul' hpe hm.1 hpos.le (lt_of_lt_of_le he hpe)

/-- **Products of a block prime and one of its cofactors are below `4Xe^{1/H}`.** -/
theorem mul_lt_of_mem_cof {rest : ℕ → Prop} [DecidablePred rest] {X : ℕ} {H : ℝ} (hH : 0 < H)
    {p m : ℕ} (hp : 1 ≤ p) (hm : m ∈ cof rest X H (blk H p)) :
    ((p * m : ℕ) : ℝ) < 4 * X * Real.exp (1 / H) := by
  rw [mem_cof] at hm
  obtain ⟨-, hpe⟩ := exp_blk_le hH hp
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (cofLo_nonneg X H _) hm.1
  have hkey : Real.exp (((blk H p : ℝ) + 1) / H) * (4 * cofLo X H (blk H p))
      = 4 * X * Real.exp (1 / H) := by
    rw [cofLo, show ((blk H p : ℝ) + 1) / H = (blk H p : ℝ) / H + 1 / H by ring, Real.exp_add]
    have h := Real.exp_add ((blk H p : ℝ) / H) (-(blk H p : ℝ) / H)
    rw [show (blk H p : ℝ) / H + -(blk H p : ℝ) / H = 0 by ring, Real.exp_zero] at h
    calc Real.exp ((blk H p : ℝ) / H) * Real.exp (1 / H)
          * (4 * ((X : ℝ) * Real.exp (-(blk H p : ℝ) / H)))
        = 4 * X * Real.exp (1 / H)
          * (Real.exp ((blk H p : ℝ) / H) * Real.exp (-(blk H p : ℝ) / H)) := by ring
      _ = 4 * X * Real.exp (1 / H) := by rw [← h, mul_one]
  push_cast
  rw [← hkey]
  calc (p : ℝ) * m < Real.exp (((blk H p : ℝ) + 1) / H) * m := mul_lt_mul_of_pos_right hpe hm0
    _ ≤ Real.exp (((blk H p : ℝ) + 1) / H) * (4 * cofLo X H (blk H p)) :=
        mul_le_mul_of_nonneg_left hm.2.1 (Real.exp_pos _).le

/-- **Interior integers see every factorisation.**  For `Xe^{1/H} < n ≤ 4X`, a prime `p ∣ n` with
`p ∈ Pr` and `n ∈ rest`, the cofactor `n/p` lies in `cof (blk p)`. -/
theorem div_mem_cof {rest : ℕ → Prop} [DecidablePred rest] {Pr : Finset ℕ}
    (hrest : ∀ p ∈ Pr, ∀ m, rest (p * m) ↔ rest m) {X : ℕ} {H : ℝ} (hH : 0 < H)
    {p n : ℕ} (hp : p ∈ Pr) (hp1 : 1 ≤ p) (hpn : p ∣ n)
    (hlow : (X : ℝ) * Real.exp (1 / H) < n) (hup : (n : ℝ) ≤ 4 * X) (hn : rest n) :
    n / p ∈ cof rest X H (blk H p) := by
  obtain ⟨k, rfl⟩ := hpn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
  rw [Nat.mul_div_cancel_left k (by omega), mem_cof]
  obtain ⟨hpe, hpe'⟩ := exp_blk_le hH hp1
  have he := Real.exp_pos ((blk H p : ℝ) / H)
  push_cast at hlow hup
  refine ⟨?_, ?_, (hrest p hp k).mp hn⟩
  · -- `Xe^{-v/H} < k` from `Xe^{1/H} < pk < e^{(v+1)/H} k`
    have hstep : (X : ℝ) * Real.exp (1 / H) < Real.exp (((blk H p : ℝ) + 1) / H) * k := by
      calc (X : ℝ) * Real.exp (1 / H) < p * k := hlow
        _ ≤ Real.exp (((blk H p : ℝ) + 1) / H) * k := by
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          exact mul_le_mul_of_nonneg_right hpe'.le hk0
    rw [show ((blk H p : ℝ) + 1) / H = 1 / H + (blk H p : ℝ) / H by ring, Real.exp_add] at hstep
    have h1 : (X : ℝ) < Real.exp ((blk H p : ℝ) / H) * k := by
      have he1 := Real.exp_pos (1 / H)
      have := (mul_lt_mul_left he1).mp (by linarith [hstep] :
        Real.exp (1 / H) * X < Real.exp (1 / H) * (Real.exp ((blk H p : ℝ) / H) * k))
      exact this
    rw [cofLo, show -(blk H p : ℝ) / H = -((blk H p : ℝ) / H) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_lt_iff₀ he]
    linarith
  · -- `k ≤ 4Xe^{-v/H}` from `pk ≤ 4X`, `p ≥ e^{v/H}`
    rw [cofLo, show -(blk H p : ℝ) / H = -((blk H p : ℝ) / H) by ring, Real.exp_neg]
    rw [show 4 * ((X : ℝ) * (Real.exp ((blk H p : ℝ) / H))⁻¹)
        = 4 * X / Real.exp ((blk H p : ℝ) / H) by ring, le_div_iff₀ he]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc (k : ℝ) * Real.exp ((blk H p : ℝ) / H) ≤ k * p := mul_le_mul_of_nonneg_left hpe hk0
      _ = p * k := by ring
      _ ≤ 4 * X := hup

end

end GaloisForLFunctions.MatomakiRadziwill
