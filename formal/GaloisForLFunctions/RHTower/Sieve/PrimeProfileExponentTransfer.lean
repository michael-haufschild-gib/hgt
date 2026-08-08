import GaloisForLFunctions.RHTower.Sieve.PrimeWindowExponentLimit

/-!
# Prime profile sums in the exponent coordinate

A prime `p ≤ N` is read at the exponent `t_p = log p / log N ∈ (0, 1]`, and a profile `g` is
sampled there:

`primeProfileSum g N = Σ_{p ≤ N} g (log p / log N) / p`.

Two exact facts control such a sum.

*Localization.* A prime of the window `(⌊N^a⌋, ⌊N^b⌋]` has exponent exactly in `(a, b]` — the
floors introduce no slop at all, because `⌊x⌋ < p` already forces `x < p`.

*Head bound.* Below the cutoff `N^c` the profile contributes at most `C · mertensA/log N`, whenever
`|g t| ≤ C t`.  Mertens' first theorem turns this into `C·c + O(1/log N)`, so a profile vanishing
linearly at the origin has a negligible small-prime head.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-- The prime profile sum, read in the exponent coordinate `t = log p / log N`. -/
def primeProfileSum (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, g (Real.log p / Real.log N) / (p : ℝ)

/-- The prime profile sum restricted to one window. -/
def primeProfileWindowSum (g : ℝ → ℝ) (N z b : ℕ) : ℝ :=
  ∑ p ∈ bigPrimeSet z b, g (Real.log p / Real.log N) / (p : ℝ)

/-! ## Exact exponent localization -/

theorem exponentCutoff_lt_of_mem {c : ℝ} {N p : ℕ} (hp : exponentCutoff c N < p) :
    (N : ℝ) ^ c < (p : ℝ) := by
  have hfl := Nat.lt_floor_add_one ((N : ℝ) ^ c)
  have hstep : ⌊(N : ℝ) ^ c⌋₊ + 1 ≤ p := hp
  have hcast : ((⌊(N : ℝ) ^ c⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hstep
  linarith

/-- **Exact exponent localization.**  Every prime of the window `(⌊N^a⌋, ⌊N^b⌋]` has exponent
coordinate in `(a, b]`. -/
theorem exponent_mem_Ioc_of_mem_bigPrimeSet {a b : ℝ} {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ bigPrimeSet (exponentCutoff a N) (exponentCutoff b N)) :
    a < Real.log p / Real.log N ∧ Real.log p / Real.log N ≤ b := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hlow, hhigh⟩, _⟩ := hp
  have hlow' : exponentCutoff a N < p := hlow
  have hpa : (N : ℝ) ^ a < (p : ℝ) := exponentCutoff_lt_of_mem hlow'
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans (Real.rpow_pos_of_pos hNpos a) hpa
  have hpb : (p : ℝ) ≤ (N : ℝ) ^ b := by
    have hcast : ((p : ℕ) : ℝ) ≤ ((exponentCutoff b N : ℕ) : ℝ) := by exact_mod_cast hhigh
    exact le_trans hcast (Nat.floor_le (by positivity))
  constructor
  · rw [lt_div_iff₀ hlogN]
    have := Real.log_lt_log (Real.rpow_pos_of_pos hNpos a) hpa
    rwa [Real.log_rpow hNpos] at this
  · rw [div_le_iff₀ hlogN]
    have := Real.log_le_log hppos hpb
    rwa [Real.log_rpow hNpos] at this

/-! ## The window approximation -/

theorem abs_primeProfileWindowSum_sub_le {g : ℝ → ℝ} {a b ε : ℝ} (_hε : 0 ≤ ε)
    (hgb : ∀ t : ℝ, a < t → t ≤ b → |g t - g a| ≤ ε) {N : ℕ} (hN : 2 ≤ N) :
    |primeProfileWindowSum g N (exponentCutoff a N) (exponentCutoff b N)
        - g a * ∑ p ∈ bigPrimeSet (exponentCutoff a N) (exponentCutoff b N), 1 / (p : ℝ)|
      ≤ ε * ∑ p ∈ bigPrimeSet (exponentCutoff a N) (exponentCutoff b N), 1 / (p : ℝ) := by
  classical
  set W := bigPrimeSet (exponentCutoff a N) (exponentCutoff b N) with hW
  have hppos : ∀ p ∈ W, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    rw [hW, bigPrimeSet, Finset.mem_filter] at hp
    exact_mod_cast hp.2.pos
  have hrw : primeProfileWindowSum g N (exponentCutoff a N) (exponentCutoff b N)
      - g a * ∑ p ∈ W, 1 / (p : ℝ)
      = ∑ p ∈ W, (g (Real.log p / Real.log N) - g a) / (p : ℝ) := by
    rw [primeProfileWindowSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have := hppos p hp
    field_simp
  rw [hrw, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  have hp0 := hppos p hp
  obtain ⟨hlt, hle⟩ := exponent_mem_Ioc_of_mem_bigPrimeSet hN (hW ▸ hp)
  rw [abs_div, abs_of_pos hp0]
  rw [show ε * (1 / (p : ℝ)) = ε / (p : ℝ) from by ring]
  gcongr
  exact hgb _ hlt hle

/-! ## The small-prime head -/

theorem abs_primeProfileSum_head_le {g : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hg : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {M N : ℕ} (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE M, g (Real.log p / Real.log N) / (p : ℝ)|
      ≤ C * mertensA M / Real.log N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesLE M,
      |g (Real.log p / Real.log N) / (p : ℝ)| ≤ C * (Real.log p / (p : ℝ)) / Real.log N := by
    intro p hp
    have hprime : p.Prime := (Nat.mem_primesLE.1 hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hnn : (0 : ℝ) ≤ Real.log p / Real.log N := by positivity
    have hbound := hg _ hnn
    rw [abs_div, abs_of_pos hppos]
    rw [div_le_div_iff₀ hppos (by positivity)]
    have hstep : |g (Real.log p / Real.log N)| * Real.log N ≤
        C * (Real.log p / Real.log N) * Real.log N :=
      mul_le_mul_of_nonneg_right hbound hlogN.le
    have heq : C * (Real.log p / Real.log N) * Real.log N
        = C * (Real.log p / (p : ℝ)) * (p : ℝ) := by
      field_simp
    rw [heq] at hstep
    exact hstep
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.sum_div, ← Finset.mul_sum, mertensA]

/-- **The small-prime head vanishes with the exponent.**  Below `N^c` a linearly vanishing profile
contributes at most `C·c` plus an `O(1/log N)` term. -/
theorem abs_primeProfileSum_head_le' {g : ℝ → ℝ} {C c : ℝ} (hC : 0 ≤ C) (_hc : 0 < c)
    (hg : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) {N : ℕ} (hN : 2 ≤ N)
    (hcut : (2 : ℝ) ≤ (N : ℝ) ^ c) :
    |∑ p ∈ Nat.primesLE (exponentCutoff c N),
        g (Real.log p / Real.log N) / (p : ℝ)|
      ≤ C * c + C * mertensFirstConst / Real.log N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
  have hbase := abs_primeProfileSum_head_le (M := exponentCutoff c N) hC hg hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hone : 1 ≤ exponentCutoff c N := by
    rw [exponentCutoff]
    exact Nat.le_floor (by push_cast; linarith)
  have honeR : (1 : ℝ) ≤ ((exponentCutoff c N : ℕ) : ℝ) := by exact_mod_cast hone
  have hAle : mertensA (exponentCutoff c N)
      ≤ Real.log (exponentCutoff c N) + mertensFirstConst := by
    have := abs_le.1 (abs_mertensA_sub_log_le hone)
    linarith [this.2]
  have hlogle : Real.log (exponentCutoff c N) ≤ c * Real.log N := by
    have hfloor_le : ((exponentCutoff c N : ℕ) : ℝ) ≤ (N : ℝ) ^ c :=
      Nat.floor_le (by positivity)
    have hstep := Real.log_le_log (by linarith : (0 : ℝ) < ((exponentCutoff c N : ℕ) : ℝ))
      hfloor_le
    rwa [Real.log_rpow hNpos] at hstep
  refine le_trans hbase ?_
  rw [div_le_iff₀ hlogN]
  have hmono : C * mertensA (exponentCutoff c N)
      ≤ C * (c * Real.log N + mertensFirstConst) := by
    refine mul_le_mul_of_nonneg_left ?_ hC
    linarith
  have hfin : C * (c * Real.log N + mertensFirstConst)
      = (C * c + C * mertensFirstConst / Real.log N) * Real.log N := by
    field_simp
  linarith [hmono, hfin.le, hfin.ge]

end

end RHTower.Sieve
