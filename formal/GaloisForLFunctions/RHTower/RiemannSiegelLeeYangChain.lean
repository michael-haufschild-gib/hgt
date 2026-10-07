import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Riemann–Siegel sums as domain-wall expansions of a Lee–Yang chain

A ferromagnetic Ising chain has sites `k = 0, …, N` with fields `u k` and walls between `k` and
`k + 1` with fugacities `c k ∈ [0, 1]`.  Its partition function is
`Z = Σ_σ ∏_{σ_k = −} u_k ∏_{σ_k ≠ σ_{k+1}} c_k`.  In transfer form, `chainPair` records the
weights `(A_k, B_k)` of the configurations on sites `0..k` with last spin `+`, resp. `−`.

* **Lee–Yang** (`chainZ_ne_zero_of_norm_lt_one`, `chainZ_ne_zero_of_im_ne_zero`): if every field
  lies in the open unit disc, then `‖B_k‖ < ‖A_k‖` and `Z ≠ 0`.  Global spin flip
  (`chainZ_reciprocal`) gives `Z(u) = (∏ u_k) Z(1/u)`.  Hence for fields `u_k = e^{−i λ_k z}`
  with `λ_k > 0`, every zero of `z ↦ Z` is real, for every choice of fugacities in `[0, 1]`.
* **Telescoping** (`prod_gammaSiteField`): for the Γ sites `λ_k = log ((k+2)/(k+1))`,
  `∏_{i ≤ k} u_i = e^{−i z log (k+2)}`.  So a single domain wall after site `k` carries the integer
  frequency `log (k+2)`.
* **Riemann–Siegel at first order** (`hasDerivAt_gammaChainZ`): along `c ↦ ε c` the partition
  function is `2 e^{−i z L/2} cos (z L/2)` at `ε = 0`, with `L = log (N+2)`.  Its `ε`-derivative
  is `2 e^{−i z L/2} Σ_{k<N} c_k cos (z log (k+2) − z L/2)`.  This is the Riemann–Siegel cosine
  sum with the frozen phase `z L/2`.
-/

open Complex Finset

namespace RHTower.LeeYangChain

noncomputable section

/-- Chain weights `(A_k, B_k)` of the configurations on sites `0..k` ending in `+`, resp. `−`. -/
def chainPair (c : ℕ → ℝ) (u : ℕ → ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, u 0)
  | k + 1 =>
      ((chainPair c u k).1 + (c k : ℂ) * (chainPair c u k).2,
        u (k + 1) * ((c k : ℂ) * (chainPair c u k).1 + (chainPair c u k).2))

/-- The chain partition function on sites `0..N`. -/
def chainZ (c : ℕ → ℝ) (u : ℕ → ℂ) (N : ℕ) : ℂ := (chainPair c u N).1 + (chainPair c u N).2

/-! ## The Lee–Yang property -/

theorem normSq_mul_add_sub (c : ℝ) (A B : ℂ) :
    Complex.normSq ((c : ℂ) * A + B) - Complex.normSq (A + (c : ℂ) * B) =
      (c ^ 2 - 1) * (Complex.normSq A - Complex.normSq B) := by
  simp only [Complex.normSq_add, Complex.normSq_ofReal, map_mul,
    Complex.conj_ofReal]
  have h1 : ((c : ℂ) * A * (starRingEnd ℂ) B).re = c * (A * (starRingEnd ℂ) B).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  have h2 : (A * ((c : ℂ) * (starRingEnd ℂ) B)).re = c * (A * (starRingEnd ℂ) B).re := by
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [h1, h2]
  ring

theorem chainPair_inside {c : ℕ → ℝ} {u : ℕ → ℂ} (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1)
    (hu : ∀ k, ‖u k‖ < 1) (k : ℕ) :
    (chainPair c u k).1 ≠ 0 ∧ ‖(chainPair c u k).2‖ < ‖(chainPair c u k).1‖ := by
  induction k with
  | zero => simpa [chainPair] using hu 0
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    obtain ⟨A, hAdef⟩ : ∃ A, A = (chainPair c u k).1 := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B, B = (chainPair c u k).2 := ⟨_, rfl⟩
    rw [← hAdef] at hA hB
    rw [← hBdef] at hB
    simp only [chainPair, ← hAdef, ← hBdef]
    have hck : ‖(c k : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 k)]
      exact hc1 k
    have hcB : ‖(c k : ℂ) * B‖ < ‖A‖ := by
      rw [norm_mul]
      calc ‖(c k : ℂ)‖ * ‖B‖ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right hck (norm_nonneg _)
        _ < ‖A‖ := by rw [one_mul]; exact hB
    have hA' : A + (c k : ℂ) * B ≠ 0 := by
      intro h
      have : A = -((c k : ℂ) * B) := by linear_combination h
      rw [this, norm_neg] at hcB
      exact lt_irrefl _ hcB
    have hsq : Complex.normSq ((c k : ℂ) * A + B) ≤ Complex.normSq (A + (c k : ℂ) * B) := by
      have h := normSq_mul_add_sub (c k) A B
      have hAB : Complex.normSq B < Complex.normSq A := by
        rw [← Complex.sq_norm, ← Complex.sq_norm]
        exact pow_lt_pow_left₀ hB (norm_nonneg _) two_ne_zero
      have hc2 : c k ^ 2 - 1 ≤ 0 := by nlinarith [hc0 k, hc1 k]
      nlinarith
    have hnorm : ‖(c k : ℂ) * A + B‖ ≤ ‖A + (c k : ℂ) * B‖ := by
      rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    refine ⟨hA', ?_⟩
    rw [norm_mul]
    calc ‖u (k + 1)‖ * ‖(c k : ℂ) * A + B‖ ≤ ‖u (k + 1)‖ * ‖A + (c k : ℂ) * B‖ :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ < 1 * ‖A + (c k : ℂ) * B‖ :=
          mul_lt_mul_of_pos_right (hu (k + 1)) (norm_pos_iff.mpr hA')
      _ = ‖A + (c k : ℂ) * B‖ := one_mul _

/-- **Lee–Yang for chains.**  Fields inside the unit disc make the partition function nonzero. -/
theorem chainZ_ne_zero_of_norm_lt_one {c : ℕ → ℝ} {u : ℕ → ℂ} (hc0 : ∀ k, 0 ≤ c k)
    (hc1 : ∀ k, c k ≤ 1) (hu : ∀ k, ‖u k‖ < 1) (N : ℕ) : chainZ c u N ≠ 0 := by
  obtain ⟨hA, hB⟩ := chainPair_inside hc0 hc1 hu N
  intro h
  rw [chainZ] at h
  have : (chainPair c u N).2 = -(chainPair c u N).1 := by linear_combination h
  rw [this, norm_neg] at hB
  exact lt_irrefl _ hB

/-- Global spin flip. -/
theorem chainPair_reciprocal (c : ℕ → ℝ) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) (k : ℕ) :
    (chainPair c u k).1 = (∏ i ∈ range (k + 1), u i) * (chainPair c (fun i => (u i)⁻¹) k).2 ∧
    (chainPair c u k).2 = (∏ i ∈ range (k + 1), u i) * (chainPair c (fun i => (u i)⁻¹) k).1 := by
  induction k with
  | zero =>
    simp only [chainPair, zero_add, range_one, prod_singleton]
    exact ⟨(mul_inv_cancel₀ (hu 0)).symm, (mul_one _).symm⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [chainPair]
    rw [prod_range_succ, h1, h2]
    have hk := hu (k + 1)
    constructor
    · field_simp
      ring
    · ring

theorem chainZ_reciprocal (c : ℕ → ℝ) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) (N : ℕ) :
    chainZ c u N = (∏ i ∈ range (N + 1), u i) * chainZ c (fun i => (u i)⁻¹) N := by
  obtain ⟨h1, h2⟩ := chainPair_reciprocal c hu N
  rw [chainZ, chainZ, h1, h2]
  ring

/-- The exponential field with frequencies `freqs`. -/
def chainExpField (freqs : ℕ → ℝ) (z : ℂ) (k : ℕ) : ℂ := cexp (-(I * (freqs k : ℂ) * z))

theorem norm_chainExpField (freqs : ℕ → ℝ) (z : ℂ) (k : ℕ) :
    ‖chainExpField freqs z k‖ = Real.exp (freqs k * z.im) := by
  rw [chainExpField, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Real zeros.**  With exponential fields of positive frequencies, every zero of the chain
partition function is real, for every choice of fugacities in `[0, 1]`. -/
theorem chainZ_ne_zero_of_im_ne_zero {c : ℕ → ℝ} {freqs : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k)
    (hc1 : ∀ k, c k ≤ 1) (hfreq : ∀ k, 0 < freqs k) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    chainZ c (chainExpField freqs z) N ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · refine chainZ_ne_zero_of_norm_lt_one hc0 hc1 (fun k => ?_) N
    rw [norm_chainExpField, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (hfreq k) hneg
  · have hne : ∀ k, chainExpField freqs z k ≠ 0 := fun k => Complex.exp_ne_zero _
    rw [chainZ_reciprocal c hne N]
    refine mul_ne_zero (prod_ne_zero_iff.mpr fun k _ => hne k)
      (chainZ_ne_zero_of_norm_lt_one hc0 hc1 (fun k => ?_) N)
    rw [norm_inv, norm_chainExpField, inv_lt_one₀ (Real.exp_pos _), Real.one_lt_exp_iff]
    exact mul_pos (hfreq k) hpos

/-! ## The Γ sites and the Riemann–Siegel linearization -/

/-- The Γ-site frequency `log ((k+2)/(k+1))`, the convergence factor of the Euler product of
`Γ(s/2)`. -/
def gammaFreq (k : ℕ) : ℝ := Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))

theorem gammaFreq_pos (k : ℕ) : 0 < gammaFreq k := by
  apply Real.log_pos
  rw [one_lt_div (by positivity)]
  linarith

/-- Telescoping: `Σ_{i ≤ k} log ((i+2)/(i+1)) = log (k+2)`. -/
theorem sum_gammaFreq (k : ℕ) : ∑ i ∈ range (k + 1), gammaFreq i = Real.log ((k : ℝ) + 2) := by
  induction k with
  | zero => simp [gammaFreq]
  | succ k ih =>
    rw [sum_range_succ, ih, gammaFreq, Real.log_div (by positivity) (by positivity)]
    push_cast
    ring_nf

theorem sum_Ico_gammaFreq {j N : ℕ} (h : j ≤ N) :
    ∑ i ∈ Ico (j + 1) (N + 1), gammaFreq i = Real.log ((N : ℝ) + 2) - Real.log ((j : ℝ) + 2) := by
  have := sum_range_add_sum_Ico gammaFreq (show j + 1 ≤ N + 1 by omega)
  rw [sum_gammaFreq, sum_gammaFreq] at this
  linarith

theorem prod_chainExpField (freqs : ℕ → ℝ) (z : ℂ) (s : Finset ℕ) :
    ∏ i ∈ s, chainExpField freqs z i = cexp (-(I * ((∑ i ∈ s, freqs i : ℝ) : ℂ) * z)) := by
  simp only [chainExpField]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]

/-- `∏_{i ≤ k} u_i = e^{−i z log (k+2)}`: a wall after site `k` carries the frequency
`log (k+2)`. -/
theorem prod_gammaSiteField (z : ℂ) (k : ℕ) :
    ∏ i ∈ range (k + 1), chainExpField gammaFreq z i = cexp (-(I * (Real.log ((k : ℝ) + 2) : ℂ) * z)) := by
  rw [prod_chainExpField, sum_gammaFreq]

theorem prod_Ico_gammaSiteField (z : ℂ) {j N : ℕ} (h : j ≤ N) :
    ∏ i ∈ Ico (j + 1) (N + 1), chainExpField gammaFreq z i =
      cexp (-(I * ((Real.log ((N : ℝ) + 2) - Real.log ((j : ℝ) + 2) : ℝ) : ℂ) * z)) := by
  rw [prod_chainExpField, sum_Ico_gammaFreq h]

/-- With all fugacities zero only the two aligned configurations survive. -/
theorem chainPair_of_eq_zero {c : ℕ → ℝ} (hc : ∀ k, c k = 0) (u : ℕ → ℂ) (k : ℕ) :
    chainPair c u k = (1, ∏ i ∈ range (k + 1), u i) := by
  induction k with
  | zero => simp [chainPair]
  | succ k ih =>
    simp only [chainPair, ih, hc k, Complex.ofReal_zero, zero_mul, add_zero, zero_add,
      prod_range_succ]
    ring_nf

/-- The derivative of the chain weights along `c ↦ ε c` at `ε = 0`: one domain wall at a time. -/
theorem hasDerivAt_chainPair (c : ℕ → ℝ) (u : ℕ → ℂ) (k : ℕ) :
    HasDerivAt (fun ε : ℝ => (chainPair (fun j => ε * c j) u k).1)
        (∑ j ∈ range k, (c j : ℂ) * ∏ i ∈ range (j + 1), u i) 0 ∧
      HasDerivAt (fun ε : ℝ => (chainPair (fun j => ε * c j) u k).2)
        (∑ j ∈ range k, (c j : ℂ) * ∏ i ∈ Ico (j + 1) (k + 1), u i) 0 := by
  have hval : ∀ m, chainPair (fun j => (0 : ℝ) * c j) u m = (1, ∏ i ∈ range (m + 1), u i) :=
    chainPair_of_eq_zero (fun j => zero_mul _) u
  induction k with
  | zero =>
    simp only [chainPair, range_zero, sum_empty]
    exact ⟨hasDerivAt_const _ _, hasDerivAt_const _ _⟩
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    have hcε : HasDerivAt (fun ε : ℝ => ((ε * c k : ℝ) : ℂ)) (c k : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (c k)).ofReal_comp
      simpa using this
    have hv0 := hval k
    have hA0 : (chainPair (fun j => (0 : ℝ) * c j) u k).1 = 1 := by rw [hv0]
    have hB0 : (chainPair (fun j => (0 : ℝ) * c j) u k).2 = ∏ i ∈ range (k + 1), u i := by
      rw [hv0]
    constructor
    · have h := HasDerivAt.add hA (HasDerivAt.mul hcε hB)
      refine h.congr_deriv ?_
      rw [sum_range_succ, hB0]
      simp
    · have h := HasDerivAt.const_mul (u (k + 1)) (HasDerivAt.add (HasDerivAt.mul hcε hA) hB)
      refine h.congr_deriv ?_
      rw [hA0, sum_range_succ]
      simp only [Complex.ofReal_zero, zero_mul, mul_one]
      have hsum : ∑ j ∈ range k, (c j : ℂ) * ∏ i ∈ Ico (j + 1) (k + 1 + 1), u i =
          u (k + 1) * ∑ j ∈ range k, (c j : ℂ) * ∏ i ∈ Ico (j + 1) (k + 1), u i := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun j hj => ?_
        rw [prod_Ico_succ_top (by have := mem_range.mp hj; omega)]
        ring
      have htop : ∏ i ∈ Ico (k + 1) (k + 1 + 1), u i = u (k + 1) := by
        rw [prod_Ico_succ_top le_rfl, Ico_self, prod_empty, one_mul]
      rw [htop, hsum]
      ring

theorem exp_add_exp_eq_two_cos (a b : ℂ) :
    cexp (-(I * a)) + cexp (-(I * b)) = 2 * cexp (-(I * ((a + b) / 2))) * Complex.cos ((a - b) / 2) := by
  rw [Complex.cos]
  have e1 : cexp (-(I * ((a + b) / 2))) * cexp ((a - b) / 2 * I) = cexp (-(I * b)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-(I * ((a + b) / 2))) * cexp (-((a - b) / 2) * I) = cexp (-(I * a)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination -e1 - e2

/-- **The zero-fugacity chain is a single cosine:**
`Z = 2 e^{−i z L/2} cos (z L/2)` with `L = log (N+2)`. -/
theorem gammaChainZ_zero (c : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    chainZ (fun j => (0 : ℝ) * c j) (chainExpField gammaFreq z) N =
      2 * cexp (-(I * (z * Real.log ((N : ℝ) + 2) / 2))) *
        Complex.cos (z * Real.log ((N : ℝ) + 2) / 2) := by
  rw [chainZ, chainPair_of_eq_zero (fun j => zero_mul _), prod_gammaSiteField]
  have h := exp_add_exp_eq_two_cos 0 ((Real.log ((N : ℝ) + 2) : ℂ) * z)
  have e1 : cexp (-(I * 0)) = 1 := by simp
  have e2 : -(I * ((Real.log ((N : ℝ) + 2) : ℂ) * z)) = -(I * (Real.log ((N : ℝ) + 2) : ℂ) * z) := by
    ring
  have e3 : (0 + (Real.log ((N : ℝ) + 2) : ℂ) * z) / 2 = z * Real.log ((N : ℝ) + 2) / 2 := by ring
  have e4 : (0 - (Real.log ((N : ℝ) + 2) : ℂ) * z) / 2 = -(z * Real.log ((N : ℝ) + 2) / 2) := by
    ring
  rw [e1, e2, e3, e4, Complex.cos_neg] at h
  exact h

/-- **Riemann–Siegel at first order.**  Along `c ↦ ε c`, the `ε`-derivative of the Γ-site chain at
`ε = 0` is `2 e^{−i z L/2} Σ_{k<N} c_k cos (z log (k+2) − z L/2)`.  This is the Riemann–Siegel
cosine sum with coefficients `c_k` at `n = k + 2` and frozen phase `z L/2`, `L = log (N+2)`. -/
theorem hasDerivAt_gammaChainZ (c : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    HasDerivAt (fun ε : ℝ => chainZ (fun j => ε * c j) (chainExpField gammaFreq z) N)
      (2 * cexp (-(I * (z * Real.log ((N : ℝ) + 2) / 2))) *
        ∑ k ∈ range N, (c k : ℂ) *
          Complex.cos (z * Real.log ((k : ℝ) + 2) - z * Real.log ((N : ℝ) + 2) / 2)) 0 := by
  obtain ⟨hA, hB⟩ := hasDerivAt_chainPair c (chainExpField gammaFreq z) N
  have h := HasDerivAt.add hA hB
  refine h.congr_deriv ?_
  rw [← sum_add_distrib, Finset.mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkN : k ≤ N := (mem_range.mp hk).le
  rw [← mul_add, prod_gammaSiteField, prod_Ico_gammaSiteField z hkN]
  have h2 := exp_add_exp_eq_two_cos ((Real.log ((k : ℝ) + 2) : ℂ) * z)
    (((Real.log ((N : ℝ) + 2) - Real.log ((k : ℝ) + 2) : ℝ) : ℂ) * z)
  have e1 : -(I * ((Real.log ((k : ℝ) + 2) : ℂ) * z)) = -(I * (Real.log ((k : ℝ) + 2) : ℂ) * z) := by
    ring
  have e2 : -(I * ((((Real.log ((N : ℝ) + 2) - Real.log ((k : ℝ) + 2) : ℝ) : ℂ)) * z)) =
      -(I * (((Real.log ((N : ℝ) + 2) - Real.log ((k : ℝ) + 2) : ℝ) : ℂ)) * z) := by ring
  rw [e1, e2] at h2
  rw [h2]
  push_cast
  ring_nf

/-- **The Riemann–Siegel cosine sum is the first-order domain-wall expansion of a real-rooted
family.**  Take the Γ-site chain on sites `0..N` with wall fugacities `ε c_k`, where
`c_k ∈ [0, 1]` and `ε ∈ [0, 1]`, and put `L = log (N+2)`.
* For every such `ε` all zeros in `z` are real.
* At `ε = 0` the partition function is `2 e^{−i z L/2} cos (z L/2)`.
* Its `ε`-derivative at `0` is `2 e^{−i z L/2} Σ_{k<N} c_k cos (z log (k+2) − z L/2)`.
With `c_k = (k+2)^{−1/2}` for `k + 2 ≤ M` and `c_k = 0` beyond, the last two items together give
the Riemann–Siegel main sum `Σ_{n ≤ M} n^{−1/2} cos (z L/2 − z log n)` with frozen phase. -/
theorem riemannSiegel_leeYang_chain {c : ℕ → ℝ} (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1)
    (N : ℕ) :
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ,
        chainZ (fun j => ε * c j) (chainExpField gammaFreq z) N = 0 → z.im = 0) ∧
      (∀ z : ℂ, chainZ (fun j => (0 : ℝ) * c j) (chainExpField gammaFreq z) N =
        2 * cexp (-(I * (z * Real.log ((N : ℝ) + 2) / 2))) *
          Complex.cos (z * Real.log ((N : ℝ) + 2) / 2)) ∧
      (∀ z : ℂ, HasDerivAt (fun ε : ℝ => chainZ (fun j => ε * c j) (chainExpField gammaFreq z) N)
        (2 * cexp (-(I * (z * Real.log ((N : ℝ) + 2) / 2))) *
          ∑ k ∈ range N, (c k : ℂ) *
            Complex.cos (z * Real.log ((k : ℝ) + 2) - z * Real.log ((N : ℝ) + 2) / 2)) 0) := by
  refine ⟨fun ε hε0 hε1 z hz => ?_, gammaChainZ_zero c N, hasDerivAt_gammaChainZ c N⟩
  by_contra him
  exact chainZ_ne_zero_of_im_ne_zero (fun k => mul_nonneg hε0 (hc0 k))
    (fun k => mul_le_one₀ hε1 (hc0 k) (hc1 k)) gammaFreq_pos N him hz

end

end RHTower.LeeYangChain
