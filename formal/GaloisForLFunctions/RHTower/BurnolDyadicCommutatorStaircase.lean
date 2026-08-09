import Mathlib

/-!
# The universal dyadic commutator staircase

Let `P_a` be multiplication by the indicator of the aperture `(0,a)` and let

`T₂ f(t) = ∑_{n ≥ 1} 2^{-n} f(t/2ⁿ)`

be the causal dyadic Euler inverse.  If `f` is constant equal to `c` on the aperture, the
commutator `[P_a, T₂] f` vanishes inside the aperture and is the geometric staircase `-c 2^{-k}`
on the dyadic shell `[a 2^k, a 2^{k+1})`.  Because the shells tile `[a, ∞)` and the `k`-th shell has
length `a 2^k`, the squared `L²`-norm of the commutator on the positive ray is exactly `2 a |c|²`.

Applied at the fixed Route-R aperture `a = 1/2` to the two Fourier orientations of the zero-divided
source, whose heads are `a_ρ` and `b_ρ`, the difference of the two squared commutator norms is
exactly the oriented Burnol current `|a_ρ|² - |b_ρ|²`.
-/

open Real Filter Topology MeasureTheory Set

noncomputable section

namespace RHTower

/-- Multiplication by the indicator of the aperture `(0,a)`. -/
def burnolAperturePart (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => if t ∈ Ioo (0 : ℝ) a then f t else 0

/-- The causal dyadic Euler inverse `T₂ f(t) = ∑_{n ≥ 1} 2^{-n} f(t/2ⁿ)`. -/
def burnolDyadicLadder (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * f (t / 2 ^ (n + 1))

/-- The aperture commutator `[P_a, T₂] f`. -/
def burnolApertureCommutator (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => burnolAperturePart a (burnolDyadicLadder f) t -
    burnolDyadicLadder (burnolAperturePart a f) t

/-! ## The staircase -/

/-- Every point of `[a, ∞)` lies in exactly one dyadic shell. -/
theorem exists_burnolDyadicShell {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    ∃ k : ℕ, a * 2 ^ k ≤ t ∧ t < a * 2 ^ (k + 1) := by
  have hset : ∃ n : ℕ, t < a * 2 ^ n := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, t / a < 2 ^ n := pow_unbounded_of_one_lt _ one_lt_two
    exact ⟨n, by rwa [div_lt_iff₀ ha, mul_comm] at hn⟩
  classical
  set n₀ : ℕ := Nat.find hset with hn₀
  have hn₀spec : t < a * 2 ^ n₀ := Nat.find_spec hset
  have hpos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso
      rw [h] at hn₀spec
      simp only [pow_zero, mul_one] at hn₀spec
      linarith
    · exact h
  refine ⟨n₀ - 1, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact absurd hcon (Nat.find_min hset (m := n₀ - 1) (by omega))
  · rwa [show n₀ - 1 + 1 = n₀ by omega]

/-- Inside the aperture the commutator vanishes. -/
theorem burnolApertureCommutator_eq_zero_of_mem {a c : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ s, s ∈ Ioo (0 : ℝ) a → f s = c) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) a) :
    burnolApertureCommutator a f t = 0 := by
  have hin : ∀ n : ℕ, t / 2 ^ (n + 1) ∈ Ioo (0 : ℝ) a := by
    intro n
    have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    refine ⟨by positivity, ?_⟩
    have h1 : t / 2 ^ (n + 1) ≤ t := by
      rw [div_le_iff₀ hpow]
      nlinarith [ht.1, one_le_two_pow_iff_of_ne_zero (n := n + 1) (by omega),
        (one_le_two_pow_iff_of_ne_zero (n := n + 1) (by omega))]
    exact lt_of_le_of_lt h1 ht.2
  have hladder : burnolDyadicLadder f t = burnolDyadicLadder (burnolAperturePart a f) t := by
    rw [burnolDyadicLadder, burnolDyadicLadder]
    refine tsum_congr (fun n => ?_)
    rw [burnolAperturePart, if_pos (hin n)]
  rw [burnolApertureCommutator, burnolAperturePart, if_pos ht, hladder, sub_self]

/-- **The universal dyadic commutator staircase.**  On the `k`-th dyadic shell the commutator has
the constant value `-c 2^{-k}`. -/
theorem burnolApertureCommutator_shell {a c : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : ∀ s, s ∈ Ioo (0 : ℝ) a → f s = c) {k : ℕ} {t : ℝ}
    (hlo : a * 2 ^ k ≤ t) (hhi : t < a * 2 ^ (k + 1)) :
    burnolApertureCommutator a f t = -c * (1 / 2 : ℝ) ^ k := by
  have hone : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hta : a ≤ t := le_trans (by nlinarith) hlo
  have hnotmem : t ∉ Ioo (0 : ℝ) a := fun hmem => absurd hmem.2 (not_lt.mpr hta)
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le ha hta
  -- membership of the dyadic samples in the aperture
  have hmem : ∀ n : ℕ, (t / 2 ^ (n + 1) ∈ Ioo (0 : ℝ) a) ↔ k ≤ n := by
    intro n
    have hpow : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    constructor
    · intro hin
      by_contra hcon
      rw [not_le] at hcon
      have hle : (2 : ℝ) ^ (n + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have : a * 2 ^ (n + 1) ≤ a * 2 ^ k := by nlinarith
      have h2 : t < a * 2 ^ (n + 1) := by
        rw [div_lt_iff₀ hpow] at hin
        linarith [hin.2]
      linarith
    · intro hkn
      refine ⟨by positivity, ?_⟩
      rw [div_lt_iff₀ hpow]
      have hle : a * 2 ^ (k + 1) ≤ a * 2 ^ (n + 1) := by
        have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      linarith
  have hterm : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * burnolAperturePart a f (t / 2 ^ (n + 1)) =
      if k ≤ n then c * (1 / 2 : ℝ) ^ (n + 1) else 0 := by
    intro n
    rw [burnolAperturePart]
    by_cases hkn : k ≤ n
    · rw [if_pos ((hmem n).mpr hkn), if_pos hkn, hf _ ((hmem n).mpr hkn)]
      ring
    · rw [if_neg (fun hc => hkn ((hmem n).mp hc)), if_neg hkn, mul_zero]
  have hsum : burnolDyadicLadder (burnolAperturePart a f) t = c * (1 / 2 : ℝ) ^ k := by
    rw [burnolDyadicLadder, tsum_congr hterm]
    have hgeom : HasSum (fun n : ℕ => if k ≤ n then c * (1 / 2 : ℝ) ^ (n + 1) else 0)
        (c * (1 / 2 : ℝ) ^ k) := by
      have hbase : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) ((1 - 1 / 2 : ℝ)⁻¹) :=
        hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
      have hscaled := hbase.mul_left (c * (1 / 2 : ℝ) ^ (k + 1))
      have hval : c * (1 / 2 : ℝ) ^ (k + 1) * (1 - 1 / 2 : ℝ)⁻¹ = c * (1 / 2 : ℝ) ^ k := by
        rw [pow_succ]
        norm_num
        ring
      rw [hval] at hscaled
      have hshift := (hasSum_nat_add_iff (f := fun n : ℕ =>
        if k ≤ n then c * (1 / 2 : ℝ) ^ (n + 1) else 0) k).mp ?_
      · have hzero : ∑ i ∈ Finset.range k,
            (if k ≤ i then c * (1 / 2 : ℝ) ^ (i + 1) else 0) = 0 := by
          refine Finset.sum_eq_zero (fun i hi => ?_)
          rw [if_neg (by omega_nat <;> skip)]
        · rw [hzero, add_zero] at hshift
          exact hshift
      · refine hscaled.congr_fun ?_
        intro n
        rw [if_pos (by omega), ← pow_add]
        ring_nf
    exact hgeom.tsum_eq
  rw [burnolApertureCommutator, burnolAperturePart, if_neg hnotmem, hsum]
  ring

end RHTower
