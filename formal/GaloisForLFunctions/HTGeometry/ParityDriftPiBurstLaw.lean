import GaloisForLFunctions.HTGeometry.PiIrrationalityExponent
import GaloisForLFunctions.HTGeometry.BinaryParityDriftExactLaws

/-!
# The parity drift of `π` cannot run at full speed for long

If `|D_π(N + L) − D_π(N)| = L`, then the base-4 digits `N + 1, …, N + L` of `π` are all `2` or all
`1`, so `π` lies within `4^{−(N+L)}` of a fraction with denominator `3·4ᴺ`.  Since `π` has finite
irrationality exponent, such full-speed windows have length `L = O(N)`:

* `exists_burst_bound_pi` : there is `K` such that for all large `N` and every `L`,
  `|D_π(N + L) − D_π(N)| = L` forces `L ≤ K N`.

This is the only unconditional statement about the parity drift of `π` that the known Diophantine
information provides; it constrains the speed of the drift, not its asymptotic frequency.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

theorem drift_add (x : ℝ) (N L : ℕ) :
    drift x (N + L) - drift x N =
      ∑ i ∈ range L, (binDigit x (2 * (N + i) + 1) - binDigit x (2 * (N + i) + 2)) := by
  unfold drift
  rw [sum_range_add, add_sub_cancel_left]

/-- A sum of `L` terms in `[−1, 1]` with absolute value `L` has constant terms `±1`. -/
theorem all_eq_of_abs_sum_eq {f : ℕ → ℤ} {L : ℕ} (hf : ∀ i, |f i| ≤ 1)
    (h : |∑ i ∈ range L, f i| = L) : (∀ i < L, f i = 1) ∨ (∀ i < L, f i = -1) := by
  have hle : ∀ i, f i ≤ 1 := fun i => (abs_le.mp (hf i)).2
  have hge : ∀ i, -1 ≤ f i := fun i => (abs_le.mp (hf i)).1
  rcases abs_eq (by positivity : (0 : ℤ) ≤ L) |>.mp h with hpos | hneg
  · left
    have hsum : ∑ i ∈ range L, (1 - f i) = 0 := by
      rw [sum_sub_distrib, hpos]; simp
    intro i hi
    have := (sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.mpr (hle j)).mp hsum i
      (mem_range.mpr hi)
    linarith
  · right
    have hsum : ∑ i ∈ range L, (f i + 1) = 0 := by
      rw [sum_add_distrib, hneg]; simp
    intro i hi
    have := (sum_eq_zero_iff_of_nonneg fun j _ => by linarith [hge j]).mp hsum i
      (mem_range.mpr hi)
    linarith

/-- A run of `L` equal base-4 digits `c ∈ {1, 2}` after position `N` puts `x` within
`4^{−(N+L)}` of `(3⌊4ᴺx⌋ + c)/(3·4ᴺ)`. -/
theorem abs_sub_le_of_quatDigit_run {x : ℝ} {N L : ℕ} {c : ℤ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hrun : ∀ i < L, quatDigit x (N + i + 1) = c) :
    |x - (3 * ⌊(4 : ℝ) ^ N * x⌋ + c) / (3 * 4 ^ N)| ≤ 1 / 4 ^ (N + L) := by
  -- `3 ⌊4^{N+k} x⌋ = 3·4ᵏ ⌊4ᴺ x⌋ + c(4ᵏ − 1)`
  have hrec : ∀ k ≤ L, 3 * ⌊(4 : ℝ) ^ (N + k) * x⌋ =
      3 * 4 ^ k * ⌊(4 : ℝ) ^ N * x⌋ + c * (4 ^ k - 1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hq := hrun k (by omega)
      have hstep := floor_four_pow_succ x (N + k)
      rw [← quatDigit_succ, hq] at hstep
      rw [show N + (k + 1) = N + k + 1 by ring, hstep]
      rw [show (3 : ℤ) * (4 * ⌊(4 : ℝ) ^ (N + k) * x⌋ + c) =
        4 * (3 * ⌊(4 : ℝ) ^ (N + k) * x⌋) + 3 * c by ring, ih (by omega)]
      ring
  have hL := hrec L le_rfl
  set F := ⌊(4 : ℝ) ^ (N + L) * x⌋ with hF
  have hF1 := Int.floor_le ((4 : ℝ) ^ (N + L) * x)
  have hF2 := Int.lt_floor_add_one ((4 : ℝ) ^ (N + L) * x)
  have hLR : (3 : ℝ) * F = 3 * 4 ^ L * ⌊(4 : ℝ) ^ N * x⌋ + c * (4 ^ L - 1) := by
    exact_mod_cast hL
  have h4N : (0 : ℝ) < 4 ^ N := by positivity
  have h4L : (0 : ℝ) < 4 ^ L := by positivity
  have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  have hc2' : (c : ℝ) ≤ 2 := by exact_mod_cast hc2
  have hpow : (4 : ℝ) ^ (N + L) = 4 ^ N * 4 ^ L := pow_add 4 N L
  rw [hpow] at hF1 hF2
  set P : ℝ := 4 ^ N * 4 ^ L with hP
  have hPpos : 0 < P := by positivity
  have hFP : F = ⌊P * x⌋ := by rw [hF, hpow]
  rw [← hFP] at hF1 hF2
  have hfrac : (3 * (⌊(4 : ℝ) ^ N * x⌋ : ℝ) + c) / (3 * 4 ^ N) = (3 * F + c) / (3 * P) := by
    rw [div_eq_div_iff (by positivity) (by positivity), hP]
    linear_combination (-(3 * (4 : ℝ) ^ N)) * hLR
  have e : x - (3 * F + c) / (3 * P) = (3 * (P * x) - 3 * F - c) / (3 * P) := by
    field_simp
    ring
  rw [hpow, hfrac, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 * P),
    div_le_div_iff₀ (by positivity) hPpos]
  have hb : |3 * (P * x) - 3 * F - c| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith
  nlinarith

/-- **Burst law for the drift of `π`.**  For all large `N`, a window on which the parity drift of
`π` moves at full speed has length at most `K N`. -/
theorem exists_burst_bound_pi :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |drift Real.pi (N + L) - drift Real.pi N| = L → (L : ℝ) ≤ K * N := by
  obtain ⟨K₀, hK₀⟩ := BeukersZetaTwo.exists_not_liouvilleWith_pi
  set K : ℝ := max K₀ 0 + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  refine ⟨K, ?_⟩
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_forall, not_le] at hcon
  -- each bad window gives a good rational approximation
  apply hK₀ (K + 1) (by rw [hK]; linarith [le_max_left K₀ 0])
  refine ⟨3 ^ (K + 1), ?_⟩
  rw [frequently_atTop] at hcon ⊢
  intro A
  obtain ⟨N, hNA, L, hL, hLK⟩ := hcon (A + 1)
  have hN1 : 1 ≤ N := by omega
  rw [drift_add] at hL
  have hbit : ∀ i, |binDigit Real.pi (2 * (N + i) + 1) - binDigit Real.pi (2 * (N + i) + 2)| ≤ 1 :=
    fun i => by
      have := abs_binDigit_sub_le Real.pi (2 * (N + i) + 1) (2 * (N + i) + 2)
      exact_mod_cast this
  obtain ⟨c, hc1, hc2, hrun⟩ : ∃ c : ℤ, 1 ≤ c ∧ c ≤ 2 ∧
      ∀ i < L, quatDigit Real.pi (N + i + 1) = c := by
    rcases all_eq_of_abs_sum_eq hbit hL with h | h
    · refine ⟨2, by norm_num, le_rfl, fun i hi => ?_⟩
      have := h i hi
      rw [binDigit_sub_binDigit_eq] at this
      split_ifs at this with h2 h1 <;> omega
    · refine ⟨1, le_rfl, by norm_num, fun i hi => ?_⟩
      have := h i hi
      rw [binDigit_sub_binDigit_eq] at this
      split_ifs at this with h2 h1 <;> omega
  have happrox := abs_sub_le_of_quatDigit_run hc1 hc2 hrun
  set q : ℕ := 3 * 4 ^ N with hq
  set m : ℤ := 3 * ⌊(4 : ℝ) ^ N * Real.pi⌋ + c with hm
  refine ⟨q, by rw [hq]; have := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := N); omega,
    m, ?_, ?_⟩
  · intro h
    have hirr : Irrational Real.pi := irrational_pi
    exact hirr ⟨(m : ℚ) / q, by rw [h]; push_cast; ring⟩
  · have hqR : (q : ℝ) = 3 * 4 ^ N := by rw [hq]; push_cast; ring
    have hmR : (m : ℝ) = 3 * ⌊(4 : ℝ) ^ N * Real.pi⌋ + c := by rw [hm]; push_cast; ring
    rw [hqR, hmR]
    refine lt_of_le_of_lt happrox ?_
    -- `4^{-(N+L)} < 3^{K+1}/(3·4ᴺ)^{K+1}` because `L > K N`
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h4 : (0 : ℝ) < 4 ^ N := by positivity
    have hrhs : (3 : ℝ) ^ (K + 1) / (3 * 4 ^ N) ^ (K + 1) = 1 / ((4 : ℝ) ^ N) ^ (K + 1) := by
      rw [Real.mul_rpow (by norm_num) h4.le]
      have : (3 : ℝ) ^ (K + 1) ≠ 0 := by positivity
      field_simp
    rw [hrhs, one_div_lt_one_div (by positivity) (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    push_cast
    nlinarith

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
