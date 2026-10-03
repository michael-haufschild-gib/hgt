import GaloisForLFunctions.HTGeometry.BinaryParityDriftDiophantineBarrier

/-!
# The BBP shape cannot decide the parity drift

The Bailey–Borwein–Plouffe series writes `π = Σ_k 16^{−k} a(k)/D(k)` with
`D(k) = (8k+1)(8k+4)(8k+5)(8k+6)` and `a(k) = 120k² + 151k + 47`.

* `exists_bbpDigits`: every real `x` with `|x| ≤ 1312/120` has an expansion
  `x = Σ_k 16^{−k} a(k)/D(k)` with integers `|a(k)| ≤ 1312`.  The greedy remainders stay below
  `1312 w_k` because consecutive weights satisfy `w_k ≤ 2624 w_{k+1}`
  (`bbpDen_succ_le : D(k+1) ≤ 164 D(k)`).
* `exists_bbpShape_drift_not_liouvilleWith_not_mem`: for `|θ| ≤ 2/5` and every countable set `C`
  there is `x ∉ C` of BBP shape with bounded numerators, parity drift `θ`, and irrationality
  exponent at most `7`.

A proof or a refutation of the Parity-Drift Hypothesis for `π` therefore cannot rest on the BBP
denominators, on the size of the numerators, on Diophantine or algebraic-independence data, or on
any combination of them.  It must use the arithmetic of the specific numerators `120k² + 151k + 47`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

/-- The BBP denominator `D(k) = (8k+1)(8k+4)(8k+5)(8k+6)`. -/
def bbpDen (k : ℕ) : ℕ := (8 * k + 1) * (8 * k + 4) * (8 * k + 5) * (8 * k + 6)

/-- The BBP weight `w_k = 16^{−k}/D(k)`. -/
noncomputable def bbpWeight (k : ℕ) : ℝ := 1 / ((16 : ℝ) ^ k * bbpDen k)

theorem bbpDen_pos (k : ℕ) : 0 < bbpDen k := by unfold bbpDen; positivity

theorem bbpWeight_pos (k : ℕ) : 0 < bbpWeight k := by
  unfold bbpWeight; have := bbpDen_pos k; positivity

/-- `D(k+1) ≤ 164 D(k)`: each factor `(8k+8+j)/(8k+j)` is largest at `k = 0`. -/
theorem bbpDen_succ_le (k : ℕ) : bbpDen (k + 1) ≤ 164 * bbpDen k := by
  unfold bbpDen
  have h1 : 8 * (k + 1) + 1 ≤ 9 * (8 * k + 1) := by omega
  have h4 : 8 * (k + 1) + 4 ≤ 3 * (8 * k + 4) := by omega
  have h56 : (8 * (k + 1) + 5) * (8 * (k + 1) + 6) * 30 ≤ 182 * ((8 * k + 5) * (8 * k + 6)) := by
    nlinarith
  generalize hP : (8 * (k + 1) + 5) * (8 * (k + 1) + 6) = P at h56
  generalize hQ : (8 * k + 5) * (8 * k + 6) = Q at h56
  have h27 : 27 * P ≤ 164 * Q := by omega
  calc (8 * (k + 1) + 1) * (8 * (k + 1) + 4) * (8 * (k + 1) + 5) * (8 * (k + 1) + 6)
      = (8 * (k + 1) + 1) * (8 * (k + 1) + 4) * P := by rw [← hP]; ring
    _ ≤ (9 * (8 * k + 1)) * (3 * (8 * k + 4)) * P := by gcongr
    _ = (8 * k + 1) * (8 * k + 4) * (27 * P) := by ring
    _ ≤ (8 * k + 1) * (8 * k + 4) * (164 * Q) := Nat.mul_le_mul_left _ h27
    _ = 164 * ((8 * k + 1) * (8 * k + 4) * (8 * k + 5) * (8 * k + 6)) := by rw [← hQ]; ring

theorem bbpWeight_le_succ (k : ℕ) : bbpWeight k ≤ 2624 * bbpWeight (k + 1) := by
  unfold bbpWeight
  have hD := bbpDen_pos k
  have hD1 := bbpDen_pos (k + 1)
  have hle : (bbpDen (k + 1) : ℝ) ≤ 164 * bbpDen k := by exact_mod_cast bbpDen_succ_le k
  rw [div_le_iff₀ (by positivity), pow_succ]
  field_simp
  nlinarith [pow_pos (show (0 : ℝ) < 16 by norm_num) k]

theorem bbpWeight_le_pow (k : ℕ) : bbpWeight k ≤ (1 / 16 : ℝ) ^ k := by
  unfold bbpWeight
  have hD : (1 : ℝ) ≤ bbpDen k := by exact_mod_cast bbpDen_pos k
  rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (show (0 : ℝ) < 16 by norm_num) k]

/-- The greedy remainders. -/
noncomputable def bbpRem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => bbpRem x k - (round (bbpRem x k / bbpWeight k) : ℝ) * bbpWeight k

/-- The greedy digits `a(k) = round(r_k / w_k)`. -/
noncomputable def bbpDigit (x : ℝ) (k : ℕ) : ℤ := round (bbpRem x k / bbpWeight k)

theorem abs_bbpRem_le {x : ℝ} (hx : |x| ≤ 1312 * bbpWeight 0) (k : ℕ) :
    |bbpRem x k| ≤ 1312 * bbpWeight k := by
  induction k with
  | zero => simpa [bbpRem] using hx
  | succ k _ =>
    have hw := bbpWeight_pos k
    have h1 : |bbpRem x (k + 1)| ≤ bbpWeight k / 2 := by
      show |bbpRem x k - (round (bbpRem x k / bbpWeight k) : ℝ) * bbpWeight k| ≤ _
      have h := abs_sub_round (bbpRem x k / bbpWeight k)
      have e : bbpRem x k - (round (bbpRem x k / bbpWeight k) : ℝ) * bbpWeight k =
          (bbpRem x k / bbpWeight k - round (bbpRem x k / bbpWeight k)) * bbpWeight k := by
        field_simp
      rw [e, abs_mul, abs_of_pos hw]
      nlinarith
    have := bbpWeight_le_succ k
    linarith

theorem abs_bbpDigit_le {x : ℝ} (hx : |x| ≤ 1312 * bbpWeight 0) (k : ℕ) :
    |bbpDigit x k| ≤ 1312 := by
  have hw := bbpWeight_pos k
  have hr : |bbpRem x k / bbpWeight k| ≤ 1312 := by
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw]
    exact abs_bbpRem_le hx k
  have h := abs_sub_round (bbpRem x k / bbpWeight k)
  have : |(bbpDigit x k : ℝ)| < 1313 := by
    unfold bbpDigit
    calc |(round (bbpRem x k / bbpWeight k) : ℝ)|
        ≤ |bbpRem x k / bbpWeight k| + |bbpRem x k / bbpWeight k -
            (round (bbpRem x k / bbpWeight k) : ℝ)| := by
          have := abs_sub_abs_le_abs_sub (bbpRem x k / bbpWeight k)
            ((round (bbpRem x k / bbpWeight k) : ℝ))
          rw [abs_sub_comm (bbpRem x k / bbpWeight k)] at h
          linarith [abs_sub_abs_le_abs_sub ((round (bbpRem x k / bbpWeight k) : ℝ))
            (bbpRem x k / bbpWeight k), abs_sub_comm ((round (bbpRem x k / bbpWeight k) : ℝ))
            (bbpRem x k / bbpWeight k)]
      _ < 1313 := by linarith
  have h' : |bbpDigit x k| < 1313 := by exact_mod_cast this
  omega

theorem sum_bbpDigit (x : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (bbpDigit x k : ℝ) * bbpWeight k = x - bbpRem x n := by
  induction n with
  | zero => simp [bbpRem]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [bbpRem, bbpDigit]
    ring

/-- **BBP numeration.**  Every `x` with `|x| ≤ 1312/120` is `Σ_k 16^{−k} a(k)/D(k)` with integers
`|a(k)| ≤ 1312`. -/
theorem exists_bbpDigits {x : ℝ} (hx : |x| ≤ 1312 / 120) :
    ∃ a : ℕ → ℤ, (∀ k, |a k| ≤ 1312) ∧
      HasSum (fun k => (a k : ℝ) / ((16 : ℝ) ^ k * bbpDen k)) x := by
  have hx' : |x| ≤ 1312 * bbpWeight 0 := by
    simp only [bbpWeight, bbpDen]; norm_num; linarith
  refine ⟨bbpDigit x, abs_bbpDigit_le hx', ?_⟩
  have hterm : ∀ k, (bbpDigit x k : ℝ) / ((16 : ℝ) ^ k * bbpDen k) =
      (bbpDigit x k : ℝ) * bbpWeight k := fun k => by unfold bbpWeight; ring
  simp_rw [hterm]
  have hsum : Summable (fun k => (bbpDigit x k : ℝ) * bbpWeight k) := by
    refine Summable.of_norm_bounded (g := fun k => 1312 * (1 / 16 : ℝ) ^ k)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (bbpWeight_pos k)]
    have h1 : |(bbpDigit x k : ℝ)| ≤ 1312 := by exact_mod_cast abs_bbpDigit_le hx' k
    exact mul_le_mul h1 (bbpWeight_le_pow k) (bbpWeight_pos k).le (by norm_num)
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [sum_bbpDigit]
  have hb : Tendsto (fun k : ℕ => 1312 * (1 / 16 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num)).const_mul 1312
  have hrem : Tendsto (bbpRem x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) hb
    rw [Real.norm_eq_abs]
    exact (abs_bbpRem_le hx' k).trans (mul_le_mul_of_nonneg_left (bbpWeight_le_pow k)
      (by norm_num))
  simpa using (tendsto_const_nhds (x := x)).sub hrem

/-- **The BBP shape cannot decide the parity drift.**  For `|θ| ≤ 2/5` and every countable set `C`
there is `x ∉ C` with an expansion `x = Σ_k 16^{−k} a(k)/((8k+1)(8k+4)(8k+5)(8k+6))`, integers
`|a(k)| ≤ 1312`, parity drift `D_x(N)/N → θ`, and irrationality exponent at most `7`. -/
theorem exists_bbpShape_drift_not_liouvilleWith_not_mem {θ : ℝ} (hθ : |θ| ≤ 2 / 5) {C : Set ℝ}
    (hC : C.Countable) :
    ∃ x : ℝ, x ∉ C ∧ Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 θ) ∧
      (∀ p > (7 : ℝ), ¬ LiouvilleWith p x) ∧
      ∃ a : ℕ → ℤ, (∀ k, |a k| ≤ 1312) ∧
        HasSum (fun k => (a k : ℝ) / ((16 : ℝ) ^ k * bbpDen k)) x := by
  have hne : (MeasureTheory.ae (digitMeasure hθ)).NeBot :=
    MeasureTheory.ae_neBot.mpr (MeasureTheory.IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, h1, h2, h3⟩ := ((ae_ofDigitSeq_not_mem hθ hC).and
    ((ae_tendsto_drift hθ).and (ae_ofDigitSeq_not_liouvilleWith hθ))).exists
  have hmem := ofDigitSeq_mem_Ico ω
  refine ⟨ofDigitSeq ω, h1, h2, h3, exists_bbpDigits ?_⟩
  rw [abs_of_nonneg hmem.1]
  linarith [hmem.2]

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
