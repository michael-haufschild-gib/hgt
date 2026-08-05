import GaloisForLFunctions.HTGeometry.ClockAnalyticWienerScale

/-!
# Wiener-summable sequences exist at every analytic scale

Wiener summability at scale `ρ` — summability of `|g k| exp (ρ |k|)` over the integers — is the
standing hypothesis of the analytic Wiener scale, and nothing produced it.

Every finitely supported sequence has it at every scale, and the class is closed under the linear
operations and under domination.  The substantive realization is geometric: a sequence decaying
like `r^{|k|}` is Wiener summable at every scale `ρ` with `r e^ρ < 1`, and that is sharp in the
sense that the weighted terms are then exactly a two-sided geometric series.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Closure properties -/

/-- The zero sequence is Wiener summable at every scale. -/
theorem wienerSummable_zero (ρ : ℝ) : WienerSummable ρ (fun _ : ℤ => (0 : ℝ)) := by
  simp [WienerSummable]

/-- Domination in modulus transfers Wiener summability. -/
theorem wienerSummable_of_abs_le {ρ : ℝ} {f g : ℤ → ℝ} (hf : WienerSummable ρ f)
    (h : ∀ k, |g k| ≤ |f k|) : WienerSummable ρ g := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hf
  exact mul_le_mul_of_nonneg_right (h k) (Real.exp_pos _).le

/-- A sequence supported on a finite set is Wiener summable at every scale. -/
theorem wienerSummable_of_support_subset {ρ : ℝ} {g : ℤ → ℝ} {s : Finset ℤ}
    (h : ∀ k ∉ s, g k = 0) : WienerSummable ρ g :=
  summable_of_ne_finset_zero (s := s) fun k hk => by
    rw [h k hk, abs_zero, zero_mul]

/-- A sequence concentrated at one index is Wiener summable at every scale. -/
theorem wienerSummable_single (ρ : ℝ) (k₀ : ℤ) (c : ℝ) :
    WienerSummable ρ (fun k => if k = k₀ then c else 0) := by
  refine wienerSummable_of_support_subset (s := {k₀}) fun k hk => ?_
  rw [Finset.mem_singleton] at hk
  simp [hk]

/-- Wiener summability is closed under addition. -/
theorem WienerSummable.add {ρ : ℝ} {f g : ℤ → ℝ} (hf : WienerSummable ρ f)
    (hg : WienerSummable ρ g) : WienerSummable ρ (fun k => f k + g k) := by
  have hsum : Summable fun k : ℤ =>
      |f k| * Real.exp (ρ * |(k : ℝ)|) + |g k| * Real.exp (ρ * |(k : ℝ)|) :=
    Summable.add hf hg
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
  have habs : |f k + g k| ≤ |f k| + |g k| := abs_add_le _ _
  have hmul := mul_le_mul_of_nonneg_right habs (Real.exp_pos (ρ * |(k : ℝ)|)).le
  rw [add_mul] at hmul
  exact hmul

/-- Wiener summability is closed under scalar multiples. -/
theorem WienerSummable.const_mul {ρ : ℝ} {g : ℤ → ℝ} (hg : WienerSummable ρ g) (c : ℝ) :
    WienerSummable ρ (fun k => c * g k) :=
  (hg.mul_left |c|).congr fun k => by rw [abs_mul]; ring

/-- Wiener summability is closed under negation. -/
theorem WienerSummable.neg {ρ : ℝ} {g : ℤ → ℝ} (hg : WienerSummable ρ g) :
    WienerSummable ρ (fun k => -g k) :=
  wienerSummable_of_abs_le hg fun k => by rw [abs_neg]

/-! ## The geometric realization -/

/-- A two-sided geometric series with ratio below one is summable. -/
theorem summable_geometric_natAbs {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℤ => q ^ k.natAbs := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_geometric_of_lt_one hq0 hq1
  · simpa using summable_geometric_of_lt_one hq0 hq1

/-- **Geometric decay is Wiener summable below the reciprocal weight.**  The weighted terms of
`r^{|k|}` are exactly the two-sided geometric series of ratio `r e^ρ`. -/
theorem wienerSummable_geometric {ρ r : ℝ} (hr : 0 ≤ r) (hrρ : r * Real.exp ρ < 1) :
    WienerSummable ρ (fun k : ℤ => r ^ k.natAbs) := by
  have hterm : ∀ k : ℤ,
      |r ^ k.natAbs| * Real.exp (ρ * |(k : ℝ)|) = (r * Real.exp ρ) ^ k.natAbs := by
    intro k
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
    rw [abs_of_nonneg (pow_nonneg hr _), habs, mul_comm ρ ((k.natAbs : ℝ)),
      Real.exp_nat_mul, mul_pow]
  refine (summable_geometric_natAbs (q := r * Real.exp ρ) ?_ hrρ).congr fun k => (hterm k).symm
  exact mul_nonneg hr (Real.exp_pos _).le

/-- The geometric realization is nonzero everywhere, so the analytic Wiener scale is carried by a
sequence with full support. -/
theorem exists_wienerSummable_ne_zero (ρ : ℝ) :
    ∃ g : ℤ → ℝ, WienerSummable ρ g ∧ ∀ k, g k ≠ 0 := by
  refine ⟨fun k => (Real.exp (-ρ) / 2) ^ k.natAbs, ?_, fun k => ?_⟩
  · refine wienerSummable_geometric (by positivity) ?_
    have hpos : (0 : ℝ) < Real.exp ρ := Real.exp_pos _
    rw [div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    norm_num
  · exact pow_ne_zero _ (by positivity)

end

end GaloisForLFunctions.HTGeometry
