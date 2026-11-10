import GaloisForLFunctions.InfiniteRankPurityTheory.IntegralTraceClassModulesOverTheIntegersAreTate
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour

/-!
# No trace-class family of zeros is integral

In finite rank a characteristic polynomial is irreducible over `ℚ` exactly when no proper subfamily of
its roots has rational power sums. The infinite-rank form for the zeros of `ξ`: a family of zeros
with weights `b_i` is **integral** when its traces `Σ_i b_i n^{ρ_i}` are integers at all large `n`.

**Theorem.** A family of distinct zeros of `ξ`, of trace class of order one and with real parts
forming a set without infinite ascending chain, is integral only if all its weights vanish
(`eq_zero_of_integral_trace_of_xi_zeros`). This covers

* every finite family of zeros, with any weights (`eq_zero_of_integral_trace_of_finite_xi_zeros`);
* every trace-class family of zeros on one vertical line, in particular of critical zeros
  (`eq_zero_of_integral_trace_of_xi_zeros_on_line`).

The reason is Kronecker's theorem over `ℤ`: an integral trace-class module is a sum of Tate twists,
and no zero is an integer. So the zero motive has no integral constituent of trace class: it is
irreducible over `ℤ` in the only sense in which finite pieces could split off.
-/

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

variable {ι : Type*}

/-- A finite family of modes has well-founded weights. -/
theorem weightsWellFounded_of_finite [Finite ι] (ρ : ι → ℂ) : WeightsWellFounded ρ := by
  intro S hS hne
  exact Set.exists_max_image S id ((Set.finite_range _).subset hS) hne

/-- Modes on one vertical line have well-founded weights. -/
theorem weightsWellFounded_of_re_eq {ρ : ι → ℂ} {σ : ℝ} (h : ∀ i, (ρ i).re = σ) :
    WeightsWellFounded ρ := by
  intro S hS hne
  obtain ⟨τ, hτ⟩ := hne
  refine ⟨τ, hτ, fun υ hυ => ?_⟩
  obtain ⟨i, hi⟩ := hS hτ
  obtain ⟨j, hj⟩ := hS hυ
  simp only at hi hj
  rw [← hi, ← hj, h i, h j]

/-- **No integral trace-class module lives in the open strip.** -/
theorem eq_zero_of_integral_trace_in_open_strip {b ρ : ι → ℂ} (hρ : Function.Injective ρ)
    (hwf : WeightsWellFounded ρ) (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖)) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) : ∀ i, b i = 0 := by
  intro i
  by_contra hbi
  obtain ⟨A, ⟨j, hj⟩, hmax⟩ := hwf (Set.range fun i => (ρ i).re) subset_rfl ⟨_, i, rfl⟩
  simp only at hj
  have hA1 : A < 1 := by
    rw [← hj]
    exact (hstrip j).2
  have hA : ∀ k, (ρ k).re ≤ A := fun k => hmax _ ⟨k, rfl⟩
  have h0 := not_visible_in_open_strip hρ hwf hA hA1 hb hint i hbi
  have hpos := (hstrip i).1
  rw [h0] at hpos
  simp at hpos

/-- **No trace-class family of zeros of `ξ` is integral.** -/
theorem eq_zero_of_integral_trace_of_xi_zeros {b ρ : ι → ℂ} (hρ : Function.Injective ρ)
    (hwf : WeightsWellFounded ρ) (hzero : ∀ i, xi (ρ i) = 0)
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖)) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) : ∀ i, b i = 0 :=
  eq_zero_of_integral_trace_in_open_strip hρ hwf
    (fun i => ⟨re_pos_of_xi_eq_zero (hzero i), re_lt_one_of_xi_eq_zero (hzero i)⟩) hb hint

/-- **No finite family of zeros of `ξ` has integral traces**, whatever the weights. -/
theorem eq_zero_of_integral_trace_of_finite_xi_zeros [Finite ι] {b ρ : ι → ℂ}
    (hρ : Function.Injective ρ) (hzero : ∀ i, xi (ρ i) = 0) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) : ∀ i, b i = 0 :=
  eq_zero_of_integral_trace_of_xi_zeros hρ (weightsWellFounded_of_finite ρ) hzero
    (summable_of_hasFiniteSupport (Set.toFinite _)) hint

/-- **No trace-class family of zeros on one vertical line has integral traces**; in particular no
trace-class family of critical zeros. -/
theorem eq_zero_of_integral_trace_of_xi_zeros_on_line {b ρ : ι → ℂ} {σ : ℝ}
    (hρ : Function.Injective ρ) (hline : ∀ i, (ρ i).re = σ) (hzero : ∀ i, xi (ρ i) = 0)
    (hb : Summable fun i => ‖b i‖ * (1 + ‖ρ i‖)) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) : ∀ i, b i = 0 :=
  eq_zero_of_integral_trace_of_xi_zeros hρ (weightsWellFounded_of_re_eq hline) hzero hb hint

end GaloisForLFunctions.InfiniteRankPurityTheory
