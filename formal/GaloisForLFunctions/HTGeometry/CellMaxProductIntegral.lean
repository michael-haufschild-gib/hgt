import GaloisForLFunctions.HTGeometry.CellMaxDiscretisation

/-!
# Discretisation of a product integral by cell maxima of one factor

`exists_cell_max_integral_le` takes the maximum of the whole integrand on each cell, which throws
away everything the other factor knows.  When the integrand is a product `G·H` with `H ≥ 0` — a
slowly varying envelope times a mean square, say — only the envelope should be frozen:

```text
∫_a^{a+mΔ} G·H  ≤  ∑_{k < m} (max_{cell k} G) · ∫_{cell k} H .
```

The sum on the right is an `ℓ¹` aggregate of cell maxima against the cell masses of `H`, not a
global maximum times a length.  That is the difference between charging the envelope's largest
value to the whole range and charging it cell by cell.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory intervalIntegral

/-- **Discretisation of a product integral by the cell maxima of one factor.**  The maximisers are
produced by the statement, so a bound on the aggregate of the envelope over the cells can consume
them. -/
theorem exists_cell_max_mul_integral_le {G H : ℝ → ℝ} (hG : Continuous G) (hH : Continuous H)
    (hH0 : ∀ t, 0 ≤ H t) (a Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ) :
    ∃ c : ℕ → ℝ, (∀ k, k < m → c k ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
      ∧ (∫ t in a..(a + (m : ℝ) * Δ), G t * H t)
        ≤ ∑ k ∈ Finset.range m,
            G (c k) * ∫ t in (a + (k : ℝ) * Δ)..(a + ((k : ℝ) + 1) * Δ), H t := by
  classical
  have hcell : ∀ k : ℕ, ∃ x ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ),
      IsMaxOn G (Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ)) x := by
    intro k
    refine (isCompact_Icc).exists_isMaxOn ?_ (hG.continuousOn)
    refine Set.nonempty_Icc.2 ?_
    have : (0 : ℝ) ≤ Δ := hΔ.le
    nlinarith [this]
  choose c hcmem hcmax using hcell
  refine ⟨c, fun k _ => hcmem k, ?_⟩
  set g : ℕ → ℝ := fun k => a + (k : ℝ) * Δ with hg
  have hadj : ∀ k < m, IntervalIntegrable (fun t => G t * H t) volume (g k) (g (k + 1)) :=
    fun k _ => ((hG.mul hH).intervalIntegrable _ _)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hadj
  have hg0 : g 0 = a := by rw [hg]; simp
  have hgm : g m = a + (m : ℝ) * Δ := by rw [hg]
  rw [hg0, hgm] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hgk : g (k + 1) = a + ((k : ℝ) + 1) * Δ := by
    simp only [hg]
    push_cast
    ring
  have hle : g k ≤ g (k + 1) := by
    simp only [hg]
    push_cast
    nlinarith [hΔ.le]
  have hbound : ∀ x ∈ Set.Icc (g k) (g (k + 1)), G x * H x ≤ G (c k) * H x := by
    intro x hx
    rw [hgk] at hx
    exact mul_le_mul_of_nonneg_right (hcmax k hx) (hH0 x)
  have hmono : (∫ t in (g k)..(g (k + 1)), G t * H t)
      ≤ ∫ t in (g k)..(g (k + 1)), G (c k) * H t :=
    intervalIntegral.integral_mono_on hle ((hG.mul hH).intervalIntegrable _ _)
      ((continuous_const.mul hH).intervalIntegrable _ _) hbound
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, hgk]

end GaloisForLFunctions.HTGeometry
end
