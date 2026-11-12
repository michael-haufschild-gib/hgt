import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EverySparseConfigurationIsRealized

/-!
# Infinitely many strict fake zeros on a vertical line

A point of a prescribed configuration is a fake zero in the strict sense only if `ζ` does not
vanish there.  The heights of a sparse configuration can be chosen freely in the intervals
`[(j+1)^A, (j+1)^A + 1]`, and `ζ` does not vanish identically on a vertical segment
(`exists_riemannZeta_ne_zero_on_segment`: the zeros of the entire function `(s − 1) ζ(s)` are
isolated).

**Theorem** (`exists_isEdit_fake_with_strict_zeros_on_a_line`).  For `1/2 < σ`,
`σ + 1/(2A) < 14/15` and `β ∈ (σ + 1/(2A), 1)` there are points `ρ_j` on the line `Re s = σ`,
infinitely many, with `ζ(ρ_j) ≠ 0` for every `j`, and a two-sided edit of the rational primes
that is an integer-norm fake at `β` whose fake zeros right of the line are exactly the points
`ρ_j`, `ρ̄_j`.  Every one of them is a zero of `ζ_B` and not of `ζ`.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

/-- `ζ` does not vanish identically on a vertical segment. -/
theorem exists_riemannZeta_ne_zero_on_segment {σ : ℝ} (hσ : σ ≠ 1) {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, a ≤ t ∧ t ≤ b ∧ riemannZeta (⟨σ, t⟩ : ℂ) ≠ 0 := by
  by_contra hall
  push Not at hall
  -- the entire function `(s − 1) ζ(s)` vanishes on the segment
  have hseg : ∀ t : ℝ, a ≤ t → t ≤ b → zetaResidueUnit (⟨σ, t⟩ : ℂ) = 0 := by
    intro t hat htb
    have hne : (⟨σ, t⟩ : ℂ) ≠ 1 := fun h => hσ (by simpa using congrArg Complex.re h)
    rw [zetaResidueUnit_of_ne hne, hall t hat htb, mul_zero]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = ⟨σ, (a + b) / 2⟩ := ⟨_, rfl⟩
  rcases (analyticAt_zetaResidueUnit z₀).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · -- zero near the midpoint: zero everywhere
    have hglob := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (f := zetaResidueUnit) (U := Set.univ) (fun z _ => analyticAt_zetaResidueUnit z)
      isPreconnected_univ (Set.mem_univ z₀) h0
    have h2 : zetaResidueUnit 2 = 0 := hglob (Set.mem_univ 2)
    rw [zetaResidueUnit_of_ne (by norm_num)] at h2
    have h3 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h3 h
  · -- an isolated zero at the midpoint: a nearby point of the segment is not a zero
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨ε, hε, hball⟩ := hne
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 2) ((b - a) / 4) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by linarith)
    have hδ1 : δ ≤ ε / 2 := by rw [hδ]; exact min_le_left _ _
    have hδ2 : δ ≤ (b - a) / 4 := by rw [hδ]; exact min_le_right _ _
    have hz : (⟨σ, (a + b) / 2 + δ⟩ : ℂ) ≠ z₀ := by
      rw [hz₀]
      intro h
      have h' := congrArg Complex.im h
      simp only [add_eq_left] at h'
      linarith
    have hdist : dist (⟨σ, (a + b) / 2 + δ⟩ : ℂ) z₀ < ε := by
      rw [hz₀, Complex.dist_eq]
      have h1 : (⟨σ, (a + b) / 2 + δ⟩ : ℂ) - ⟨σ, (a + b) / 2⟩ = ⟨0, δ⟩ := by
        apply Complex.ext <;> simp
      rw [h1]
      have h2 : ‖(⟨0, δ⟩ : ℂ)‖ ≤ |(0 : ℝ)| + |δ| := Complex.norm_le_abs_re_add_abs_im _
      rw [abs_zero, zero_add, abs_of_pos hδ0] at h2
      linarith
    exact hball hdist hz (hseg _ (by linarith) (by linarith))

/-- **Infinitely many strict fake zeros on one vertical line.**  There are infinitely many
points `ρ_j` on the line `Re s = σ`, none a zero of `ζ`, and a two-sided edit of the rational
primes that is an integer-norm fake at `β` with fake zeros exactly the points `ρ_j`, `ρ̄_j`. -/
theorem exists_isEdit_fake_with_strict_zeros_on_a_line {σ A : ℝ} (hσ : 1 / 2 < σ) (hA : 0 < A)
    (hroom : σ + 1 / (2 * A) < 14 / 15) {β : ℝ} (hβ : σ + 1 / (2 * A) < β) (hβ1 : β < 1) :
    ∃ (ρ : ℕ → ℂ) (e : ℕ → ℤ), (∀ j, (ρ j).re = σ) ∧ (∀ j, riemannZeta (ρ j) ≠ 0) ∧
      (Set.range ρ).Infinite ∧ IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β ∧
      HasFakeZeroSet (editSystem e) {z : ℂ | ∃ j, z = ρ j ∨ z = (starRingEnd ℂ) (ρ j)} := by
  have hσ1 : σ ≠ 1 := by
    have h1 : 0 < 1 / (2 * A) := one_div_pos.mpr (by linarith)
    intro h
    linarith
  have hex : ∀ j : ℕ, ∃ t : ℝ, ((j : ℝ) + 1) ^ A ≤ t ∧ t ≤ ((j : ℝ) + 1) ^ A + 1 ∧
      riemannZeta (⟨σ, t⟩ : ℂ) ≠ 0 := fun j =>
    exists_riemannZeta_ne_zero_on_segment hσ1 (by linarith)
  choose t ht1 ht2 htζ using hex
  have hpos : ∀ j, 0 ≤ t j := fun j =>
    le_trans (Real.rpow_nonneg (by positivity) _) (ht1 j)
  have hcfg : IsSparseConfig (fun j => (⟨σ, t j⟩ : ℂ)) σ A :=
    { half := fun _ => hσ
      le := fun _ => le_rfl
      pos := hA
      room := hroom
      height := fun j => by
        show ((j : ℝ) + 1) ^ A ≤ |t j|
        rw [abs_of_nonneg (hpos j)]
        exact ht1 j }
  obtain ⟨e, he, hfake, -, hset⟩ := hcfg.exists_isEdit_fake_sparse ⟨0, htζ 0⟩ hβ hβ1
  refine ⟨fun j => (⟨σ, t j⟩ : ℂ), e, fun _ => rfl, htζ, ?_, he, hfake, hset⟩
  -- the heights are unbounded
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨j, hj⟩ := exists_nat_gt M
  have h1 : t j ≤ M := hM ⟨_, ⟨j, rfl⟩, rfl⟩
  have h2 : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ A := by
    have h3 := Real.rpow_le_rpow_of_exponent_le
      (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)] : (1 : ℝ) ≤ (j : ℝ) + 1) hcfg.one_lt.le
    rwa [Real.rpow_one] at h3
  linarith [ht1 j]

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
