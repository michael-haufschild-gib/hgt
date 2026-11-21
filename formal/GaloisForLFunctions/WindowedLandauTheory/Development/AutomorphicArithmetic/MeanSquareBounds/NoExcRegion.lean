import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplex

/-! Excluding the possible real exception in the logarithmic Dirichlet region. -/

namespace QH

theorem zero_free_of_noExc (c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (lam : ℝ), 1 ≤ lam → Real.log N ≤ lam →
      (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) → ∀ ρ : ℂ, ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
        ρ.re ≤ 1 - c / (lam + Real.log (|ρ.im| + 3)) := by
  obtain ⟨c1, hc1, H⟩ := WindowedLandauTheory.ZeroFreeDirichlet.zFRDirichlet
  refine ⟨min c1 c₀, lt_min hc1 hc₀, ?_⟩
  intro N _ χ lam hlam hN hex ρ r1 hz
  by_contra hlt
  have hlt := not_le.mp hlt
  have ht := abs_nonneg ρ.im
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlA : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
  have hAB : Real.log (|ρ.im| + 2) ≤ Real.log (|ρ.im| + 3) := Real.log_le_log (by linarith) (by linarith)
  have hm0 : 0 < min c1 c₀ := lt_min hc1 hc₀
  have hreg : WindowedLandauTheory.ZeroFreeDirichlet.InRegion c1 N ρ := by
    unfold WindowedLandauTheory.ZeroFreeDirichlet.InRegion
    rw [Real.log_mul (by linarith) (by linarith)]
    have : min c1 c₀ / (lam + Real.log (|ρ.im| + 3)) ≤ c1 / (Real.log N + Real.log (|ρ.im| + 2)) :=
      div_le_div₀ hc1.le (min_le_left _ _) (by linarith) (by linarith)
    linarith
  have hLZ : WindowedLandauTheory.ZeroFreeDirichlet.IsLZero χ ρ := by
    refine ⟨Or.inr fun h => ?_, hz⟩
    rw [h, Complex.one_re] at r1
    exact lt_irrefl _ r1
  obtain ⟨hsq, hne, him, -⟩ := H N χ ρ hreg hLZ
  have hρ : ((ρ.re : ℝ) : ℂ) = ρ := Complex.ext (by simp) (by simp [him])
  have h2 : min c1 c₀ / (lam + Real.log (|ρ.im| + 3)) ≤ c₀ :=
    (div_le_self hm0.le (by linarith)).trans (min_le_right _ _)
  refine hex hsq hne ρ.re (by linarith) r1 ?_
  rw [hρ]; exact hz

end QH
