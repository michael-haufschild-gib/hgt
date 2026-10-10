import GaloisForLFunctions.RHTower.JointAncestryRouteCapstone
import GaloisForLFunctions.RHTower.VonMangoldtMinusOneAbscissa
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Without a chain, the JAS abscissa bounds the zeros

The off-line Xi zeros either form a chain with no farthest zero (`JasOffLineChain`), or RH holds,
or a farthest zero `ρ₀` exists.  A farthest zero forces `σ* ≥ 1 + |Re ρ₀ − ½|`, so

`Re ρ ≤ ½ + (σ* − 1)` for every Xi zero `ρ` whenever there is no chain and RH fails.

Consequences of the absence of a chain alone:

* a zero-free half-plane `Re s > ½ + α` with `α < ½` (the farthest zero lies inside the open strip);
* a power-saving prime number theorem `|ψ(t) − t| ≤ C t^θ` with `θ < 1` (generalized von Koch);
* if moreover the aggregate is positive semidefinite at some `σ ≥ 1`, every Xi zero satisfies
  `Re ρ ≤ σ − ½`.

So the no-chain half of the route capstone `RH ⟺ JasDressedPSD 1 ∧ ¬ JasOffLineChain` already
contains a zero-free half-plane strictly inside the critical strip.
-/

namespace RHTower

noncomputable section

/-- Without a chain and without RH there is a farthest off-line zero. -/
theorem exists_farthest_offLine_of_not_jasOffLineChain (hno : ¬ JasOffLineChain)
    (hRH : ¬ RiemannHypothesis) :
    ∃ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 ∧
      ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
  unfold JasOffLineChain at hno
  push Not at hno
  obtain ⟨q₀, hoff, hmax⟩ := hno (exists_offLine_of_not_riemannHypothesis hRH)
  exact ⟨q₀, hoff, hmax⟩

/-- **Off a chain, the zeros lie left of `½ + (σ* − 1)`.** -/
theorem xiZeroHalfPlaneBound_jasAbscissa_of_not_jasOffLineChain (hno : ¬ JasOffLineChain)
    (hRH : ¬ RiemannHypothesis) : XiZeroHalfPlaneBound (jasAbscissa - 1) := by
  obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hno hRH
  have hσ := le_jasAbscissa_of_maximal_offLine q₀ hoff hmax
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h1 := hmax q
  have h2 := le_abs_self ((q.1 : ℂ).re - 1 / 2)
  linarith

/-- **No chain gives a zero-free half-plane strictly inside the strip.** -/
theorem exists_xiZeroHalfPlaneBound_lt_half_of_not_jasOffLineChain (hno : ¬ JasOffLineChain) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 / 2 ∧ XiZeroHalfPlaneBound α := by
  by_cases hRH : RiemannHypothesis
  · exact ⟨0, le_rfl, by norm_num, riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH⟩
  · obtain ⟨q₀, -, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hno hRH
    have hstrip := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q₀.1)
    refine ⟨|(q₀.1 : ℂ).re - 1 / 2|, abs_nonneg _, ?_, ?_⟩
    · rw [abs_lt]; constructor <;> linarith [hstrip.1, hstrip.2]
    · intro ρ hρ
      obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
      linarith [hmax q, le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **No chain gives a power-saving prime number theorem.** -/
theorem exists_chebyshevPsiReal_powerSaving_of_not_jasOffLineChain (hno : ¬ JasOffLineChain) :
    ∃ θ : ℝ, θ < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |chebyshevPsiReal t - t| ≤ C * t ^ θ := by
  obtain ⟨α, hα0, hα, hXi⟩ := exists_xiZeroHalfPlaneBound_lt_half_of_not_jasOffLineChain hno
  obtain ⟨C, hC, hbound⟩ := Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound
    hα0 hα hXi (epsilon := (1 / 2 - α) / 2) (by linarith)
  exact ⟨1 / 2 + α + (1 / 2 - α) / 2, by linarith, C, hC, hbound⟩

/-- **Positivity at `σ ≥ 1` without a chain places every zero left of `σ − ½`.** -/
theorem xiZeroHalfPlaneBound_of_jasDressedPSD_of_not_chain {σ : ℝ} (hσ : 1 ≤ σ)
    (hpsd : JasDressedPSD σ) (hno : ¬ JasOffLineChain) : XiZeroHalfPlaneBound (σ - 1) := by
  by_cases hRH : RiemannHypothesis
  · intro ρ hρ
    have h := riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH ρ hρ
    linarith
  · intro ρ hρ
    have h := xiZeroHalfPlaneBound_jasAbscissa_of_not_jasOffLineChain hno hRH ρ hρ
    have hle := jasDressedPSD_iff_jasAbscissa_le.mp hpsd
    linarith

end

end RHTower
