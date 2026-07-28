import GaloisForLFunctions.RHTower.LayerCakeZeroCount
import GaloisForLFunctions.RHTower.JensenMeanLog

/-!
# The Carlson skeleton: from a rectangle identity and a second moment to a zero count

Carlson's density argument has four ingredients.  Three are proved elsewhere in this development and
are unconditional:

* the layer-cake identity and the count-from-weighted-sum bound (`LayerCakeZeroCount`);
* the mean-log bound `2∫ log‖f‖ ≤ (b−a)·log(mean of ‖f‖²)` (`JensenMeanLog`);
* a bounded fourth moment for `ζ·M_y` on `re s = σ₀ > 1/2` (`FourthMomentDiagonal`).

The fourth is Littlewood's rectangle identity, which relates the weighted zero sum to the boundary
log-modulus.  This module takes that identity as an explicit hypothesis and assembles everything else,
so the whole argument is reduced to that one analytic input:

```text
2π ∑_β (β − σ₀)  ≤  ∫ log‖f(σ₀+it)‖ dt  −  ∫ log‖f(σ₁+it)‖ dt  +  E
```

Given it, a second-moment bound on the left edge and a log-modulus lower bound on the right edge cap
the zero count at every interior abscissa.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- **Carlson's counting bound, modulo the rectangle identity.**  With

* `hlittle` : the rectangle identity in inequality form,
* `hJensen` : the mean-log bound on the left edge (from `two_mul_integral_log_norm_le`),
* `hright`  : a lower bound for the log-modulus integral on the right edge,

the number of abscissas exceeding `σ` is bounded by the boundary data. -/
theorem count_le_of_rectangle_and_moment
    {σ₀ σ₁ σ T₁ T₂ E D L₀ L₁ M : ℝ} (Z : Finset ℝ)
    (hZ : ∀ b ∈ Z, σ₀ ≤ b ∧ b ≤ σ₁) (hσ : σ₀ < σ)
    (_hT : T₁ < T₂)
    (hlittle : 2 * Real.pi * (∑ b ∈ Z, (b - σ₀)) ≤ L₀ - L₁ + E)
    (hJensen : 2 * L₀ ≤ (T₂ - T₁) * Real.log (M / (T₂ - T₁)))
    (hright : -(D * (T₂ - T₁)) ≤ L₁) :
    (σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ)
      ≤ ((T₂ - T₁) * Real.log (M / (T₂ - T₁)) / 2 + D * (T₂ - T₁) + E) / (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcount := count_le_of_sum_sub Z hZ (le_of_lt hσ)
  have hchain : 2 * Real.pi * ((σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ))
      ≤ (T₂ - T₁) * Real.log (M / (T₂ - T₁)) / 2 + D * (T₂ - T₁) + E := by
    calc 2 * Real.pi * ((σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ))
        ≤ 2 * Real.pi * (∑ b ∈ Z, (b - σ₀)) :=
          mul_le_mul_of_nonneg_left hcount (le_of_lt hπ)
      _ ≤ L₀ - L₁ + E := hlittle
      _ ≤ (T₂ - T₁) * Real.log (M / (T₂ - T₁)) / 2 + D * (T₂ - T₁) + E := by linarith
  rw [le_div_iff₀ hπ]
  linarith [hchain]

/-- **The `o(T)` shape.**  If the boundary data grows linearly in the box height — a second moment
`M ≤ C·(T₂−T₁)`, a bounded right edge, and an error `E ≤ F·(T₂−T₁)` — then the count at every
interior abscissa is at most a constant multiple of the height, with the constant explicit in the
boundary data.  Sublinearity in Carlson's theorem comes from letting `σ₁ → σ` afterwards, which makes
the factor `(σ − σ₀)⁻¹` the only obstruction. -/
theorem count_le_linear_of_boundary
    {σ₀ σ₁ σ T₁ T₂ C D F M L₀ L₁ E : ℝ} (Z : Finset ℝ)
    (hZ : ∀ b ∈ Z, σ₀ ≤ b ∧ b ≤ σ₁) (hσ : σ₀ < σ)
    (hT : T₁ < T₂) (_hC : 0 < C)
    (hM : M ≤ C * (T₂ - T₁))
    (hlittle : 2 * Real.pi * (∑ b ∈ Z, (b - σ₀)) ≤ L₀ - L₁ + E)
    (hJensen : 2 * L₀ ≤ (T₂ - T₁) * Real.log (M / (T₂ - T₁)))
    (hright : -(D * (T₂ - T₁)) ≤ L₁)
    (hE : E ≤ F * (T₂ - T₁))
    (hMpos : 0 < M) :
    (σ - σ₀) * ((Z.filter fun b => σ < b).card : ℝ)
      ≤ (T₂ - T₁) * (Real.log C / 2 + D + F) / (2 * Real.pi) := by
  have hlen : 0 < T₂ - T₁ := by linarith
  have hmean : M / (T₂ - T₁) ≤ C := by
    rw [div_le_iff₀ hlen]; linarith
  have hmeanpos : 0 < M / (T₂ - T₁) := div_pos hMpos hlen
  have hlog : Real.log (M / (T₂ - T₁)) ≤ Real.log C :=
    Real.log_le_log hmeanpos hmean
  have hbase := count_le_of_rectangle_and_moment (σ₁ := σ₁) (T₁ := T₁) (T₂ := T₂)
    (E := E) (D := D) (L₀ := L₀) (L₁ := L₁) (M := M) Z hZ hσ hT hlittle hJensen hright
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine le_trans hbase ?_
  rw [div_le_div_iff_of_pos_right hπ]
  nlinarith [hlog, hlen, hE]

end RHTower
