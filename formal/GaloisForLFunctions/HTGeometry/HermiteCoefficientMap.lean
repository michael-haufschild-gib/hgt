import GaloisForLFunctions.HTGeometry.SchwartzShiftedSeminorm

/-!
# The normalized Hermite coefficients of a Schwartz function

Dividing the pairing against a Hermite function by its `L²` norm gives the coefficient of the
Schwartz function along the normalized Hermite function.  Cauchy–Schwarz bounds that coefficient by
the `L²` norm of the function, and the decay estimate bounds `(2π(2n+1))ᵏ` times it by the `L²`
norm of the `k`-th power of the Hamiltonian.

These are the two estimates the coefficient map into a Köthe space of rapidly decreasing sequences
consumes: the second says the coefficients lie in the space, the first that the map is bounded.

* `hermiteNorm_pos` : the Hermite functions have positive `L²` norm.
* `hermiteCoeff` : the normalized coefficient.
* `norm_hermiteCoeff_le` : **`|cₙ(f)| ≤ ‖f‖₂`.**
* `hermiteCoeff_decay` : **`(2π(2n+1))ᵏ|cₙ(f)| ≤ ‖Hᵏf‖₂`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

theorem hermiteNorm_pos (n : ℕ) :
    0 < ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ := by
  refine norm_pos_iff.mpr ?_
  exact hermiteSchwartz_toLp_ne_zero n

/-- The coefficient of a Schwartz function along the normalized `n`-th Hermite function. -/
def hermiteCoeff (f : 𝓢(ℝ, ℂ)) (n : ℕ) : ℂ :=
  ((‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ : ℂ))⁻¹
    * schwartzPair f (hermiteSchwartz n)

theorem norm_hermiteCoeff (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ‖hermiteCoeff f n‖
      = ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖⁻¹
        * ‖schwartzPair f (hermiteSchwartz n)‖ := by
  rw [hermiteCoeff, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hermiteNorm_pos n)]

/-- **The normalized coefficients are bounded by the `L²` norm.** -/
theorem norm_hermiteCoeff_le (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ‖hermiteCoeff f n‖ ≤ ‖f.toLp 2 (volume : Measure ℝ)‖ := by
  have hpos := hermiteNorm_pos n
  rw [norm_hermiteCoeff]
  have hcs := norm_schwartzPair_hermiteSchwartz_le f n
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  calc ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖
        * ‖f.toLp 2 (volume : Measure ℝ)‖ := hcs
    _ = ‖f.toLp 2 (volume : Measure ℝ)‖
        * ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ := by ring

/-- **The normalized coefficients decay faster than any power**, with the `L²` norm of a power of
the Hamiltonian as the constant. -/
theorem hermiteCoeff_decay (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (2 * π * (2 * n + 1)) ^ k * ‖hermiteCoeff f n‖
      ≤ ‖((hamiltonianCLM^[k]) f).toLp 2 (volume : Measure ℝ)‖ := by
  have hpos := hermiteNorm_pos n
  have hdecay := schwartzPair_hermiteSchwartz_hamiltonian_decay k n f
  rw [norm_hermiteCoeff]
  have hrewrite : (2 * π * (2 * n + 1)) ^ k
      * (‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖⁻¹
        * ‖schwartzPair f (hermiteSchwartz n)‖)
      = ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖⁻¹
        * ((2 * π * (2 * n + 1)) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖) := by ring
  rw [hrewrite, inv_mul_eq_div, div_le_iff₀ hpos]
  calc (2 * π * (2 * n + 1)) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖
        * ‖((hamiltonianCLM^[k]) f).toLp 2 (volume : Measure ℝ)‖ := hdecay
    _ = ‖((hamiltonianCLM^[k]) f).toLp 2 (volume : Measure ℝ)‖
        * ‖(hermiteSchwartz n).toLp 2 (volume : Measure ℝ)‖ := by ring

/-- The coefficient map kills only the zero function: it is injective on the Schwartz space. -/
theorem hermiteCoeff_eq_zero_iff (f : 𝓢(ℝ, ℂ)) :
    (∀ n : ℕ, hermiteCoeff f n = 0) ↔ f = 0 := by
  constructor
  · intro h
    refine hermiteSchwartz_complete fun n => ?_
    have hn := h n
    rw [hermiteCoeff, mul_eq_zero] at hn
    rcases hn with hzero | hpair
    · exact absurd hzero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (hermiteNorm_pos n).ne'))
    · exact hpair
  · rintro rfl
    intro n
    rw [hermiteCoeff, schwartzPair_comm, schwartzPair_zero_right, mul_zero]

end GaloisForLFunctions

end
