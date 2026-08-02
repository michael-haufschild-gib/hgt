import GaloisForLFunctions.HTGeometry.HermiteCoefficientMap

/-!
# The Schwartz seminorms of the normalized Hermite functions grow polynomially

The shifted number operator acts on the `n`-th Hermite function by `4π(n+1)`, so its powers act by
the corresponding powers.  Feeding that into the comparison of the Schwartz seminorms with the
oscillator seminorms bounds every Schwartz seminorm of the *normalized* Hermite function by a fixed
power of `4π(n+1)` — polynomial growth in the index, with the `L²` normalization cancelling the
factorial growth of the unnormalized functions.

That polynomial bound, against the faster-than-polynomial decay of the coefficients, is what makes
the Hermite expansion of a Schwartz function converge in the Schwartz topology.

* `shiftedNumberCLM_hermiteSchwartz` : **eigenvalue `4π(n+1)`.**
* `hermiteUnit` : the normalized Hermite function as a Schwartz map.
* `schwartzSeminorm_hermiteUnit_le` : **`p_{k,n}(ĥⱼ) ≤ C·(4π(j+1))^{k+n+2}`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The shifted eigenvalue -/

theorem shiftedNumberCLM_hermiteSchwartz (j : ℕ) :
    shiftedNumberCLM (hermiteSchwartz j) = (4 * (π : ℂ) * (j + 1)) • hermiteSchwartz j := by
  rw [shiftedNumberCLM_apply, numberCLM_hermiteSchwartz, ← add_smul]
  congr 1
  ring

theorem shiftedNumberCLM_iterate_hermiteSchwartz (m j : ℕ) :
    (shiftedNumberCLM^[m]) (hermiteSchwartz j)
      = ((4 * (π : ℂ) * (j + 1)) ^ m) • hermiteSchwartz j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, shiftedNumberCLM_hermiteSchwartz, smul_smul,
      pow_succ]

theorem norm_toLp_shiftedIterate_hermite (m j : ℕ) :
    ‖((shiftedNumberCLM^[m]) (hermiteSchwartz j)).toLp 2 (volume : Measure ℝ)‖
      = (4 * π * (j + 1)) ^ m * ‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ := by
  rw [shiftedNumberCLM_iterate_hermiteSchwartz, toLp_smul, norm_smul, norm_pow]
  congr 2
  have hval : (4 * (π : ℂ) * (j + 1)) = ((4 * π * (j + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ## The normalized Hermite functions -/

/-- The normalized `j`-th Hermite function, as a Schwartz map. -/
def hermiteUnit (j : ℕ) : 𝓢(ℝ, ℂ) :=
  ((‖(hermiteSchwartz j).toLp 2 (volume : Measure ℝ)‖ : ℂ))⁻¹ • hermiteSchwartz j

theorem norm_toLp_hermiteUnit_shifted (m j : ℕ) :
    ‖((shiftedNumberCLM^[m]) (hermiteUnit j)).toLp 2 (volume : Measure ℝ)‖
      = (4 * π * (j + 1)) ^ m := by
  have hpos := hermiteNorm_pos j
  rw [hermiteUnit, shiftedNumberCLM_iterate_smul, toLp_smul, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, norm_toLp_shiftedIterate_hermite]
  field_simp

/-- **Every Schwartz seminorm of the normalized Hermite functions grows at most polynomially.** -/
theorem schwartzSeminorm_hermiteUnit_le (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      SchwartzMap.seminorm ℂ k n (hermiteUnit j) ≤ C * (4 * π * (j + 1)) ^ (k + n + 2) := by
  obtain ⟨C, hC, hbound⟩ := schwartzSeminorm_le_shifted k n
  refine ⟨C, hC, fun j => ?_⟩
  have h := hbound (hermiteUnit j)
  rwa [norm_toLp_hermiteUnit_shifted] at h

end GaloisForLFunctions

end
