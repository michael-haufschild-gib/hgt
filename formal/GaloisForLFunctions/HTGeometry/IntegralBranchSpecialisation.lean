import GaloisForLFunctions.HTGeometry.EisensteinIntegralForm

/-!
# From a rational branch to a `p`-adic root

The four steps — Eisenstein's denominator bound, the matching rescaling of branch and polynomial,
the lift along `ℤ ↪ ℚ`, and evaluation at a small `p`-adic number — are assembled here into one
statement: a power-series root of a polynomial with integral coefficients over `ℚ⟦t⟧` produces, for
every prime `p` and every `a ∈ ℤ_p` of norm below one, a genuine root in `ℤ_p` of an integral
polynomial specialised at `a`.

This is the arithmetic content that a specialisation argument consumes: the formal branches of an
algebraic function are not merely formal — they take values.
-/

namespace GaloisForLFunctions.HTGeometry

open PowerSeries

/-- Every rational is cleared into the integers by its denominator. -/
theorem hfrac_int_range :
    ∀ x : ℚ, ∃ d ∈ (Int.castRingHom ℚ).range, d ≠ 0 ∧ d * x ∈ (Int.castRingHom ℚ).range := by
  intro x
  refine ⟨(x.den : ℚ), ⟨(x.den : ℤ), by simp⟩, ?_, ?_⟩
  · exact_mod_cast x.den_nz
  · rw [Rat.den_mul_eq_num]
    exact ⟨x.num, by simp⟩

/-- **A rational branch has an integral model.**  After Eisenstein's rescaling the branch and its
defining polynomial both live over `ℤ`. -/
theorem exists_integral_root_form
    {f : Polynomial (PowerSeries ℚ)}
    (hf : ∀ i N, PowerSeries.coeff N (f.coeff i) ∈ (Int.castRingHom ℚ).range)
    {y : PowerSeries ℚ} (hroot : f.eval y = 0) {r : ℕ}
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative f).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative f).eval y) ≠ 0) :
    ∃ (g : Polynomial (PowerSeries ℤ)) (z : PowerSeries ℤ), g.eval z = 0 := by
  obtain ⟨q, hq, hq0, D, hD, hD0, hbnd⟩ :=
    exists_coeff_mem_of_isRoot_of_frac (A := (Int.castRingHom ℚ).range) hfrac_int_range hf hroot
      hlow hr
  obtain ⟨z, hzmap⟩ :=
    exists_map_eq_of_coeff_mem_range (Int.castRingHom ℚ) (coeffMem_scaledRoot hbnd)
  obtain ⟨g, hgmap⟩ :=
    exists_polyMap_eq_of_coeff_mem_range (Int.castRingHom ℚ) (coeffMem_scaledPoly hD hq hf)
  refine ⟨g, z, ?_⟩
  have hinj : Function.Injective (PowerSeries.map (Int.castRingHom ℚ)) :=
    PowerSeries.map_injective _ Int.cast_injective
  apply hinj
  rw [map_zero, eval_map_of_eval, hgmap, hzmap]
  exact eval_scaledPoly D q hroot

/-- **A rational branch produces a `p`-adic root.**  For every prime `p` and every `a ∈ ℤ_p` of
norm below one, the integral model of the branch specialises to a root in `ℤ_p`. -/
theorem exists_padic_root_of_branch (p : ℕ) [Fact p.Prime] {a : ℤ_[p]} (ha : ‖a‖ < 1)
    {f : Polynomial (PowerSeries ℚ)}
    (hf : ∀ i N, PowerSeries.coeff N (f.coeff i) ∈ (Int.castRingHom ℚ).range)
    {y : PowerSeries ℚ} (hroot : f.eval y = 0) {r : ℕ}
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative f).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative f).eval y) ≠ 0) :
    ∃ (g : Polynomial (PowerSeries ℤ)) (x : ℤ_[p]),
      (g.map (padicEval p ha)).eval x = 0 := by
  obtain ⟨g, z, hgz⟩ := exists_integral_root_form hf hroot hlow hr
  exact ⟨g, padicEval p ha z, isRoot_padicEval p ha hgz⟩

end GaloisForLFunctions.HTGeometry
