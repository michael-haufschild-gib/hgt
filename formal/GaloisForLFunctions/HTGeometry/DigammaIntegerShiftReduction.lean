import GaloisForLFunctions.HTGeometry.GammaMonomialLogDeriv

/-!
# Reducing a digamma shift modulo the integers

`ψ(z + n)` differs from `ψ(z)` by a rational function, so a finite family of digamma shifts may
always be replaced by pairwise incongruent orbit representatives without leaving the differential
field they generate over `ℂ(s)`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The `n`-fold digamma shift.** -/
theorem digamma_add_natCast {z : ℂ} (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) (n : ℕ) :
    Complex.digamma (z + (n : ℂ))
      = Complex.digamma z + ∑ i ∈ Finset.range n, (z + (i : ℂ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hzn : ∀ m : ℕ, z + (n : ℂ) ≠ -(m : ℂ) := by
        intro m hcon
        refine hz (m + n) ?_
        have : z = -(m : ℂ) - (n : ℂ) := by linear_combination hcon
        rw [this]
        push_cast
        ring
      have hrw : z + ((n + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 := by push_cast; ring
      rw [hrw, Complex.digamma_apply_add_one _ hzn, ih, Finset.sum_range_succ]
      ring

/-- The `j`-th jet of a digamma shift, reduced modulo the integers. -/
theorem digamma_add_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    Complex.digamma (z + (n : ℂ))
      = Complex.digamma z + ∑ i ∈ Finset.range n, (z + (i : ℂ))⁻¹ :=
  digamma_add_natCast (fun m => gamma_shift_ne_zero_of_re_pos hz m) n

end

end GaloisForLFunctions.HTGeometry
