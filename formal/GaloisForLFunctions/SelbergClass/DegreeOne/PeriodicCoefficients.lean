import GaloisForLFunctions.SelbergClass.DegreeOne.BoundaryLaw

/-!
# The conductor is an integer, and the twisted coefficients are periodic

Let `F` be a nonzero element of the extended class of degree one, with conductor `q` and internal
shift `θ`.  Then `q` is a positive integer (`exists_conductor_eq_nat`) and `n ↦ a(n) n^{iθ}` has
period `q` on the positive integers (`twistedCoeff_add_conductor`).

The exponential series has period `2πi`, so its boundary law is invariant under `β ↦ β + 2π`.  A point
of the lattice `(2π/q)ℕ` with nonzero strength must be carried back to the lattice, which forces
`q ∈ ℕ`; then the strengths at `2πm/q` and `2π(m+q)/q` agree.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

theorem boundaryPath_add_two_pi (β y : ℝ) :
    boundaryPath (β + 2 * π) y = boundaryPath β y + 2 * (π : ℂ) * I := by
  unfold boundaryPath
  push_cast
  ring

theorem series_boundaryPath_add (F : ExtendedSelbergClass) (β y : ℝ) :
    ordinaryExponentialSeries F (boundaryPath (β + 2 * π) y) =
      ordinaryExponentialSeries F (boundaryPath β y) := by
  rw [boundaryPath_add_two_pi]
  exact ordinaryExponentialSeries_periodic F _

theorem natCast_cpow_ne_zero {m : ℕ} (hm : m ≠ 0) (w : ℂ) : (m : ℂ) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm)]
  exact Complex.exp_ne_zero _

/-- **The conductor of a degree-one element is a positive integer.** -/
theorem exists_conductor_eq_nat (F : ExtendedSelbergClass) (hd : F.gammaData.degree = 1) :
    ∃ q : ℕ, q ≠ 0 ∧ F.gammaData.conductor = q := by
  obtain ⟨C, hC, hlat, hoff⟩ := exists_boundary_law F hd
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, F.coeff m₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact F.coeff_ne_zero (ArithmeticFunction.ext h)
  have hm₀0 : m₀ ≠ 0 := by
    rintro rfl
    exact hm₀ F.coeff.map_zero
  have hq := F.gammaData.conductor_pos
  have hκ := latticeStep_pos F.gammaData
  have hL : C * (star (F.coeff m₀) * (m₀ : ℂ) ^ (-(I * (F.gammaData.internalShift : ℂ)))) ≠ 0 :=
    mul_ne_zero hC (mul_ne_zero (star_ne_zero.mpr hm₀) (natCast_cpow_ne_zero hm₀0 _))
  have hm₀R : (0 : ℝ) < m₀ := by exact_mod_cast Nat.pos_of_ne_zero hm₀0
  have hβ : 0 < latticeStep F.gammaData * m₀ + 2 * π := by positivity
  have hmem : ∃ m : ℕ, m ≠ 0 ∧ latticeStep F.gammaData * m₀ + 2 * π = latticeStep F.gammaData * m := by
    by_contra hnot
    push Not at hnot
    have h0 := hoff _ hβ hnot
    have h1 := hlat m₀ hm₀0
    simp only [series_boundaryPath_add] at h0
    exact hL (tendsto_nhds_unique h1 h0)
  obtain ⟨m, _, hm⟩ := hmem
  have hreal : (m₀ : ℝ) + F.gammaData.conductor = m := by
    unfold latticeStep at hm
    have hπ := Real.pi_pos
    field_simp at hm
    linarith
  have hlt : m₀ < m := by
    have : (m₀ : ℝ) < m := by linarith
    exact_mod_cast this
  refine ⟨m - m₀, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith

/-- The strengths of the boundary law are periodic. -/
theorem star_coeff_mul_cpow_add (F : ExtendedSelbergClass) (hd : F.gammaData.degree = 1) {q : ℕ}
    (hq : F.gammaData.conductor = q) {m : ℕ} (hm : m ≠ 0) :
    star (F.coeff (m + q)) * ((m + q : ℕ) : ℂ) ^ (-(I * (F.gammaData.internalShift : ℂ))) =
      star (F.coeff m) * (m : ℂ) ^ (-(I * (F.gammaData.internalShift : ℂ))) := by
  obtain ⟨C, hC, hlat, _⟩ := exists_boundary_law F hd
  have hq0 : (q : ℝ) ≠ 0 := by
    have := F.gammaData.conductor_pos
    rw [hq] at this
    exact this.ne'
  have hshift : latticeStep F.gammaData * ((m + q : ℕ) : ℝ) =
      latticeStep F.gammaData * m + 2 * π := by
    unfold latticeStep
    rw [hq]
    push_cast
    field_simp
  have h1 := hlat (m + q) (by omega)
  rw [hshift] at h1
  simp only [series_boundaryPath_add] at h1
  exact mul_left_cancel₀ hC (tendsto_nhds_unique h1 (hlat m hm))

/-- The coefficients with the internal shift removed. -/
def twistedCoeff (F : ExtendedSelbergClass) (n : ℕ) : ℂ :=
  F.coeff n * (n : ℂ) ^ (I * (F.gammaData.internalShift : ℂ))

theorem star_natCast_cpow {m : ℕ} (hm : m ≠ 0) (θ : ℝ) :
    star ((m : ℂ) ^ (-(I * (θ : ℂ)))) = (m : ℂ) ^ (I * (θ : ℂ)) := by
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [Complex.cpow_def_of_ne_zero hmc, Complex.cpow_def_of_ne_zero hmc, Complex.star_def,
    ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.natCast_log,
    Complex.conj_ofReal]
  ring

/-- **Periodicity of the twisted coefficients.** -/
theorem twistedCoeff_add_conductor (F : ExtendedSelbergClass) (hd : F.gammaData.degree = 1) {q : ℕ}
    (hq : F.gammaData.conductor = q) {m : ℕ} (hm : m ≠ 0) :
    twistedCoeff F (m + q) = twistedCoeff F m := by
  have h := congrArg star (star_coeff_mul_cpow_add F hd hq hm)
  rw [star_mul', star_mul', star_star, star_star, star_natCast_cpow (by omega),
    star_natCast_cpow hm] at h
  exact h

end GaloisForLFunctions.SelbergClass.DegreeOne
