import GaloisForLFunctions.HTGeometry.CubeNoEmbedding

/-!
# Independent circle coordinates force topological dimension

If a space carries an `m`-parameter family whose points are separated by `m` circle-valued
coordinates winding independently along the parameters, then the parameter cube sits inside it as a
topological cube.  Consequently no continuous map into `ℝ^k` with `k < m` can separate the points of
that cube.

This is the geometric half of the statement that a compact abelian group with `m` rationally
independent characters has covering dimension at least `m`.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- **Points of the unit cube are separated by their circle coordinates.** -/
theorem eq_of_exp_pi_mul_I_eq {m : ℕ} {v v' : EuclideanSpace ℝ (Fin m)} (hv : v ∈ unitCube m)
    (hv' : v' ∈ unitCube m)
    (hexp : ∀ j, Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (v' j : ℂ))) : v = v' := by
  refine PiLp.ext fun j => ?_
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp j)
  have hpi : ((Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero]
    exact mul_ne_zero h1 Complex.I_ne_zero
  have hkey : ((Real.pi : ℂ) * Complex.I) * ((v j : ℂ) - (v' j : ℂ) - 2 * (n : ℂ)) = 0 := by
    rw [mul_sub, mul_sub]
    rw [hn]
    ring
  have hzero : (v j : ℂ) - (v' j : ℂ) - 2 * (n : ℂ) = 0 := by
    rcases mul_eq_zero.mp hkey with hc | hc
    · exact absurd hc hpi
    · exact hc
  have hreal : (v j : ℝ) - v' j - 2 * (n : ℝ) = 0 := by
    have hc : (((v j : ℝ) - v' j - 2 * (n : ℝ) : ℝ) : ℂ) = 0 := by
      push_cast
      push_cast at hzero
      linear_combination hzero
    have := Complex.ofReal_eq_zero.mp hc
    linarith [this]
  obtain ⟨hv0, hv1⟩ := hv j
  obtain ⟨hv'0, hv'1⟩ := hv' j
  have hnbound : |(2 : ℝ) * (n : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
      have hcast : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := by push_cast; ring
      exact_mod_cast hcast ▸ (by exact_mod_cast hz : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ))
    rw [abs_mul] at hnbound
    simp only [abs_two] at hnbound
    linarith
  rw [hn0] at hreal
  push_cast at hreal
  linarith

/-- **Independent circle coordinates obstruct a low-dimensional continuous separation.** -/
theorem not_separating_of_circle_coordinates {X : Type*} [TopologicalSpace X] {k m : ℕ}
    (hkm : k < m) (Θ : EuclideanSpace ℝ (Fin m) → X) (χ : Fin m → X → ℂ)
    (hχΘ : ∀ (v : EuclideanSpace ℝ (Fin m)) (j : Fin m),
      χ j (Θ v) = Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ)))
    (h : X → EuclideanSpace ℝ (Fin k))
    (hcont : ContinuousOn (fun v => h (Θ v)) (unitCube m))
    (hsep : ∀ v ∈ unitCube m, ∀ v' ∈ unitCube m, h (Θ v) = h (Θ v') →
      ∀ j, χ j (Θ v) = χ j (Θ v')) :
    False := by
  refine not_injOn_unitCube hkm (fun v => h (Θ v)) hcont ?_
  intro v hv v' hv' heq
  refine eq_of_exp_pi_mul_I_eq hv hv' fun j => ?_
  rw [← hχΘ v j, ← hχΘ v' j]
  exact hsep v hv v' hv' heq j

end GaloisForLFunctions.HTGeometry
