import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeReflectionWalk
import GaloisForLFunctions.HTGeometry.InfinitesimalCompressionCurvature

/-!
# Exact leakage of the actual probe walk

On the finite probe span, the squared norm lost by each Chebyshev polynomial
of the Weil signal is exactly the squared norm of the walk outside that span.
Thus every order is contractive, with equality precisely at a return to the
probe span. No orthonormality of the original probe family is required.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open _root_.Polynomial

theorem norm_walk_pow {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x}) (n : ℕ)
    (x : ZeroSpace) : ‖(walk p ^ n) x‖ = ‖x‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change ‖walk p ((walk p ^ n) x)‖ = ‖x‖
    rw [norm_walk, ih]

/-- The Chebyshev signal is the component of the walk retained by the probe span. -/
theorem chebyshev_apply_eq_projected_walk {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
    (n : ℕ) {x : ZeroSpace} (hx : x ∈ probeSpace p) :
    aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x = probeProjection p ((walk p ^ n) x) := by
  have h := congrArg (fun A : ZeroSpace →L[ℂ] ZeroSpace => A x) (walk_compression p n)
  have hQ : probeProjection p x = x := Submodule.starProjection_eq_self_iff.mpr hx
  change probeProjection p ((walk p ^ n) (probeProjection p x)) =
    aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) (probeProjection p x) at h
  rw [hQ] at h
  exact h.symm

/-- Every Chebyshev order has an exact Pythagorean loss formula on actual probes. -/
theorem chebyshev_leakage_identity {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
    (n : ℕ) {x : ZeroSpace} (hx : x ∈ probeSpace p) :
    ‖aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x‖ ^ 2 +
      ‖(walk p ^ n) x - probeProjection p ((walk p ^ n) x)‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [chebyshev_apply_eq_projected_walk p n hx]
  have h := HTGeometry.norm_sq_causalCompression_add_orthogonalLeakage
    (probeSpace p) (walk p ^ n) (norm_walk_pow p n) x
  change ‖probeProjection p ((walk p ^ n) x)‖ * ‖probeProjection p ((walk p ^ n) x)‖ +
    ‖(walk p ^ n) x - probeProjection p ((walk p ^ n) x)‖ *
      ‖(walk p ^ n) x - probeProjection p ((walk p ^ n) x)‖ = ‖x‖ * ‖x‖ at h
  simpa only [pow_two] using h

/-- Chebyshev filtering never increases the norm of a vector in the actual probe span. -/
theorem chebyshev_norm_le {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
    (n : ℕ) {x : ZeroSpace} (hx : x ∈ probeSpace p) :
    ‖aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x‖ ≤ ‖x‖ := by
  have h := chebyshev_leakage_identity p n hx
  nlinarith only [h, sq_nonneg ‖(walk p ^ n) x - probeProjection p ((walk p ^ n) x)‖,
    norm_nonneg (aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x), norm_nonneg x]

/-- Equality in the contraction bound is exactly return to the finite probe span. -/
theorem chebyshev_norm_eq_iff_return {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
    (n : ℕ) {x : ZeroSpace} (hx : x ∈ probeSpace p) :
    ‖aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x‖ = ‖x‖ ↔
      (walk p ^ n) x ∈ probeSpace p := by
  constructor
  · intro he
    have h := chebyshev_leakage_identity p n hx
    rw [he] at h
    have hz : ‖(walk p ^ n) x - probeProjection p ((walk p ^ n) x)‖ = 0 := by
      nlinarith only [h, norm_nonneg ((walk p ^ n) x - probeProjection p ((walk p ^ n) x))]
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro hret
    rw [chebyshev_apply_eq_projected_walk p n hx]
    have hQ : probeProjection p ((walk p ^ n) x) = (walk p ^ n) x :=
      Submodule.starProjection_eq_self_iff.mpr hret
    rw [hQ, norm_walk_pow]

#print axioms chebyshev_leakage_identity
#print axioms chebyshev_norm_le
#print axioms chebyshev_norm_eq_iff_return

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
