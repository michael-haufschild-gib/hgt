import Mathlib

/-!
# Determinant torsion, exact history, phase quotient, and open logarithmic lift

For a scalar `u` in a field, the based two-term complex `C(u) : 0 → k e₁ →(·u) k e₀ → 0` is acyclic
as soon as `u ≠ 0`, so the homological observer sees the same object — zero — for every `u`.  The
comparison scalar `u` between the declared source bases survives as the determinant history, and
this file certifies the three ways it is lost or retained:

* `basedChainIso_nonempty_iff` — a basis-preserving chain isomorphism `C(u) → C(v)` exists exactly
  when `u = v`, while `exists_unbased_chainIso` shows that declaring arbitrary independent basis
  changes as gauge collapses the whole nonzero family: the source marking is load-bearing;
* `det_sumDifferential` — the history is multiplicative under orthogonal direct sums, being the
  determinant of the diagonal differential;
* `positiveShadow_eq_iff_phase` — the positive shadow `|τ|²` is exactly the quotient of `ℂˣ` by its
  `U(1)`-phase action, so positive scalarization is a phase quotient;
* `closed_observation_open_lift` — the loop `u_N(t) = exp(2πiNt)` has constantly zero homology,
  constant positive shadow one, and a closed determinant history, yet its logarithmic lift is open
  with endpoint `2πiN`, recovered by the logarithmic-derivative integral.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section BasedComplex

variable {k : Type*} [Field k]

/-- The differential of the based two-term complex `C(u)`: multiplication by the comparison
scalar `u` between the declared source bases. -/
def torsionDifferential (u : k) : k →ₗ[k] k := LinearMap.toSpanSingleton k k u

theorem torsionDifferential_apply (u c : k) : torsionDifferential u c = c * u := rfl

/-- **`C(u)` is acyclic in degree one.** -/
theorem torsionDifferential_ker (u : k) (hu : u ≠ 0) :
    LinearMap.ker (torsionDifferential u) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro c hc
  rw [torsionDifferential_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_right hu

/-- **`C(u)` is acyclic in degree zero.** -/
theorem torsionDifferential_range (u : k) (hu : u ≠ 0) :
    LinearMap.range (torsionDifferential u) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  exact ⟨y * u⁻¹, by rw [torsionDifferential_apply, inv_mul_cancel_right₀ hu]⟩

theorem torsionDifferential_eq_smul (u : k) :
    torsionDifferential u = u • (LinearMap.id : k →ₗ[k] k) := by
  ext
  simp [torsionDifferential_apply, mul_comm]

/-- **The determinant history is the determinant of the differential.**  For the based two-term
complex the comparison scalar is exactly `det d_u`. -/
theorem det_torsionDifferential (u : k) : LinearMap.det (torsionDifferential u) = u := by
  rw [torsionDifferential_eq_smul, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_self, pow_one]

/-- **Homology forgets the whole family.**  All nonzero comparison scalars give the same, zero,
homological observation. -/
theorem homology_indistinguishable (u v : k) (hu : u ≠ 0) (hv : v ≠ 0) :
    LinearMap.ker (torsionDifferential u) = LinearMap.ker (torsionDifferential v) ∧
      LinearMap.range (torsionDifferential u) = LinearMap.range (torsionDifferential v) := by
  rw [torsionDifferential_ker u hu, torsionDifferential_ker v hv,
    torsionDifferential_range u hu, torsionDifferential_range v hv]
  exact ⟨rfl, rfl⟩

/-- The differential of a finite orthogonal sum of based two-term complexes. -/
noncomputable def sumDifferential {r : ℕ} (u : Fin r → k) : (Fin r → k) →ₗ[k] (Fin r → k) :=
  Matrix.toLin' (Matrix.diagonal u)

theorem sumDifferential_apply {r : ℕ} (u : Fin r → k) (c : Fin r → k) (j : Fin r) :
    sumDifferential u c j = u j * c j := by
  simp [sumDifferential, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- **Determinant history is multiplicative under direct sums.** -/
theorem det_sumDifferential {r : ℕ} (u : Fin r → k) :
    LinearMap.det (sumDifferential u) = ∏ j, u j := by
  rw [sumDifferential, LinearMap.det_toLin', Matrix.det_diagonal]

/-- A based chain isomorphism `C(u) → C(v)`: linear automorphisms in both degrees fixing the
declared basis vectors and commuting with the differentials. -/
structure BasedChainIso (u v : k) where
  /-- Degree-one component. -/
  deg1 : k ≃ₗ[k] k
  /-- Degree-zero component. -/
  deg0 : k ≃ₗ[k] k
  /-- The degree-one basis vector is preserved. -/
  base1 : deg1 1 = 1
  /-- The degree-zero basis vector is preserved. -/
  base0 : deg0 1 = 1
  /-- The square commutes. -/
  commutes : ∀ c, deg0 (torsionDifferential u c) = torsionDifferential v (deg1 c)

/-- A basis-fixing linear automorphism of the ground field is the identity. -/
theorem linearEquiv_eq_id_of_base {f : k ≃ₗ[k] k} (hf : f 1 = 1) (c : k) : f c = c := by
  have := f.map_smul c 1
  simpa [hf, smul_eq_mul] using this

/-- **Determinant history is a complete based invariant.**  A basis-preserving chain isomorphism
`C(u) → C(v)` exists if and only if `u = v`. -/
theorem basedChainIso_nonempty_iff (u v : k) : Nonempty (BasedChainIso u v) ↔ u = v := by
  constructor
  · rintro ⟨F⟩
    have h := F.commutes 1
    rw [linearEquiv_eq_id_of_base F.base0, linearEquiv_eq_id_of_base F.base1,
      torsionDifferential_apply, torsionDifferential_apply, one_mul, one_mul] at h
    exact h
  · rintro rfl
    exact ⟨{ deg1 := LinearEquiv.refl k k
             deg0 := LinearEquiv.refl k k
             base1 := rfl
             base0 := rfl
             commutes := fun _ => rfl }⟩

/-- **Unrestricted gauge destroys the invariant.**  If arbitrary independent basis changes in the
two degrees are declared gauge, every nonzero comparison scalar becomes every other one. -/
theorem exists_unbased_chainIso (u v : k) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ f1 f0 : k ≃ₗ[k] k, ∀ c, f0 (torsionDifferential u c) = torsionDifferential v (f1 c) := by
  refine ⟨LinearEquiv.refl k k,
    LinearEquiv.smulOfNeZero k k (v * u⁻¹) (mul_ne_zero hv (inv_ne_zero hu)), fun c => ?_⟩
  show (v * u⁻¹) • (c * u) = c * v
  rw [smul_eq_mul]
  field_simp

end BasedComplex

section PhaseQuotient

/-- The positive history shadow `|τ|²`. -/
noncomputable def positiveShadow (u : ℂ) : ℝ := Complex.normSq u

theorem positiveShadow_pos {u : ℂ} (hu : u ≠ 0) : 0 < positiveShadow u :=
  Complex.normSq_pos.mpr hu

/-- Unitary histories all have positive shadow one. -/
theorem positiveShadow_exp (θ : ℝ) : positiveShadow (Complex.exp (θ * Complex.I)) = 1 := by
  have h : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  rw [positiveShadow, Complex.normSq_eq_norm_sq, h, one_pow]

/-- **Positive scalarization is exactly the phase quotient.**  Two nonzero determinant histories
have the same positive shadow if and only if they differ by a `U(1)` phase. -/
theorem positiveShadow_eq_iff_phase {u v : ℂ} (hu : u ≠ 0) :
    positiveShadow u = positiveShadow v ↔ ∃ θ : ℝ, v = Complex.exp (θ * Complex.I) * u := by
  constructor
  · intro h
    have hnorm : ‖v / u‖ = 1 := by
      rw [norm_div]
      have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      have : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        exact h
      have hnn : ‖u‖ = ‖v‖ := by
        have h1 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
        have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
        nlinarith [this]
      rw [← hnn]
      exact div_self hu'
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (v / u)).mp hnorm
    exact ⟨θ, by rw [hθ]; field_simp⟩
  · rintro ⟨θ, rfl⟩
    simp only [positiveShadow, map_mul]
    rw [show Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 from positiveShadow_exp θ,
      one_mul]

end PhaseQuotient

section OpenLift

/-- The angular speed of the `N`-fold determinant loop. -/
noncomputable def loopSpeed (N : ℤ) : ℂ := 2 * Real.pi * Complex.I * N

/-- The `N`-fold determinant history loop `u_N(t) = exp(2πiNt)`. -/
noncomputable def loopHistory (N : ℤ) (t : ℝ) : ℂ := Complex.exp (loopSpeed N * t)

/-- The chosen logarithmic lift of the determinant history. -/
noncomputable def logLift (N : ℤ) (t : ℝ) : ℂ := loopSpeed N * t

theorem exp_logLift (N : ℤ) (t : ℝ) : Complex.exp (logLift N t) = loopHistory N t := rfl

theorem loopSpeed_mul (N : ℤ) (t : ℝ) :
    loopSpeed N * t = ((2 * Real.pi * N * t : ℝ) : ℂ) * Complex.I := by
  simp only [loopSpeed]
  push_cast
  ring

theorem loopSpeed_ne_zero {N : ℤ} (hN : N ≠ 0) : loopSpeed N ≠ 0 := by
  simp only [loopSpeed, ne_eq, mul_eq_zero, not_or]
  refine ⟨⟨⟨two_ne_zero, ?_⟩, Complex.I_ne_zero⟩, ?_⟩
  · exact_mod_cast Real.pi_ne_zero
  · exact_mod_cast hN

/-- The determinant history is nowhere zero, so every member of the family is acyclic. -/
theorem loopHistory_ne_zero (N : ℤ) (t : ℝ) : loopHistory N t ≠ 0 := Complex.exp_ne_zero _

/-- The positive shadow of the loop is constantly one. -/
theorem positiveShadow_loopHistory (N : ℤ) (t : ℝ) : positiveShadow (loopHistory N t) = 1 := by
  rw [loopHistory, loopSpeed_mul]
  exact positiveShadow_exp _

/-- The determinant history is a closed loop. -/
theorem loopHistory_zero (N : ℤ) : loopHistory N 0 = 1 := by
  simp [loopHistory]

theorem loopHistory_one (N : ℤ) : loopHistory N 1 = 1 := by
  have h : loopSpeed N * (1 : ℝ) = (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [loopSpeed]
    push_cast
    ring
  rw [loopHistory, h, Complex.exp_int_mul_two_pi_mul_I]

/-- **The logarithmic lift is open.**  Its endpoint increment is `2πiN`, nonzero for `N ≠ 0`. -/
theorem logLift_endpoint (N : ℤ) : logLift N 1 - logLift N 0 = loopSpeed N := by
  simp [logLift]

theorem logLift_ne_of_ne_zero {N : ℤ} (hN : N ≠ 0) : logLift N 1 ≠ logLift N 0 := by
  intro h
  exact loopSpeed_ne_zero hN (by rw [← logLift_endpoint N, h, sub_self])

theorem hasDerivAt_loopHistory (N : ℤ) (t : ℝ) :
    HasDerivAt (loopHistory N) (loopSpeed N * loopHistory N t) t := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (loopSpeed N * z))
      (Complex.exp (loopSpeed N * (t : ℂ)) * loopSpeed N) (t : ℂ) := by
    simpa using ((hasDerivAt_id ((t : ℂ))).const_mul (loopSpeed N)).cexp
  have h2 := h.comp_ofReal
  rw [mul_comm] at h2
  exact h2

theorem deriv_loopHistory (N : ℤ) (t : ℝ) :
    deriv (loopHistory N) t = loopSpeed N * loopHistory N t :=
  (hasDerivAt_loopHistory N t).deriv

/-- The logarithmic-derivative integrand of the loop is constant. -/
theorem loopLogDerivative (N : ℤ) (t : ℝ) :
    (loopHistory N t)⁻¹ * deriv (loopHistory N) t = loopSpeed N := by
  rw [deriv_loopHistory, mul_comm (loopSpeed N) (loopHistory N t), ← mul_assoc,
    inv_mul_cancel₀ (loopHistory_ne_zero N t), one_mul]

/-- **The winding number is recovered from the determinant history.** -/
theorem winding_integral (N : ℤ) :
    ∫ t in (0 : ℝ)..1, (loopHistory N t)⁻¹ * deriv (loopHistory N) t = loopSpeed N := by
  rw [intervalIntegral.integral_congr (g := fun _ => loopSpeed N)
    (fun t _ => loopLogDerivative N t), intervalIntegral.integral_const]
  simp

theorem winding_number_eq (N : ℤ) :
    (2 * Real.pi * Complex.I)⁻¹ * ∫ t in (0 : ℝ)..1, (loopHistory N t)⁻¹ * deriv (loopHistory N) t
      = (N : ℂ) := by
  rw [winding_integral, loopSpeed]
  have hne : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  field_simp

/-- **Closed exact observation can have open lifted history.**  The `N`-fold determinant loop is
acyclic at every time, has constant positive shadow one and closed determinant history, yet its
logarithmic lift is open with endpoint increment `2πiN`, and that increment is exactly the
logarithmic-derivative integral. -/
theorem closed_observation_open_lift {N : ℤ} (hN : N ≠ 0) :
    (∀ t : ℝ, LinearMap.ker (torsionDifferential (loopHistory N t)) = ⊥ ∧
        LinearMap.range (torsionDifferential (loopHistory N t)) = ⊤) ∧
      (∀ t : ℝ, positiveShadow (loopHistory N t) = 1) ∧
      loopHistory N 0 = 1 ∧ loopHistory N 1 = 1 ∧
      logLift N 1 ≠ logLift N 0 ∧
      logLift N 1 - logLift N 0 = 2 * Real.pi * Complex.I * N ∧
      (2 * Real.pi * Complex.I)⁻¹ *
          ∫ t in (0 : ℝ)..1, (loopHistory N t)⁻¹ * deriv (loopHistory N) t = (N : ℂ) :=
  ⟨fun t => ⟨torsionDifferential_ker _ (loopHistory_ne_zero N t),
      torsionDifferential_range _ (loopHistory_ne_zero N t)⟩,
    positiveShadow_loopHistory N, loopHistory_zero N, loopHistory_one N,
    logLift_ne_of_ne_zero hN, logLift_endpoint N, winding_number_eq N⟩

end OpenLift

end GaloisForLFunctions.HTGeometry
