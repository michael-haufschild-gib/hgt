import GaloisForLFunctions.RHTower.ProlateEndpointNonvanishing

/-!
# Endpoint-normalized radial prolate modes

The regular radial solution is canonically normalized by its nonzero singular-endpoint value.
This removes every arbitrary eigenvector scale before comparison with the Dunster `J_0` branch.
-/

noncomputable section

namespace RHTower

/-- Normalize a real-line profile to value one at the radial endpoint. -/
def prolateEndpointNormalize (Phi : ℝ → ℝ) (x : ℝ) : ℝ := Phi x / Phi 1

theorem prolateEndpointNormalize_one {Phi : ℝ → ℝ} (hPhi : Phi 1 ≠ 0) :
    prolateEndpointNormalize Phi 1 = 1 := by
  exact div_self hPhi

theorem contDiff_prolateEndpointNormalize {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateEndpointNormalize Phi) := by
  unfold prolateEndpointNormalize
  fun_prop

theorem even_prolateEndpointNormalize {Phi : ℝ → ℝ} (hPhi : Function.Even Phi) :
    Function.Even (prolateEndpointNormalize Phi) := by
  intro x
  unfold prolateEndpointNormalize
  rw [show Phi (-x) = Phi x from hPhi x]

theorem deriv_prolateEndpointNormalize {Phi : ℝ → ℝ}
    (hPhi : Differentiable ℝ Phi) (x : ℝ) :
    deriv (prolateEndpointNormalize Phi) x = deriv Phi x / Phi 1 := by
  unfold prolateEndpointNormalize
  simpa using deriv_div_const (c := Phi 1) (hPhi x)

theorem deriv2_prolateEndpointNormalize {Phi : ℝ → ℝ}
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi)) (x : ℝ) :
    deriv (deriv (prolateEndpointNormalize Phi)) x = deriv (deriv Phi) x / Phi 1 := by
  have hfun : deriv (prolateEndpointNormalize Phi) = fun y => deriv Phi y / Phi 1 := by
    funext y
    exact deriv_prolateEndpointNormalize hPhi1 y
  rw [hfun]
  simpa using deriv_div_const (c := Phi 1) (hPhi2 x)

/-- Endpoint normalization preserves the global prolate eigen-equation. -/
theorem prolateSLAction_endpointNormalize
    {c chi : ℝ} {Phi : ℝ → ℝ}
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi))
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    ∀ x : ℝ,
      prolateSLAction c (prolateEndpointNormalize Phi) x =
        chi * prolateEndpointNormalize Phi x := by
  intro x
  simp only [prolateSLAction, prolateEndpointNormalize,
    deriv_prolateEndpointNormalize hPhi1,
    deriv2_prolateEndpointNormalize hPhi1 hPhi2]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hx := heig x
  simp only [prolateSLAction] at hx
  linear_combination (Phi 1)⁻¹ * hx

/-- Endpoint normalization preserves the exterior radial equation. -/
theorem radialProlate_ode_endpointNormalize
    {s c : ℝ} {Phi : ℝ → ℝ}
    (hPhi1 : Differentiable ℝ Phi) (hPhi2 : Differentiable ℝ (deriv Phi))
    (hradial : ∀ x : ℝ,
      (x ^ 2 - 1) * deriv (deriv Phi) x + 2 * x * deriv Phi x
        - (s * c ^ 2 - c ^ 2 * x ^ 2) * Phi x = 0) :
    ∀ x : ℝ,
      (x ^ 2 - 1) * deriv (deriv (prolateEndpointNormalize Phi)) x
          + 2 * x * deriv (prolateEndpointNormalize Phi) x
        - (s * c ^ 2 - c ^ 2 * x ^ 2) * prolateEndpointNormalize Phi x = 0 := by
  intro x
  simp only [prolateEndpointNormalize,
    deriv_prolateEndpointNormalize hPhi1,
    deriv2_prolateEndpointNormalize hPhi1 hPhi2]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  linear_combination (Phi 1)⁻¹ * hradial x

/-- The normalized endpoint derivative is fixed by the radial separation ratio. -/
theorem two_mul_deriv_endpointNormalize_one
    {s c : ℝ} {Phi : ℝ → ℝ} (hPhi : Differentiable ℝ Phi) (hPhiOne : Phi 1 ≠ 0)
    (hend : 2 * deriv Phi 1 = (s * c ^ 2 - c ^ 2) * Phi 1) :
    2 * deriv (prolateEndpointNormalize Phi) 1 = s * c ^ 2 - c ^ 2 := by
  rw [deriv_prolateEndpointNormalize hPhi]
  field_simp [hPhiOne]
  calc
    2 * deriv Phi 1 = (s * c ^ 2 - c ^ 2) * Phi 1 := hend
    _ = Phi 1 * c ^ 2 * (s - 1) := by ring

/-- Every live signed mode supplies an exact, smooth, even, endpoint-normalized regular radial
solution. -/
theorem exists_endpointNormalized_radialProlate_of_signedMode
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ (Phi R : ℝ → ℝ) (chi s : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧ Phi ≠ 0 ∧ Function.Even Phi ∧
        Phi 1 ≠ 0 ∧ R = prolateEndpointNormalize Phi ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R ∧ Function.Even R ∧ R 1 = 1 ∧
        (∀ x : ℝ,
          bandTransform (2 * Real.pi * a ^ 2) Phi x =
            evenProlateSignedValue a n ^ 2 * Phi x) ∧
        (∀ x : ℝ,
          prolateSLAction (2 * Real.pi * a ^ 2) R x = chi * R x) ∧
        s = radialSeparationRatio (2 * Real.pi * a ^ 2) chi ∧ 0 ≤ s ∧
        2 * deriv R 1 = s * (2 * Real.pi * a ^ 2) ^ 2
            - (2 * Real.pi * a ^ 2) ^ 2 ∧
        (∀ x : ℝ,
          (x ^ 2 - 1) * deriv (deriv R) x + 2 * x * deriv R x
            - (s * (2 * Real.pi * a ^ 2) ^ 2
                - (2 * Real.pi * a ^ 2) ^ 2 * x ^ 2) * R x = 0) := by
  obtain ⟨Phi, chi, s, hsm, hne, heven, hone, hband, heig, hs, hs0, hend, hradial⟩ :=
    exists_global_even_radialProlate_endpoint_ne_zero_of_signedMode ha n hvalue
  have hPhi1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hPhi2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  let R := prolateEndpointNormalize Phi
  refine ⟨Phi, R, chi, s, hsm, hne, heven, hone, rfl,
    contDiff_prolateEndpointNormalize hsm, even_prolateEndpointNormalize heven,
    prolateEndpointNormalize_one hone, hband, ?_, hs, hs0, ?_, ?_⟩
  · exact prolateSLAction_endpointNormalize hPhi1 hPhi2 heig
  · exact two_mul_deriv_endpointNormalize_one hPhi1 hone hend
  · exact radialProlate_ode_endpointNormalize hPhi1 hPhi2 hradial

end RHTower

end
