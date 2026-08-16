import Mathlib

/-!
# The semilocal prolate control deformation

The one-prime cyclic prolate candidate and the transported archimedean control differ only in their
grading term.  Writing `θ` for the Sonin intertwiner and

`K_p = N_p - θ N_∞ θ⁻¹`

for the pure grading deformation, the two formal expressions satisfy

`W^cyc_{λ,p} = W^θ_{λ,p} + λ² K_p`.

Under a common closed realization the second resolvent identity turns this into

`R_cyc - R_θ = -λ² R_cyc K_p R_θ`,

and compressing by the two Sonin projections splits the cyclic relative-resolvent corner as

`C_cyc = C_θ - λ² (1 - Q_p) R_cyc K_p R_θ η_p Q_∞`.

Everything here is ring algebra: the analytic content of the card is exactly the hypothesis that a
common closed realization exists, which is carried as an explicit resolvent hypothesis.

## Main results

* `conj_prolate` — conjugating the archimedean expression gives the transported control;
* `cyclic_eq_transported_add_deformation` — identity (2);
* `second_resolvent_identity` — identity (3);
* `relativeCorner_split` — identity (4).
-/

noncomputable section

namespace RHTower

variable {A : Type*} [Ring A]

theorem conj_mul (θ : Aˣ) (x y : A) :
    (θ : A) * (x * y) * (↑θ⁻¹ : A)
      = ((θ : A) * x * (↑θ⁻¹ : A)) * ((θ : A) * y * (↑θ⁻¹ : A)) := by
  have h : (↑θ⁻¹ : A) * (θ : A) = 1 := θ.inv_mul
  calc (θ : A) * (x * y) * (↑θ⁻¹ : A)
      = (θ : A) * x * ((↑θ⁻¹ : A) * (θ : A)) * y * (↑θ⁻¹ : A) := by rw [h]; noncomm_ring
    _ = ((θ : A) * x * (↑θ⁻¹ : A)) * ((θ : A) * y * (↑θ⁻¹ : A)) := by noncomm_ring

/-! ### The second resolvent identity -/

set_option linter.unusedVariables false in
/-- **Identity (3).**  If two closed realizations differ by `V` and both are invertible at `z`, their
resolvents differ by the sandwiched perturbation. -/
theorem second_resolvent_identity {W₁ W₂ V R₁ R₂ z : A}
    (hW : W₁ = W₂ + V)
    (h₁ : R₁ * (W₁ - z) = 1) (h₁' : (W₁ - z) * R₁ = 1)
    (h₂ : R₂ * (W₂ - z) = 1) (h₂' : (W₂ - z) * R₂ = 1) :
    R₁ - R₂ = -(R₁ * V * R₂) := by
  have hstep : R₁ * ((W₂ - z) * R₂) - (R₁ * (W₁ - z)) * R₂ = R₁ - R₂ := by
    rw [h₂', h₁, mul_one, one_mul]
  have hdiff : (W₂ - z) - (W₁ - z) = -V := by
    rw [hW]; abel
  calc R₁ - R₂ = R₁ * ((W₂ - z) * R₂) - (R₁ * (W₁ - z)) * R₂ := hstep.symm
    _ = R₁ * ((W₂ - z) - (W₁ - z)) * R₂ := by noncomm_ring
    _ = R₁ * (-V) * R₂ := by rw [hdiff]
    _ = -(R₁ * V * R₂) := by noncomm_ring

/-! ### The relative-resolvent corner -/

/-- The Sonin relative-resolvent corner of a realization. -/
def relativeCorner (Qp Qinf etap R Rinf : A) : A :=
  (1 - Qp) * (R * etap - etap * Rinf) * Qinf

variable [Algebra ℂ A]

/-! ### The formal prolate expressions -/

/-- The formal prolate expression `-D² + λ² N`. -/
def prolateExpr (D N : A) (lam : ℂ) : A := -(D * D) + (lam ^ 2) • N

/-- The pure grading deformation `K_p = N_p - θ N_∞ θ⁻¹`. -/
def gradingDeformation (Np : A) (θ : Aˣ) (Ninf : A) : A :=
  Np - (θ : A) * Ninf * ((↑θ⁻¹ : A))

theorem conj_smul (θ : Aˣ) (c : ℂ) (x : A) :
    (θ : A) * (c • x) * (↑θ⁻¹ : A) = c • ((θ : A) * x * (↑θ⁻¹ : A)) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  have hcomm : (algebraMap ℂ A c) * (θ : A) = (θ : A) * (algebraMap ℂ A c) :=
    Algebra.commutes c _
  calc (θ : A) * (algebraMap ℂ A c * x) * (↑θ⁻¹ : A)
      = ((θ : A) * algebraMap ℂ A c) * x * (↑θ⁻¹ : A) := by noncomm_ring
    _ = (algebraMap ℂ A c * (θ : A)) * x * (↑θ⁻¹ : A) := by rw [hcomm]
    _ = algebraMap ℂ A c * ((θ : A) * x * (↑θ⁻¹ : A)) := by noncomm_ring

/-- **The transported control.**  Conjugating the archimedean prolate expression by the Sonin
intertwiner replaces the scaling generator and transports the grading. -/
theorem conj_prolate (θ : Aˣ) (Dinf Dp Ninf : A) (lam : ℂ)
    (hD : (θ : A) * Dinf * (↑θ⁻¹ : A) = Dp) :
    (θ : A) * prolateExpr Dinf Ninf lam * (↑θ⁻¹ : A)
      = prolateExpr Dp ((θ : A) * Ninf * (↑θ⁻¹ : A)) lam := by
  rw [prolateExpr, prolateExpr, mul_add, add_mul, ← hD]
  congr 1
  · rw [show (θ : A) * (-(Dinf * Dinf)) = -((θ : A) * (Dinf * Dinf)) by noncomm_ring, neg_mul,
      conj_mul]
  · rw [conj_smul]

/-- **Identity (2).**  The cyclic candidate is the transported control plus the pure grading
deformation. -/
theorem cyclic_eq_transported_add_deformation (Dp Np Ninf : A) (θ : Aˣ) (lam : ℂ) :
    prolateExpr Dp Np lam
      = prolateExpr Dp ((θ : A) * Ninf * (↑θ⁻¹ : A)) lam
        + (lam ^ 2) • gradingDeformation Np θ Ninf := by
  rw [prolateExpr, prolateExpr, gradingDeformation, smul_sub]
  abel

/-- **Identity (4).**  The cyclic corner is the transported corner plus the compressed correction
term produced by the grading deformation. -/
theorem relativeCorner_split {Wcyc Wθ Rcyc Rθ Rinf z Kp Qp Qinf etap : A} (lam : ℂ)
    (hW : Wcyc = Wθ + (lam ^ 2) • Kp)
    (h₁ : Rcyc * (Wcyc - z) = 1) (h₁' : (Wcyc - z) * Rcyc = 1)
    (h₂ : Rθ * (Wθ - z) = 1) (h₂' : (Wθ - z) * Rθ = 1) :
    relativeCorner Qp Qinf etap Rcyc Rinf
      = relativeCorner Qp Qinf etap Rθ Rinf
        - (lam ^ 2) • ((1 - Qp) * (Rcyc * Kp * Rθ) * etap * Qinf) := by
  have hres : Rcyc - Rθ = -(Rcyc * ((lam ^ 2) • Kp) * Rθ) :=
    second_resolvent_identity hW h₁ h₁' h₂ h₂'
  have hsmul : Rcyc * ((lam ^ 2) • Kp) * Rθ = (lam ^ 2) • (Rcyc * Kp * Rθ) := by
    rw [mul_smul_comm, smul_mul_assoc]
  rw [hsmul] at hres
  rw [relativeCorner, relativeCorner]
  have hsplit : Rcyc * etap - etap * Rinf
      = (Rθ * etap - etap * Rinf) + (Rcyc - Rθ) * etap := by noncomm_ring
  rw [hsplit, hres]
  rw [mul_add, add_mul]
  rw [show (-((lam ^ 2) • (Rcyc * Kp * Rθ))) * etap
      = -((lam ^ 2) • (Rcyc * Kp * Rθ * etap)) by
    rw [neg_mul, smul_mul_assoc]]
  rw [show (1 - Qp) * (-((lam ^ 2) • (Rcyc * Kp * Rθ * etap)))
      = -((lam ^ 2) • ((1 - Qp) * (Rcyc * Kp * Rθ * etap))) by
    rw [mul_neg, mul_smul_comm]]
  rw [show (-((lam ^ 2) • ((1 - Qp) * (Rcyc * Kp * Rθ * etap)))) * Qinf
      = -((lam ^ 2) • ((1 - Qp) * (Rcyc * Kp * Rθ * etap) * Qinf)) by
    rw [neg_mul, smul_mul_assoc]]
  rw [sub_eq_add_neg]
  noncomm_ring

end RHTower
