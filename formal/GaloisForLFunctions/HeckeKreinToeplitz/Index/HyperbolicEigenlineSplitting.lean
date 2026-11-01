import GaloisForLFunctions.HeckeKreinToeplitz.Index.PositiveEigenlineCoefficients

/-!
# Splitting off two reflected null eigenlines

Two common null eigenvectors with pairing one span an invariant hyperbolic
plane. The coefficient of any vector is its positive orthogonal remainder
plus the hyperbolic pair determined by its two null coordinates.
-/

noncomputable section
set_option autoImplicit false
open Complex Module
open scoped ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pairing_sub_right (u v w : H × ℂ) :
    pairing u (v - w) = pairing u v - pairing u w := (pairingLinear u).map_sub v w

theorem pairing_sub_left (u v w : H × ℂ) :
    pairing (u - v) w = pairing u w - pairing v w := by
  rw [← pairing_conj_symm, pairing_sub_right, map_sub, pairing_conj_symm, pairing_conj_symm]

/-- Orthogonal remainder after removing both null coordinates. -/
def hyperbolicRemainder (w v u : H × ℂ) : H × ℂ :=
  u - pairing v u • w - pairing w u • v

theorem hyperbolicRemainder_decomposition (w v u : H × ℂ) :
    u = hyperbolicRemainder w v u + pairing v u • w + pairing w u • v := by
  unfold hyperbolicRemainder
  abel

theorem hyperbolicRemainder_orthogonal {w v : H × ℂ}
    (hw : pairing w w = 0) (hv : pairing v v = 0) (hwv : pairing w v = 1)
    (u : H × ℂ) :
    pairing w (hyperbolicRemainder w v u) = 0 ∧
      pairing v (hyperbolicRemainder w v u) = 0 := by
  have hvw : pairing v w = 1 := by rw [← pairing_conj_symm, hwv, map_one]
  constructor
  · rw [hyperbolicRemainder, pairing_sub_right, pairing_sub_right,
      pairing_smul_right, pairing_smul_right, hw, hwv, mul_zero, mul_one, sub_zero, sub_self]
  · rw [hyperbolicRemainder, pairing_sub_right, pairing_sub_right,
      pairing_smul_right, pairing_smul_right, hv, hvw, mul_zero, mul_one, sub_self, sub_zero]

theorem pairing_hyperbolic_sum {w v r s : H × ℂ}
    (hw : pairing w w = 0) (hv : pairing v v = 0) (hwv : pairing w v = 1)
    (hrw : pairing w r = 0) (hrv : pairing v r = 0)
    (hsw : pairing w s = 0) (hsv : pairing v s = 0) (a b c d : ℂ) :
    pairing (r + a • w + b • v) (s + c • w + d • v) =
      pairing r s + conj a * d + conj b * c := by
  have hvw : pairing v w = 1 := by rw [← pairing_conj_symm, hwv, map_one]
  have hrw' : pairing r w = 0 := by rw [← pairing_conj_symm, hrw, map_zero]
  have hrv' : pairing r v = 0 := by rw [← pairing_conj_symm, hrv, map_zero]
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
    hw, hv, hwv, hvw, hrw', hrv', hsw, hsv, mul_zero, mul_one, add_zero, zero_add]
  ring

variable {G : Type*} [Group G]

/-- A reflected common null pair splits every coefficient into a positive kernel and one pair. -/
theorem exists_positive_hyperbolic_remainder
    (ρ : G →* End ℂ (H × ℂ))
    (hρ : ∀ g u v, pairing (ρ g u) (ρ g v) = pairing u v)
    (χ : G →* ℂ) {w v : H × ℂ}
    (hw : ∀ g, ρ g w = χ g • w)
    (hv : ∀ g, ρ g v = reflectChar χ g • v)
    (hwq : pairing w w = 0) (hvq : pairing v v = 0) (hwv : pairing w v = 1)
    (u : H × ℂ) :
    ∃ p : G → ℂ, IsPosDefKernel p ∧ ∀ g,
      pairing u (ρ g u) = p g + pairKernel χ (conj (pairing w u) * pairing v u) g := by
  let r := hyperbolicRemainder w v u
  have hr := hyperbolicRemainder_orthogonal hwq hvq hwv u
  have hw0 : w ≠ 0 := by
    intro he
    rw [he] at hwv
    simp only [pairing, Prod.fst_zero, Prod.snd_zero, inner_zero_left, map_zero,
      zero_mul, sub_zero] at hwv
    exact zero_ne_one hwv
  let p : G → ℂ := fun g => pairing r (ρ g r)
  have hp : IsPosDefKernel p :=
    isPosDefCoefficient_of_nonpositive_eigenvector ρ hρ χ hw hw0 (by rw [hwq]; rfl) hr.1
  refine ⟨p, hp, fun g => ?_⟩
  have hsrw : pairing w (ρ g r) = 0 := by
    rw [pairing_action_right ρ hρ χ hw, hr.1, mul_zero]
  have hsrv : pairing v (ρ g r) = 0 := by
    rw [pairing_action_right ρ hρ (reflectChar χ) hv, hr.2, mul_zero]
  have hdec := hyperbolicRemainder_decomposition w v u
  have hact : ρ g u = ρ g r + (pairing v u * χ g) • w +
      (pairing w u * reflectChar χ g) • v := by
    calc
      ρ g u = ρ g (r + pairing v u • w + pairing w u • v) := congrArg (ρ g) hdec
      _ = _ := by rw [map_add, map_add, map_smul, map_smul, hw, hv, smul_smul, smul_smul]
  calc
    pairing u (ρ g u) =
        pairing (r + pairing v u • w + pairing w u • v)
          (ρ g r + (pairing v u * χ g) • w + (pairing w u * reflectChar χ g) • v) :=
      congrArg₂ pairing hdec hact
    _ = pairing r (ρ g r) + conj (pairing v u) * (pairing w u * reflectChar χ g) +
        conj (pairing w u) * (pairing v u * χ g) :=
      pairing_hyperbolic_sum hwq hvq hwv hr.1 hr.2 hsrw hsrv _ _ _ _
    _ = p g + pairKernel χ (conj (pairing w u) * pairing v u) g := by
      simp only [p, pairKernel, map_mul, conj_conj]
      ring

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
