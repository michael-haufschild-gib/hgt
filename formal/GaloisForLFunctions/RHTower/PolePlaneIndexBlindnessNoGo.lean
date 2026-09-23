import GaloisForLFunctions.RHTower.CountermodelCarrierHyperbolicPlane
import GaloisForLFunctions.RHTower.CompletedZetaPolePlane

/-!
# The pole plane is blind to the index

The completed zeta function `Λ = Λ₀ + P` has polar part `P(s) = -1/s - 1/(1-s)`: one hyperbolic
pole plane, exchanged by the functional equation.  Multiplying `Λ` by the normalized off-line
quartet `Q(s)/Q(0)` of the entire countermodel gives a function

`Λ_Q(s) = Λ(s) Q(s)/Q(0)`

with **exactly the same functional equation and exactly the same polar part**: `Λ_Q = E_Q + P`
with `E_Q` entire, because `P(s)(Q(s)/Q(0) - 1)` is a polynomial.  Yet `Λ_Q` vanishes at the two
upper-half-plane points `1/2 ± a₀ + iγ`, whose seam carrier is two hyperbolic planes.

Hence the boundary datum "functional equation, Gamma factor, one simple pole at `0` and one at `1`
with residues `∓1`" does not determine the index of the primitive part.  Any law of the form
"the completion boundary is one hyperbolic plane, therefore the natural form has exactly one
positive square" is refuted: the boundary is identical for `Λ` and `Λ_Q`, and `Λ_Q` carries two
extra positive squares.
-/

open Complex GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The quartet as a quadratic in `s(s-1)` -/

/-- The off-line root `1/2 + a₀ + iγ`. -/
def quartetRoot (a0 gam : ℝ) : ℂ := ((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I

/-- The conjugate off-line root `1/2 + a₀ - iγ`. -/
def quartetRootConj (a0 gam : ℝ) : ℂ := ((1 / 2 + a0 : ℝ) : ℂ) - (gam : ℂ) * I

/-- `c = ρ(1-ρ)` for the off-line root. -/
def quartetC (a0 gam : ℝ) : ℂ := quartetRoot a0 gam * (1 - quartetRoot a0 gam)

/-- `c' = ρ̄(1-ρ̄)` for the conjugate root. -/
def quartetC' (a0 gam : ℝ) : ℂ := quartetRootConj a0 gam * (1 - quartetRootConj a0 gam)

/-- The quartet is `(s(s-1) + c)(s(s-1) + c')`. -/
theorem offLineQuartet_eq_quadratic (a0 gam : ℝ) (s : ℂ) :
    offLineQuartet a0 gam s = (s * (s - 1) + quartetC a0 gam) * (s * (s - 1) + quartetC' a0 gam) := by
  unfold offLineQuartet quartetC quartetC' quartetRoot quartetRootConj
  push_cast
  ring

/-- The quartet at `0` is `c c'`. -/
theorem offLineQuartet_zero_eq_mul (a0 gam : ℝ) :
    offLineQuartet a0 gam 0 = quartetC a0 gam * quartetC' a0 gam := by
  rw [offLineQuartet_eq_quadratic]
  ring

theorem quartetRoot_ne_zero {a0 : ℝ} (ha0 : 0 < a0) (gam : ℝ) : quartetRoot a0 gam ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [quartetRoot] at this
  linarith

theorem quartetRoot_ne_one {a0 : ℝ} (ha1 : a0 < 1 / 2) (gam : ℝ) : quartetRoot a0 gam ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [quartetRoot] at this
  linarith

theorem quartetRootConj_ne_zero {a0 : ℝ} (ha0 : 0 < a0) (gam : ℝ) :
    quartetRootConj a0 gam ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [quartetRootConj] at this
  linarith

theorem quartetRootConj_ne_one {a0 : ℝ} (ha1 : a0 < 1 / 2) (gam : ℝ) :
    quartetRootConj a0 gam ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [quartetRootConj] at this
  linarith

theorem quartetC_ne_zero {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (gam : ℝ) :
    quartetC a0 gam ≠ 0 :=
  mul_ne_zero (quartetRoot_ne_zero ha0 gam) (sub_ne_zero.mpr (Ne.symm (quartetRoot_ne_one ha1 gam)))

theorem quartetC'_ne_zero {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (gam : ℝ) :
    quartetC' a0 gam ≠ 0 :=
  mul_ne_zero (quartetRootConj_ne_zero ha0 gam)
    (sub_ne_zero.mpr (Ne.symm (quartetRootConj_ne_one ha1 gam)))

/-- The quartet does not vanish at `0`. -/
theorem offLineQuartet_zero_ne_zero {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (gam : ℝ) :
    offLineQuartet a0 gam 0 ≠ 0 := by
  rw [offLineQuartet_zero_eq_mul]
  exact mul_ne_zero (quartetC_ne_zero ha0 ha1 gam) (quartetC'_ne_zero ha0 ha1 gam)

/-! ## The boundary-preserving twist -/

/-- The quartet twist `Λ_Q(s) = Λ(s) Q(s)/Q(0)`. -/
def completedZetaQuartetTwist (a0 gam : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta s * (offLineQuartet a0 gam s / offLineQuartet a0 gam 0)

/-- The twist satisfies the same functional equation as `Λ`. -/
theorem completedZetaQuartetTwist_one_sub (a0 gam : ℝ) (s : ℂ) :
    completedZetaQuartetTwist a0 gam (1 - s) = completedZetaQuartetTwist a0 gam s := by
  unfold completedZetaQuartetTwist
  rw [completedRiemannZeta_one_sub, offLineQuartet_reflect]

/-- The polynomial correction `(s² - s + c + c')/Q(0)`. -/
def quartetTwistCorrection (a0 gam : ℝ) (s : ℂ) : ℂ :=
  (s ^ (2 : ℕ) - s + (quartetC a0 gam + quartetC' a0 gam)) / offLineQuartet a0 gam 0

/-- **The polar part times the normalized quartet minus one is a polynomial.**  For `s ≠ 0, 1`,
`P(s)(Q(s)/Q(0) - 1) = (s² - s + c + c')/Q(0)`. -/
theorem polarPart_mul_quartet_ratio_sub_one {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (gam : ℝ)
    {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    completedZetaPolarPart s * (offLineQuartet a0 gam s / offLineQuartet a0 gam 0 - 1)
      = quartetTwistCorrection a0 gam s := by
  have hc := quartetC_ne_zero ha0 ha1 gam
  have hc' := quartetC'_ne_zero ha0 ha1 gam
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold completedZetaPolarPart quartetTwistCorrection
  rw [offLineQuartet_eq_quadratic, offLineQuartet_zero_eq_mul]
  field_simp
  ring

/-- The entire part of the twist. -/
def quartetTwistEntirePart (a0 gam : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta₀ s * (offLineQuartet a0 gam s / offLineQuartet a0 gam 0)
    + quartetTwistCorrection a0 gam s

/-- The entire part is entire. -/
theorem differentiable_quartetTwistEntirePart (a0 gam : ℝ) :
    Differentiable ℂ (quartetTwistEntirePart a0 gam) := by
  have hQ : Differentiable ℂ (offLineQuartet a0 gam) := by
    unfold offLineQuartet
    fun_prop
  have h1 : Differentiable ℂ
      (fun s => completedRiemannZeta₀ s * (offLineQuartet a0 gam s / offLineQuartet a0 gam 0)) :=
    differentiable_completedZeta₀.mul (hQ.div_const _)
  have h2 : Differentiable ℂ
      (fun s : ℂ => (s ^ (2 : ℕ) - s + (quartetC a0 gam + quartetC' a0 gam)) / offLineQuartet a0 gam 0) := by
    fun_prop
  exact h1.add h2

/-- **Same polar part.**  Off the two poles, `Λ_Q = E_Q + P` with `E_Q` entire and `P` the polar
part of `Λ` itself. -/
theorem completedZetaQuartetTwist_eq_entire_add_polar {a0 : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2)
    (gam : ℝ) {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    completedZetaQuartetTwist a0 gam s
      = quartetTwistEntirePart a0 gam s + completedZetaPolarPart s := by
  unfold completedZetaQuartetTwist quartetTwistEntirePart
  rw [completedRiemannZeta_eq_entire_add_polar, ← polarPart_mul_quartet_ratio_sub_one ha0 ha1 gam hs hs1]
  ring

/-- The twist vanishes at the off-line root. -/
theorem completedZetaQuartetTwist_eq_zero_root (a0 gam : ℝ) :
    completedZetaQuartetTwist a0 gam (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 := by
  unfold completedZetaQuartetTwist
  rw [offLineQuartet_eq_zero, zero_div, mul_zero]

/-- The twist vanishes at the reflected off-line root. -/
theorem completedZetaQuartetTwist_eq_zero_reflected (a0 gam : ℝ) :
    completedZetaQuartetTwist a0 gam (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 := by
  unfold completedZetaQuartetTwist
  rw [offLineQuartet_eq_zero_reflected, zero_div, mul_zero]

/-- **The pole plane is blind to the index.**  For `0 < a₀ < 1/2` and `γ > 0`: the quartet twist
has the functional equation of `Λ`; off the poles it is an entire function plus the polar part of
`Λ`, so it has the same simple poles at `0` and `1` with the same residues `-1, +1` and the same
residue pairing of inertia `(1,1)`; and it vanishes at the two distinct upper-half-plane points
`1/2 ± a₀ + iγ`, whose seam carrier has inertia `(2,2)`.  The boundary datum therefore carries no
information about the index of the primitive part. -/
theorem polePlane_index_blind {a0 gam : ℝ} (ha0 : 0 < a0) (ha1 : a0 < 1 / 2) (hgam : 0 < gam) :
    (∀ s : ℂ, completedZetaQuartetTwist a0 gam (1 - s) = completedZetaQuartetTwist a0 gam s) ∧
    Differentiable ℂ (quartetTwistEntirePart a0 gam) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      completedZetaQuartetTwist a0 gam s
        = quartetTwistEntirePart a0 gam s + completedZetaPolarPart s) ∧
    (∀ s : ℂ, completedRiemannZeta s = completedRiemannZeta₀ s + completedZetaPolarPart s) ∧
    completedZetaQuartetTwist a0 gam (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 ∧
    completedZetaQuartetTwist a0 gam (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 ∧
    (∃ z : Fin (2 * 2) → ℂ,
      SeamCarrierExactInertia
        ![(((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I),
          (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I)] z) :=
  ⟨completedZetaQuartetTwist_one_sub a0 gam,
    differentiable_quartetTwistEntirePart a0 gam,
    fun _ hs hs1 => completedZetaQuartetTwist_eq_entire_add_polar ha0 ha1 gam hs hs1,
    completedRiemannZeta_eq_entire_add_polar,
    completedZetaQuartetTwist_eq_zero_root a0 gam,
    completedZetaQuartetTwist_eq_zero_reflected a0 gam,
    (entireCountermodel_seam_two_hyperbolicPlanes ha0 hgam).2.2⟩

end

end RHTower
