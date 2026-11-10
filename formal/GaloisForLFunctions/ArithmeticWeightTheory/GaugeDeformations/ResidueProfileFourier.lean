import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingMoment
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Principal and nonprincipal profiles of residue-class phases

Finite character inversion separates the principal average from the
nonprincipal arithmetic modulation. Common endpoint values force every
nonprincipal deviation to have zero endpoint mass. The principal average
retains the imaginary endpoint tangent of the unit profiles.
-/

open Complex Filter Topology Metric Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {q : ℕ} [NeZero q]

/-- Uniform real mass on the reduced residue classes. -/
def residueClassWeight (q : ℕ) [NeZero q] : ℝ :=
  (Fintype.card (ZMod q)ˣ : ℝ)⁻¹

theorem residueClassWeight_card : residueClassWeight q * (Fintype.card (ZMod q)ˣ : ℝ) = 1 := by
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem sum_residueClassWeight : (∑ _a : (ZMod q)ˣ, residueClassWeight q) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  exact residueClassWeight_card

/-- The principal-character average of the actual residue profiles. -/
def residueAverage (Φ : (ZMod q)ˣ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, (residueClassWeight q : ℂ) * Φ a z

/-- The Fourier coefficient of the deviation from the trivial phase. -/
def residueFourierDeviation (Φ : (ZMod q)ˣ → ℂ → ℂ)
    (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  (residueClassWeight q : ℂ) * ∑ a : (ZMod q)ˣ, (χ⁻¹) a * (Φ a z - 1)

/-- Adding one makes the Fourier deviation compatible with the canonical
Taylor coefficients of a normalized profile. -/
def residueFourierProfile (Φ : (ZMod q)ˣ → ℂ → ℂ)
    (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  1 + residueFourierDeviation Φ χ z

omit [NeZero q] in
private theorem inverse_character_unit (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    (χ⁻¹) (a : ZMod q) = χ ((a : ZMod q)⁻¹) := by
  rw [MulChar.inv_apply, Ring.inverse_of_isUnit a.isUnit]
  simp

private theorem residue_character_kernel (a b : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, (χ⁻¹) a * χ b) =
      if a = b then (Fintype.card (ZMod q)ˣ : ℂ) else 0 := by
  simp_rw [inverse_character_unit]
  simpa only [Units.ext_iff, ZMod.card_units_eq_totient] using
    DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit b

private theorem sum_residue_character_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ a : (ZMod q)ˣ, χ a = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul, ← Units.val_mul] using
    (Fintype.sum_equiv (Equiv.mulLeft b)
      (fun a : (ZMod q)ˣ => χ (↑(b * a) : ZMod q)) (fun a : (ZMod q)ˣ => χ a)
      (fun a => rfl))

/-- Finite Fourier inversion is applied to the actual phase values. -/
theorem residueFourier_inversion (Φ : (ZMod q)ˣ → ℂ → ℂ) (b : (ZMod q)ˣ) (z : ℂ) :
    (∑ χ : DirichletCharacter ℂ q, residueFourierDeviation Φ χ z * χ b) = Φ b z - 1 := by
  classical
  have hmass : (residueClassWeight q : ℂ) * (Fintype.card (ZMod q)ˣ : ℂ) = 1 := by
    exact_mod_cast (residueClassWeight_card (q := q))
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, ∑ a : (ZMod q)ˣ,
        (residueClassWeight q : ℂ) * ((χ⁻¹) a * χ b) * (Φ a z - 1) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [residueFourierDeviation, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a : (ZMod q)ˣ, (residueClassWeight q : ℂ) * (Φ a z - 1) *
        ∑ χ : DirichletCharacter ℂ q, (χ⁻¹) a * χ b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = ∑ a : (ZMod q)ˣ, (residueClassWeight q : ℂ) * (Φ a z - 1) *
        (if a = b then (Fintype.card (ZMod q)ˣ : ℂ) else 0) := by
      simp_rw [residue_character_kernel]
    _ = (residueClassWeight q : ℂ) * (Φ b z - 1) * (Fintype.card (ZMod q)ˣ : ℂ) := by
      rw [Finset.sum_eq_single b]
      · simp only [ite_true]
      · intro a _ hab
        rw [if_neg hab, mul_zero]
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    _ = Φ b z - 1 := by
      rw [mul_right_comm, hmass, one_mul]

/-- The principal Fourier profile is exactly the arithmetic average. -/
theorem residueFourierProfile_one (Φ : (ZMod q)ˣ → ℂ → ℂ) (z : ℂ) :
    residueFourierProfile Φ 1 z = residueAverage Φ z := by
  have hmass : (∑ _a : (ZMod q)ˣ, (residueClassWeight q : ℂ)) = 1 := by
    exact_mod_cast (sum_residueClassWeight (q := q))
  simp only [residueFourierProfile, residueFourierDeviation, residueAverage,
    inv_one, MulChar.one_apply_coe, one_mul, Finset.mul_sum, mul_sub,
    mul_one, Finset.sum_sub_distrib, hmass]
  ring

theorem residueFourierDeviation_one (Φ : (ZMod q)ˣ → ℂ → ℂ) (z : ℂ) :
    residueFourierDeviation Φ 1 z = residueAverage Φ z - 1 := by
  have h := residueFourierProfile_one Φ z
  change 1 + residueFourierDeviation Φ 1 z = residueAverage Φ z at h
  linear_combination h

theorem analyticOnNhd_residueFourierProfile {Φ : (ZMod q)ˣ → ℂ → ℂ} {R : NNReal}
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R)) (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (residueFourierProfile Φ χ) (closedBall 0 R) := by
  intro z hz
  have ha : AnalyticAt ℂ (∑ a : (ZMod q)ˣ, fun w : ℂ => (χ⁻¹) a * (Φ a w - 1)) z :=
    Finset.univ.analyticAt_sum (fun a _ =>
      analyticAt_const.mul ((hΦ a z hz).sub analyticAt_const))
  have he : (∑ a : (ZMod q)ˣ, fun w : ℂ => (χ⁻¹) a * (Φ a w - 1)) =
      (fun w : ℂ => ∑ a : (ZMod q)ˣ, (χ⁻¹) a * (Φ a w - 1)) := by
    funext w
    simp only [Finset.sum_apply]
  rw [he] at ha
  exact analyticAt_const.add (analyticAt_const.mul ha)

theorem analyticOnNhd_residueAverage {Φ : (ZMod q)ˣ → ℂ → ℂ} {R : NNReal}
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R)) :
    AnalyticOnNhd ℂ (residueAverage Φ) (closedBall 0 R) := by
  have ha := analyticOnNhd_residueFourierProfile hΦ 1
  rwa [show residueFourierProfile Φ 1 = residueAverage Φ from funext (residueFourierProfile_one Φ)] at ha

theorem residueFourierProfile_zero {Φ : (ZMod q)ˣ → ℂ → ℂ}
    (h0 : ∀ a, Φ a 0 = 1) (χ : DirichletCharacter ℂ q) : residueFourierProfile Φ χ 0 = 1 := by
  simp only [residueFourierProfile, residueFourierDeviation, h0, sub_self,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- A nonprincipal character sees no endpoint deviation. -/
theorem residueFourierProfile_endpoint {Φ : (ZMod q)ˣ → ℂ → ℂ}
    (h1 : ∀ a, Φ a 1 = -1) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    residueFourierProfile Φ χ 1 = 1 := by
  have hi : χ⁻¹ ≠ 1 := by
    intro he
    apply hχ
    simpa only [inv_inv, inv_one] using congrArg (fun ψ : DirichletCharacter ℂ q => ψ⁻¹) he
  simp only [residueFourierProfile, residueFourierDeviation, h1,
    ← Finset.sum_mul, sum_residue_character_zero (χ⁻¹) hi, zero_mul, mul_zero, add_zero]

theorem residueAverage_zero {Φ : (ZMod q)ˣ → ℂ → ℂ}
    (h0 : ∀ a, Φ a 0 = 1) : residueAverage Φ 0 = 1 := by
  have h := residueFourierProfile_zero h0 (1 : DirichletCharacter ℂ q)
  rwa [residueFourierProfile_one] at h

theorem residueAverage_one {Φ : (ZMod q)ˣ → ℂ → ℂ}
    (h1 : ∀ a, Φ a 1 = -1) : residueAverage Φ 1 = -1 := by
  have hm : (∑ _a : (ZMod q)ˣ, (residueClassWeight q : ℂ)) = 1 := by
    exact_mod_cast (sum_residueClassWeight (q := q))
  simp only [residueAverage, h1, mul_neg, mul_one, Finset.sum_neg_distrib, hm]

/-- The principal mean retains the normalized endpoints and imaginary tangent. -/
theorem residueAverage_properties {Φ : (ZMod q)ˣ → ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (h0 : ∀ a, Φ a 0 = 1) (h1 : ∀ a, Φ a 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1) :
    AnalyticOnNhd ℂ (residueAverage Φ) (closedBall 0 R) ∧
      residueAverage Φ 0 = 1 ∧ residueAverage Φ 1 = -1 ∧ (deriv (residueAverage Φ) 1).re = 0 := by
  exact analyticPhase_affine_average Finset.univ (fun _ => residueClassWeight q) Φ hR
    sum_residueClassWeight (fun a _ => hΦ a) (fun a _ => h0 a) (fun a _ => h1 a)
    (fun a _ => hu a)

#print axioms residueFourier_inversion
#print axioms residueFourierProfile_endpoint
#print axioms residueAverage_properties
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
