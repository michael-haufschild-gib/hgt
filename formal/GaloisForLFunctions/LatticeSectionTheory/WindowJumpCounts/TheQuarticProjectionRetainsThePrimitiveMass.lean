import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.EvenCenteredPrimitiveMass
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicChargedGaps

/-!
# Primitive mass after a quartic Legendre projection

Subtract the primitive of the quartic projection before applying Wirtinger.
Integration by parts retains the exact low moments, including the interaction
of the fourth and sixth moments. Only the orthogonal residual pays the
Dirichlet constant.
-/

noncomputable section
open Real MeasureTheory Set intervalIntegral
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

private theorem integral_sq_sub {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    (∫ x in (0 : ℝ)..1, (F x - G x) ^ 2) =
      (∫ x in (0 : ℝ)..1, F x ^ 2) - 2 * (∫ x in (0 : ℝ)..1, F x * G x) +
        (∫ x in (0 : ℝ)..1, G x ^ 2) := by
  have he : (fun x => (F x - G x) ^ 2) =
      fun x => F x ^ 2 - 2 * (F x * G x) + G x ^ 2 := by funext x; ring
  rw [he, intervalIntegral.integral_add (μ := volume)
    (f := fun x => F x ^ 2 - 2 * (F x * G x)) (g := fun x => G x ^ 2)
    (((hF.pow 2).intervalIntegrable 0 1).sub ((hF.mul hG).intervalIntegrable 0 1 |>.const_mul 2))
    ((hG.pow 2).intervalIntegrable 0 1),
    intervalIntegral.integral_sub (μ := volume)
    (f := fun x => F x ^ 2) (g := fun x => 2 * (F x * G x))
    ((hF.pow 2).intervalIntegrable 0 1)
    ((hF.mul hG).intervalIntegrable 0 1 |>.const_mul 2), intervalIntegral.integral_const_mul]

private theorem primitive_projection_bound {G P K A : ℝ → ℝ}
    (hG : Continuous G) (hP : Continuous P)
    (hK : ∀ x, HasDerivAt K (P x) x) (hA : ∀ x, HasDerivAt A (K x) x)
    (hK0 : K 0 = 0) (hK1 : K 1 = ∫ x in (0 : ℝ)..1, G x) :
    (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2) ≤
      (1 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..1, (G x - P x) ^ 2) +
      2 * (∫ x in (0 : ℝ)..1, G x) * A 1 -
      2 * (∫ x in (0 : ℝ)..1, G x * A x) - (∫ x in (0 : ℝ)..1, K x ^ 2) := by
  let H := fun x => ∫ y in (0 : ℝ)..x, G y
  have hD (x : ℝ) : HasDerivAt H (G x) x := (hG.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun x => (hK x).continuousAt
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun x => (hA x).continuousAt
  have hw := HTGeometry.dirichlet_wirtinger_intervalIntegral
    (a := (0 : ℝ)) (b := 1) (by norm_num)
    (f := fun x => ((H x - K x : ℝ) : ℂ))
    (f' := fun x => ((G x - P x : ℝ) : ℂ))
    (fun x _ => ((hD x).sub (hK x)).ofReal_comp)
    (Complex.continuous_ofReal.comp (hG.sub hP)).continuousOn
    (by simp [H, hK0]) (by simp [H, hK1])
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero] at hw
  rw [integral_sq_sub hH hKc, show (1 / Real.pi) ^ 2 = 1 / Real.pi ^ 2 by ring] at hw
  have hibp := integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := fun x => H x * A x)
    (fun x _ => (hD x).mul (hA x))
    (((hG.mul hAc).add (hH.mul hKc)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (μ := volume)
    (f := fun x => G x * A x) (g := fun x => H x * K x)
    ((hG.mul hAc).intervalIntegrable 0 1)
    ((hH.mul hKc).intervalIntegrable 0 1)] at hibp
  change (∫ x in (0 : ℝ)..1, G x * A x) + (∫ x in (0 : ℝ)..1, H x * K x) =
    H 1 * A 1 - H 0 * A 0 at hibp
  simp only [H, integral_same, zero_mul, sub_zero] at hibp
  change (∫ x in (0 : ℝ)..1, H x ^ 2) ≤ _
  linarith only [hw, hibp]

/-- Retaining the quartic projection confines the Wirtinger loss to its residual mass. -/
theorem primitive_mass_le_quartic_projection {G : ℝ → ℝ} (hG : Continuous G) :
    let m := fun n : ℕ => ∫ x in (0 : ℝ)..1, G x * legP (2 * n) x
    (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..x, G y) ^ 2) ≤
      (1 / Real.pi ^ 2) * ((∫ x in (0 : ℝ)..1, G x ^ 2) -
        m 0 ^ 2 - 5 * m 1 ^ 2 - 9 * m 2 ^ 2) +
      (m 0 - m 1) ^ 2 / 3 + (m 1 - m 2) ^ 2 / 7 + m 2 ^ 2 / 11 -
        2 * m 2 * m 3 / 11 := by
  intro m
  let P := fun x => m 0 + 5 * m 1 * legP 2 x + 9 * m 2 * legP 4 x
  let K := fun x => (m 0 - m 1) * legP 1 x + (m 1 - m 2) * legP 3 x + m 2 * legP 5 x
  let A := fun x => (m 0 - m 1) * legP 2 x / 3 +
    (m 1 - m 2) * (legP 4 x - legP 2 x) / 7 + m 2 * (legP 6 x - legP 4 x) / 11
  have hP : Continuous P := by dsimp only [P]; fun_prop
  have hK : Continuous K := by dsimp only [K]; fun_prop
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hDK (x : ℝ) : HasDerivAt K (P x) x := by
    have h := (((hasDerivAt_legP 1 x).const_mul (m 0 - m 1)).add
      ((hasDerivAt_legP 3 x).const_mul (m 1 - m 2))).add
      ((hasDerivAt_legP 5 x).const_mul (m 2))
    apply h.congr_deriv
    dsimp only [P]
    norm_num [legP', legP]
    ring
  have hDA (x : ℝ) : HasDerivAt A (K x) x := by
    have h := ((((hasDerivAt_legP 2 x).const_mul (m 0 - m 1)).div_const 3).add
      ((((hasDerivAt_legP 4 x).sub (hasDerivAt_legP 2 x)).const_mul (m 1 - m 2)).div_const 7)).add
      ((((hasDerivAt_legP 6 x).sub (hasDerivAt_legP 4 x)).const_mul (m 2)).div_const 11)
    apply h.congr_deriv
    dsimp only [K]
    norm_num [legP', legP]
    ring
  have hm0 : m 0 = ∫ x in (0 : ℝ)..1, G x := by simp [m, legP]
  have hK0 : K 0 = 0 := by norm_num [K, legP]
  have hK1 : K 1 = ∫ x in (0 : ℝ)..1, G x := by
    norm_num [K, legP]
    exact hm0
  have hA1 : A 1 = (m 0 - m 1) / 3 := by norm_num [A, legP]
  have hGP : (∫ x in (0 : ℝ)..1, G x * P x) = m 0 ^ 2 + 5 * m 1 ^ 2 + 9 * m 2 ^ 2 := by
    have he : (fun x => G x * P x) = fun x =>
        m 0 * G x + 5 * m 1 * (G x * legP 2 x) + 9 * m 2 * (G x * legP 4 x) := by
      funext x; dsimp only [P]; ring
    rw [he]
    simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
      [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    rw [← hm0]
    change m 0 * m 0 + 5 * m 1 * m 1 + 9 * m 2 * m 2 = _
    ring
  have hPP : (∫ x in (0 : ℝ)..1, P x ^ 2) = m 0 ^ 2 + 5 * m 1 ^ 2 + 9 * m 2 ^ 2 := by
    conv_lhs => arg 1; ext x; dsimp only [P]; norm_num [legP]; ring_nf
    simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
      [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_pow]
    norm_num
    ring
  have hKK : (∫ x in (0 : ℝ)..1, K x ^ 2) =
      (m 0 - m 1) ^ 2 / 3 + (m 1 - m 2) ^ 2 / 7 + m 2 ^ 2 / 11 := by
    conv_lhs => arg 1; ext x; dsimp only [K]; norm_num [legP]; ring_nf
    simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
      [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_pow]
    norm_num
    ring
  have hGA : (∫ x in (0 : ℝ)..1, G x * A x) =
      (m 0 - m 1) * m 1 / 3 + (m 1 - m 2) * (m 2 - m 1) / 7 +
        m 2 * (m 3 - m 2) / 11 := by
    have he : (fun x => G x * A x) = fun x =>
        ((m 0 - m 1) / 3) * (G x * legP 2 x) +
        ((m 1 - m 2) / 7) * (G x * legP 4 x) -
        ((m 1 - m 2) / 7) * (G x * legP 2 x) +
        (m 2 / 11) * (G x * legP 6 x) - (m 2 / 11) * (G x * legP 4 x) := by
      funext x; dsimp only [A]; ring
    rw [he]
    simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
      [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
    change (m 0 - m 1) / 3 * m 1 + (m 1 - m 2) / 7 * m 2 -
      (m 1 - m 2) / 7 * m 1 + m 2 / 11 * m 3 - m 2 / 11 * m 2 = _
    ring
  have h := primitive_projection_bound hG hP hDK hDA hK0 hK1
  rw [integral_sq_sub hG hP, hGP, hPP, hKK, hGA, hA1, ← hm0] at h
  convert h using 1 <;> ring

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.primitive_mass_le_quartic_projection
