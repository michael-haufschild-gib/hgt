import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateMonotoneFoldDomination
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# The two-sided representation in odd-profile coordinates

The corpus's odd profile is `oddProfile a = m_a / (2 sinh(a/2))` and its test is
`oddProfileTest a w = oddProfile a · w = Φ(ω_a w) / (2 sinh(a/2))`. Since the Markov energy is
quadratic, `markovEnergy (c • f) = c² markovEnergy f` for real `c`, and the two-sided representation
of `Φ(ω_a w)` reads, in these coordinates,

    markovEnergy(oddProfileTest a w)
      = (2 S_a(w) − D_a(w)) / (4 sinh(a/2)²) + 2 ∫_{x>0} oddProfile a x · sinh(x/2) · w(x)² dx.

The last term is the half-line form of the odd sinh potential: the whole budget by which the
reflected difference energy may exceed twice the same-side energy is the sinh potential, with
coefficient one.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Scaling of the Markov energy -/

theorem weilTest_smul_self (c : ℂ) (f : ℝ → ℂ) :
    EF.weilTest (c • f) (c • f) = (c * conj c) • EF.weilTest f f := by
  funext x
  rw [Pi.smul_apply, weilTest_apply, weilTest_apply, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem weilPoleTerm_smul (a : ℂ) (k : ℝ → ℂ) : weilPoleTerm (a • k) = a * weilPoleTerm k := by
  unfold weilPoleTerm
  rw [paperFT_smul, paperFT_smul]
  ring

/-- The Markov energy is quadratic under real scaling. -/
theorem markovEnergy_real_smul (c : ℝ) (f : ℝ → ℂ) :
    markovEnergy ((c : ℂ) • f) = c ^ 2 * markovEnergy f := by
  unfold markovEnergy
  rw [weilTest_smul_self, RHTower.WeilSpectral.weilFullFunctional_smul, weilPoleTerm_smul, ← mul_sub,
    conj_ofReal,
    ← ofReal_mul, re_ofReal_mul]
  ring

/-! ### The odd profile as a scaled shifted ground state -/

theorem shiftDifference_eq_two_sinh_mul_oddProfile {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    shiftDifference a x = 2 * Real.sinh (a / 2) * oddProfile a x := by
  have hs : 2 * Real.sinh (a / 2) ≠ 0 :=
    mul_ne_zero two_ne_zero (Real.sinh_ne_zero.mpr (div_ne_zero ha two_ne_zero))
  unfold oddProfile shiftDifference
  field_simp

theorem oddProfileTest_eq_smul_phiDoob {a : ℝ} (ha : 0 < a) (w : ℝ → ℝ) :
    (fun x => (oddProfileTest a w x : ℂ)) =
      ((1 / (2 * Real.sinh (a / 2)) : ℝ) : ℂ) •
        fun x => (phiDoobTest (fun y => shiftedGroundState a y * w y) x : ℂ) := by
  have hs : 2 * Real.sinh (a / 2) ≠ 0 := by
    have := Real.sinh_pos_iff.mpr (by linarith : 0 < a / 2)
    positivity
  funext x
  rw [Pi.smul_apply, smul_eq_mul, ← ofReal_mul]
  congr 1
  show oddProfile a x * w x =
    1 / (2 * Real.sinh (a / 2)) * (riemannKernelReal x * (shiftedGroundState a x * w x))
  rw [← mul_assoc (riemannKernelReal x), riemannKernelReal_mul_shiftedGroundState,
    shiftDifference_eq_two_sinh_mul_oddProfile ha.ne']
  field_simp

/-! ### The two-sided representation of the odd-profile test -/

/-- **Two-sided representation in odd-profile coordinates.** For `a > 0` and every even
`w ∈ C²_c(ℝ)`,

    markovEnergy(oddProfileTest a w)
      = (2 S_a(w) − D_a(w)) / (4 sinh(a/2)²) + 2 ∫_{x>0} oddProfile a x · sinh(x/2) · w(x)². -/
theorem markovEnergy_oddProfileTest_eq_twoSided {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    markovEnergy (fun x => (oddProfileTest a w x : ℂ)) =
      (2 * sameSideEnergy (shiftedGroundState a) w -
          reflectedDifferenceEnergy (shiftedGroundState a) w) / (4 * Real.sinh (a / 2) ^ 2) +
        2 * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  rw [oddProfileTest_eq_smul_phiDoob ha, markovEnergy_real_smul,
    markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hw hwc heven]
  have hI : (∫ x in Ioi (0 : ℝ), w x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      2 * Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [shiftDifference_eq_two_sinh_mul_oddProfile ha.ne']
    ring
  rw [hI]
  field_simp
  ring

/-- Nonnegativity of the Markov energy on `oddProfileTest a w` is the variation inequality
`D_a(w) ≤ 2 S_a(w) + 8 sinh(a/2)² ∫_{x>0} oddProfile a · sinh(x/2) · w²`. -/
theorem markovEnergy_oddProfileTest_nonneg_iff_variation {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) (heven : ∀ x, w (-x) = w x) :
    0 ≤ markovEnergy (fun x => (oddProfileTest a w x : ℂ)) ↔
      reflectedDifferenceEnergy (shiftedGroundState a) w ≤
        2 * sameSideEnergy (shiftedGroundState a) w +
          8 * Real.sinh (a / 2) ^ 2 *
            ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2 := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hs2 : 0 < 4 * Real.sinh (a / 2) ^ 2 := by positivity
  have key : (2 * sameSideEnergy (shiftedGroundState a) w -
        reflectedDifferenceEnergy (shiftedGroundState a) w) / (4 * Real.sinh (a / 2) ^ 2) +
      2 * (∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) =
      ((2 * sameSideEnergy (shiftedGroundState a) w -
        reflectedDifferenceEnergy (shiftedGroundState a) w) +
        8 * Real.sinh (a / 2) ^ 2 *
          ∫ x in Ioi (0 : ℝ), oddProfile a x * Real.sinh (x / 2) * w x ^ 2) /
        (4 * Real.sinh (a / 2) ^ 2) := by
    field_simp
    ring
  rw [markovEnergy_oddProfileTest_eq_twoSided ha hw hwc heven, key, le_div_iff₀ hs2, zero_mul]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
