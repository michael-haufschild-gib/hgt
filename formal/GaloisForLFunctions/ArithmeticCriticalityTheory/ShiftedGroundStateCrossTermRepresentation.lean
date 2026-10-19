import GaloisForLFunctions.ArithmeticCriticalityTheory.SignedCombinationOriginFailure

/-!
# The cross-term form of the Markov energy on a shifted ground state

Expanding the reflected difference square `(u(x) − u(t−x))² = u(x)² + u(t−x)² − 2u(x)u(t−x)` and
using the symmetry of the collar,

    ∫_0^t m_a(x) m_a(t−x) (u(x) − u(t−x))² dx = 2 ∫_0^t m_a(x) m_a(t−x) u(x)² dx − 2 X_a(u)(t),

with the **cross term** `X_a(u)(t) = ∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx`. Integrating against the
jump measure and using the collar Fubini identity, `D = 2∫u² m_a C_a − 2 X`, so the two-sided
representation becomes

    markovEnergy(Φ(ω_a u)) = 2 S_a(u) + 2 X_a(u) − 2 ∫_{x>0} u(x)² m_a(x) (C_a(x) − 2 sinh(a/2) sinh(x/2)) dx.

The cross term is a prime sum of the autocorrelation-type kernel `m_a u ∗ m_a u` at the shifts
`log n`; the last term is controlled by the collar bounds. This is the form in which the Markov
energy of far-apart bumps is evaluated.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The cross term of one shift, `∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx`. -/
def crossShift (a : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * (u x * u (t - x))

/-- The cross energy `∫ dm(t) crossShift a u t`. -/
def crossEnergy (a : ℝ) (u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * crossShift a u t) +
    ∑' n : ℕ, vonMangoldtAtom n * crossShift a u (Real.log n)

/-- The reflected difference integral as collar integral minus cross term. -/
theorem integral_reflectedDifference_eq_two_collar_sub_two_cross (a : ℝ) {u : ℝ → ℝ}
    (hu : Continuous u) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      2 * (∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) -
        2 * crossShift a u t := by
  have hm := continuous_shiftDifference a
  have hmr : Continuous fun x => shiftDifference a (t - x) :=
    hm.comp (continuous_const.sub continuous_id)
  have hur : Continuous fun x => u (t - x) := hu.comp (continuous_const.sub continuous_id)
  have hc1 : Continuous fun x => shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 :=
    (hm.mul hmr).mul (hu.pow 2)
  have hc2 : Continuous fun x => shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2 :=
    (hmr.mul hm).mul (hur.pow 2)
  have hc3 : Continuous fun x => shiftDifference a x * shiftDifference a (t - x) * (u x * u (t - x)) :=
    (hm.mul hmr).mul (hu.mul hur)
  have hi1 : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (t - x) * u x ^ 2)
      (Ioo (0 : ℝ) t) := hc1.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi2 : IntegrableOn (fun x => shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2)
      (Ioo (0 : ℝ) t) := hc2.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hi3 : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (t - x) *
      (u x * u (t - x))) (Ioo (0 : ℝ) t) :=
    hc3.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hrefl : (∫ x in Ioo (0 : ℝ) t, shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
    have h := RHTower.setIntegral_Ioo_reflect_self
      (fun y => shiftDifference a y * shiftDifference a (t - y) * u y ^ 2) t
    refine (setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_).trans h
    show shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2 =
      shiftDifference a (t - x) * shiftDifference a (t - (t - x)) * u (t - x) ^ 2
    rw [sub_sub_cancel]
  have hpt : ∀ x, reflectedDifferenceJump (shiftedGroundState a) u t x =
      (shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 +
        shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2) -
        2 * (shiftDifference a x * shiftDifference a (t - x) * (u x * u (t - x))) := by
    intro x
    rw [reflectedDifferenceJump_shiftedGroundState]
    ring
  have hi12 : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 +
      shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2) (Ioo (0 : ℝ) t) :=
    hi1.add hi2
  unfold crossShift
  rw [setIntegral_congr_fun measurableSet_Ioo fun x _ => hpt x, integral_sub hi12
    (hi3.const_mul 2), integral_add hi1 hi2, integral_const_mul, hrefl]
  ring

/-- Integrability in the shift of the archimedean cross term. -/
theorem integrableOn_archLevy_mul_crossShift {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    IntegrableOn (fun t => archLevyDensity t * crossShift a u t) (Ioi 0) := by
  have hC := integrableOn_archLevy_mul_collarIntegral ha hu.continuous huc
  have hD := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc
  have hsub : IntegrableOn (fun t => archLevyDensity t *
      (∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) -
      (1 / 2) * (archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x)) (Ioi 0) :=
    hC.sub (hD.const_mul _)
  refine hsub.congr_fun (fun t _ => ?_) measurableSet_Ioi
  show archLevyDensity t *
      (∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) -
      (1 / 2) * (archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
    archLevyDensity t * crossShift a u t
  rw [integral_reflectedDifference_eq_two_collar_sub_two_cross a hu.continuous t]
  ring

/-- Summability in the prime of the prime cross terms. -/
theorem summable_atom_mul_crossShift {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    Summable fun n : ℕ => vonMangoldtAtom n * crossShift a u (Real.log n) := by
  have hC := summable_atom_mul_collarIntegral ha hu.continuous huc
  have hD := summable_atom_mul_reflectedDifferenceIntegral ha hu huc
  refine (hC.sub (hD.mul_left (1 / 2))).congr fun n => ?_
  rw [integral_reflectedDifference_eq_two_collar_sub_two_cross a hu.continuous]
  ring

/-- `D_a(u) = 2 ∫_{x>0} u² m_a C_a − 2 X_a(u)`. -/
theorem reflectedDifferenceEnergy_eq_two_collar_sub_two_cross {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    reflectedDifferenceEnergy (shiftedGroundState a) u =
      2 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x) -
        2 * crossEnergy a u := by
  have hC := integrableOn_archLevy_mul_collarIntegral ha hu.continuous huc
  have hX := integrableOn_archLevy_mul_crossShift ha hu huc
  have hCs := summable_atom_mul_collarIntegral ha hu.continuous huc
  have hXs := summable_atom_mul_crossShift ha hu huc
  have hpt := integral_reflectedDifference_eq_two_collar_sub_two_cross a hu.continuous
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) -
        2 * ∫ t in Ioi (0 : ℝ), archLevyDensity t * crossShift a u t := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hC.const_mul 2) (hX.const_mul 2)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hpt t]
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n),
          reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) =
      2 * (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2) -
        2 * ∑' n : ℕ, vonMangoldtAtom n * crossShift a u (Real.log n) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hCs.mul_left 2).tsum_sub (hXs.mul_left 2)]
    refine tsum_congr fun n => ?_
    rw [hpt]
    ring
  have hfub := integral_dm_collar_eq_integral_sq_mul_collarMass ha hu.continuous huc
  unfold reflectedDifferenceEnergy crossEnergy
  linear_combination harch + hprime + 2 * hfub

/-- **Cross-term representation of the Markov energy.** For `a > 0` and every even `u ∈ C²_c(ℝ)`,

    markovEnergy(Φ(ω_a u)) = 2 S_a(u) + 2 X_a(u) − 2 ∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2)). -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_cross {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      2 * sameSideEnergy (shiftedGroundState a) u + 2 * crossEnergy a u -
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
          (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2)) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven,
    reflectedDifferenceEnergy_eq_two_collar_sub_two_cross ha hu1 huc]
  have hI1 := integrableOn_sq_mul_shiftDifference_mul_collarMass ha hu.continuous huc
  have hI2 : IntegrableOn (fun x => (2 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) *
      u x ^ 2) (Ioi 0) :=
    integrableOn_continuous_mul_sq ((continuous_const.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))) hu.continuous huc _
  have hI2' : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      (2 * Real.sinh (a / 2) * Real.sinh (x / 2))) (Ioi 0) :=
    hI2.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have hsplit : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))) =
      (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x) -
        ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
          (2 * Real.sinh (a / 2) * Real.sinh (x / 2)) := by
    rw [← integral_sub hI1 hI2']
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hsrc : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
      (2 * Real.sinh (a / 2) * Real.sinh (x / 2))) =
      2 * Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  rw [hsplit, hsrc]
  ring

/-- The same-side energy is nonnegative. -/
theorem sameSideEnergy_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ → ℝ) :
    0 ≤ sameSideEnergy (shiftedGroundState a) u := by
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  unfold sameSideEnergy
  refine add_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    (tsum_nonneg fun n => ?_)
  · exact mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le
      (integral_sameSideGroundJump_nonneg hpos (mem_Ioi.mp ht).le)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n)
      (integral_sameSideGroundJump_nonneg hpos (Real.log_natCast_nonneg n))

/-- **Lower bound by the cross term.** For `a > 0` and every even `u ∈ C²_c(ℝ)`,

    markovEnergy(Φ(ω_a u)) ≥ 2 X_a(u) − 2 ∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2)). -/
theorem markovEnergy_phiDoob_shiftedGroundState_ge_cross {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    2 * crossEnergy a u - 2 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))) ≤
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_cross ha hu huc heven]
  have := sameSideEnergy_nonneg ha u
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
