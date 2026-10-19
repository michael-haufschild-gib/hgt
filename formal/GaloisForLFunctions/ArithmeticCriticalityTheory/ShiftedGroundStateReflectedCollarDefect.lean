import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSourceEquation

/-!
# The folded defect of the shifted ground states: the reflected collar mass

The folded generator differs from the two-sided generator by the reflected collar. For the shifted
ground state `ω_a` with `a > 0` and `x > 0`,

    (𝓛_N ω_a)(x) − Φ(x) cosh(x/2) ω_a(x) = 2 Φ(x) [ sinh(a/2) sinh(x/2) − C_a(x) ],

where the reflected collar mass

    C_a(x) = ∫_0^∞ ω(t) (Φ(t−x−a) − Φ(t−x+a))⁺ dt + Σ_n Λ(n) n^{−1/2} (Φ(log n − x − a) − Φ(log n − x + a))⁺

collects the mass that returns from the reflected side; the positive part vanishes for `t ≤ x`. So
`ω_a` is a folded supersolution at `x` exactly when `C_a(x) ≤ sinh(a/2) sinh(x/2)`. The archimedean
collar is integrable because the Lévy density is decreasing beyond `x`, and the prime collar is
summable because it is dominated by a shifted prime sum of Riemann's kernel.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The reflected collar of one shift, `2Φ(x)Φ(t−x) ω(t−x)⁺`. -/
def reflectedCollarShift (ω : ℝ → ℝ) (t x : ℝ) : ℝ :=
  2 * riemannKernelReal x * riemannKernelReal (t - x) * max (ω (t - x)) 0

/-- The reflected collar mass of the shifted ground state in test coordinates. -/
def shiftedCollarMass (a x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) +
    ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0

theorem twoSidedShiftGenerator_eq_folded_add_reflectedCollar {ω : ℝ → ℝ}
    (hodd : ∀ x, ω (-x) = -ω x) (hpos : ∀ x, 0 < x → 0 < ω x) (t x : ℝ) :
    twoSidedShiftGenerator ω t x = foldedShiftGenerator ω t x + reflectedCollarShift ω t x :=
  twoSidedShiftGenerator_eq_folded_add_collar hodd hpos t x

theorem reflectedCollarShift_shiftedGroundState (a t x : ℝ) :
    reflectedCollarShift (shiftedGroundState a) t x =
      2 * riemannKernelReal x * max (shiftDifference a (t - x)) 0 := by
  unfold reflectedCollarShift
  rw [mul_assoc (2 * riemannKernelReal x),
    mul_max_of_nonneg _ _ (riemannKernelReal_pos (t - x)).le, mul_zero,
    riemannKernelReal_mul_shiftedGroundState]

theorem max_shiftDifference_le (a s : ℝ) :
    max (shiftDifference a s) 0 ≤ riemannKernelReal (s - a) := by
  unfold shiftDifference
  exact max_le (by linarith [riemannKernelReal_pos (s + a)]) (riemannKernelReal_pos (s - a)).le

theorem max_shiftDifference_eq_zero_of_nonpos {a s : ℝ} (ha : 0 < a) (hs : s ≤ 0) :
    max (shiftDifference a s) 0 = 0 := by
  apply max_eq_right
  rcases hs.lt_or_eq with h | h
  · have hpos := shiftDifference_pos ha (neg_pos.mpr h)
    rw [shiftDifference_neg] at hpos
    linarith
  · subst h
    unfold shiftDifference
    rw [zero_sub, zero_add, riemannKernelReal_neg', sub_self]

/-- The archimedean reflected collar of `ω_a` is integrable: it vanishes for `t ≤ x` and is
dominated by `ω(x) Φ(t − x − a)` beyond `x`. -/
theorem integrableOn_archLevy_max_shiftDifference {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t => archLevyDensity t * max (shiftDifference a (t - x)) 0) (Ioi 0) := by
  have hbound : Integrable (fun t : ℝ => archLevyDensity x * riemannKernelReal (t - (x + a)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrable_riemannKernelReal.comp_sub_right (x + a)).const_mul _).integrableOn
  refine Integrable.mono' hbound ?_ ?_
  · exact (measurable_archLevyDensity.mul
      (((continuous_shiftDifference a).comp (continuous_id.sub continuous_const)).max
        continuous_const).measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (archLevyDensity_pos ht0).le (le_max_right _ _))]
    by_cases hxt : t ≤ x
    · rw [max_shiftDifference_eq_zero_of_nonpos ha (by linarith), mul_zero]
      exact mul_nonneg (archLevyDensity_pos hx).le (riemannKernelReal_pos _).le
    · rw [not_le] at hxt
      have h1 : archLevyDensity t ≤ archLevyDensity x :=
        (strictAntiOn_archLevyDensity_Ioi hx ht0 hxt).le
      have h2 := max_shiftDifference_le a (t - x)
      rw [show t - x - a = t - (x + a) by ring] at h2
      exact mul_le_mul h1 h2 (le_max_right _ _) (archLevyDensity_pos hx).le

/-- The prime reflected collar of `ω_a` is summable: it is dominated by the prime shift sum of
Riemann's kernel at `x + a`. -/
theorem summable_atom_max_shiftDifference (a x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (le_max_right _ _)) (fun n => ?_)
    (summable_primeShift_left (x + a))
  have h := max_shiftDifference_le a (Real.log n - x)
  have e : riemannKernelReal (Real.log n - x - a) = riemannKernelReal (x + a - Real.log n) := by
    rw [show x + a - Real.log n = -(Real.log n - x - a) by ring, riemannKernelReal_neg']
  rw [e] at h
  exact mul_le_mul_of_nonneg_left h (vonMangoldtAtom_nonneg n)

theorem integrableOn_archLevy_twoSidedShiftGenerator_shiftedGroundState (a x : ℝ) :
    IntegrableOn (fun u => archLevyDensity u * twoSidedShiftGenerator (shiftedGroundState a) u x)
      (Ioi 0) := by
  have hx := integrableOn_symArchTerm x
  have hxa := integrableOn_symArchTerm (x - a)
  have hxpa := integrableOn_symArchTerm (x + a)
  have hcomb : IntegrableOn (fun u => -(shiftDifference a x * symArchTerm x u -
      riemannKernelReal x * (symArchTerm (x - a) u - symArchTerm (x + a) u))) (Ioi 0) :=
    ((hx.const_mul (shiftDifference a x)).sub
      ((hxa.sub hxpa).const_mul (riemannKernelReal x))).neg
  exact hcomb.congr_fun
    (fun u _ => (archLevy_twoSidedShiftGenerator_shiftedGroundState a x u).symm) measurableSet_Ioi

theorem summable_atom_twoSidedShiftGenerator_shiftedGroundState (a x : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * twoSidedShiftGenerator (shiftedGroundState a) (Real.log n) x := by
  have hx := summable_primeKernelSum x
  have hxa := summable_primeKernelSum (x - a)
  have hxpa := summable_primeKernelSum (x + a)
  exact ((hx.mul_left (shiftDifference a x)).sub
    ((hxa.sub hxpa).mul_left (riemannKernelReal x))).congr fun n =>
      (atom_twoSidedShiftGenerator_shiftedGroundState a x n).symm

theorem archLevy_foldedShiftGenerator_shiftedGroundState {a : ℝ} (ha : 0 < a) (t x : ℝ) :
    archLevyDensity t * foldedShiftGenerator (shiftedGroundState a) t x =
      archLevyDensity t * twoSidedShiftGenerator (shiftedGroundState a) t x -
        2 * riemannKernelReal x * (archLevyDensity t * max (shiftDifference a (t - x)) 0) := by
  rw [twoSidedShiftGenerator_eq_folded_add_reflectedCollar (shiftedGroundState_neg a)
    (fun y hy => shiftedGroundState_pos ha hy) t x, reflectedCollarShift_shiftedGroundState]
  ring

theorem atom_foldedShiftGenerator_shiftedGroundState {a : ℝ} (ha : 0 < a) (x : ℝ) (n : ℕ) :
    vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x =
      vonMangoldtAtom n * twoSidedShiftGenerator (shiftedGroundState a) (Real.log n) x -
        2 * riemannKernelReal x * (vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0) := by
  rw [twoSidedShiftGenerator_eq_folded_add_reflectedCollar (shiftedGroundState_neg a)
    (fun y hy => shiftedGroundState_pos ha hy) (Real.log n) x,
    reflectedCollarShift_shiftedGroundState]
  ring

/-- **Folded generator of the shifted ground state.**
`𝓛_N ω_a = 𝓛_D ω_a − 2Φ(x) C_a(x)` for `a > 0`, `x > 0`. -/
theorem foldedGenerator_shiftedGroundState {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    foldedGenerator (shiftedGroundState a) x =
      twoSidedGenerator (shiftedGroundState a) x - 2 * riemannKernelReal x * shiftedCollarMass a x := by
  unfold foldedGenerator twoSidedGenerator shiftedCollarMass
  have harch : (∫ t in Ioi (0 : ℝ),
      archLevyDensity t * foldedShiftGenerator (shiftedGroundState a) t x) =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator (shiftedGroundState a) t x) -
        2 * riemannKernelReal x *
          ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 := by
    rw [← integral_const_mul, ← integral_sub
      (integrableOn_archLevy_twoSidedShiftGenerator_shiftedGroundState a x)
      ((integrableOn_archLevy_max_shiftDifference ha hx).const_mul _)]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ =>
      archLevy_foldedShiftGenerator_shiftedGroundState ha t x
  have hprime : (∑' n : ℕ,
      vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x) =
      (∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator (shiftedGroundState a) (Real.log n) x) -
        2 * riemannKernelReal x *
          ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 := by
    rw [← tsum_mul_left, ← (summable_atom_twoSidedShiftGenerator_shiftedGroundState a x).tsum_sub
      ((summable_atom_max_shiftDifference a x).mul_left _)]
    exact tsum_congr fun n => atom_foldedShiftGenerator_shiftedGroundState ha x n
  rw [harch, hprime]
  ring

/-- **Folded defect of the shifted ground state.**
`(𝓛_N ω_a)(x) − Φ(x) cosh(x/2) ω_a(x) = 2Φ(x) [sinh(a/2) sinh(x/2) − C_a(x)]`. -/
theorem foldedGenerator_shiftedGroundState_sub_potential {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x =
      2 * riemannKernelReal x * (Real.sinh (a / 2) * Real.sinh (x / 2) - shiftedCollarMass a x) := by
  rw [foldedGenerator_shiftedGroundState ha hx]
  have h := twoSidedGenerator_shiftedGroundState_sub_potential a x
  linear_combination h

/-- The shifted ground state is a folded supersolution at `x` exactly when its reflected collar mass
is at most its source `sinh(a/2) sinh(x/2)`. -/
theorem foldedSupersolution_shiftedGroundState_iff {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x ≤
        foldedGenerator (shiftedGroundState a) x ↔
      shiftedCollarMass a x ≤ Real.sinh (a / 2) * Real.sinh (x / 2) := by
  have h := foldedGenerator_shiftedGroundState_sub_potential ha hx
  have hΦ : 0 < 2 * riemannKernelReal x := by
    have := riemannKernelReal_pos x
    positivity
  constructor
  · intro hle
    have h0 : 0 ≤ 2 * riemannKernelReal x *
        (Real.sinh (a / 2) * Real.sinh (x / 2) - shiftedCollarMass a x) := by linarith
    have := (mul_nonneg_iff_of_pos_left hΦ).mp h0
    linarith
  · intro hC
    have h0 : 0 ≤ 2 * riemannKernelReal x *
        (Real.sinh (a / 2) * Real.sinh (x / 2) - shiftedCollarMass a x) :=
      mul_nonneg hΦ.le (sub_nonneg.mpr hC)
    linarith

theorem shiftedCollarMass_nonneg (a x : ℝ) : 0 ≤ shiftedCollarMass a x := by
  unfold shiftedCollarMass
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _)
  have h2 : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 :=
    tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (le_max_right _ _)
  linarith

/-- The folded defect of `ω_a` never exceeds the two-sided source: the reflected collar only
subtracts. -/
theorem foldedGenerator_shiftedGroundState_sub_potential_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x ≤
      2 * Real.sinh (a / 2) * Real.sinh (x / 2) * riemannKernelReal x := by
  rw [foldedGenerator_shiftedGroundState_sub_potential ha hx]
  have hΦ := riemannKernelReal_pos x
  have hC := shiftedCollarMass_nonneg a x
  nlinarith [mul_nonneg hΦ.le hC]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
