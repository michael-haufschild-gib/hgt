import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePoleFreeVariationInequality
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedVariationInequality
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCrossTermRepresentation

/-!
# Pole-Free Shift-Averaged Variation Inequality, Translation Invariance, and Cross-Energy Dominance

This module connects four pillars of the shifted ground-state theory in
`ArithmeticCriticalityTheory`:

1. **Exact Pole-Variance Decomposition and Translation Invariance (`u ↦ u + c`):**
   Combining the two-sided ground-state representation (`ShiftedGroundStateTwoSidedRepresentation`)
   with the profile variance `V_a(u) = profileVariance a u` and moment
   `profileMoment a u = ∫_{x>0} u(x) m_a(x) sinh(x/2) dx`
   (`ShiftedGroundStatePoleFreeVariationInequality`) yields the exact single-shift decomposition
   $$
     \operatorname{markovEnergy}(\Phi(\omega_a u))
       = \bigl(2 S_a(u) - D_a(u) + V_a(u)\bigr) + 8 \bigl(\operatorname{profileMoment}(a, u)\bigr)^2.
   $$
   Using the half-line moment identity $\int_{x>0} m_a(x)\sinh(x/2)\,dx = \sinh(a/2)/2$
   (`ShiftedGroundStatePlateauPositivity`), we prove that adding an arbitrary constant $c \in \mathbb{R}$
   shifts `profileMoment` by $c \sinh(a/2)/2$ while leaving `sameSideEnergy`,
   `reflectedDifferenceEnergy`, `averagedSameSideEnergy`, `averagedReflectedEnergy`, and
   `profileVariance` strictly invariant.

2. **Unconditional Derivation of the Pole-Free Variation Inequality from `RiemannHypothesis`:**
   Connecting the odd-sector criterion (`riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg`)
   with the mean-corrected plateau limit equivalence (`reflectedDifferenceEnergy_le_poleFree_iff`)
   proves unconditionally that `RiemannHypothesis` implies the pole-free variation inequality
   $$
     D_a(u) \le 2 S_a(u) + V_a(u)
   $$
   for every $a > 0$ and every even $u \in C^2_c(\mathbb{R})$, strictly sharpening
   `reflectedDifferenceEnergy_le_of_riemannHypothesis` by the non-negative pole term
   $8 (\operatorname{profileMoment}(a, u))^2$. In particular, under the pole-free variation
   inequality (and hence under `RiemannHypothesis`), the single-shift Markov energy is bounded below
   by the pole energy $8 (\operatorname{profileMoment}(a, u))^2$.

3. **Unconditional Collar Dominance of the Cross Energy and Cross-Term Pole-Free Identity:**
   Combining nonnegativity of the reflected difference energy with the cross-term decomposition
   (`ShiftedGroundStateCrossTermRepresentation`) proves the unconditional collar bound
   $$
     X_a(u) \le \int_{x>0} u(x)^2 m_a(x) C_a(x)\,dx
   $$
   together with the cross-term representation of the pole-free form.

4. **Shift-Integrated Bessel Bound and Pole-Strengthened Shift-Averaged Variation Inequality:**
   Integrating the source decomposition over $a \in (0, \infty)$ against
   `ShiftAveragedVariationInequality` proves that $a \mapsto (\operatorname{profileMoment}(a, u))^2$
   and $a \mapsto V_a(u)$ are integrable on $(0, \infty)$ and satisfy the exact identity
   $$
     \int_0^\infty V_a(u)\,da + 8 \int_0^\infty \bigl(\operatorname{profileMoment}(a, u)\bigr)^2\,da
       = 2 \int_{x>0} u(x)^2 \sinh^2(x/2)\,dx,
   $$
   yielding an unconditional Bessel-type inequality for the shift-difference moments:
   $$
     8 \int_0^\infty \bigl(\operatorname{profileMoment}(a, u)\bigr)^2\,da
       \le 2 \int_{x>0} u(x)^2 \sinh^2(x/2)\,dx.
   $$
   Integrating the single-shift pole-free variation inequality over $a > 0$ then establishes the
   **pole-strengthened shift-averaged variation inequality**
   $$
     \bar{D}(u) + 8 \int_0^\infty \bigl(\operatorname{profileMoment}(a, u)\bigr)^2\,da
       \le 2 \bar{S}(u) + 2 \int_{x>0} u(x)^2 \sinh^2(x/2)\,dx,
   $$
   and proves unconditionally that `RiemannHypothesis` implies both this pole-strengthened
   shift-averaged inequality and the shift-averaged variation inequality.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### 1. Exact Pole-Variance Decomposition and Translation Invariance -/

/-- Exact decomposition of the two-sided source into the profile variance plus the explicit-formula
pole term `8 (profileMoment a u)^2`. -/
theorem source_shiftedGroundState_eq_profileVariance_add_eight_profileMoment_sq
    (a : ℝ) (u : ℝ → ℝ) :
    4 * Real.sinh (a / 2) *
        (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      profileVariance a u + 8 * profileMoment a u ^ 2 := by
  unfold profileVariance
  ring

/-- **Exact Pole-Free + Pole Decomposition of the Single-Shift Markov Energy.**
For every shift `a > 0` and every even `u ∈ C²_c(ℝ)`, the Markov energy of `Φ(ω_a u)` splits into
the translation-invariant pole-free form `2 S_a(u) - D_a(u) + V_a(u)` plus the nonnegative pole
energy `8 (profileMoment a u)^2`. -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      (2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u) +
        8 * profileMoment a u ^ 2 := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven]
  unfold profileVariance
  ring

/-- For a zero-moment profile (`profileMoment a u = 0`), the Markov energy of `Φ(ω_a u)` is equal
to the pole-free form without any plateau truncation limit. -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_of_profileMoment_eq_zero
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) (hm : profileMoment a u = 0) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq
    ha hu huc heven, hm]
  ring

/-- Cauchy–Schwarz bound for the half-line sinh moment: the pole term `8 (profileMoment a u)^2` is
dominated by the two-sided source. -/
theorem eight_mul_profileMoment_sq_le_source {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    8 * profileMoment a u ^ 2 ≤
      4 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  have h := profileVariance_nonneg ha hu huc
  unfold profileVariance at h
  linarith

/-- Pointwise translation invariance of the same-side ground jump under `u ↦ u + c`. -/
theorem sameSideGroundJump_add_const (ω u : ℝ → ℝ) (c t x : ℝ) :
    sameSideGroundJump ω (fun y => u y + c) t x = sameSideGroundJump ω u t x := by
  unfold sameSideGroundJump
  congr 1
  ring

/-- Pointwise translation invariance of the reflected difference jump under `u ↦ u + c`. -/
theorem reflectedDifferenceJump_add_const (ω u : ℝ → ℝ) (c t x : ℝ) :
    reflectedDifferenceJump ω (fun y => u y + c) t x = reflectedDifferenceJump ω u t x := by
  unfold reflectedDifferenceJump
  congr 1
  ring

/-- Translation invariance of the same-side energy under `u ↦ u + c`. -/
theorem sameSideEnergy_add_const (ω u : ℝ → ℝ) (c : ℝ) :
    sameSideEnergy ω (fun y => u y + c) = sameSideEnergy ω u := by
  unfold sameSideEnergy
  simp only [sameSideGroundJump_add_const]

/-- Translation invariance of the reflected difference energy under `u ↦ u + c`. -/
theorem reflectedDifferenceEnergy_add_const (ω u : ℝ → ℝ) (c : ℝ) :
    reflectedDifferenceEnergy ω (fun y => u y + c) = reflectedDifferenceEnergy ω u := by
  unfold reflectedDifferenceEnergy
  simp only [reflectedDifferenceJump_add_const]

/-- Translation invariance of the shift-averaged same-side shift integral under `u ↦ u + c`. -/
theorem averagedSameSideShift_add_const (u : ℝ → ℝ) (c t : ℝ) :
    averagedSameSideShift (fun y => u y + c) t = averagedSameSideShift u t := by
  unfold averagedSameSideShift
  congr 1
  ext x
  ring

/-- Translation invariance of the shift-averaged reflected shift integral under `u ↦ u + c`. -/
theorem averagedReflectedShift_add_const (u : ℝ → ℝ) (c t : ℝ) :
    averagedReflectedShift (fun y => u y + c) t = averagedReflectedShift u t := by
  unfold averagedReflectedShift
  congr 1
  ext x
  ring

/-- Translation invariance of the shift-averaged same-side energy under `u ↦ u + c`. -/
theorem averagedSameSideEnergy_add_const (u : ℝ → ℝ) (c : ℝ) :
    averagedSameSideEnergy (fun y => u y + c) = averagedSameSideEnergy u := by
  unfold averagedSameSideEnergy
  simp only [averagedSameSideShift_add_const]

/-- Translation invariance of the shift-averaged reflected energy under `u ↦ u + c`. -/
theorem averagedReflectedEnergy_add_const (u : ℝ → ℝ) (c : ℝ) :
    averagedReflectedEnergy (fun y => u y + c) = averagedReflectedEnergy u := by
  unfold averagedReflectedEnergy
  simp only [averagedReflectedShift_add_const]

/-- Adding a constant `c` shifts `profileMoment a u` by `c * (sinh(a/2) / 2)`. -/
theorem profileMoment_add_const (a : ℝ) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (c : ℝ) :
    profileMoment a (fun x => u x + c) =
      profileMoment a u + c * (Real.sinh (a / 2) / 2) := by
  have h1 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have h2 : IntegrableOn (fun x => c * (shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
    (integrable_shiftDifference_mul_sinh_half a).integrableOn.const_mul c
  unfold profileMoment
  have heq : ∀ x, (u x + c) * shiftDifference a x * Real.sinh (x / 2) =
      u x * shiftDifference a x * Real.sinh (x / 2) +
        c * (shiftDifference a x * Real.sinh (x / 2)) := fun x => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => heq x,
    integral_add h1 h2, integral_const_mul, integral_Ioi_shiftDifference_mul_sinh_half]

/-- **Translation Invariance of the Profile Variance.**
For every shift `a` and every continuous compactly supported profile `u`, `profileVariance a` is
invariant under `u ↦ u + c`. -/
theorem profileVariance_add_const (a : ℝ) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (c : ℝ) :
    profileVariance a (fun x => u x + c) = profileVariance a u := by
  have h1 := integrableOn_sq_mul_shiftDifference_mul_sinh hu huc a
  have h2 := integrableOn_mul_shiftDifference_mul_sinh hu huc a
  have h3 := (integrable_shiftDifference_mul_sinh_half a).integrableOn (s := Ioi 0)
  have h2c : IntegrableOn (fun x => 2 * c * (u x * shiftDifference a x * Real.sinh (x / 2)))
      (Ioi 0) := h2.const_mul (2 * c)
  have h12 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) +
      2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) := h1.add h2c
  have h3c : IntegrableOn (fun x => c ^ 2 * (shiftDifference a x * Real.sinh (x / 2)))
      (Ioi 0) := h3.const_mul (c ^ 2)
  have heq : ∀ x, (u x + c) ^ 2 * shiftDifference a x * Real.sinh (x / 2) =
      (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) +
        2 * c * (u x * shiftDifference a x * Real.sinh (x / 2))) +
        c ^ 2 * (shiftDifference a x * Real.sinh (x / 2)) := fun x => by ring
  have hsq : (∫ x in Ioi (0 : ℝ), (u x + c) ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) +
        2 * c * profileMoment a u + c ^ 2 * (Real.sinh (a / 2) / 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x _ => heq x,
      integral_add h12 h3c, integral_add h1 h2c, integral_const_mul, integral_const_mul,
      integral_Ioi_shiftDifference_mul_sinh_half]
    rfl
  unfold profileVariance
  rw [hsq, profileMoment_add_const a hu huc c]
  ring

/-- **Translation Invariance of the Pole-Free Form.**
The full pole-free energy `2 S_a(u) - D_a(u) + V_a(u)` is invariant under `u ↦ u + c`. -/
theorem poleFreeEnergy_add_const (a : ℝ) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (c : ℝ) :
    2 * sameSideEnergy (shiftedGroundState a) (fun x => u x + c) -
        reflectedDifferenceEnergy (shiftedGroundState a) (fun x => u x + c) +
        profileVariance a (fun x => u x + c) =
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [sameSideEnergy_add_const, reflectedDifferenceEnergy_add_const,
    profileVariance_add_const a hu huc c]

/-! ### 2. Unconditional Derivation of the Pole-Free Variation Inequality from RH -/

/-- Under the Riemann Hypothesis, every mean-corrected plateau test
`Φ(ω_a (u - ū u_L))` has nonnegative Markov energy. -/
theorem markovEnergy_meanCorrectedProfile_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (a : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) (L : ℝ) :
    0 ≤ markovEnergy (fun x =>
      (phiDoobTest (fun y => shiftedGroundState a y * meanCorrectedProfile a u L y) x : ℂ)) := by
  set w := meanCorrectedProfile a u L
  have hwcd : ContDiff ℝ 2 w :=
    hu.sub (contDiff_const.mul (contDiff_smoothPlateau L))
  have hwc : HasCompactSupport w :=
    huc.sub (hasCompactSupport_smoothPlateau L).mul_left
  have hweven : ∀ x, w (-x) = w x := fun x => by
    show u (-x) - 2 * profileMoment a u / Real.sinh (a / 2) * smoothPlateau L (-x) =
      u x - 2 * profileMoment a u / Real.sinh (a / 2) * smoothPlateau L x
    rw [heven, smoothPlateau_neg]
  have hv : ContDiff ℝ 2 fun y => shiftedGroundState a y * w y :=
    (contDiff_shiftedGroundState a).mul hwcd
  have hvc : HasCompactSupport fun y => shiftedGroundState a y * w y := hwc.mul_left
  have hodd : ∀ x, (fun y => shiftedGroundState a y * w y) (-x) =
      -(fun y => shiftedGroundState a y * w y) x := fun x => by
    simp only
    rw [shiftedGroundState_neg, hweven]
    ring
  exact (riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg.mp hRH) _ hv hvc hodd

/-- **The Riemann Hypothesis implies the Pole-Free Variation Inequality.**
For every shift `a > 0` and every even `u ∈ C²_c(ℝ)`, `RiemannHypothesis` implies
`D_a(u) ≤ 2 S_a(u) + V_a(u)`, sharpening `reflectedDifferenceEnergy_le_of_riemannHypothesis` by
the nonnegative pole term `8 (profileMoment a u)^2`. -/
theorem reflectedDifferenceEnergy_le_poleFree_of_riemannHypothesis
    (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [reflectedDifferenceEnergy_le_poleFree_iff ha hu huc heven]
  intro η hη
  refine Eventually.of_forall fun L => ?_
  have h0 := markovEnergy_meanCorrectedProfile_nonneg_of_riemannHypothesis hRH a hu huc heven L
  linarith

/-- Whenever the pole-free variation inequality holds at shift `a`, the Markov energy of `Φ(ω_a u)`
is bounded below by the explicit-formula pole term `8 (profileMoment a u)^2`. -/
theorem eight_mul_profileMoment_sq_le_markovEnergy_of_poleFree
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x)
    (hpole : reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u) :
    8 * profileMoment a u ^ 2 ≤
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq
    ha hu huc heven]
  linarith

/-- Under `RiemannHypothesis`, the Markov energy of `Φ(ω_a u)` is bounded below by the pole term
`8 (profileMoment a u)^2`. -/
theorem eight_mul_profileMoment_sq_le_markovEnergy_of_riemannHypothesis
    (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    8 * profileMoment a u ^ 2 ≤
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) :=
  eight_mul_profileMoment_sq_le_markovEnergy_of_poleFree ha hu huc heven
    (reflectedDifferenceEnergy_le_poleFree_of_riemannHypothesis hRH ha hu huc heven)

/-! ### 3. Cross-Energy Collar Dominance and Cross-Term Pole-Free Representation -/

/-- Unconditional per-shift Cauchy–Schwarz dominance of `crossShift` by the collar integral. -/
theorem crossShift_le_collar_integral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (t : ℝ) :
    crossShift a u t ≤
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
  have h1 := integral_reflectedDifference_shiftedGroundState_nonneg ha u t
  have h2 := integral_reflectedDifference_eq_two_collar_sub_two_cross a hu t
  linarith

/-- **Unconditional Collar Dominance of the Cross Energy.**
For every shift `a > 0` and `u ∈ C¹_c(ℝ)`, the cross energy `X_a(u)` is bounded above by the collar
integral `∫_{x>0} u(x)^2 m_a(x) C_a(x) dx`. -/
theorem crossEnergy_le_collar_integral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) :
    crossEnergy a u ≤
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x := by
  have h1 := reflectedDifferenceEnergy_shiftedGroundState_nonneg ha u
  have h2 := reflectedDifferenceEnergy_eq_two_collar_sub_two_cross ha hu huc
  linarith

/-- **Cross-Term Representation of the Pole-Free Form.**
Expresses `2 S_a(u) - D_a(u) + V_a(u)` in terms of the same-side energy, the cross energy `X_a(u)`,
the collar excess `C_a(x) - 2 sinh(a/2) sinh(x/2)`, and `- 8 (profileMoment a u)^2`. -/
theorem poleFree_eq_two_sameSide_add_two_cross_sub_collar_sub_pole
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) :
    2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u =
      2 * sameSideEnergy (shiftedGroundState a) u + 2 * crossEnergy a u -
        2 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
          (shiftedCollarMass a x - 2 * Real.sinh (a / 2) * Real.sinh (x / 2))) -
        8 * profileMoment a u ^ 2 := by
  have h1 := markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq
    ha hu huc heven
  have h2 := markovEnergy_phiDoob_shiftedGroundState_eq_cross ha hu huc heven
  linarith

/-! ### 4. Shift-Integrated Profile Variance, Bessel Bound, and Pole-Strengthened Shift-Averaged Variation -/

/-- Measurability of the shift-moment map `a ↦ profileMoment a u`. -/
theorem measurable_profileMoment {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable fun a => profileMoment a u := by
  have hc : Continuous fun p : ℝ × ℝ =>
      u p.2 * shiftDifference p.1 p.2 * Real.sinh (p.2 / 2) :=
    ((hu.comp continuous_snd).mul continuous_shiftDifference_uncurry).mul
      (Real.continuous_sinh.comp (continuous_snd.div_const 2))
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- Integrability of `a ↦ 8 * profileMoment a u ^ 2` on `(0, ∞)` for any continuous compactly
supported `u`. -/
theorem integrableOn_eight_mul_profileMoment_sq {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun a => 8 * profileMoment a u ^ 2) (Ioi 0) := by
  refine (integrableOn_source_shiftedGroundState hu huc).mono'
    (measurable_const.mul ((measurable_profileMoment hu).pow_const 2)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun a ha => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact eight_mul_profileMoment_sq_le_source ha hu huc

/-- Integrability of `a ↦ profileMoment a u ^ 2` on `(0, ∞)` for any continuous compactly
supported `u`. -/
theorem integrableOn_profileMoment_sq {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun a => profileMoment a u ^ 2) (Ioi 0) := by
  have h := (integrableOn_eight_mul_profileMoment_sq hu huc).const_mul (1 / 8)
  refine IntegrableOn.congr_fun h (fun a _ => ?_) measurableSet_Ioi
  ring

/-- Integrability of `a ↦ profileVariance a u` on `(0, ∞)` for any continuous compactly
supported `u`. -/
theorem integrableOn_profileVariance {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    IntegrableOn (fun a => profileVariance a u) (Ioi 0) :=
  (integrableOn_source_shiftedGroundState hu huc).sub
    (integrableOn_eight_mul_profileMoment_sq hu huc)

/-- **Shift-Integrated Variance–Pole Identity.**
The shift integral of the profile variance plus `8` times the shift integral of the squared
profile moment equals the hyperbolic source `2 ∫_{x>0} u(x)^2 sinh^2(x/2) dx`. -/
theorem integral_Ioi_profileVariance_add_eight_integral_profileMoment_sq
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) :
    (∫ a in Ioi (0 : ℝ), profileVariance a u) +
        8 * (∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have hsrc := integrableOn_source_shiftedGroundState hu huc
  have hpole := integrableOn_eight_mul_profileMoment_sq hu huc
  have hsub : (∫ a in Ioi (0 : ℝ), profileVariance a u) =
      (∫ a in Ioi (0 : ℝ), 4 * Real.sinh (a / 2) *
        ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
      ∫ a in Ioi (0 : ℝ), 8 * profileMoment a u ^ 2 :=
    integral_sub hsrc hpole
  rw [hsub, integral_Ioi_source_shiftedGroundState hu huc, integral_const_mul]
  ring

/-- Nonnegativity of the shift-integrated profile variance. -/
theorem integral_Ioi_profileVariance_nonneg {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    0 ≤ ∫ a in Ioi (0 : ℝ), profileVariance a u :=
  setIntegral_nonneg measurableSet_Ioi fun _ ha => profileVariance_nonneg ha hu huc

/-- **Unconditional Bessel-Type Inequality for Shift-Difference Moments.**
For every continuous compactly supported profile `u`,
`8 ∫_{a>0} (profileMoment a u)^2 da ≤ 2 ∫_{x>0} u(x)^2 sinh^2(x/2) dx`. -/
theorem eight_mul_integral_Ioi_profileMoment_sq_le_two_integral_sinh_sq
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) :
    8 * (∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2) ≤
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have h1 := integral_Ioi_profileVariance_add_eight_integral_profileMoment_sq hu huc
  have h2 := integral_Ioi_profileVariance_nonneg hu huc
  linarith

/-- **Pole-Free Decomposition of the Shift-Averaged Markov Energy.**
Splits `∫_{a>0} markovEnergy(Φ(ω_a u)) da` into the shift-averaged pole-free energy
`2 S̄(u) - D̄(u) + ∫_{a>0} V_a(u) da` plus `8 ∫_{a>0} (profileMoment a u)^2 da`. -/
theorem integral_Ioi_markovEnergy_eq_poleFree_add_eight_integral_profileMoment_sq
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    (∫ a in Ioi (0 : ℝ),
        markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ))) =
      (2 * averagedSameSideEnergy u - averagedReflectedEnergy u +
        ∫ a in Ioi (0 : ℝ), profileVariance a u) +
        8 * ∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2 := by
  rw [integral_Ioi_markovEnergy_phiDoob_shiftedGroundState hu huc heven,
    ← integral_Ioi_profileVariance_add_eight_integral_profileMoment_sq hu.continuous huc]
  ring

/-- Shift average of the single-shift pole-free energy `2 S_a(u) - D_a(u) + V_a(u)`. -/
theorem integral_Ioi_poleFree_eq {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ a in Ioi (0 : ℝ),
        (2 * sameSideEnergy (shiftedGroundState a) u -
          reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u)) =
      2 * averagedSameSideEnergy u - averagedReflectedEnergy u +
        ∫ a in Ioi (0 : ℝ), profileVariance a u := by
  have hS := integrableOn_sameSideEnergy_shiftedGroundState hu huc
  have hD := integrableOn_reflectedDifferenceEnergy_shiftedGroundState hu.continuous huc
  have hV := integrableOn_profileVariance hu.continuous huc
  have hSD : IntegrableOn (fun a => 2 * sameSideEnergy (shiftedGroundState a) u -
      reflectedDifferenceEnergy (shiftedGroundState a) u) (Ioi 0) := (hS.const_mul 2).sub hD
  rw [integral_add hSD hV, integral_sub (hS.const_mul 2) hD, integral_const_mul,
    integral_Ioi_sameSideEnergy_shiftedGroundState hu huc,
    integral_Ioi_reflectedDifferenceEnergy_shiftedGroundState hu.continuous huc]

/-- **Pole-Strengthened Shift-Averaged Variation Inequality from Single-Shift Pole-Free Positivity.**
If `D_a(u) ≤ 2 S_a(u) + V_a(u)` holds for all `a > 0`, then
`D̄(u) + 8 ∫_{a>0} (profileMoment a u)^2 da ≤ 2 S̄(u) + 2 ∫_{x>0} u(x)^2 sinh^2(x/2) dx`. -/
theorem averagedReflectedEnergy_add_eight_integral_profileMoment_sq_le_of_poleFree
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (hpole : ∀ a > 0, reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u) :
    averagedReflectedEnergy u + 8 * (∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2) ≤
      2 * averagedSameSideEnergy u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have h0 : 0 ≤ ∫ a in Ioi (0 : ℝ),
      (2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u + profileVariance a u) := by
    refine setIntegral_nonneg measurableSet_Ioi fun a ha => ?_
    have := hpole a ha
    linarith
  rw [integral_Ioi_poleFree_eq hu huc] at h0
  have hV := integral_Ioi_profileVariance_add_eight_integral_profileMoment_sq hu.continuous huc
  linarith

/-- **The Riemann Hypothesis implies the Pole-Strengthened Shift-Averaged Variation Inequality.**
For every even `u ∈ C²_c(ℝ)`, `RiemannHypothesis` implies
`D̄(u) + 8 ∫_{a>0} (profileMoment a u)^2 da ≤ 2 S̄(u) + 2 ∫_{x>0} u(x)^2 sinh^2(x/2) dx`. -/
theorem averagedReflectedEnergy_add_eight_integral_profileMoment_sq_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    averagedReflectedEnergy u + 8 * (∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2) ≤
      2 * averagedSameSideEnergy u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 :=
  averagedReflectedEnergy_add_eight_integral_profileMoment_sq_le_of_poleFree
    (hu.of_le (by norm_num)) huc fun _ ha =>
    reflectedDifferenceEnergy_le_poleFree_of_riemannHypothesis hRH ha hu huc heven

/-- **The Riemann Hypothesis implies the Shift-Averaged Variation Inequality.**
For every even `u ∈ C²_c(ℝ)`, `RiemannHypothesis` implies
`D̄(u) ≤ 2 S̄(u) + 2 ∫_{x>0} u(x)^2 sinh^2(x/2) dx`. -/
theorem averagedReflectedEnergy_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    averagedReflectedEnergy u ≤
      2 * averagedSameSideEnergy u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * Real.sinh (x / 2) ^ 2 := by
  have h1 := averagedReflectedEnergy_add_eight_integral_profileMoment_sq_le_of_riemannHypothesis
    hRH hu huc heven
  have h2 : 0 ≤ ∫ a in Ioi (0 : ℝ), profileMoment a u ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
