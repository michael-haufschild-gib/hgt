import GaloisForLFunctions.RHTower.CHMDPrimeDivisorCuts
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The unavoidable reflected-prime singular component

For odd half-line tests, the normalized difference-square kernel has positive
archimedean and same-side prime measures and a negative reflected-prime measure.
The first two are mutually singular with the entire last measure. On
B = {(x, log 2 - x) : 0 < x < log 2 / 2}, only the reflected prime 2 survives,
with positive finite mass. Every strictly positive scalar reweighting retains
this obstruction, even after any absolutely continuous or diagonal correction.
These are the original von Mangoldt coefficients and original theta factors.

The negative component must be retained with its positive collar diagonal.
Their exact compensation equals the positive prime-crossing energy, and its
complete sum has the finite-divisor cut expansion. Every nonzero odd compact
test has strictly positive compensated crossing energy. The per-prime identity
and the full Doob source identity retain their original common factors of two.

This rejects literal local positive-jump absorption. It does not assert that
the Weil quadratic form is negative, exclude nonlocal factorizations, or settle
the remaining cosh subtraction or RH.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

noncomputable section
namespace RHTower.CHMDReflectedPrime

/-- The ordered half of the first prime's reflection line. -/
def firstPrimeSlice : Set (ℝ × ℝ) :=
  (Prod.fst ⁻¹' Ioo (0 : ℝ) (Real.log 2 / 2)) ∩
    {p | p.2 = Real.log 2 - p.1}

def forwardCurve (d : ℕ) (x : ℝ) : ℝ × ℝ := (x, x + Real.log d)
def reflectedCurve (d : ℕ) (x : ℝ) : ℝ × ℝ := (x, Real.log d - x)

def forwardDensity (d : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom d * riemannKernelReal x * riemannKernelReal (x + Real.log d)

def reflectedDensity (d : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom d * riemannKernelReal x * riemannKernelReal (Real.log d - x)

theorem continuous_reflectedDensity (d : ℕ) : Continuous (reflectedDensity d) :=
  (continuous_const.mul continuous_riemannKernelReal).mul
    (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))

theorem reflectedDensity_nonneg (d : ℕ) (x : ℝ) : 0 ≤ reflectedDensity d x :=
  mul_nonneg (mul_nonneg (vonMangoldtAtom_nonneg d) (riemannKernelReal_pos _).le)
    (riemannKernelReal_pos _).le

def forwardMeasure (d : ℕ) : Measure (ℝ × ℝ) :=
  Measure.map (forwardCurve d) ((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (forwardDensity d x)))

def reflectedMeasure (d : ℕ) : Measure (ℝ × ℝ) :=
  Measure.map (reflectedCurve d) ((volume.restrict (Ioo (0 : ℝ) (Real.log d / 2))).withDensity
    (fun x => ENNReal.ofReal (reflectedDensity d x)))

/-- The ordinary density of the reflected archimedean difference-square term. -/
def archMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure ℝ).prod volume).withDensity (fun p =>
    if 0 < p.1 ∧ p.1 < p.2 then ENNReal.ofReal
      (reflectedArchLevyWeight p.1 (p.2 - p.1) * riemannKernelReal p.1 * riemannKernelReal p.2)
    else 0)

def positiveJumpMeasure : Measure (ℝ × ℝ) := archMeasure + Measure.sum forwardMeasure

def negativeJumpMeasure : Measure (ℝ × ℝ) := Measure.sum reflectedMeasure

theorem measurableSet_firstPrimeSlice : MeasurableSet firstPrimeSlice :=
  (measurable_fst measurableSet_Ioo).inter
    (isClosed_eq continuous_snd (continuous_const.sub continuous_fst)).measurableSet

theorem planar_firstPrimeSlice_zero : (volume.prod volume) firstPrimeSlice = 0 := by
  rw [Measure.prod_apply measurableSet_firstPrimeSlice]
  have hz (x : ℝ) : volume {y : ℝ | (x, y) ∈ firstPrimeSlice} = 0 := by
    apply measure_mono_null (t := {Real.log 2 - x}) _ (measure_singleton _)
    intro y hy
    exact hy.2
  calc
    _ = ∫⁻ _x : ℝ, (0 : ℝ≥0∞) := lintegral_congr hz
    _ = 0 := lintegral_zero

theorem diagonal_preimage_empty : (fun x : ℝ => (x, x)) ⁻¹' firstPrimeSlice = ∅ := by
  ext x
  simp only [firstPrimeSlice, mem_preimage, mem_inter_iff, mem_Ioo, mem_setOf_eq, mem_empty_iff_false,
    iff_false]
  rintro ⟨⟨hx0, hxL⟩, he⟩
  linarith

theorem log_nat_ne_log_two {d : ℕ} (hd : d ≠ 2) : Real.log (d : ℝ) ≠ Real.log 2 := by
  intro he
  have hd0 : d ≠ 0 := by
    intro hz
    simp only [hz, Nat.cast_zero, Real.log_zero] at he
    have hp : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hc : (d : ℝ) = 2 := Real.log_injOn_pos
    (show (d : ℝ) ∈ Ioi 0 by
      change (0 : ℝ) < d
      exact_mod_cast Nat.pos_of_ne_zero hd0)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) he
  exact hd (by exact_mod_cast hc)

theorem forward_preimage_empty (d : ℕ) : forwardCurve d ⁻¹' firstPrimeSlice = ∅ := by
  ext x
  simp only [firstPrimeSlice, forwardCurve, mem_preimage, mem_inter_iff, mem_Ioo,
    mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨⟨hx0, hxL⟩, he⟩
  by_cases hd : 2 ≤ d
  · have hl : Real.log (2 : ℝ) ≤ Real.log d :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hd)
    linarith
  · have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with rfl | rfl <;> norm_num at he <;> linarith

theorem reflected_preimage_empty {d : ℕ} (hd : d ≠ 2) :
    reflectedCurve d ⁻¹' firstPrimeSlice = ∅ := by
  ext x
  simp only [firstPrimeSlice, reflectedCurve, mem_preimage, mem_inter_iff, mem_Ioo,
    mem_setOf_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hx, he⟩
  exact log_nat_ne_log_two hd (by linarith)

theorem reflected_two_preimage : reflectedCurve 2 ⁻¹' firstPrimeSlice =
    Ioo (0 : ℝ) (Real.log 2 / 2) := by
  ext x
  simp [firstPrimeSlice, reflectedCurve]

theorem forwardMeasure_slice_zero (d : ℕ) : forwardMeasure d firstPrimeSlice = 0 := by
  rw [forwardMeasure, Measure.map_apply (by unfold forwardCurve; fun_prop)
    measurableSet_firstPrimeSlice, forward_preimage_empty, measure_empty]

theorem reflectedMeasure_slice_zero {d : ℕ} (hd : d ≠ 2) :
    reflectedMeasure d firstPrimeSlice = 0 := by
  rw [reflectedMeasure, Measure.map_apply (by unfold reflectedCurve; fun_prop)
    measurableSet_firstPrimeSlice, reflected_preimage_empty hd, measure_empty]

theorem archMeasure_slice_zero : archMeasure firstPrimeSlice = 0 :=
  withDensity_absolutelyContinuous _ _ planar_firstPrimeSlice_zero

theorem positiveJumpMeasure_slice_zero : positiveJumpMeasure firstPrimeSlice = 0 := by
  rw [positiveJumpMeasure, Measure.add_apply, archMeasure_slice_zero,
    Measure.sum_apply _ measurableSet_firstPrimeSlice]
  simp only [forwardMeasure_slice_zero, tsum_zero, add_zero]

theorem negativeJumpMeasure_slice_eq : negativeJumpMeasure firstPrimeSlice =
    reflectedMeasure 2 firstPrimeSlice := by
  rw [negativeJumpMeasure, Measure.sum_apply _ measurableSet_firstPrimeSlice]
  exact tsum_eq_single 2 (fun d hd => reflectedMeasure_slice_zero hd)

theorem negativeJumpMeasure_restrict_slice :
    negativeJumpMeasure.restrict firstPrimeSlice = (reflectedMeasure 2).restrict firstPrimeSlice := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS, negativeJumpMeasure,
    Measure.sum_apply _ (hS.inter measurableSet_firstPrimeSlice)]
  apply tsum_eq_single 2
  intro d hd
  exact measure_mono_null inter_subset_right (reflectedMeasure_slice_zero hd)

theorem reflectedDensity_two_pos (x : ℝ) : 0 < reflectedDensity 2 x := by
  have ha : 0 < vonMangoldtAtom 2 := by
    rw [vonMangoldtAtom, if_pos (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  exact mul_pos (mul_pos ha (riemannKernelReal_pos _)) (riemannKernelReal_pos _)

theorem reflectedMeasure_two_slice_eq : reflectedMeasure 2 firstPrimeSlice =
    ∫⁻ x in Ioo (0 : ℝ) (Real.log 2 / 2), ENNReal.ofReal (reflectedDensity 2 x) := by
  rw [reflectedMeasure, Measure.map_apply (by unfold reflectedCurve; fun_prop)
    measurableSet_firstPrimeSlice, reflected_two_preimage, withDensity_apply _ measurableSet_Ioo]
  simp only [Nat.cast_ofNat, Measure.restrict_restrict measurableSet_Ioo, inter_self]

theorem negativeJumpMeasure_slice_pos : 0 < negativeJumpMeasure firstPrimeSlice := by
  rw [negativeJumpMeasure_slice_eq, reflectedMeasure_two_slice_eq,
    setLIntegral_pos_iff (continuous_reflectedDensity 2).measurable.ennreal_ofReal]
  have hs : Function.support (fun x => ENNReal.ofReal (reflectedDensity 2 x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (reflectedDensity_two_pos x)).ne'
  rw [hs, univ_inter, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); linarith)

theorem negativeJumpMeasure_slice_lt_top : negativeJumpMeasure firstPrimeSlice < ∞ := by
  rw [negativeJumpMeasure_slice_eq, reflectedMeasure_two_slice_eq]
  have hi : IntegrableOn (reflectedDensity 2) (Ioo (0 : ℝ) (Real.log 2 / 2)) :=
    (continuous_reflectedDensity 2).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => (reflectedDensity_two_pos x).le))]
  exact ENNReal.ofReal_lt_top

/-- The actual reflected jump kernel has a nonzero negative singular component. -/
theorem negativeJumpMeasure_not_le_positive : ¬ negativeJumpMeasure ≤ positiveJumpMeasure := by
  intro h
  have hc := h firstPrimeSlice
  rw [positiveJumpMeasure_slice_zero] at hc
  exact (not_le_of_gt negativeJumpMeasure_slice_pos) hc

theorem diagonalMeasure_slice_zero (ν : Measure ℝ) :
    Measure.map (fun x : ℝ => (x, x)) ν firstPrimeSlice = 0 := by
  rw [Measure.map_apply (by fun_prop) measurableSet_firstPrimeSlice,
    diagonal_preimage_empty, measure_empty]

/-- No strictly positive scalar reweighting, absolutely continuous correction, or
diagonal killing measure removes the retained negative prime component. -/
theorem negative_component_survives_positive_gauge
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) (hpos : ∀ p, 0 < g p)
    (A : Measure (ℝ × ℝ)) (hA : A ≪ (volume : Measure ℝ).prod volume) (ν : Measure ℝ) :
    ¬ negativeJumpMeasure.withDensity g ≤
      positiveJumpMeasure.withDensity g + A + Measure.map (fun x : ℝ => (x, x)) ν := by
  have hp : positiveJumpMeasure.withDensity g firstPrimeSlice = 0 :=
    withDensity_absolutelyContinuous _ _ positiveJumpMeasure_slice_zero
  have hn : 0 < negativeJumpMeasure.withDensity g firstPrimeSlice := by
    rw [withDensity_apply _ measurableSet_firstPrimeSlice, setLIntegral_pos_iff hg]
    have hs : Function.support g = univ := by
      ext p
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (hpos p).ne'
    rw [hs, univ_inter]
    exact negativeJumpMeasure_slice_pos
  intro h
  have hc := h firstPrimeSlice
  rw [Measure.add_apply, Measure.add_apply, hp, hA planar_firstPrimeSlice_zero,
    diagonalMeasure_slice_zero, zero_add, zero_add] at hc
  exact (not_le_of_gt hn) hc

/-- Integration against the negative component uses exactly the original prime
coefficient and the two original theta factors. -/
theorem lintegral_reflectedMeasure (d : ℕ) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂reflectedMeasure d) =
      ∫⁻ x in Ioo (0 : ℝ) (Real.log d / 2),
        ENNReal.ofReal (reflectedDensity d x) * F (x, Real.log d - x) := by
  have hcurve : Measurable (reflectedCurve d) := by unfold reflectedCurve; fun_prop
  rw [reflectedMeasure, lintegral_map hF hcurve]
  exact lintegral_withDensity_eq_lintegral_mul _
    (continuous_reflectedDensity d).measurable.ennreal_ofReal (hF.comp hcurve)

def reflectedDifference (v : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) (Real.log d / 2),
    reflectedDensity d x * (v x - v (Real.log d - x)) ^ 2

theorem reflectedDifference_as_measure {v : ℝ → ℝ} (hv : Continuous v) (d : ℕ) :
    ENNReal.ofReal (reflectedDifference v d) =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((v p.1 - v p.2) ^ 2) ∂reflectedMeasure d := by
  have hF : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((v p.1 - v p.2) ^ 2)) :=
    (((hv.comp continuous_fst).sub (hv.comp continuous_snd)).pow 2).measurable.ennreal_ofReal
  rw [lintegral_reflectedMeasure d hF]
  have hi : IntegrableOn (fun x => reflectedDensity d x * (v x - v (Real.log d - x)) ^ 2)
      (Ioo (0 : ℝ) (Real.log d / 2)) :=
    ((continuous_reflectedDensity d).mul
      ((hv.sub (hv.comp (continuous_const.sub continuous_id))).pow 2)).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  rw [reflectedDifference, ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => mul_nonneg (reflectedDensity_nonneg d x) (sq_nonneg _)))]
  exact lintegral_congr fun x => ENNReal.ofReal_mul (reflectedDensity_nonneg d x)

/-- Exact link to every original prime jump: its reflected negative difference
term is accompanied by the original positive collar killing density. -/
theorem integral_primeJump_eq_reflected_difference {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (d : ℕ) :
    (∫ x, phiDoobPrimeJump v d x) =
      vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity v (Real.log d) x) +
      2 * (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x) -
      2 * reflectedDifference v d := by
  have hsum := integral_phiDoobCollarSumSq_add_diffSq_eq_killing hv (Real.log d)
  have hdiff := integral_phiDoobCollarDiffSq_eq_two_mul_half hv (Real.log_natCast_nonneg d)
  have hcollar : (∫ x in Ioo (0 : ℝ) (Real.log d), phiDoobCollarSumSq v (Real.log d) x) =
      (∫ x in Ioo (0 : ℝ) (Real.log d), phiDoobCollarKillingDensity v (Real.log d) x) -
      2 * ∫ x in Ioo (0 : ℝ) (Real.log d / 2),
        phiDoobArchShiftJump v (Real.log d - 2 * x) x := by linarith
  have hD : reflectedDifference v d = vonMangoldtAtom d *
      ∫ x in Ioo (0 : ℝ) (Real.log d / 2),
        phiDoobArchShiftJump v (Real.log d - 2 * x) x := by
    rw [reflectedDifference, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    unfold reflectedDensity phiDoobArchShiftJump
    dsimp only
    rw [show x + (Real.log d - 2 * x) = Real.log d - x by ring]
    ring
  rw [integral_phiDoobPrimeJump_eq_halfLine_of_odd hv hvc hodd]
  change 2 * (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v d x) +
    vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d), phiDoobCollarSumSq v (Real.log d) x) = _
  rw [hcollar, hD]
  ring

/-- The unavoidable negative reflected measure is compensated exactly by the
original collar diagonal, giving the retained positive crossing energy. -/
theorem primeCrossing_eq_compensation {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (d : ℕ) :
    CHMDPrimeCuts.primeCrossing v d =
      vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity v (Real.log d) x) - 2 * reflectedDifference v d := by
  have hj (x : ℝ) : phiDoobPrimeJump (fun y => v (-y)) d x = phiDoobPrimeJump v d x := by
    simp only [phiDoobPrimeJump, hodd]
    ring
  have hs := CHMDPrimeCuts.integral_primeJump_split hv hvc d
  simp_rw [hj] at hs
  have hr := integral_primeJump_eq_reflected_difference hv hvc hodd d
  linarith

/-- The complete compensated reflected source has the positive finite-divisor
cut expansion. No prime power or theta index is discarded. -/
theorem compensated_source_hasSum_cuts {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    HasSum (fun N : ℕ+ => ∫ u, CHMDPrimeCuts.cutDensity N v u)
      (∑' d : ℕ, (vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity v (Real.log d) x) - 2 * reflectedDifference v d)) := by
  simpa only [primeCrossing_eq_compensation hv hvc hodd] using
    CHMDPrimeCuts.compact_primeCrossing_hasSum_cuts hv hvc

/-- All ordered reflected prime lines, including inactive indices with empty collars. -/
def reflectedSlice (d : ℕ) : Set (ℝ × ℝ) :=
  (Prod.fst ⁻¹' Ioo (0 : ℝ) (Real.log d / 2)) ∩ {p | p.2 = Real.log d - p.1}

def reflectedSupport : Set (ℝ × ℝ) := ⋃ d : ℕ, reflectedSlice d

theorem measurableSet_reflectedSlice (d : ℕ) : MeasurableSet (reflectedSlice d) :=
  (measurable_fst measurableSet_Ioo).inter
    (isClosed_eq continuous_snd (continuous_const.sub continuous_fst)).measurableSet

theorem measurableSet_reflectedSupport : MeasurableSet reflectedSupport :=
  MeasurableSet.iUnion measurableSet_reflectedSlice

theorem planar_reflectedSlice_zero (d : ℕ) : (volume.prod volume) (reflectedSlice d) = 0 := by
  rw [Measure.prod_apply (measurableSet_reflectedSlice d)]
  have hz (x : ℝ) : volume {y : ℝ | (x, y) ∈ reflectedSlice d} = 0 := by
    apply measure_mono_null (t := {Real.log d - x}) _ (measure_singleton _)
    intro y hy
    exact hy.2
  calc
    _ = ∫⁻ _x : ℝ, (0 : ℝ≥0∞) := lintegral_congr hz
    _ = 0 := lintegral_zero

theorem forwardMeasure_reflectedSlice_zero (m d : ℕ) :
    forwardMeasure m (reflectedSlice d) = 0 := by
  rw [forwardMeasure, Measure.map_apply (by unfold forwardCurve; fun_prop)
    (measurableSet_reflectedSlice d)]
  have hp : forwardCurve m ⁻¹' reflectedSlice d ⊆ {(Real.log d - Real.log m) / 2} := by
    intro x hx
    have he : x + Real.log m = Real.log d - x := hx.2
    change x = (Real.log d - Real.log m) / 2
    linarith
  apply measure_mono_null hp
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left (measure_singleton _)

theorem positiveJumpMeasure_reflectedSupport_zero : positiveJumpMeasure reflectedSupport = 0 := by
  have ha : archMeasure reflectedSupport = 0 := by
    apply withDensity_absolutelyContinuous
    exact measure_iUnion_null planar_reflectedSlice_zero
  have hf (m : ℕ) : forwardMeasure m reflectedSupport = 0 :=
    measure_iUnion_null (forwardMeasure_reflectedSlice_zero m)
  rw [positiveJumpMeasure, Measure.add_apply, ha,
    Measure.sum_apply _ measurableSet_reflectedSupport]
  simp only [hf, tsum_zero, add_zero]

theorem reflectedMeasure_compl_support_zero (d : ℕ) :
    reflectedMeasure d reflectedSupportᶜ = 0 := by
  rw [reflectedMeasure, Measure.map_apply (by unfold reflectedCurve; fun_prop)
    measurableSet_reflectedSupport.compl]
  have hp : reflectedCurve d ⁻¹' reflectedSupportᶜ ⊆ (Ioo (0 : ℝ) (Real.log d / 2))ᶜ := by
    intro x hx hi
    apply hx
    exact mem_iUnion.mpr ⟨d, hi, rfl⟩
  apply measure_mono_null hp
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  simp

theorem negativeJumpMeasure_compl_support_zero : negativeJumpMeasure reflectedSupportᶜ = 0 := by
  rw [negativeJumpMeasure, Measure.sum_apply _ measurableSet_reflectedSupport.compl]
  simp only [reflectedMeasure_compl_support_zero, tsum_zero]

/-- Exact global sign separation: the positive archimedean and same-side prime
measure is mutually singular with the entire reflected-prime negative measure. -/
theorem positive_negative_mutuallySingular : positiveJumpMeasure ⟂ₘ negativeJumpMeasure :=
  ⟨reflectedSupport, measurableSet_reflectedSupport, positiveJumpMeasure_reflectedSupport_zero,
    negativeJumpMeasure_compl_support_zero⟩

/-- Despite its negative jump component, the original compensated collar source
is strictly positive on every nonzero odd compact test. -/
theorem compensated_source_pos {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hne : v ≠ 0) :
    0 < ∑' d : ℕ, (vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
      phiDoobCollarKillingDensity v (Real.log d) x) - 2 * reflectedDifference v d) := by
  rw [← (compensated_source_hasSum_cuts hv hvc hodd).tsum_eq]
  exact CHMDPrimeCuts.crossing_cuts_pos hv hvc hne

/-- The compensated singular component occurs in the full original Doob source;
the remaining cosh subtraction is explicit. -/
theorem doob_source_eq_reflected_compensation {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      phiDoobArchJumpEnergy v + 2 * CHMDPrimeCuts.sameSide v +
      (∑' d : ℕ, (vonMangoldtAtom d * (∫ x in Ioo (0 : ℝ) (Real.log d),
        phiDoobCollarKillingDensity v (Real.log d) x) - 2 * reflectedDifference v d)) -
      phiDoobCoshMass (fun x => v x ^ 2) := by
  have hs : CHMDPrimeCuts.sameSide (fun x => v (-x)) = CHMDPrimeCuts.sameSide v := by
    apply tsum_congr
    intro d
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [phiDoobPrimeJump, hodd]
    ring
  rw [CHMDPrimeCuts.doob_source_eq_positive_cuts_sub_cosh hv hvc, hs,
    (compensated_source_hasSum_cuts hv.continuous hvc hodd).tsum_eq]
  ring

end RHTower.CHMDReflectedPrime
