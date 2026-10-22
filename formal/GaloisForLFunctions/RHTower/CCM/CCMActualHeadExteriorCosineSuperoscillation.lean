import GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorGaugeCoerciveCompactReduction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exterior cosine superoscillation for CCM gauges

Finite binomial packets supported in an arbitrary exterior frequency band reproduce a prescribed
lower-frequency cosine pointwise. Their real parts are represented exactly as differences of two
finite positive exterior measures, hence are exact null gauges for every compatible Suzuki
aperture. Genuine frequency downshift has a sharp cost: packet coefficient variation—and exactly
the combined mass of those two measures—is `(2c - 1)^N`, so it diverges exponentially when `c > 1`.

This closes the qualitative compact-expressivity question while isolating the quantitative barrier:
local approximation alone cannot produce a globally nonnegative corrected CCM representative,
because the mass budget controlling its tails explodes along this canonical approximation.
-/

open scoped BigOperators Topology
open Filter Finset MeasureTheory

namespace RHTower

noncomputable section

/-- First-order exponential scaling along positive natural denominators. -/
lemma tendsto_natSucc_mul_exp_div_sub_one (w : ℂ) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
        (Complex.exp (w / ((n + 1 : ℕ) : ℂ)) - 1))
      atTop (𝓝 w) := by
  by_cases hw : w = 0
  · simp [hw]
  have ht : Tendsto (fun n : ℕ => w / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝 0)))
  have htne : ∀ n : ℕ, w / ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro n
    exact div_ne_zero hw (by exact_mod_cast Nat.succ_ne_zero n)
  have htp : Tendsto (fun n : ℕ => w / ((n + 1 : ℕ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [nhdsWithin, tendsto_inf]
    refine ⟨ht, ?_⟩
    rw [tendsto_principal]
    exact Filter.Eventually.of_forall (fun n => htne n)
  have hslope := (Complex.hasDerivAt_exp 0).tendsto_slope_zero.comp htp
  have hwconst : Tendsto (fun _ : ℕ => w) atTop (𝓝 w) := tendsto_const_nhds
  have hmul := hwconst.mul hslope
  convert hmul using 1
  · ext n
    simp only [Function.comp_apply, zero_add, Complex.exp_zero, smul_eq_mul]
    field_simp [hw]
  · simp

/-- A finite exponential packet whose binomial frequencies lie in a prescribed exterior band. -/
def exteriorSuperoscillationPacket
    (H δ c x : ℝ) (N : ℕ) : ℂ :=
  Complex.exp (((H * x : ℝ) : ℂ) * Complex.I) *
    (((1 - c : ℝ) : ℂ) + (c : ℂ) *
      Complex.exp ((((-δ * x : ℝ) : ℂ) * Complex.I) / (N : ℂ))) ^ N

/-- Real coefficient of the `k`th exterior atom in an `N`-packet. -/
def exteriorSuperoscillationCoefficient (c : ℝ) (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) * c ^ k * (1 - c) ^ (N - k)

/-- Frequency of the `k`th exterior atom in an `N`-packet. -/
def exteriorSuperoscillationFrequency (H δ : ℝ) (N k : ℕ) : ℝ :=
  H - (k : ℝ) * δ / (N : ℝ)

private theorem integrable_finsetIndexedWeightedDirac
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (node : ι → ℝ) (f : ℝ → ℝ) :
    Integrable f
      (∑ k ∈ s, ENNReal.ofReal (w k) • Measure.dirac (node k)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Integrable.smul_measure (integrable_dirac (by simp)) (by simp)).add_measure ih

private theorem integral_finsetIndexedWeightedDirac
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (node : ι → ℝ) (f : ℝ → ℝ) :
    (∫ h, f h ∂(∑ k ∈ s,
      ENNReal.ofReal (w k) • Measure.dirac (node k))) =
      ∑ k ∈ s, w k * f (node k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a s)
      have hws : ∀ k ∈ s, 0 ≤ w k := fun k hk => hw k (Finset.mem_insert_of_mem hk)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        integral_add_measure
          (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
          (integrable_finsetIndexedWeightedDirac s w node f),
        integral_smul_measure, integral_dirac, ih hws,
        ENNReal.toReal_ofReal hwa, smul_eq_mul]

/-- Positive part of the finite signed exterior measure carried by a packet. -/
def exteriorSuperoscillationPositiveMeasure
    (H δ c : ℝ) (N : ℕ) : Measure ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    ENNReal.ofReal (max (exteriorSuperoscillationCoefficient c N k) 0) •
      Measure.dirac
        (exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))

/-- Negative part of the finite signed exterior measure carried by a packet. -/
def exteriorSuperoscillationNegativeMeasure
    (H δ c : ℝ) (N : ℕ) : Measure ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    ENNReal.ofReal (max (-exteriorSuperoscillationCoefficient c N k) 0) •
      Measure.dirac
        (exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))

instance isFiniteMeasure_exteriorSuperoscillationPositiveMeasure
    (H δ c : ℝ) (N : ℕ) :
    IsFiniteMeasure (exteriorSuperoscillationPositiveMeasure H δ c N) := by
  unfold exteriorSuperoscillationPositiveMeasure
  letI (k : ℕ) : IsFiniteMeasure
      (ENNReal.ofReal (max (exteriorSuperoscillationCoefficient c N k) 0) •
        Measure.dirac
          (exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

instance isFiniteMeasure_exteriorSuperoscillationNegativeMeasure
    (H δ c : ℝ) (N : ℕ) :
    IsFiniteMeasure (exteriorSuperoscillationNegativeMeasure H δ c N) := by
  unfold exteriorSuperoscillationNegativeMeasure
  letI (k : ℕ) : IsFiniteMeasure
      (ENNReal.ofReal (max (-exteriorSuperoscillationCoefficient c N k) 0) •
        Measure.dirac
          (exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

/-- Exact finite exponential expansion of the packet. -/
theorem exteriorSuperoscillationPacket_eq_sum
    (H δ c x : ℝ) (N : ℕ) :
    exteriorSuperoscillationPacket H δ c x N =
      ∑ k ∈ Finset.range (N + 1),
        (exteriorSuperoscillationCoefficient c N k : ℂ) *
          Complex.exp (((exteriorSuperoscillationFrequency H δ N k * x : ℝ) : ℂ) *
            Complex.I) := by
  unfold exteriorSuperoscillationPacket
  rw [add_comm, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp [exteriorSuperoscillationCoefficient, exteriorSuperoscillationFrequency]
  push_cast
  rw [mul_pow, ← Complex.exp_nat_mul]
  let A : ℂ := (H : ℂ) * (x : ℂ) * Complex.I
  let B : ℂ := (k : ℂ) * ((-(δ : ℂ) * (x : ℂ) * Complex.I) / (N : ℂ))
  let C : ℂ := ((H : ℂ) - (k : ℂ) * (δ : ℂ) / (N : ℂ)) * (x : ℂ) * Complex.I
  let K : ℂ := (N.choose k : ℂ) * (c : ℂ) ^ k * (1 - (c : ℂ)) ^ (N - k)
  have hExp : Complex.exp A * Complex.exp B = Complex.exp C := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [A, B, C]
    ring
  calc
    _ = K * (Complex.exp A * Complex.exp B) := by
      dsimp [K, A, B]
      ring
    _ = K * Complex.exp C := by rw [hExp]
    _ = _ := by
      dsimp [K, C]

/-- Real cosine polynomial carried by the same exterior frequencies as the complex packet. -/
def exteriorSuperoscillationCosineSum
    (H δ c x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1),
    exteriorSuperoscillationCoefficient c N k *
      Real.cos (exteriorSuperoscillationFrequency H δ N k * x)

/-- The cosine polynomial is exactly the real part of the complex packet. -/
theorem exteriorSuperoscillationCosineSum_eq_re
    (H δ c x : ℝ) (N : ℕ) :
    exteriorSuperoscillationCosineSum H δ c x N =
      (exteriorSuperoscillationPacket H δ c x N).re := by
  rw [exteriorSuperoscillationPacket_eq_sum]
  rw [Complex.re_sum]
  simp only [exteriorSuperoscillationCosineSum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Complex.exp_ofReal_mul_I_re]

/-- Positive-minus-positive atomic exterior measures realize the cosine packet exactly. -/
theorem exteriorCosineMeasureGauge_sub_eq_cosineSum
    (H δ c xi : ℝ) (N : ℕ) :
    ccmActualHeadExteriorCosineMeasureGauge
        (exteriorSuperoscillationPositiveMeasure H δ c N) xi -
      ccmActualHeadExteriorCosineMeasureGauge
        (exteriorSuperoscillationNegativeMeasure H δ c N) xi =
      exteriorSuperoscillationCosineSum H δ c xi N := by
  let node : ℕ → ℝ := fun k =>
    exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi)
  let f : ℝ → ℝ := fun h => Real.cos (2 * Real.pi * h * xi)
  have hpos :
      (∫ h, f h ∂exteriorSuperoscillationPositiveMeasure H δ c N) =
        ∑ k ∈ Finset.range (N + 1),
          max (exteriorSuperoscillationCoefficient c N k) 0 * f (node k) := by
    unfold exteriorSuperoscillationPositiveMeasure
    exact integral_finsetIndexedWeightedDirac _ _
      (fun k hk => le_max_right _ _) _ _
  have hneg :
      (∫ h, f h ∂exteriorSuperoscillationNegativeMeasure H δ c N) =
        ∑ k ∈ Finset.range (N + 1),
          max (-exteriorSuperoscillationCoefficient c N k) 0 * f (node k) := by
    unfold exteriorSuperoscillationNegativeMeasure
    exact integral_finsetIndexedWeightedDirac _ _
      (fun k hk => le_max_right _ _) _ _
  unfold ccmActualHeadExteriorCosineMeasureGauge
  change (∫ h, f h ∂exteriorSuperoscillationPositiveMeasure H δ c N) -
      (∫ h, f h ∂exteriorSuperoscillationNegativeMeasure H δ c N) = _
  rw [hpos, hneg, ← Finset.sum_sub_distrib]
  unfold exteriorSuperoscillationCosineSum
  apply Finset.sum_congr rfl
  intro k hk
  have hphase :
      2 * Real.pi * node k * xi =
        exteriorSuperoscillationFrequency H δ N k * xi := by
    dsimp [node]
    field_simp [Real.pi_ne_zero]
  rw [show f (node k) =
      Real.cos (exteriorSuperoscillationFrequency H δ N k * xi) by
        dsimp [f]
        rw [hphase]]
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- The signed atomic packet is an exact corrected-symbol gauge representative. -/
theorem correctedExteriorSuperoscillationRepresentative_eq
    (a : SuzukiPositiveAperture) (H δ c xi : ℝ) (N : ℕ) :
    ccmCorrectedExteriorMeasureGaugeRepresentative a
        (exteriorSuperoscillationPositiveMeasure H δ c N)
        (exteriorSuperoscillationNegativeMeasure H δ c N) xi =
      correctedCCMSymbol a.1 (2 * Real.pi * xi) +
        exteriorSuperoscillationCosineSum H δ c xi N := by
  unfold ccmCorrectedExteriorMeasureGaugeRepresentative
  rw [← exteriorCosineMeasureGauge_sub_eq_cosineSum]
  ring

/-- Total mass of the packet's positive measure is its positive coefficient mass. -/
theorem exteriorSuperoscillationPositiveMeasure_measureReal_univ
    (H δ c : ℝ) (N : ℕ) :
    (exteriorSuperoscillationPositiveMeasure H δ c N).real Set.univ =
      ∑ k ∈ Finset.range (N + 1),
        max (exteriorSuperoscillationCoefficient c N k) 0 := by
  have h := integral_finsetIndexedWeightedDirac
    (Finset.range (N + 1))
    (fun k => max (exteriorSuperoscillationCoefficient c N k) 0)
    (fun k hk => le_max_right _ _)
    (fun k => exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))
    (fun _ => (1 : ℝ))
  unfold exteriorSuperoscillationPositiveMeasure
  simpa using h

/-- Total mass of the packet's negative measure is its negative coefficient mass. -/
theorem exteriorSuperoscillationNegativeMeasure_measureReal_univ
    (H δ c : ℝ) (N : ℕ) :
    (exteriorSuperoscillationNegativeMeasure H δ c N).real Set.univ =
      ∑ k ∈ Finset.range (N + 1),
        max (-exteriorSuperoscillationCoefficient c N k) 0 := by
  have h := integral_finsetIndexedWeightedDirac
    (Finset.range (N + 1))
    (fun k => max (-exteriorSuperoscillationCoefficient c N k) 0)
    (fun k hk => le_max_right _ _)
    (fun k => exteriorSuperoscillationFrequency H δ N k / (2 * Real.pi))
    (fun _ => (1 : ℝ))
  unfold exteriorSuperoscillationNegativeMeasure
  simpa using h

/-- Combined positive and negative measure mass is exactly coefficient total variation. -/
theorem exteriorSuperoscillationMeasure_mass_eq_sum_abs
    (H δ c : ℝ) (N : ℕ) :
    (exteriorSuperoscillationPositiveMeasure H δ c N).real Set.univ +
      (exteriorSuperoscillationNegativeMeasure H δ c N).real Set.univ =
      ∑ k ∈ Finset.range (N + 1),
        |exteriorSuperoscillationCoefficient c N k| := by
  rw [exteriorSuperoscillationPositiveMeasure_measureReal_univ,
    exteriorSuperoscillationNegativeMeasure_measureReal_univ,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  let q := exteriorSuperoscillationCoefficient c N k
  change max q 0 + max (-q) 0 = |q|
  rcases le_total q 0 with hq | hq
  · have hnq : 0 ≤ -q := neg_nonneg.mpr hq
    rw [max_eq_right hq, max_eq_left hnq, abs_of_nonpos hq]
    ring
  · have hnq : -q ≤ 0 := neg_nonpos.mpr hq
    rw [max_eq_left hq, max_eq_right hnq, abs_of_nonneg hq]
    ring

/-- Every binomial frequency stays exterior when the whole packet band does. -/
theorem exteriorSuperoscillationFrequency_ge
    {H₀ H δ : ℝ} {N k : ℕ}
    (hδ : 0 ≤ δ) (hband : H₀ ≤ H - δ) (hk : k ≤ N) :
    H₀ ≤ exteriorSuperoscillationFrequency H δ N k := by
  unfold exteriorSuperoscillationFrequency
  by_cases hN : N = 0
  · subst N
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [Nat.cast_zero, zero_mul, zero_div, sub_zero]
    linarith
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hkcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have hquot : (k : ℝ) * δ / (N : ℝ) ≤ δ := by
    rw [div_le_iff₀ hNpos]
    nlinarith
  linarith

/-- Positive packet measure is carried by the rescaled exterior half-line. -/
theorem ae_exteriorSuperoscillationPositiveMeasure_ge
    {H₀ H δ c : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hband : H₀ ≤ H - δ) :
    ∀ᵐ h : ℝ ∂exteriorSuperoscillationPositiveMeasure H δ c N,
      H₀ / (2 * Real.pi) ≤ h := by
  unfold exteriorSuperoscillationPositiveMeasure
  rw [ae_finsetSum_measure_iff]
  intro k hk
  apply Measure.ae_smul_measure
  rw [ae_dirac_iff measurableSet_Ici]
  exact div_le_div_of_nonneg_right
    (exteriorSuperoscillationFrequency_ge hδ hband (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    (by positivity)

/-- Negative packet measure has the same exterior carrier. -/
theorem ae_exteriorSuperoscillationNegativeMeasure_ge
    {H₀ H δ c : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hband : H₀ ≤ H - δ) :
    ∀ᵐ h : ℝ ∂exteriorSuperoscillationNegativeMeasure H δ c N,
      H₀ / (2 * Real.pi) ≤ h := by
  unfold exteriorSuperoscillationNegativeMeasure
  rw [ae_finsetSum_measure_iff]
  intro k hk
  apply Measure.ae_smul_measure
  rw [ae_dirac_iff measurableSet_Ici]
  exact div_le_div_of_nonneg_right
    (exteriorSuperoscillationFrequency_ge hδ hband (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    (by positivity)

/-- Aperture-scaled positive packet measure is supported beyond physical diameter. -/
theorem ae_exteriorSuperoscillationPositiveMeasure_two_aperture_le
    (a : SuzukiPositiveAperture) {H δ c : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hband : 4 * Real.pi * a.1 ≤ H - δ) :
    ∀ᵐ h : ℝ ∂exteriorSuperoscillationPositiveMeasure H δ c N,
      2 * a.1 ≤ h := by
  have h := ae_exteriorSuperoscillationPositiveMeasure_ge
    (H₀ := 4 * Real.pi * a.1) (H := H) (δ := δ) (c := c) (N := N) hδ hband
  have heq : 4 * Real.pi * a.1 / (2 * Real.pi) = 2 * a.1 := by
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [heq] using h

/-- Aperture-scaled negative packet measure is supported beyond physical diameter. -/
theorem ae_exteriorSuperoscillationNegativeMeasure_two_aperture_le
    (a : SuzukiPositiveAperture) {H δ c : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hband : 4 * Real.pi * a.1 ≤ H - δ) :
    ∀ᵐ h : ℝ ∂exteriorSuperoscillationNegativeMeasure H δ c N,
      2 * a.1 ≤ h := by
  have h := ae_exteriorSuperoscillationNegativeMeasure_ge
    (H₀ := 4 * Real.pi * a.1) (H := H) (δ := δ) (c := c) (N := N) hδ hband
  have heq : 4 * Real.pi * a.1 / (2 * Real.pi) = 2 * a.1 := by
    field_simp [Real.pi_ne_zero]
    ring
  simpa only [heq] using h

/-- Every exterior superoscillation packet is an exact aperture null gauge. -/
theorem integral_exteriorSuperoscillationCosineSum_mul_density_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (H δ c : ℝ) (N : ℕ) (hδ : 0 ≤ δ)
    (hband : 4 * Real.pi * a.1 ≤ H - δ) :
    (∫ xi : ℝ, exteriorSuperoscillationCosineSum H δ c xi N *
      ‖(fourierUnitary (f : SoninL2) : ℝ → ℂ) xi‖ ^ 2) = 0 := by
  have hzero := integral_ccmActualHeadExteriorCosineMeasureGauge_sub_mul_density_eq_zero
    a f
    (exteriorSuperoscillationPositiveMeasure H δ c N)
    (exteriorSuperoscillationNegativeMeasure H δ c N)
    (ae_exteriorSuperoscillationPositiveMeasure_two_aperture_le a hδ hband)
    (ae_exteriorSuperoscillationNegativeMeasure_two_aperture_le a hδ hband)
  simpa only [exteriorCosineMeasureGauge_sub_eq_cosineSum] using hzero

/-- Exact total-variation cost of the canonical downshifting packet. -/
theorem sum_abs_exteriorSuperoscillationCoefficient
    {c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      |exteriorSuperoscillationCoefficient c N k|) = (2 * c - 1) ^ N := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have h1c : |1 - c| = c - 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    ring
  calc
    (∑ k ∈ Finset.range (N + 1),
        |exteriorSuperoscillationCoefficient c N k|) =
        ∑ k ∈ Finset.range (N + 1),
          c ^ k * (c - 1) ^ (N - k) * (N.choose k : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hchoose0 : (0 : ℝ) ≤ (N.choose k : ℝ) := Nat.cast_nonneg _
            rw [exteriorSuperoscillationCoefficient, abs_mul, abs_mul, abs_pow, abs_pow,
              abs_of_nonneg hchoose0, abs_of_nonneg hc0, h1c]
            ring
    _ = (c + (c - 1)) ^ N := (add_pow c (c - 1) N).symm
    _ = (2 * c - 1) ^ N := by ring

/-- Exact combined measure mass in the downshifting regime. -/
theorem exteriorSuperoscillationMeasure_mass
    {c : ℝ} (hc : 1 ≤ c) (H δ : ℝ) (N : ℕ) :
    (exteriorSuperoscillationPositiveMeasure H δ c N).real Set.univ +
      (exteriorSuperoscillationNegativeMeasure H δ c N).real Set.univ =
      (2 * c - 1) ^ N := by
  rw [exteriorSuperoscillationMeasure_mass_eq_sum_abs,
    sum_abs_exteriorSuperoscillationCoefficient hc]

/-- Packet coefficients have net mass one despite potentially enormous total variation. -/
theorem sum_exteriorSuperoscillationCoefficient (c : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      exteriorSuperoscillationCoefficient c N k) = 1 := by
  calc
    (∑ k ∈ Finset.range (N + 1),
        exteriorSuperoscillationCoefficient c N k) =
        (c + (1 - c)) ^ N := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k hk
          unfold exteriorSuperoscillationCoefficient
          ring
    _ = 1 := by simp

/-- A target strictly below an exterior band forces the superoscillation parameter above one. -/
theorem one_lt_superoscillationParameter_of_effectiveFrequency_lt
    {H₀ H δ c : ℝ} (hδ : 0 < δ)
    (hband : H₀ ≤ H - δ) (hlow : H - c * δ < H₀) :
    1 < c := by
  nlinarith

/-- In the genuine downshift regime, canonical packet variation diverges exponentially. -/
theorem tendsto_sum_abs_exteriorSuperoscillationCoefficient_atTop
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        |exteriorSuperoscillationCoefficient c N k|)
      atTop atTop := by
  have hbase : 1 < 2 * c - 1 := by linarith
  convert tendsto_pow_atTop_atTop_of_one_lt hbase using 1
  ext N
  exact sum_abs_exteriorSuperoscillationCoefficient hc.le N

/-- Signed packet measure mass diverges for every genuine downshift. -/
theorem tendsto_exteriorSuperoscillationMeasure_mass_atTop
    {c : ℝ} (hc : 1 < c) (H δ : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (exteriorSuperoscillationPositiveMeasure H δ c N).real Set.univ +
          (exteriorSuperoscillationNegativeMeasure H δ c N).real Set.univ)
      atTop atTop := by
  convert tendsto_sum_abs_exteriorSuperoscillationCoefficient_atTop hc using 1
  ext N
  exact exteriorSuperoscillationMeasure_mass_eq_sum_abs H δ c N

/-- Canonical exterior-frequency approximation to a lower-frequency cosine. -/
def exteriorCosineSuperoscillation
    (H₀ lam x : ℝ) (N : ℕ) : ℝ :=
  exteriorSuperoscillationCosineSum (H₀ + 1) 1 (H₀ + 1 - lam) x N

/-- Every atom in the canonical approximation lies at or above `H₀`. -/
theorem exteriorCosineSuperoscillation_frequency_ge
    (H₀ : ℝ) {N k : ℕ} (hk : k ≤ N) :
    H₀ ≤ exteriorSuperoscillationFrequency (H₀ + 1) 1 N k := by
  apply exteriorSuperoscillationFrequency_ge (H₀ := H₀) (H := H₀ + 1) (δ := 1)
  · norm_num
  · ring_nf
    exact le_rfl
  · exact hk

/-- Exact variation formula for the canonical exterior approximation. -/
theorem sum_abs_exteriorCosineSuperoscillationCoefficient
    {H₀ lam : ℝ} (hlam : lam ≤ H₀) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      |exteriorSuperoscillationCoefficient (H₀ + 1 - lam) N k|) =
        (2 * (H₀ - lam) + 1) ^ N := by
  rw [sum_abs_exteriorSuperoscillationCoefficient (by linarith)]
  congr 1
  ring

/-- Strict downshift makes canonical exterior approximation variation diverge. -/
theorem tendsto_sum_abs_exteriorCosineSuperoscillationCoefficient_atTop
    {H₀ lam : ℝ} (hlam : lam < H₀) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        |exteriorSuperoscillationCoefficient (H₀ + 1 - lam) N k|)
      atTop atTop := by
  exact tendsto_sum_abs_exteriorSuperoscillationCoefficient_atTop (by linarith)

/-- First-order exponential scaling along all natural denominators; the `N = 0` value is harmless. -/
lemma tendsto_natCast_mul_exp_div_sub_one (w : ℂ) :
    Tendsto
      (fun N : ℕ => (N : ℂ) * (Complex.exp (w / (N : ℂ)) - 1))
      atTop (𝓝 w) := by
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by
    simpa [Nat.cast_add, Nat.cast_one] using tendsto_natSucc_mul_exp_div_sub_one w)

/-- The exterior packet superoscillates at the lower effective frequency `H - cδ`. -/
theorem tendsto_exteriorSuperoscillationPacket
    (H δ c x : ℝ) :
    Tendsto (fun N : ℕ => exteriorSuperoscillationPacket H δ c x N)
      atTop
      (𝓝 (Complex.exp ((((H - c * δ) * x : ℝ) : ℂ) * Complex.I))) := by
  let w : ℂ := (((-δ * x : ℝ) : ℂ) * Complex.I)
  have hcore := tendsto_natCast_mul_exp_div_sub_one w
  have hc : Tendsto
      (fun N : ℕ => (N : ℂ) *
        ((c : ℂ) * (Complex.exp (w / (N : ℂ)) - 1)))
      atTop (𝓝 ((c : ℂ) * w)) := by
    have hcconst : Tendsto (fun _ : ℕ => (c : ℂ)) atTop (𝓝 (c : ℂ)) :=
      tendsto_const_nhds
    convert (hcconst.mul hcore) using 1
    · ext N
      ring
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto hc
  have hpref : Tendsto
      (fun _ : ℕ => Complex.exp (((H * x : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 (Complex.exp (((H * x : ℝ) : ℂ) * Complex.I))) := tendsto_const_nhds
  have hmul := hpref.mul hpow
  convert hmul using 1
  · ext N
    dsimp [exteriorSuperoscillationPacket, w]
    congr 2
    push_cast
    ring
  · rw [← Complex.exp_add]
    congr 2
    dsimp [w]
    push_cast
    ring

/-- Pointwise compact-core reproduction by exterior cosine atoms. -/
theorem tendsto_exteriorSuperoscillationCosineSum
    (H δ c x : ℝ) :
    Tendsto (fun N : ℕ => exteriorSuperoscillationCosineSum H δ c x N)
      atTop (𝓝 (Real.cos ((H - c * δ) * x))) := by
  have hcomplex := tendsto_exteriorSuperoscillationPacket H δ c x
  have hre := (Complex.continuous_re.tendsto
    (Complex.exp ((((H - c * δ) * x : ℝ) : ℂ) * Complex.I))).comp hcomplex
  convert hre using 1
  · ext N
    exact exteriorSuperoscillationCosineSum_eq_re H δ c x N
  · rw [Complex.exp_ofReal_mul_I_re]

/-- Exterior atoms reproduce any prescribed lower-frequency cosine pointwise. -/
theorem tendsto_exteriorCosineSuperoscillation (H₀ lam x : ℝ) :
    Tendsto (fun N : ℕ => exteriorCosineSuperoscillation H₀ lam x N)
      atTop (𝓝 (Real.cos (lam * x))) := by
  unfold exteriorCosineSuperoscillation
  convert tendsto_exteriorSuperoscillationCosineSum
    (H₀ + 1) 1 (H₀ + 1 - lam) x using 1
  ring_nf

end

end RHTower
