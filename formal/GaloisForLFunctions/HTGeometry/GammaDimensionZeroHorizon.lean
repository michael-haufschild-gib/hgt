import GaloisForLFunctions.HTGeometry.GammaBaireInverseCoding
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# A dimension-zero constrained horizon for the Euler Gamma function

We choose the linearly receding pole schedule `N(k) = N₀ + k`, where `N₀` is the unconditional
common-collar threshold.  The associated inverse-Gamma horizon is homeomorphic to Baire space and
Gamma reads its histories by deleting the first inverse sheet.

The new assertion proved here is ambient and quantitative: this uncountable Baire horizon has
Hausdorff dimension zero as a subset of `ℂ`.  The proof uses actual Gamma sheets.  Reciprocal
inversion compresses the entire common exterior into a fixed disk, contributing the final
factorial factor in each symbolic cylinder.  Countable cylinder costs therefore factor into tails
of the summable series `(2 / n!)^s`; their products tend to zero for every `s > 0`.
-/

namespace GaloisForLFunctions

open Complex Filter Function Metric Set Topology
open scoped NNReal ENNReal MeasureTheory BigOperators

noncomputable section

/-- The canonical linearly receding cutoff schedule. -/
def gammaThinSchedule (k : ℕ) : ℕ := gammaCommonInverseCollar.threshold + k

theorem gammaThinSchedule_late :
    ∀ k, gammaCommonInverseCollar.threshold ≤ gammaThinSchedule k := by
  intro k
  exact Nat.le_add_right _ _

/-- The constrained Gamma horizon selected by the linearly receding schedule. -/
def gammaConstrainedHorizon : Set ℂ := Set.range (gammaBaireCode gammaThinSchedule)

/-- The constrained horizon is literally a Baire space, not merely a continuous image of one. -/
def gammaConstrainedHorizonHomeomorph :
    (ℕ → ℕ) ≃ₜ gammaConstrainedHorizon :=
  gammaBaireCodeHomeomorph gammaThinSchedule gammaThinSchedule_late

/-- The exact contraction accumulated by the first `d` symbols of a history. -/
def gammaPrefixWeight (N ω : ℕ → ℕ) : ℕ → ℝ≥0
  | 0 => 1
  | d + 1 => gammaExteriorContraction (gammaCodeLabel N ω 0) *
      gammaPrefixWeight (gammaCodeShift N) (gammaCodeShift ω) d

/-- The same accumulated contraction, expressed on a finite word. -/
def gammaWordWeight : (d : ℕ) → (ℕ → ℕ) → (Fin d → ℕ) → ℝ≥0
  | 0, _N, _w => 1
  | d + 1, N, w => gammaExteriorContraction (N 0 + w 0) *
      gammaWordWeight d (gammaCodeShift N) (Fin.tail w)

theorem gammaPrefixWeight_eq_wordWeight (N ω : ℕ → ℕ) (d : ℕ) :
    gammaPrefixWeight N ω d = gammaWordWeight d N (fun i => ω i) := by
  induction d generalizing N ω with
  | zero => rfl
  | succ d ih =>
      simp only [gammaPrefixWeight, gammaWordWeight, gammaCodeLabel]
      congr 1
      simpa [gammaCodeShift, Fin.tail] using
        ih (gammaCodeShift N) (gammaCodeShift ω)

/-- Reciprocal compression supplies a global diameter bound for one actual Gamma sheet. -/
theorem dist_gammaExteriorInverseBranch_le_half_contraction
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {x y : ℂ} (hx : x ∈ gammaExterior) (hy : y ∈ gammaExterior) :
    dist (gammaExteriorInverseBranch n x) (gammaExteriorInverseBranch n y) ≤
      (gammaExteriorContraction n : ℝ) / 2 := by
  have htx := neg_inv_mem_gammaMicroscopeTarget hx
  have hty := neg_inv_mem_gammaMicroscopeTarget hy
  have hrecip : dist (-x⁻¹) (-y⁻¹) ≤ (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall] at htx hty
    calc
      dist (-x⁻¹) (-y⁻¹) ≤ dist (-x⁻¹) 0 + dist 0 (-y⁻¹) := dist_triangle _ _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add htx (by simpa [dist_comm] using hty)
      _ = 1 / 2 := by norm_num
  have hbranch := gammaCommonInverseCollar.lipschitzOn hn
  have hB := hbranch.dist_le_mul (-x⁻¹) htx (-y⁻¹) hty
  rw [gammaExteriorInverseBranch, gammaExteriorInverseBranch, dist_eq_norm]
  simp only [add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  calc
    ‖reciprocalGammaFactorialScale n‖ *
        ‖gammaCommonInverseCollar.branch n (-x⁻¹) -
          gammaCommonInverseCollar.branch n (-y⁻¹)‖
        ≤ ‖reciprocalGammaFactorialScale n‖ * (2 * dist (-x⁻¹) (-y⁻¹)) := by
          gcongr
          simpa only [dist_eq_norm, NNReal.coe_ofNat] using hB
    _ ≤ ‖reciprocalGammaFactorialScale n‖ * (2 * (1 / 2 : ℝ)) := by
          gcongr
    _ = (gammaExteriorContraction n : ℝ) / 2 := by
          simp [gammaExteriorContraction]

/-- Histories with a common nonempty prefix have diameter bounded by the full product of their
actual factorial sheet contractions. -/
theorem dist_gammaBaireCode_le_prefixWeight
    {N ω ν : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) (d : ℕ)
    (hων : ∀ k < d + 1, ω k = ν k) :
    dist (gammaBaireCode N ω) (gammaBaireCode N ν) ≤
      (gammaPrefixWeight N ω (d + 1) : ℝ) / 2 := by
  induction d generalizing N ω ν with
  | zero =>
      have h0 : ω 0 = ν 0 := hων 0 (by omega)
      have hlabel : gammaCodeLabel N ω 0 = gammaCodeLabel N ν 0 := by
        simp [gammaCodeLabel, h0]
      rw [gammaBaireCode_selfSimilarity hN, gammaBaireCode_selfSimilarity hN, hlabel]
      have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
        intro k
        simpa [gammaCodeShift] using hN (k + 1)
      have hdiam := dist_gammaExteriorInverseBranch_le_half_contraction
        (gammaCodeLabel_late (ω := ν) hN 0)
        (gammaBaireCode_mem (ω := gammaCodeShift ω) hNshift)
        (gammaBaireCode_mem (ω := gammaCodeShift ν) hNshift)
      simpa [gammaPrefixWeight, gammaCodeLabel, h0] using hdiam
  | succ d ih =>
      have h0 : ω 0 = ν 0 := hων 0 (by omega)
      have hlabel : gammaCodeLabel N ω 0 = gammaCodeLabel N ν 0 := by
        simp [gammaCodeLabel, h0]
      have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
        intro k
        simpa [gammaCodeShift] using hN (k + 1)
      have htail : ∀ k < d + 1, gammaCodeShift ω k = gammaCodeShift ν k := by
        intro k hk
        simpa [gammaCodeShift] using hων (k + 1) (by omega)
      have hih := ih hNshift htail
      rw [gammaBaireCode_selfSimilarity hN, gammaBaireCode_selfSimilarity hN, hlabel]
      have hlip := lipschitzOn_gammaExteriorInverseBranch
        (n := gammaCodeLabel N ν 0) (gammaCodeLabel_late (ω := ν) hN 0)
      have hdist := hlip.dist_le_mul
        (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω))
        (gammaBaireCode_mem (ω := gammaCodeShift ω) hNshift)
        (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ν))
        (gammaBaireCode_mem (ω := gammaCodeShift ν) hNshift)
      calc
        dist (gammaExteriorInverseBranch (gammaCodeLabel N ν 0)
            (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω)))
            (gammaExteriorInverseBranch (gammaCodeLabel N ν 0)
              (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ν)))
            ≤ (gammaExteriorContraction (gammaCodeLabel N ν 0) : ℝ) *
                dist (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ω))
                  (gammaBaireCode (gammaCodeShift N) (gammaCodeShift ν)) := by
              simpa using hdist
        _ ≤ (gammaExteriorContraction (gammaCodeLabel N ν 0) : ℝ) *
              ((gammaPrefixWeight (gammaCodeShift N) (gammaCodeShift ω) (d + 1) : ℝ) / 2) := by
              gcongr
        _ = (gammaPrefixWeight N ω (d + 2) : ℝ) / 2 := by
              simp only [gammaPrefixWeight]
              rw [hlabel]
              norm_cast
              ring

/-- The cylinder of all horizon points with a prescribed finite Baire prefix. -/
def gammaHorizonCylinder (d : ℕ) (w : Fin d → ℕ) : Set ℂ :=
  {z | ∃ ω : ℕ → ℕ,
    (∀ k (hk : k < d), ω k = w ⟨k, hk⟩) ∧ z = gammaBaireCode gammaThinSchedule ω}

theorem gammaConstrainedHorizon_cylinder_cover (d : ℕ) :
    gammaConstrainedHorizon ⊆ ⋃ w : Fin d → ℕ, gammaHorizonCylinder d w := by
  rintro z ⟨ω, rfl⟩
  rw [Set.mem_iUnion]
  refine ⟨(fun i : Fin d => ω i), ?_⟩
  exact ⟨ω, by simp, rfl⟩

theorem gammaWordWeight_eq_of_matches
    {N ω : ℕ → ℕ} {d : ℕ} {w : Fin d → ℕ}
    (hω : ∀ k (hk : k < d), ω k = w ⟨k, hk⟩) :
    gammaPrefixWeight N ω d = gammaWordWeight d N w := by
  rw [gammaPrefixWeight_eq_wordWeight]
  congr 1
  funext i
  exact hω i i.isLt

/-- Every nonempty symbolic cylinder has its full word-weight as an ambient diameter bound. -/
theorem ediam_gammaHorizonCylinder_le_wordWeight
    (d : ℕ) (w : Fin (d + 1) → ℕ) :
    Metric.ediam (gammaHorizonCylinder (d + 1) w) ≤
      (gammaWordWeight (d + 1) gammaThinSchedule w : ℝ≥0∞) := by
  apply Metric.ediam_le
  rintro _ ⟨ω, hω, rfl⟩ _ ⟨ν, hν, rfl⟩
  have hων : ∀ k < d + 1, ω k = ν k := by
    intro k hk
    exact (hω k hk).trans (hν k hk).symm
  have hdist := dist_gammaBaireCode_le_prefixWeight gammaThinSchedule_late d hων
  have hweight := gammaWordWeight_eq_of_matches (N := gammaThinSchedule) hω
  rw [hweight] at hdist
  have hdist' : dist (gammaBaireCode gammaThinSchedule ω)
      (gammaBaireCode gammaThinSchedule ν) ≤
      (gammaWordWeight (d + 1) gammaThinSchedule w : ℝ) := by
    exact hdist.trans (div_le_self (NNReal.coe_nonneg _) (by norm_num : (1 : ℝ) ≤ 2))
  exact_mod_cast hdist'

theorem gammaWordWeight_le_half_pow
    {N : ℕ → ℕ} (hN : ∀ k, gammaCommonInverseCollar.threshold ≤ N k) :
    ∀ d (w : Fin d → ℕ), gammaWordWeight d N w ≤ (1 / 2 : ℝ≥0) ^ d := by
  intro d
  induction d generalizing N with
  | zero => intro w; simp [gammaWordWeight]
  | succ d ih =>
      intro w
      have hNshift : ∀ k, gammaCommonInverseCollar.threshold ≤ gammaCodeShift N k := by
        intro k
        simpa [gammaCodeShift] using hN (k + 1)
      have hlabel : gammaCommonInverseCollar.threshold ≤ N 0 + w 0 :=
        (hN 0).trans (Nat.le_add_right _ _)
      rw [gammaWordWeight, pow_succ]
      simpa [mul_comm] using
        mul_le_mul (gammaExteriorContraction_le_half hlabel)
          (ih hNshift (Fin.tail w)) (by positivity) (by positivity)

/-! ## Factorial `s`-mass of finite words -/

theorem gammaExteriorContraction_pos (n : ℕ) :
    0 < (gammaExteriorContraction n : ℝ) := by
  rw [gammaExteriorContraction_eq]
  positivity

/-- For every positive real exponent, the actual factorial contraction weights are summable. -/
theorem summable_gammaExteriorContraction_rpow
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => (gammaExteriorContraction n) ^ s) := by
  rw [← NNReal.summable_coe]
  let f : ℕ → ℝ := fun n => (gammaExteriorContraction n : ℝ) ^ s
  have hfpos : ∀ n, 0 < f n := fun n =>
    Real.rpow_pos_of_pos (gammaExteriorContraction_pos n) s
  have hcsucc : ∀ n,
      (gammaExteriorContraction (n + 1) : ℝ) =
        (gammaExteriorContraction n : ℝ) / (n + 1 : ℝ) := by
    intro n
    rw [gammaExteriorContraction_eq, gammaExteriorContraction_eq, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  have hratio : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hpow := (tendsto_rpow_neg_atTop hs).comp hbase
    apply hpow.congr'
    exact Eventually.of_forall fun n => by
      simp only [Function.comp_apply, Real.norm_eq_abs, f]
      rw [abs_of_pos (hfpos (n + 1)), abs_of_pos (hfpos n), hcsucc,
        Real.div_rpow (gammaExteriorContraction_pos n).le (by positivity) s]
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hfn : (gammaExteriorContraction n : ℝ) ^ s ≠ 0 := (hfpos n).ne'
      rw [Real.rpow_neg hn.le]
      field_simp
  have hsum : Summable f := summable_of_ratio_test_tendsto_lt_one
    (f := f) (l := 0) (by norm_num)
    (Eventually.of_forall fun n => (hfpos n).ne') hratio
  simpa [f, NNReal.coe_rpow] using hsum

/-- The `s`-mass of all possible labels at one clock depth. -/
def gammaStageMass (s : ℝ) (M : ℕ) : ℝ≥0∞ :=
  ∑' a : ℕ, (gammaExteriorContraction (M + a) : ℝ≥0∞) ^ s

theorem gammaStageMass_ne_top {s : ℝ} (hs : 0 < s) (M : ℕ) :
    gammaStageMass s M ≠ ∞ := by
  rw [gammaStageMass]
  simp_rw [← ENNReal.coe_rpow_of_nonneg _ hs.le]
  rw [ENNReal.tsum_coe_ne_top_iff_summable]
  have hsum := summable_gammaExteriorContraction_rpow hs
  simpa [Nat.add_comm] using (NNReal.summable_nat_add_iff M).2 hsum

/-- Along the linearly receding schedule, one-stage masses tend to zero. -/
theorem tendsto_gammaStageMass_gammaThinSchedule
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun k => gammaStageMass s (gammaThinSchedule k)) atTop (𝓝 0) := by
  let f : ℕ → ℝ≥0∞ := fun n => (gammaExteriorContraction n : ℝ≥0∞) ^ s
  have hsum : (∑' n, f n) ≠ ∞ := by
    simpa [gammaStageMass, f] using gammaStageMass_ne_top hs 0
  have htail := (ENNReal.tendsto_sum_nat_add f hsum).comp
    (tendsto_add_atTop_nat gammaCommonInverseCollar.threshold)
  apply htail.congr'
  exact Eventually.of_forall fun k => by
    simp only [Function.comp_apply, gammaStageMass, f]
    apply tsum_congr
    intro a
    apply congrArg (fun m : ℕ => (gammaExteriorContraction m : ℝ≥0∞) ^ s)
    simp [gammaThinSchedule]
    omega

/-- Recursive product of the stage masses for the first `d` clock depths. -/
def gammaScheduleMass (s : ℝ) : (ℕ → ℕ) → ℕ → ℝ≥0∞
  | _N, 0 => 1
  | N, d + 1 => gammaStageMass s (N 0) * gammaScheduleMass s (gammaCodeShift N) d

theorem gammaScheduleMass_eq_prod (s : ℝ) (N : ℕ → ℕ) (d : ℕ) :
    gammaScheduleMass s N d = ∏ k ∈ Finset.range d, gammaStageMass s (N k) := by
  induction d generalizing N with
  | zero => simp [gammaScheduleMass]
  | succ d ih =>
      rw [gammaScheduleMass, ih, Finset.prod_range_succ']
      simp only [gammaCodeShift_apply]
      ac_rfl

/-- The total `s`-mass of all finite words factors into the product of one-stage tail masses. -/
theorem tsum_gammaWordWeight_rpow
    {s : ℝ} (hs : 0 ≤ s) (N : ℕ → ℕ) (d : ℕ) :
    (∑' w : Fin d → ℕ, ((gammaWordWeight d N w : ℝ≥0∞) ^ s)) =
      gammaScheduleMass s N d := by
  induction d generalizing N with
  | zero => simp [gammaWordWeight, gammaScheduleMass]
  | succ d ih =>
      let e := Fin.consEquiv (fun _ : Fin (d + 1) => ℕ)
      calc
        (∑' w : Fin (d + 1) → ℕ, ((gammaWordWeight (d + 1) N w : ℝ≥0∞) ^ s))
            = ∑' p : ℕ × (Fin d → ℕ),
                ((gammaWordWeight (d + 1) N (e p) : ℝ≥0∞) ^ s) :=
              (e.tsum_eq _).symm
        _ = ∑' a : ℕ, ∑' w : Fin d → ℕ,
              ((((gammaExteriorContraction (N 0 + a) : ℝ≥0∞) ^ s) *
                ((gammaWordWeight d (gammaCodeShift N) w : ℝ≥0∞) ^ s))) := by
              rw [ENNReal.tsum_prod']
              congr 1
              funext a
              congr 1
              funext w
              change ((gammaExteriorContraction (N 0 + a) : ℝ≥0∞) *
                  (gammaWordWeight d (gammaCodeShift N) w : ℝ≥0∞)) ^ s = _
              rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
        _ = (∑' a : ℕ, ((gammaExteriorContraction (N 0 + a) : ℝ≥0∞) ^ s)) *
              (∑' w : Fin d → ℕ,
                ((gammaWordWeight d (gammaCodeShift N) w : ℝ≥0∞) ^ s)) := by
              simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
        _ = gammaScheduleMass s N (d + 1) := by
              rw [ih]
              simp [gammaScheduleMass, gammaStageMass]

theorem tendsto_gammaScheduleMass_gammaThinSchedule
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun d => gammaScheduleMass s gammaThinSchedule d) atTop (𝓝 0) := by
  rw [show (fun d => gammaScheduleMass s gammaThinSchedule d) =
      (fun d => ∏ k ∈ Finset.range d, gammaStageMass s (gammaThinSchedule k)) by
        funext d
        exact gammaScheduleMass_eq_prod s gammaThinSchedule d]
  have hstage := tendsto_gammaStageMass_gammaThinSchedule hs
  have hev : ∀ᶠ k in atTop, gammaStageMass s (gammaThinSchedule k) ≤ 1 / 2 :=
    (hstage.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1 / 2)))
  rw [eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  rw [← tendsto_add_atTop_iff_nat K]
  let C : ℝ≥0∞ := ∏ k ∈ Finset.range K, gammaStageMass s (gammaThinSchedule k)
  have hC : C ≠ ∞ := by
    apply ENNReal.prod_ne_top
    intro k hk
    exact gammaStageMass_ne_top hs _
  have hbound : Tendsto (fun d => C * (1 / 2 : ℝ≥0∞) ^ d) atTop (𝓝 0) := by
    have hp := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
    simpa using ENNReal.Tendsto.const_mul hp (Or.inr hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
  · intro d
    exact bot_le
  · intro d
    change (∏ k ∈ Finset.range (d + K), gammaStageMass s (gammaThinSchedule k)) ≤ _
    rw [show d + K = K + d by omega, Finset.prod_range_add]
    apply mul_le_mul_left'
    calc
      (∏ k ∈ Finset.range d, gammaStageMass s (gammaThinSchedule (K + k)))
          ≤ ∏ _k ∈ Finset.range d, (1 / 2 : ℝ≥0∞) := by
            apply Finset.prod_le_prod
            · intro k hk
              exact bot_le
            intro k hk
            exact hK (K + k) (Nat.le_add_right K k)
      _ = (1 / 2 : ℝ≥0∞) ^ d := by simp

/-! ## Vanishing Hausdorff measure and zero dimension -/

theorem hausdorffMeasure_gammaConstrainedHorizon_eq_zero
    {s : ℝ} (hs : 0 < s) :
    MeasureTheory.Measure.hausdorffMeasure s gammaConstrainedHorizon = 0 := by
  let r : ℕ → ℝ≥0∞ := fun d => ((1 / 2 : ℝ≥0) ^ (d + 1) : ℝ≥0∞)
  let t : ∀ d : ℕ, (Fin (d + 1) → ℕ) → Set ℂ :=
    fun d w => gammaHorizonCylinder (d + 1) w
  have hr : Tendsto r atTop (𝓝 0) := by
    have hp := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < 1)
    exact hp.comp (tendsto_add_atTop_nat 1)
  have ht : ∀ᶠ d in atTop, ∀ w, Metric.ediam (t d w) ≤ r d := by
    exact Eventually.of_forall fun d w => by
      apply (ediam_gammaHorizonCylinder_le_wordWeight d w).trans
      simp only [r]
      exact_mod_cast gammaWordWeight_le_half_pow gammaThinSchedule_late (d + 1) w
  have hcover : ∀ᶠ d in atTop, gammaConstrainedHorizon ⊆ ⋃ w, t d w := by
    exact Eventually.of_forall fun d => gammaConstrainedHorizon_cylinder_cover (d + 1)
  have hcostBound : ∀ d,
      (∑' w : Fin (d + 1) → ℕ, Metric.ediam (t d w) ^ s) ≤
        gammaScheduleMass s gammaThinSchedule (d + 1) := by
    intro d
    rw [← tsum_gammaWordWeight_rpow hs.le gammaThinSchedule (d + 1)]
    apply ENNReal.tsum_le_tsum
    intro w
    apply ENNReal.rpow_le_rpow
    · exact ediam_gammaHorizonCylinder_le_wordWeight d w
    · exact hs.le
  have hmass : Tendsto (fun d => gammaScheduleMass s gammaThinSchedule (d + 1))
      atTop (𝓝 0) :=
    (tendsto_gammaScheduleMass_gammaThinSchedule hs).comp (tendsto_add_atTop_nat 1)
  have hcost : Tendsto
      (fun d => ∑' w : Fin (d + 1) → ℕ, Metric.ediam (t d w) ^ s)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
    · intro d
      exact bot_le
    · exact hcostBound
  have hle := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum
    s gammaConstrainedHorizon r hr t ht hcover
  rw [hcost.liminf_eq] at hle
  exact bot_unique hle

/-- **Dimension-zero constrained horizon.**  The actual Euler-Gamma inverse-history horizon is
homeomorphic to Baire space while having zero Hausdorff dimension in the ambient complex plane. -/
theorem dimH_gammaConstrainedHorizon :
    dimH gammaConstrainedHorizon = 0 := by
  apply le_antisymm
  · apply dimH_le
    intro s hsTop
    have hs0 : s = 0 := by
      by_contra hsne
      have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hsne)
      have hzero := hausdorffMeasure_gammaConstrainedHorizon_eq_zero hspos
      rw [hzero] at hsTop
      exact ENNReal.zero_ne_top hsTop
    simp [hs0]
  · exact bot_le

end

end GaloisForLFunctions
