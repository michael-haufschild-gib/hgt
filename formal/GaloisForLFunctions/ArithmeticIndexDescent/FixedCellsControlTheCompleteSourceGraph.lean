import GaloisForLFunctions.ArithmeticIndexDescent.AShortNewCellPaysItsOwnInteraction
import GaloisForLFunctions.ArithmeticIndexDescent.TheGraphNormIsControlledBySectionEnergy

/-!
# Fixed arithmetic cells control the complete source graph

A summable loss of old square mass lets each new cell pay an arbitrary
continuous spatial weight. All widths are chosen once and all independently
profiled finite prefixes retain the weighted floor. Applying this construction
to the exact inverse Doob mass yields a graph bound with any factor above one,
uniformly across the unbounded integer-log carrier. No lower width bound or
exhaustion of the full test space is asserted.
-/

open MeasureTheory Set
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- Square mass against a specified spatial weight. -/
def weightedSectionMass (ω : ℝ → ℝ) (f : realTests) : ℝ :=
  ∫ u, f.1 u ^ 2 * ω u

private theorem integrable_section_square (f : realTests) : Integrable (fun u => f.1 u ^ 2) := by
  have hcs : HasCompactSupport (fun u => f.1 u ^ 2) :=
    HasCompactSupport.comp_left (f := f.1) (g := fun t : ℝ => t ^ 2) f.2.2 (by simp)
  have hc : Continuous (fun u => f.1 u ^ 2) := f.2.1.continuous.pow 2
  exact hc.integrable_of_hasCompactSupport hcs

private theorem integrable_weighted_section_square {ω : ℝ → ℝ} (hω : Continuous ω)
    (f : realTests) : Integrable (fun u => f.1 u ^ 2 * ω u) := by
  have hcs : HasCompactSupport (fun u => f.1 u ^ 2) :=
    HasCompactSupport.comp_left (f := f.1) (g := fun t : ℝ => t ^ 2) f.2.2 (by simp)
  have hwcs : HasCompactSupport (fun u => f.1 u ^ 2 * ω u) := hcs.mul_right
  have hc : Continuous (fun u => f.1 u ^ 2) := f.2.1.continuous.pow 2
  have hwc : Continuous (fun u => f.1 u ^ 2 * ω u) := hc.mul hω
  exact hwc.integrable_of_hasCompactSupport hwcs

theorem weightedSectionMass_nonneg {ω : ℝ → ℝ} (hω : ∀ u, 0 ≤ ω u) (f : realTests) :
    0 ≤ weightedSectionMass ω f := by
  change 0 ≤ ∫ u, f.1 u ^ 2 * ω u
  apply integral_nonneg
  intro u
  exact mul_nonneg (sq_nonneg _) (hω u)

theorem sectionMass_le_weightedSectionMass {ω : ℝ → ℝ} (hω : Continuous ω)
    (hω1 : ∀ u, 1 ≤ ω u) (f : realTests) :
    sectionMass f.1 ≤ weightedSectionMass ω f := by
  apply integral_mono (integrable_section_square f) (integrable_weighted_section_square hω f)
  intro u
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hω1 u) (sq_nonneg (f.1 u))

/-- A fixed cell pays its local weighted mass through an ordinary mass charge. -/
theorem weightedSectionMass_le_cellCharge {ω : ℝ → ℝ} (hω : Continuous ω)
    (f : realTests) {C : ℝ} (hC : ∀ u, f.1 u ≠ 0 → ω u ≤ C) :
    weightedSectionMass ω f ≤ C * sectionMass f.1 := by
  calc
    _ ≤ ∫ u, f.1 u ^ 2 * C := by
      apply integral_mono (integrable_weighted_section_square hω f)
        ((integrable_section_square f).mul_const C)
      intro u
      by_cases hf : f.1 u = 0
      · simp only [hf, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hC u hf) (sq_nonneg _)
    _ = _ := by rw [integral_mul_const]; exact mul_comm _ _

/-- Spatial weighting preserves exact mass addition on separated profiles. -/
theorem weightedSectionMass_add_of_disjoint {ω : ℝ → ℝ} (hω : Continuous ω)
    (p g : realTests) (hdisj : ∀ u, p.1 u * g.1 u = 0) :
    weightedSectionMass ω (p + g) = weightedSectionMass ω p + weightedSectionMass ω g := by
  change (∫ u, (p.1 u + g.1 u) ^ 2 * ω u) = _
  calc
    _ = ∫ u, p.1 u ^ 2 * ω u + g.1 u ^ 2 * ω u := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hsq : (p.1 u + g.1 u) ^ 2 = p.1 u ^ 2 + g.1 u ^ 2 := by
        nlinarith only [hdisj u]
      rw [hsq, add_mul]
    _ = _ := integral_add (integrable_weighted_section_square hω p)
      (integrable_weighted_section_square hω g)

namespace OrderedCellGeometry

/-- A bounded envelope that stops before the next ordered centre. -/
def envelopeWidth (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  min 1 ((b (n + 1) - b n) / 2)

/-- The compact union of the first fixed cell envelopes. -/
def prefixEnvelope (b : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ Finset.range n,
    Icc (b i - envelopeWidth b i / 2) (b i + envelopeWidth b i / 2)

theorem envelopeWidth_pos {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    0 < envelopeWidth b n :=
  lt_min zero_lt_one (div_pos (sub_pos.mpr (hb (Nat.lt_succ_self n))) (by norm_num))

/-- Every new centre lies strictly outside the old envelopes. -/
theorem centre_not_mem_prefix {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    b n ∉ prefixEnvelope b n := by
  intro hmem
  simp only [prefixEnvelope, Set.mem_iUnion] at hmem
  obtain ⟨i, hi, hui⟩ := hmem
  have hin : i < n := Finset.mem_range.mp hi
  have hnext : b (i + 1) ≤ b n := hb.monotone (by omega)
  have hinc : b i < b (i + 1) := hb (Nat.lt_succ_self i)
  have he : envelopeWidth b i ≤ (b (i + 1) - b i) / 2 := min_le_right _ _
  linarith only [hui.2, hnext, hinc, he]

/-- Compactness gives a positive separation from all old profiles at once. -/
theorem exists_prefix_gap {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ prefixEnvelope b n, d < |u - b n| := by
  have hc : IsCompact (prefixEnvelope b n) :=
    (Finset.range n).isCompact_biUnion fun _ _ => isCompact_Icc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl
    (b n) (centre_not_mem_prefix hb n)
  refine ⟨r / 2, div_pos hr (by norm_num), ?_⟩
  intro u hu
  have hfar : r ≤ |u - b n| := by
    by_contra hnot
    have huB : u ∈ Metric.ball (b n) r := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_not_ge hnot
    exact hball huB hu
  linarith only [hr, hfar]

/-- Each finite envelope has a common source window independent of the profiles. -/
theorem exists_prefix_window {b : ℕ → ℝ} (hb : StrictMono b) (n : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u ∈ prefixEnvelope b n, |u| < R := by
  let S := ∑ i ∈ Finset.range n, (|b i| + envelopeWidth b i / 2)
  have hterm (i : ℕ) : 0 ≤ |b i| + envelopeWidth b i / 2 :=
    add_nonneg (abs_nonneg _) (div_nonneg (envelopeWidth_pos hb i).le (by norm_num))
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hterm i
  refine ⟨S + 1, by linarith only [hS], ?_⟩
  intro u hu
  simp only [prefixEnvelope, Set.mem_iUnion] at hu
  obtain ⟨i, hi, hui⟩ := hu
  have hdist : |u - b i| ≤ envelopeWidth b i / 2 :=
    abs_le.mpr ⟨by linarith only [hui.1], by linarith only [hui.2]⟩
  have htri := abs_add_le (u - b i) (b i)
  rw [sub_add_cancel] at htri
  have hiS : |b i| + envelopeWidth b i / 2 ≤ S :=
    Finset.single_le_sum (fun j _ => hterm j) hi
  linarith only [hdist, htri, hiS]

end OrderedCellGeometry

open OrderedCellGeometry

/-- A single width choice pays a prescribed continuous spatial weight on every finite prefix. -/
theorem exists_fixedCellWidths_weighted_coercive {ω : ℝ → ℝ}
    {centres : ℕ → ℝ} (hb : StrictMono centres) (hω : Continuous ω)
    (hω1 : ∀ u, 1 ≤ ω u) :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ (∀ n, w n ≤ 1) ∧
      ∀ N : ℕ, ∀ G : ℕ → realTests,
        (∀ i ∈ Finset.range N, ∀ u,
          w i / 2 < |u - centres i| → (G i).1 u = 0) →
        weightedSectionMass ω (∑ i ∈ Finset.range N, G i) ≤
          realWeilForm (∑ i ∈ Finset.range N, G i) (∑ i ∈ Finset.range N, G i) := by
  let a : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)
  have hε (n : ℕ) : 0 < ε n := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith only)
  have ha0 (n : ℕ) : 0 ≤ a n := by dsimp [a]; positivity
  have haε (n : ℕ) : a n - ε n = a (n + 1) := by
    dsimp [a, ε]
    push_cast
    ring
  have hcellbound (n : ℕ) : ∃ c : ℝ, 1 ≤ c ∧
      ∀ u ∈ Icc (centres n - 1) (centres n + 1), ω u ≤ c := by
    obtain ⟨x, _, hx⟩ := (isCompact_Icc (a := centres n - 1) (b := centres n + 1)).exists_isMaxOn
      ⟨centres n, by constructor <;> linarith only⟩ hω.continuousOn
    exact ⟨ω x, hω1 x, fun u hu => hx hu⟩
  choose c hc hωc using hcellbound
  choose R hR hwindow using exists_prefix_window hb
  choose d hd hgap using exists_prefix_gap hb
  choose η hη hext using fun n =>
    exists_shortCell_diagonal_extension (hR n) (hd n) (hε n) (centres n) (a (n + 1) * c n)
  let w : ℕ → ℝ := fun n => min (envelopeWidth centres n) (min (d n) (η n / 2))
  have hw (n : ℕ) : 0 < w n :=
    lt_min (envelopeWidth_pos hb n) (lt_min (hd n) (div_pos (hη n) (by norm_num)))
  have hwe (n : ℕ) : w n ≤ envelopeWidth centres n := min_le_left _ _
  have hw1 (n : ℕ) : w n ≤ 1 := (hwe n).trans (min_le_left _ _)
  have hwd (n : ℕ) : w n ≤ d n := (min_le_right _ _).trans (min_le_left _ _)
  have hwη (n : ℕ) : w n < η n := by
    have hh : w n ≤ η n / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hh, hη n]
  refine ⟨w, hw, hw1, ?_⟩
  -- The decreasing reserve pays old losses; the new diagonal pays its local weight.
  have hfloor (N : ℕ) : ∀ G : ℕ → realTests,
      (∀ i ∈ Finset.range N, ∀ u, w i / 2 < |u - centres i| → (G i).1 u = 0) →
      a N * weightedSectionMass ω (∑ i ∈ Finset.range N, G i) ≤
        realWeilForm (∑ i ∈ Finset.range N, G i) (∑ i ∈ Finset.range N, G i) := by
    induction N with
    | zero =>
      intro G _
      simp only [Finset.range_zero, Finset.sum_empty, map_zero]
      simp [weightedSectionMass]
    | succ n ih =>
      intro G hG
      let p : realTests := ∑ i ∈ Finset.range n, G i
      have hold := ih G (fun i hi => hG i (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
      change a n * weightedSectionMass ω p ≤ realWeilForm p p at hold
      have hgs := hG n (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have hp0 : ∀ u, u ∉ prefixEnvelope centres n → p.1 u = 0 := by
        intro u hu
        change (∑ i ∈ Finset.range n, G i).1 u = 0
        rw [Submodule.coe_sum, Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro i hi
        apply hG i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))) u
        by_contra hnot
        have hdist : |u - centres i| ≤ w i / 2 := le_of_not_gt hnot
        have hcell : u ∈ Icc (centres i - envelopeWidth centres i / 2)
            (centres i + envelopeWidth centres i / 2) := by
          obtain ⟨hl, hr⟩ := abs_le.mp hdist
          constructor <;> linarith only [hl, hr, hwe i]
        apply hu
        simp only [prefixEnvelope, Set.mem_iUnion]
        exact ⟨i, hi, hcell⟩
      have hpR : ∀ u, R n < |u| → p.1 u = 0 := by
        intro u hu
        apply hp0
        intro hm
        exact (hwindow n u hm).not_gt hu
      have hpd : ∀ u, p.1 u ≠ 0 → d n < |u - centres n| := by
        intro u hu
        apply hgap n u
        by_contra hm
        exact hu (hp0 u hm)
      have hdisj : ∀ u, p.1 u * (G n).1 u = 0 := by
        intro u
        by_cases hpz : p.1 u = 0
        · rw [hpz, zero_mul]
        have hdist := hpd u hpz
        have hz : (G n).1 u = 0 := hgs u (by linarith only [hdist, hwd n, hd n])
        rw [hz, mul_zero]
      have hlocal : weightedSectionMass ω (G n) ≤ c n * sectionMass (G n).1 := by
        apply weightedSectionMass_le_cellCharge hω
        intro u hgu
        have hnear : |u - centres n| ≤ w n / 2 :=
          le_of_not_gt (fun h => hgu (hgs u h))
        obtain ⟨hl, hr⟩ := abs_le.mp hnear
        apply hωc n u
        constructor <;> linarith only [hl, hr, hw1 n]
      have hnew := hext n (w n) (hw n) (hwη n) p (G n) hpR hpd hgs
      have holdpay := mul_le_mul_of_nonneg_left
        (sectionMass_le_weightedSectionMass hω hω1 p) (hε n).le
      have hnewpay := mul_le_mul_of_nonneg_left hlocal (ha0 (n + 1))
      have hcost : a n * weightedSectionMass ω p - ε n * weightedSectionMass ω p =
          a (n + 1) * weightedSectionMass ω p := by rw [← sub_mul, haε n]
      rw [Finset.sum_range_succ]
      change a (n + 1) * weightedSectionMass ω (p + G n) ≤ realWeilForm (p + G n) (p + G n)
      rw [weightedSectionMass_add_of_disjoint hω p (G n) hdisj]
      nlinarith only [hold, hnew, holdpay, hnewpay, hcost]
  intro N G hG
  have ha : 1 ≤ a N := by
    have hh : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    dsimp [a]
    linarith only [hh]
  have hmass := mul_le_mul_of_nonneg_right ha
    (weightedSectionMass_nonneg (fun u => (by norm_num : (0 : ℝ) ≤ 1).trans (hω1 u))
      (∑ i ∈ Finset.range N, G i))
  rw [one_mul] at hmass
  exact hmass.trans (hfloor N G hG)

/-- The exact source mass density in the inverse Doob coordinates. -/
def sourceGraphMassWeight (u : ℝ) : ℝ :=
  Real.cosh (u / 2) / riemannKernelReal u

theorem sourceGraphMassWeight_pos (u : ℝ) : 0 < sourceGraphMassWeight u :=
  div_pos (Real.cosh_pos _) (riemannKernelReal_pos _)

theorem continuous_sourceGraphMassWeight : Continuous sourceGraphMassWeight :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).div
    continuous_riemannKernelReal (fun u => (riemannKernelReal_pos u).ne')

/-- Compact C² tests retain their exact mass in the complete source graph. -/
theorem norm_realTestGraphLift_source_sq_eq_weightedMass (f : realTests) :
    ‖(realTestGraphLift f).val.fst‖ ^ 2 = weightedSectionMass sourceGraphMassWeight f := by
  rw [_root_.RHTower.CHMDPolar.norm_sq_eq_integral]
  have he : (∫ u, ((realTestGraphLift f).val.fst u) ^ 2 ∂massMeasure) =
      ∫ u, phiDoobInv f.1 u ^ 2 ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [testLift_source f.1 f.2.1 f.2.2] with u hu
    change ((testLift f.1 f.2.1 f.2.2).val.fst u) ^ 2 = _
    rw [hu]
  rw [he, _root_.RHTower.CHMDPolar.integral_mass]
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp [massDensity, phiDoobInv, weightedSectionMass, sourceGraphMassWeight]
  field_simp [(riemannKernelReal_pos u).ne']

/-- The global polar rows charge only the source mass beyond the full Weil diagonal. -/
def sourceGraphMassPenalty : ℝ := 2 * (1 + ‖tanhL‖ ^ 2)

theorem sourceGraphMassPenalty_pos : 0 < sourceGraphMassPenalty := by
  unfold sourceGraphMassPenalty
  positivity

theorem norm_realTestGraphLift_sq_le_weil_add_weightedMass (f : realTests) :
    ‖realTestGraphLift f‖ ^ 2 ≤ realWeilForm f f +
      sourceGraphMassPenalty * weightedSectionMass sourceGraphMassWeight f := by
  let p := realTestGraphLift f
  have hn := sourceEnergy_add_two_mass p
  have hw := weilForm_realTestGraphLift f
  change weilForm p = realWeilForm f f at hw
  have ht : ⟪p.val.fst, tanhL⟫_ℝ ^ 2 ≤ ‖p.val.fst‖ ^ 2 * ‖tanhL‖ ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  rw [← norm_realTestGraphLift_source_sq_eq_weightedMass]
  unfold weilForm at hw
  change ‖p‖ ^ 2 ≤ realWeilForm f f +
    2 * (1 + ‖tanhL‖ ^ 2) * ‖p.val.fst‖ ^ 2
  nlinarith only [hn, hw, ht, sq_nonneg ⟪p.val.fst, oneL⟫_ℝ]

/-- This spatial weight pays the global graph mass with a chosen relative error. -/
def graphCoerciveMassWeight (ε u : ℝ) : ℝ :=
  1 + (sourceGraphMassPenalty / ε) * sourceGraphMassWeight u

private theorem continuous_graphCoerciveMassWeight (ε : ℝ) :
    Continuous (graphCoerciveMassWeight ε) :=
  continuous_const.add (continuous_sourceGraphMassWeight.const_mul _)

private theorem graphCoerciveMassWeight_one_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    1 ≤ graphCoerciveMassWeight ε u := by
  have hp := mul_nonneg (div_nonneg sourceGraphMassPenalty_pos.le hε.le)
    (sourceGraphMassWeight_pos u).le
  dsimp only [graphCoerciveMassWeight]
  linarith only [hp]

/-- The chosen source weight decomposes into ordinary mass and the exact graph-mass charge. -/
theorem weightedSectionMass_graphCoercive (ε : ℝ) (f : realTests) :
    weightedSectionMass (graphCoerciveMassWeight ε) f = sectionMass f.1 +
      (sourceGraphMassPenalty / ε) * weightedSectionMass sourceGraphMassWeight f := by
  calc
    _ = ∫ u, f.1 u ^ 2 + (f.1 u ^ 2 * sourceGraphMassWeight u) *
        (sourceGraphMassPenalty / ε) := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [graphCoerciveMassWeight]
      ring
    _ = _ := by
      rw [integral_add (integrable_section_square f)
        ((integrable_weighted_section_square continuous_sourceGraphMassWeight f).mul_const _),
        integral_mul_const]
      change sectionMass f.1 + weightedSectionMass sourceGraphMassWeight f * _ = _
      rw [mul_comm (weightedSectionMass sourceGraphMassWeight f)]

/-- One fixed sequence of cells controls the complete source graph over every finite prefix. -/
theorem exists_fixedCellWidths_graph_coercive {centres : ℕ → ℝ}
    (hb : StrictMono centres) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ (∀ n, w n ≤ 1) ∧
      ∀ N : ℕ, ∀ G : ℕ → realTests,
        (∀ i ∈ Finset.range N, ∀ u,
          w i / 2 < |u - centres i| → (G i).1 u = 0) →
        ‖realTestGraphLift (∑ i ∈ Finset.range N, G i)‖ ^ 2 ≤
          (1 + ε) * realWeilForm (∑ i ∈ Finset.range N, G i)
            (∑ i ∈ Finset.range N, G i) := by
  obtain ⟨w, hw, hw1, hbound⟩ := exists_fixedCellWidths_weighted_coercive hb
    (continuous_graphCoerciveMassWeight ε) (graphCoerciveMassWeight_one_le hε)
  refine ⟨w, hw, hw1, ?_⟩
  intro N G hG
  let f : realTests := ∑ i ∈ Finset.range N, G i
  have hpaid := hbound N G hG
  change weightedSectionMass (graphCoerciveMassWeight ε) f ≤ realWeilForm f f at hpaid
  rw [weightedSectionMass_graphCoercive] at hpaid
  have hm : 0 ≤ sectionMass f.1 := integral_nonneg (fun u => sq_nonneg (f.1 u))
  have hcharge : sourceGraphMassPenalty * weightedSectionMass sourceGraphMassWeight f ≤
      ε * realWeilForm f f := by
    have hp : (sourceGraphMassPenalty / ε) * weightedSectionMass sourceGraphMassWeight f ≤
        realWeilForm f f := by linarith only [hpaid, hm]
    have hh := mul_le_mul_of_nonneg_left hp hε.le
    have he : ε * ((sourceGraphMassPenalty / ε) *
        weightedSectionMass sourceGraphMassWeight f) =
        sourceGraphMassPenalty * weightedSectionMass sourceGraphMassWeight f := by
      field_simp [hε.ne']
    rw [he] at hh
    exact hh
  have hgraph := norm_realTestGraphLift_sq_le_weil_add_weightedMass f
  change ‖realTestGraphLift f‖ ^ 2 ≤ (1 + ε) * realWeilForm f f
  nlinarith only [hgraph, hcharge]

/-- Integer logarithms admit one fixed carrier with a uniform full graph bound. -/
theorem exists_fixedLogCellWidths_graph_coercive :
    ∃ w : ℕ → ℝ, (∀ n, 0 < w n) ∧ (∀ n, w n ≤ 1) ∧
      ∀ N : ℕ, ∀ G : ℕ → realTests,
        (∀ i ∈ Finset.range N, ∀ u,
          w i / 2 < |u - Real.log ((i : ℝ) + 1)| → (G i).1 u = 0) →
        ‖realTestGraphLift (∑ i ∈ Finset.range N, G i)‖ ^ 2 ≤
          2 * realWeilForm (∑ i ∈ Finset.range N, G i)
            (∑ i ∈ Finset.range N, G i) := by
  have hb : StrictMono (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
    intro i j hij
    apply Real.log_lt_log (by positivity)
    have hc : (i : ℝ) < j := by exact_mod_cast hij
    linarith only [hc]
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    exists_fixedCellWidths_graph_coercive hb (show (0 : ℝ) < 1 by norm_num)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedCellWidths_weighted_coercive
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_realTestGraphLift_source_sq_eq_weightedMass
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedCellWidths_graph_coercive
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedLogCellWidths_graph_coercive
