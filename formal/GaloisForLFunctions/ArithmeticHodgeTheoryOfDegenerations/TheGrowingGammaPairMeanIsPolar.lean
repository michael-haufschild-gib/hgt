import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingNearPairMeanIsPolar
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearAndFarGammaProfilesHaveOneFinitePart
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSeparatedGammaTailIsUniformAtGrowingOverlap

/-!
# The growing Gamma pair mean is polar

Actual near and separated archimedean entries retain their signed profile
means at growing overlap. Fixed scaled-gap annuli use periodic averaging;
the remaining tail is uniform in the horizon. The near and far logarithmic
source moments cancel, leaving `-aφ(log(4π) + γ)` at the polar conductor pair.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis BezoutValuationIncidence
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A matrix pairing restricted to a fixed scaled logarithmic gap interval. -/
def gapMatrixPair (A : ℕ → ℕ → ℝ) (α β w : ℝ) (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    if α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w then
      u n * v j * A n j / (Real.sqrt n * Real.sqrt j) else 0

private theorem abs_gapMatrixPair_sub_nearPairSum_le {A : ℕ → ℕ → ℝ} {K : ℝ → ℝ}
    {α β w ε B : ℝ} {N : ℕ} {u v : ℕ → ℝ}
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    (herr : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
      α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w →
      |A n j - K (|Real.log j - Real.log n| / w)| ≤ ε) :
    |gapMatrixPair A α β w N u v - nearPairSum K α β w N u v (fun _ => 1)| ≤
      B ^ 2 * ε * nearPairSum (fun _ => 1) α β w N (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  unfold gapMatrixPair nearPairSum
  simp only [one_mul, mul_one]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  by_cases hgap : α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w
  · rw [if_pos hgap, if_pos hgap, if_pos hgap]
    have heq : u n * v j * A n j / (Real.sqrt n * Real.sqrt j) -
        u n * v j * K (|Real.log j - Real.log n| / w) / (Real.sqrt n * Real.sqrt j) =
        u n * v j * (A n j - K (|Real.log j - Real.log n| / w)) /
          (Real.sqrt n * Real.sqrt j) := by ring
    rw [heq, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    have hprod := mul_le_mul (mul_le_mul (hu n) (hv j) (abs_nonneg _) hB)
      (herr n hn j hj hgap) (abs_nonneg _) (mul_nonneg hB hB)
    exact (div_le_div_of_nonneg_right hprod (by positivity)).trans_eq (by ring)
  · simp only [if_neg hgap, sub_self, abs_zero, mul_zero, le_refl]

private theorem tendsto_gapMatrixPair_sub_nearPairSum_div_overlap {A : ℕ → ℕ → ℕ → ℝ}
    {K : ℝ → ℝ} {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    {u v : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {c ε : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))
    (hε0 : Tendsto ε atTop (𝓝 0))
    (herr : ∀ᶠ N in atTop, ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
      α * (c N / N) < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * (c N / N) →
      |A N n j - K (|Real.log j - Real.log n| / (c N / N))| ≤ ε N) :
    Tendsto (fun N => (gapMatrixPair (A N) α β (c N / N) N u v -
      nearPairSum K α β (c N / N) N u v (fun _ => 1)) / c N) atTop (𝓝 0) := by
  have hmass := tendsto_nearPairSum_div_overlap (K := fun _ => (1 : ℝ))
    (A := 1) (L := 0) hα hαβ hβ (by intros; simp) (by intros; simp) le_rfl
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; simp) (by intros; simp) hc hcinf hcN
  have hlim := (hε0.mul hmass).const_mul (B ^ 2)
  simp only [zero_mul, mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [herr] with N hN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hc N)]
  exact (div_le_div_of_nonneg_right
    (abs_gapMatrixPair_sub_nearPairSum_le hu hv hN) (hc N).le).trans_eq (by ring)

/-- The near archimedean entry after its common logarithmic shell part is removed. -/
def nearArchimedeanRemainder (φ : ℝ → ℝ) (w : ℝ) (n j : ℕ) : ℝ :=
  atomArchPair (atomDilate φ w) n j / (∫ u, atomDilate φ w u ^ 2) -
    Real.log (1 / w) * shellAutocorr φ (|Real.log j - Real.log n| / w) / (∫ u, φ u ^ 2)

/-- The near remainder has the same even profile for both orientations of an arithmetic pair. -/
theorem abs_nearArchimedeanRemainder_sub_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {w : ℝ} (hw : 0 < w) (hw3 : w ≤ 1 / 3) {n j : ℕ}
    (hs : |Real.log j - Real.log n| ≤ 2 * w) :
    |nearArchimedeanRemainder φ w n j -
      nearKernel φ (|Real.log j - Real.log n| / w) / (∫ u, φ u ^ 2)| ≤ 3 * w := by
  have hb : |atomArchPair (atomDilate φ w) n j / (∫ u, atomDilate φ w u ^ 2) -
      (Real.log (1 / w) * shellAutocorr φ (|Real.log j - Real.log n| / w) +
        nearKernel φ (|Real.log j - Real.log n| / w)) / (∫ u, φ u ^ 2)| ≤ 3 * w := by
    by_cases hnonneg : 0 ≤ Real.log j - Real.log n
    · rw [abs_of_nonneg hnonneg] at hs ⊢
      exact abs_atomArchPair_sub_nearKernel_le hφ hsupp hM hw hw3 hnonneg hs
    · have hnonneg' : 0 ≤ Real.log n - Real.log j := by linarith
      have hgap : |Real.log j - Real.log n| = Real.log n - Real.log j := by
        rw [abs_of_neg (lt_of_not_ge hnonneg), neg_sub]
      rw [hgap] at hs ⊢
      rw [atomArchPair_comm (atomDilate φ w) n j]
      exact abs_atomArchPair_sub_nearKernel_le hφ hsupp hM hw hw3 hnonneg' hs
  convert hb using 1
  congr 1
  unfold nearArchimedeanRemainder
  ring

/-- Only the polar conductor pair survives in the growing near archimedean remainder. -/
theorem tendsto_nearArchimedeanRemainderPair_div_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => gapMatrixPair (nearArchimedeanRemainder φ (c N / N)) 0 2 (c N / N) N
      (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N) atTop
      (𝓝 (if m = 1 ∧ l = 1 then (2 / (∫ u, φ u ^ 2)) * ∫ s in (0 : ℝ)..2, nearKernel φ s else 0)) := by
  obtain ⟨A, L, hL0, hA, hL⟩ := exists_nearKernel_bounds hφ hsupp
  let K : ℝ → ℝ := fun s => nearKernel φ s / (∫ u, φ u ^ 2)
  have hAK : ∀ s ∈ Icc (0 : ℝ) 2, |K s| ≤ A / (∫ u, φ u ^ 2) := by
    intro s hs
    dsimp only [K]
    rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (hA s hs) hM.le
  have hLK : ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2,
      |K x - K y| ≤ (L / (∫ u, φ u ^ 2)) * |x - y| := by
    intro x hx y hy
    dsimp only [K]
    rw [← sub_div, abs_div, abs_of_pos hM]
    exact (div_le_div_of_nonneg_right (hL x hx y hy) hM.le).trans_eq (by ring)
  have hmain := tendsto_nearPairSum_ramanujan_div_overlap (K := K) (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2)
    hAK hLK (div_nonneg hL0 hM.le) hm hl hc hcinf hcN
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have hv : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  have hε : Tendsto (fun N : ℕ => 3 * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul 3
  have herr := tendsto_gapMatrixPair_sub_nearPairSum_div_overlap
    (A := fun N => nearArchimedeanRemainder φ (c N / N)) (K := K)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2)
    hu hv hc hcinf hcN (ε := fun N => 3 * (c N / N))
    hε (by
      filter_upwards [eventually_ge_atTop 1,
        hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with N hN hw
      intro n hn j hj hgap
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact abs_nearArchimedeanRemainder_sub_le hφ hsupp hM (div_pos (hc N) hN0) hw.le hgap.2)
  have h := herr.add hmain
  simp only [zero_add] at h
  have htarget : (if m = 1 ∧ l = 1 then 2 * ∫ s in (0 : ℝ)..2, K s else 0) =
      (if m = 1 ∧ l = 1 then (2 / (∫ u, φ u ^ 2)) * ∫ s in (0 : ℝ)..2, nearKernel φ s else 0) := by
    dsimp only [K]
    rw [intervalIntegral.integral_div]
    split_ifs <;> ring
  rw [htarget] at h
  exact h.congr fun N => by ring

/-- The reciprocal far profile is bounded and Lipschitz on scaled gaps at least two. -/
theorem exists_crossSingular_inverse_bounds {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s : ℝ, 2 ≤ s → |crossSingular φ (1 / s)| ≤ C) ∧
      ∀ x y : ℝ, 2 ≤ x → 2 ≤ y →
        |crossSingular φ (1 / x) - crossSingular φ (1 / y)| ≤ C * |x - y| := by
  let C : ℝ := 1 / (2 * ∫ u, φ u ^ 2) *
    ((1 / (1 - (1 / 2 : ℝ)) ^ 2 + 1) * ∫ t, |bumpAutocorr φ t|)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hm : ∀ s : ℝ, 2 ≤ s → 1 / s ∈ Icc (0 : ℝ) (1 / 2) := by
    intro s hs
    exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hs⟩
  refine ⟨C, hC, ?_, ?_⟩
  · intro s hs
    have h := abs_crossSingular_sub_le hφ hsupp hM (by norm_num : (1 / 2 : ℝ) < 1)
      (hm s hs) (show (0 : ℝ) ∈ Icc 0 (1 / 2) by constructor <;> norm_num)
    have hz : crossSingular φ 0 = 0 := by simp [crossSingular]
    rw [hz, sub_zero, sub_zero, abs_of_nonneg (hm s hs).1] at h
    exact h.trans (mul_le_of_le_one_right hC ((hm s hs).2.trans (by norm_num)))
  · intro x y hx hy
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hxy : (1 : ℝ) ≤ x * y := by
      have h := mul_le_mul hx hy (by norm_num : (0 : ℝ) ≤ 2) hx0.le
      nlinarith only [h]
    have hscalar : |1 / x - 1 / y| ≤ |x - y| := by
      have heq : 1 / x - 1 / y = (y - x) / (x * y) := by
        field_simp [hx0.ne', hy0.ne']
      rw [heq, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
      exact (div_le_iff₀ (mul_pos hx0 hy0)).mpr (le_mul_of_one_le_right (abs_nonneg _) hxy)
    exact (abs_crossSingular_sub_le hφ hsupp hM (by norm_num : (1 / 2 : ℝ) < 1)
      (hm x hx) (hm y hy)).trans (mul_le_mul_of_nonneg_left hscalar hC)

/-- On every fixed scaled-gap annulus, the actual far cross pairing has its singular-profile mean. -/
theorem tendsto_truncatedFarCrossPair_div_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {T : ℝ} (hT : 2 ≤ T) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcinf : Tendsto c atTop atTop) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N)))
      2 T (c N / N) N (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N) atTop
      (𝓝 (if m = 1 ∧ l = 1 then 2 * ∫ s in (2 : ℝ)..T, crossSingular φ (1 / s) else 0)) := by
  obtain ⟨C, hC, hA, hL⟩ := exists_crossSingular_inverse_bounds hφ hsupp hM
  let K : ℝ → ℝ := fun s => crossSingular φ (1 / s)
  have hmain := tendsto_nearPairSum_ramanujan_div_overlap (K := K)
    (by norm_num : (0 : ℝ) ≤ 2) hT (by linarith : 0 < T)
    (fun s hs => hA s hs.1) (fun x hx y hy => hL x y hx.1 hy.1) hC hm hl hc hcinf hcN
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have hv : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  let D : ℝ := 5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ u, φ u ^ 2)
  have hε : Tendsto (fun N : ℕ => D * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul D
  have herr := tendsto_gapMatrixPair_sub_nearPairSum_div_overlap
    (A := fun N => atomCrossErrorKernel (atomDilate φ (c N / N))) (K := K)
    (by norm_num : (0 : ℝ) ≤ 2) hT (by linarith : 0 < T)
    hu hv hc hcinf hcN (ε := fun N => D * (c N / N)) hε (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      intro n hn j hj hgap
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hw : 0 < c N / N := div_pos (hc N) hN0
      have hws : c N / N < |Real.log j - Real.log n| := by linarith only [hgap.1, hw]
      have hs0 : 0 < |Real.log j - Real.log n| := hw.trans hws
      have hnj : n ≠ j := by
        rintro rfl
        simp only [sub_self, abs_zero] at hs0
        exact (lt_irrefl 0) hs0
      have hb := abs_atomCrossErrorKernel_sub_crossSingular_le hφ hsupp hM hw
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hj).1 hnj hws
      have heq : 1 / (|Real.log j - Real.log n| / (c N / N)) =
          (c N / N) / |Real.log j - Real.log n| := by
        field_simp [hw.ne', hs0.ne']
      dsimp only [K]
      rw [heq]
      exact hb)
  have h := herr.add hmain
  simp only [zero_add] at h
  exact h.congr fun N => by ring

/-- The complete separated cross pairing, before logarithmic horizon normalization. -/
def farCrossPair (φ : ℝ → ℝ) (w : ℝ) (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    if 2 * w < |Real.log j - Real.log n| then
      u n * v j * atomCrossErrorKernel (atomDilate φ w) n j / (Real.sqrt n * Real.sqrt j) else 0

private theorem farCrossPair_sub_truncation (φ : ℝ → ℝ) {w T : ℝ} (hw : 0 ≤ w) (hT : 2 ≤ T)
    (N : ℕ) (u v : ℕ → ℝ) :
    farCrossPair φ w N u v - gapMatrixPair (atomCrossErrorKernel (atomDilate φ w)) 2 T w N u v =
      ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        if T * w < |Real.log j - Real.log n| then
          u n * v j * atomCrossErrorKernel (atomDilate φ w) n j / (Real.sqrt n * Real.sqrt j) else 0 := by
  unfold farCrossPair gapMatrixPair
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hcut : 2 * w ≤ T * w := mul_le_mul_of_nonneg_right hT hw
  by_cases hlow : 2 * w < |Real.log j - Real.log n|
  · by_cases hhigh : |Real.log j - Real.log n| ≤ T * w
    · simp only [hlow, hhigh, and_self, if_true, not_lt.mpr hhigh, if_false, sub_self]
    · simp only [hlow, hhigh, and_false, if_false, if_true, lt_of_not_ge hhigh, sub_zero]
  · have htail : ¬T * w < |Real.log j - Real.log n| := fun h => hlow (hcut.trans_lt h)
    simp only [hlow, htail, false_and, if_false, sub_self]

/-- The far cross limit is polar, with the infinite-gap tail paid uniformly in the horizon. -/
theorem tendsto_farCrossPair_div_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => farCrossPair φ (c N / N) N
      (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N) atTop
      (𝓝 (if m = 1 ∧ l = 1 then 2 * farCrossFinitePart φ else 0)) := by
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have hv : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  let D : ℝ := B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let E : ℝ := 16 * D + 4
  have hE : 0 < E := by dsimp only [E]; positivity
  have hsmall : Tendsto (fun N : ℕ => 32 * D * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul (32 * D)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let T : ℝ := 2 + 3 * E / ε
  have hT : 2 ≤ T := by
    dsimp only [T]
    exact le_add_of_nonneg_right (by positivity)
  have hT0 : 0 < T := by linarith
  have hε3 : 0 < ε / 3 := by positivity
  have hTsmall : E / T < ε / 3 := by
    apply (div_lt_iff₀ hT0).mpr
    have heq : ε / 3 * T = 2 * ε / 3 + E := by dsimp only [T]; field_simp [hε.ne']
    rw [heq]
    linarith only [hε]
  have htrunc := tendsto_truncatedFarCrossPair_div_overlap hφ hsupp hM hm hl hT hc hcinf hcN
  let kT : ℝ := if m = 1 ∧ l = 1 then 2 * ∫ s in (2 : ℝ)..T, crossSingular φ (1 / s) else 0
  let k : ℝ := if m = 1 ∧ l = 1 then 2 * farCrossFinitePart φ else 0
  have hk : |kT - k| ≤ 4 / T := by
    dsimp only [kT, k]
    by_cases hml : m = 1 ∧ l = 1
    · rw [if_pos hml, if_pos hml, ← mul_sub, abs_mul, abs_of_pos zero_lt_two]
      exact (mul_le_mul_of_nonneg_left (abs_integral_crossSingular_inv_sub_le hφ hsupp hM hT)
        zero_le_two).trans_eq (by ring)
    · simp only [if_neg hml, sub_self, abs_zero]
      positivity
  have hclose : ∀ᶠ N in atTop,
      |gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N))) 2 T (c N / N) N
        (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N - kT| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using htrunc.eventually (Metric.ball_mem_nhds kT hε3)
  filter_upwards [eventually_ge_atTop 1, hclose, hsmall.eventually (gt_mem_nhds hε3)]
    with N hN hcloseN hsmallN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c N / N := div_pos (hc N) hN0
  let a : ℝ := farCrossPair φ (c N / N) N
    (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N
  let b : ℝ := gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N))) 2 T (c N / N) N
    (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) / c N
  change |b - kT| < ε / 3 at hcloseN
  have hab : |a - b| ≤ 16 * D / T + 32 * D * (c N / N) := by
    dsimp only [a, b]
    rw [← sub_div, farCrossPair_sub_truncation φ hw.le hT,
      abs_div, abs_of_pos (hc N)]
    exact (div_le_div_of_nonneg_right (abs_farCross_pair_tail_le hφ hsupp hM (hc N) hT hN hu hv)
      (hc N).le).trans_eq (by dsimp only [D]; field_simp [hN0.ne', (hc N).ne', hT0.ne'])
  have htriangle : |a - k| ≤ |a - b| + |b - kT| + |kT - k| := by
    have heq : a - k = (a - b) + (b - kT) + (kT - k) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have heq : 16 * D / T + 4 / T = E / T := by dsimp only [E]; ring
  rw [Real.dist_eq]
  change |a - k| < ε
  linarith only [htriangle, hab, hcloseN, hsmallN, hk, hTsmall, heq]

/-- The actual near remainder and separated cross pairing have one signed polar limit. -/
theorem tendsto_nearArchimedean_sub_farCross_pair_div_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (gapMatrixPair (nearArchimedeanRemainder φ (c N / N)) 0 2 (c N / N) N
        (ramanujanLagCoefficient m) (ramanujanLagCoefficient l) -
        farCrossPair φ (c N / N) N (ramanujanLagCoefficient m) (ramanujanLagCoefficient l)) / c N)
      atTop (𝓝 (if m = 1 ∧ l = 1 then
        -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
          (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) else 0)) := by
  have h := (tendsto_nearArchimedeanRemainderPair_div_overlap hφ hsupp hM hm hl hc hcinf hcN).sub
    (tendsto_farCrossPair_div_overlap hφ hsupp hM hm hl hc hcinf hcN)
  have heq : (2 / (∫ u, φ u ^ 2)) * (∫ s in (0 : ℝ)..2, nearKernel φ s) -
      2 * farCrossFinitePart φ = -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
    rw [integral_nearKernel hφ hsupp, nearConstant_eq]
    have hl : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
      congr 1
      ring
    rw [hl]
    unfold farCrossFinitePart
    ring
  by_cases hml : m = 1 ∧ l = 1
  · simp only [if_pos hml, heq] at h ⊢
    exact h.congr fun N => by ring
  · simp only [if_neg hml, sub_self] at h ⊢
    exact h.congr fun N => by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearArchimedeanRemainderPair_div_overlap

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_truncatedFarCrossPair_div_overlap

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_nearArchimedean_sub_farCross_pair_div_overlap
