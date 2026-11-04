import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsReadEitherEndOfANearPair
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheFarCrossErrorAtGrowingOverlap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheGrowingGammaPairMeanIsPolar

/-!
# Terminal windows retain the signed Gamma mean

Near and separated Gamma entries are tested against a slowly varying
terminal profile. Fixed scaled-gap intervals retain the profile integral;
the reciprocal-square tail is uniform before the horizon limit. Their
signed finite parts cancel the profile-dependent source moment.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem abs_weighted_gapPair_sub_endpoint_le
    {A : ℕ → ℕ → ℝ} {K F : ℝ → ℝ} {α β w ε B BF : ℝ}
    {N : ℕ} {u v : ℕ → ℝ}
    (hF : ∀ x, |F x| ≤ BF) (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    (herr : ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
      α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w →
      |A n j - K (|Real.log j - Real.log n| / w)| ≤ ε) :
    |gapMatrixPair A α β w N (fun n => F (n / N) * u n) v -
      endpointNearPairSum K F α β w N u v| ≤
      (BF * B ^ 2 * ε) *
        nearPairSum (fun _ => 1) α β w N (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  unfold gapMatrixPair endpointNearPairSum nearPairSum
  simp only [mul_one]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  by_cases hgap : α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w
  · rw [if_pos hgap, if_pos hgap, if_pos hgap, ← sub_div]
    have heq : (F ((n : ℝ) / N) * u n) * v j * A n j -
        F (n / N) * u n * v j * K (|Real.log j - Real.log n| / w) =
        (F (n / N) * u n * v j) * (A n j - K (|Real.log j - Real.log n| / w)) := by ring
    rw [heq, abs_div, abs_of_nonneg (by positivity :
      0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (j : ℝ)), abs_mul]
    have hcoef : |F ((n : ℝ) / N) * u n * v j| ≤ BF * B ^ 2 := by
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_mul (hF _) (hu n) (abs_nonneg _) hBF)
        (hv j) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact (div_le_div_of_nonneg_right
      (mul_le_mul hcoef (herr n hn j hj hgap) (abs_nonneg _) (by positivity))
      (by positivity)).trans_eq (by ring)
  · simp only [if_neg hgap, sub_self, abs_zero, mul_zero, le_refl]

private theorem tendsto_weighted_gapPair_sub_endpoint_div_overlap
    {A : ℕ → ℕ → ℕ → ℝ} {K F : ℝ → ℝ} {α β B BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    {u v : ℕ → ℝ} (hF : ∀ x, |F x| ≤ BF)
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {c ε : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0))
    (herr : ∀ᶠ N in atTop, ∀ n ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
      α * (c N / N) < |Real.log j - Real.log n| ∧
        |Real.log j - Real.log n| ≤ β * (c N / N) →
      |A N n j - K (|Real.log j - Real.log n| / (c N / N))| ≤ ε N) :
    Tendsto (fun N : ℕ =>
      (gapMatrixPair (A N) α β (c N / N) N (fun n => F (n / N) * u n) v -
        endpointNearPairSum K F α β (c N / N) N u v) / c N) atTop (𝓝 0) := by
  have hmass := tendsto_nearPairSum_div_overlap (K := fun _ => (1 : ℝ))
    (A := 1) (L := 0) hα hαβ hβ (by intros; norm_num) (by intros; simp) le_rfl
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc hcinf hcN
  have hlim := (hε.const_mul (BF * B ^ 2)).mul hmass
  simp only [mul_zero, zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [herr] with N hN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hc N)]
  exact (div_le_div_of_nonneg_right (abs_weighted_gapPair_sub_endpoint_le hF hu hv hN)
    (hc N).le).trans_eq (by ring)

section Weighted

variable {φ F : ℝ → ℝ} {u v : ℕ → ℝ} {q : ℕ} {B BF LF : ℝ}
  (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Icc 0 1 → φ t = 0)
  (hM : 0 < ∫ t, φ t ^ 2)
  (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
  (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |F x - F y| ≤ LF * |x - y|)
  (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
  (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
  {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
  (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))

include hφ hsupp hM hF hLF hFL hq hu hv huB hvB hc hcinf hcN

/-- The actual near Gamma remainder retains the terminal profile integral. -/
theorem tendsto_weighted_nearArchimedeanRemainderPair_div_overlap :
    Tendsto (fun N : ℕ =>
      gapMatrixPair (nearArchimedeanRemainder φ (c N / N)) 0 2 (c N / N) N
        (fun n => F (n / N) * u n) v / c N) atTop
      (𝓝 (2 * periodicMean u q * periodicMean v q *
        (∫ s in (0 : ℝ)..2, nearKernel φ s / (∫ t, φ t ^ 2)) * ∫ x in (0 : ℝ)..1, F x)) := by
  obtain ⟨A, L, hL0, hA, hL⟩ := exists_nearKernel_bounds hφ hsupp
  let K : ℝ → ℝ := fun s => nearKernel φ s / (∫ t, φ t ^ 2)
  have hAK : ∀ s ∈ Icc (0 : ℝ) 2, |K s| ≤ A / (∫ t, φ t ^ 2) := by
    intro s hs
    dsimp only [K]
    rw [abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right (hA s hs) hM.le
  have hLK : ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2,
      |K x - K y| ≤ (L / (∫ t, φ t ^ 2)) * |x - y| := by
    intro x hx y hy
    dsimp only [K]
    rw [← sub_div, abs_div, abs_of_pos hM]
    exact (div_le_div_of_nonneg_right (hL x hx y hy) hM.le).trans_eq (by ring)
  have hm := tendsto_endpointNearPairSum_div_overlap
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2) two_pos
    hAK hLK (div_nonneg hL0 hM.le) hF hLF hFL hq hu hv huB hvB hc hcinf hcN
  have hε : Tendsto (fun N : ℕ => 3 * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul 3
  have hz := tendsto_weighted_gapPair_sub_endpoint_div_overlap
    (A := fun N => nearArchimedeanRemainder φ (c N / N)) (K := K)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2) two_pos
    hF huB hvB hc hcinf hcN hε (by
      filter_upwards [eventually_ge_atTop 1,
        hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with N hN hw
      intro n hn j hj hgap
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact abs_nearArchimedeanRemainder_sub_le hφ hsupp hM (div_pos (hc N) hN0) hw.le hgap.2)
  have h := hz.add hm
  simp only [zero_add] at h
  exact h.congr fun N => by ring

/-- On a fixed separated-gap interval, the actual cross entries retain their signed profile. -/
theorem tendsto_weighted_truncatedFarCrossPair_div_overlap {T : ℝ} (hT : 2 ≤ T) :
    Tendsto (fun N : ℕ => gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N)))
      2 T (c N / N) N (fun n => F (n / N) * u n) v / c N) atTop
      (𝓝 (2 * periodicMean u q * periodicMean v q *
        (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) * ∫ x in (0 : ℝ)..1, F x)) := by
  let K : ℝ → ℝ := fun s => crossSingular φ (1 / s)
  have hm := tendsto_endpointNearPairSum_div_overlap (K := K)
    (by norm_num : (0 : ℝ) ≤ 2) hT (by linarith : 0 < T)
    (fun s hs => abs_crossSingular_inv_le hφ hsupp hM hs.1)
    (fun x hx y hy => abs_crossSingular_inv_sub_le hφ hsupp hM hx.1 hy.1)
    (div_nonneg (farCrossLip_nonneg φ) (by norm_num))
    hF hLF hFL hq hu hv huB hvB hc hcinf hcN
  let D : ℝ := 5 / 2 * (∫ t, |bumpAutocorr φ t|) / (∫ t, φ t ^ 2)
  have hε : Tendsto (fun N : ℕ => D * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul D
  have hz := tendsto_weighted_gapPair_sub_endpoint_div_overlap
    (A := fun N => atomCrossErrorKernel (atomDilate φ (c N / N))) (K := K)
    (by norm_num : (0 : ℝ) ≤ 2) hT (by linarith : 0 < T)
    hF huB hvB hc hcinf hcN hε (by
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
  have h := hz.add hm
  simp only [zero_add] at h
  exact h.congr fun N => by ring

end Weighted

private theorem farCrossPair_sub_gap_cut (φ : ℝ → ℝ) {w T : ℝ} (hw : 0 ≤ w) (hT : 2 ≤ T)
    (N : ℕ) (u v : ℕ → ℝ) :
    farCrossPair φ w N u v - gapMatrixPair (atomCrossErrorKernel (atomDilate φ w)) 2 T w N u v =
      ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        if T * w < |Real.log j - Real.log n| then
          u n * v j * atomCrossErrorKernel (atomDilate φ w) n j / (Real.sqrt n * Real.sqrt j)
        else 0 := by
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

section Weighted

variable {φ F : ℝ → ℝ} {u v : ℕ → ℝ} {q : ℕ} {B BF LF : ℝ}
  (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Icc 0 1 → φ t = 0)
  (hM : 0 < ∫ t, φ t ^ 2)
  (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
  (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |F x - F y| ≤ LF * |x - y|)
  (hq : 0 < q) (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
  (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
  {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
  (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0))

include hφ hsupp hM hF hLF hFL hq hu hv huB hvB hc hcinf hcN

/-- The separated cross limit retains a terminal weight with a horizon-uniform far tail. -/
theorem tendsto_weighted_farCrossPair_div_overlap :
    Tendsto (fun N : ℕ => farCrossPair φ (c N / N) N (fun n => F (n / N) * u n) v / c N)
      atTop (𝓝 (2 * periodicMean u q * periodicMean v q *
        farCrossFinitePart φ * ∫ x in (0 : ℝ)..1, F x)) := by
  let B' : ℝ := max (BF * B) B
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hU : ∀ (N n : ℕ), |F ((n : ℝ) / N) * u n| ≤ B' := by
    intro N n
    rw [abs_mul]
    exact (mul_le_mul (hF _) (huB n) (abs_nonneg _) hBF).trans (le_max_left _ _)
  have hV : ∀ n, |v n| ≤ B' := fun n => (hvB n).trans (le_max_right _ _)
  let θ : ℝ := periodicMean u q * periodicMean v q * ∫ x in (0 : ℝ)..1, F x
  let D : ℝ := B' ^ 2 * (152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let E : ℝ := 16 * D + 4 * |θ| + 1
  have hE : 0 < E := by dsimp only [E]; positivity
  have hsmall : Tendsto (fun N : ℕ => 32 * D * (c N / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hcN.const_mul (32 * D)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let T : ℝ := 2 + 3 * E / ε
  have hT : 2 ≤ T := le_add_of_nonneg_right (by positivity)
  have hT0 : 0 < T := by linarith
  have hε3 : 0 < ε / 3 := by positivity
  have hTsmall : E / T < ε / 3 := by
    apply (div_lt_iff₀ hT0).mpr
    have heq : ε / 3 * T = 2 * ε / 3 + E := by dsimp only [T]; field_simp [hε.ne']
    rw [heq]
    linarith only [hε]
  have htrunc := tendsto_weighted_truncatedFarCrossPair_div_overlap
    hφ hsupp hM hF hLF hFL hq hu hv huB hvB hc hcinf hcN hT
  let kT : ℝ := 2 * θ * ∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)
  let k : ℝ := 2 * θ * farCrossFinitePart φ
  have hk : |kT - k| ≤ 4 * |θ| / T := by
    dsimp only [kT, k]
    rw [← mul_sub, abs_mul, abs_mul, abs_of_pos zero_lt_two]
    exact (mul_le_mul_of_nonneg_left (abs_integral_crossSingular_inv_sub_le hφ hsupp hM hT)
      (by positivity : 0 ≤ 2 * |θ|)).trans_eq (by ring)
  have heTarget : 2 * periodicMean u q * periodicMean v q *
      (∫ s in (2 : ℝ)..T, crossSingular φ (1 / s)) * (∫ x in (0 : ℝ)..1, F x) = kT := by
    dsimp only [kT, θ]
    ring
  rw [heTarget] at htrunc
  have hclose : ∀ᶠ N in atTop,
      |gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N))) 2 T (c N / N) N
        (fun n => F (n / N) * u n) v / c N - kT| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using htrunc.eventually (Metric.ball_mem_nhds kT hε3)
  filter_upwards [eventually_ge_atTop 1, hclose, hsmall.eventually (gt_mem_nhds hε3)]
    with N hN hcloseN hsmallN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c N / N := div_pos (hc N) hN0
  let a : ℝ := farCrossPair φ (c N / N) N (fun n => F (n / N) * u n) v / c N
  let b : ℝ := gapMatrixPair (atomCrossErrorKernel (atomDilate φ (c N / N)))
    2 T (c N / N) N (fun n => F (n / N) * u n) v / c N
  change |b - kT| < ε / 3 at hcloseN
  have hab : |a - b| ≤ 16 * D / T + 32 * D * (c N / N) := by
    dsimp only [a, b]
    rw [← sub_div, farCrossPair_sub_gap_cut φ hw.le hT, abs_div, abs_of_pos (hc N)]
    exact (div_le_div_of_nonneg_right
      (abs_farCross_pair_tail_le hφ hsupp hM (hc N) hT hN (hU N) hV) (hc N).le).trans_eq
      (by dsimp only [D]; field_simp [hN0.ne', (hc N).ne', hT0.ne'])
  have htriangle : |a - k| ≤ |a - b| + |b - kT| + |kT - k| := by
    have heq : a - k = (a - b) + (b - kT) + (kT - k) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hpaid : 16 * D / T + 4 * |θ| / T ≤ E / T := by
    dsimp only [E]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hT0.le
  have htarget : 2 * periodicMean u q * periodicMean v q *
      farCrossFinitePart φ * (∫ x in (0 : ℝ)..1, F x) = k := by dsimp only [k, θ]; ring
  rw [Real.dist_eq, htarget]
  change |a - k| < ε
  linarith only [htriangle, hab, hcloseN, hsmallN, hk, hTsmall, hpaid]

/-- Terminal profiles preserve the exact signed cancellation of the near and far Gamma means. -/
theorem tendsto_weighted_nearArchimedean_sub_farCross_pair_div_overlap :
    Tendsto (fun N : ℕ =>
      (gapMatrixPair (nearArchimedeanRemainder φ (c N / N)) 0 2 (c N / N) N
        (fun n => F (n / N) * u n) v -
        farCrossPair φ (c N / N) N (fun n => F (n / N) * u n) v) / c N) atTop
      (𝓝 (-((∫ t, φ t) ^ 2 / (∫ t, φ t ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
        periodicMean u q * periodicMean v q * ∫ x in (0 : ℝ)..1, F x)) := by
  have hn := tendsto_weighted_nearArchimedeanRemainderPair_div_overlap
    hφ hsupp hM hF hLF hFL hq hu hv huB hvB hc hcinf hcN
  have hf := tendsto_weighted_farCrossPair_div_overlap
    hφ hsupp hM hF hLF hFL hq hu hv huB hvB hc hcinf hcN
  have heq : (2 / (∫ t, φ t ^ 2)) * (∫ s in (0 : ℝ)..2, nearKernel φ s) -
      2 * farCrossFinitePart φ = -((∫ t, φ t) ^ 2 / (∫ t, φ t ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
    rw [integral_nearKernel hφ hsupp, nearConstant_eq]
    have hl : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
      rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * Real.pi ≠ 0)]
      congr 1
      ring
    rw [hl]
    unfold farCrossFinitePart
    ring
  have h := hn.sub hf
  rw [intervalIntegral.integral_div] at h
  have htarget : 2 * periodicMean u q * periodicMean v q *
      ((∫ s in (0 : ℝ)..2, nearKernel φ s) / (∫ t, φ t ^ 2)) * (∫ x in (0 : ℝ)..1, F x) -
      2 * periodicMean u q * periodicMean v q * farCrossFinitePart φ * (∫ x in (0 : ℝ)..1, F x) =
      -((∫ t, φ t) ^ 2 / (∫ t, φ t ^ 2)) *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) *
        periodicMean u q * periodicMean v q * (∫ x in (0 : ℝ)..1, F x) := by
    calc
      _ = ((2 / (∫ t, φ t ^ 2)) * (∫ s in (0 : ℝ)..2, nearKernel φ s) -
          2 * farCrossFinitePart φ) * periodicMean u q * periodicMean v q *
            (∫ x in (0 : ℝ)..1, F x) := by ring
      _ = _ := by rw [heq]
  rw [htarget] at h
  exact h.congr fun N => by ring

end Weighted
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_weighted_nearArchimedeanRemainderPair_div_overlap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_weighted_farCrossPair_div_overlap
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_weighted_nearArchimedean_sub_farCross_pair_div_overlap
