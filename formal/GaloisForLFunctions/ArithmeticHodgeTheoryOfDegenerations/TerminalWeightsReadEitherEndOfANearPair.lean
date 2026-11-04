import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsPreserveThePolarNearMean

/-!
# A terminal weight can read either end of a near pair

The linear separation of two horizon indices is bounded by their
logarithmic separation times the horizon. A Lipschitz weight can therefore
be moved from the smaller index to a specified endpoint with an error
that vanishes after division by the overlap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory

/-- A logarithmic-gap pairing with a terminal profile on its first index. -/
def endpointNearPairSum (K F : ℝ → ℝ) (α β w : ℝ) (N : ℕ)
    (u v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
    if α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w then
      F (n / N) * u n * v j * K (|Real.log j - Real.log n| / w) /
        (Real.sqrt n * Real.sqrt j)
    else 0

private theorem abs_terminal_weight_sub_min_le {F : ℝ → ℝ} {LF β w : ℝ}
    (hLF : 0 ≤ LF) (hβ : 0 < β) (hw : 0 < w)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {N n j : ℕ} (hn : n ∈ Finset.Icc 1 N) (hj : j ∈ Finset.Icc 1 N)
    (hgap : |Real.log j - Real.log n| ≤ β * w) :
    |F (n / N) - F ((min n j : ℕ) / N)| ≤ LF * (β * w) := by
  have hN : 1 ≤ N := (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN0]
    exact_mod_cast (Finset.mem_Icc.mp hk).2
  by_cases hnj : n ≤ j
  · rw [min_eq_left hnj, sub_self, abs_zero]
    positivity
  · have hjn : j ≤ n := by omega
    have hjnR : (j : ℝ) ≤ n := by exact_mod_cast hjn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hj0)
    rw [inv_div, Real.log_div hn0.ne' hj0.ne'] at hlog
    have hgap' : Real.log n - Real.log j ≤ β * w :=
      (le_abs_self _).trans (by simpa only [abs_sub_comm] using hgap)
    have heq : 1 - (j : ℝ) / n = ((n : ℝ) - j) / n := by
      field_simp [hn0.ne']
    rw [heq] at hlog
    have hlin : (n : ℝ) - j ≤ β * w * n :=
      (div_le_iff₀ hn0).mp (hlog.trans hgap')
    have hdiff : ((n : ℝ) - j) / N ≤ β * w := by
      rw [div_le_iff₀ hN0]
      exact hlin.trans (mul_le_mul_of_nonneg_left hnN (by positivity))
    rw [min_eq_right hjn]
    have h := hFL _ (hmem n hn) _ (hmem j hj)
    rw [← sub_div, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hjnR) hN0.le)] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdiff hLF)

/-- Moving a bounded-kernel near-pair weight to the first endpoint costs only its variation. -/
theorem abs_endpointNearPairSum_sub_nearPairSum_le
    {K F : ℝ → ℝ} {α β A LF w : ℝ}
    (hαβ : α ≤ β) (hβ : 0 < β) (hw : 0 < w)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    (N : ℕ) :
    |endpointNearPairSum K F α β w N u v -
      nearPairSum K α β w N u v (fun n => F (n / N))| ≤
      (LF * β * w * B ^ 2 * A) *
        nearPairSum (fun _ => 1) α β w N (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  unfold endpointNearPairSum nearPairSum
  simp only [mul_one]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  by_cases hgap : α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w
  · rw [if_pos hgap, if_pos hgap, if_pos hgap]
    have hs : |Real.log j - Real.log n| / w ∈ Icc α β :=
      ⟨((lt_div_iff₀ hw).mpr hgap.1).le, (div_le_iff₀ hw).mpr hgap.2⟩
    have hFdiff := abs_terminal_weight_sub_min_le hLF hβ hw hFL hn hj hgap.2
    have heq : F ((n : ℝ) / N) * u n * v j * K (|Real.log j - Real.log n| / w) -
        F ((min n j : ℕ) / N) * u n * v j * K (|Real.log j - Real.log n| / w) =
        (F (n / N) - F ((min n j : ℕ) / N)) * u n * v j *
          K (|Real.log j - Real.log n| / w) := by ring
    rw [← sub_div, heq, abs_div, abs_of_nonneg (by positivity :
      0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (j : ℝ)), abs_mul, abs_mul, abs_mul]
    have hb : |F ((n : ℝ) / N) - F ((min n j : ℕ) / N)| * |u n| * |v j| *
        |K (|Real.log j - Real.log n| / w)| ≤ (LF * (β * w)) * B * B * A :=
      mul_le_mul (mul_le_mul
        (mul_le_mul hFdiff (hu n) (abs_nonneg _) (by positivity))
        (hv j) (abs_nonneg _) (by positivity)) (hA _ hs) (abs_nonneg _) (by positivity)
    exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by ring)
  · simp only [if_neg hgap, sub_self, abs_zero, mul_zero, le_refl]

/-- The endpoint and smaller-index readings agree after overlap normalization. -/
theorem tendsto_endpointNearPairSum_sub_nearPairSum_div_overlap
    {K F : ℝ → ℝ} {α β A LF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (endpointNearPairSum K F α β (c N / N) N u v -
      nearPairSum K α β (c N / N) N u v (fun n => F (n / N))) / c N)
      atTop (𝓝 0) := by
  have hmass := tendsto_nearPairSum_div_overlap (K := fun _ => (1 : ℝ))
    (A := 1) (L := 0) hα hαβ hβ (by intros; norm_num) (by intros; simp) le_rfl
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc hcinf hcN
  have hcoeff := (((hcN.const_mul (LF * β)).mul_const (B ^ 2)).mul_const A)
  have hlim := hcoeff.mul hmass
  simp only [mul_zero, zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := abs_endpointNearPairSum_sub_nearPairSum_le hαβ hβ
    (div_pos (hc N) hN0) hA hLF hFL hu hv N
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hc N)]
  exact (div_le_div_of_nonneg_right hb (hc N).le).trans_eq (by ring)

/-- The signed periodic near mean is unchanged when the terminal profile reads one endpoint. -/
theorem tendsto_endpointNearPairSum_div_overlap
    {K F : ℝ → ℝ} {α β A L LF BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A)
    (hL : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |K x - K y| ≤ L * |x - y|)
    (hL0 : 0 ≤ L) (hF : ∀ x, |F x| ≤ BF) (hLF : 0 ≤ LF)
    (hFL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |F x - F y| ≤ LF * |x - y|)
    {u v : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hu : ∀ n, u (n + q) = u n) (hv : ∀ n, v (n + q) = v n)
    {B : ℝ} (huB : ∀ n, |u n| ≤ B) (hvB : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => endpointNearPairSum K F α β (c N / N) N u v / c N)
      atTop (𝓝 (2 * periodicMean u q * periodicMean v q *
        (∫ s in α..β, K s) * ∫ x in (0 : ℝ)..1, F x)) := by
  have hz := tendsto_endpointNearPairSum_sub_nearPairSum_div_overlap hα hαβ hβ hA hLF
    hFL huB hvB hc hcinf hcN
  have hm := tendsto_nearPairSum_terminal_weight_div_overlap hα hαβ hβ hA hL hL0 hF hFL
    hq hu hv huB hvB hc hcinf hcN
  have h := hz.add hm
  simp only [zero_add] at h
  exact h.congr fun N => by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_endpointNearPairSum_sub_nearPairSum_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_endpointNearPairSum_div_overlap
