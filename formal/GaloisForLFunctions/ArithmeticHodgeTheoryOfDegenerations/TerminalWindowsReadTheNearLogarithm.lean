import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWeightsReadEitherEndOfANearPair
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearBlockAlongAGrowingOverlap

/-!
# The near logarithm reads the terminal coordinate

The logarithm on an incoming index can be moved to the terminal endpoint:
its difference is the exact logarithmic gap. The resulting limit retains
the profile `x ↦ h(log x) log x` rather than its unweighted mean.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence
open RenormalizedArithmeticPotentialTheory.CompletedShell

/-- Moving an incoming logarithm to the terminal endpoint costs the near-pair gap. -/
theorem abs_endpointNearPairSum_log_transfer_le
    {K F : ℝ → ℝ} {α β A BF w : ℝ}
    (hαβ : α ≤ β) (hβ : 0 < β) (hw : 0 < w)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A) (hF : ∀ x, |F x| ≤ BF)
    {u v : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {N : ℕ} (hN : 1 ≤ N) :
    |endpointNearPairSum K F α β w N u (fun j => v j * Real.log ((j : ℝ) / N)) -
      endpointNearPairSum K (fun x => F x * Real.log x) α β w N u v| ≤
      (BF * B ^ 2 * A * β * w) *
        nearPairSum (fun _ => 1) α β w N (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hF 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold endpointNearPairSum nearPairSum
  simp only [mul_one]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  by_cases hgap : α * w < |Real.log j - Real.log n| ∧ |Real.log j - Real.log n| ≤ β * w
  · rw [if_pos hgap, if_pos hgap, if_pos hgap]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hs : |Real.log j - Real.log n| / w ∈ Icc α β :=
      ⟨((lt_div_iff₀ hw).mpr hgap.1).le, (div_le_iff₀ hw).mpr hgap.2⟩
    have hlog : |Real.log ((j : ℝ) / N) - Real.log ((n : ℝ) / N)| ≤ β * w := by
      rw [Real.log_div hj0.ne' hN0.ne', Real.log_div hn0.ne' hN0.ne', sub_sub_sub_cancel_right]
      exact hgap.2
    have heq : F ((n : ℝ) / N) * u n * (v j * Real.log ((j : ℝ) / N)) *
          K (|Real.log j - Real.log n| / w) -
        (F ((n : ℝ) / N) * Real.log ((n : ℝ) / N)) * u n * v j *
          K (|Real.log j - Real.log n| / w) =
        F ((n : ℝ) / N) * u n * v j * K (|Real.log j - Real.log n| / w) *
          (Real.log ((j : ℝ) / N) - Real.log ((n : ℝ) / N)) := by ring
    rw [← sub_div, heq, abs_div,
      abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (j : ℝ)),
      abs_mul, abs_mul, abs_mul, abs_mul]
    have hb : |F ((n : ℝ) / N)| * |u n| * |v j| *
        |K (|Real.log j - Real.log n| / w)| *
        |Real.log ((j : ℝ) / N) - Real.log ((n : ℝ) / N)| ≤
        BF * B * B * A * (β * w) :=
      mul_le_mul (mul_le_mul (mul_le_mul
        (mul_le_mul (hF _) (hu n) (abs_nonneg _) hBF) (hv j) (abs_nonneg _) (by positivity))
        (hA _ hs) (abs_nonneg _) (by positivity)) hlog (abs_nonneg _) (by positivity)
    exact (div_le_div_of_nonneg_right hb (by positivity)).trans_eq (by ring)
  · simp only [if_neg hgap, sub_self, abs_zero, mul_zero, le_refl]

/-- The incoming and terminal logarithms agree after overlap normalization. -/
theorem tendsto_endpointNearPairSum_log_transfer
    {K F : ℝ → ℝ} {α β A BF : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : 0 < β)
    (hA : ∀ s ∈ Icc α β, |K s| ≤ A) (hF : ∀ x, |F x| ≤ BF)
    {u v : ℕ → ℝ} {B : ℝ} (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (endpointNearPairSum K F α β (c N / N) N u (fun j => v j * Real.log ((j : ℝ) / N)) -
        endpointNearPairSum K (fun x => F x * Real.log x) α β (c N / N) N u v) / c N)
      atTop (𝓝 0) := by
  have hmass := tendsto_nearPairSum_div_overlap (K := fun _ => (1 : ℝ))
    (A := 1) (L := 0) hα hαβ hβ (by intros; norm_num) (by intros; simp) le_rfl
    (q := 1) (u := fun _ => 1) (v := fun _ => 1) (B := 1) one_pos
    (by intros; rfl) (by intros; rfl) (by intros; norm_num) (by intros; norm_num)
    hc hcinf hcN
  have hlim := (hcN.const_mul (BF * B ^ 2 * A * β)).mul hmass
  simp only [mul_zero, zero_mul] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := abs_endpointNearPairSum_log_transfer_le hαβ hβ (div_pos (hc N) hN0)
    hA hF hu hv hN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hc N)]
  exact (div_le_div_of_nonneg_right hb (hc N).le).trans_eq (by ring)

/-- The terminal near logarithmic row has its polar profile integral at every sublinear
growing overlap. The sign of its occurrence in the complete form is separate. -/
theorem tendsto_terminal_nearLogRow
    {φ h : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {A : ℝ} (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      endpointNearPairSum (fun s => shellAutocorr φ s / ∫ u, φ u ^ 2)
        (logProfile h) 0 2 (c N / N) N (ramanujanLagCoefficient l)
        (fun j => ramanujanLagCoefficient m j * Real.log ((j : ℝ) / N)) / c N)
      atTop (𝓝 (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x else 0)) := by
  obtain ⟨LK, hLK0, hK, hKL⟩ := exists_shellKernel_bounds hφ hφsupp hM
  obtain ⟨BF, _, hBF, _⟩ := exists_bound_lipschitz hh hsupp
  have hhlog : ContDiff ℝ 2 (fun y => y * h y) := contDiff_id.mul hh
  have hslog : ∀ y, y ∉ Set.Icc (-A) 0 → y * h y = 0 := by
    intro y hy
    rw [hsupp y hy, mul_zero]
  obtain ⟨BG, _, hBG, _⟩ := exists_bound_lipschitz hhlog hslog
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hslog) hhlog (by norm_num)
  have hGL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |logProfile (fun z => z * h z) x - logProfile (fun z => z * h z) y| ≤
        ((LG : ℝ) * Real.exp (2 * A)) * |x - y| :=
    fun x _ y _ => abs_logProfile_sub_le hhlog hslog hA hBG hLG x y
  let B : ℝ := (∑ d ∈ m.divisors, (d : ℝ)) + ∑ d ∈ l.divisors, (d : ℝ)
  have hu : ∀ n, ramanujanLagCoefficient l (n + l * m) = ramanujanLagCoefficient l n :=
    fun n => ramanujanLagCoefficient_add_mul l n m
  have hv : ∀ n, ramanujanLagCoefficient m (n + l * m) = ramanujanLagCoefficient m n := by
    intro n
    rw [mul_comm l m]
    exact ramanujanLagCoefficient_add_mul m n l
  have huB : ∀ n, |ramanujanLagCoefficient l n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le l n).trans (le_add_of_nonneg_left (by positivity))
  have hvB : ∀ n, |ramanujanLagCoefficient m n| ≤ B := fun n =>
    (abs_ramanujanLagCoefficient_le m n).trans (le_add_of_nonneg_right (by positivity))
  have hmain := tendsto_endpointNearPairSum_div_overlap
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 2) hK hKL hLK0
    (fun x => abs_logProfile_le hBG x) (by positivity : 0 ≤ (LG : ℝ) * Real.exp (2 * A))
    hGL (Nat.mul_pos hl hm) hu hv huB hvB hc hcinf hcN
  rw [periodicMean_ramanujan_of_dvd hl (Nat.mul_pos hl hm) (dvd_mul_right l m),
    periodicMean_ramanujan_of_dvd hm (Nat.mul_pos hl hm) (dvd_mul_left m l),
    integral_shellKernel hφ hφsupp hM] at hmain
  have heq : 2 * (if l = 1 then (1 : ℝ) else 0) * (if m = 1 then (1 : ℝ) else 0) *
        ((∫ u, φ u) ^ 2 / (2 * ∫ u, φ u ^ 2)) *
        (∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x) =
      (if m = 1 ∧ l = 1 then ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) *
        ∫ x in (0 : ℝ)..1, logProfile (fun y => y * h y) x else 0) := by
    split_ifs <;> simp_all only [and_self, and_true, and_false, true_and, false_and,
      mul_zero, zero_mul, mul_one]
    field_simp
  rw [heq] at hmain
  have htransfer := tendsto_endpointNearPairSum_log_transfer
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ) < 2) hK (fun x => abs_logProfile_le hBF x) huB hvB hc hcinf hcN
  have hprofile : (fun x => logProfile h x * Real.log x) = logProfile (fun y => y * h y) := by
    funext x
    unfold logProfile
    split_ifs <;> ring
  rw [hprofile] at htransfer
  have ht := htransfer.add hmain
  simp only [zero_add] at ht
  exact ht.congr fun N => by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_endpointNearPairSum_log_transfer
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_terminal_nearLogRow
