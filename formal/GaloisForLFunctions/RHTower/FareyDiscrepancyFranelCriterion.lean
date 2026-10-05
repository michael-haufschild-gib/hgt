import GaloisForLFunctions.RHTower.FareySawtoothMeanSquare

/-!
# The Franel–Landau criterion

Let `F_n = {f_1 < ⋯ < f_L}` be the Farey fractions `a/q`, `1 ≤ a ≤ q ≤ n`.  The Riemann hypothesis
holds if and only if `Σ_ν |f_ν - ν/L| = O(n^{1/2+δ})` for every `δ > 0`.

The converse direction is Landau's receiver.  For the forward direction, write
`D(x) = L x - N_n(x)` for the Farey defect.  Distinct Farey fractions are at least `1/n²` apart,
so `N_n` is constant on `[f_ν, f_ν + 1/n²)` and `D` grows there with slope `L`; on `[0, 1]`,
`D = ½ + S_n` with `S_n` the Farey sawtooth.  Averaging over these disjoint intervals gives
`Σ_ν |f_ν - ν/L| ≤ (n²/L) ∫_0^1 |S_n| + 3/2`.  The mean square of `S_n` is
`O(n^{1+2δ} log³ n)` under the Riemann hypothesis, and `L ≥ n²/16`.
-/

open Finset MeasureTheory

open RHTower.Sieve (fareySet mem_fareySet)

namespace RHTower

noncomputable section

/-- Distinct Farey fractions of order `n` are at least `1/n²` apart. -/
theorem one_div_sq_le_fareyValue_sub {n : ℕ} {p r : ℕ × ℕ} (hp : p ∈ fareySet n)
    (hr : r ∈ fareySet n) (hlt : fareyValue p < fareyValue r) :
    1 / (n : ℝ) ^ 2 ≤ fareyValue r - fareyValue p := by
  obtain ⟨_, ⟨hq1, hqn⟩, _, _⟩ := mem_fareySet.mp hp
  obtain ⟨_, ⟨hs1, hsn⟩, _, _⟩ := mem_fareySet.mp hr
  unfold fareyValue at hlt ⊢
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
  have hs0 : (0 : ℝ) < r.2 := by exact_mod_cast hs1
  have hcross : p.1 * r.2 < r.1 * p.2 := by
    rw [div_lt_div_iff₀ hq0 hs0] at hlt
    exact_mod_cast hlt
  have hnum : 1 ≤ (r.1 : ℝ) * p.2 - p.1 * r.2 := by
    have h1 : p.1 * r.2 + 1 ≤ r.1 * p.2 := hcross
    have h2 : (p.1 : ℝ) * r.2 + 1 ≤ r.1 * p.2 := by exact_mod_cast h1
    linarith
  have hden : (p.2 : ℝ) * r.2 ≤ (n : ℝ) ^ 2 := by
    have h1 : (p.2 : ℝ) ≤ n := by exact_mod_cast hqn
    have h2 : (r.2 : ℝ) ≤ n := by exact_mod_cast hsn
    rw [sq]
    exact mul_le_mul h1 h2 hs0.le (by positivity)
  have e : (r.1 : ℝ) / r.2 - p.1 / p.2 = ((r.1 : ℝ) * p.2 - p.1 * r.2) / (p.2 * r.2) := by
    field_simp
  rw [e]
  calc 1 / (n : ℝ) ^ 2 ≤ 1 / ((p.2 : ℝ) * r.2) := one_div_le_one_div_of_le (by positivity) hden
    _ ≤ ((r.1 : ℝ) * p.2 - p.1 * r.2) / (p.2 * r.2) :=
        div_le_div_of_nonneg_right hnum (by positivity)

/-- The Farey count is constant on `[f, f + 1/n²)` for every Farey fraction `f`. -/
theorem fareyCount_eq_fareyRank {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareySet n) {x : ℝ}
    (hx0 : fareyValue p ≤ x) (hx1 : x < fareyValue p + 1 / (n : ℝ) ^ 2) :
    fareyCount n x = fareyRank n p := by
  unfold fareyCount fareyRank
  congr 1
  refine filter_congr fun r hr => ?_
  constructor
  · intro hrx
    by_contra hlt
    have := one_div_sq_le_fareyValue_sub hp hr (not_le.mp hlt)
    linarith
  · intro hrp
    linarith

theorem measurable_fareySawtooth (n : ℕ) : Measurable (fareySawtooth n) :=
  Finset.measurable_sum _ fun _ _ =>
    (measurable_centeredFract.comp (measurable_const_mul _)).mul_const _

theorem abs_fareySawtooth_le (n : ℕ) (x : ℝ) :
    |fareySawtooth n x| ≤ ∑ k ∈ Ioc 0 n, |(mertensIoc (n / k) : ℝ)| / 2 := by
  unfold fareySawtooth
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h1 := abs_centeredFract_le ((k : ℝ) * x)
  have h2 := abs_nonneg (mertensIoc (n / k) : ℝ)
  nlinarith

/-- Bounded measurable functions are integrable on `(0, 1]`. -/
theorem integrableOn_Ioc_zero_one_of_abs_le {g : ℝ → ℝ} (hg : Measurable g) (K : ℝ)
    (hK : ∀ x, |g x| ≤ K) : IntegrableOn g (Set.Ioc 0 1) :=
  Integrable.of_bound hg.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)

/-- A Farey fraction `f < 1` of order `n` satisfies `0 < f` and `f + 1/n² ≤ 1`. -/
theorem fareyValue_pos_and_add_le {n : ℕ} (hn : 1 ≤ n) {p : ℕ × ℕ} (hp : p ∈ fareySet n)
    (hp1 : fareyValue p < 1) : 0 < fareyValue p ∧ fareyValue p + 1 / (n : ℝ) ^ 2 ≤ 1 := by
  obtain ⟨⟨ha1, _⟩, ⟨hq1, hqn⟩, _, _⟩ := mem_fareySet.mp hp
  have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · unfold fareyValue
    have : (0 : ℝ) < p.1 := by exact_mod_cast ha1
    positivity
  · have hlt : p.1 < p.2 := by
      have := hp1
      unfold fareyValue at this
      rw [div_lt_one hq0] at this
      exact_mod_cast this
    have h1 : (p.1 : ℝ) + 1 ≤ p.2 := by exact_mod_cast hlt
    have h2 : 1 / (n : ℝ) ^ 2 ≤ 1 / (p.2 : ℝ) := by
      refine one_div_le_one_div_of_le hq0 ?_
      have : (p.2 : ℝ) ≤ n := by exact_mod_cast hqn
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have h3 : fareyValue p + 1 / (p.2 : ℝ) = ((p.1 : ℝ) + 1) / p.2 := by
      unfold fareyValue; field_simp
    have h4 : ((p.1 : ℝ) + 1) / p.2 ≤ 1 := div_le_one_of_le₀ h1 hq0.le
    linarith

/-- The local estimate: `(1/n²)(|L f - rank f| - L/n² - ½) ≤ ∫_{[f, f + 1/n²)} |S_n|` for every
Farey fraction `f < 1`. -/
theorem fareyDefect_le_setIntegral {n : ℕ} (hn : 1 ≤ n) {p : ℕ × ℕ} (hp : p ∈ fareySet n)
    (hp1 : fareyValue p < 1) :
    1 / (n : ℝ) ^ 2 * (|((fareySet n).card : ℝ) * fareyValue p - fareyRank n p|
        - ((fareySet n).card : ℝ) * (1 / (n : ℝ) ^ 2) - 1 / 2)
      ≤ ∫ x in Set.Ico (fareyValue p) (fareyValue p + 1 / (n : ℝ) ^ 2), |fareySawtooth n x| := by
  set h : ℝ := 1 / (n : ℝ) ^ 2 with hh
  set L : ℝ := ((fareySet n).card : ℝ) with hL
  set f : ℝ := fareyValue p with hf
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : 0 < h := by positivity
  obtain ⟨hf0, hfh⟩ := fareyValue_pos_and_add_le hn hp hp1
  have hsub : Set.Ico f (f + h) ⊆ Set.Ioc 0 1 := fun x hx =>
    ⟨lt_of_lt_of_le hf0 hx.1, by linarith [hx.2]⟩
  have hL0 : 0 ≤ L := by positivity
  have hpt : ∀ x ∈ Set.Ico f (f + h),
      |L * f - fareyRank n p| - L * h - 1 / 2 ≤ |fareySawtooth n x| := by
    intro x hx
    have hcnt := fareyCount_eq_fareyRank hp hx.1 hx.2
    have hdef := card_mul_sub_fareyCount_eq hn (x := x) (by linarith [hx.1]) (by linarith [hx.2])
    rw [hcnt] at hdef
    have hS : L * x - fareyRank n p = 1 / 2 + fareySawtooth n x := hdef
    have e : L * f - fareyRank n p = (1 / 2 + fareySawtooth n x) - L * (x - f) := by linarith
    have h1 : 0 ≤ L * (x - f) := mul_nonneg hL0 (by linarith [hx.1])
    have h2 : L * (x - f) ≤ L * h := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hL0
    have h3 : |1 / 2 + fareySawtooth n x| ≤ 1 / 2 + |fareySawtooth n x| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h4 : |L * f - fareyRank n p| ≤ 1 / 2 + |fareySawtooth n x| + L * h := by
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h1]
      linarith
    linarith
  have hint1 : IntegrableOn (fun _ : ℝ => |L * f - fareyRank n p| - L * h - 1 / 2)
      (Set.Ico f (f + h)) :=
    (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl).mono_set hsub
  have hint2 : IntegrableOn (fun x => |fareySawtooth n x|) (Set.Ico f (f + h)) :=
    (integrableOn_Ioc_zero_one_of_abs_le (measurable_fareySawtooth n).abs _
      fun x => by rw [abs_abs]; exact abs_fareySawtooth_le n x).mono_set hsub
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Ico hpt
  rw [setIntegral_const, Real.volume_real_Ico, smul_eq_mul,
    show max (f + h - f) 0 = h by rw [add_sub_cancel_left, max_eq_left hh0.le]] at hmono
  exact hmono

/-- `∫_{(0,1]} |S_n| ≤ (∫_0^1 S_n²)/(2T) + T/2` for `T > 0`. -/
theorem setIntegral_abs_fareySawtooth_le (n : ℕ) {T : ℝ} (hT : 0 < T) :
    ∫ x in Set.Ioc (0 : ℝ) 1, |fareySawtooth n x|
      ≤ (∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2 := by
  set K := ∑ k ∈ Ioc 0 n, |(mertensIoc (n / k) : ℝ)| / 2
  have hK : ∀ x, |fareySawtooth n x| ≤ K := abs_fareySawtooth_le n
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hint1 : IntegrableOn (fun x => |fareySawtooth n x|) (Set.Ioc 0 1) :=
    integrableOn_Ioc_zero_one_of_abs_le (measurable_fareySawtooth n).abs K
      fun x => by rw [abs_abs]; exact hK x
  have hsq : IntegrableOn (fun x => fareySawtooth n x ^ 2) (Set.Ioc 0 1) :=
    integrableOn_Ioc_zero_one_of_abs_le ((measurable_fareySawtooth n).pow_const 2) (K ^ 2)
      fun x => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
  have hint2 : IntegrableOn (fun x => fareySawtooth n x ^ 2 / (2 * T) + T / 2) (Set.Ioc 0 1) :=
    (hsq.div_const _).add (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl)
  have hpt : ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      |fareySawtooth n x| ≤ fareySawtooth n x ^ 2 / (2 * T) + T / 2 := by
    intro x _
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    have := sq_nonneg (|fareySawtooth n x| - T)
    have e : |fareySawtooth n x| ^ 2 = fareySawtooth n x ^ 2 := sq_abs _
    nlinarith
  refine (setIntegral_mono_on hint1 hint2 measurableSet_Ioc hpt).trans_eq ?_
  rw [integral_add (hsq.div_const _)
      (integrableOn_Ioc_zero_one_of_abs_le measurable_const _ fun _ => le_rfl),
    integral_div, setIntegral_const, Real.volume_real_Ioc, smul_eq_mul,
    intervalIntegral.integral_of_le zero_le_one]
  norm_num

/-- The Farey discrepancy is at most the number of Farey fractions. -/
theorem fareyL1Discrepancy_le_card (n : ℕ) : fareyL1Discrepancy n ≤ (fareySet n).card := by
  unfold fareyL1Discrepancy
  calc ∑ p ∈ fareySet n, |fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)|
      ≤ ∑ _p ∈ fareySet n, (1 : ℝ) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨⟨ha1, _⟩, ⟨hq1, _⟩, hle, _⟩ := mem_fareySet.mp hp
        have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
        have hf0 : 0 ≤ fareyValue p := by unfold fareyValue; positivity
        have hf1 : fareyValue p ≤ 1 := by
          unfold fareyValue; rw [div_le_one hq0]; exact_mod_cast hle
        have hr0 : 0 ≤ (fareyRank n p : ℝ) / ((fareySet n).card : ℝ) := by positivity
        have hr1 : (fareyRank n p : ℝ) / ((fareySet n).card : ℝ) ≤ 1 := by
          have hc : fareyRank n p ≤ (fareySet n).card := card_filter_le _ _
          rcases Nat.eq_zero_or_pos (fareySet n).card with h0 | hpos
          · rw [h0, Nat.cast_zero, div_zero]; norm_num
          · rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast hc
        rw [abs_sub_le_iff]
        constructor <;> linarith
    _ = (fareySet n).card := by simp

/-- **The transfer inequality.**  For `n ≥ 1` and `T > 0`,
`Σ_ν |f_ν - ν/L| ≤ (n²/L)((∫_0^1 S_n²)/(2T) + T/2) + 3/2`. -/
theorem fareyL1Discrepancy_le_meanSquare {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T) :
    fareyL1Discrepancy n ≤ (n : ℝ) ^ 2 / ((fareySet n).card : ℝ)
        * ((∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2) + 3 / 2 := by
  set L : ℝ := ((fareySet n).card : ℝ) with hL
  set h : ℝ := 1 / (n : ℝ) ^ 2 with hh
  set A : ℝ := (∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2 with hA
  set P := (fareySet n).filter (fun p => fareyValue p < 1) with hP
  set J : ℕ × ℕ → Set ℝ := fun p => Set.Ico (fareyValue p) (fareyValue p + h) with hJ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : 0 < h := by positivity
  have hmem11 : ((1 : ℕ), (1 : ℕ)) ∈ fareySet n :=
    mem_fareySet.mpr ⟨⟨le_rfl, hn⟩, ⟨le_rfl, hn⟩, le_rfl, Nat.coprime_one_left 1⟩
  have hLpos : 0 < L := by
    rw [hL]; exact_mod_cast card_pos.mpr ⟨_, hmem11⟩
  have hLle : L ≤ (n : ℝ) ^ 2 := by rw [hL]; exact_mod_cast card_fareySet_le n
  -- the fractions equal to `1` contribute nothing
  have hsplit : fareyL1Discrepancy n = ∑ p ∈ P, |L * fareyValue p - fareyRank n p| / L := by
    unfold fareyL1Discrepancy
    rw [← sum_filter_add_sum_filter_not (fareySet n) (fun p => fareyValue p < 1)]
    have hzero : ∑ p ∈ (fareySet n).filter (fun p => ¬ fareyValue p < 1),
        |fareyValue p - (fareyRank n p : ℝ) / ((fareySet n).card : ℝ)| = 0 := by
      refine sum_eq_zero fun p hp => ?_
      obtain ⟨hp0, hp1⟩ := mem_filter.mp hp
      obtain ⟨_, ⟨hq1, _⟩, hle, _⟩ := mem_fareySet.mp hp0
      have hq0 : (0 : ℝ) < p.2 := by exact_mod_cast hq1
      have hf1 : fareyValue p ≤ 1 := by
        unfold fareyValue; rw [div_le_one hq0]; exact_mod_cast hle
      have hfeq : fareyValue p = 1 := le_antisymm hf1 (not_lt.mp hp1)
      have hrank : fareyRank n p = (fareySet n).card := by
        unfold fareyRank
        congr 1
        refine filter_true_of_mem fun r hr => ?_
        obtain ⟨_, ⟨hr1, _⟩, hrle, _⟩ := mem_fareySet.mp hr
        have hr0 : (0 : ℝ) < r.2 := by exact_mod_cast hr1
        rw [hfeq]; unfold fareyValue; rw [div_le_one hr0]; exact_mod_cast hrle
      rw [hfeq, hrank, div_self hLpos.ne', sub_self, abs_zero]
    rw [hzero, add_zero]
    refine sum_congr rfl fun p _ => ?_
    rw [show fareyValue p - (fareyRank n p : ℝ) / L = (L * fareyValue p - fareyRank n p) / L by
      field_simp, abs_div, abs_of_pos hLpos]
  have hsubJ : ∀ p ∈ P, J p ⊆ Set.Ioc 0 1 := by
    intro p hp x hx
    obtain ⟨hf0, hfh⟩ := fareyValue_pos_and_add_le hn (mem_filter.mp hp).1 (mem_filter.mp hp).2
    exact ⟨lt_of_lt_of_le hf0 hx.1, by linarith [hx.2]⟩
  have hintIoc : IntegrableOn (fun x => |fareySawtooth n x|) (Set.Ioc 0 1) :=
    integrableOn_Ioc_zero_one_of_abs_le (measurable_fareySawtooth n).abs _
      fun x => by rw [abs_abs]; exact abs_fareySawtooth_le n x
  have hdisj : Set.Pairwise (↑P) (Function.onFun Disjoint J) := by
    intro p hp r hr hpr
    have hp' := (mem_filter.mp (mem_coe.mp hp)).1
    have hr' := (mem_filter.mp (mem_coe.mp hr)).1
    have hne : fareyValue p ≠ fareyValue r := fun heq => hpr (fareyValue_injOn n hp' hr' heq)
    rw [Function.onFun, Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := one_div_sq_le_fareyValue_sub hp' hr' hlt
      linarith [hx1.2, hx2.1]
    · have := one_div_sq_le_fareyValue_sub hr' hp' hlt
      linarith [hx2.2, hx1.1]
  have hunion : ∑ p ∈ P, ∫ x in J p, |fareySawtooth n x|
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1, |fareySawtooth n x| := by
    rw [← integral_biUnion_finset P (fun p _ => measurableSet_Ico) hdisj
      (fun p hp => hintIoc.mono_set (hsubJ p hp))]
    exact setIntegral_mono_set hintIoc (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (LE.le.eventuallyLE (Set.iUnion₂_subset fun p hp => hsubJ p hp))
  have hIoc : ∫ x in Set.Ioc (0 : ℝ) 1, |fareySawtooth n x| ≤ A :=
    setIntegral_abs_fareySawtooth_le n hT
  have hloc : ∀ p ∈ P, h * (|L * fareyValue p - fareyRank n p| - L * h - 1 / 2)
      ≤ ∫ x in J p, |fareySawtooth n x| :=
    fun p hp => fareyDefect_le_setIntegral hn (mem_filter.mp hp).1 (mem_filter.mp hp).2
  have hsum : h * ∑ p ∈ P, |L * fareyValue p - fareyRank n p|
      - h * ((P.card : ℝ) * (L * h + 1 / 2)) ≤ A := by
    have h1 := sum_le_sum hloc
    have e : ∑ p ∈ P, h * (|L * fareyValue p - fareyRank n p| - L * h - 1 / 2)
        = h * ∑ p ∈ P, |L * fareyValue p - fareyRank n p|
          - h * ((P.card : ℝ) * (L * h + 1 / 2)) := by
      rw [← mul_sum, sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, nsmul_eq_mul,
        nsmul_eq_mul]
      ring
    rw [e] at h1
    linarith
  have hPcard : (P.card : ℝ) ≤ L := by rw [hL]; exact_mod_cast card_filter_le _ _
  have hhn : (n : ℝ) ^ 2 * h = 1 := by rw [hh]; field_simp
  have hDsum : ∑ p ∈ P, |L * fareyValue p - fareyRank n p|
      ≤ (n : ℝ) ^ 2 * A + L * (L * h + 1 / 2) := by
    have h1 : h * ∑ p ∈ P, |L * fareyValue p - fareyRank n p|
        ≤ A + h * (L * (L * h + 1 / 2)) := by
      have : h * ((P.card : ℝ) * (L * h + 1 / 2)) ≤ h * (L * (L * h + 1 / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPcard (by positivity)) hh0.le
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (n : ℝ))
    calc ∑ p ∈ P, |L * fareyValue p - fareyRank n p|
        = ((n : ℝ) ^ 2 * h) * ∑ p ∈ P, |L * fareyValue p - fareyRank n p| := by
          rw [hhn, one_mul]
      _ = (n : ℝ) ^ 2 * (h * ∑ p ∈ P, |L * fareyValue p - fareyRank n p|) := by ring
      _ ≤ (n : ℝ) ^ 2 * (A + h * (L * (L * h + 1 / 2))) := h2
      _ = (n : ℝ) ^ 2 * A + ((n : ℝ) ^ 2 * h) * (L * (L * h + 1 / 2)) := by ring
      _ = (n : ℝ) ^ 2 * A + L * (L * h + 1 / 2) := by rw [hhn, one_mul]
  have hLh : L * h ≤ 1 := by
    rw [hh, mul_one_div, div_le_one (by positivity)]
    exact hLle
  rw [hsplit, ← sum_div]
  calc (∑ p ∈ P, |L * fareyValue p - fareyRank n p|) / L
      ≤ ((n : ℝ) ^ 2 * A + L * (L * h + 1 / 2)) / L :=
        div_le_div_of_nonneg_right hDsum hLpos.le
    _ = (n : ℝ) ^ 2 / L * A + L * h + 1 / 2 := by field_simp; ring
    _ ≤ (n : ℝ) ^ 2 / L * A + 3 / 2 := by linarith

/-- **The discrepancy under a Mertens bound.**  If `|M(n/k)| k^a ≤ B n^a` for `1 ≤ k ≤ n` with
`a ≥ ½` and `n ≥ 256`, then `Σ_ν |f_ν - ν/L| ≤ 16 (B²/24 + ½) n^a (1 + log n)² + 3/2`. -/
theorem fareyL1Discrepancy_le_of_mertens_bound {B a : ℝ} (hB : 0 ≤ B) (ha : 1 / 2 ≤ a)
    {n : ℕ} (hn : 256 ≤ n)
    (hM : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      |(mertensIoc (n / k) : ℝ)| * (k : ℝ) ^ a ≤ B * (n : ℝ) ^ a) :
    fareyL1Discrepancy n
      ≤ 16 * (B ^ 2 / 24 + 1 / 2) * ((n : ℝ) ^ a * (1 + Real.log n) ^ 2) + 3 / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hna : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  set T : ℝ := (n : ℝ) ^ a * (1 + Real.log n) ^ 2 with hT
  have hT0 : 0 < T := by positivity
  have htr := fareyL1Discrepancy_le_meanSquare hn1 hT0
  have hQ := integral_sq_fareySawtooth_le hB ha n hM
  have hL16 := card_fareySet_ge hn
  have hLpos : 0 < ((fareySet n).card : ℝ) := lt_of_lt_of_le (by positivity) hL16
  have hratio : (n : ℝ) ^ 2 / (fareySet n).card ≤ 16 := by
    rw [div_le_iff₀ hLpos]; linarith
  have hQ0 : 0 ≤ ∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun x _ => sq_nonneg _
  have hA : (∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2
      ≤ (B ^ 2 / 24 + 1 / 2) * T := by
    have h1 : (∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T)
        ≤ B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3 / (2 * T) :=
      div_le_div_of_nonneg_right hQ (by positivity)
    have h2 : B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3 / (2 * T)
        ≤ B ^ 2 / 24 * T := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : (1 + Real.log n) ^ 3 ≤ (1 + Real.log n) ^ 4 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      calc B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 3
          ≤ B ^ 2 / 12 * ((n : ℝ) ^ a) ^ 2 * (1 + Real.log n) ^ 4 :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = B ^ 2 / 24 * T * (2 * T) := by rw [hT]; ring
    linarith
  have hAnn : 0 ≤ (∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2 := by
    positivity
  calc fareyL1Discrepancy n
      ≤ (n : ℝ) ^ 2 / ((fareySet n).card : ℝ)
          * ((∫ x in (0 : ℝ)..1, fareySawtooth n x ^ 2) / (2 * T) + T / 2) + 3 / 2 := htr
    _ ≤ 16 * ((B ^ 2 / 24 + 1 / 2) * T) + 3 / 2 := by
        gcongr
    _ = 16 * (B ^ 2 / 24 + 1 / 2) * T + 3 / 2 := by ring

/-- **Farey discrepancy from a Mertens power bound.**  If `|M(N)| ≤ C (N+1)^a` for all `N` with
`½ ≤ a ≤ 1`, then `Σ_ν |f_ν - ν/L| = O(n^{a+δ})` for every `δ > 0`. -/
theorem fareyL1Discrepancy_le_of_mertens_rpow_bound {a C : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (hC0 : 0 ≤ C) (hC : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ, fareyL1Discrepancy n ≤ C' * ((n : ℝ) + 1) ^ (a + δ) := by
  set B : ℝ := 2 * C with hB
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := (1 + 2 / δ) ^ 2 with hK
  set C₁ : ℝ := 16 * (B ^ 2 / 24 + 1 / 2) * K + 3 / 2 with hC₁
  refine ⟨max C₁ 65536, le_trans (by norm_num) (le_max_right _ _), fun n => ?_⟩
  set e : ℝ := a + δ with he
  have hn1R : (0 : ℝ) ≤ n := n.cast_nonneg
  have hpow1 : 1 ≤ ((n : ℝ) + 1) ^ e := Real.one_le_rpow (by linarith) (by linarith)
  rcases lt_or_ge n 256 with hn | hn
  · have h1 := fareyL1Discrepancy_le_card n
    have h2 : ((fareySet n).card : ℝ) ≤ 65536 := by
      have h3 : (fareySet n).card ≤ 65536 :=
        le_trans (card_fareySet_le n) (by
          have : n ^ 2 ≤ 256 ^ 2 := Nat.pow_le_pow_left hn.le 2
          simpa using this)
      exact_mod_cast h3
    calc fareyL1Discrepancy n ≤ 65536 := h1.trans h2
      _ ≤ 65536 * ((n : ℝ) + 1) ^ e := by nlinarith
      _ ≤ max C₁ 65536 * ((n : ℝ) + 1) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hmain := fareyL1Discrepancy_le_of_mertens_bound hB0 ha hn
      (fun k hk hkn => abs_mertensIoc_div_mul_rpow_le_of_bound (by linarith) ha1 hC hk hkn)
    have hn256 : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hlogle : 1 + Real.log n ≤ (1 + 2 / δ) * (n : ℝ) ^ (δ / 2) := by
      have h1 := Real.log_le_rpow_div (x := n) hn0.le (by positivity : 0 < δ / 2)
      have h2 : 1 ≤ (n : ℝ) ^ (δ / 2) := Real.one_le_rpow hn1 (by positivity)
      have e1 : (n : ℝ) ^ (δ / 2) / (δ / 2) = 2 / δ * (n : ℝ) ^ (δ / 2) := by
        field_simp
      rw [e1] at h1
      nlinarith
    have hsq : (1 + Real.log n) ^ 2 ≤ K * (n : ℝ) ^ δ := by
      have h0 : 0 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
      have h3 : ((n : ℝ) ^ (δ / 2)) ^ 2 = (n : ℝ) ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        push_cast
        ring
      calc (1 + Real.log n) ^ 2 ≤ ((1 + 2 / δ) * (n : ℝ) ^ (δ / 2)) ^ 2 :=
            pow_le_pow_left₀ h0 hlogle 2
        _ = K * (n : ℝ) ^ δ := by rw [mul_pow, h3]
    have hTb : (n : ℝ) ^ a * (1 + Real.log n) ^ 2 ≤ K * ((n : ℝ) + 1) ^ e := by
      calc (n : ℝ) ^ a * (1 + Real.log n) ^ 2 ≤ (n : ℝ) ^ a * (K * (n : ℝ) ^ δ) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = K * (n : ℝ) ^ (a + δ) := by rw [Real.rpow_add hn0 a δ]; ring
        _ ≤ K * ((n : ℝ) + 1) ^ e :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le (by linarith) (by linarith))
              (by positivity)
    calc fareyL1Discrepancy n
        ≤ 16 * (B ^ 2 / 24 + 1 / 2) * ((n : ℝ) ^ a * (1 + Real.log n) ^ 2) + 3 / 2 := hmain
      _ ≤ 16 * (B ^ 2 / 24 + 1 / 2) * (K * ((n : ℝ) + 1) ^ e) + 3 / 2 * ((n : ℝ) + 1) ^ e := by
          have h16 : 0 ≤ 16 * (B ^ 2 / 24 + 1 / 2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hTb h16]
      _ = C₁ * ((n : ℝ) + 1) ^ e := by rw [hC₁]; ring
      _ ≤ max C₁ 65536 * ((n : ℝ) + 1) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Franel's theorem.**  Under the Riemann hypothesis, `Σ_ν |f_ν - ν/L| = O(n^{1/2+δ})` for every
`δ > 0`. -/
theorem fareyL1Discrepancy_bound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  intro δ hδ
  set δ₀ : ℝ := min δ 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min hδ one_pos
  have hδ₀1 : δ₀ ≤ 1 := min_le_right δ 1
  have hδ₀δ : δ₀ ≤ δ := min_le_left δ 1
  obtain ⟨C, hC0, hC⟩ :=
    riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH (δ₀ / 2) (by positivity)
  obtain ⟨C', hC'0, hC'⟩ := fareyL1Discrepancy_le_of_mertens_rpow_bound (a := 1 / 2 + δ₀ / 2)
    (by linarith) (by linarith) hC0 hC (δ := δ₀ / 2) (by positivity)
  refine ⟨C', hC'0, fun n => (hC' n).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)) hC'0
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **The Franel–Landau criterion.**  The Riemann hypothesis holds if and only if the Farey
discrepancy satisfies `Σ_ν |f_ν - ν/L| = O(n^{1/2+δ})` for every `δ > 0`. -/
theorem riemannHypothesis_iff_fareyL1Discrepancy_le :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      fareyL1Discrepancy n ≤ C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
  ⟨fareyL1Discrepancy_bound_of_riemannHypothesis, riemannHypothesis_of_fareyL1Discrepancy_le⟩

end

end RHTower
