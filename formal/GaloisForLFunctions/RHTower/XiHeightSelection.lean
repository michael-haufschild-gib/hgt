import GaloisForLFunctions.RHTower.XiSegmentEstimate

/-!
# Choosing a good height

The one-zero contribution `log(1 + 9/(T−γ)²)` to the movement of `log‖xi‖` is `O(1/(T−γ)²)` for a
far zero, but for a zero within unit distance it is as large as `2log(1/|T−γ|)`.  A *minimal-gap*
choice of `T` — one with `|T−γ| ≫ 1/log T` for every `γ` — therefore only gives
`O(log T·log log T)`, which is not a fixed power.  Averaging is what gives a fixed power: the mean of
`∫_n^{n+1} log(1+9/(T−γ)²)dT` is bounded *uniformly in `γ`*, and only `O(log n)` zeros can be near
the segment, so some height in `[n, n+1]` has the whole near-sum `O(log n)`.

## Main results

* `logKernel_le_majorant`, `intervalIntegrable_logKernel`
* `integral_logKernel_le` — the uniform mean bound
-/

open MeasureTheory intervalIntegral Set Filter Topology

namespace RHTower

noncomputable section

/-- A global majorant for the one-zero kernel. -/
theorem logKernel_le_majorant (v : ℝ) :
    Real.log (1 + 9 / v ^ 2) ≤ Real.log 45 + 2 * |Real.log v| + 1 := by
  have hlog45 : (0 : ℝ) ≤ Real.log 45 := Real.log_nonneg (by norm_num)
  rcases eq_or_ne v 0 with rfl | hv
  · norm_num
    linarith
  have hv2 : (0 : ℝ) < v ^ 2 := by positivity
  rcases le_or_gt (|v|) 6 with hle | hgt
  · have hsq : v ^ 2 ≤ 36 := by
      have := sq_abs v
      nlinarith [abs_nonneg v]
    have hsplit : Real.log (1 + 9 / v ^ 2) = Real.log (v ^ 2 + 9) - Real.log (v ^ 2) := by
      rw [← Real.log_div (by positivity) hv2.ne']
      congr 1
      field_simp
    have h1 : Real.log (v ^ 2 + 9) ≤ Real.log 45 :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (v ^ 2) = 2 * Real.log |v| := by
      rw [← sq_abs v, Real.log_pow]
      push_cast
      ring
    have h3 : -(2 * Real.log |v|) ≤ 2 * |Real.log v| := by
      rw [Real.log_abs]
      have := neg_abs_le (Real.log v)
      linarith [le_abs_self (Real.log v)]
    rw [hsplit, h2]
    linarith
  · have hsq : (36 : ℝ) < v ^ 2 := by
      have := sq_abs v
      nlinarith [abs_nonneg v]
    have hsmall : 9 / v ^ 2 ≤ 1 := by
      rw [div_le_one hv2]
      linarith
    have hpos : (0 : ℝ) < 1 + 9 / v ^ 2 := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    have habs : (0 : ℝ) ≤ |Real.log v| := abs_nonneg _
    linarith

theorem measurable_logKernel (γ : ℝ) :
    Measurable fun T : ℝ => Real.log (1 + 9 / (T - γ) ^ 2) := by
  fun_prop

theorem intervalIntegrable_logKernel (γ a b : ℝ) :
    IntervalIntegrable (fun T : ℝ => Real.log (1 + 9 / (T - γ) ^ 2)) volume a b := by
  have hmaj : IntervalIntegrable
      (fun T : ℝ => Real.log 45 + 2 * |Real.log (T - γ)| + 1) volume a b := by
    have h1 : IntervalIntegrable (fun T : ℝ => Real.log (T - γ)) volume a b := by
      have h := (intervalIntegrable_log' (a := a - γ) (b := b - γ)).comp_sub_right γ
      simpa using h
    exact ((intervalIntegrable_const).add ((h1.abs).const_mul 2)).add intervalIntegrable_const
  refine hmaj.mono_fun ((measurable_logKernel γ).aestronglyMeasurable) ?_
  filter_upwards with T
  have h0 : 0 ≤ Real.log (1 + 9 / (T - γ) ^ 2) := log_kernel_nonneg T γ |>.trans_eq (by ring_nf)
  have hmajnn : 0 ≤ Real.log 45 + 2 * |Real.log (T - γ)| + 1 := by
    have : (0 : ℝ) ≤ Real.log 45 := Real.log_nonneg (by norm_num)
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg hmajnn]
  exact logKernel_le_majorant (T - γ)

/-- The uniform mean bound: over a unit segment the one-zero kernel integrates to at most a
constant, no matter where the zero sits. -/
theorem integral_logKernel_le (γ : ℝ) {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 1)
    (h1 : -6 ≤ a - γ) (h2 : b - γ ≤ 6) :
    (∫ T in a..b, Real.log (1 + 9 / (T - γ) ^ 2))
      ≤ Real.log 45 + 1 + 2 * ∫ v in (-6 : ℝ)..6, |Real.log v| := by
  have hL : (∫ T in a..b, Real.log (1 + 9 / (T - γ) ^ 2))
      ≤ ∫ T in a..b, (Real.log 45 + 2 * |Real.log (T - γ)| + 1) := by
    refine intervalIntegral.integral_mono_on hab (intervalIntegrable_logKernel γ a b) ?_ ?_
    · have h1' : IntervalIntegrable (fun T : ℝ => Real.log (T - γ)) volume a b := by
        have h := (intervalIntegrable_log' (a := a - γ) (b := b - γ)).comp_sub_right γ
        simpa using h
      exact ((intervalIntegrable_const).add ((h1'.abs).const_mul 2)).add intervalIntegrable_const
    · intro T _
      exact logKernel_le_majorant (T - γ)
  refine hL.trans ?_
  have hconst : (∫ T in a..b, (Real.log 45 + 2 * |Real.log (T - γ)| + 1))
      = (Real.log 45 + 1) * (b - a) + 2 * ∫ T in a..b, |Real.log (T - γ)| := by
    have h1' : IntervalIntegrable (fun T : ℝ => Real.log (T - γ)) volume a b := by
      have h := (intervalIntegrable_log' (a := a - γ) (b := b - γ)).comp_sub_right γ
      simpa using h
    rw [show (fun T : ℝ => Real.log 45 + 2 * |Real.log (T - γ)| + 1)
        = fun T : ℝ => (Real.log 45 + 1) + 2 * |Real.log (T - γ)| by funext T; ring]
    rw [intervalIntegral.integral_add intervalIntegrable_const ((h1'.abs).const_mul 2),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  rw [hconst]
  have hshift : (∫ T in a..b, |Real.log (T - γ)|) = ∫ v in (a - γ)..(b - γ), |Real.log v| := by
    have := intervalIntegral.integral_comp_sub_right
      (a := a) (b := b) (fun v : ℝ => |Real.log v|) γ
    exact this
  have hmono : (∫ v in (a - γ)..(b - γ), |Real.log v|)
      ≤ ∫ v in (-6 : ℝ)..6, |Real.log v| := by
    refine intervalIntegral.integral_mono_interval h1 (by linarith) h2 ?_
      ((intervalIntegrable_log').abs)
    filter_upwards with v
    exact abs_nonneg _
  have hlog45 : (0 : ℝ) ≤ Real.log 45 := Real.log_nonneg (by norm_num)
  rw [hshift]
  nlinarith [hmono, hlen, hab]

/-! ## The count in a band of arbitrary radius -/

theorem exists_card_band_le {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ r) → (F.card : ℝ) ≤ C * Real.log t := by
  obtain ⟨Cw, hCw0, hCw⟩ := exists_tsum_weighted_density_le
  refine ⟨(1 + r ^ 2) * Cw, by positivity, ?_⟩
  filter_upwards [hCw] with t ht F hF
  obtain ⟨hsum, hbound⟩ := ht
  have hlow : ∀ q ∈ F, (1 : ℝ) / (1 + r ^ 2) ≤ (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ 2) := by
    intro q hq
    have habs : |(q.1 : ℂ).im - t| ≤ r := hF q hq
    have hsq : (t - (q.1 : ℂ).im) ^ 2 ≤ r ^ 2 := by
      have h1 : ((q.1 : ℂ).im - t) ^ 2 = (t - (q.1 : ℂ).im) ^ 2 := by ring
      nlinarith [sq_abs ((q.1 : ℂ).im - t), abs_nonneg ((q.1 : ℂ).im - t)]
    have hd1 : (0 : ℝ) < 1 + (t - (q.1 : ℂ).im) ^ 2 := by positivity
    have hd2 : (0 : ℝ) < 1 + r ^ 2 := by positivity
    rw [div_le_div_iff₀ hd2 hd1]
    linarith
  have hcard : (F.card : ℝ) * ((1 : ℝ) / (1 + r ^ 2))
      ≤ ∑ q ∈ F, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ 2) := by
    have := Finset.card_nsmul_le_sum F
      (fun q => (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ 2)) ((1 : ℝ) / (1 + r ^ 2)) hlow
    rw [nsmul_eq_mul] at this
    exact this
  have hle : (∑ q ∈ F, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ 2))
      ≤ ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (t - (q.1 : ℂ).im) ^ 2) :=
    hsum.sum_le_tsum F (fun q _ => by positivity)
  have hd2 : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hchain : (F.card : ℝ) * ((1 : ℝ) / (1 + r ^ 2)) ≤ Cw * Real.log t := by
    linarith
  rw [mul_one_div, div_le_iff₀ hd2] at hchain
  nlinarith [hchain]

/-! ## The measure-theoretic pigeonhole -/

theorem exists_height_le_average {a : ℝ} {g : ℝ → ℝ} {N : Set ℝ}
    (hN : volume N = 0) (hg : IntervalIntegrable g volume a (a + 1)) :
    ∃ T ∈ Ioc a (a + 1), T ∉ N ∧ g T ≤ (∫ T in a..(a + 1), g T) + 1 := by
  by_contra hcon
  push_neg at hcon
  set B : ℝ := (∫ T in a..(a + 1), g T) + 1 with hB
  have hmeas : IntegrableOn g (Ioc a (a + 1)) volume := by
    have := hg.1
    exact this
  have hNc : ∀ᵐ T ∂(volume.restrict (Ioc a (a + 1))), T ∉ N := by
    refine ae_restrict_of_ae ?_
    exact compl_mem_ae_iff.2 hN
  have hae : ∀ᵐ T ∂(volume.restrict (Ioc a (a + 1))), B ≤ g T := by
    filter_upwards [hNc, ae_restrict_mem measurableSet_Ioc] with T hT hmem
    exact le_of_lt (hcon T hmem hT)
  have hconst : IntegrableOn (fun _ : ℝ => B) (Ioc a (a + 1)) volume :=
    (continuous_const : Continuous fun _ : ℝ => B).integrableOn_Ioc
  have hmono := MeasureTheory.setIntegral_mono_ae_restrict hconst hmeas hae
  rw [MeasureTheory.setIntegral_const] at hmono
  have hvol : (volume : Measure ℝ).real (Ioc a (a + 1)) = 1 := by
    rw [Measure.real, Real.volume_Ioc]
    have hlen : (a + 1) - a = 1 := by ring
    rw [hlen, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]
  rw [hvol, one_smul] at hmono
  have hval : (∫ T in Ioc a (a + 1), g T) = ∫ T in a..(a + 1), g T :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  rw [hval, hB] at hmono
  linarith

/-! ## The choice of height -/

/-- **Burnol's choice of heights.**  In every unit interval far enough out there is a height,
avoiding every ordinate of the divisor and its negative, at which the whole one-zero sum is
`O(log n)`. -/
theorem exists_good_height :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℝ, ∀ n : ℝ, n₀ ≤ n → ∃ T : ℝ, n ≤ T ∧ T ≤ n + 1 ∧
      (∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0) ∧
      (∀ q : XiZeroCopy, T + (q.1 : ℂ).im ≠ 0) ∧
      (∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)) ≤ C * Real.log n := by
  classical
  obtain ⟨Ccnt, hCcnt0, hCcnt⟩ := exists_card_band_le (r := 5) (by norm_num)
  obtain ⟨Cw, hCw0, hCw⟩ := exists_tsum_weighted_density_le
  rw [Filter.eventually_atTop] at hCcnt hCw
  obtain ⟨t₁, ht₁⟩ := hCcnt
  obtain ⟨t₂, ht₂⟩ := hCw
  set C₀ : ℝ := Real.log 45 + 1 + 2 * ∫ v in (-6 : ℝ)..6, |Real.log v| with hC₀def
  have hC₀0 : 0 ≤ C₀ := by
    have h1 : (0 : ℝ) ≤ Real.log 45 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ ∫ v in (-6 : ℝ)..6, |Real.log v| := by
      refine intervalIntegral.integral_nonneg (by norm_num) fun v _ => abs_nonneg _
    linarith
  refine ⟨Ccnt * C₀ + 1 + 36 * Cw + 1, by positivity, max (max t₁ t₂) 10, ?_⟩
  intro n hn
  have hn10 : (10 : ℝ) ≤ n := le_trans (le_max_right _ _) hn
  have hnt₁ : t₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnt₂ : t₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hlogn : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  -- the near set
  set S : Finset XiZeroCopy :=
    (finite_xiZeroCopy_band n (by norm_num : (0 : ℝ) ≤ 5)).toFinset with hSdef
  have hSmem : ∀ q : XiZeroCopy, q ∈ S ↔ |(q.1 : ℂ).im - n| ≤ 5 := by
    intro q
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl
  have hcard : (S.card : ℝ) ≤ Ccnt * Real.log n :=
    ht₁ n hnt₁ S fun q hq => (hSmem q).1 hq
  -- the null set of bad heights
  set N : Set ℝ := (⋃ q : XiZeroCopy, {(q.1 : ℂ).im}) ∪ (⋃ q : XiZeroCopy, {-(q.1 : ℂ).im})
    with hNdef
  have hNnull : volume N = 0 := by
    refine measure_union_null ?_ ?_
    · exact (Set.countable_iUnion fun q => Set.countable_singleton _).measure_zero _
    · exact (Set.countable_iUnion fun q => Set.countable_singleton _).measure_zero _
  -- the near sum and its average
  set g : ℝ → ℝ := fun T => ∑ q ∈ S, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) with hgdef
  have hgint : IntervalIntegrable g volume n (n + 1) := by
    have heq : (∑ q ∈ S, fun T : ℝ => Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2)) = g := by
      funext u
      rw [hgdef]
      simp [Finset.sum_apply]
    rw [← heq]
    exact IntervalIntegrable.sum S fun q _ => intervalIntegrable_logKernel _ n (n + 1)
  obtain ⟨T, hTmem, hTN, hTle⟩ := exists_height_le_average hNnull hgint
  have hTlow : n ≤ T := le_of_lt hTmem.1
  have hThigh : T ≤ n + 1 := hTmem.2
  have havg : (∫ u in n..(n + 1), g u) ≤ Ccnt * Real.log n * C₀ := by
    have hsum : (∫ u in n..(n + 1), g u)
        = ∑ q ∈ S, ∫ u in n..(n + 1), Real.log (1 + 9 / (u - (q.1 : ℂ).im) ^ 2) :=
      intervalIntegral.integral_finsetSum (fun q _ => intervalIntegrable_logKernel _ n (n + 1))
    rw [hsum]
    have hterm : ∀ q ∈ S,
        (∫ u in n..(n + 1), Real.log (1 + 9 / (u - (q.1 : ℂ).im) ^ 2)) ≤ C₀ := by
      intro q hq
      have hband : |(q.1 : ℂ).im - n| ≤ 5 := (hSmem q).1 hq
      obtain ⟨hlo, hhi⟩ := abs_le.1 hband
      exact integral_logKernel_le _ (by linarith) (by linarith) (by linarith) (by linarith)
    calc (∑ q ∈ S, ∫ u in n..(n + 1), Real.log (1 + 9 / (u - (q.1 : ℂ).im) ^ 2))
        ≤ ∑ _q ∈ S, C₀ := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * C₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Ccnt * Real.log n * C₀ := by
          exact mul_le_mul_of_nonneg_right hcard hC₀0
  -- the height avoids every ordinate
  have hT1 : ∀ q : XiZeroCopy, T - (q.1 : ℂ).im ≠ 0 := by
    intro q hq
    refine hTN (Or.inl ?_)
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    simp only [Set.mem_singleton_iff]
    linarith [sub_eq_zero.1 hq]
  have hT2 : ∀ q : XiZeroCopy, T + (q.1 : ℂ).im ≠ 0 := by
    intro q hq
    refine hTN (Or.inr ?_)
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    simp only [Set.mem_singleton_iff]
    linarith [eq_neg_of_add_eq_zero_left hq]
  refine ⟨T, hTlow, hThigh, hT1, hT2, ?_⟩
  -- split the sum
  have hsummable := summable_logKernel T
  have hsplit := hsummable.sum_add_tsum_compl (s := S)
  have hwsum := ht₂ T (le_trans hnt₂ hTlow)
  obtain ⟨hwS, hwB⟩ := hwsum
  have hfar : (∑' q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ},
      Real.log (1 + 9 / (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)) ≤ 18 * (Cw * Real.log T) := by
    have hcomp : ∀ q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ},
        Real.log (1 + 9 / (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)
          ≤ 18 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)) := by
      rintro ⟨q, hq⟩
      have hnot : ¬ (|(q.1 : ℂ).im - n| ≤ 5) := by
        intro hle
        exact hq ((hSmem q).2 hle)
      have habs : 5 < |(q.1 : ℂ).im - n| := lt_of_not_ge hnot
      have hfar4 : 16 ≤ (T - (q.1 : ℂ).im) ^ 2 := by
        have hTn : |T - n| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        have hstep : |(q.1 : ℂ).im - n| - |T - n| ≤ |((q.1 : ℂ).im - n) - (T - n)| :=
          abs_sub_abs_le_abs_sub _ _
        have hsimp : ((q.1 : ℂ).im - n) - (T - n) = (q.1 : ℂ).im - T := by ring
        rw [hsimp] at hstep
        have h4 : 4 < |(q.1 : ℂ).im - T| := by linarith
        rw [abs_sub_comm] at h4
        nlinarith [sq_abs (T - (q.1 : ℂ).im), abs_nonneg (T - (q.1 : ℂ).im)]
      have hpos : (0 : ℝ) < (T - (q.1 : ℂ).im) ^ 2 := by linarith
      have hlog : Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2) ≤ 9 / (T - (q.1 : ℂ).im) ^ 2 := by
        have hp : (0 : ℝ) < 1 + 9 / (T - (q.1 : ℂ).im) ^ 2 := by positivity
        have := Real.log_le_sub_one_of_pos hp
        linarith
      have hcmp : 9 / (T - (q.1 : ℂ).im) ^ 2
          ≤ 18 * ((1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ hpos (by positivity)]
        nlinarith
      linarith
    have hsub1 : Summable (fun q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ} =>
        Real.log (1 + 9 / (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)) := hsummable.subtype _
    have hsub2 : Summable (fun q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ} =>
        18 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2))) :=
      (hwS.mul_left 18).subtype _
    refine le_trans (hsub1.tsum_le_tsum hcomp hsub2) ?_
    have hwsplit := (hwS.mul_left 18).sum_add_tsum_compl (s := S)
    have hnn : (0 : ℝ) ≤ ∑ q ∈ S, 18 * ((1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2)) :=
      Finset.sum_nonneg fun q _ => by positivity
    have htot : (∑' q : XiZeroCopy, 18 * ((1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2)))
        = 18 * ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2) := hwS.tsum_mul_left 18
    have : (∑' q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ},
        18 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)))
        ≤ 18 * ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2) := by
      rw [← htot, ← hwsplit]
      linarith
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left hwB (by norm_num)
  -- the near sum at the chosen height
  have hnear : g T ≤ Ccnt * Real.log n * C₀ + 1 := le_trans hTle (by linarith)
  have hlogT : Real.log T ≤ 2 * Real.log n := by
    have h1 : Real.log T ≤ Real.log (n + 1) := Real.log_le_log (by linarith) hThigh
    have h2 : Real.log (n + 1) ≤ Real.log (n * n) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith
    have h3 : Real.log (n * n) = 2 * Real.log n := by
      rw [Real.log_mul (by linarith) (by linarith)]
      ring
    linarith
  have hfinal : (∑' q : XiZeroCopy, Real.log (1 + 9 / (T - (q.1 : ℂ).im) ^ 2))
      = g T + ∑' q : {q : XiZeroCopy // q ∈ (↑S : Set XiZeroCopy)ᶜ},
          Real.log (1 + 9 / (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2) := by
    rw [hgdef]
    exact hsplit.symm
  rw [hfinal]
  have hCw18 : 18 * (Cw * Real.log T) ≤ 36 * Cw * Real.log n := by
    nlinarith [hCw0, Real.log_nonneg (by linarith : (1:ℝ) ≤ n)]
  nlinarith [hnear, hfar, hCw18, hlogn, hC₀0, hCcnt0]

end

end RHTower

