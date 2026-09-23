import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationCharacteristic
import GaloisForLFunctions.HTGeometry.SecondMainTheoremChain
import GaloisForLFunctions.HTGeometry.LogDerivativeProximity

open Complex Metric Real Set Topology Filter ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeromorphicOn

theorem smallGrowth_circleAverage_posLog_inv_sub_le_all (a : ℂ) {r : ℝ} (hr : 1 ≤ r) :
    Real.circleAverage (fun z => Real.posLog ‖z - a‖⁻¹) 0 r ≤ Real.log 2 := by
  by_cases ha : a ∈ closedBall (0 : ℂ) r
  · exact circleAverage_posLog_inv_sub_le hr ha
  · have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have har : r < ‖a‖ := by
      rw [mem_closedBall_iff_norm, sub_zero, not_le] at ha
      exact ha
    have ha0 : 0 < ‖a‖ := hr0.trans har
    have hmero : MeromorphicOn (fun z : ℂ => z - a) (sphere (0 : ℂ) |r|) :=
      (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn
    have hint₁ : CircleIntegrable (fun z => Real.posLog ‖z - a‖) 0 r :=
      hmero.circleIntegrable_posLog_norm
    have hint₂ : CircleIntegrable (fun z => Real.log ‖z - a‖) 0 r :=
      hmero.circleIntegrable_log_norm
    have hfun : (fun z : ℂ => Real.posLog ‖z - a‖⁻¹) =
        (fun z : ℂ => Real.posLog ‖z - a‖) - fun z : ℂ => Real.log ‖z - a‖ := by
      funext z
      rw [Pi.sub_apply, posLog_inv_eq_negPart, Real.posLog, posPart_neg]
    rw [hfun, Real.circleAverage_sub hint₁ hint₂]
    have hlogavg :
        Real.circleAverage (fun z => Real.log ‖z - a‖) 0 r = Real.log ‖a‖ := by
      have hanalytic : AnalyticOnNhd ℂ (fun z : ℂ => z - a)
          (closedBall (0 : ℂ) |r|) := analyticOnNhd_id.sub analyticOnNhd_const
      have hfree : ∀ z ∈ closedBall (0 : ℂ) |r|, z - a ≠ 0 := by
        intro z hz hza
        apply ha
        have hza' : z = a := sub_eq_zero.mp hza
        simpa [abs_of_pos hr0, hza'] using hz
      have hmean := hanalytic.circleAverage_log_norm_of_ne_zero hfree
      simpa using hmean
    have hlog2a : 0 ≤ Real.log (2 * ‖a‖) :=
      Real.log_nonneg (by nlinarith [ha0])
    have hposavg :
        Real.circleAverage (fun z => Real.posLog ‖z - a‖) 0 r ≤
          Real.log (2 * ‖a‖) := by
      refine Real.circleAverage_mono_on_of_le_circle hint₁ ?_
      intro z hz
      have hzr : ‖z‖ = r := by
        simpa [mem_sphere_iff_norm, abs_of_pos hr0] using hz
      have hdist : ‖z - a‖ ≤ 2 * ‖a‖ := by
        calc
          ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le z a
          _ ≤ 2 * ‖a‖ := by rw [hzr]; linarith
      have hlogle : Real.log ‖z - a‖ ≤ Real.log (2 * ‖a‖) := by
        rcases eq_or_lt_of_le (norm_nonneg (z - a)) with hzero | hpos
        · rw [← hzero, Real.log_zero]
          exact hlog2a
        · exact Real.log_le_log hpos hdist
      rw [Real.posLog]
      exact max_le hlog2a hlogle
    have hsplit : Real.log (2 * ‖a‖) = Real.log 2 + Real.log ‖a‖ :=
      Real.log_mul two_ne_zero (ne_of_gt ha0)
    rw [hlogavg]
    linarith

theorem smallGrowth_norm_reflectedKernel_le_two {u w : ℂ} {R r : ℝ}
    (hr : 1 ≤ r) (hR : 2 * r ≤ R) (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ r) :
    ‖(starRingEnd ℂ) u / ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ ≤ 2 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hR0 : 0 ≤ R := le_trans (mul_nonneg (by norm_num) hr0) hR
  have hprod : ‖(starRingEnd ℂ) u * w‖ ≤ R * r := by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul hu hw (norm_nonneg w) hR0
  have hden : R ^ (2 : ℕ) - R * r ≤
      ‖((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ := by
    calc
      R ^ (2 : ℕ) - R * r ≤ ‖((R : ℂ) ^ (2 : ℕ))‖ - ‖(starRingEnd ℂ) u * w‖ := by
        rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR0]
        linarith
      _ ≤ ‖((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ :=
        norm_sub_norm_le _ _
  have hRr : R * r ≤ R ^ (2 : ℕ) / 2 := by
    nlinarith
  have hRpos : 0 < R := by nlinarith
  have hdenpos : 0 < ‖((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ := by
    have : 0 < R ^ (2 : ℕ) - R * r := by
      nlinarith
    exact this.trans_le hden
  rw [norm_div, RCLike.norm_conj, div_le_iff₀ hdenpos]
  calc
    ‖u‖ ≤ R := hu
    _ ≤ 2 * (R ^ (2 : ℕ) - R * r) := by
      have hRone : 1 ≤ R := by nlinarith
      nlinarith
    _ ≤ 2 * ‖((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ := by gcongr

private theorem smallGrowth_posLog_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.posLog x ≤ x := by
  rw [Real.posLog]
  exact max_le hx (Real.log_le_self hx)

theorem smallGrowth_circleAverage_posLog_divisorKernel_le
    (D : ℂ → ℤ) (T : Finset ℂ) {R r : ℝ}
    (hr : 1 ≤ r) (hR : 2 * r ≤ R)
    (hTmem : ∀ u ∈ T, ‖u‖ ≤ R) (hTne : ∀ u ∈ T, D u ≠ 0) :
    Real.circleAverage
        (fun w => Real.posLog ‖∑ u ∈ T, (D u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) u /
            ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))‖) 0 r ≤
      5 * ∑ u ∈ T, |(D u : ℝ)| := by
  classical
  let K : ℂ → ℂ → ℂ := fun u w =>
    1 / (w - u) + (starRingEnd ℂ) u /
      ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)
  have hmeroK : ∀ u : ℂ, Meromorphic (K u) := by
    intro u z
    apply MeromorphicAt.add
    · exact analyticAt_const.meromorphicAt.div
        (analyticAt_id.sub analyticAt_const).meromorphicAt
    · exact analyticAt_const.meromorphicAt.div
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).meromorphicAt
  have hmeroSum : Meromorphic (fun w => ∑ u ∈ T, (D u : ℂ) * K u w) := by
    intro z
    clear hTmem hTne
    induction T using Finset.induction with
    | empty => simp
    | @insert u S hu ih =>
        have hsplit : (fun w : ℂ => ∑ v ∈ insert u S, (D v : ℂ) * K v w) =
            (fun w => (D u : ℂ) * K u w) +
              fun w => ∑ v ∈ S, (D v : ℂ) * K v w := by
          funext w
          rw [Finset.sum_insert hu]
          rfl
        rw [hsplit]
        exact (analyticAt_const.meromorphicAt.mul (hmeroK u z)).add ih
  have hleftInt : CircleIntegrable
      (fun w => Real.posLog ‖∑ u ∈ T, (D u : ℂ) * K u w‖) 0 r :=
    (show MeromorphicOn (fun w => ∑ u ∈ T, (D u : ℂ) * K u w)
        (sphere (0 : ℂ) |r|) from fun z _ => hmeroSum z).circleIntegrable_posLog_norm
  have hinvInt : ∀ u ∈ T,
      CircleIntegrable (fun w => Real.posLog ‖w - u‖⁻¹) 0 r := by
    intro u _
    exact circleIntegrable_posLog_inv_sub u r
  let C : ℝ := (T.card : ℝ) + ∑ u ∈ T, (|(D u : ℝ)| + 3 * Real.log 2)
  have hrightInt : CircleIntegrable
      (fun w => (T.card : ℝ) +
        ∑ u ∈ T, (|(D u : ℝ)| + 2 * Real.log 2 +
          Real.posLog ‖w - u‖⁻¹)) 0 r := by
    have hconst : CircleIntegrable (fun _ : ℂ => (T.card : ℝ)) 0 r :=
      ContinuousOn.circleIntegrable' continuousOn_const
    apply hconst.add
    apply CircleIntegrable.fun_sum T
    intro u hu
    have hc : CircleIntegrable
        (fun _ : ℂ => |(D u : ℝ)| + 2 * Real.log 2) 0 r :=
      ContinuousOn.circleIntegrable' continuousOn_const
    exact hc.add (hinvInt u hu)
  have hpoint : ∀ w ∈ sphere (0 : ℂ) |r|,
      Real.posLog ‖∑ u ∈ T, (D u : ℂ) * K u w‖ ≤
        (T.card : ℝ) + ∑ u ∈ T, (|(D u : ℝ)| + 2 * Real.log 2 +
          Real.posLog ‖w - u‖⁻¹) := by
    intro w hw
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hwnorm : ‖w‖ ≤ r := by
      have : ‖w‖ = r := by simpa [mem_sphere_iff_norm, abs_of_pos hr0] using hw
      linarith
    have hnormK : ∀ u ∈ T, ‖K u w‖ ≤ ‖w - u‖⁻¹ + 2 := by
      intro u hu
      dsimp [K]
      calc
        ‖1 / (w - u) + (starRingEnd ℂ) u /
            ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ ≤
            ‖1 / (w - u)‖ +
              ‖(starRingEnd ℂ) u /
                ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w)‖ := norm_add_le _ _
        _ ≤ ‖w - u‖⁻¹ + 2 := by
          rw [norm_div, norm_one, one_div]
          gcongr
          exact smallGrowth_norm_reflectedKernel_le_two hr hR (hTmem u hu) hwnorm
    have hnormSum : ‖∑ u ∈ T, (D u : ℂ) * K u w‖ ≤
        ∑ u ∈ T, |(D u : ℝ)| * (‖w - u‖⁻¹ + 2) := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, Complex.norm_intCast]
      exact mul_le_mul_of_nonneg_left (hnormK u hu) (abs_nonneg _)
    calc
      Real.posLog ‖∑ u ∈ T, (D u : ℂ) * K u w‖ ≤
          Real.posLog (∑ u ∈ T, |(D u : ℝ)| * (‖w - u‖⁻¹ + 2)) :=
        Real.posLog_le_posLog (norm_nonneg _) hnormSum
      _ ≤ Real.log (T.card : ℝ) +
          ∑ u ∈ T, Real.posLog (|(D u : ℝ)| * (‖w - u‖⁻¹ + 2)) :=
        Real.posLog_sum T _
      _ ≤ (T.card : ℝ) +
          ∑ u ∈ T, (|(D u : ℝ)| + 2 * Real.log 2 +
            Real.posLog ‖w - u‖⁻¹) := by
        have hcard : Real.log (T.card : ℝ) ≤ (T.card : ℝ) :=
          Real.log_le_self (Nat.cast_nonneg _)
        gcongr with u hu
        calc
          Real.posLog (|(D u : ℝ)| * (‖w - u‖⁻¹ + 2)) ≤
              Real.posLog |(D u : ℝ)| + Real.posLog (‖w - u‖⁻¹ + 2) :=
            Real.posLog_mul
          _ ≤ |(D u : ℝ)| + 2 * Real.log 2 + Real.posLog ‖w - u‖⁻¹ := by
            have habs := smallGrowth_posLog_le_self_of_nonneg (abs_nonneg (D u : ℝ))
            have hadd := Real.posLog_add (x := ‖w - u‖⁻¹) (y := 2)
            have htwo : Real.posLog (2 : ℝ) = Real.log 2 := by
              rw [Real.posLog, max_eq_right (Real.log_nonneg (by norm_num))]
            rw [htwo] at hadd
            linarith
  have havg := Real.circleAverage_mono hleftInt hrightInt hpoint
  have hrightAvg : Real.circleAverage
      (fun w => (T.card : ℝ) +
        ∑ u ∈ T, (|(D u : ℝ)| + 2 * Real.log 2 +
          Real.posLog ‖w - u‖⁻¹)) 0 r ≤
      (T.card : ℝ) + ∑ u ∈ T, (|(D u : ℝ)| + 3 * Real.log 2) := by
    have hconst : CircleIntegrable (fun _ : ℂ => (T.card : ℝ)) 0 r :=
      ContinuousOn.circleIntegrable' continuousOn_const
    have htermInt : ∀ u ∈ T, CircleIntegrable
        (fun w => |(D u : ℝ)| + 2 * Real.log 2 +
          Real.posLog ‖w - u‖⁻¹) 0 r := by
      intro u hu
      exact (ContinuousOn.circleIntegrable' continuousOn_const).add (hinvInt u hu)
    rw [show (fun w => (T.card : ℝ) + ∑ u ∈ T,
        (|(D u : ℝ)| + 2 * Real.log 2 + Real.posLog ‖w - u‖⁻¹)) =
        (fun _ : ℂ => (T.card : ℝ)) + fun w => ∑ u ∈ T,
          (|(D u : ℝ)| + 2 * Real.log 2 + Real.posLog ‖w - u‖⁻¹) from rfl,
      Real.circleAverage_add hconst (CircleIntegrable.fun_sum T htermInt),
      Real.circleAverage_const, Real.circleAverage_fun_sum htermInt]
    gcongr with u hu
    have hci : CircleIntegrable (fun _ : ℂ => |(D u : ℝ)| + 2 * Real.log 2) 0 r :=
      ContinuousOn.circleIntegrable' continuousOn_const
    rw [show (fun w => |(D u : ℝ)| + 2 * Real.log 2 + Real.posLog ‖w - u‖⁻¹) =
        (fun _ : ℂ => |(D u : ℝ)| + 2 * Real.log 2) +
          fun w => Real.posLog ‖w - u‖⁻¹ from rfl,
      Real.circleAverage_add hci (hinvInt u hu), Real.circleAverage_const]
    linarith [smallGrowth_circleAverage_posLog_inv_sub_le_all u hr]
  have hcardMass : (T.card : ℝ) ≤ ∑ u ∈ T, |(D u : ℝ)| := by
    calc
      (T.card : ℝ) = ∑ _u ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ u ∈ T, |(D u : ℝ)| := by
        gcongr with u hu
        have hne : (D u : ℝ) ≠ 0 := by exact_mod_cast hTne u hu
        have habspos : 0 < |(D u : ℝ)| := abs_pos.mpr hne
        exact_mod_cast (Int.one_le_abs (hTne u hu))
  have hlogtwo : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogterm : (T.card : ℝ) * (3 * Real.log 2) ≤
      3 * ∑ u ∈ T, |(D u : ℝ)| := by
    have hcard0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc
      (T.card : ℝ) * (3 * Real.log 2) ≤ (T.card : ℝ) * 3 := by
        gcongr
        nlinarith
      _ ≤ (∑ u ∈ T, |(D u : ℝ)|) * 3 := by gcongr
      _ = 3 * ∑ u ∈ T, |(D u : ℝ)| := by ring
  calc
    Real.circleAverage
        (fun w => Real.posLog ‖∑ u ∈ T, (D u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) u /
            ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))‖) 0 r =
        Real.circleAverage
          (fun w => Real.posLog ‖∑ u ∈ T, (D u : ℂ) * K u w‖) 0 r := by rfl
    _ ≤ (T.card : ℝ) + ∑ u ∈ T, (|(D u : ℝ)| + 3 * Real.log 2) :=
      havg.trans hrightAvg
    _ ≤ 5 * ∑ u ∈ T, |(D u : ℝ)| := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      nlinarith [hcardMass, hlogterm]

theorem smallGrowth_divisor_inv_apply {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ u, meromorphicOrderAt f u ≠ ⊤) (R : ℝ) (u : ℂ) :
    divisor f⁻¹ (closedBall (0 : ℂ) |R|) u =
      -divisor f (closedBall (0 : ℂ) |R|) u := by
  let B := closedBall (0 : ℂ) |R|
  by_cases hu : u ∈ B
  · have hfinv : MeromorphicOn f⁻¹ B := fun z _ => (hf z).inv
    have hforder : meromorphicOrderAt f⁻¹ u ≠ ⊤ := by
      rw [meromorphicOrderAt_inv]
      simpa using horder u
    rw [divisor_apply hfinv hu, divisor_apply (fun z _ => hf z) hu,
      meromorphicOrderAt_inv]
    simp
  · have hfzero : divisor f B u = 0 := by
      by_contra hne
      exact hu ((divisor f B).supportWithinDomain (Function.mem_support.mpr hne))
    have hinvzero : divisor f⁻¹ B u = 0 := by
      by_contra hne
      exact hu ((divisor f⁻¹ B).supportWithinDomain (Function.mem_support.mpr hne))
    rw [hfzero, hinvzero, neg_zero]

noncomputable def smallGrowth_divisorSupportFinset (f : ℂ → ℂ) (R : ℝ) : Finset ℂ :=
  ((divisor f (closedBall (0 : ℂ) |R|)).finiteSupport
    (isCompact_closedBall (0 : ℂ) |R|)).toFinset

theorem smallGrowth_sum_abs_divisor_eq_poleMass_add_inv
    {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ u, meromorphicOrderAt f u ≠ ⊤) (R : ℝ) :
    let D := divisor f (closedBall (0 : ℂ) |R|)
    let T := smallGrowth_divisorSupportFinset f R
    ∑ u ∈ T, |(D u : ℝ)| =
      poleMultiplicityMass f R + poleMultiplicityMass f⁻¹ R := by
  classical
  let D := divisor f (closedBall (0 : ℂ) |R|)
  have hDfin : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  let T := smallGrowth_divisorSupportFinset f R
  have hT : T = hDfin.toFinset := by rfl
  have hmass : poleMultiplicityMass f R = ∑ u ∈ T, (D u : ℝ)⁻ := by
    rw [poleMultiplicityMass]
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    rw [hT]
    apply (Set.Finite.mem_toFinset hDfin).2
    apply Function.mem_support.mpr
    intro hDu
    exact hu (by simp [D, hDu])
  have hmassInv : poleMultiplicityMass f⁻¹ R = ∑ u ∈ T, (-D u : ℝ)⁻ := by
    rw [poleMultiplicityMass]
    calc
      (∑ᶠ u : ℂ, ((divisor f⁻¹ (closedBall (0 : ℂ) |R|) u : ℝ))⁻) =
          ∑ᶠ u : ℂ, (-D u : ℝ)⁻ := by
            apply finsum_congr
            intro u
            rw [smallGrowth_divisor_inv_apply hf horder]
            simp [D]
      _ = ∑ u ∈ T, (-D u : ℝ)⁻ := by
        apply finsum_eq_sum_of_support_subset
        intro u hu
        simp only [Function.mem_support] at hu
        rw [hT]
        apply (Set.Finite.mem_toFinset hDfin).2
        apply Function.mem_support.mpr
        intro hDu
        exact hu (by simp [D, hDu])
  rw [hmass, hmassInv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  change |(D u : ℝ)| = (D u : ℝ)⁻ + (-D u : ℝ)⁻
  rcases le_total 0 (D u) with hu | hu
  · simp [negPart, hu]
  · simp [negPart, hu]

private theorem smallGrowth_entire_not_locally_zero {f : entireSubring ℂ} (hf : f ≠ 0) :
    ∀ a : ℂ, ¬ ∀ᶠ z in 𝓝 a, (f : ℂ → ℂ) z = 0 := by
  intro a ha
  apply hf
  apply Subtype.ext
  funext z
  have heq : Set.EqOn (f : ℂ → ℂ) 0 Set.univ :=
    f.2.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ a) ha
  simpa using heq (Set.mem_univ z)

theorem smallGrowth_exists_good_radius {x : EntireField ℂ}
    (p : EntireFractionPresentation x) (hx : x ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    ∃ R : ℝ, 3 * r ≤ R ∧ R ≤ 3 * r + 1 ∧ 2 * r ≤ R ∧ 1 ≤ R ∧
      ∀ z ∈ sphere (0 : ℂ) |R|,
        divisor p.function (closedBall (0 : ℂ) |R|) z = 0 := by
  let q : entireSubring ℂ := p.numerator * p.denominator
  have hqne : q ≠ 0 := mul_ne_zero (p.numerator_ne_zero hx) p.denominator_ne_zero
  obtain ⟨R, hRlow, hRhigh, hqR⟩ :=
    exists_radius_no_boundary_zero q.2 (smallGrowth_entire_not_locally_zero hqne) (3 * r)
  have hRpos : 0 < R := by nlinarith
  refine ⟨R, hRlow, hRhigh, by nlinarith, by nlinarith, ?_⟩
  intro z hz
  have hzR : z ∈ sphere (0 : ℂ) R := by
    simpa [abs_of_pos hRpos] using hz
  have hqz : (q : ℂ → ℂ) z ≠ 0 := hqR z hzR
  have hnum : (p.numerator : ℂ → ℂ) z ≠ 0 := by
    intro hzero
    apply hqz
    simp [q, hzero]
  have hden : (p.denominator : ℂ → ℂ) z ≠ 0 := by
    intro hzero
    apply hqz
    simp [q, hzero]
  have hzball : z ∈ closedBall (0 : ℂ) |R| := sphere_subset_closedBall hz
  have hana : AnalyticAt ℂ p.function z := by
    exact (p.numerator.2 z (Set.mem_univ z)).div
      (p.denominator.2 z (Set.mem_univ z)) hden
  have hord : analyticOrderAt p.function z = 0 :=
    hana.analyticOrderAt_eq_zero.mpr (div_ne_zero hnum hden)
  rw [divisor_apply (fun w _ => p.meromorphic w) hzball,
    hana.meromorphicOrderAt_eq, hord]
  simp

theorem smallGrowth_proximity_logDeriv_le {x : EntireField ℂ}
    (p : EntireFractionPresentation x) (hx : x ≠ 0) {r R : ℝ}
    (hr : 1 ≤ r) (hR : 2 * r ≤ R)
    (hbd : ∀ z ∈ sphere (0 : ℂ) |R|,
      divisor p.function (closedBall (0 : ℂ) |R|) z = 0) :
    proximity (fun z => deriv p.function z / p.function z) ⊤ r ≤
      Real.log 2 + 5 * (poleMultiplicityMass p.function R +
        poleMultiplicityMass p.function⁻¹ R) +
        8 * characteristic p.function ⊤ R +
        4 * max |Real.log ‖p.function 0‖|
          |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖| := by
  classical
  let D := divisor p.function (closedBall (0 : ℂ) |R|)
  let T := smallGrowth_divisorSupportFinset p.function R
  let S : ℂ → ℂ := fun w => ∑ u ∈ T, (D u : ℂ) *
    (1 / (w - u) + (starRingEnd ℂ) u /
      ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))
  let C : ℝ := max |Real.log ‖p.function 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖|
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hRpos : 0 < R := by nlinarith
  have hRone : 1 ≤ R := by nlinarith
  have horder : ∀ u, meromorphicOrderAt p.function u ≠ ⊤ :=
    p.meromorphicOrderAt_ne_top hx
  have hmass : ∑ u ∈ T, |(D u : ℝ)| =
      poleMultiplicityMass p.function R + poleMultiplicityMass p.function⁻¹ R := by
    exact smallGrowth_sum_abs_divisor_eq_poleMass_add_inv p.meromorphic horder R
  have hTmem : ∀ u ∈ T, ‖u‖ ≤ R := by
    intro u hu
    have huSupport : u ∈ D.support := by
      simpa [T, smallGrowth_divisorSupportFinset, D] using hu
    have huBall := D.supportWithinDomain huSupport
    simpa [D, abs_of_pos hRpos, mem_closedBall_iff_norm] using huBall
  have hTne : ∀ u ∈ T, D u ≠ 0 := by
    intro u hu
    simpa [T, smallGrowth_divisorSupportFinset, D, Function.mem_support] using hu
  have hfinsum (w : ℂ) : (∑ᶠ u : ℂ, (D u : ℂ) *
      (1 / (w - u) + (starRingEnd ℂ) u /
        ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))) = S w := by
    dsimp only [S]
    apply finsum_eq_sum_of_support_subset
    intro u hu
    apply (show u ∈ T ↔ D u ≠ 0 by
      simp [T, smallGrowth_divisorSupportFinset, D, Function.mem_support]).2
    intro hDu
    apply hu
    simp [hDu]
  have hcoeff0 : 0 ≤ 2 * R / (R - r) ^ (2 : ℕ) := by positivity
  have hcoeff4 : 2 * R / (R - r) ^ (2 : ℕ) ≤ 4 := by
    have hgap : 0 < R - r := by nlinarith
    rw [div_le_iff₀ (sq_pos_of_pos hgap)]
    nlinarith
  have hchar0 : 0 ≤ characteristic p.function ⊤ R :=
    characteristic_nonneg hRone
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (le_max_left _ _)
  let B : ℝ := 2 * R / (R - r) ^ (2 : ℕ) *
    (2 * characteristic p.function ⊤ R + C)
  have hB0 : 0 ≤ B := mul_nonneg hcoeff0 (add_nonneg (mul_nonneg (by norm_num) hchar0) hC0)
  have hBbound : B ≤ 8 * characteristic p.function ⊤ R + 4 * C := by
    dsimp [B]
    calc
      2 * R / (R - r) ^ (2 : ℕ) * (2 * characteristic p.function ⊤ R + C) ≤
          4 * (2 * characteristic p.function ⊤ R + C) := by gcongr
      _ = 8 * characteristic p.function ⊤ R + 4 * C := by ring
  have hpoint : ∀ w ∈ sphere (0 : ℂ) |r|,
      Real.posLog ‖deriv p.function w / p.function w‖ ≤
        Real.log 2 + Real.posLog ‖S w‖ + B := by
    intro w hw
    by_cases hfw : p.function w = 0
    · rw [hfw, div_zero, norm_zero, Real.posLog_zero]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hposS : 0 ≤ Real.posLog ‖S w‖ := by
        rw [Real.posLog]
        exact le_max_left _ _
      linarith
    · have hwnorm : ‖w‖ = r := by
        simpa [mem_sphere_iff_norm, abs_of_pos hr0] using hw
      have hwball : w ∈ ball (0 : ℂ) R := by
        rw [mem_ball_iff_norm, sub_zero, hwnorm]
        nlinarith
      have hden : (p.denominator : ℂ → ℂ) w ≠ 0 := by
        intro hzero
        apply hfw
        simp [EntireFractionPresentation.function, hzero]
      have hana : AnalyticAt ℂ p.function w :=
        (p.numerator.2 w (Set.mem_univ w)).div
          (p.denominator.2 w (Set.mem_univ w)) hden
      have hwballClosed : w ∈ closedBall (0 : ℂ) |R| := by
        simpa [abs_of_pos hRpos] using Metric.ball_subset_closedBall hwball
      have hord : analyticOrderAt p.function w = 0 :=
        hana.analyticOrderAt_eq_zero.mpr hfw
      have hwdiv : D w = 0 := by
        dsimp [D]
        rw [divisor_apply (fun z _ => p.meromorphic z) hwballClosed,
          hana.meromorphicOrderAt_eq, hord]
        simp
      have hnorm := PoissonJensen.norm_logDeriv_le_characteristic hRone p.meromorphic
        (fun u => horder u) hbd hwball hana hfw (by simpa [D] using hwdiv)
      simp only [sub_zero, logDeriv_apply, hwnorm] at hnorm
      change ‖deriv p.function w / p.function w‖ ≤
        ‖∑ᶠ u : ℂ, (D u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) u /
            ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))‖ + B at hnorm
      rw [hfinsum w] at hnorm
      calc
        Real.posLog ‖deriv p.function w / p.function w‖ ≤
            Real.posLog (‖S w‖ + B) :=
          Real.posLog_le_posLog (norm_nonneg _) hnorm
        _ ≤ Real.log 2 + Real.posLog ‖S w‖ + Real.posLog B := Real.posLog_add
        _ ≤ Real.log 2 + Real.posLog ‖S w‖ + B := by
          gcongr
          exact smallGrowth_posLog_le_self_of_nonneg hB0
  have hmeroS : Meromorphic S := by
    intro z
    dsimp only [S]
    clear hTmem hTne hmass
    induction T using Finset.induction with
    | empty => simp
    | @insert u U hu ih =>
        have hterm : MeromorphicAt (fun w => (D u : ℂ) *
            (1 / (w - u) + (starRingEnd ℂ) u /
              ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))) z := by
          apply analyticAt_const.meromorphicAt.mul
          apply MeromorphicAt.add
          · exact analyticAt_const.meromorphicAt.div
              (analyticAt_id.sub analyticAt_const).meromorphicAt
          · exact analyticAt_const.meromorphicAt.div
              (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).meromorphicAt
        have hsplit : (fun w : ℂ => ∑ v ∈ insert u U, (D v : ℂ) *
            (1 / (w - v) + (starRingEnd ℂ) v /
              ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) v * w))) =
            (fun w => (D u : ℂ) *
              (1 / (w - u) + (starRingEnd ℂ) u /
                ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) u * w))) +
            fun w => ∑ v ∈ U, (D v : ℂ) *
              (1 / (w - v) + (starRingEnd ℂ) v /
                ((R : ℂ) ^ (2 : ℕ) - (starRingEnd ℂ) v * w)) := by
          funext w
          rw [Finset.sum_insert hu]
          rfl
        rw [hsplit]
        exact hterm.add ih
  have hleftInt : CircleIntegrable
      (fun w => Real.posLog ‖deriv p.function w / p.function w‖) 0 r := by
    have hmeroLog : Meromorphic (fun w => deriv p.function w / p.function w) :=
      p.meromorphic.deriv.div p.meromorphic
    exact (show MeromorphicOn (fun w => deriv p.function w / p.function w)
      (sphere (0 : ℂ) |r|) from fun z _ => hmeroLog z).circleIntegrable_posLog_norm
  have hSInt : CircleIntegrable (fun w => Real.posLog ‖S w‖) 0 r :=
    (show MeromorphicOn S (sphere (0 : ℂ) |r|) from
      fun z _ => hmeroS z).circleIntegrable_posLog_norm
  have hrightInt : CircleIntegrable
      (fun w => Real.log 2 + Real.posLog ‖S w‖ + B) 0 r :=
    ((ContinuousOn.circleIntegrable' continuousOn_const).add hSInt).add
      (ContinuousOn.circleIntegrable' continuousOn_const)
  have hprox : proximity (fun z => deriv p.function z / p.function z) ⊤ r =
      Real.circleAverage
        (fun z => Real.posLog ‖deriv p.function z / p.function z‖) 0 r := by
    simpa using (proximity_top_logDeriv_eq (f := p.function) (a := 0) (r := r))
  rw [hprox]
  have havg := Real.circleAverage_mono hleftInt hrightInt hpoint
  have hkernel := smallGrowth_circleAverage_posLog_divisorKernel_le D T hr hR hTmem hTne
  change Real.circleAverage (fun w => Real.posLog ‖S w‖) 0 r ≤
    5 * ∑ u ∈ T, |(D u : ℝ)| at hkernel
  have hconst1 : CircleIntegrable (fun _ : ℂ => Real.log 2) 0 r :=
    ContinuousOn.circleIntegrable' continuousOn_const
  have hconstB : CircleIntegrable (fun _ : ℂ => B) 0 r :=
    ContinuousOn.circleIntegrable' continuousOn_const
  have havgExpand : Real.circleAverage
      (fun w => Real.log 2 + Real.posLog ‖S w‖ + B) 0 r =
      Real.log 2 + Real.circleAverage (fun w => Real.posLog ‖S w‖) 0 r + B := by
    rw [show (fun w => Real.log 2 + Real.posLog ‖S w‖ + B) =
        ((fun _ : ℂ => Real.log 2) + fun w => Real.posLog ‖S w‖) +
          fun _ => B from rfl,
      Real.circleAverage_add (hconst1.add hSInt) hconstB,
      Real.circleAverage_add hconst1 hSInt,
      Real.circleAverage_const, Real.circleAverage_const]
  rw [havgExpand] at havg
  dsimp [C] at hBbound ⊢
  rw [hmass] at hkernel
  linarith

private theorem smallGrowth_eventuallyEq_deriv_of_eventuallyEq_nhdsNE {F f : ℂ → ℂ} {z : ℂ}
    (h : F =ᶠ[𝓝[≠] z] f) : deriv F =ᶠ[𝓝[≠] z] deriv f := by
  rw [Filter.eventuallyEq_iff_exists_mem] at h ⊢
  obtain ⟨s, hs, hEq⟩ := h
  rw [mem_nhdsWithin] at hs
  obtain ⟨u, hu, hzu, hsub⟩ := hs
  refine ⟨u ∩ {z}ᶜ, mem_nhdsWithin.mpr ⟨u, hu, hzu, fun y hy ↦ hy⟩, fun y hy ↦ ?_⟩
  have hopen : IsOpen (u ∩ {z}ᶜ) := hu.inter isOpen_compl_singleton
  have hev : F =ᶠ[𝓝 y] f := by
    filter_upwards [hopen.mem_nhds hy] with w hw
    exact hEq (hsub hw)
  exact hev.deriv_eq

/-- Differentiation does not create a pole at a point where a meromorphic function is analytic. -/
theorem smallGrowth_meromorphicOrderAt_deriv_nonneg {f : ℂ → ℂ} {z : ℂ}
    (hf : Meromorphic f) (hord : 0 ≤ meromorphicOrderAt f z) :
    0 ≤ meromorphicOrderAt (deriv f) z := by
  let F : ℂ → ℂ := toMeromorphicNFOn f (Set.univ : Set ℂ)
  have hNF : MeromorphicNFAt F z :=
    meromorphicNFOn_toMeromorphicNFOn f (Set.univ : Set ℂ) (Set.mem_univ z)
  have hForder : 0 ≤ meromorphicOrderAt F z := by
    rw [meromorphicOrderAt_toMeromorphicNFOn
      (show MeromorphicOn f Set.univ from fun w _ => hf w) (Set.mem_univ z)]
    exact hord
  have hFana : AnalyticAt ℂ F z :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hForder
  have hFf : F =ᶠ[𝓝[≠] z] f :=
    (show MeromorphicOn f Set.univ from fun w _ => hf w).toMeromorphicNFOn_eq_self_on_nhdsNE
      (Set.mem_univ z)
  rw [← meromorphicOrderAt_congr
    (smallGrowth_eventuallyEq_deriv_of_eventuallyEq_nhdsNE hFf)]
  exact hFana.deriv.meromorphicOrderAt_nonneg

/-- The integrated counting function of a nonnegative locally finite divisor is nonnegative. -/
theorem smallGrowth_locallyFinsupp_logCounting_nonneg
    {D : Function.locallyFinsupp ℂ ℤ} (hD : 0 ≤ D) {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ Function.locallyFinsuppWithin.logCounting D r := by
  classical
  let P := Function.locallyFinsuppWithin.toClosedBall r D
  have hPfin : P.support.Finite :=
    P.finiteSupport (isCompact_closedBall (0 : ℂ) |r|)
  let T := hPfin.toFinset
  change 0 ≤ (∑ᶠ z : ℂ, (P z : ℝ) * Real.log (r * ‖z‖⁻¹)) +
    (D 0 : ℝ) * Real.log r
  rw [finsum_eq_sum_of_support_subset _ (s := T) (by
    intro z hz
    exact (Set.Finite.mem_toFinset hPfin).2 (Function.mem_support.mpr (by
      intro hzero
      exact hz (by simp [hzero]))))]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hzP : z ∈ P.support := by
        exact (Set.Finite.mem_toFinset hPfin).1 (by simpa [T] using hz)
      have hzball := P.supportWithinDomain hzP
      have hr0 : 0 ≤ r := zero_le_one.trans hr
      have hznorm : ‖z‖ ≤ r := by
        simpa [abs_of_nonneg hr0, mem_closedBall_zero_iff] using hzball
      have hnormpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hratio : 1 ≤ r * ‖z‖⁻¹ := by
        calc
          1 = ‖z‖ * ‖z‖⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hnormpos)]
          _ ≤ r * ‖z‖⁻¹ :=
            mul_le_mul_of_nonneg_right hznorm (inv_nonneg.mpr (norm_nonneg z))
      have hlog : 0 ≤ Real.log (r * ‖z‖⁻¹) := Real.log_nonneg hratio
      have hP0 : 0 ≤ P z := by
        change 0 ≤ if z ∈ closedBall (0 : ℂ) |r| then D z else 0
        rw [if_pos hzball]
        exact hD z
      exact mul_nonneg (by exact_mod_cast hP0) hlog
  · exact mul_nonneg (by exact_mod_cast hD 0) (Real.log_nonneg hr)

/-- Pointwise domination of nonnegative divisors implies domination of their counting functions. -/
theorem smallGrowth_locallyFinsupp_logCounting_mono
    {D E : Function.locallyFinsupp ℂ ℤ} (hDE : D ≤ E)
    {r : ℝ} (hr : 1 ≤ r) :
    Function.locallyFinsuppWithin.logCounting D r ≤
      Function.locallyFinsuppWithin.logCounting E r := by
  have hdiff : 0 ≤ E - D := sub_nonneg.mpr hDE
  have hnonneg := smallGrowth_locallyFinsupp_logCounting_nonneg hdiff hr
  have heq : E = D + (E - D) := by abel
  have hmap : Function.locallyFinsuppWithin.logCounting E r =
      Function.locallyFinsuppWithin.logCounting D r +
        Function.locallyFinsuppWithin.logCounting (E - D) r := by
    calc
      Function.locallyFinsuppWithin.logCounting E r =
          Function.locallyFinsuppWithin.logCounting (D + (E - D)) r :=
        congrArg (fun X => Function.locallyFinsuppWithin.logCounting X r) heq
      _ = Function.locallyFinsuppWithin.logCounting D r +
          Function.locallyFinsuppWithin.logCounting (E - D) r := by
        rw [map_add]
        rfl
  rw [hmap]
  linarith

/-- A derivative raises each pole multiplicity by one, hence by at most a factor of two. -/
theorem smallGrowth_poleDivisor_deriv_le_two {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    (divisor (deriv f) Set.univ)⁻ ≤ 2 • (divisor f Set.univ)⁻ := by
  change ∀ z, ((divisor (deriv f) Set.univ)⁻) z ≤
    (2 • (divisor f Set.univ)⁻) z
  intro z
  change (divisor (deriv f) Set.univ z)⁻ ≤
    2 * (divisor f Set.univ z)⁻
  rw [divisor_apply (fun w _ => hf.deriv w) (Set.mem_univ z),
    divisor_apply (fun w _ => hf w) (Set.mem_univ z)]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (horder z)
  rcases le_or_gt 0 m with hmnonneg | hmneg
  · have hnonneg : 0 ≤ meromorphicOrderAt f z := by rw [← hm]; exact_mod_cast hmnonneg
    have hdnonneg := smallGrowth_meromorphicOrderAt_deriv_nonneg hf hnonneg
    rcases eq_or_ne (meromorphicOrderAt (deriv f) z) ⊤ with hdtop | hdtop
    · simp [hdtop, ← hm, negPart, hmnonneg]
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hdtop
      have hdnonneg' : 0 ≤ d := by
        rw [← hd] at hdnonneg
        exact_mod_cast hdnonneg
      simp [← hd, ← hm, negPart, hmnonneg, hdnonneg']
  · have hmd : meromorphicOrderAt (deriv f) z = (m - 1 : ℤ) := by
      apply meromorphicOrderAt_deriv
      · simpa using (show ((m : WithTop ℤ) : WithTop ℤ) ≠ 0 by
          exact_mod_cast hmneg.ne)
      · simpa only [sub_add_cancel] using hm.symm
    have hduntop : (meromorphicOrderAt (deriv f) z).untop₀ = m - 1 := by
      rw [hmd]
      rfl
    have hfuntop : (meromorphicOrderAt f z).untop₀ = m := by
      rw [← hm]
      simp
    rw [hduntop, hfuntop]
    simp [negPart]
    omega

/-- Differentiation multiplies the integrated pole-counting function by at most two. -/
theorem smallGrowth_logCounting_deriv_le_two {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ z, meromorphicOrderAt f z ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    logCounting (deriv f) ⊤ r ≤ 2 * logCounting f ⊤ r := by
  rw [logCounting_top, logCounting_top]
  let D : Function.locallyFinsupp ℂ ℤ := (divisor (deriv f) Set.univ)⁻
  let E : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  have hD : 0 ≤ D := by
    intro z
    change 0 ≤ ((divisor (deriv f) Set.univ z : ℤ)⁻)
    rw [negPart]
    exact le_max_right _ _
  have hDE : D ≤ 2 • E := by
    exact smallGrowth_poleDivisor_deriv_le_two hf horder
  have hmono := smallGrowth_locallyFinsupp_logCounting_mono hDE hr
  change Function.locallyFinsuppWithin.logCounting D r ≤
    2 * Function.locallyFinsuppWithin.logCounting E r
  calc
    Function.locallyFinsuppWithin.logCounting D r ≤
        Function.locallyFinsuppWithin.logCounting (2 • E) r := hmono
    _ = 2 * Function.locallyFinsuppWithin.logCounting E r := by
      rw [map_nsmul]
      simp [nsmul_eq_mul]

/-- The proximity of a derivative is bounded by that of the function and its logarithmic
derivative. -/
theorem smallGrowth_proximity_deriv_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ z, meromorphicOrderAt f z ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    proximity (deriv f) ⊤ r ≤ proximity f ⊤ r +
      proximity (fun z => deriv f z / f z) ⊤ r := by
  have hne : ∀ᶠ z in Filter.codiscrete ℂ, f z ≠ 0 :=
    MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero
      (fun z _ => hf z) (fun z _ => horder z)
  have hneSphere : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), f z ≠ 0 :=
    hne.filter_mono (codiscreteWithin_mono (subset_univ _))
  have heq : deriv f =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
      f * fun z => deriv f z / f z := by
    filter_upwards [hneSphere] with z hz
    change deriv f z = f z * (deriv f z / f z)
    field_simp
  exact proximity_top_le_of_codiscrete_mul (by positivity) heq hf
    (hf.deriv.div hf)

/-- Characteristic of a derivative is bounded by twice the original characteristic plus the
logarithmic-derivative proximity. -/
theorem smallGrowth_characteristic_deriv_le {f : ℂ → ℂ} (hf : Meromorphic f)
    (horder : ∀ z, meromorphicOrderAt f z ≠ ⊤) {r : ℝ} (hr : 1 ≤ r) :
    characteristic (deriv f) ⊤ r ≤ 2 * characteristic f ⊤ r +
      proximity (fun z => deriv f z / f z) ⊤ r := by
  have hprox := smallGrowth_proximity_deriv_le hf horder hr
  have hcount := smallGrowth_logCounting_deriv_le_two hf horder hr
  have hprox0 : 0 ≤ proximity f ⊤ r := proximity_nonneg r
  rw [characteristic, characteristic]
  change proximity (deriv f) ⊤ r + logCounting (deriv f) ⊤ r ≤
    2 * (proximity f ⊤ r + logCounting f ⊤ r) +
      proximity (fun z => deriv f z / f z) ⊤ r
  linarith

/-- The logarithmic derivative of a nonzero small-growth entire fraction has sublinear
proximity.  This is the Nevanlinna logarithmic-derivative lemma in the exact form required by the
small-growth differential field. -/
theorem smallGrowth_proximity_logDeriv_isLittleO {x : EntireField ℂ}
    (p : EntireFractionPresentation x) (hx : x ≠ 0)
    (hp : characteristic p.function ⊤ =o[atTop] id) :
    (fun r => proximity (fun z => deriv p.function z / p.function z) ⊤ r) =o[atTop] id := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  let L : ℝ := Real.log 2
  let Acoef : ℝ := 32 + 80 / L
  let ε : ℝ := c / (2 * Acoef)
  let C : ℝ := max |Real.log ‖p.function 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖|
  let K : ℝ := L + 4 * C
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by norm_num)
  have hAcoef : 0 < Acoef := by
    dsimp [Acoef]
    positivity
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hinv : characteristic p.function⁻¹ ⊤ =o[atTop] id :=
    characteristic_inv_isLittleO p.meromorphic hp
  obtain ⟨A, hA⟩ := (eventually_atTop.1 (hp.bound hε))
  obtain ⟨B, hB⟩ := (eventually_atTop.1 (hinv.bound hε))
  filter_upwards [eventually_ge_atTop
      (max 1 (max A (max B (2 * K / c))))] with r hrLarge
  have hr : 1 ≤ r := le_trans (le_max_left _ _) hrLarge
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨R, hRlow, hRhigh, hRtwice, hRone, hboundary⟩ :=
    smallGrowth_exists_good_radius p hx hr
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have h2Rpos : 0 < 2 * R := mul_pos (by norm_num) hRpos
  have hRA : A ≤ R := by
    have hrA : A ≤ r := by
      calc
        A ≤ max A (max B (2 * K / c)) := le_max_left _ _
        _ ≤ max 1 (max A (max B (2 * K / c))) := le_max_right _ _
        _ ≤ r := hrLarge
    linarith
  have hRB : B ≤ 2 * R := by
    have hrB : B ≤ r := by
      calc
        B ≤ max B (2 * K / c) := le_max_left _ _
        _ ≤ max A (max B (2 * K / c)) := le_max_right _ _
        _ ≤ max 1 (max A (max B (2 * K / c))) := le_max_right _ _
        _ ≤ r := hrLarge
    linarith
  have h2RA : A ≤ 2 * R := hRA.trans (by linarith)
  have hTfR : characteristic p.function ⊤ R ≤ ε * R := by
    have hbound := hA R hRA
    have hchar0 : 0 ≤ characteristic p.function ⊤ R := characteristic_nonneg hRone
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hchar0,
      abs_of_pos hRpos] using hbound
  have hTf2R : characteristic p.function ⊤ (2 * R) ≤ ε * (2 * R) := by
    have hbound := hA (2 * R) h2RA
    have hchar0 : 0 ≤ characteristic p.function ⊤ (2 * R) :=
      characteristic_nonneg (by linarith : 1 ≤ 2 * R)
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hchar0,
      abs_of_pos h2Rpos] using hbound
  have hTinv2R : characteristic p.function⁻¹ ⊤ (2 * R) ≤ ε * (2 * R) := by
    have hbound := hB (2 * R) hRB
    have hchar0 : 0 ≤ characteristic p.function⁻¹ ⊤ (2 * R) :=
      characteristic_nonneg (by linarith : 1 ≤ 2 * R)
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hchar0,
      abs_of_pos h2Rpos] using hbound
  have hRfour : R ≤ 4 * r := by linarith
  have hTfRr : characteristic p.function ⊤ R ≤ 4 * ε * r := by
    have hε0 := hε.le
    nlinarith
  have hTf2Rr : characteristic p.function ⊤ (2 * R) ≤ 8 * ε * r := by
    have hε0 := hε.le
    nlinarith
  have hTinv2Rr : characteristic p.function⁻¹ ⊤ (2 * R) ≤ 8 * ε * r := by
    have hε0 := hε.le
    nlinarith
  have hNFleT : logCounting p.function ⊤ (2 * R) ≤
      characteristic p.function ⊤ (2 * R) := by
    have hprox0 : 0 ≤ proximity p.function ⊤ (2 * R) := proximity_nonneg (2 * R)
    change logCounting p.function ⊤ (2 * R) ≤
      proximity p.function ⊤ (2 * R) + logCounting p.function ⊤ (2 * R)
    linarith
  have hNIleT : logCounting p.function⁻¹ ⊤ (2 * R) ≤
      characteristic p.function⁻¹ ⊤ (2 * R) := by
    have hprox0 : 0 ≤ proximity p.function⁻¹ ⊤ (2 * R) := proximity_nonneg (2 * R)
    change logCounting p.function⁻¹ ⊤ (2 * R) ≤
      proximity p.function⁻¹ ⊤ (2 * R) + logCounting p.function⁻¹ ⊤ (2 * R)
    linarith
  have hmassF : L * poleMultiplicityMass p.function R ≤
      characteristic p.function ⊤ (2 * R) :=
    (log_two_mul_poleMultiplicityMass_le_logCounting p.meromorphic hRone).trans hNFleT
  have hmassI : L * poleMultiplicityMass p.function⁻¹ R ≤
      characteristic p.function⁻¹ ⊤ (2 * R) :=
    (log_two_mul_poleMultiplicityMass_le_logCounting p.meromorphic.inv hRone).trans hNIleT
  have hmassSum : poleMultiplicityMass p.function R +
      poleMultiplicityMass p.function⁻¹ R ≤ 16 * ε * r / L := by
    rw [le_div_iff₀ hL]
    calc
      (poleMultiplicityMass p.function R + poleMultiplicityMass p.function⁻¹ R) * L =
          L * poleMultiplicityMass p.function R +
            L * poleMultiplicityMass p.function⁻¹ R := by ring
      _ ≤ characteristic p.function ⊤ (2 * R) +
          characteristic p.function⁻¹ ⊤ (2 * R) := add_le_add hmassF hmassI
      _ ≤ 16 * ε * r := by linarith
  have hvariable : 5 * (poleMultiplicityMass p.function R +
        poleMultiplicityMass p.function⁻¹ R) +
      8 * characteristic p.function ⊤ R ≤ Acoef * ε * r := by
    calc
      5 * (poleMultiplicityMass p.function R + poleMultiplicityMass p.function⁻¹ R) +
          8 * characteristic p.function ⊤ R ≤
          5 * (16 * ε * r / L) + 8 * (4 * ε * r) := by gcongr
      _ = Acoef * ε * r := by dsimp [Acoef]; ring
  have hAε : Acoef * ε = c / 2 := by
    dsimp [ε]
    field_simp
  have hrK : 2 * K / c ≤ r := le_trans (le_max_right _ _) <|
    le_trans (le_max_right _ _) <|
      le_trans (le_max_right _ _) hrLarge
  have hconstant : K ≤ c / 2 * r := by
    rw [div_le_iff₀ hc] at hrK
    nlinarith
  have hprox := smallGrowth_proximity_logDeriv_le p hx hr hRtwice hboundary
  have hproxNonneg : 0 ≤ proximity
      (fun z => deriv p.function z / p.function z) ⊤ r := proximity_nonneg r
  have hfinal : proximity (fun z => deriv p.function z / p.function z) ⊤ r ≤ c * r := by
    dsimp [K, L, C] at hprox hconstant
    rw [hAε] at hvariable
    linarith
  simpa [Real.norm_eq_abs, abs_of_nonneg hproxNonneg, abs_of_pos hrpos] using hfinal

/-- Differentiating the literal function of a nonzero small-growth presentation preserves
sublinear Nevanlinna characteristic. -/
theorem smallGrowth_characteristic_deriv_isLittleO {x : EntireField ℂ}
    (p : EntireFractionPresentation x) (hx : x ≠ 0)
    (hp : characteristic p.function ⊤ =o[atTop] id) :
    characteristic (deriv p.function) ⊤ =o[atTop] id := by
  let v : ℝ → ℝ := fun r => 2 * characteristic p.function ⊤ r +
    proximity (fun z => deriv p.function z / p.function z) ⊤ r
  have hv : v =o[atTop] id :=
    (hp.const_mul_left 2).add (smallGrowth_proximity_logDeriv_isLittleO p hx hp)
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact characteristic_nonneg hr
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact smallGrowth_characteristic_deriv_le p.meromorphic
      (p.meromorphicOrderAt_ne_top hx) hr

/-- In one complex variable, directional derivative in direction `1` is the ordinary derivative. -/
theorem smallGrowth_entireDirectionalDerivative_one (f : ℂ → ℂ) :
    entireDirectionalDerivative (1 : ℂ) f = deriv f := by
  funext z
  rw [entireDirectionalDerivative, fderiv_eq_smul_deriv]
  simp

theorem smallGrowth_fieldDirDerivation_algebraMap (a : entireSubring ℂ) :
    fieldDirDerivation (1 : ℂ)
        (algebraMap (entireSubring ℂ) (EntireField ℂ) a) =
      algebraMap (entireSubring ℂ) (EntireField ℂ) (entireDirDeriv (1 : ℂ) a) := by
  rw [fieldDirDerivation,
    GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- Quotient-rule presentation of the fraction-field derivative. -/
noncomputable def smallGrowth_derivPresentation {x : EntireField ℂ}
    (p : EntireFractionPresentation x) :
    EntireFractionPresentation (fieldDirDerivation (1 : ℂ) x) where
  numerator := entireDirDeriv (1 : ℂ) p.numerator * p.denominator -
    p.numerator * entireDirDeriv (1 : ℂ) p.denominator
  denominator := p.denominator ^ (2 : ℕ)
  denominator_ne_zero := pow_ne_zero 2 p.denominator_ne_zero
  eq_div := by
    calc
      fieldDirDerivation (1 : ℂ) x =
          fieldDirDerivation (1 : ℂ)
            (algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator) :=
        congrArg (fieldDirDerivation (1 : ℂ)) p.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ)
            (entireDirDeriv (1 : ℂ) p.numerator * p.denominator -
              p.numerator * entireDirDeriv (1 : ℂ) p.denominator) /
          algebraMap (entireSubring ℂ) (EntireField ℂ) (p.denominator ^ (2 : ℕ)) := by
        rw [Derivation.leibniz_div]
        rw [smallGrowth_fieldDirDerivation_algebraMap,
          smallGrowth_fieldDirDerivation_algebraMap]
        simp only [Algebra.smul_def, map_sub, map_mul, map_pow]
        simp
        ring

/-- Literal function of the quotient-rule presentation agrees codiscretely with the ordinary
derivative of the original literal fraction. -/
theorem smallGrowth_derivPresentation_function_eventuallyEq {x : EntireField ℂ}
    (p : EntireFractionPresentation x) :
    (smallGrowth_derivPresentation p).function =ᶠ[Filter.codiscrete ℂ]
      deriv p.function := by
  have hnumDiff : Differentiable ℂ (p.numerator : ℂ → ℂ) :=
    differentiable_of_analyticOnNhd p.numerator.2
  have hdenDiff : Differentiable ℂ (p.denominator : ℂ → ℂ) :=
    differentiable_of_analyticOnNhd p.denominator.2
  filter_upwards [p.denominator_eventually_ne_zero] with z hz
  change
    (((entireDirDeriv (1 : ℂ) p.numerator : entireSubring ℂ) : ℂ → ℂ) z *
          (p.denominator : ℂ → ℂ) z -
        (p.numerator : ℂ → ℂ) z *
          ((entireDirDeriv (1 : ℂ) p.denominator : entireSubring ℂ) : ℂ → ℂ) z) /
        ((p.denominator : ℂ → ℂ) z ^ (2 : ℕ)) =
      deriv ((p.numerator : ℂ → ℂ) / (p.denominator : ℂ → ℂ)) z
  rw [deriv_div (hnumDiff z) (hdenDiff z) hz]
  rw [entireDirDeriv_coe, entireDirDeriv_coe,
    smallGrowth_entireDirectionalDerivative_one,
    smallGrowth_entireDirectionalDerivative_one]

/-- The exact small-growth carrier is closed under the ordinary complex derivative. -/
theorem HasSmallGrowth.fieldDirDerivation_one {x : EntireField ℂ}
    (hx : HasSmallGrowth x) :
    HasSmallGrowth (fieldDirDerivation (1 : ℂ) x) := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hasSmallGrowth_zero
  · obtain ⟨p, hp⟩ := hx
    let q := smallGrowth_derivPresentation p
    refine ⟨q, ?_⟩
    have hderivSmall := smallGrowth_characteristic_deriv_isLittleO p hx0 hp
    have hcharEq : (fun r => characteristic q.function ⊤ r) =ᶠ[atTop]
        fun r => characteristic (deriv p.function) ⊤ r := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      exact characteristic_congr_codiscrete q.meromorphic p.meromorphic.deriv
        (smallGrowth_derivPresentation_function_eventuallyEq p) (by positivity)
    exact hderivSmall.congr' hcharEq.symm EventuallyEq.rfl

end

end GaloisForLFunctions.HTGeometry
