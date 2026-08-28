import GaloisForLFunctions.HTGeometry.ConstitutiveFiniteEscortFormationProperness
import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
import GaloisForLFunctions.HTGeometry.IntervalPoincare
import GaloisForLFunctions.HTGeometry.PrimitiveAverageLimit
import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.RHTower.SecondMoment

/-!
# Response polarization, Fisher tails, and Jeffreys escape

Positive response length and reciprocal work share one local density but induce different global
tail uniformities.  Finite exponential escorts realize the separation exactly.
-/

open Filter MeasureTheory Set Topology InformationTheory ProbabilityTheory
open scoped ENNReal Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric response length between two source parameters. -/
def responseLength (I : ℝ → ℝ) (a b : ℝ) : ℝ :=
  |∫ u : ℝ in a..b, √(I u)|

/-- Symmetric reciprocal response work between two source parameters. -/
def responseWork (I : ℝ → ℝ) (a b : ℝ) : ℝ :=
  |b - a| * |∫ u : ℝ in a..b, I u|

@[simp] theorem responseLength_self (I : ℝ → ℝ) (a : ℝ) :
    responseLength I a a = 0 := by simp [responseLength]

@[simp] theorem responseWork_self (I : ℝ → ℝ) (a : ℝ) :
    responseWork I a a = 0 := by simp [responseWork]

@[simp] theorem responseLength_comm (I : ℝ → ℝ) (a b : ℝ) :
    responseLength I a b = responseLength I b a := by
  rw [responseLength, responseLength, intervalIntegral.integral_symm]
  simp

@[simp] theorem responseWork_comm (I : ℝ → ℝ) (a b : ℝ) :
    responseWork I a b = responseWork I b a := by
  rw [responseWork, responseWork, intervalIntegral.integral_symm]
  simp [abs_sub_comm]

/-- Local fusion: squared response length never exceeds reciprocal work `(RPC.2)`. -/
theorem responseLength_sq_le_responseWork
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u)
    {a b : ℝ} (hab : a ≤ b) :
    responseLength I a b ^ 2 ≤ responseWork I a b := by
  have hsqrt : Continuous (fun u : ℝ => √(I u)) := hI.sqrt
  have hsqrtInt : IntervalIntegrable (fun u : ℝ => √(I u)) volume a b :=
    hsqrt.intervalIntegrable a b
  have hsqrtSqInt : IntervalIntegrable (fun u : ℝ => (√(I u)) ^ 2) volume a b :=
    by
      rw [show (fun u : ℝ => (√(I u)) ^ 2) = I by
        funext u
        exact Real.sq_sqrt (hI0 u)]
      exact hI.intervalIntegrable a b
  have hcs := sq_integral_le_length_mul hab hsqrtInt.1 hsqrtSqInt.1
  have hsquare : (∫ u in Set.Ioc a b, (√(I u)) ^ 2) =
      ∫ u : ℝ in a..b, I u := by
    rw [intervalIntegral.integral_of_le hab]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    exact Real.sq_sqrt (hI0 u)
  have hsqrtSet : (∫ u in Set.Ioc a b, √(I u)) =
      ∫ u : ℝ in a..b, √(I u) := by
    rw [intervalIntegral.integral_of_le hab]
  rw [hsquare, hsqrtSet] at hcs
  have hmass : 0 ≤ ∫ u : ℝ in a..b, I u :=
    intervalIntegral.integral_nonneg hab (fun u _ => hI0 u)
  simpa [responseLength, responseWork, abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg hmass, sq_abs] using hcs

private theorem tendsto_abs_intervalAverage
    {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    Tendsto (fun h : ℝ => |∫ u : ℝ in t..t + h, g u| / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 |g t|) := by
  let G : ℝ → ℝ := fun x => ∫ u : ℝ in t..x, g u
  have hG : HasDerivAt G (g t) t :=
    (hg.integral_hasStrictDerivAt t t).hasDerivAt
  have hcomp : HasDerivAt (fun h : ℝ => G (t + h)) (g t) 0 := by
    have hinner : HasDerivAt (fun h : ℝ => t + h) 1 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add t
    have hG' : HasDerivAt G (g t) (t + 0) := by simpa using hG
    simpa [Function.comp_def] using hG'.comp 0 hinner
  have hslope := hasDerivAt_iff_tendsto_slope.mp hcomp
  have hzero : G (t + 0) = 0 := by simp [G]
  have habs : Tendsto (fun h : ℝ => |slope (fun y : ℝ => G (t + y)) 0 h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 |g t|) :=
    (continuous_abs.tendsto (g t)).comp hslope
  refine habs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [slope_def_field, hzero]
  simp only [sub_zero, G, abs_div]

/-- Local response length recovers the square-root density `(RPC.3)`. -/
theorem tendsto_responseLength_div_abs
    {I : ℝ → ℝ} (hI : Continuous I) (_hI0 : ∀ u, 0 ≤ I u) (t : ℝ) :
    Tendsto (fun h : ℝ => responseLength I t (t + h) / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 √(I t)) := by
  simpa [responseLength, abs_of_nonneg (Real.sqrt_nonneg _)] using
    tendsto_abs_intervalAverage hI.sqrt t

/-- Local reciprocal work recovers the response density `(RPC.3)`. -/
theorem tendsto_responseWork_div_sq
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u) (t : ℝ) :
    Tendsto (fun h : ℝ => responseWork I t (t + h) / h ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (I t)) := by
  have havg := tendsto_abs_intervalAverage hI t
  rw [abs_of_nonneg (hI0 t)] at havg
  refine havg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  simp only [responseWork, add_sub_cancel_left]
  rw [show h ^ 2 = |h| * |h| by rw [← sq_abs]; ring]
  rw [mul_div_mul_left _ _ (abs_ne_zero.mpr hh0)]

/-- Uniform collapse of the positive response-length tail. -/
def ResponseLengthTailCollapses (I : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ a b : ℝ,
    T ≤ a → T ≤ b → responseLength I a b < ε

/-- Unbounded reciprocal work on every positive tail. -/
def ResponseWorkTailUnbounded (I : ℝ → ℝ) : Prop :=
  ∀ T B : ℝ, ∃ a b : ℝ, T ≤ a ∧ T ≤ b ∧ B < responseWork I a b

/-- Uniform boundedness of complete reflected response work. -/
def BoundedReflectedResponseWork (I : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ T : ℝ, 1 ≤ T → responseWork I (-T) T ≤ B

private theorem tendsto_setIntegral_Ici_atTop_zero
    {g : ℝ → ℝ} (hg : Integrable g volume) (hg0 : ∀ x, 0 ≤ g x) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in Set.Ici (n : ℝ), g x) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable ((Set.Ici (n : ℝ)).indicator g) volume :=
    fun n => hg.aestronglyMeasurable.indicator measurableSet_Ici
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ, ‖(Set.Ici (n : ℝ)).indicator g x‖ ≤ g x := by
    intro n
    filter_upwards with x
    by_cases hx : x ∈ Set.Ici (n : ℝ)
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact hg0 x
  have hlim : ∀ᵐ x : ℝ,
      Tendsto (fun n : ℕ => (Set.Ici (n : ℝ)).indicator g x) atTop (𝓝 0) := by
    filter_upwards with x
    have hev : ∀ᶠ n : ℕ in atTop, (Set.Ici (n : ℝ)).indicator g x = 0 := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop x] with n hn
      exact Set.indicator_of_notMem (by simpa only [Set.mem_Ici, not_le] using hn) g
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  simpa only [MeasureTheory.integral_indicator measurableSet_Ici, integral_zero] using
    MeasureTheory.tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim

private theorem responseLength_le_setIntegral_Ici
    {I : ℝ → ℝ} (_hI : Continuous I) (_hI0 : ∀ u, 0 ≤ I u)
    {T a b : ℝ} (hInt : IntegrableOn (fun u : ℝ => √(I u)) (Set.Ici T) volume)
    (ha : T ≤ a) (hb : T ≤ b) :
    responseLength I a b ≤ ∫ u : ℝ in Set.Ici T, √(I u) := by
  have hg0 : ∀ u, 0 ≤ √(I u) := fun u => Real.sqrt_nonneg _
  have hordered : ∀ {x y : ℝ}, T ≤ x → x ≤ y →
      responseLength I x y ≤ ∫ u : ℝ in Set.Ici T, √(I u) := by
    intro x y hTx hxy
    have hsub : Set.Ioc x y ⊆ Set.Ici T := by
      intro u hu
      exact le_trans hTx hu.1.le
    have hmono : (∫ u : ℝ in Set.Ioc x y, √(I u)) ≤
        ∫ u : ℝ in Set.Ici T, √(I u) :=
      MeasureTheory.setIntegral_mono_set hInt
        (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hsub)
    rw [responseLength, abs_of_nonneg
      (intervalIntegral.integral_nonneg hxy (fun u _ => hg0 u)),
      intervalIntegral.integral_of_le hxy]
    exact hmono
  rcases le_total a b with hab | hba
  · exact hordered ha hab
  · rw [responseLength_comm]
    exact hordered hb hba

/-- Finite square-root tail mass forces vanishing response-length diameter `(RPC.6)`. -/
theorem responseLengthTailCollapses_of_integrableOn_Ici
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u)
    {T₀ : ℝ} (hTail : IntegrableOn (fun u : ℝ => √(I u)) (Set.Ici T₀) volume) :
    ResponseLengthTailCollapses I := by
  let g : ℝ → ℝ := (Set.Ici T₀).indicator fun u : ℝ => √(I u)
  have hg : Integrable g volume := by
    simpa only [g] using hTail.integrable_indicator measurableSet_Ici
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    simp only [g]
    exact Set.indicator_nonneg (fun x _ => Real.sqrt_nonneg _) u
  have htailZero := tendsto_setIntegral_Ici_atTop_zero hg hg0
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, (∫ u : ℝ in Set.Ici (n : ℝ), g u) < ε :=
    htailZero.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hT₀, hTsmall⟩ : ∃ n : ℕ, T₀ ≤ (n : ℝ) ∧
      (∫ u : ℝ in Set.Ici (n : ℝ), g u) < ε := by
    exact (hsmall.and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop T₀)).exists.imp
        fun n h => ⟨h.2, h.1⟩
  let T : ℝ := n
  refine ⟨T, fun a b ha hb => ?_⟩
  have hIntT : IntegrableOn (fun u : ℝ => √(I u)) (Set.Ici T) volume :=
    hTail.mono_set (Set.Ici_subset_Ici.mpr hT₀)
  have hbound := responseLength_le_setIntegral_Ici hI hI0 hIntT ha hb
  have heq : (∫ u : ℝ in Set.Ici T, g u) =
      ∫ u : ℝ in Set.Ici T, √(I u) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    simpa only [g] using
      Set.indicator_of_mem (show u ∈ Set.Ici T₀ from le_trans hT₀ hu)
        (fun u : ℝ => √(I u))
  rw [heq] at hTsmall
  exact lt_of_le_of_lt hbound hTsmall

private theorem intervalIntegral_mono_of_nonneg
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u)
    {A a b B : ℝ} (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B) :
    (∫ u : ℝ in a..b, I u) ≤ ∫ u : ℝ in A..B, I u := by
  have hAB : A ≤ B := hAa.trans (hab.trans hbB)
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hAB]
  exact MeasureTheory.setIntegral_mono_set (hI.intervalIntegrable A B).1
    (Filter.Eventually.of_forall hI0) (Filter.Eventually.of_forall (by
      intro u hu
      exact ⟨lt_of_le_of_lt hAa hu.1, hu.2.trans hbB⟩))

/-- Positive mass on every finite tail forces unbounded reciprocal work `(RPC.7)`. -/
theorem responseWorkTailUnbounded_of_positive_tail
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u)
    (hpos : ∀ T : ℝ, ∃ b : ℝ, T < b ∧ 0 < ∫ u : ℝ in T..b, I u) :
    ResponseWorkTailUnbounded I := by
  intro T B
  obtain ⟨b₀, hTb₀, hmass⟩ := hpos T
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (B / (∫ u : ℝ in T..b₀, I u))
  let b : ℝ := b₀ + n
  have hb₀b : b₀ ≤ b := by simp [b]
  have hTb : T ≤ b := hTb₀.le.trans hb₀b
  have hmono : (∫ u : ℝ in T..b₀, I u) ≤ ∫ u : ℝ in T..b, I u :=
    intervalIntegral_mono_of_nonneg hI hI0 le_rfl hTb₀.le hb₀b
  have hnB : B < (n : ℝ) * ∫ u : ℝ in T..b₀, I u :=
    (div_lt_iff₀ hmass).mp hn
  refine ⟨T, b, le_rfl, hTb, ?_⟩
  rw [responseWork, abs_of_nonneg (sub_nonneg.mpr hTb),
    abs_of_nonneg (intervalIntegral.integral_nonneg hTb (fun u _ => hI0 u))]
  have hlen : (n : ℝ) ≤ b - T := by
    dsimp [b]
    linarith
  nlinarith

/-- Complete reflected work is bounded exactly for zero response `(RPC.7b)`. -/
theorem boundedReflectedResponseWork_iff
    {I : ℝ → ℝ} (hI : Continuous I) (hI0 : ∀ u, 0 ≤ I u) :
    BoundedReflectedResponseWork I ↔ ∀ u, I u = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hnonzero
    push Not at hnonzero
    obtain ⟨u₀, hu₀⟩ := hnonzero
    have hu₀pos : 0 < I u₀ := lt_of_le_of_ne (hI0 u₀) (Ne.symm hu₀)
    let A := u₀ - 1
    let C := u₀ + 1
    have hmass : 0 < ∫ u : ℝ in A..C, I u := by
      apply RHTower.intervalIntegral_pos_of_continuous_nonneg_of_exists_pos hI
      · exact fun u _ => hI0 u
      · exact ⟨u₀, by constructor <;> dsimp [A, C] <;> linarith, hu₀pos⟩
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt
      (max (max |A| |C|) (max 1 (B / (2 * (∫ u : ℝ in A..C, I u)))))
    let T : ℝ := n
    have hT_A : -T ≤ A := by
      have h := lt_of_le_of_lt (le_max_left |A| |C|)
        (lt_of_le_of_lt (le_max_left _ _) hn)
      dsimp [T]
      exact neg_le_of_abs_le (by exact_mod_cast h.le)
    have hC_T : C ≤ T := by
      have h := lt_of_le_of_lt (le_max_right |A| |C|)
        (lt_of_le_of_lt (le_max_left _ _) hn)
      dsimp [T]
      exact le_trans (le_abs_self C) (by exact_mod_cast h.le)
    have hT1 : (1 : ℝ) ≤ T := by
      have h := lt_of_le_of_lt (le_max_left (1 : ℝ) _)
        (lt_of_le_of_lt (le_max_right _ _) hn)
      exact h.le
    have hmassMono : (∫ u : ℝ in A..C, I u) ≤ ∫ u : ℝ in -T..T, I u :=
      intervalIntegral_mono_of_nonneg hI hI0 hT_A (by dsimp [A, C]; linarith) hC_T
    have hTlarge : B < 2 * T * ∫ u : ℝ in A..C, I u := by
      have h := lt_of_le_of_lt (le_max_right (1 : ℝ) _)
        (lt_of_le_of_lt (le_max_right _ _) hn)
      have hden : 0 < 2 * (∫ u : ℝ in A..C, I u) := by positivity
      have := (div_lt_iff₀ hden).mp h
      dsimp [T]
      nlinarith
    have hwork := hB T hT1
    rw [responseWork, abs_of_nonneg (by linarith : 0 ≤ T - (-T)),
      abs_of_nonneg (intervalIntegral.integral_nonneg (by linarith : -T ≤ T)
        (fun u _ => hI0 u))] at hwork
    nlinarith
  · intro hzero
    refine ⟨0, fun T _ => ?_⟩
    simp [responseWork, hzero]

/-! ## Quantitative finite-escort tails -/

/-- Tilted mass outside a prescribed top-score fibre. -/
noncomputable def finiteTiltOffTopMass {n : ℕ} (w r : Fin n → ℝ)
    (rTop t : ℝ) : ℝ :=
  ∑ x with r x ≠ rTop, finiteExponentialTilt w r t x

private lemma finiteTopWeight_le_one {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (rTop : ℝ) :
    ∑ x with r x = rTop, w x ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => hw x)

private lemma finiteExpPartition_ge_topWeight_mul_exp {n : ℕ}
    {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x) (rTop t : ℝ) :
    (∑ x with r x = rTop, w x) * Real.exp (t * rTop) ≤
      finiteExpPartition w r t := by
  unfold finiteExpPartition
  calc
    (∑ x with r x = rTop, w x) * Real.exp (t * rTop) =
        ∑ x with r x = rTop, w x * Real.exp (t * r x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hx.2]
    _ ≤ ∑ x, w x * Real.exp (t * r x) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => mul_nonneg (hw x) (Real.exp_pos _).le)

private lemma finiteOffTopWeight_eq_one_sub {n : ℕ} {w r : Fin n → ℝ}
    (hsum : ∑ x, w x = 1) (rTop : ℝ) :
    (∑ x with r x ≠ rTop, w x) = 1 - ∑ x with r x = rTop, w x := by
  have hpartition := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => r x = rTop) w
  rw [hsum] at hpartition
  linarith

private lemma finiteTiltOffTopMass_eq_div {n : ℕ} {w r : Fin n → ℝ}
    (rTop t : ℝ) :
    finiteTiltOffTopMass w r rTop t =
      (∑ x with r x ≠ rTop, w x * Real.exp (t * r x)) /
        finiteExpPartition w r t := by
  unfold finiteTiltOffTopMass finiteExponentialTilt
  rw [Finset.sum_div]

/-- A positive top fibre and spectral gap give the exact exponential off-top mass bound. -/
theorem finiteTiltOffTopMass_le_exp {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta t : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (ht : 0 ≤ t) :
    finiteTiltOffTopMass w r rTop t ≤
      ((1 - ∑ x with r x = rTop, w x) /
        (∑ x with r x = rTop, w x)) * Real.exp (-delta * t) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  have hM1 : M ≤ 1 := finiteTopWeight_le_one hw hsum rTop
  have hOneM : 0 ≤ 1 - M := sub_nonneg.mpr hM1
  have hZ : 0 < finiteExpPartition w r t := finiteExpPartition_pos hw hsum t
  have hZlower : M * Real.exp (t * rTop) ≤ finiteExpPartition w r t :=
    finiteExpPartition_ge_topWeight_mul_exp hw rTop t
  have hnum : (∑ x with r x ≠ rTop, w x * Real.exp (t * r x)) ≤
      (1 - M) * (Real.exp (t * rTop) * Real.exp (-delta * t)) := by
    calc
      (∑ x with r x ≠ rTop, w x * Real.exp (t * r x)) ≤
          ∑ x with r x ≠ rTop,
            w x * (Real.exp (t * rTop) * Real.exp (-delta * t)) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_filter] at hx
        have hscore : t * r x ≤ t * rTop + (-delta * t) := by
          have := hgap x hx.2
          nlinarith
        have hexp := (Real.exp_le_exp).2 hscore
        rw [Real.exp_add] at hexp
        exact mul_le_mul_of_nonneg_left hexp (hw x)
      _ = (1 - M) * (Real.exp (t * rTop) * Real.exp (-delta * t)) := by
        rw [← Finset.sum_mul, finiteOffTopWeight_eq_one_sub hsum rTop]
  rw [finiteTiltOffTopMass_eq_div]
  apply (div_le_iff₀ hZ).2
  have hM : 0 < M := by simpa only [M] using hTop
  calc
    (∑ x with r x ≠ rTop, w x * Real.exp (t * r x)) ≤
        (1 - M) * (Real.exp (t * rTop) * Real.exp (-delta * t)) := hnum
    _ = ((1 - M) / M * Real.exp (-delta * t)) *
        (M * Real.exp (t * rTop)) := by
      rw [show ((1 - M) / M * Real.exp (-delta * t)) *
          (M * Real.exp (t * rTop)) =
          ((1 - M) / M * M) *
            (Real.exp (-delta * t) * Real.exp (t * rTop)) by ring,
        div_mul_cancel₀ (1 - M) hM.ne']
      ring
    _ ≤ ((1 - M) / M * Real.exp (-delta * t)) *
        finiteExpPartition w r t := by
      exact mul_le_mul_of_nonneg_left hZlower
        (mul_nonneg (div_nonneg hOneM hTop.le) (Real.exp_pos _).le)

/-- Weighted variance is no larger than weighted square error around any comparison score. -/
theorem finiteTiltVariance_le_squareError {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t c : ℝ) :
    finiteTiltVariance w r t ≤
      ∑ x, finiteExponentialTilt w r t x * (r x - c) ^ 2 := by
  have hprob := finiteExponentialTilt_sum (r := r) hw hsum t
  unfold finiteTiltVariance finiteTiltMean
  simp_rw [show ∀ x, finiteExponentialTilt w r t x * (r x - c) ^ 2 =
      finiteExponentialTilt w r t x *
          (r x - ∑ y, finiteExponentialTilt w r t y * r y) ^ 2 +
        finiteExponentialTilt w r t x *
          (∑ y, finiteExponentialTilt w r t y * r y - c) ^ 2 +
        2 * finiteExponentialTilt w r t x *
          (r x - ∑ y, finiteExponentialTilt w r t y * r y) *
          (∑ y, finiteExponentialTilt w r t y * r y - c) by intro x; ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcenter : ∑ x, finiteExponentialTilt w r t x *
      (r x - ∑ y, finiteExponentialTilt w r t y * r y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hprob]
    ring
  have hcross : ∑ x, 2 * finiteExponentialTilt w r t x *
      (r x - ∑ y, finiteExponentialTilt w r t y * r y) *
      (∑ y, finiteExponentialTilt w r t y * r y - c) = 0 := by
    calc
      (∑ x, 2 * finiteExponentialTilt w r t x *
          (r x - ∑ y, finiteExponentialTilt w r t y * r y) *
          (∑ y, finiteExponentialTilt w r t y * r y - c)) =
          2 * (∑ y, finiteExponentialTilt w r t y * r y - c) *
            ∑ x, finiteExponentialTilt w r t x *
              (r x - ∑ y, finiteExponentialTilt w r t y * r y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hcenter]; ring
  rw [hcross, add_zero]
  have hsquare : 0 ≤ ∑ x, finiteExponentialTilt w r t x *
      (∑ y, finiteExponentialTilt w r t y * r y - c) ^ 2 := by
    exact Finset.sum_nonneg fun x _ => mul_nonneg
      (finiteExponentialTilt_nonneg hw hsum t x) (sq_nonneg _)
  linarith

/-- Square error around the top score is controlled by range squared times off-top mass. -/
theorem finiteTiltSquareError_le_range_mul_offTopMass {n : ℕ}
    {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop R t : ℝ} (hR : ∀ x, |r x - rTop| ≤ R) :
    (∑ x, finiteExponentialTilt w r t x * (r x - rTop) ^ 2) ≤
      R ^ 2 * finiteTiltOffTopMass w r rTop t := by
  classical
  unfold finiteTiltOffTopMass
  rw [Finset.mul_sum]
  calc
    (∑ x, finiteExponentialTilt w r t x * (r x - rTop) ^ 2) =
        ∑ x, if r x ≠ rTop then
          finiteExponentialTilt w r t x * (r x - rTop) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · simp [not_ne_iff.mp hx]
    _ ≤ ∑ x, if r x ≠ rTop then
          R ^ 2 * finiteExponentialTilt w r t x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · have hsq : (r x - rTop) ^ 2 ≤ R ^ 2 := by
          apply (sq_le_sq).2
          rw [abs_of_nonneg ((abs_nonneg _).trans (hR x))]
          exact hR x
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq
          (finiteExponentialTilt_nonneg hw hsum t x)
      · exact le_rfl
    _ = ∑ x with r x ≠ rTop,
          R ^ 2 * finiteExponentialTilt w r t x := by
      rw [Finset.sum_filter]

/-- Finite-escort Fisher response obeys the exact top-gap exponential envelope. -/
theorem finiteTiltVariance_le_topGap_exp {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta R t : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hR : ∀ x, |r x - rTop| ≤ R) (ht : 0 ≤ t) :
    finiteTiltVariance w r t ≤
      R ^ 2 * ((1 - ∑ x with r x = rTop, w x) /
        (∑ x with r x = rTop, w x)) * Real.exp (-delta * t) := by
  calc
    finiteTiltVariance w r t ≤
        ∑ x, finiteExponentialTilt w r t x * (r x - rTop) ^ 2 :=
      finiteTiltVariance_le_squareError hw hsum t rTop
    _ ≤ R ^ 2 * finiteTiltOffTopMass w r rTop t :=
      finiteTiltSquareError_le_range_mul_offTopMass hw hsum hR
    _ ≤ R ^ 2 * (((1 - ∑ x with r x = rTop, w x) /
          (∑ x with r x = rTop, w x)) * Real.exp (-delta * t)) := by
      exact mul_le_mul_of_nonneg_left
        (finiteTiltOffTopMass_le_exp hw hsum hTop hgap ht) (sq_nonneg R)
    _ = _ := by ring

private theorem continuous_finiteTiltVariance {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) :
    Continuous (finiteTiltVariance w r) := by
  apply continuous_iff_continuousAt.2
  intro t
  have hfun : finiteTiltVariance w r = fun s =>
      finiteTiltSecondMoment w r s - finiteTiltMean w r s ^ 2 := by
    funext s
    exact finiteTiltVariance_eq_second_sub_sq hw hsum s
  rw [hfun]
  apply ContinuousAt.sub
  · have hsecond : finiteTiltSecondMoment w r = fun s =>
        (∑ x, w x * r x ^ 2 * Real.exp (s * r x)) /
          finiteExpPartition w r s := by
      funext s
      exact finiteTiltSecondMoment_eq_div s
    rw [hsecond]
    exact (by fun_prop : ContinuousAt
      (fun s : ℝ => ∑ x, w x * r x ^ 2 * Real.exp (s * r x)) t).div
        (hasDerivAt_finiteExpPartition w r t).continuousAt
        (finiteExpPartition_pos hw hsum t).ne'
  · exact (hasDerivAt_finiteTiltMean hw hsum t).continuousAt.pow 2

/-- Exact Jeffreys work is parameter length times integrated Fisher response `(RPC.12)`. -/
theorem finiteTiltJeffreysReal_eq_integral_variance {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) (a b : ℝ) :
    finiteTiltJeffreysReal w r a b =
      (b - a) * ∫ u : ℝ in a..b, finiteTiltVariance w r u := by
  have hFTC : (∫ u : ℝ in a..b, finiteTiltVariance w r u) =
      finiteTiltMean w r b - finiteTiltMean w r a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_finiteTiltMean (fun x => (hw x).le) hsum t)
      ((continuous_finiteTiltVariance (fun x => (hw x).le) hsum).intervalIntegrable a b)
  rw [finiteTiltJeffreysReal_eq hw hsum, hFTC]
  ring

/-- Exact finite-escort Jeffreys divergence equals abstract reciprocal response work. -/
theorem finiteTiltJeffreysReal_eq_responseWork {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    {a b : ℝ} (hab : a ≤ b) :
    finiteTiltJeffreysReal w r a b = responseWork (finiteTiltVariance w r) a b := by
  rw [finiteTiltJeffreysReal_eq_integral_variance hw hsum]
  unfold responseWork
  rw [abs_of_nonneg (sub_nonneg.mpr hab),
    abs_of_nonneg (intervalIntegral.integral_nonneg hab
      (fun u _ => finiteTiltVariance_nonneg (fun x => (hw x).le) hsum u))]

/-- Intrinsic one-dimensional Fisher length of a finite escort arc. -/
noncomputable def finiteEscortFisherLength {n : ℕ} (w r : Fin n → ℝ)
    (a b : ℝ) : ℝ :=
  ∫ u : ℝ in a..b, √(finiteTiltVariance w r u)

/-- Escort Fisher length is exactly abstract response length `(RPC.13)`. -/
theorem finiteEscortFisherLength_eq_responseLength {n : ℕ} {w r : Fin n → ℝ}
    {a b : ℝ} (hab : a ≤ b) :
    finiteEscortFisherLength w r a b = responseLength (finiteTiltVariance w r) a b := by
  unfold finiteEscortFisherLength responseLength
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab
    (fun u _ => Real.sqrt_nonneg _))]

/-- Square-root Fisher response inherits the sharp exponential top-gap envelope. -/
theorem sqrt_finiteTiltVariance_le_topGap_exp {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta R t : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hR : ∀ x, |r x - rTop| ≤ R) (ht : 0 ≤ t) :
    √(finiteTiltVariance w r t) ≤
      R * √((1 - ∑ x with r x = rTop, w x) /
        (∑ x with r x = rTop, w x)) * Real.exp (-delta * t / 2) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  let C : ℝ := (1 - M) / M
  have hM1 : M ≤ 1 := finiteTopWeight_le_one hw hsum rTop
  have hM : 0 < M := by simpa only [M] using hTop
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hM1) hM.le
  have hTopSet : (Finset.univ.filter fun x => r x = rTop).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hTop
    simp at hTop
  obtain ⟨x, _⟩ := hTopSet
  have hR0 : 0 ≤ R := (abs_nonneg (r x - rTop)).trans (hR x)
  have hbound := finiteTiltVariance_le_topGap_exp hw hsum hTop hgap hR ht
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · rw [mul_pow, mul_pow, Real.sq_sqrt hC]
    have hexp : Real.exp (-delta * t / 2) ^ 2 = Real.exp (-delta * t) := by
      rw [← Real.exp_nat_mul]
      apply congrArg Real.exp
      ring
    rw [hexp]
    simpa only [M, C, mul_assoc] using hbound

/-- Exact positive Fisher-tail bound for a finite escort with supplied top data `(RPC.14)`. -/
theorem integral_Ioi_sqrt_finiteTiltVariance_le {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta R T : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hR : ∀ x, |r x - rTop| ≤ R) (hdelta : 0 < delta) (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Ioi T, √(finiteTiltVariance w r t)) ≤
      2 * R * √((1 - ∑ x with r x = rTop, w x) /
        (∑ x with r x = rTop, w x)) / delta *
          Real.exp (-delta * T / 2) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  let C : ℝ := (1 - M) / M
  let K : ℝ := R * √C
  have hM1 : M ≤ 1 := finiteTopWeight_le_one hw hsum rTop
  have hM : 0 < M := by simpa only [M] using hTop
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hM1) hM.le
  have hTopSet : (Finset.univ.filter fun x => r x = rTop).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hTop
    simp at hTop
  obtain ⟨x, _⟩ := hTopSet
  have hR0 : 0 ≤ R := (abs_nonneg (r x - rTop)).trans (hR x)
  have hK : 0 ≤ K := mul_nonneg hR0 (Real.sqrt_nonneg _)
  have hpoint : ∀ t ∈ Set.Ioi T,
      √(finiteTiltVariance w r t) ≤ K * Real.exp (-(delta / 2 * t)) := by
    intro t ht
    have h := sqrt_finiteTiltVariance_le_topGap_exp hw hsum hTop hgap hR
      (hT.trans ht.le)
    have hexp : -(delta / 2 * t) = -delta * t / 2 := by ring
    rw [hexp]
    simpa only [M, C, K] using h
  have hExpInt : IntegrableOn (fun t : ℝ => Real.exp (-(delta / 2 * t)))
      (Set.Ioi T) := integrableOn_exp_neg_mul_Ioi (half_pos hdelta) T
  have hDomInt : IntegrableOn (fun t : ℝ => K * Real.exp (-(delta / 2 * t)))
      (Set.Ioi T) := hExpInt.const_mul K
  have hFCont : Continuous (fun t : ℝ => √(finiteTiltVariance w r t)) :=
    Real.continuous_sqrt.comp (continuous_finiteTiltVariance hw hsum)
  have hFInt : IntegrableOn (fun t : ℝ => √(finiteTiltVariance w r t))
      (Set.Ioi T) := by
    change Integrable (fun t : ℝ => √(finiteTiltVariance w r t))
      (volume.restrict (Set.Ioi T))
    change Integrable (fun t : ℝ => K * Real.exp (-(delta / 2 * t)))
      (volume.restrict (Set.Ioi T)) at hDomInt
    apply hDomInt.mono hFCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (Real.exp_pos _).le)]
    exact hpoint t ht
  calc
    (∫ t : ℝ in Set.Ioi T, √(finiteTiltVariance w r t)) ≤
        ∫ t : ℝ in Set.Ioi T, K * Real.exp (-(delta / 2 * t)) :=
      MeasureTheory.setIntegral_mono_on hFInt hDomInt measurableSet_Ioi hpoint
    _ = K * (Real.exp (-(delta / 2 * T)) / (delta / 2)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_exp_neg_mul_Ioi (half_pos hdelta) T]
    _ = 2 * R * √((1 - ∑ x with r x = rTop, w x) /
          (∑ x with r x = rTop, w x)) / delta *
          Real.exp (-delta * T / 2) := by
      dsimp only [K, C, M]
      rw [show -(delta / 2 * T) = -delta * T / 2 by ring]
      conv_lhs =>
        rhs
        rw [div_eq_mul_inv, inv_div]
      ring

/-- Positive square-root Fisher response is integrable under supplied top-gap data. -/
theorem integrableOn_Ioi_sqrt_finiteTiltVariance {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta R T : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hR : ∀ x, |r x - rTop| ≤ R) (hdelta : 0 < delta) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => √(finiteTiltVariance w r t)) (Set.Ioi T) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  let C : ℝ := (1 - M) / M
  let K : ℝ := R * √C
  have hTopSet : (Finset.univ.filter fun x => r x = rTop).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hTop
    simp at hTop
  obtain ⟨x, _⟩ := hTopSet
  have hR0 : 0 ≤ R := (abs_nonneg (r x - rTop)).trans (hR x)
  have hK : 0 ≤ K := mul_nonneg hR0 (Real.sqrt_nonneg _)
  have hpoint : ∀ t ∈ Set.Ioi T,
      √(finiteTiltVariance w r t) ≤ K * Real.exp (-(delta / 2 * t)) := by
    intro t ht
    have h := sqrt_finiteTiltVariance_le_topGap_exp hw hsum hTop hgap hR
      (hT.trans ht.le)
    have hexp : -(delta / 2 * t) = -delta * t / 2 := by ring
    rw [hexp]
    simpa only [M, C, K] using h
  have hExpInt : IntegrableOn (fun t : ℝ => Real.exp (-(delta / 2 * t)))
      (Set.Ioi T) := integrableOn_exp_neg_mul_Ioi (half_pos hdelta) T
  have hDomInt : IntegrableOn (fun t : ℝ => K * Real.exp (-(delta / 2 * t)))
      (Set.Ioi T) := hExpInt.const_mul K
  change Integrable (fun t : ℝ => √(finiteTiltVariance w r t))
    (volume.restrict (Set.Ioi T))
  change Integrable (fun t : ℝ => K * Real.exp (-(delta / 2 * t)))
    (volume.restrict (Set.Ioi T)) at hDomInt
  apply hDomInt.mono
    (Real.continuous_sqrt.comp (continuous_finiteTiltVariance hw hsum)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change |√(finiteTiltVariance w r t)| ≤ |K * Real.exp (-(delta / 2 * t))|
  rw [abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (mul_nonneg hK (Real.exp_pos _).le)]
  exact hpoint t ht

private lemma finiteExpPartition_neg_score {n : ℕ} (w r : Fin n → ℝ) (t : ℝ) :
    finiteExpPartition w (fun x => -r x) t = finiteExpPartition w r (-t) := by
  unfold finiteExpPartition
  apply Finset.sum_congr rfl
  intro x _
  rw [show t * -r x = -t * r x by ring]

private lemma finiteExponentialTilt_neg_score {n : ℕ} (w r : Fin n → ℝ)
    (t : ℝ) (x : Fin n) :
    finiteExponentialTilt w (fun y => -r y) t x =
      finiteExponentialTilt w r (-t) x := by
  unfold finiteExponentialTilt
  rw [finiteExpPartition_neg_score]
  rw [show t * -r x = -t * r x by ring]

private lemma finiteTiltMean_neg_score {n : ℕ} (w r : Fin n → ℝ) (t : ℝ) :
    finiteTiltMean w (fun x => -r x) t = -finiteTiltMean w r (-t) := by
  unfold finiteTiltMean
  calc
    (∑ x, finiteExponentialTilt w (fun y => -r y) t x * -r x) =
        ∑ x, -(finiteExponentialTilt w r (-t) x * r x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [finiteExponentialTilt_neg_score]
      ring
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- Score and parameter reflection preserve finite-escort Fisher response. -/
theorem finiteTiltVariance_neg_score {n : ℕ} (w r : Fin n → ℝ) (t : ℝ) :
    finiteTiltVariance w (fun x => -r x) t = finiteTiltVariance w r (-t) := by
  unfold finiteTiltVariance
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteExponentialTilt_neg_score, finiteTiltMean_neg_score]
  ring

private theorem setIntegral_Iio_neg_endpoint (f : ℝ → ℝ) (T : ℝ) :
    (∫ s in Set.Iio (-T), f s) = ∫ v in Set.Ioi T, f (-v) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding f (Set.Iio (-T))
  simpa [show (fun v : ℝ => -v) ⁻¹' Set.Iio (-T) = Set.Ioi T by
    ext v
    simp] using h.symm

/-- Exact negative Fisher-tail bound for supplied bottom data `(RPC.14)`. -/
theorem integral_Iio_sqrt_finiteTiltVariance_le {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rBottom delta R T : ℝ}
    (hBottom : 0 < ∑ x with r x = rBottom, w x)
    (hgap : ∀ x, r x ≠ rBottom → delta ≤ r x - rBottom)
    (hR : ∀ x, |r x - rBottom| ≤ R) (hdelta : 0 < delta) (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Iio (-T), √(finiteTiltVariance w r t)) ≤
      2 * R * √((1 - ∑ x with r x = rBottom, w x) /
        (∑ x with r x = rBottom, w x)) / delta *
          Real.exp (-delta * T / 2) := by
  have hTop : 0 < ∑ x with -r x = -rBottom, w x := by simpa using hBottom
  have hgap' : ∀ x, -r x ≠ -rBottom → delta ≤ -rBottom - -r x := by
    intro x hx
    have hx' : r x ≠ rBottom := by simpa using hx
    rw [show -rBottom - -r x = r x - rBottom by ring]
    exact hgap x hx'
  have hR' : ∀ x, |-r x - -rBottom| ≤ R := by
    intro x
    rw [show -r x - -rBottom = -(r x - rBottom) by ring, abs_neg]
    exact hR x
  have h := integral_Ioi_sqrt_finiteTiltVariance_le
    (w := w) (r := fun x => -r x) hw hsum hTop hgap' hR' hdelta hT
  rw [setIntegral_Iio_neg_endpoint]
  simpa only [finiteTiltVariance_neg_score, neg_inj] using h

/-! ## Canonical finite-score boundary data -/

/-- Maximum score on a nonempty finite state space. -/
noncomputable def finiteTopScore {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty r

/-- Minimum score on a nonempty finite state space. -/
noncomputable def finiteBottomScore {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty r

/-- Exact score range `r₊ - r₋`. -/
noncomputable def finiteScoreRange {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) : ℝ :=
  finiteTopScore r - finiteBottomScore r

/-- Total source weight on the maximum-score fibre. -/
noncomputable def finiteTopWeight {n : ℕ} [Nonempty (Fin n)]
    (w r : Fin n → ℝ) : ℝ :=
  ∑ x with r x = finiteTopScore r, w x

/-- Total source weight on the minimum-score fibre. -/
noncomputable def finiteBottomWeight {n : ℕ} [Nonempty (Fin n)]
    (w r : Fin n → ℝ) : ℝ :=
  ∑ x with r x = finiteBottomScore r, w x

/-- Canonical positive gap below the top score; zero only when the off-top fibre is empty. -/
noncomputable def finiteTopGap {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) : ℝ :=
  let offTop := Finset.univ.filter fun x => r x ≠ finiteTopScore r
  if h : offTop.Nonempty then
    offTop.inf' h fun x => finiteTopScore r - r x
  else 0

/-- Canonical positive gap above the bottom score; zero only when the off-bottom fibre is empty. -/
noncomputable def finiteBottomGap {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) : ℝ :=
  let offBottom := Finset.univ.filter fun x => r x ≠ finiteBottomScore r
  if h : offBottom.Nonempty then
    offBottom.inf' h fun x => r x - finiteBottomScore r
  else 0

lemma finiteBottomScore_le {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) (x : Fin n) :
    finiteBottomScore r ≤ r x := by
  exact Finset.inf'_le r (Finset.mem_univ x)

lemma le_finiteTopScore {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) (x : Fin n) :
    r x ≤ finiteTopScore r := by
  exact Finset.le_sup' r (Finset.mem_univ x)

lemma exists_eq_finiteTopScore {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) :
    ∃ x, r x = finiteTopScore r := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty r
  exact ⟨x, hx.symm⟩

lemma exists_eq_finiteBottomScore {n : ℕ} [Nonempty (Fin n)] (r : Fin n → ℝ) :
    ∃ x, r x = finiteBottomScore r := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty r
  exact ⟨x, hx.symm⟩

private lemma finiteOffTop_nonempty_of_nonconstant {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) :
    (Finset.univ.filter fun x => r x ≠ finiteTopScore r).Nonempty := by
  by_contra hempty
  have hall : ∀ x, r x = finiteTopScore r := by
    intro x
    by_contra hx
    exact hempty ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨i, j, hij⟩ := hvar
  exact hij ((hall i).trans (hall j).symm)

private lemma finiteOffBottom_nonempty_of_nonconstant {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) :
    (Finset.univ.filter fun x => r x ≠ finiteBottomScore r).Nonempty := by
  by_contra hempty
  have hall : ∀ x, r x = finiteBottomScore r := by
    intro x
    by_contra hx
    exact hempty ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨i, j, hij⟩ := hvar
  exact hij ((hall i).trans (hall j).symm)

lemma finiteTopGap_pos_of_nonconstant {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) : 0 < finiteTopGap r := by
  let offTop := Finset.univ.filter fun x => r x ≠ finiteTopScore r
  have hoff : offTop.Nonempty := finiteOffTop_nonempty_of_nonconstant hvar
  rw [finiteTopGap, dif_pos hoff]
  obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf' hoff
    (fun x => finiteTopScore r - r x)
  rw [heq]
  rw [Finset.mem_filter] at hx
  exact sub_pos.mpr (lt_of_le_of_ne (le_finiteTopScore r x) hx.2)

lemma finiteBottomGap_pos_of_nonconstant {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) : 0 < finiteBottomGap r := by
  let offBottom := Finset.univ.filter fun x => r x ≠ finiteBottomScore r
  have hoff : offBottom.Nonempty := finiteOffBottom_nonempty_of_nonconstant hvar
  rw [finiteBottomGap, dif_pos hoff]
  obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf' hoff
    (fun x => r x - finiteBottomScore r)
  rw [heq]
  rw [Finset.mem_filter] at hx
  exact sub_pos.mpr (lt_of_le_of_ne (finiteBottomScore_le r x) (Ne.symm hx.2))

lemma finiteTopGap_le_sub {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) (x : Fin n)
    (hx : r x ≠ finiteTopScore r) :
    finiteTopGap r ≤ finiteTopScore r - r x := by
  let offTop := Finset.univ.filter fun y => r y ≠ finiteTopScore r
  have hoff : offTop.Nonempty := finiteOffTop_nonempty_of_nonconstant hvar
  rw [finiteTopGap, dif_pos hoff]
  exact Finset.inf'_le (fun y => finiteTopScore r - r y)
    (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)

lemma finiteBottomGap_le_sub {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) (x : Fin n)
    (hx : r x ≠ finiteBottomScore r) :
    finiteBottomGap r ≤ r x - finiteBottomScore r := by
  let offBottom := Finset.univ.filter fun y => r y ≠ finiteBottomScore r
  have hoff : offBottom.Nonempty := finiteOffBottom_nonempty_of_nonconstant hvar
  rw [finiteBottomGap, dif_pos hoff]
  exact Finset.inf'_le (fun y => r y - finiteBottomScore r)
    (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)

lemma finiteScoreRange_pos_of_nonconstant {n : ℕ} [Nonempty (Fin n)]
    {r : Fin n → ℝ} (hvar : ∃ i j, r i ≠ r j) : 0 < finiteScoreRange r := by
  by_contra hR
  have hEq : finiteTopScore r = finiteBottomScore r := by
    have hle : finiteTopScore r ≤ finiteBottomScore r := by
      simpa only [finiteScoreRange, not_lt, sub_nonpos] using hR
    exact le_antisymm hle ((finiteBottomScore_le r (Classical.choice inferInstance)).trans
      (le_finiteTopScore r (Classical.choice inferInstance)))
  obtain ⟨i, j, hij⟩ := hvar
  have hi : r i = finiteTopScore r := le_antisymm (le_finiteTopScore r i)
    (hEq.symm ▸ finiteBottomScore_le r i)
  have hj : r j = finiteTopScore r := le_antisymm (le_finiteTopScore r j)
    (hEq.symm ▸ finiteBottomScore_le r j)
  exact hij (hi.trans hj.symm)

lemma abs_sub_finiteTopScore_le_range {n : ℕ} [Nonempty (Fin n)]
    (r : Fin n → ℝ) (x : Fin n) :
    |r x - finiteTopScore r| ≤ finiteScoreRange r := by
  rw [abs_of_nonpos (sub_nonpos.mpr (le_finiteTopScore r x))]
  unfold finiteScoreRange
  linarith [finiteBottomScore_le r x]

lemma abs_sub_finiteBottomScore_le_range {n : ℕ} [Nonempty (Fin n)]
    (r : Fin n → ℝ) (x : Fin n) :
    |r x - finiteBottomScore r| ≤ finiteScoreRange r := by
  rw [abs_of_nonneg (sub_nonneg.mpr (finiteBottomScore_le r x))]
  unfold finiteScoreRange
  linarith [le_finiteTopScore r x]

lemma finiteTopWeight_pos {n : ℕ} [Nonempty (Fin n)] {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) : 0 < finiteTopWeight w r := by
  obtain ⟨x, hx⟩ := exists_eq_finiteTopScore r
  unfold finiteTopWeight
  exact Finset.sum_pos' (fun y _ => (hw y).le)
    ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩, hw x⟩

lemma finiteBottomWeight_pos {n : ℕ} [Nonempty (Fin n)] {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) : 0 < finiteBottomWeight w r := by
  obtain ⟨x, hx⟩ := exists_eq_finiteBottomScore r
  unfold finiteBottomWeight
  exact Finset.sum_pos' (fun y _ => (hw y).le)
    ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩, hw x⟩

/-- Canonical positive Fisher-tail estimate using `r₊, R, w₊, Δ₊` from `(RPC.10)`. -/
theorem finiteEscort_positiveFisherTail_le {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Ioi T, √(finiteTiltVariance w r t)) ≤
      2 * finiteScoreRange r * √((1 - finiteTopWeight w r) / finiteTopWeight w r) /
        finiteTopGap r * Real.exp (-finiteTopGap r * T / 2) := by
  exact integral_Ioi_sqrt_finiteTiltVariance_le (fun x => (hw x).le) hsum
    (finiteTopWeight_pos hw) (finiteTopGap_le_sub hvar)
    (abs_sub_finiteTopScore_le_range r) (finiteTopGap_pos_of_nonconstant hvar) hT

/-- Canonical negative Fisher-tail estimate using `r₋, R, w₋, Δ₋` from `(RPC.10)`. -/
theorem finiteEscort_negativeFisherTail_le {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in Set.Iio (-T), √(finiteTiltVariance w r t)) ≤
      2 * finiteScoreRange r * √((1 - finiteBottomWeight w r) / finiteBottomWeight w r) /
        finiteBottomGap r * Real.exp (-finiteBottomGap r * T / 2) := by
  exact integral_Iio_sqrt_finiteTiltVariance_le (fun x => (hw x).le) hsum
    (finiteBottomWeight_pos hw) (finiteBottomGap_le_sub hvar)
    (abs_sub_finiteBottomScore_le_range r) (finiteBottomGap_pos_of_nonconstant hvar) hT

/-- Complete nonconstant finite-escort curve has finite total Fisher length. -/
theorem finiteEscort_fisherResponse_integrable {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Integrable (fun t : ℝ => √(finiteTiltVariance w r t)) volume := by
  have hpos : IntegrableOn (fun t : ℝ => √(finiteTiltVariance w r t))
      (Set.Ioi 0) :=
    integrableOn_Ioi_sqrt_finiteTiltVariance (fun x => (hw x).le) hsum
      (finiteTopWeight_pos hw) (finiteTopGap_le_sub hvar)
      (abs_sub_finiteTopScore_le_range r) (finiteTopGap_pos_of_nonconstant hvar) le_rfl
  have hbottom : 0 < ∑ x with -r x = -finiteBottomScore r, w x := by
    simpa only [finiteBottomWeight, neg_inj] using
      finiteBottomWeight_pos (w := w) (r := r) hw
  have hgap : ∀ x, -r x ≠ -finiteBottomScore r →
      finiteBottomGap r ≤ -finiteBottomScore r - -r x := by
    intro x hx
    rw [show -finiteBottomScore r - -r x = r x - finiteBottomScore r by ring]
    exact finiteBottomGap_le_sub hvar x (by simpa using hx)
  have hR : ∀ x, |-r x - -finiteBottomScore r| ≤ finiteScoreRange r := by
    intro x
    rw [show -r x - -finiteBottomScore r = -(r x - finiteBottomScore r) by ring,
      abs_neg]
    exact abs_sub_finiteBottomScore_le_range r x
  have hnegRef : IntegrableOn
      (fun t : ℝ => √(finiteTiltVariance w (fun x => -r x) t)) (Set.Ioi 0) :=
    integrableOn_Ioi_sqrt_finiteTiltVariance (fun x => (hw x).le) hsum
      hbottom hgap hR (finiteBottomGap_pos_of_nonconstant hvar) le_rfl
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have hiff := hmp.integrableOn_comp_preimage hme
    (f := fun t : ℝ => √(finiteTiltVariance w (fun x => -r x) t))
    (s := Set.Ioi (0 : ℝ))
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
    ext x
    simp
  rw [hpre] at hiff
  have hnegReflected := hiff.mpr hnegRef
  have hneg : IntegrableOn (fun t : ℝ => √(finiteTiltVariance w r t))
      (Set.Iio 0) := by
    convert hnegReflected using 1
    funext t
    change √(finiteTiltVariance w r t) =
      √(finiteTiltVariance w (fun x => -r x) (-t))
    rw [finiteTiltVariance_neg_score]
    simp
  have hposIci : IntegrableOn (fun t : ℝ => √(finiteTiltVariance w r t))
      (Set.Ici 0) := (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos
  have hall := hneg.union hposIci
  rw [Set.Iio_union_Ici] at hall
  change Integrable (fun t : ℝ => √(finiteTiltVariance w r t))
    (volume.restrict Set.univ) at hall
  simpa only [Measure.restrict_univ] using hall

/-- Distance of the tilted mean from a supplied top score is range times off-top mass. -/
theorem abs_finiteTiltMean_sub_top_le {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop R t : ℝ} (hmax : ∀ x, r x ≤ rTop)
    (hR : ∀ x, |r x - rTop| ≤ R) :
    |finiteTiltMean w r t - rTop| ≤ R * finiteTiltOffTopMass w r rTop t := by
  have hprob := finiteExponentialTilt_sum (r := r) hw hsum t
  have hMeanLe : finiteTiltMean w r t ≤ rTop := by
    unfold finiteTiltMean
    calc
      (∑ x, finiteExponentialTilt w r t x * r x) ≤
          ∑ x, finiteExponentialTilt w r t x * rTop := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hmax x)
          (finiteExponentialTilt_nonneg hw hsum t x)
      _ = rTop := by rw [← Finset.sum_mul, hprob, one_mul]
  rw [abs_of_nonpos (sub_nonpos.mpr hMeanLe), neg_sub]
  have herror : rTop - finiteTiltMean w r t =
      ∑ x, finiteExponentialTilt w r t x * (rTop - r x) := by
    unfold finiteTiltMean
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hprob]
    ring
  rw [herror]
  classical
  unfold finiteTiltOffTopMass
  rw [Finset.mul_sum]
  calc
    (∑ x, finiteExponentialTilt w r t x * (rTop - r x)) =
        ∑ x, if r x ≠ rTop then
          finiteExponentialTilt w r t x * (rTop - r x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs with hx
      · rfl
      · simp [not_ne_iff.mp hx]
    _ ≤ ∑ x, if r x ≠ rTop then
          R * finiteExponentialTilt w r t x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · have hdist : rTop - r x ≤ R := by
          rw [show rTop - r x = |r x - rTop| by
            rw [abs_of_nonpos (sub_nonpos.mpr (hmax x))]
            ring]
          exact hR x
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdist
          (finiteExponentialTilt_nonneg hw hsum t x)
      · exact le_rfl
    _ = ∑ x with r x ≠ rTop,
          R * finiteExponentialTilt w r t x := by rw [Finset.sum_filter]

/-- Supplied top data force convergence of the finite-escort mean to the top score. -/
theorem tendsto_finiteTiltMean_atTop {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta R : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hmax : ∀ x, r x ≤ rTop)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hR : ∀ x, |r x - rTop| ≤ R) (hdelta : 0 < delta) :
    Tendsto (finiteTiltMean w r) atTop (𝓝 rTop) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  let C : ℝ := (1 - M) / M
  have hM1 : M ≤ 1 := finiteTopWeight_le_one hw hsum rTop
  have hM : 0 < M := by simpa only [M] using hTop
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hM1) hM.le
  have hTopSet : (Finset.univ.filter fun x => r x = rTop).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hTop
    simp at hTop
  obtain ⟨x, _⟩ := hTopSet
  have hR0 : 0 ≤ R := (abs_nonneg (r x - rTop)).trans (hR x)
  have hExp : Tendsto (fun t : ℝ => Real.exp (-(delta * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero hdelta
  have hDom : Tendsto (fun t : ℝ => R * C * Real.exp (-(delta * t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp.const_mul (R * C)
  have hErr : Tendsto (fun t : ℝ => |finiteTiltMean w r t - rTop|) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun t => abs_nonneg _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      calc
        |finiteTiltMean w r t - rTop| ≤
            R * finiteTiltOffTopMass w r rTop t :=
          abs_finiteTiltMean_sub_top_le hw hsum hmax hR
        _ ≤ R * (C * Real.exp (-delta * t)) := by
          exact mul_le_mul_of_nonneg_left
            (finiteTiltOffTopMass_le_exp hw hsum hTop hgap ht) hR0
        _ = R * C * Real.exp (-(delta * t)) := by
          rw [show -delta * t = -(delta * t) by ring, mul_assoc]
    · exact hDom
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Real.dist_eq] using hErr

/-- Canonical maximum-score boundary law for finite escorts `(RPC.19)`. -/
theorem finiteEscort_mean_tendsto_top {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Tendsto (finiteTiltMean w r) atTop (𝓝 (finiteTopScore r)) := by
  exact tendsto_finiteTiltMean_atTop (fun x => (hw x).le) hsum
    (finiteTopWeight_pos hw) (le_finiteTopScore r) (finiteTopGap_le_sub hvar)
    (abs_sub_finiteTopScore_le_range r) (finiteTopGap_pos_of_nonconstant hvar)

/-- Canonical minimum-score boundary law along the reflected parameter `(RPC.19)`. -/
theorem finiteEscort_mean_neg_tendsto_bottom {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Tendsto (fun t => finiteTiltMean w r (-t)) atTop (𝓝 (finiteBottomScore r)) := by
  have hvarNeg : ∃ i j, -r i ≠ -r j := by
    obtain ⟨i, j, hij⟩ := hvar
    exact ⟨i, j, fun h => hij (neg_injective h)⟩
  have h := finiteEscort_mean_tendsto_top (w := w) (r := fun x => -r x) hw hsum hvarNeg
  have hneg := h.neg
  convert hneg using 1
  · funext t
    rw [finiteTiltMean_neg_score]
    simp
  · simp only [finiteTopScore]
    have hbot_le : ∀ y, finiteBottomScore r ≤ r y := finiteBottomScore_le r
    have hxle : ∀ y, -r y ≤ -finiteBottomScore r := fun y => neg_le_neg (hbot_le y)
    have hEq : Finset.univ.sup' Finset.univ_nonempty (fun x => -r x) =
        -finiteBottomScore r := le_antisymm
      ((Finset.sup'_le_iff Finset.univ_nonempty (fun x => -r x)).2
        (fun y _ => hxle y))
      (by
        obtain ⟨y, hy⟩ := exists_eq_finiteBottomScore r
        simpa [hy] using Finset.le_sup' (fun x => -r x) (Finset.mem_univ y))
    rw [hEq]
    simp

/-- Supplied top-gap data force all tilted mass off the top fibre to vanish. -/
theorem tendsto_finiteTiltOffTopMass_atTop_zero {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    {rTop delta : ℝ}
    (hTop : 0 < ∑ x with r x = rTop, w x)
    (hgap : ∀ x, r x ≠ rTop → delta ≤ rTop - r x)
    (hdelta : 0 < delta) :
    Tendsto (finiteTiltOffTopMass w r rTop) atTop (𝓝 0) := by
  let M : ℝ := ∑ x with r x = rTop, w x
  let C : ℝ := (1 - M) / M
  have hM1 : M ≤ 1 := finiteTopWeight_le_one hw hsum rTop
  have hM : 0 < M := by simpa only [M] using hTop
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hM1) hM.le
  have hExp : Tendsto (fun t : ℝ => Real.exp (-(delta * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_mul_atTop_nhds_zero hdelta
  have hExp' : Tendsto (fun t : ℝ => Real.exp (-delta * t)) atTop (𝓝 0) := by
    have heq : (fun t : ℝ => Real.exp (-delta * t)) =
        fun t : ℝ => Real.exp (-(delta * t)) := by
      funext t
      apply congrArg Real.exp
      ring
    rw [heq]
    exact hExp
  have hDom : Tendsto (fun t : ℝ => C * Real.exp (-delta * t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp'.const_mul C
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => Finset.sum_nonneg fun x _ =>
      finiteExponentialTilt_nonneg hw hsum t x
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa only [M, C] using finiteTiltOffTopMass_le_exp hw hsum hTop hgap ht
  · simpa only [M, C] using hDom

/-- Tilted mass outside a prescribed bottom-score fibre. -/
noncomputable def finiteTiltOffBottomMass {n : ℕ} (w r : Fin n → ℝ)
    (rBottom t : ℝ) : ℝ :=
  ∑ x with r x ≠ rBottom, finiteExponentialTilt w r t x

private lemma finiteTiltOffTopMass_neg_score {n : ℕ} (w r : Fin n → ℝ)
    (rBottom t : ℝ) :
    finiteTiltOffTopMass w (fun x => -r x) (-rBottom) t =
      finiteTiltOffBottomMass w r rBottom (-t) := by
  unfold finiteTiltOffTopMass finiteTiltOffBottomMass
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    exact finiteExponentialTilt_neg_score w r t x

/-- Canonical escort law converges to the maximum-score boundary fibre. -/
theorem finiteEscort_offTopMass_tendsto_zero {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Tendsto (finiteTiltOffTopMass w r (finiteTopScore r)) atTop (𝓝 0) := by
  exact tendsto_finiteTiltOffTopMass_atTop_zero (fun x => (hw x).le) hsum
    (finiteTopWeight_pos hw) (finiteTopGap_le_sub hvar)
    (finiteTopGap_pos_of_nonconstant hvar)

/-- Canonical escort law converges along reflection to the minimum-score boundary fibre. -/
theorem finiteEscort_offBottomMass_neg_tendsto_zero {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Tendsto (fun t => finiteTiltOffBottomMass w r (finiteBottomScore r) (-t))
      atTop (𝓝 0) := by
  have htop : 0 < ∑ x with -r x = -finiteBottomScore r, w x := by
    simpa only [neg_inj, finiteBottomWeight] using finiteBottomWeight_pos (w := w) (r := r) hw
  have hgap : ∀ x, -r x ≠ -finiteBottomScore r →
      finiteBottomGap r ≤ -finiteBottomScore r - -r x := by
    intro x hx
    rw [show -finiteBottomScore r - -r x = r x - finiteBottomScore r by ring]
    exact finiteBottomGap_le_sub hvar x (by simpa using hx)
  have h := tendsto_finiteTiltOffTopMass_atTop_zero (w := w) (r := fun x => -r x)
    (fun x => (hw x).le) hsum htop hgap (finiteBottomGap_pos_of_nonconstant hvar)
  have hfun : finiteTiltOffTopMass w (fun x => -r x) (-finiteBottomScore r) =
      fun t => finiteTiltOffBottomMass w r (finiteBottomScore r) (-t) := by
    funext t
    exact finiteTiltOffTopMass_neg_score w r (finiteBottomScore r) t
  rw [hfun] at h
  exact h

/-- Every positive Jeffreys tail of a nonconstant finite escort has infinite diameter `(RPC.15)`. -/
theorem finiteTiltJeffreys_positiveTail_unbounded {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    ∀ T B : ℝ, ∃ a b : ℝ, T ≤ a ∧ a ≤ b ∧ B < finiteTiltJeffreysReal w r a b := by
  intro T B
  let d : ℝ := finiteTiltMean w r (T + 1) - finiteTiltMean w r T
  have hd : 0 < d := by
    exact sub_pos.mpr (finiteTiltMean_strictMono hw hsum hvar (by linarith))
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 (B / d))
  let b : ℝ := T + n
  have hn1 : (1 : ℝ) ≤ n := (le_max_left 1 (B / d)).trans hn.le
  have hnB : B < (n : ℝ) * d := by
    exact (div_lt_iff₀ hd).mp ((le_max_right 1 (B / d)).trans_lt hn)
  have hTb : T ≤ b := by dsimp [b]; exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hMean : finiteTiltMean w r (T + 1) ≤ finiteTiltMean w r b :=
    (finiteTiltMean_strictMono hw hsum hvar).monotone (by dsimp [b]; linarith)
  refine ⟨T, b, le_rfl, hTb, ?_⟩
  rw [finiteTiltJeffreysReal_eq hw hsum]
  dsimp only [b, d] at hnB hMean ⊢
  nlinarith

/-- Every negative Jeffreys tail of a nonconstant finite escort has infinite diameter `(RPC.15)`. -/
theorem finiteTiltJeffreys_negativeTail_unbounded {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    ∀ T B : ℝ, ∃ a b : ℝ, a ≤ b ∧ b ≤ -T ∧ B < finiteTiltJeffreysReal w r a b := by
  intro T B
  let d : ℝ := finiteTiltMean w r (-T) - finiteTiltMean w r (-T - 1)
  have hd : 0 < d := by
    exact sub_pos.mpr (finiteTiltMean_strictMono hw hsum hvar (by linarith))
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 (B / d))
  let a : ℝ := -T - n
  have hn1 : (1 : ℝ) ≤ n := (le_max_left 1 (B / d)).trans hn.le
  have hnB : B < (n : ℝ) * d := by
    exact (div_lt_iff₀ hd).mp ((le_max_right 1 (B / d)).trans_lt hn)
  have haT : a ≤ -T := by
    dsimp [a]
    exact sub_le_self (-T) (Nat.cast_nonneg n)
  have hMean : finiteTiltMean w r a ≤ finiteTiltMean w r (-T - 1) :=
    (finiteTiltMean_strictMono hw hsum hvar).monotone (by dsimp [a]; linarith)
  refine ⟨a, -T, haT, le_rfl, ?_⟩
  rw [finiteTiltJeffreysReal_eq hw hsum]
  dsimp only [a, d] at hnB hMean ⊢
  nlinarith

/-- Reflected Jeffreys work divided by diameter converges exactly to score range `(RPC.16)`. -/
theorem finiteTiltJeffreys_reflection_div_tendsto_range {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    Tendsto (fun t : ℝ => finiteTiltJeffreysReal w r t (-t) / (2 * t))
      atTop (𝓝 (finiteScoreRange r)) := by
  have hdiff := (finiteEscort_mean_tendsto_top hw hsum hvar).sub
    (finiteEscort_mean_neg_tendsto_bottom hw hsum hvar)
  have heq : ∀ᶠ t : ℝ in atTop,
      finiteTiltJeffreysReal w r t (-t) / (2 * t) =
        finiteTiltMean w r t - finiteTiltMean w r (-t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [finiteTiltJeffreysReal_reflection_eq hw hsum]
    unfold finiteReflectedTiltWork
    apply (div_eq_iff (mul_ne_zero (by norm_num) ht.ne')).2
    ring
  have hlim : Tendsto
      (fun t => finiteTiltMean w r t - finiteTiltMean w r (-t)) atTop
      (𝓝 (finiteScoreRange r)) := by
    simpa only [finiteScoreRange] using hdiff
  exact hlim.congr' (Filter.EventuallyEq.symm heq)

/-- Finite escort mean differentiates by a strictly positive Fisher response `(RPC.11)`. -/
theorem finiteEscort_mean_deriv_variance_pos {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) (t : ℝ) :
    HasDerivAt (finiteTiltMean w r) (finiteTiltVariance w r t) t ∧
      0 < finiteTiltVariance w r t :=
  ⟨hasDerivAt_finiteTiltMean (fun x => (hw x).le) hsum t,
    finiteTiltVariance_pos hw hsum hvar t⟩

/-- Every nonconstant finite escort has collapsing Fisher-length tails. -/
theorem finiteEscort_responseLengthTailCollapses {n : ℕ} [Nonempty (Fin n)]
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    ResponseLengthTailCollapses (finiteTiltVariance w r) := by
  apply responseLengthTailCollapses_of_integrableOn_Ici (T₀ := 0)
    (continuous_finiteTiltVariance (fun x => (hw x).le) hsum)
    (fun t => finiteTiltVariance_nonneg (fun x => (hw x).le) hsum t)
  exact (finiteEscort_fisherResponse_integrable hw hsum hvar).integrableOn

/-- Every nonconstant finite escort has unbounded positive reciprocal-work tails. -/
theorem finiteEscort_responseWorkTailUnbounded {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) :
    ResponseWorkTailUnbounded (finiteTiltVariance w r) := by
  have hcont := continuous_finiteTiltVariance (r := r) (fun x => (hw x).le) hsum
  have hnonneg := fun t => finiteTiltVariance_nonneg (r := r)
    (fun x => (hw x).le) hsum t
  apply responseWorkTailUnbounded_of_positive_tail hcont hnonneg
  intro T
  refine ⟨T + 1, by linarith, ?_⟩
  apply RHTower.intervalIntegral_pos_of_continuous_nonneg_of_exists_pos hcont
  · exact fun t _ => hnonneg t
  · refine ⟨T + 1 / 2, by constructor <;> linarith,
      finiteTiltVariance_pos hw hsum hvar (T + 1 / 2)⟩

/-- A faithful response coordinate is selected exactly by bounded complete reflected work. -/
theorem boundedReflectedResponseWork_iff_coordinate_eq_zero
    {Q : Type*} [Zero Q] (I : Q → ℝ → ℝ)
    (hI : ∀ q, Continuous (I q)) (hI0 : ∀ q t, 0 ≤ I q t)
    (hfaithful : ∀ q, (∀ t, I q t = 0) ↔ q = 0) (q : Q) :
    BoundedReflectedResponseWork (I q) ↔ q = 0 := by
  rw [boundedReflectedResponseWork_iff (hI q) (hI0 q)]
  exact hfaithful q

/-! ## Common recovery and observer deficit -/

/-- Extended-real Jeffreys information of two measures. -/
noncomputable def measureJeffreys {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) : ℝ≥0∞ :=
  klDiv μ ν + klDiv ν μ

/-- A parameter-independent Markov recovery preserves Jeffreys information exactly `(RPC.24)`. -/
theorem commonRecovery_measureJeffreys {X H : Type*}
    [MeasurableSpace X] [MeasurableSpace H]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X H) [IsMarkovKernel K] :
    measureJeffreys (μ ⊗ₘ K) (ν ⊗ₘ K) = measureJeffreys μ ν := by
  unfold measureJeffreys
  rw [commonRecovery_klDiv ν μ K, commonRecovery_klDiv μ ν K]

/-- Common recovery preserves every finite-difference local-response quotient. -/
theorem commonRecovery_localResponseQuotient_eq {X H : Type*}
    [MeasurableSpace X] [MeasurableSpace H]
    (μ : ℝ → Measure X) (hprob : ∀ t, IsProbabilityMeasure (μ t))
    (K : Kernel X H) [IsMarkovKernel K] (t h : ℝ) :
    (measureJeffreys (μ t ⊗ₘ K) (μ (t + h) ⊗ₘ K)).toReal / h ^ 2 =
      (measureJeffreys (μ t) (μ (t + h))).toReal / h ^ 2 := by
  letI := hprob t
  letI := hprob (t + h)
  rw [commonRecovery_measureJeffreys]

/-- Consequently every reconstructed local Fisher-response limit is recovery-invariant `(RPC.25)`. -/
theorem commonRecovery_localResponse_tendsto_iff {X H : Type*}
    [MeasurableSpace X] [MeasurableSpace H]
    (μ : ℝ → Measure X) (hprob : ∀ t, IsProbabilityMeasure (μ t))
    (K : Kernel X H) [IsMarkovKernel K] (t I : ℝ) :
    Tendsto (fun h : ℝ =>
      (measureJeffreys (μ t ⊗ₘ K) (μ (t + h) ⊗ₘ K)).toReal / h ^ 2)
        (𝓝[≠] 0) (𝓝 I) ↔
    Tendsto (fun h : ℝ =>
      (measureJeffreys (μ t) (μ (t + h))).toReal / h ^ 2)
        (𝓝[≠] 0) (𝓝 I) := by
  have hfun : (fun h : ℝ =>
      (measureJeffreys (μ t ⊗ₘ K) (μ (t + h) ⊗ₘ K)).toReal / h ^ 2) =
      fun h : ℝ => (measureJeffreys (μ t) (μ (t + h))).toReal / h ^ 2 := by
    funext h
    exact commonRecovery_localResponseQuotient_eq μ hprob K t h
  rw [hfun]

/-- Jeffreys information contracts under every measurable observer. -/
theorem measureJeffreys_map_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (g : X → Y) (hg : Measurable g) :
    measureJeffreys (μ.map g) (ν.map g) ≤ measureJeffreys μ ν := by
  unfold measureJeffreys
  exact add_le_add (klDiv_map_le_arbitrary μ ν g hg)
    (klDiv_map_le_arbitrary ν μ g hg)

/-- Limits of locally ordered work quotients retain their order. -/
theorem localResponse_le_of_work_le
    (observed complete : ℝ → ℝ → ℝ) (t IObserved IComplete : ℝ)
    (hObserved : Tendsto (fun h => observed t (t + h) / h ^ 2)
      (𝓝[≠] 0) (𝓝 IObserved))
    (hComplete : Tendsto (fun h => complete t (t + h) / h ^ 2)
      (𝓝[≠] 0) (𝓝 IComplete))
    (hle : ∀ h, observed t (t + h) ≤ complete t (t + h)) :
    IObserved ≤ IComplete := by
  apply le_of_tendsto_of_tendsto hObserved hComplete
  exact Filter.Eventually.of_forall fun h =>
    div_le_div_of_nonneg_right (hle h) (sq_nonneg h)

/-- Whenever observer and complete local Fisher responses exist, data processing gives `(RPC.27)`. -/
theorem measureJeffreys_map_localResponse_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ℝ → Measure X) (hprob : ∀ t, IsProbabilityMeasure (μ t))
    (g : X → Y) (hg : Measurable g) (t IObserved IComplete : ℝ)
    (hfinite : ∀ h, measureJeffreys (μ t) (μ (t + h)) ≠ ⊤)
    (hObserved : Tendsto (fun h =>
      (measureJeffreys ((μ t).map g) ((μ (t + h)).map g)).toReal / h ^ 2)
        (𝓝[≠] 0) (𝓝 IObserved))
    (hComplete : Tendsto (fun h =>
      (measureJeffreys (μ t) (μ (t + h))).toReal / h ^ 2)
        (𝓝[≠] 0) (𝓝 IComplete)) :
    IObserved ≤ IComplete := by
  apply le_of_tendsto_of_tendsto hObserved hComplete
  exact Filter.Eventually.of_forall fun h => by
    letI := hprob t
    letI := hprob (t + h)
    have hle := measureJeffreys_map_le (μ t) (μ (t + h)) g hg
    exact div_le_div_of_nonneg_right (ENNReal.toReal_mono (hfinite h) hle) (sq_nonneg h)

/-- Pointwise response contraction contracts every integrable Fisher-length region. -/
theorem setIntegral_sqrt_response_le {IObserved IComplete : ℝ → ℝ} {s : Set ℝ}
    (hObserved : IntegrableOn (fun t => √(IObserved t)) s)
    (hComplete : IntegrableOn (fun t => √(IComplete t)) s)
    (hs : MeasurableSet s) (hle : ∀ t ∈ s, IObserved t ≤ IComplete t) :
    (∫ t : ℝ in s, √(IObserved t)) ≤ ∫ t : ℝ in s, √(IComplete t) := by
  exact MeasureTheory.setIntegral_mono_on hObserved hComplete hs
    (fun t ht => Real.sqrt_le_sqrt (hle t ht))

/-- Complete Jeffreys work missing from an observer. -/
noncomputable def finiteEscortTailDeficit {n : ℕ} (w r : Fin n → ℝ)
    (observed : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  finiteTiltJeffreysReal w r a b - observed a b

/-- Data-processing domination makes observer deficit nonnegative. -/
theorem finiteEscortTailDeficit_nonneg {n : ℕ} (w r : Fin n → ℝ)
    (observed : ℝ → ℝ → ℝ) {a b : ℝ}
    (hle : observed a b ≤ finiteTiltJeffreysReal w r a b) :
    0 ≤ finiteEscortTailDeficit w r observed a b := by
  unfold finiteEscortTailDeficit
  linarith

/-- Bounded observed positive-tail work forces unbounded deficit escape `(RPC.29)`. -/
theorem finiteEscort_positiveTailDeficit_unbounded {n : ℕ} {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) (observed : ℝ → ℝ → ℝ)
    {T C : ℝ} (hObserved : ∀ a b, T ≤ a → a ≤ b → observed a b ≤ C) :
    ∀ B : ℝ, ∃ a b : ℝ, T ≤ a ∧ a ≤ b ∧
      B < finiteEscortTailDeficit w r observed a b := by
  intro B
  obtain ⟨a, b, ha, hab, hfull⟩ :=
    finiteTiltJeffreys_positiveTail_unbounded hw hsum hvar T (B + C)
  refine ⟨a, b, ha, hab, ?_⟩
  have hobs := hObserved a b ha hab
  unfold finiteEscortTailDeficit
  linarith

/-- Reflected complete work splits exactly into observed work and deficit `(RPC.29a)`. -/
theorem finiteEscort_reflectedWork_conservation {n : ℕ} (w r : Fin n → ℝ)
    (observed : ℝ → ℝ → ℝ) (T : ℝ) :
    finiteTiltJeffreysReal w r (-T) T = observed (-T) T +
      finiteEscortTailDeficit w r observed (-T) T := by
  unfold finiteEscortTailDeficit
  ring

/-- If reflected observed work and deficit are both bounded, score is constant. -/
theorem finiteEscort_boundedObservedAndDeficit_imp_constant {n : ℕ}
    {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (observed : ℝ → ℝ → ℝ) (C D : ℝ)
    (hObserved : ∀ k : ℕ, observed (-(k : ℝ)) k ≤ C)
    (hDeficit : ∀ k : ℕ,
      finiteEscortTailDeficit w r observed (-(k : ℝ)) k ≤ D) :
    ∀ i j, r i = r j := by
  apply (finiteTiltJeffreysReflection_bounded_iff_score_constant hw hsum).mp
  refine ⟨C + D, fun k => ?_⟩
  have hobs := hObserved k
  have hdef := hDeficit k
  unfold finiteEscortTailDeficit at hdef
  have hsym : finiteTiltJeffreysReal w r k (-k) =
      finiteTiltJeffreysReal w r (-k) k := by
    rw [finiteTiltJeffreysReal_eq hw hsum, finiteTiltJeffreysReal_eq hw hsum]
    ring
  rw [hsym]
  nlinarith

end

end GaloisForLFunctions.HTGeometry
