import GaloisForLFunctions.HTGeometry.FiniteBlaschkeBoundary
import GaloisForLFunctions.HTGeometry.HardyDiskBlaschke
import GaloisForLFunctions.HTGeometry.HardyMultiplierZeroModelDimension

open Complex Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard phase-normalized disk Blaschke factor. -/
def normalizedBlaschkeFactor (a z : ℂ) : ℂ :=
  if a = 0 then z else -((‖a‖ : ℂ) / a) * blaschkeFactor a z

theorem norm_normalizedBlaschkeFactor_le_one
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖normalizedBlaschkeFactor a z‖ ≤ 1 := by
  by_cases ha0 : a = 0
  · simpa [normalizedBlaschkeFactor, ha0] using hz
  rw [normalizedBlaschkeFactor, if_neg ha0]
  have hscale : ‖-((‖a‖ : ℂ) / a)‖ = 1 := by
    rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha0)]
  rw [norm_mul, hscale, one_mul]
  exact norm_blaschkeFactor_le_one ha hz

theorem normalizedBlaschkeFactor_self
    (a : ℂ) : normalizedBlaschkeFactor a a = 0 := by
  by_cases ha0 : a = 0
  · simp [normalizedBlaschkeFactor, ha0]
  rw [normalizedBlaschkeFactor, if_neg ha0, blaschkeFactor]
  simp

theorem differentiableOn_normalizedBlaschkeFactor
    {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (normalizedBlaschkeFactor a) (Metric.ball 0 1) := by
  by_cases ha0 : a = 0
  · subst a
    have hfun : normalizedBlaschkeFactor (0 : ℂ) = fun z => z := by
      funext z
      simp [normalizedBlaschkeFactor]
    rw [hfun]
    exact (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).differentiableOn
  have hfun : normalizedBlaschkeFactor a =
      fun z => -((‖a‖ : ℂ) / a) * blaschkeFactor a z := by
    funext z
    simp [normalizedBlaschkeFactor, ha0]
  rw [hfun]
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  apply DifferentiableAt.differentiableWithinAt
  have hc : DifferentiableAt ℂ (fun _ : ℂ => -((‖a‖ : ℂ) / a)) z :=
    differentiableAt_const _
  exact hc.mul (FiniteBlaschke.differentiableAt_blaschkeFactor
    (blaschke_denom_ne_zero (by nlinarith [norm_nonneg a, norm_nonneg z])))

private theorem conj_mul_eq_norm_cast_sq (a : ℂ) :
    (starRingEnd ℂ) a * a = (‖a‖ : ℂ) ^ 2 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem normalizedBlaschkeFactor_sub_one
    {a z : ℂ} (ha0 : a ≠ 0) (hden : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    normalizedBlaschkeFactor a z - 1 =
      (((‖a‖ : ℂ) - 1) *
        (1 + ((‖a‖ : ℂ) / a) * z)) /
          (1 - (starRingEnd ℂ) a * z) := by
  rw [normalizedBlaschkeFactor, if_neg ha0, blaschkeFactor]
  have hsq := conj_mul_eq_norm_cast_sq a
  have hconj : (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 / a :=
    (eq_div_iff ha0).2 hsq
  let d : ℂ := 1 - (starRingEnd ℂ) a * z
  have hd : d ≠ 0 := hden
  calc
    -((‖a‖ : ℂ) / a) * ((z - a) / d) - 1 =
        (-((‖a‖ : ℂ) / a) * (z - a)) / d - d / d := by
          rw [div_self hd]
          ring
    _ = (-((‖a‖ : ℂ) / a) * (z - a) - d) / d := by
      field_simp [hd]
    _ = (((‖a‖ : ℂ) - 1) * (1 + ((‖a‖ : ℂ) / a) * z)) / d := by
      congr 1
      dsimp only [d]
      rw [hconj]
      field_simp [ha0]
      ring

theorem norm_normalizedBlaschkeFactor_sub_one_le
    {a z : ℂ} (ha : ‖a‖ < 1)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (hz : ‖z‖ ≤ R) :
    ‖normalizedBlaschkeFactor a z - 1‖ ≤
      (2 / (1 - R)) * (1 - ‖a‖) := by
  by_cases ha0 : a = 0
  · subst a
    have hfrac : R + 1 ≤ 2 / (1 - R) := by
      apply (le_div_iff₀ (sub_pos.mpr hR1)).2
      nlinarith [sq_nonneg R]
    simp only [normalizedBlaschkeFactor, norm_zero, sub_zero, mul_one]
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
      _ ≤ R + 1 := by simpa using add_le_add_right hz 1
      _ ≤ 2 / (1 - R) := hfrac
  have haz : ‖a‖ * ‖z‖ < 1 := by
    calc
      ‖a‖ * ‖z‖ ≤ ‖a‖ * R :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right ha.le hR0
      _ < 1 := by simpa using hR1
  have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 := by
    apply blaschke_denom_ne_zero
    simpa [mul_comm] using haz
  rw [normalizedBlaschkeFactor_sub_one ha0 hden, norm_div, norm_mul]
  have hfirst : ‖((‖a‖ : ℂ) - 1)‖ = 1 - ‖a‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ha.le)]
    ring
  have hscale : ‖(‖a‖ : ℂ) / a‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg a), div_self (norm_ne_zero_iff.mpr ha0)]
  have hnum : ‖1 + ((‖a‖ : ℂ) / a) * z‖ ≤ 2 := by
    calc
      ‖1 + ((‖a‖ : ℂ) / a) * z‖ ≤ 1 + ‖((‖a‖ : ℂ) / a) * z‖ := by
        simpa using norm_add_le (1 : ℂ) (((‖a‖ : ℂ) / a) * z)
      _ = 1 + ‖z‖ := by rw [norm_mul, hscale, one_mul]
      _ ≤ 2 := by linarith
  have hdenLower : 1 - R ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) a * z)
    rw [norm_one, norm_mul, RCLike.norm_conj] at hrev
    have hazle : ‖a‖ * ‖z‖ ≤ R := by
      calc
        ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ :=
          mul_le_mul_of_nonneg_right ha.le (norm_nonneg z)
        _ ≤ R := by simpa using hz
    linarith
  have hdenPos : 0 < ‖1 - (starRingEnd ℂ) a * z‖ := norm_pos_iff.mpr hden
  have hRpos : 0 < 1 - R := sub_pos.mpr hR1
  rw [hfirst]
  calc
    (1 - ‖a‖) * ‖1 + ((‖a‖ : ℂ) / a) * z‖ /
        ‖1 - (starRingEnd ℂ) a * z‖
        ≤ (1 - ‖a‖) * 2 / ‖1 - (starRingEnd ℂ) a * z‖ := by
          gcongr
    _ ≤ (1 - ‖a‖) * 2 / (1 - R) := by
          exact div_le_div_of_nonneg_left
            (mul_nonneg (sub_nonneg.mpr ha.le) (by norm_num)) hRpos hdenLower
    _ = (2 / (1 - R)) * (1 - ‖a‖) := by ring

/-- Infinite phase-normalized Blaschke product for a sequence of disk points. -/
def infiniteBlaschkeProduct (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, normalizedBlaschkeFactor (a n) z

/-- The Blaschke condition gives locally uniform convergence on the open disk. -/
theorem infiniteBlaschkeProduct_hasProdLocallyUniformlyOn
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) :
    HasProdLocallyUniformlyOn
      (fun n z => normalizedBlaschkeFactor (a n) z)
      (infiniteBlaschkeProduct a) (Metric.ball 0 1) := by
  have hball : ∀ R : ℝ, 0 ≤ R → R < 1 →
      HasProdLocallyUniformlyOn
        (fun n z => normalizedBlaschkeFactor (a n) z)
        (infiniteBlaschkeProduct a) (Metric.ball 0 R) := by
    intro R hR0 hR1
    let f : ℕ → ℂ → ℂ := fun n z => normalizedBlaschkeFactor (a n) z - 1
    have hu : Summable (fun n => (2 / (1 - R)) * (1 - ‖a n‖)) :=
      hsum.mul_left _
    have hbound : ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖f n z‖ ≤ (2 / (1 - R)) * (1 - ‖a n‖) := by
      refine Eventually.of_forall fun n z hz => ?_
      apply norm_normalizedBlaschkeFactor_sub_one_le
        (haDisk n) hR0 hR1
      exact (mem_ball_zero_iff.mp hz).le
    have hcts : ∀ n, ContinuousOn (f n) (Metric.ball (0 : ℂ) R) := by
      intro n
      apply ContinuousOn.sub
      · exact ((differentiableOn_normalizedBlaschkeFactor (haDisk n)).mono
          (Metric.ball_subset_ball hR1.le)).continuousOn
      · exact continuousOn_const
    have hpl := Summable.hasProdLocallyUniformlyOn_nat_one_add
      isOpen_ball hu hbound hcts
    convert hpl using 1
    · ext n z
      simp only [f]
      ring
    · funext z
      exact tprod_congr (fun n => by simp only [f]; ring)
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball
  intro K hK hKcompact
  by_cases hne : K.Nonempty
  · obtain ⟨z0, hz0, hmax⟩ :=
      hKcompact.exists_isMaxOn hne continuous_norm.continuousOn
    have hz01 : ‖z0‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hK hz0
    let R : ℝ := (‖z0‖ + 1) / 2
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    have hR1 : R < 1 := by dsimp [R]; linarith
    have hKR : K ⊆ Metric.ball (0 : ℂ) R := by
      intro z hz
      have hzle : ‖z‖ ≤ ‖z0‖ := hmax hz
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [R]
      linarith
    exact ((hball R hR0 hR1).mono hKR).hasProdUniformlyOn_of_isCompact hKcompact
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    exact ((hball (1 / 2) (by norm_num) (by norm_num)).mono
      (Set.empty_subset _)).hasProdUniformlyOn_of_isCompact isCompact_empty

/-- The infinite Blaschke product is holomorphic on the open disk. -/
theorem differentiableOn_infiniteBlaschkeProduct
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) :
    DifferentiableOn ℂ (infiniteBlaschkeProduct a) (Metric.ball 0 1) := by
  have hprod := infiniteBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hdiff : ∀ᶠ s : Finset ℕ in atTop,
      DifferentiableOn ℂ
        (fun z => ∏ n ∈ s, normalizedBlaschkeFactor (a n) z)
        (Metric.ball (0 : ℂ) 1) := by
    refine Eventually.of_forall fun s => ?_
    classical
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro n t hnt iht
      simp only [Finset.prod_insert hnt]
      exact (differentiableOn_normalizedBlaschkeFactor (haDisk n)).mul iht
  exact (show TendstoLocallyUniformlyOn
      (fun s : Finset ℕ => fun z =>
        ∏ n ∈ s, normalizedBlaschkeFactor (a n) z)
      (infiniteBlaschkeProduct a) atTop (Metric.ball 0 1) from hprod).differentiableOn
        hdiff isOpen_ball

/-- The infinite Blaschke product is contractive at every disk point. -/
theorem norm_infiniteBlaschkeProduct_le_one
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖infiniteBlaschkeProduct a z‖ ≤ 1 := by
  have hprod := infiniteBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hlim := hprod.tendstoLocallyUniformlyOn_finsetRange.tendsto_at hzmem
  have hnormlim : Tendsto
      (fun N => ‖∏ n ∈ Finset.range N, normalizedBlaschkeFactor (a n) z‖)
      atTop (𝓝 ‖infiniteBlaschkeProduct a z‖) :=
    (continuous_norm.tendsto _).comp hlim
  apply le_of_tendsto hnormlim
  refine Eventually.of_forall fun N => ?_
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun n _ =>
    norm_normalizedBlaschkeFactor_le_one (haDisk n) hz.le

/-- Every prescribed point is an exact zero of the infinite product. -/
theorem infiniteBlaschkeProduct_apply_zero
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) (n : ℕ) :
    infiniteBlaschkeProduct a (a n) = 0 := by
  have hprod := infiniteBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hzmem : a n ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using haDisk n
  have hzero : Tendsto
      (fun s : Finset ℕ => ∏ i ∈ s, normalizedBlaschkeFactor (a i) (a n))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({n} : Finset ℕ)] with s hs
    symm
    exact Finset.prod_eq_zero (by simpa using hs) (normalizedBlaschkeFactor_self (a n))
  exact tendsto_nhds_unique (hprod.hasProd hzmem) hzero

/-- The bounded analytic multiplier represented by an infinite Blaschke product. -/
def infiniteBlaschkeMultiplier
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) : DiskMultiplier where
  fn := infiniteBlaschkeProduct a
  diff := differentiableOn_infiniteBlaschkeProduct a haDisk hsum
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => norm_infiniteBlaschkeProduct_le_one a haDisk hsum
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)

theorem infiniteBlaschkeMultiplier_apply_zero
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) (n : ℕ) :
    (infiniteBlaschkeMultiplier a haDisk hsum).fn (a n) = 0 :=
  infiniteBlaschkeProduct_apply_zero a haDisk hsum n

/-- An injective Blaschke sequence creates an infinite-dimensional Hardy model space. -/
theorem not_finiteDimensional_infiniteBlaschkeMultiplier_modelSpace
    (a : ℕ → ℂ) (haDisk : ∀ n, ‖a n‖ < 1)
    (hsum : Summable (fun n => 1 - ‖a n‖)) (hinj : Function.Injective a) :
    ¬ FiniteDimensional ℂ
      (hardyMultiplierModelSpace (infiniteBlaschkeMultiplier a haDisk hsum)) := by
  apply not_finiteDimensional_hardyMultiplierModelSpace_of_unbounded_zeros
  intro k
  refine ⟨fun i : Fin k => a i, fun i => haDisk i, ?_, fun i => ?_⟩
  · exact hinj.comp Fin.val_injective
  · exact infiniteBlaschkeMultiplier_apply_zero a haDisk hsum i

end

end GaloisForLFunctions.HTGeometry
