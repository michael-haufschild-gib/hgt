import GaloisForLFunctions.HTGeometry.InfiniteBlaschkeMultiplier

open Complex Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Phase-normalized Blaschke product over an arbitrary divisor index type. -/
def indexedBlaschkeProduct {ι : Type*} (a : ι → ℂ) (z : ℂ) : ℂ :=
  ∏' i, normalizedBlaschkeFactor (a i) z

/-- The indexed Blaschke condition gives locally uniform convergence on the open disk. -/
theorem indexedBlaschkeProduct_hasProdLocallyUniformlyOn
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    HasProdLocallyUniformlyOn
      (fun i z => normalizedBlaschkeFactor (a i) z)
      (indexedBlaschkeProduct a) (Metric.ball 0 1) := by
  have hball : ∀ R : ℝ, 0 ≤ R → R < 1 →
      HasProdLocallyUniformlyOn
        (fun i z => normalizedBlaschkeFactor (a i) z)
        (indexedBlaschkeProduct a) (Metric.ball 0 R) := by
    intro R hR0 hR1
    let f : ι → ℂ → ℂ := fun i z => normalizedBlaschkeFactor (a i) z - 1
    have hu : Summable (fun i => (2 / (1 - R)) * (1 - ‖a i‖)) :=
      hsum.mul_left _
    have hbound : ∀ᶠ i in cofinite, ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖f i z‖ ≤ (2 / (1 - R)) * (1 - ‖a i‖) := by
      refine Eventually.of_forall fun i z hz => ?_
      apply norm_normalizedBlaschkeFactor_sub_one_le
        (haDisk i) hR0 hR1
      exact (mem_ball_zero_iff.mp hz).le
    have hcts : ∀ i, ContinuousOn (f i) (Metric.ball (0 : ℂ) R) := by
      intro i
      apply ContinuousOn.sub
      · exact ((differentiableOn_normalizedBlaschkeFactor (haDisk i)).mono
          (Metric.ball_subset_ball hR1.le)).continuousOn
      · exact continuousOn_const
    have hpl := Summable.hasProdLocallyUniformlyOn_one_add
      isOpen_ball hu hbound hcts
    convert hpl using 1
    · ext i z
      simp only [f]
      ring
    · funext z
      exact tprod_congr (fun i => by simp only [f]; ring)
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

/-- The indexed Blaschke product is holomorphic on the open disk. -/
theorem differentiableOn_indexedBlaschkeProduct
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    DifferentiableOn ℂ (indexedBlaschkeProduct a) (Metric.ball 0 1) := by
  classical
  have hprod := indexedBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hdiff : ∀ᶠ s : Finset ι in atTop,
      DifferentiableOn ℂ
        (fun z => ∏ i ∈ s, normalizedBlaschkeFactor (a i) z)
        (Metric.ball (0 : ℂ) 1) := by
    refine Eventually.of_forall fun s => ?_
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i t hit iht
      simp only [Finset.prod_insert hit]
      exact (differentiableOn_normalizedBlaschkeFactor (haDisk i)).mul iht
  exact (show TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun z =>
        ∏ i ∈ s, normalizedBlaschkeFactor (a i) z)
      (indexedBlaschkeProduct a) atTop (Metric.ball 0 1) from hprod).differentiableOn
        hdiff isOpen_ball

/-- The indexed Blaschke product is contractive at every disk point. -/
theorem norm_indexedBlaschkeProduct_le_one
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖indexedBlaschkeProduct a z‖ ≤ 1 := by
  classical
  have hprod := indexedBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hlim : Tendsto
      (fun s : Finset ι => ∏ i ∈ s, normalizedBlaschkeFactor (a i) z)
      atTop (𝓝 (indexedBlaschkeProduct a z)) :=
    (show TendstoLocallyUniformlyOn
      (fun s : Finset ι => fun w =>
        ∏ i ∈ s, normalizedBlaschkeFactor (a i) w)
      (indexedBlaschkeProduct a) atTop (Metric.ball 0 1) from hprod).tendsto_at hzmem
  have hnormlim : Tendsto
      (fun s : Finset ι => ‖∏ i ∈ s, normalizedBlaschkeFactor (a i) z‖)
      atTop (𝓝 ‖indexedBlaschkeProduct a z‖) :=
    (continuous_norm.tendsto _).comp hlim
  apply le_of_tendsto hnormlim
  refine Eventually.of_forall fun s => ?_
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ =>
    norm_normalizedBlaschkeFactor_le_one (haDisk i) hz.le

/-- A normalized Blaschke factor has no disk zero except its prescribed divisor point. -/
theorem normalizedBlaschkeFactor_eq_zero_iff
    {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    normalizedBlaschkeFactor a z = 0 ↔ z = a := by
  by_cases ha0 : a = 0
  · subst a
    simp [normalizedBlaschkeFactor]
  rw [normalizedBlaschkeFactor, if_neg ha0, mul_eq_zero]
  have hscale : -((‖a‖ : ℂ) / a) ≠ 0 := by
    exact neg_ne_zero.mpr
      (div_ne_zero (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)) ha0)
  simp only [hscale, false_or]
  exact blaschkeFactor_eq_zero_iff ha hz

/-- The zero set of an indexed Blaschke product inside the disk is exactly its prescribed divisor. -/
theorem indexedBlaschkeProduct_ne_zero
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖))
    {z : ℂ} (hz : ‖z‖ < 1) (haway : ∀ i, z ≠ a i) :
    indexedBlaschkeProduct a z ≠ 0 := by
  let C : ℝ := 2 / (1 - ‖z‖)
  have hCsum : Summable (fun i => C * (1 - ‖a i‖)) := hsum.mul_left C
  have hdev : Summable (fun i => ‖normalizedBlaschkeFactor (a i) z - 1‖) := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      (fun i => norm_normalizedBlaschkeFactor_sub_one_le
        (haDisk i) (norm_nonneg z) hz le_rfl)
    exact hCsum
  have hne : ∀ i, normalizedBlaschkeFactor (a i) z ≠ 0 := by
    intro i hzero
    exact haway i ((normalizedBlaschkeFactor_eq_zero_iff
      (haDisk i) hz.le).mp hzero)
  have hlog : Summable
      (fun i => Complex.log (normalizedBlaschkeFactor (a i) z)) := by
    have h := Complex.summable_log_one_add_of_summable hdev.of_norm
    convert h using 1
    ext i
    congr 1
    ring
  rw [indexedBlaschkeProduct, ← Complex.cexp_tsum_eq_tprod hne hlog]
  exact Complex.exp_ne_zero _

/-- Every indexed divisor point is an exact zero of the product. -/
theorem indexedBlaschkeProduct_apply_zero
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (i : ι) :
    indexedBlaschkeProduct a (a i) = 0 := by
  classical
  have hprod := indexedBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum
  have hzmem : a i ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using haDisk i
  have hzero : Tendsto
      (fun s : Finset ι => ∏ j ∈ s, normalizedBlaschkeFactor (a j) (a i))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with s hs
    symm
    exact Finset.prod_eq_zero (by simpa using hs) (normalizedBlaschkeFactor_self (a i))
  exact tendsto_nhds_unique (hprod.hasProd hzmem) hzero

/-- Bounded analytic multiplier represented by an indexed Blaschke divisor. -/
def indexedBlaschkeMultiplier
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) : DiskMultiplier where
  fn := indexedBlaschkeProduct a
  diff := differentiableOn_indexedBlaschkeProduct a haDisk hsum
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => norm_indexedBlaschkeProduct_le_one a haDisk hsum
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)

theorem indexedBlaschkeMultiplier_apply_zero
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (i : ι) :
    (indexedBlaschkeMultiplier a haDisk hsum).fn (a i) = 0 :=
  indexedBlaschkeProduct_apply_zero a haDisk hsum i

/-- Arbitrarily large distinct indexed zero packets force infinite model dimension. -/
theorem not_finiteDimensional_indexedBlaschkeMultiplier_modelSpace
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖))
    (hpackets : ∀ k : ℕ, ∃ q : Fin k → ι,
      Function.Injective (fun i => a (q i))) :
    ¬ FiniteDimensional ℂ
      (hardyMultiplierModelSpace (indexedBlaschkeMultiplier a haDisk hsum)) := by
  apply not_finiteDimensional_hardyMultiplierModelSpace_of_unbounded_zeros
  intro k
  obtain ⟨q, hq⟩ := hpackets k
  refine ⟨fun i => a (q i), fun i => haDisk (q i), hq, fun i => ?_⟩
  exact indexedBlaschkeMultiplier_apply_zero a haDisk hsum (q i)

end

end GaloisForLFunctions.HTGeometry
