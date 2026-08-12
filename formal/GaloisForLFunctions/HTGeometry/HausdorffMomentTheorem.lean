import GaloisForLFunctions.HTGeometry.HausdorffNodeComparison

/-!
# Hausdorff's moment theorem

A completely monotone sequence is the moment sequence of a finite positive measure on the unit
interval.

The quadrature levels reproduce the falling-factorial moments exactly, and the node comparison
bounds the ordinary moments by `b 0 · m²/N`, so the ordinary moments converge to `b m`.  After
normalising by `b 0` the levels are probability measures on a compact space, whose space of
probability measures is itself compact; any cluster point of the sequence therefore has exactly the
prescribed moments, because taking the integral of a bounded continuous test function is continuous
and a cluster point of a convergent sequence is its limit.

Together with `hausdorffMoment_isCompletelyMonotone` and `hausdorffSource_eq_of_moments_eq` this
identifies the Hausdorff moment sequences exactly.
-/

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The exact ratio identity and the moment estimate -/

/-- The falling-factorial moment identity in ratio form. -/
theorem sum_hausdorffWeight_ratio (b : ℕ → ℝ) {N m : ℕ} (hm : m ≤ N) :
    ∑ k ∈ range (N + 1),
        hausdorffWeight b N k *
          (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ))
      = b m := by
  have hdnat : N.descFactorial m ≠ 0 := by
    intro h
    have := Nat.descFactorial_eq_zero_iff_lt.mp h
    omega
  have hd : ((N.descFactorial m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdnat
  have hsplit : ∑ k ∈ range (N + 1),
      hausdorffWeight b N k *
        (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ))
      = (∑ k ∈ range (N + 1), hausdorffWeight b N k * ((k.descFactorial m : ℕ) : ℝ)) /
          ((N.descFactorial m : ℕ) : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, sum_hausdorffWeight_descFactorial b hm]
  field_simp

/-- **The moment estimate.**  The ordinary moments of the level-`N` quadrature are within
`b 0 · m²/N` of the prescribed values. -/
theorem abs_hausdorffMoment_hausdorffQuadrature_sub_le {b : ℕ → ℝ}
    (hb : HausdorffCompletelyMonotone b) {N m : ℕ} (hm : m ≤ N) (hN : 0 < N) :
    |hausdorffMoment (hausdorffQuadrature b N) m - b m|
      ≤ b 0 * (((m : ℝ) * (m : ℝ)) / (N : ℝ)) := by
  rw [hausdorffMoment_hausdorffQuadrature hb N m, ← sum_hausdorffWeight_ratio b hm,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ range (N + 1),
      |hausdorffWeight b N k * ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) ^ m -
        hausdorffWeight b N k *
          (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ))|
        ≤ hausdorffWeight b N k * (((m : ℝ) * (m : ℝ)) / (N : ℝ)) := by
    intro k hkmem
    have hk : k ≤ N := by
      have := Finset.mem_range.mp hkmem
      omega
    have hnode : ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) = (k : ℝ) / (N : ℝ) :=
      hausdorffNode_coe hk
    have hcmp := abs_node_pow_sub_ratio_le (N := N) (m := m) (k := k) hm hk hN
    have hfac : hausdorffWeight b N k * ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) ^ m -
        hausdorffWeight b N k *
          (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ))
        = hausdorffWeight b N k *
            (((k : ℝ) / (N : ℝ)) ^ m -
              ((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ)) := by
      rw [hnode]; ring
    rw [hfac, abs_mul, abs_of_nonneg (hausdorffWeight_nonneg hb N k)]
    exact mul_le_mul_of_nonneg_left hcmp (hausdorffWeight_nonneg hb N k)
  calc |∑ k ∈ range (N + 1),
        (hausdorffWeight b N k * ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) ^ m -
          hausdorffWeight b N k *
            (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ)))|
      ≤ ∑ k ∈ range (N + 1),
          |hausdorffWeight b N k * ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) ^ m -
            hausdorffWeight b N k *
              (((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (N + 1), hausdorffWeight b N k * (((m : ℝ) * (m : ℝ)) / (N : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = b 0 * (((m : ℝ) * (m : ℝ)) / (N : ℝ)) := by
        rw [← Finset.sum_mul, sum_hausdorffWeight]

/-- **The ordinary moments converge.** -/
theorem tendsto_hausdorffMoment_hausdorffQuadrature {b : ℕ → ℝ}
    (hb : HausdorffCompletelyMonotone b) (m : ℕ) :
    Tendsto (fun N => hausdorffMoment (hausdorffQuadrature b N) m) atTop (𝓝 (b m)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun N : ℕ => b 0 * (((m : ℝ) * (m : ℝ)) / (N : ℝ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (max m 1)] with N hN
    have hm : m ≤ N := le_trans (le_max_left _ _) hN
    have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
    simpa [Real.norm_eq_abs] using abs_hausdorffMoment_hausdorffQuadrature_sub_le hb hm hN0
  · have hlim := tendsto_const_div_atTop_nhds_zero_nat (b 0 * ((m : ℝ) * (m : ℝ)))
    refine hlim.congr fun N => ?_
    rw [mul_div_assoc]

/-! ## The limiting measure -/

/-- The monomial test function on the unit interval. -/
def hausdorffTest (m : ℕ) : BoundedContinuousFunction HausdorffSourceSpace ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun y => (y : ℝ) ^ m, by fun_prop⟩

@[simp] theorem hausdorffTest_apply (m : ℕ) (y : HausdorffSourceSpace) :
    hausdorffTest m y = (y : ℝ) ^ m := rfl

/-- A cluster point of a convergent sequence is its limit. -/
theorem eq_of_clusterPt_of_tendsto_seq {X : Type*} [TopologicalSpace X] [T2Space X]
    {g : ℕ → X} {y L : X} (hcl : ClusterPt y (Filter.map g atTop))
    (hlim : Tendsto g atTop (𝓝 L)) : y = L := by
  have hmap : Filter.map g atTop ≤ 𝓝 L := hlim
  haveI : (𝓝 y ⊓ Filter.map g atTop).NeBot := hcl
  have h1 : Tendsto (id : X → X) (𝓝 y ⊓ Filter.map g atTop) (𝓝 y) :=
    tendsto_id.mono_left inf_le_left
  have h2 : Tendsto (id : X → X) (𝓝 y ⊓ Filter.map g atTop) (𝓝 L) :=
    tendsto_id.mono_left (le_trans inf_le_right hmap)
  exact tendsto_nhds_unique h1 h2

/-- A completely monotone sequence is nonincreasing. -/
theorem hausdorffCompletelyMonotone_antitone {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b)
    (m : ℕ) : b (m + 1) ≤ b m := by
  have h := hb m 1
  simp only [Function.iterate_one, fwdDiff, pow_one] at h
  linarith

/-- A completely monotone sequence is nonnegative. -/
theorem hausdorffCompletelyMonotone_nonneg {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b)
    (m : ℕ) : 0 ≤ b m := by
  have h := hb m 0
  simpa using h

/-- **Hausdorff's moment theorem.**  Every completely monotone sequence is the moment sequence of a
finite positive measure on the unit interval. -/
theorem exists_hausdorffSource_of_completelyMonotone {b : ℕ → ℝ}
    (hb : HausdorffCompletelyMonotone b) :
    ∃ ν : Measure HausdorffSourceSpace, IsFiniteMeasure ν ∧ hausdorffMoment ν = b := by
  rcases eq_or_lt_of_le (hausdorffCompletelyMonotone_nonneg hb 0) with hzero | hpos
  · -- a vanishing zeroth term forces the whole sequence to vanish
    refine ⟨0, by infer_instance, funext fun m => ?_⟩
    have hle : ∀ m : ℕ, b m ≤ b 0 := by
      intro m
      induction m with
      | zero => exact le_rfl
      | succ m ih => exact le_trans (hausdorffCompletelyMonotone_antitone hb m) ih
    have h1 : b m ≤ 0 := by
      have := hle m
      linarith [hzero]
    have h2 : 0 ≤ b m := hausdorffCompletelyMonotone_nonneg hb m
    have hbm : b m = 0 := le_antisymm h1 h2
    rw [hausdorffMoment, hbm]
    simp
  · -- normalise the quadrature levels and take a cluster point
    have hb0 : (0 : ℝ) < b 0 := hpos
    have hb0ne : ENNReal.ofReal (b 0) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hb0]
    have hb0top : ENNReal.ofReal (b 0) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmassN : ∀ N : ℕ, (hausdorffQuadrature b N) Set.univ = ENNReal.ofReal (b 0) := by
      intro N
      have hmass := hausdorffQuadrature_mass hb N
      have hfin : ∫ _y, (1 : ℝ) ∂(hausdorffQuadrature b N)
          = ((hausdorffQuadrature b N) Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def]
      have hlt : (hausdorffQuadrature b N) Set.univ ≠ ⊤ := measure_ne_top _ _
      rw [hfin] at hmass
      rw [← hmass, ENNReal.ofReal_toReal hlt]
    -- the normalised levels
    set P : ℕ → ProbabilityMeasure HausdorffSourceSpace := fun N =>
      ⟨(ENNReal.ofReal (b 0))⁻¹ • hausdorffQuadrature b N, by
        constructor
        rw [Measure.smul_apply, smul_eq_mul, hmassN N,
          ENNReal.inv_mul_cancel hb0ne hb0top]⟩ with hPdef
    have hPcoe : ∀ N : ℕ, ((P N : ProbabilityMeasure HausdorffSourceSpace) : Measure _)
        = (ENNReal.ofReal (b 0))⁻¹ • hausdorffQuadrature b N := fun N => rfl
    -- moments of the normalised levels
    have hPmoment : ∀ (N m : ℕ),
        ∫ y, hausdorffTest m y ∂((P N : ProbabilityMeasure HausdorffSourceSpace) : Measure _)
          = (b 0)⁻¹ * hausdorffMoment (hausdorffQuadrature b N) m := by
      intro N m
      rw [hPcoe N, integral_smul_measure]
      have hconv : ((ENNReal.ofReal (b 0))⁻¹).toReal = (b 0)⁻¹ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hb0.le]
      rw [smul_eq_mul, hconv]
      rfl
    have hPtendsto : ∀ m : ℕ,
        Tendsto (fun N => ∫ y, hausdorffTest m y
            ∂((P N : ProbabilityMeasure HausdorffSourceSpace) : Measure _)) atTop
          (𝓝 ((b 0)⁻¹ * b m)) := by
      intro m
      refine ((tendsto_hausdorffMoment_hausdorffQuadrature hb m).const_mul _).congr fun N => ?_
      exact (hPmoment N m).symm
    obtain ⟨Q, hQ⟩ := exists_clusterPt_of_compactSpace (Filter.map P atTop)
    have hQmoment : ∀ m : ℕ,
        ∫ y, hausdorffTest m y ∂((Q : ProbabilityMeasure HausdorffSourceSpace) : Measure _)
          = (b 0)⁻¹ * b m := by
      intro m
      have hcont := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (X := HausdorffSourceSpace) (hausdorffTest m)
      have hclmap : ClusterPt
          (∫ y, hausdorffTest m y ∂((Q : ProbabilityMeasure HausdorffSourceSpace) : Measure _))
          (Filter.map (fun N => ∫ y, hausdorffTest m y
            ∂((P N : ProbabilityMeasure HausdorffSourceSpace) : Measure _)) atTop) := by
        have hstep := hQ.map (f := fun μ : ProbabilityMeasure HausdorffSourceSpace =>
            ∫ x, hausdorffTest m x ∂(μ : Measure _))
          hcont.continuousAt tendsto_map
        rwa [Filter.map_map] at hstep
      exact eq_of_clusterPt_of_tendsto_seq hclmap (hPtendsto m)
    have hfinQ : IsFiniteMeasure (ENNReal.ofReal (b 0) •
        ((Q : ProbabilityMeasure HausdorffSourceSpace) : Measure HausdorffSourceSpace)) := by
      constructor
      have hQuniv : ((Q : ProbabilityMeasure HausdorffSourceSpace) :
          Measure HausdorffSourceSpace) Set.univ = 1 := Q.2.measure_univ
      rw [Measure.smul_apply, smul_eq_mul, hQuniv, mul_one]
      exact ENNReal.ofReal_lt_top
    refine ⟨ENNReal.ofReal (b 0) •
        ((Q : ProbabilityMeasure HausdorffSourceSpace) : Measure HausdorffSourceSpace),
      hfinQ, funext fun m => ?_⟩
    rw [hausdorffMoment, integral_smul_measure, ENNReal.toReal_ofReal hb0.le, smul_eq_mul]
    have : ∫ y : HausdorffSourceSpace, (y : ℝ) ^ m
        ∂((Q : ProbabilityMeasure HausdorffSourceSpace) : Measure _) = (b 0)⁻¹ * b m := hQmoment m
    rw [this]
    field_simp

/-- **The Hausdorff characterisation.**  A sequence is completely monotone exactly when it is the
moment sequence of a finite positive measure on the unit interval. -/
theorem hausdorffCompletelyMonotone_iff_exists_source (b : ℕ → ℝ) :
    HausdorffCompletelyMonotone b ↔
      ∃ ν : Measure HausdorffSourceSpace, IsFiniteMeasure ν ∧ hausdorffMoment ν = b := by
  constructor
  · exact exists_hausdorffSource_of_completelyMonotone
  · rintro ⟨ν, hfin, rfl⟩
    exact hausdorffMoment_isCompletelyMonotone ν

/-- **Existence and uniqueness of the Hausdorff source.** -/
theorem existsUnique_hausdorffSource_of_completelyMonotone {b : ℕ → ℝ}
    (hb : HausdorffCompletelyMonotone b) :
    ∃! ν : { μ : Measure HausdorffSourceSpace // IsFiniteMeasure μ }, hausdorffMoment ν.1 = b := by
  obtain ⟨ν, hfin, hmom⟩ := exists_hausdorffSource_of_completelyMonotone hb
  refine ⟨⟨ν, hfin⟩, hmom, ?_⟩
  rintro ⟨μ, hfinμ⟩ hmomμ
  have : μ = ν := by
    haveI := hfinμ
    haveI := hfin
    exact hausdorffSource_eq_of_moments_eq (fun m => by rw [hmomμ, hmom])
  simpa using this

/-! ## Strict positivity for a source inside the open interval -/

/-- **Equation `(9)`.**  A nonzero source carried by the open interval makes every signed iterated
difference strictly positive. -/
theorem hausdorffMoment_strict_completelyMonotone (ν : Measure HausdorffSourceSpace)
    [IsFiniteMeasure ν] (hne : 0 < ν Set.univ)
    (hsupp : ∀ᵐ y : HausdorffSourceSpace ∂ν, 0 < (y : ℝ) ∧ (y : ℝ) < 1) (m k : ℕ) :
    0 < (-1) ^ k * ((fwdDiff 1)^[k] (hausdorffMoment ν) m) := by
  rw [signed_fwdDiff_iter_hausdorffMoment]
  set f : HausdorffSourceSpace → ℝ := fun y => (y : ℝ) ^ m * (1 - (y : ℝ)) ^ k with hf
  have hpos : ∀ᵐ y ∂ν, 0 < f y := by
    filter_upwards [hsupp] with y hy
    exact mul_pos (pow_pos hy.1 m) (pow_pos (by linarith [hy.2]) k)
  have hnn : 0 ≤ᵐ[ν] f := by
    filter_upwards [hpos] with y hy using hy.le
  have hint : Integrable f ν := integrable_of_continuous ν (by fun_prop)
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hae : ∀ᵐ y : HausdorffSourceSpace ∂ν, y ∈ Function.support f := by
    filter_upwards [hpos] with y hy
    exact ne_of_gt hy
  have hcompl : ν (Function.support f)ᶜ = 0 := MeasureTheory.ae_iff.mp hae
  have hcover : ν Set.univ ≤ ν (Function.support f) := by
    have hunion := measure_union_le (μ := ν) (Function.support f) (Function.support f)ᶜ
    rw [Set.union_compl_self, hcompl, add_zero] at hunion
    exact hunion
  exact lt_of_lt_of_le hne hcover

end

end GaloisForLFunctions.HTGeometry
