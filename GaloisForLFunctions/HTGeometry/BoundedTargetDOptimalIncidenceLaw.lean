import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw
import GaloisForLFunctions.HTGeometry.FiniteBuresComparisonLaw

/-!
# Dimension-optimal incidence for bounded target continua

A bounded family spanning its finite occupied coordinate space admits one
positive-definite covariance whose inverse leverage is at most dimension at
every target. Consequently complete capture by an arbitrary—possibly
uncountable—target family costs occupied dimension and one worst-target
quadratic moment, with no circuit count, covering number, or union bound.
-/

open Filter MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem convex_traceProduct_sublevel
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    Convex ℝ {M : Matrix (Fin n) (Fin n) ℂ |
      ((C * M).trace).re ≤ q} := by
  intro M hM N hN a b ha hb hab
  simp only [Set.mem_setOf_eq] at hM hN ⊢
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hq : a * q + b * q = q := by
    rw [← add_mul, hab, one_mul]
  nlinarith

theorem closed_traceProduct_sublevel
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ |
      ((C * M).trace).re ≤ q} := by
  have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      ((C * M).trace).re) := by fun_prop
  exact isClosed_le hcont continuous_const

theorem traceProduct_ray
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ((C * finiteBuresTargetRay v).trace).re =
      (star v ⬝ᵥ (C *ᵥ v)).re := by
  simp only [finiteBuresTargetRay, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply]
  ring

theorem sourceEnergy_targetRay
    {n : ℕ} (u v : Fin n → ℂ) :
    finitePositiveReporterSourceEnergy (finiteBuresTargetRay v) u =
      ‖finiteComplexInner u v‖ ^ 2 := by
  unfold finitePositiveReporterSourceEnergy finiteBuresTargetRay
  rw [Matrix.vecMulVec_mulVec]
  unfold finiteComplexInner
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, op_smul_eq_mul]
  rw [show (∑ x, star (u x) * (v x * ∑ y, star (v y) * u y)) =
      (∑ x, star (u x) * v x) * (∑ y, star (v y) * u y) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  have hsecond : (∑ y, star (v y) * u y) =
      star (∑ x, star (u x) * v x) := by
    change finiteComplexInner v u = conj (finiteComplexInner u v)
    exact finiteComplexInner_conj_symm v u
  rw [hsecond]
  change (((∑ x, conj (u x) * v x) *
      conj (∑ x, conj (u x) * v x)).re) = _
  rw [Complex.mul_conj']
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _

theorem traceProduct_le_on_occupiedBody
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    {V : Set (Fin n → ℂ)} {q : ℝ}
    (hV : ∀ v ∈ V, (star v ⬝ᵥ (C *ᵥ v)).re ≤ q) :
    ∀ M ∈ finiteBuresOccupiedTargetBody V,
      ((C * M).trace).re ≤ q := by
  have hrays : finiteBuresTargetRay '' V ⊆
      {M : Matrix (Fin n) (Fin n) ℂ | ((C * M).trace).re ≤ q} := by
    rintro M ⟨v, hv, rfl⟩
    change ((C * finiteBuresTargetRay v).trace).re ≤ q
    rw [traceProduct_ray]
    exact hV v hv
  exact closedConvexHull_min hrays
    (convex_traceProduct_sublevel C q)
    (closed_traceProduct_sublevel C q)

theorem det_raySegment
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) (s : ℝ)
    (hM : M.PosDef) (hs : s ≠ 1) :
    ((1 - s) • M + s • finiteBuresTargetRay v).det =
      M.det * ((1 - (s : ℂ)) ^ n *
        ((1 - (s : ℂ)) + (s : ℂ) * (star v ⬝ᵥ M⁻¹.mulVec v))) := by
  classical
  have hsC : (1 - (s : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hs.symm)
  have hunit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have hfactor :
      (1 - s) • M + s • finiteBuresTargetRay v =
        (1 - (s : ℂ)) •
          (M + (s / (1 - s) : ℝ) • finiteBuresTargetRay v) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      smul_eq_mul]
    field_simp
  rw [hfactor, Matrix.det_smul, finiteBuresTargetRay,
    det_add_smul_vecMulVec_self_star _ hunit _ (s / (1 - s)),
    Fintype.card_fin]
  push_cast
  field_simp
  ring

/-- A positive-definite covariance maximizing determinant along every ray
segment has leverage at most ambient complex dimension. -/
theorem targetLeverage_le_card_of_segmentDetMaximal
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : M.PosDef) (v : Fin (n + 1) → ℂ)
    (hmax : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (((1 - s) • M + s • finiteBuresTargetRay v).det).re ≤ M.det.re) :
    (star v ⬝ᵥ M⁻¹.mulVec v).re ≤ (n + 1 : ℝ) := by
  let ell : ℂ := star v ⬝ᵥ M⁻¹.mulVec v
  let d := M.det.re
  have hell_nonneg : 0 ≤ ell := hM.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hell_re_nonneg : 0 ≤ ell.re := (RCLike.nonneg_iff.mp hell_nonneg).1
  have hell_im : ell.im = 0 := (RCLike.nonneg_iff.mp hell_nonneg).2
  have hell_eq : ell = (ell.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hell_im
  have hdet_pos : 0 < M.det := hM.det_pos
  have hd_pos : 0 < d := (RCLike.pos_iff.mp hdet_pos).1
  have hdet_im : M.det.im = 0 := (RCLike.pos_iff.mp hdet_pos).2
  have hdet_eq : M.det = (d : ℂ) := by
    apply Complex.ext
    · simp [d]
    · simpa using hdet_im
  let g : ℝ → ℝ := fun s =>
    (((1 - s) • M + s • finiteBuresTargetRay v).det).re
  let p : ℝ → ℝ := fun s =>
    d * ((1 - s) ^ n * ((1 - s) + s * ell.re))
  have hgp : ∀ s : ℝ, s ≠ 1 → g s = p s := by
    intro s hs
    show (((1 - s) • M + s • finiteBuresTargetRay v).det).re =
      d * ((1 - s) ^ n * ((1 - s) + s * ell.re))
    rw [det_raySegment M v s hM hs]
    show (M.det *
      ((1 - (s : ℂ)) ^ n * ((1 - (s : ℂ)) + (s : ℂ) * ell))).re = _
    rw [hdet_eq, hell_eq,
      show ((d : ℂ) * ((1 - (s : ℂ)) ^ n *
            ((1 - (s : ℂ)) + (s : ℂ) * (ell.re : ℂ)))) =
          ((d * ((1 - s) ^ n * ((1 - s) + s * ell.re)) : ℝ) : ℂ) by
        push_cast; ring]
    exact Complex.ofReal_re _
  have hpderiv : HasDerivAt p (d * (ell.re - (n + 1 : ℝ))) 0 := by
    have hlin : HasDerivAt (fun s : ℝ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have hpow : HasDerivAt (fun s : ℝ => (1 - s) ^ n) (-(n : ℝ)) 0 := by
      have h := hlin.pow n
      have he : (n : ℝ) * (1 - 0) ^ (n - 1) * (-1) = -(n : ℝ) := by
        norm_num
      exact he ▸ h
    have hid : HasDerivAt (fun s : ℝ => s * ell.re) ell.re 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const ell.re
    have hmul : HasDerivAt p
        (d * (-(n : ℝ) * ((1 - 0) + 0 * ell.re) +
          (1 - (0 : ℝ)) ^ n * (-1 + ell.re))) 0 :=
      HasDerivAt.const_mul d (hpow.mul (hlin.add hid))
    have hval :
        -(n : ℝ) * ((1 - 0) + 0 * ell.re) +
            (1 - (0 : ℝ)) ^ n * (-1 + ell.re) =
          ell.re - (n + 1 : ℝ) := by
      simp only [sub_zero, zero_mul, add_zero, mul_one, one_pow, one_mul]
      ring
    rw [hval] at hmul
    exact hmul
  have hgeq : g =ᶠ[nhds 0] p := by
    filter_upwards [eventually_ne_nhds (show (0 : ℝ) ≠ 1 by norm_num)] with s hs
    exact hgp s hs
  have hgderiv : HasDerivAt g (d * (ell.re - (n + 1 : ℝ))) 0 :=
    hpderiv.congr_of_eventuallyEq hgeq
  have hgmax : IsMaxOn g (Set.Icc (0 : ℝ) 1) 0 := by
    intro s hs
    change g s ≤ g 0
    simpa [g] using hmax s hs
  have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by
        rw [segment_eq_Icc zero_le_one])
  have hderiv_nonpos := hgmax.localize.hasFDerivWithinAt_nonpos
    hgderiv.hasFDerivAt.hasFDerivWithinAt htan
  have hprod : d * (ell.re - (n + 1 : ℝ)) ≤ 0 := by
    simpa using hderiv_nonpos
  show ell.re ≤ (n + 1 : ℝ)
  nlinarith [hprod, hd_pos]

/-- Every compact occupied family spanning its finite coordinate space has
a determinant-optimal covariance whose leverage is bounded by dimension. -/
theorem exists_compactDOptimalCovariance
    {n : ℕ} {V : Set (Fin (n + 1) → ℂ)}
    (hVne : V.Nonempty) (hVcompact : IsCompact V)
    (hVspan : Submodule.span ℂ V = ⊤) :
    ∃ M ∈ finiteBuresOccupiedTargetBody V,
      M.PosDef ∧ ∀ v ∈ V,
        (star v ⬝ᵥ M⁻¹.mulVec v).re ≤ (n + 1 : ℝ) := by
  let K := finiteBuresOccupiedTargetBody V
  have hKne : K.Nonempty := finiteBuresOccupiedTargetBody_nonempty hVne
  have hKcompact : IsCompact K :=
    finiteBuresOccupiedTargetBody_isCompact hVcompact
  have hKconvex : Convex ℝ K := finiteBuresOccupiedTargetBody_convex V
  have hKpsd : K ⊆ {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
      M.PosSemidef} := finiteBuresOccupiedTargetBody_posSemidef V
  have hdetContinuous : Continuous
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M.det.re) := by
    fun_prop
  obtain ⟨M, hMK, hmax⟩ :=
    hKcompact.exists_isMaxOn hKne hdetContinuous.continuousOn
  obtain ⟨t, htSub, _htCard, htSpan, _htIndep⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℂ V
  have htSpanTop : Submodule.span ℂ (t : Set (Fin (n + 1) → ℂ)) = ⊤ := by
    rw [htSpan, hVspan]
  have htne : t.Nonempty := by
    by_contra hnot
    have htEmpty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [htEmpty] at htSpanTop
    simpa using htSpanTop
  letI : Nonempty t := Finset.nonempty_coe_sort.mpr htne
  let target : t → Fin (n + 1) → ℂ := fun z => z.1
  have htargetSpan : Submodule.span ℂ (Set.range target) = ⊤ := by
    have hrange : Set.range target = (t : Set (Fin (n + 1) → ℂ)) := by
      ext v
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hv
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [hrange, htSpanTop]
  let w : t → ℝ := fun _ => (Fintype.card t : ℝ)⁻¹
  let M0 := finiteDesignGram target w
  have hM0pd : M0.PosDef := by
    dsimp [M0, w]
    exact finiteDesignGram_uniform_posDef target htargetSpan
  have hw0 : ∀ i : t, 0 ≤ w i := by
    intro i
    dsimp [w]
    positivity
  have hw1 : ∑ i : t, w i = 1 := by
    dsimp [w]
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  have hM0K : M0 ∈ K := by
    dsimp [M0, K]
    unfold finiteDesignGram
    apply hKconvex.sum_mem
    · intro i _
      exact hw0 i
    · simpa using hw1
    · intro i _
      apply finiteBuresTargetRay_mem_occupiedTargetBody
      exact htSub i.2
  have hdetM0 : 0 < M0.det.re := (RCLike.pos_iff.mp hM0pd.det_pos).1
  have hdetM : 0 < M.det.re := hdetM0.trans_le (hmax hM0K)
  have hMdet : M.det ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hdetM
    exact lt_irrefl 0 hdetM
  have hMpd : M.PosDef := (hKpsd hMK).posDef_iff_det_ne_zero.mpr hMdet
  refine ⟨M, hMK, hMpd, ?_⟩
  intro v hv
  apply targetLeverage_le_card_of_segmentDetMaximal M hMpd v
  intro s hs
  apply hmax
  exact hKconvex hMK (finiteBuresTargetRay_mem_occupiedTargetBody hv)
    (sub_nonneg.mpr hs.2) hs.1 (by linarith)

/-- Compactness may be supplied by closure: every bounded occupied family
spanning its coordinate space admits the same dimension-optimal reporter. -/
theorem exists_boundedDOptimalCovariance
    {n : ℕ} {V : Set (Fin (n + 1) → ℂ)}
    (hVne : V.Nonempty) (hVbounded : Bornology.IsBounded V)
    (hVspan : Submodule.span ℂ V = ⊤) :
    ∃ M ∈ finiteBuresOccupiedTargetBody V,
      M.PosDef ∧ ∀ v ∈ V,
        (star v ⬝ᵥ M⁻¹.mulVec v).re ≤ (n + 1 : ℝ) := by
  have hclosureCompact : IsCompact (closure V) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hVbounded.closure⟩
  have hclosureSpan : Submodule.span ℂ (closure V) = ⊤ := by
    apply le_antisymm le_top
    rw [← hVspan]
    exact Submodule.span_mono subset_closure
  obtain ⟨M, hMclosure, hMpd, hleverage⟩ :=
    exists_compactDOptimalCovariance
      hVne.closure hclosureCompact hclosureSpan
  refine ⟨M, ?_, hMpd, ?_⟩
  · rw [finiteBuresOccupiedTargetBody_closure_of_isBounded hVbounded] at hMclosure
    exact hMclosure
  · intro v hv
    exact hleverage v (subset_closure hv)

/-- Occupied-dimensional capacity bound by the worst physical target
quadratic moment. -/
theorem compactBuresDualCapacity_sq_le_card_mul_uniformRayMoment
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.PosSemidef)
    {V : Set (Fin n → ℂ)} (hVne : V.Nonempty)
    (hVbounded : Bornology.IsBounded V)
    {q : ℝ} (hV : ∀ v ∈ V, (star v ⬝ᵥ (C *ᵥ v)).re ≤ q) :
    compactBuresDualCapacity C (finiteBuresOccupiedTargetBody V) ^ 2 ≤
      (n : ℝ) * q := by
  let K := finiteBuresOccupiedTargetBody V
  have hKne : K.Nonempty := finiteBuresOccupiedTargetBody_nonempty hVne
  have hKcompact : IsCompact K :=
    finiteBuresOccupiedTargetBody_isCompact_of_isBounded hVbounded
  have hKpsd : K ⊆ {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} :=
    finiteBuresOccupiedTargetBody_posSemidef V
  obtain ⟨M, hMK, hcap⟩ :=
    exists_compactBuresRootFidelity_eq_dualCapacity C hKne hKcompact hKpsd
  have hM : M.PosSemidef := hKpsd hMK
  have hpair : ((C * M).trace).re ≤ q :=
    traceProduct_le_on_occupiedBody C hV M hMK
  have hq0 : 0 ≤ q := by
    obtain ⟨v, hv⟩ := hVne
    exact (hC.re_dotProduct_nonneg v).trans (hV v hv)
  have hrank : (M.rank : ℝ) ≤ n := by
    have hrankNat : M.rank ≤ n := by
      simpa using Matrix.rank_le_card_width M
    exact_mod_cast hrankNat
  rw [hcap]
  calc
    finiteBuresRootFidelity C M ^ 2 ≤
        (M.rank : ℝ) * ((C * M).trace).re := by
      simpa [finiteBuresRootFidelity] using
        finiteBuresTrace_sq_le_rank_mul_traceProduct hC hM
    _ ≤ (n : ℝ) * q :=
      mul_le_mul hrank hpair
        (finiteMatrix_re_trace_mul_nonneg_of_posSemidef hC hM)
        (Nat.cast_nonneg n)

/-- One determinant-optimal reporter controls capture by any bounded target
family.  The cost is occupied dimension, not target cardinality. -/
theorem boundedTarget_completeCapture_le_dim_mul_worstRayMoment
    {X C : Type*} [MeasurableSpace X] [Nonempty C] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin (n + 1) → ℂ)
    (state : X → Fin (n + 1) → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hbounded : Bornology.IsBounded (Set.range target))
    (hspan : Submodule.span ℂ (Set.range target) = ⊤)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu)
    (q : ℝ)
    (hmoment : ∀ c, ∫ x,
      ‖finiteComplexInner (state x) (target c)‖ ^ 2 ∂mu ≤ q) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      (n + 1 : ℝ) * q := by
  have htargetNe : (Set.range target).Nonempty := Set.range_nonempty target
  obtain ⟨M, hMbody, hMpd, hleverage⟩ :=
    exists_boundedDOptimalCovariance htargetNe hbounded hspan
  have hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy M (state x)) mu :=
    finitePositiveReporterSourceEnergy_integrable mu state M hprod
  have hbase := finitePositiveReporter_completeIncidence_covariance_bound
    mu M hMpd target state threshold hthreshold (n + 1 : ℝ)
      (by positivity)
      (fun c ↦ by
        simpa [finitePositiveReporterTargetLeverage] using
          hleverage (target c) ⟨c, rfl⟩)
      hint hprod
  have hray : ∀ v ∈ Set.range target,
      (star v ⬝ᵥ
        (finitePositiveReporterSourceCovariance mu state *ᵥ v)).re ≤ q := by
    intro v hv
    obtain ⟨c, rfl⟩ := hv
    calc
      (star (target c) ⬝ᵥ
          (finitePositiveReporterSourceCovariance mu state *ᵥ target c)).re =
          ((finitePositiveReporterSourceCovariance mu state *
            finiteBuresTargetRay (target c)).trace).re :=
        (traceProduct_ray
          (finitePositiveReporterSourceCovariance mu state) (target c)).symm
      _ = ∫ x, finitePositiveReporterSourceEnergy
            (finiteBuresTargetRay (target c)) (state x) ∂mu :=
        finitePositiveReporter_re_trace_covariance_mul_eq_integral
          mu state (finiteBuresTargetRay (target c)) hprod
      _ = ∫ x, ‖finiteComplexInner (state x) (target c)‖ ^ 2 ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sourceEnergy_targetRay (state x) (target c)
      _ ≤ q := hmoment c
  have hpair :
      ((finitePositiveReporterSourceCovariance mu state * M).trace).re ≤ q :=
    traceProduct_le_on_occupiedBody
      (finitePositiveReporterSourceCovariance mu state) hray M hMbody
  exact hbase.trans (mul_le_mul_of_nonneg_left hpair (by positivity))

end

end GaloisForLFunctions.HTGeometry
