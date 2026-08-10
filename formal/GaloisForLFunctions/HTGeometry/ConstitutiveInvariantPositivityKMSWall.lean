import Mathlib
import GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex

/-!
# Invariant-positivity reversibility wall and the KMS irreversibility measure

A faithful invariant probability on a compact monoid forces reversibility: every left translation is
surjective, hence every element is invertible and the monoid is a compact topological group.  Full
support is load-bearing — an absorbing zero collapses the invariant measure to a point mass.

At positive temperature the situation reverses.  A KMS exchange identity applied to an isometry with
positive energy does not erase the one-sided defect: it assigns each history layer the exact mass
`(1 − q) qⁿ`, and it is incompatible with any quotient in which the isometry becomes invertible.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Topology Filter

/-! ## A closed-graph criterion -/

/-- **Closed graph implies continuity into a compact Hausdorff space.**  Mathlib has no such
criterion; it is proved here by an ultrafilter argument. -/
theorem continuous_of_isClosed_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [T2Space Y] {f : X → Y}
    (hgraph : IsClosed {p : X × Y | p.2 = f p.1}) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Filter.tendsto_iff_ultrafilter]
  intro u hu
  obtain ⟨y, -, hy⟩ :=
    isCompact_univ.ultrafilter_le_nhds (u.map f) (by simp)
  have hgraphTendsto : Filter.Tendsto (fun z : X => (z, f z)) (u : Filter X) (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact Filter.Tendsto.prodMk hu hy
  have hmem : (x, y) ∈ {p : X × Y | p.2 = f p.1} :=
    hgraph.mem_of_tendsto hgraphTendsto (Filter.Eventually.of_forall fun z => rfl)
  have hxy : y = f x := hmem
  rw [← hxy]
  exact hy

/-! ## Theorem 1.1 — faithful invariant positivity forces reversibility -/

section InvariantPositivity

variable {M : Type*} [Monoid M] [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ContinuousMul M] [MeasurableSpace M] [BorelSpace M]

/-- Left translation. -/
def leftTranslate (x : M) : M → M := fun y => x * y

omit [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] in
theorem continuous_leftTranslate (x : M) : Continuous (leftTranslate x) :=
  continuous_const.mul continuous_id

/-- **Every left translation of a compact monoid with a faithful invariant probability is
surjective.** -/
theorem surjective_leftTranslate (μ : Measure M) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (hinv : ∀ x : M, Measure.map (leftTranslate x) μ = μ) (x : M) :
    Function.Surjective (leftTranslate x) := by
  by_contra hcon
  obtain ⟨z, hz⟩ := not_forall.mp hcon
  have himg : IsCompact (Set.range (leftTranslate x)) := by
    have := isCompact_univ (X := M)
    simpa [Set.image_univ] using this.image (continuous_leftTranslate x)
  have hclosed : IsClosed (Set.range (leftTranslate x)) := himg.isClosed
  have hopen : IsOpen (Set.range (leftTranslate x))ᶜ := hclosed.isOpen_compl
  have hne : (Set.range (leftTranslate x))ᶜ.Nonempty := ⟨z, hz⟩
  have hpos : 0 < μ (Set.range (leftTranslate x))ᶜ := hopen.measure_pos μ hne
  have hzero : μ (Set.range (leftTranslate x))ᶜ = 0 := by
    have hmeas : MeasurableSet (Set.range (leftTranslate x))ᶜ := hclosed.measurableSet.compl
    have h1 := hinv x
    have h2 : Measure.map (leftTranslate x) μ (Set.range (leftTranslate x))ᶜ
        = μ ((leftTranslate x) ⁻¹' (Set.range (leftTranslate x))ᶜ) :=
      Measure.map_apply (continuous_leftTranslate x).measurable hmeas
    have h3 : (leftTranslate x) ⁻¹' (Set.range (leftTranslate x))ᶜ = ∅ := by
      ext w
      simp
    rw [h3, measure_empty] at h2
    rw [← h1]
    exact h2
  exact absurd hzero (ne_of_gt hpos)

/-- **Theorem 1.1, algebraic half.**  Every element of the monoid is invertible. -/
theorem isUnit_of_invariant_faithful (μ : Measure M) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (hinv : ∀ x : M, Measure.map (leftTranslate x) μ = μ) (x : M) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := surjective_leftTranslate μ hinv x 1
  obtain ⟨z, hz⟩ := surjective_leftTranslate μ hinv y 1
  have hxy : x * y = 1 := hy
  have hyz : y * z = 1 := hz
  have hxz : x = z := by
    calc x = x * 1 := (mul_one x).symm
      _ = x * (y * z) := by rw [hyz]
      _ = (x * y) * z := (mul_assoc x y z).symm
      _ = z := by rw [hxy, one_mul]
  refine ⟨⟨x, y, hxy, ?_⟩, rfl⟩
  rw [hxz, ← hyz]

/-- **Theorem 1.1, group structure.**  The monoid carries a group structure. -/
theorem nonempty_group_of_invariant_faithful (μ : Measure M) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (hinv : ∀ x : M, Measure.map (leftTranslate x) μ = μ) :
    Nonempty (Group M) :=
  ⟨groupOfIsUnit (isUnit_of_invariant_faithful μ hinv)⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- **Theorem 1.1, topological half.**  On a compact Hausdorff monoid any inversion map has closed
graph and is therefore continuous. -/
theorem continuous_inv_of_closed_graph (inv : M → M)
    (hinv₁ : ∀ x : M, x * inv x = 1) (hinv₂ : ∀ x : M, inv x * x = 1) :
    Continuous inv := by
  refine continuous_of_isClosed_graph ?_
  have hset : {p : M × M | p.2 = inv p.1} = {p : M × M | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
    ext p
    constructor
    · intro h
      simp only [Set.mem_setOf_eq] at h ⊢
      rw [h]
      exact ⟨hinv₁ p.1, hinv₂ p.1⟩
    · rintro ⟨h1, h2⟩
      calc p.2 = p.2 * 1 := (mul_one _).symm
        _ = p.2 * (p.1 * inv p.1) := by rw [hinv₁]
        _ = (p.2 * p.1) * inv p.1 := (mul_assoc _ _ _).symm
        _ = inv p.1 := by rw [h2, one_mul]
  rw [hset]
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)

omit [TopologicalSpace M] [CompactSpace M] [T2Space M] [ContinuousMul M] [BorelSpace M] in
/-- **The sharp erasure countermodel.**  An absorbing zero forces the invariant probability to be
the point mass there: full support is load-bearing. -/
theorem invariant_of_absorbing_zero (μ : Measure M) [IsProbabilityMeasure μ]
    (hinv : ∀ x : M, Measure.map (leftTranslate x) μ = μ)
    {z : M} (hz : ∀ y : M, z * y = z) : μ = Measure.dirac z := by
  have h1 : Measure.map (leftTranslate z) μ = μ := hinv z
  have h2 : leftTranslate z = fun _ : M => z := funext hz
  rw [h2] at h1
  rw [← h1, Measure.map_const]
  simp

end InvariantPositivity

/-! ## Theorem 2.1 — KMS balance measures the defect -/

section KMSDefect

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem alg_map_pow_smul (σ : A →ₐ[ℂ] A) {v : A} {q : ℂ} (hσ : σ v = q • v) (n : ℕ) :
    σ (v ^ n) = q ^ n • v ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, map_mul, ih, hσ, pow_succ, smul_mul_smul_comm]

omit [Algebra ℂ A] in
theorem isometry_pow {v w : A} (h : w * v = 1) (n : ℕ) : w ^ n * v ^ n = 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : w ^ (m + 1) = w ^ m * w := pow_succ w m
    have h2 : v ^ (m + 1) = v * v ^ m := by rw [pow_succ']
    rw [h1, h2]
    calc w ^ m * w * (v * v ^ m) = w ^ m * (w * v) * v ^ m := by simp [mul_assoc]
      _ = w ^ m * v ^ m := by rw [h, mul_one]
      _ = 1 := ih

variable (φ : A →ₗ[ℂ] ℂ) (σ : A →ₐ[ℂ] A)

/-- **Equation (4).**  The KMS exchange identity evaluates the range projections of an isometry with
positive energy on the geometric sequence `qⁿ`. -/
theorem kms_range_mass
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v w : A} {q : ℂ} (hσ : σ v = q • v) (hiso : w * v = 1) (hone : φ 1 = 1) (n : ℕ) :
    φ (v ^ n * w ^ n) = q ^ n := by
  rw [hexch, alg_map_pow_smul σ hσ n, mul_smul_comm, map_smul, isometry_pow hiso n, hone,
    smul_eq_mul, mul_one]

/-- **Equation (5).** -/
theorem kms_defect_mass
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v w : A} {q : ℂ} (hσ : σ v = q • v) (hiso : w * v = 1) (hone : φ 1 = 1) (n : ℕ) :
    φ (1 - v ^ n * w ^ n) = 1 - q ^ n := by
  rw [map_sub, hone, kms_range_mass φ σ hexch hσ hiso hone n]

/-- **Equation (6).**  Each orthogonal history layer carries exactly the mass `(1 − q) qⁿ`. -/
theorem kms_layer_mass
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {v w : A} {q : ℂ} (hσ : σ v = q • v) (hiso : w * v = 1) (hone : φ 1 = 1) (n : ℕ) :
    φ (v ^ n * (1 - v * w) * w ^ n) = (1 - q) * q ^ n := by
  have hsplit : v ^ n * (1 - v * w) * w ^ n = v ^ n * w ^ n - v ^ (n + 1) * w ^ (n + 1) := by
    rw [pow_succ, pow_succ']
    noncomm_ring
  rw [hsplit, map_sub, kms_range_mass φ σ hexch hσ hiso hone n,
    kms_range_mass φ σ hexch hσ hiso hone (n + 1)]
  ring

/-- **No positive-temperature KMS state descends to the reversible quotient.**  If the image of the
isometry is invertible, the same exchange identity forces `q = 1`. -/
theorem kms_forces_q_eq_one
    (hexch : ∀ a b : A, φ (a * b) = φ (b * σ a))
    {u w : A} {q : ℂ} (hσ : σ u = q • u) (hiso : w * u = 1) (hunit : u * w = 1)
    (hone : φ 1 = 1) : q = 1 := by
  have h1 : φ (u * w) = q := by
    have := kms_range_mass φ σ hexch hσ hiso hone 1
    simpa using this
  rw [hunit, hone] at h1
  exact h1.symm

end KMSDefect

/-! ## §3 — the universal Toeplitz realization -/

section ToeplitzGibbs

open scoped InnerProductSpace ENNReal

/-- The `n`-th standard basis vector of the Hardy space. -/
noncomputable def basisVec (n : ℕ) : ToeplitzSpace := lp.single 2 n (1 : ℂ)

@[simp] theorem basisVec_apply (n k : ℕ) :
    (basisVec n : ℕ → ℂ) k = if n = k then 1 else 0 := by
  rw [basisVec, lp.single_apply]
  simp [Pi.single_apply, eq_comm]

theorem norm_basisVec (n : ℕ) : ‖basisVec n‖ = 1 := by
  rw [basisVec, lp.norm_single (by norm_num)]
  simp

theorem shiftOp_basisVec (n m : ℕ) : shiftOp n (basisVec m) = basisVec (m + n) := by
  ext k
  show shiftFun n (basisVec m : ℕ → ℂ) k = (basisVec (m + n) : ℕ → ℂ) k
  by_cases h : k < n
  · rw [shiftFun_of_lt h, basisVec_apply, if_neg (by omega)]
  · rw [shiftFun_of_le (by omega), basisVec_apply, basisVec_apply]
    by_cases h2 : m + n = k
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- The diagonal matrix entry of the `n`-th defect. -/
theorem defectOp_diag (n m : ℕ) :
    ((defectOp n (basisVec m)) : ℕ → ℂ) m = if m < n then 1 else 0 := by
  rw [defectOp_apply, basisVec_apply, if_pos rfl]

/-- **Equation (8).**  The Gibbs state of the gauge dynamics: the trace against `(1−q) q^N`. -/
noncomputable def toeplitzGibbsState (q : ℝ) (a : ToeplitzSpace →L[ℂ] ToeplitzSpace) : ℂ :=
  ∑' n : ℕ, (1 - (q : ℂ)) * (q : ℂ) ^ n * ((a (basisVec n) : ℕ → ℂ) n)

/-- The state is the diagonal expectation in the standard basis. -/
theorem toeplitzGibbsState_eq_inner (q : ℝ) (a : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    toeplitzGibbsState q a
      = ∑' n : ℕ, (1 - (q : ℂ)) * (q : ℂ) ^ n * ⟪basisVec n, a (basisVec n)⟫_ℂ := by
  refine tsum_congr fun n => ?_
  congr 1
  rw [basisVec, lp.inner_single_left]
  simp

theorem norm_q_lt_one {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) : ‖(q : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

theorem tsum_thermal {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' n : ℕ, (1 - (q : ℂ)) * (q : ℂ) ^ n = 1 := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (norm_q_lt_one h0 h1)]
  have hne : (1 : ℂ) - (q : ℂ) ≠ 0 := by
    intro hcon
    have h2 : (q : ℂ) = 1 := by linear_combination -hcon
    have h3 : (q : ℝ) = 1 := by exact_mod_cast h2
    linarith
  field_simp

/-- **Normalization.**  The Gibbs state is a state. -/
theorem toeplitzGibbsState_one {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    toeplitzGibbsState q 1 = 1 := by
  rw [toeplitzGibbsState]
  have hfun : (fun n : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ n
      * (((1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) (basisVec n)) : ℕ → ℂ) n)
      = fun n : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ n := by
    funext n
    rw [one_apply_eq_self, basisVec_apply, if_pos rfl, mul_one]
  rw [hfun, tsum_thermal h0 h1]

/-- **Equation (5) in the Toeplitz realization.**  The defect carries mass `1 − qⁿ`. -/
theorem toeplitzGibbsState_defect {q : ℝ} (h1 : q < 1) (n : ℕ) :
    toeplitzGibbsState q (defectOp n) = 1 - (q : ℂ) ^ n := by
  rw [toeplitzGibbsState]
  have hfun : (fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m * ((defectOp n (basisVec m)) : ℕ → ℂ) m)
      = fun m : ℕ => if m < n then (1 - (q : ℂ)) * (q : ℂ) ^ m else 0 := by
    funext m
    rw [defectOp_diag]
    by_cases h : m < n
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hfun]
  have hzero : ∀ m ∉ Finset.range n,
      (if m < n then (1 - (q : ℂ)) * (q : ℂ) ^ m else 0) = 0 := by
    intro m hm
    rw [if_neg (by simpa using hm)]
  rw [tsum_eq_sum hzero]
  have hsum : ∑ m ∈ Finset.range n, (if m < n then (1 - (q : ℂ)) * (q : ℂ) ^ m else 0)
      = (1 - (q : ℂ)) * ∑ m ∈ Finset.range n, (q : ℂ) ^ m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos (Finset.mem_range.mp hm)]
  rw [hsum]
  have hne : (q : ℂ) - 1 ≠ 0 := by
    intro hcon
    have h2 : (q : ℂ) = 1 := by linear_combination hcon
    have h3 : (q : ℝ) = 1 := by exact_mod_cast h2
    linarith
  rw [geom_sum_eq (by
    intro hcon
    exact hne (by rw [hcon]; ring))]
  field_simp
  ring

/-- The state is additive on the pairs used below. -/
theorem toeplitzGibbsState_sub {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    toeplitzGibbsState q (1 - defectOp n)
      = toeplitzGibbsState q 1 - toeplitzGibbsState q (defectOp n) := by
  have hsummable1 : Summable fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m
      * (((1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) (basisVec m)) : ℕ → ℂ) m := by
    have hfun : (fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m
        * (((1 : ToeplitzSpace →L[ℂ] ToeplitzSpace) (basisVec m)) : ℕ → ℂ) m)
        = fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m := by
      funext m
      rw [one_apply_eq_self, basisVec_apply, if_pos rfl, mul_one]
    rw [hfun]
    exact (summable_geometric_of_norm_lt_one (norm_q_lt_one h0 h1)).mul_left _
  have hsummable2 : Summable fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m
      * ((defectOp n (basisVec m)) : ℕ → ℂ) m := by
    refine summable_of_ne_finset_zero (s := Finset.range n) ?_
    intro m hm
    rw [defectOp_diag, if_neg (by simpa using hm), mul_zero]
  rw [toeplitzGibbsState, toeplitzGibbsState, toeplitzGibbsState,
    ← Summable.tsum_sub hsummable1 hsummable2]
  refine tsum_congr fun m => ?_
  rw [← mul_sub]
  congr 1

/-- **Equation (4) in the Toeplitz realization.**  `φ(VⁿV*ⁿ) = qⁿ`. -/
theorem toeplitzGibbsState_rangeProj {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    toeplitzGibbsState q (shiftOp n ∘L backOp n) = (q : ℂ) ^ n := by
  have hsplit : shiftOp n ∘L backOp n = 1 - defectOp n := by
    rw [defectOp, ContinuousLinearMap.one_def]
    abel
  rw [hsplit, toeplitzGibbsState_sub h0 h1, toeplitzGibbsState_one h0 h1,
    toeplitzGibbsState_defect h1]
  ring

/-- The `n`-th history layer `pₙ = Vⁿ(1 − VV*)V*ⁿ`. -/
noncomputable def historyLayer (n : ℕ) : ToeplitzSpace →L[ℂ] ToeplitzSpace :=
  shiftOp n ∘L defectOp 1 ∘L backOp n

theorem historyLayer_diag (n m : ℕ) :
    ((historyLayer n (basisVec m)) : ℕ → ℂ) m = if m = n then 1 else 0 := by
  have hdec : historyLayer n = defectOp (n + 1) - defectOp n := by
    rw [historyLayer, defectOp_add n 1]
    abel
  rw [hdec]
  show ((defectOp (n + 1) (basisVec m)) : ℕ → ℂ) m - ((defectOp n (basisVec m)) : ℕ → ℂ) m = _
  rw [defectOp_diag, defectOp_diag]
  by_cases h : m = n
  · rw [if_pos (by omega), if_neg (by omega), if_pos h, sub_zero]
  · by_cases h2 : m < n
    · rw [if_pos (by omega), if_pos h2, if_neg h, sub_self]
    · rw [if_neg (by omega), if_neg (by omega), if_neg h, sub_zero]

/-- **Equation (6) in the Toeplitz realization.**  Each history layer carries exactly the mass
`(1 − q) qⁿ`. -/
theorem toeplitzGibbsState_layer (q : ℝ) (n : ℕ) :
    toeplitzGibbsState q (historyLayer n) = (1 - (q : ℂ)) * (q : ℂ) ^ n := by
  rw [toeplitzGibbsState]
  have hfun : (fun m : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ m * ((historyLayer n (basisVec m)) : ℕ → ℂ) m)
      = fun m : ℕ => if m = n then (1 - (q : ℂ)) * (q : ℂ) ^ n else 0 := by
    funext m
    rw [historyLayer_diag]
    by_cases h : m = n
    · rw [if_pos h, if_pos h, mul_one, h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hfun, tsum_ite_eq]

/-- **Off-diagonal vanishing.**  The gauge dynamics kills every non-diagonal monomial. -/
theorem toeplitzGibbsState_offDiagonal (q : ℝ) {m n : ℕ} (hmn : m ≠ n) :
    toeplitzGibbsState q (shiftOp m ∘L backOp n) = 0 := by
  rw [toeplitzGibbsState]
  have hfun : (fun k : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ k
      * ((((shiftOp m ∘L backOp n) (basisVec k)) : ℕ → ℂ) k)) = fun _ : ℕ => (0 : ℂ) := by
    funext k
    have hdiag : (((shiftOp m ∘L backOp n) (basisVec k)) : ℕ → ℂ) k = 0 := by
      show shiftFun m (fun j => (basisVec k : ℕ → ℂ) (j + n)) k = 0
      by_cases h : k < m
      · rw [shiftFun_of_lt h]
      · rw [shiftFun_of_le (by omega), basisVec_apply, if_neg (by omega)]
    rw [hdiag, mul_zero]
  rw [hfun, tsum_zero]

/-! ### Faithfulness -/

theorem thermalDiag_eq {q : ℝ} (b : ToeplitzSpace →L[ℂ] ToeplitzSpace) (n : ℕ) :
    (1 - (q : ℂ)) * (q : ℂ) ^ n
        * (((ContinuousLinearMap.adjoint b ∘L b) (basisVec n)) : ℕ → ℂ) n
      = (((1 - q) * q ^ n * ‖b (basisVec n)‖ ^ 2 : ℝ) : ℂ) := by
  have h2 : ⟪basisVec n, (ContinuousLinearMap.adjoint b ∘L b) (basisVec n)⟫_ℂ
      = ((‖b (basisVec n)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have h3 : (((ContinuousLinearMap.adjoint b ∘L b) (basisVec n)) : ℕ → ℂ) n
      = ((‖b (basisVec n)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h2, basisVec, lp.inner_single_left]
    simp
  rw [h3]
  push_cast
  ring

theorem summable_thermalDiag {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1)
    (b : ToeplitzSpace →L[ℂ] ToeplitzSpace) :
    Summable fun n : ℕ => (1 - q) * q ^ n * ‖b (basisVec n)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((summable_geometric_of_lt_one h0 h1).mul_left ((1 - q) * ‖b‖ ^ 2)))
  have hbound : ‖b (basisVec n)‖ ≤ ‖b‖ := by
    have := b.le_opNorm (basisVec n)
    rwa [norm_basisVec, mul_one] at this
  have hsq : ‖b (basisVec n)‖ ^ 2 ≤ ‖b‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hq : (0 : ℝ) ≤ (1 - q) * q ^ n := by
    have : (0 : ℝ) ≤ 1 - q := by linarith
    positivity
  calc (1 - q) * q ^ n * ‖b (basisVec n)‖ ^ 2 ≤ (1 - q) * q ^ n * ‖b‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq hq
    _ = (1 - q) * ‖b‖ ^ 2 * q ^ n := by ring

/-- **Faithfulness.**  A positive operator with vanishing Gibbs expectation is zero. -/
theorem toeplitzGibbsState_faithful {q : ℝ} (h0 : 0 < q) (h1 : q < 1)
    (b : ToeplitzSpace →L[ℂ] ToeplitzSpace)
    (hzero : toeplitzGibbsState q (ContinuousLinearMap.adjoint b ∘L b) = 0) : b = 0 := by
  set g : ℕ → ℝ := fun n => (1 - q) * q ^ n * ‖b (basisVec n)‖ ^ 2 with hg
  have hnonneg : ∀ n, 0 ≤ g n := by
    intro n
    have : (0 : ℝ) ≤ 1 - q := by linarith
    rw [hg]
    positivity
  have hsummable : Summable g := summable_thermalDiag h0.le h1 b
  have hHas : HasSum (fun n : ℕ => ((g n : ℝ) : ℂ)) ((∑' n, g n : ℝ) : ℂ) :=
    hsummable.hasSum.map (Complex.ofRealHom.toAddMonoidHom) Complex.continuous_ofReal
  have hEq : (fun n : ℕ => ((g n : ℝ) : ℂ))
      = fun n : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ n
        * (((ContinuousLinearMap.adjoint b ∘L b) (basisVec n)) : ℕ → ℂ) n := by
    funext n
    rw [thermalDiag_eq b n]
  have hsumzero : ∑' n, g n = 0 := by
    have hcomplex : ((∑' n, g n : ℝ) : ℂ) = 0 := by
      rw [← hHas.tsum_eq, hEq, ← toeplitzGibbsState]
      exact hzero
    exact_mod_cast hcomplex
  have hzeroTerm : ∀ n, g n = 0 := by
    intro n
    refine le_antisymm ?_ (hnonneg n)
    calc g n ≤ ∑' m, g m := hsummable.le_tsum n fun j _ => hnonneg j
      _ = 0 := hsumzero
  have hbe : ∀ n, b (basisVec n) = 0 := by
    intro n
    have h := hzeroTerm n
    rw [hg] at h
    have hq : (0 : ℝ) < (1 - q) * q ^ n := by
      have h2 : (0 : ℝ) < 1 - q := by linarith
      positivity
    have : ‖b (basisVec n)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h3 | h3
      · exact absurd h3 (ne_of_gt hq)
      · exact h3
    have hnorm : ‖b (basisVec n)‖ = 0 := by
      nlinarith [norm_nonneg (b (basisVec n))]
    exact norm_eq_zero.mp hnorm
  refine ContinuousLinearMap.ext fun f => ?_
  have hsingle : ∀ n : ℕ, b (lp.single 2 n ((f : ℕ → ℂ) n)) = 0 := by
    intro n
    have hsmul : (lp.single 2 n ((f : ℕ → ℂ) n) : ToeplitzSpace)
        = ((f : ℕ → ℂ) n) • basisVec n := by
      rw [basisVec, ← lp.single_smul]
      simp
    rw [hsmul, map_smul, hbe n, smul_zero]
  have hsum : HasSum (fun n : ℕ => lp.single 2 n ((f : ℕ → ℂ) n)) f :=
    lp.hasSum_single (by norm_num) f
  have hmap : HasSum (fun n : ℕ => b (lp.single 2 n ((f : ℕ → ℂ) n))) (b f) :=
    hsum.map b.toLinearMap.toAddMonoidHom b.continuous
  have hzeroSum : HasSum (fun n : ℕ => b (lp.single 2 n ((f : ℕ → ℂ) n))) 0 := by
    have : (fun n : ℕ => b (lp.single 2 n ((f : ℕ → ℂ) n))) = fun _ : ℕ => (0 : ToeplitzSpace) :=
      funext hsingle
    rw [this]
    exact hasSum_zero
  rw [hmap.unique hzeroSum]
  rfl

/-- The history layers carry the full geometric distribution: their masses sum to one. -/
theorem tsum_historyLayer_mass {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' n : ℕ, toeplitzGibbsState q (historyLayer n) = 1 := by
  have hfun : (fun n : ℕ => toeplitzGibbsState q (historyLayer n))
      = fun n : ℕ => (1 - (q : ℂ)) * (q : ℂ) ^ n :=
    funext fun n => toeplitzGibbsState_layer q n
  rw [hfun, tsum_thermal h0 h1]

/-- **The law.**  On the universal Toeplitz realization the Gibbs state is a faithful state whose
diagonal is the geometric history distribution: the range projections carry `qⁿ`, the defects carry
`1 − qⁿ`, each orthogonal history layer carries exactly `(1 − q) qⁿ`, and every off-diagonal
monomial is killed by the gauge dynamics.  The abstract `kms_forces_q_eq_one` shows no such state
survives a quotient in which the isometry becomes invertible. -/
theorem invariant_positivity_wall_and_kms_measure {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (n : ℕ) :
    toeplitzGibbsState q 1 = 1 ∧
      toeplitzGibbsState q (shiftOp n ∘L backOp n) = (q : ℂ) ^ n ∧
      toeplitzGibbsState q (defectOp n) = 1 - (q : ℂ) ^ n ∧
      toeplitzGibbsState q (historyLayer n) = (1 - (q : ℂ)) * (q : ℂ) ^ n ∧
      (∀ m : ℕ, m ≠ n → toeplitzGibbsState q (shiftOp m ∘L backOp n) = 0) ∧
      (∀ b : ToeplitzSpace →L[ℂ] ToeplitzSpace,
        toeplitzGibbsState q (ContinuousLinearMap.adjoint b ∘L b) = 0 → b = 0) ∧
      ∑' k : ℕ, toeplitzGibbsState q (historyLayer k) = 1 :=
  ⟨toeplitzGibbsState_one h0.le h1, toeplitzGibbsState_rangeProj h0.le h1 n,
    toeplitzGibbsState_defect h1 n, toeplitzGibbsState_layer q n,
    fun _ hm => toeplitzGibbsState_offDiagonal q hm,
    fun b hb => toeplitzGibbsState_faithful h0 h1 b hb,
    tsum_historyLayer_mass h0.le h1⟩

end ToeplitzGibbs

end GaloisForLFunctions.HTGeometry