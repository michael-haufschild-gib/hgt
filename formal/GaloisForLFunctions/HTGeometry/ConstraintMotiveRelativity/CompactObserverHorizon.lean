import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow

/-!
# The compact observer: local gauges and the cofinal horizon

A compact observer `K : H → Y` on an infinite-dimensional Hilbert source can be injective on every
member of a nested cofinal tower of finite-dimensional charts.  On each chart the observation floor

`σ(S) = min { ‖K x‖ : x ∈ S, ‖x‖ = 1 }`

is attained and positive, so the chart inverse exists with the exact reconstruction norm `σ(S)⁻¹`.
But the floors are antitone and tend to zero: a uniform floor would make `K` bounded below on the
whole space, and a compact operator bounded below has finite-dimensional domain.  Consequently no
bounded left inverse exists at all.

The positive Gram shadow `K*K` has the same floor, is invariant under output isometries, and the
observed image of every bounded source history has compact closure — while the source history
itself can be uniformly separated, as an orthonormal sequence is.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open Metric Set Filter Topology
open scoped InnerProductSpace

section CompactObserver

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

/-- The unit sphere of a source chart, inside the ambient space. -/
def chartSphere (S : Submodule 𝕜 H) : Set H := {x : H | x ∈ S ∧ ‖x‖ = 1}

/-- **`(COH.3)`.**  The observation floor of a source chart. -/
noncomputable def obsFloor (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) : ℝ :=
  sInf ((fun x => ‖K x‖) '' chartSphere S)

omit [CompleteSpace H] [CompleteSpace Y] in
theorem bddBelow_obsSet (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) :
    BddBelow ((fun x => ‖K x‖) '' chartSphere S) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, -, rfl⟩
  exact norm_nonneg _

omit [CompleteSpace H] [CompleteSpace Y] in
theorem obsFloor_nonneg (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) : 0 ≤ obsFloor K S := by
  rw [obsFloor]
  rcases Set.eq_empty_or_nonempty ((fun x => ‖K x‖) '' chartSphere S) with h | h
  · rw [h]; simp
  · exact le_csInf h (by rintro y ⟨x, -, rfl⟩; exact norm_nonneg _)

omit [CompleteSpace H] [CompleteSpace Y] in
theorem obsFloor_le_of_mem {K : H →L[𝕜] Y} {S : Submodule 𝕜 H} {x : H} (hx : x ∈ S)
    (hnx : ‖x‖ = 1) : obsFloor K S ≤ ‖K x‖ :=
  csInf_le (bddBelow_obsSet K S) ⟨x, ⟨hx, hnx⟩, rfl⟩

omit [CompleteSpace H] [CompleteSpace Y] in
/-- The floor is the exact chart coercivity constant. -/
theorem obsFloor_mul_le {K : H →L[𝕜] Y} {S : Submodule 𝕜 H} {x : H} (hx : x ∈ S) :
    obsFloor K S * ‖x‖ ≤ ‖K x‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
    have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
    set u : H := ((‖x‖ : 𝕜))⁻¹ • x with hu
    have huS : u ∈ S := S.smul_mem _ hx
    have hnu : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos,
        inv_mul_cancel₀ hnx]
    have hle := obsFloor_le_of_mem (K := K) huS hnu
    have hKu : ‖K u‖ = (‖x‖ : ℝ)⁻¹ * ‖K x‖ := by
      rw [hu, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos]
    rw [hKu] at hle
    rw [← le_div_iff₀ hpos, div_eq_inv_mul]
    calc obsFloor K S ≤ (‖x‖ : ℝ)⁻¹ * ‖K x‖ := hle
      _ = (‖x‖ : ℝ)⁻¹ * ‖K x‖ := rfl

omit [CompleteSpace H] in
theorem chartSphere_eq_image (S : Submodule 𝕜 H) :
    chartSphere S = (S.subtypeL) '' (Metric.sphere (0 : S) 1) := by
  ext x
  constructor
  · rintro ⟨hxS, hxn⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    simpa [mem_sphere_iff_norm] using hxn
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    simpa [mem_sphere_iff_norm] using hy

omit [CompleteSpace H] [CompleteSpace Y] in
/-- **`(COH.3)`, attainment.**  On a nonzero finite-dimensional chart the floor is attained. -/
theorem exists_norm_eq_obsFloor (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) [FiniteDimensional 𝕜 S]
    [Nontrivial S] : ∃ x ∈ chartSphere S, ‖K x‖ = obsFloor K S := by
  have hcpt : IsCompact (chartSphere (𝕜 := 𝕜) S) := by
    rw [chartSphere_eq_image]
    exact (isCompact_sphere (0 : S) 1).image (S.subtypeL).continuous
  have hne : (chartSphere (𝕜 := 𝕜) S).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : S)
    have hv0 : (v : H) ≠ 0 := fun h => hv (Subtype.ext h)
    have hpos : (0 : ℝ) < ‖(v : H)‖ := norm_pos_iff.2 hv0
    refine ⟨((‖(v : H)‖ : 𝕜))⁻¹ • (v : H), S.smul_mem _ v.2, ?_⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos,
      inv_mul_cancel₀ hpos.ne']
  obtain ⟨x, hx, hmin⟩ := hcpt.exists_isMinOn hne
    (Continuous.continuousOn (by continuity : Continuous fun x : H => ‖K x‖))
  refine ⟨x, hx, ?_⟩
  refine le_antisymm ?_ (obsFloor_le_of_mem hx.1 hx.2)
  refine le_csInf (hne.image _) ?_
  rintro y ⟨z, hz, rfl⟩
  exact hmin hz

omit [CompleteSpace H] [CompleteSpace Y] in
/-- **`(COH.3)`, positivity.**  Injectivity on the chart makes the floor positive. -/
theorem obsFloor_pos (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) [FiniteDimensional 𝕜 S] [Nontrivial S]
    (hinj : ∀ x ∈ S, K x = 0 → x = 0) : 0 < obsFloor K S := by
  obtain ⟨x, hx, hval⟩ := exists_norm_eq_obsFloor K S
  have hx0 : x ≠ 0 := by
    intro h
    have := hx.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hKx : K x ≠ 0 := fun h => hx0 (hinj x hx.1 h)
  rw [← hval]
  exact norm_pos_iff.2 hKx

omit [CompleteSpace H] [CompleteSpace Y] in
/-- The unit sphere of a nonzero chart is nonempty. -/
theorem chartSphere_nonempty {S : Submodule 𝕜 H} (hS : S ≠ ⊥) :
    (chartSphere (𝕜 := 𝕜) S).Nonempty := by
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  set u : H := (((‖x‖ : ℝ)⁻¹ : ℝ) : 𝕜) • x with hu
  have huS : u ∈ S := S.smul_mem _ hxS
  refine ⟨u, huS, ?_⟩
  rw [hu, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hpos),
    inv_mul_cancel₀ hpos.ne']

omit [CompleteSpace H] [CompleteSpace Y] in
/-- **`(COH.3)`, monotonicity.**  A larger chart has a smaller floor, provided the smaller chart
carries a unit vector.  Nonemptiness is necessary: the floor of the zero chart is the infimum of
the empty set, namely `0`, which no positive floor of a larger chart can lie below. -/
theorem obsFloor_antitone (K : H →L[𝕜] Y) {S T : Submodule 𝕜 H} (hST : S ≤ T)
    (hS : (chartSphere (𝕜 := 𝕜) S).Nonempty) :
    obsFloor K T ≤ obsFloor K S := by
  obtain ⟨x₀, hx₀⟩ := hS
  refine le_csInf ⟨‖K x₀‖, ⟨x₀, hx₀, rfl⟩⟩ ?_
  rintro y ⟨x, hx, rfl⟩
  exact obsFloor_le_of_mem (hST hx.1) hx.2

omit [CompleteSpace H] [CompleteSpace Y] in
/-- **`(COH.3a)`.**  On a chart with positive floor the reconstruction norm is exactly the inverse
floor: `σ(S)⁻¹` is the least constant bounding the source energy by the observed energy. -/
theorem isLeast_reconstruction_constant (K : H →L[𝕜] Y) (S : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 S] [Nontrivial S] (hpos : 0 < obsFloor K S) :
    IsLeast {c : ℝ | ∀ x ∈ S, ‖x‖ ≤ c * ‖K x‖} (obsFloor K S)⁻¹ := by
  constructor
  · intro x hx
    have h := obsFloor_mul_le (K := K) hx
    rw [← le_div_iff₀' hpos] at h
    rw [inv_mul_eq_div]
    exact h
  · intro c hc
    obtain ⟨x, hx, hval⟩ := exists_norm_eq_obsFloor K S
    have h := hc x hx.1
    rw [hx.2, hval] at h
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith

/-! ### The cofinal horizon -/

omit [CompleteSpace Y] in
/-- **Theorem 2.1 (2).**  Along a nested cofinal tower the observation floors tend to zero: a
uniform floor would make the compact observer bounded below on the whole source. -/
theorem tendsto_obsFloor_zero (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    (hH : ¬ FiniteDimensional 𝕜 H) (Hn : ℕ → Submodule 𝕜 H) (hmono : Monotone Hn)
    (hnt : ∀ n, Hn n ≠ ⊥) (hdense : Dense (⋃ n, (Hn n : Set H))) :
    Filter.Tendsto (fun n => obsFloor K (Hn n)) Filter.atTop (nhds 0) := by
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ N, obsFloor K (Hn N) < ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hbdd : ∀ x ∈ (⊤ : Submodule 𝕜 H), ε * ‖x‖ ≤ ‖K x‖ := by
      have hclosed : IsClosed {x : H | ε * ‖x‖ ≤ ‖K x‖} :=
        isClosed_le (by fun_prop) (by fun_prop)
      have hsub : (⋃ n, (Hn n : Set H)) ⊆ {x : H | ε * ‖x‖ ≤ ‖K x‖} := by
        rintro x hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
        exact le_trans (mul_le_mul_of_nonneg_right (hcon n) (norm_nonneg x))
          (obsFloor_mul_le hn)
      have huniv : {x : H | ε * ‖x‖ ≤ ‖K x‖} = Set.univ := by
        refine Set.eq_univ_of_univ_subset ?_
        rw [← hdense.closure_eq]
        exact hclosed.closure_subset_iff.2 hsub
      intro x _
      have : x ∈ {x : H | ε * ‖x‖ ≤ ‖K x‖} := by rw [huniv]; trivial
      exact this
    have hfd : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 H) :=
      _root_.GaloisForLFunctions.HTGeometry.finiteDimensional_of_isCompactOperator_of_bounded_below
        hK ⊤ (by simp) hε hbdd
    exact hH (Submodule.topEquiv.finiteDimensional)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hsmall ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : obsFloor K (Hn n) ≤ obsFloor K (Hn N) :=
    obsFloor_antitone K (hmono hn) (chartSphere_nonempty (hnt N))
  have h2 : 0 ≤ obsFloor K (Hn n) := obsFloor_nonneg K _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
  linarith

omit [CompleteSpace Y] in
/-- **Theorem 2.1 (5).**  A compact observer on an infinite-dimensional source has no bounded left
inverse. -/
theorem not_exists_bounded_left_inverse (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    (hH : ¬ FiniteDimensional 𝕜 H) : ¬ ∃ R : Y →L[𝕜] H, ∀ x : H, R (K x) = x := by
  rintro ⟨R, hR⟩
  have hpos : (0 : ℝ) < (‖R‖ + 1)⁻¹ := by positivity
  have hbdd : ∀ x ∈ (⊤ : Submodule 𝕜 H), (‖R‖ + 1)⁻¹ * ‖x‖ ≤ ‖K x‖ := by
    intro x _
    have h1 : ‖x‖ ≤ ‖R‖ * ‖K x‖ := by
      have := R.le_opNorm (K x)
      rwa [hR x] at this
    have h2 : ‖R‖ * ‖K x‖ ≤ (‖R‖ + 1) * ‖K x‖ := by
      have := norm_nonneg (K x)
      nlinarith
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (K x)]
  have hfd : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 H) :=
    _root_.GaloisForLFunctions.HTGeometry.finiteDimensional_of_isCompactOperator_of_bounded_below
      hK ⊤ (by simp) hpos hbdd
  exact hH (Submodule.topEquiv.finiteDimensional)

/-! ### The positive Gram shadow -/

/-- **`(COH.5)`.**  The positive shadow of the observer. -/
noncomputable def gram (K : H →L[𝕜] Y) : H →L[𝕜] H := (ContinuousLinearMap.adjoint K).comp K

theorem gram_inner_self (K : H →L[𝕜] Y) (x : H) :
    RCLike.re (inner 𝕜 (gram K x) x) = ‖K x‖ ^ 2 := by
  rw [gram, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  exact inner_self_eq_norm_sq _

/-- **`(COH.6)`.**  The compressed positive metric has the same floor. -/
theorem gram_floor (K : H →L[𝕜] Y) (S : Submodule 𝕜 H) [FiniteDimensional 𝕜 S] [Nontrivial S] :
    (∃ x ∈ chartSphere (𝕜 := 𝕜) S, RCLike.re (inner 𝕜 (gram K x) x) = obsFloor K S ^ 2) ∧
      ∀ y ∈ chartSphere (𝕜 := 𝕜) S, obsFloor K S ^ 2 ≤ RCLike.re (inner 𝕜 (gram K y) y) := by
  obtain ⟨x, hx, hval⟩ := exists_norm_eq_obsFloor K S
  constructor
  · exact ⟨x, hx, by rw [gram_inner_self, hval]⟩
  · intro y hy
    rw [gram_inner_self]
    have h := obsFloor_le_of_mem (K := K) hy.1 hy.2
    have h0 := obsFloor_nonneg K S
    nlinarith [norm_nonneg (K y)]

/-- **`(COH.7)`.**  The Gram shadow is blind to output isometries. -/
theorem gram_isometry (K : H →L[𝕜] Y) (W : Y →ₗᵢ[𝕜] Y) :
    gram (W.toContinuousLinearMap.comp K) = gram K := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_right 𝕜 fun y => ?_
  rw [gram, gram]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  exact W.inner_map_map _ _

/-! ### Compact observed image and open source history -/

omit [CompleteSpace H] [CompleteSpace Y] in
/-- **`(COH.8)`.**  The observed image of a bounded source history has compact closure. -/
theorem isCompact_closure_image_of_bounded (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    {S : Type*} (x : S → H) {r : ℝ} (hr : ∀ s, ‖x s‖ ≤ r) :
    IsCompact (closure (Set.range fun s => K (x s))) := by
  have hcpt := hK.isCompact_closure_image_closedBall r
  have hsub : (Set.range fun s => K (x s)) ⊆ K '' Metric.closedBall 0 r := by
    rintro y ⟨s, rfl⟩
    exact ⟨x s, by simpa [Metric.mem_closedBall, dist_eq_norm] using hr s, rfl⟩
  exact hcpt.of_isClosed_subset isClosed_closure (closure_mono hsub)

omit [CompleteSpace H] in
/-- An orthonormal family is uniformly separated. -/
theorem norm_sub_orthonormal {ι : Type*} {e : ι → H} (he : Orthonormal 𝕜 e) {m n : ι}
    (h : m ≠ n) : ‖e m - e n‖ = Real.sqrt 2 := by
  have hsq : ‖e m - e n‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, he.1 m, he.1 n, he.2 h]
    norm_num
  have hnn : (0 : ℝ) ≤ ‖e m - e n‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- **`(COH.9)`.**  A compact observer sends every orthonormal source sequence to zero: the source
history stays `√2`-separated while its observed history closes at one point. -/
theorem tendsto_norm_image_orthonormal (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    {e : ℕ → H} (he : Orthonormal 𝕜 e) :
    Filter.Tendsto (fun n => ‖K (e n)‖) Filter.atTop (nhds 0) := by
  have hweak : ∀ z : Y, Filter.Tendsto (fun n => inner 𝕜 (K (e n)) z) Filter.atTop (nhds 0) := by
    intro z
    have hsum := he.inner_products_summable (ContinuousLinearMap.adjoint K z)
    have hz := hsum.tendsto_atTop_zero
    have hrw : ∀ n, ‖inner 𝕜 (K (e n)) z‖ ^ 2
        = ‖inner 𝕜 (e n) (ContinuousLinearMap.adjoint K z)‖ ^ 2 := by
      intro n
      rw [ContinuousLinearMap.adjoint_inner_right]
    have hz2 : Filter.Tendsto (fun n => ‖inner 𝕜 (K (e n)) z‖ ^ 2) Filter.atTop (nhds 0) :=
      hz.congr fun n => (hrw n).symm
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Filter.Tendsto (fun n => Real.sqrt (‖inner 𝕜 (K (e n)) z‖ ^ 2)) Filter.atTop
        (nhds (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hz2
    rw [Real.sqrt_zero] at hsq
    exact hsq.congr fun n => Real.sqrt_sq (norm_nonneg _)
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hne⟩ := hcon
  have hfreq : ∃ᶠ n in Filter.atTop, ε ≤ ‖K (e n)‖ := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hne N
    refine ⟨n, hn, ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hd
    exact hd
  obtain ⟨φ, hφ, hp⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hmem : ∀ k, K (e (φ k)) ∈ closure (K '' Metric.closedBall (0 : H) 1) := by
    intro k
    exact subset_closure ⟨e (φ k), by
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_eq (he.1 (φ k)), rfl⟩
  obtain ⟨z, -, ψ, hψ, hlim⟩ :=
    (hK.isCompact_closure_image_closedBall 1).tendsto_subseq hmem
  have hnormz : ε ≤ ‖z‖ := by
    have := (continuous_norm.tendsto z).comp hlim
    refine ge_of_tendsto this ?_
    exact Filter.Eventually.of_forall fun j => hp (ψ j)
  have hinner1 : Filter.Tendsto (fun j => inner 𝕜 (K (e (φ (ψ j)))) z) Filter.atTop
      (nhds (inner 𝕜 z z)) := by
    have hc : Continuous fun w : Y => (inner 𝕜 w z : 𝕜) := by fun_prop
    exact (hc.tendsto z).comp hlim
  have hinner2 : Filter.Tendsto (fun j => inner 𝕜 (K (e (φ (ψ j)))) z) Filter.atTop (nhds 0) :=
    (hweak z).comp ((hφ.comp hψ).tendsto_atTop)
  have hzz : (inner 𝕜 z z : 𝕜) = 0 := tendsto_nhds_unique hinner1 hinner2
  have hz0 : z = 0 := inner_self_eq_zero.1 hzz
  rw [hz0, norm_zero] at hnormz
  linarith

omit [CompleteSpace Y] in
/-- **`(COH.3a)`.**  The worst-case unit-output reconstruction norms, and hence the reconstruction
energies, diverge along the tower. -/
theorem tendsto_reconstruction_norm_atTop (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    (hH : ¬ FiniteDimensional 𝕜 H) (Hn : ℕ → Submodule 𝕜 H) (hmono : Monotone Hn)
    (hnt : ∀ n, Hn n ≠ ⊥) (hdense : Dense (⋃ n, (Hn n : Set H)))
    (hpos : ∀ n, 0 < obsFloor K (Hn n)) :
    Filter.Tendsto (fun n => (obsFloor K (Hn n))⁻¹) Filter.atTop Filter.atTop := by
  have h0 := tendsto_obsFloor_zero K hK hH Hn hmono hnt hdense
  have hgt : ∀ᶠ n in Filter.atTop, obsFloor K (Hn n) ∈ Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun n => hpos n
  have h' : Filter.Tendsto (fun n => obsFloor K (Hn n)) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 hgt
  exact h'.inv_tendsto_nhdsGT_zero

omit [CompleteSpace Y] in
/-- The reconstruction energy `σ⁻²` diverges as well. -/
theorem tendsto_reconstruction_energy_atTop (K : H →L[𝕜] Y) (hK : IsCompactOperator K)
    (hH : ¬ FiniteDimensional 𝕜 H) (Hn : ℕ → Submodule 𝕜 H) (hmono : Monotone Hn)
    (hnt : ∀ n, Hn n ≠ ⊥) (hdense : Dense (⋃ n, (Hn n : Set H)))
    (hpos : ∀ n, 0 < obsFloor K (Hn n)) :
    Filter.Tendsto (fun n => (obsFloor K (Hn n))⁻¹ ^ 2) Filter.atTop Filter.atTop := by
  have h := tendsto_reconstruction_norm_atTop K hK hH Hn hmono hnt hdense hpos
  exact (tendsto_pow_atTop (two_ne_zero)).comp h

end CompactObserver



end HTGeometry.ConstraintMotiveRelativity
