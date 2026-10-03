import GaloisForLFunctions.HTGeometry.IsometricConjugationSchatten
import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability
import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitCountermodels

/-!
# Source-complete compact-observer transience

A bounded reporter packet `A = (A_a)` on a Hilbert space `E` is **source-complete** when its common
commutant is `ℂ1` (**(SC.3b)**).  On an infinite-dimensional separable space:

* a trace-class sequence of bounded trace norm with `‖[R_n, A_a]‖₁ → 0` is weakly null: every
  weak cluster point is a Hilbert–Schmidt operator commuting with the packet, hence a scalar, hence
  zero (**(SC.10a)–(SC.10c)**); the weak clusters are extracted in `ℓ²(ℕ × ℕ)` through the matrix of
  the operator, transported by a Hilbert basis, so no `𝒦(H)* = 𝒮₁(H)` duality is needed;
* hence `tr(K R_n) → 0` for every compact `K` (**(SC.10b)**): compact operators are uniformly small
  on the tails of a basis, while the finite heads are weak pairings;
* the explicit pair `L e_j = 2^{-j} e_j`, `P = |Ω⟩⟨Ω|`, `Ω = Σ √3 2^{-(j+1)} e_j` on `ℓ²(ℕ)` is
  source-complete, and no nonzero trace-class operator commutes with it (**(SC.1)–(SC.8)**).
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

/-! ## Source-complete packets -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **(SC.3b)** A reporter packet is source-complete when its common commutant is `ℂ1`. -/
def IsSourceComplete {κ : Type*} (A : κ → E →L[ℂ] E) : Prop :=
  ∀ T : E →L[ℂ] E, (∀ a, T ∘L A a = A a ∘L T) → ∃ c : ℂ, T = c • ContinuousLinearMap.id ℂ E

theorem norm_inner_apply_le_traceNorm {T : E →L[ℂ] E} (hT : MemSchattenClass 1 T) (x y : E) :
    ‖⟪x, T y⟫_ℂ‖ ≤ traceNorm E T * (‖x‖ * ‖y‖) := by
  calc ‖⟪x, T y⟫_ℂ‖ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖x‖ * (traceNorm E T * ‖y‖) := by
        gcongr
        exact norm_le_traceNorm_of_memSchattenClass_one hT
    _ = traceNorm E T * (‖x‖ * ‖y‖) := by ring

/-- A Hilbert–Schmidt scalar operator on a space with an infinite Hilbert basis vanishes. -/
theorem eq_zero_of_isHilbertSchmidt_smul_id {ι : Type*} [Infinite ι] (b : HilbertBasis ι ℂ E) {c : ℂ}
    (h : (c • ContinuousLinearMap.id ℂ E).IsHilbertSchmidt) : c = 0 := by
  have hs := h.summable b
  simp only [smul_apply, id_apply, norm_smul, b.orthonormal.1, mul_one] at hs
  have := (summable_const_iff _).1 hs
  simpa using this

/-- The Hilbert basis as an isometry onto `ℓ²`. -/
def basisIsometry {ι : Type*} (b : HilbertBasis ι ℂ E) : E →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (b.repr : E →L[ℂ] lp (fun _ : ι => ℂ) 2)

theorem adjoint_basisIsometry_comp {ι : Type*} (b : HilbertBasis ι ℂ E) :
    adjoint (basisIsometry b) ∘L basisIsometry b = ContinuousLinearMap.id ℂ E := by
  ext x
  simp [basisIsometry, LinearIsometryEquiv.adjoint_eq_symm]

theorem basisIsometry_comp_adjoint {ι : Type*} (b : HilbertBasis ι ℂ E) :
    basisIsometry b ∘L adjoint (basisIsometry b) = ContinuousLinearMap.id ℂ (lp (fun _ : ι => ℂ) 2) := by
  ext x
  simp [basisIsometry, LinearIsometryEquiv.adjoint_eq_symm]

theorem inner_cornerConj_basisIsometry {ι : Type*} (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (x y : E) :
    ⟪basisIsometry b x, cornerConj (basisIsometry b) T (basisIsometry b y)⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h : adjoint (basisIsometry b) (basisIsometry b y) = y := by
    rw [← comp_apply, adjoint_basisIsometry_comp, id_apply]
  rw [cornerConj, comp_apply, comp_apply, h]
  exact b.repr.inner_map_map x (T y)

end General

/-! ## Weak clusters in `ℓ²` -/

section Cluster

variable {ι : Type*} [DecidableEq ι] [Countable ι]

/-- A bounded trace-class sequence on `ℓ²(ι)` has a subsequence converging weakly, in the sense of
all matrix pairings, to a Hilbert–Schmidt operator. -/
theorem exists_weakCluster_lp (T : ℕ → lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (hS : ∀ n, MemSchattenClass 1 (T n)) {B : ℝ} (hB : ∀ n, traceNorm _ (T n) ≤ B) :
    ∃ (φ : ℕ → ℕ) (W : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2), StrictMono φ ∧
      W.IsHilbertSchmidt ∧ ∀ x y, Tendsto (fun n => ⟪x, T (φ n) y⟫_ℂ) atTop (𝓝 ⟪x, W y⟫_ℂ) := by
  haveI := separableSpace_lp_countable (ι := ι × ι)
  set m := fun n => operatorMatrixVec (T n) (hS n).one_isHilbertSchmidt with hmdef
  obtain ⟨w, φ, hφ, -, hweak⟩ := exists_weaklyConvergent_subseq_of_bounded m B
    (fun n => (norm_operatorMatrixVec_le _ (hS n)).trans (hB n))
  have hK : HilbertSchmidt.IsHS (w : ι × ι → ℂ) := summable_norm_sq_lp w
  have hW : (HilbertSchmidt.toOperator hK).IsHilbertSchmidt := HilbertSchmidt.isHilbertSchmidt_toOperator hK
  have hmat : operatorMatrixVec (HilbertSchmidt.toOperator hK) hW = w :=
    lp.ext (HilbertSchmidt.matrixOf_toOperator hK)
  refine ⟨φ, HilbertSchmidt.toOperator hK, hφ, hW, fun x y => ?_⟩
  have h := (Complex.continuous_conj.tendsto _).comp (hweak (testMatrix x y))
  simp only [Function.comp_def, inner_conj_symm] at h
  rw [← inner_testMatrix_operatorMatrixVec _ hW, hmat]
  exact h.congr fun n => inner_testMatrix_operatorMatrixVec _ _ x y

end Cluster

/-! ## Theorem 3.3: weak extinction -/

section Transience

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **(SC.10a)–(SC.10c) Weak extinction.**  If `A` is source-complete on a space with a Hilbert basis
indexed by `ℕ`, a trace-class sequence of bounded trace norm with `‖[R_n, A_a]‖₁ → 0` for every `a`
satisfies `⟨x, R_n y⟩ → 0`. -/
theorem tendsto_inner_of_isSourceComplete (b : HilbertBasis ℕ ℂ E) {κ : Type*}
    {A : κ → E →L[ℂ] E} (hA : IsSourceComplete A) (R : ℕ → E →L[ℂ] E)
    (hS : ∀ n, MemSchattenClass 1 (R n)) {B : ℝ} (hB : ∀ n, traceNorm E (R n) ≤ B)
    (hcomm : ∀ a, Tendsto (fun n => traceNorm E (R n ∘L A a - A a ∘L R n)) atTop (𝓝 0)) (x y : E) :
    Tendsto (fun n => ⟪x, R n y⟫_ℂ) atTop (𝓝 0) := by
  classical
  set U := basisIsometry b
  have hU := adjoint_basisIsometry_comp b
  set R' := fun n => cornerConj U (R n) with hR'
  have hS' : ∀ n, MemSchattenClass 1 (R' n) := fun n => (memSchattenClass_cornerConj_iff hU _).2 (hS n)
  have hB' : ∀ n, traceNorm _ (R' n) ≤ B := fun n => by rw [hR', traceNorm_cornerConj hU]; exact hB n
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop, ε ≤ dist ⟪x, R n y⟫_ℂ 0 := Filter.frequently_atTop.2 hfreq
  obtain ⟨ψ, hψ, hψε⟩ := extraction_of_frequently_atTop hfr
  obtain ⟨φ, W', hφ, hW', hconv⟩ := exists_weakCluster_lp (fun n => R' (ψ n)) (fun n => hS' _)
    (fun n => hB' _)
  set W : E →L[ℂ] E := adjoint U ∘L W' ∘L U with hWdef
  have hWin : ∀ x' y' : E, ⟪U x', W' (U y')⟫_ℂ = ⟪x', W y'⟫_ℂ := fun x' y' => by
    rw [hWdef, comp_apply, comp_apply, adjoint_inner_right]
  have hconvE : ∀ x' y' : E, Tendsto (fun n => ⟪x', R (ψ (φ n)) y'⟫_ℂ) atTop (𝓝 ⟪x', W y'⟫_ℂ) :=
    fun x' y' => by
      have h := hconv (U x') (U y')
      rw [hWin] at h
      exact h.congr fun n => inner_cornerConj_basisIsometry b _ x' y'
  have hcommW : ∀ a, W ∘L A a = A a ∘L W := by
    intro a
    refine ContinuousLinearMap.ext fun y' => ext_inner_left ℂ fun x' => ?_
    have h1 := (hconvE x' (A a y')).sub (hconvE (adjoint (A a) x') y')
    have h2 : Tendsto (fun n => ⟪x', R (ψ (φ n)) (A a y')⟫_ℂ - ⟪adjoint (A a) x', R (ψ (φ n)) y'⟫_ℂ)
        atTop (𝓝 0) := by
      have hc := (hcomm a).comp (hψ.comp hφ).tendsto_atTop
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hc.mul_const (‖x'‖ * ‖y'‖))
      rw [adjoint_inner_left]
      have := norm_inner_apply_le_traceNorm (memSchattenClass_one_comp_sub_comp (hS (ψ (φ n))) (A a)) x' y'
      simpa [sub_apply, comp_apply] using this
    have heq := tendsto_nhds_unique h1 h2
    rw [adjoint_inner_left, sub_eq_zero] at heq
    simpa [comp_apply] using heq
  obtain ⟨c, hc⟩ := hA W hcommW
  have hWHS : W.IsHilbertSchmidt := (hW'.comp_right U).comp_left (adjoint U)
  rw [hc] at hWHS
  have hc0 := eq_zero_of_isHilbertSchmidt_smul_id b hWHS
  have hlim := hconvE x y
  rw [hc, hc0, zero_smul, zero_apply, inner_zero_right] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds 0 hε)).exists
  exact absurd (hψε (φ n)) (not_le.2 hn)

end Transience

/-! ## Head projections on `ℓ²(ℕ)` and compact observers -/

section Head

/-- The weight of the head projection `Q_r = Σ_{j ≤ r} |e_j⟩⟨e_j|`. -/
def headWeight (r j : ℕ) : ℂ := if j ≤ r then 1 else 0

theorem norm_headWeight_le (r j : ℕ) : ‖headWeight r j‖ ≤ 1 := by
  unfold headWeight
  split_ifs <;> simp

/-- **(SC.17)** The finite source-head projection `Q_r` on `ℓ²(ℕ)`. -/
def headProjection (r : ℕ) : ℓ²ℕ →L[ℂ] ℓ²ℕ :=
  LpDiagonal.lpDiag (headWeight r) 1 zero_le_one (norm_headWeight_le r)

theorem headProjection_apply (r : ℕ) (x : ℓ²ℕ) (j : ℕ) :
    headProjection r x j = headWeight r j * x j :=
  LpDiagonal.lpDiag_coe _ _ _ _ _ _

theorem sub_headProjection_apply (r : ℕ) (x : ℓ²ℕ) (j : ℕ) :
    (x - headProjection r x) j = (1 - headWeight r j) * x j := by
  rw [lp.coeFn_sub, Pi.sub_apply, headProjection_apply]
  ring

theorem norm_sub_headProjection_sq (r : ℕ) (x : ℓ²ℕ) :
    ‖x - headProjection r x‖ ^ 2 = ∑' j, ‖(1 - headWeight r j) * x j‖ ^ 2 := by
  rw [lp_two_norm_sq_eq_tsum]
  exact tsum_congr fun j => by rw [sub_headProjection_apply]

theorem norm_one_sub_headWeight_le (r j : ℕ) : ‖1 - headWeight r j‖ ≤ 1 := by
  unfold headWeight
  split_ifs <;> simp

theorem norm_sub_headProjection_le (r : ℕ) (x : ℓ²ℕ) : ‖x - headProjection r x‖ ≤ ‖x‖ := by
  have hle : ∀ j, ‖(1 - headWeight r j) * x j‖ ^ 2 ≤ ‖x j‖ ^ 2 := fun j => by
    rw [norm_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_headWeight_le r j)) 2
  have h : ‖x - headProjection r x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sub_headProjection_sq, lp_two_norm_sq_eq_tsum]
    exact Summable.tsum_le_tsum hle
      ((summable_norm_sq_lp x).of_nonneg_of_le (fun _ => by positivity) hle) (summable_norm_sq_lp x)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem tendsto_norm_sub_headProjection (x : ℓ²ℕ) :
    Tendsto (fun r => ‖x - headProjection r x‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun r => ‖x - headProjection r x‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [norm_sub_headProjection_sq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun r j => ‖(1 - headWeight r j) * x j‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun j => ‖x j‖ ^ 2) (summable_norm_sq_lp x) (fun j => ?_)
      (Eventually.of_forall fun r j => ?_)
    · simpa using h
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop j] with r hr
      simp [headWeight, hr]
    · rw [norm_pow, norm_norm, norm_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_headWeight_le r j)) 2
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h
  exact h.congr fun r => by simp [Real.sqrt_sq (norm_nonneg _)]

theorem inner_sub_headProjection (r : ℕ) (z y : ℓ²ℕ) :
    ⟪z, y - headProjection r y⟫_ℂ = ⟪z - headProjection r z, y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [sub_headProjection_apply, sub_headProjection_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul]
  have h : starRingEnd ℂ (1 - headWeight r j) = 1 - headWeight r j := by
    unfold headWeight
    split_ifs <;> simp
  rw [h]
  ring

/-- A compact operator is uniformly small on the tails: `‖K(1 - Q_r)‖ → 0`. -/
theorem tendsto_norm_comp_sub_headProjection (K : ℓ²ℕ →L[ℂ] ℓ²ℕ) (hK : IsCompactOperator K) :
    Tendsto (fun r => ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)‖) atTop (𝓝 0) := by
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  have hfr : ∃ᶠ r in atTop, ε ≤ dist ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)‖ 0 :=
    Filter.frequently_atTop.2 hfreq
  obtain ⟨ψ, hψ, hψε⟩ := extraction_of_frequently_atTop hfr
  have hlt : ∀ k, ε / 2 < ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection (ψ k))‖ := fun k => by
    have := hψε k
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    linarith
  choose y hy1 hy2 using fun k => exists_lt_apply_of_lt_opNorm _ (hlt k)
  set u := fun k => y k - headProjection (ψ k) (y k) with hudef
  have hu : ∀ k, ‖u k‖ ≤ 1 := fun k => (norm_sub_headProjection_le _ _).trans (hy1 k).le
  have hweak : ∀ z, Tendsto (fun k => ⟪z, u k⟫_ℂ) atTop (𝓝 0) := fun z => by
    have hz := (tendsto_norm_sub_headProjection z).comp hψ.tendsto_atTop
    refine squeeze_zero_norm (fun k => ?_) hz
    rw [hudef, inner_sub_headProjection]
    calc ‖⟪z - headProjection (ψ k) z, y k⟫_ℂ‖ ≤ ‖z - headProjection (ψ k) z‖ * ‖y k‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖z - headProjection (ψ k) z‖ * 1 := by gcongr; exact (hy1 k).le
      _ = ‖z - headProjection (ψ k) z‖ := mul_one _
  have hK0 := tendsto_norm_compact_of_weaklyNull K hK u hu hweak
  have hval : ∀ k, ε / 2 < ‖K (u k)‖ := fun k => by
    have := hy2 k
    simpa [hudef, comp_apply, sub_apply, id_apply] using this
  obtain ⟨k, hk⟩ := (hK0.eventually (Metric.ball_mem_nhds 0 (half_pos hε))).exists
  rw [dist_zero_right] at hk
  linarith [hval k]

theorem headProjection_single (r i : ℕ) :
    headProjection r (lp.single 2 i (1 : ℂ)) = headWeight r i • lp.single 2 i (1 : ℂ) := by
  refine lp.ext (funext fun j => ?_)
  rw [headProjection_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem opTrace_comp_headProjection {X : ℓ²ℕ →L[ℂ] ℓ²ℕ} (hX : MemSchattenClass 1 X) (r : ℕ) :
    opTrace (X ∘L headProjection r) =
      ∑ i ∈ Finset.range (r + 1), ⟪(lp.single 2 i (1 : ℂ) : ℓ²ℕ), X (lp.single 2 i 1)⟫_ℂ := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one (hX.one_comp_right _) (HilbertSchmidt.lpBasis ℕ)]
  rw [tsum_eq_sum (s := Finset.range (r + 1)) fun i hi => ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [HilbertSchmidt.lpBasis_apply, comp_apply, headProjection_single, headWeight,
      if_pos (by omega), one_smul]
  · rw [Finset.mem_range] at hi
    rw [HilbertSchmidt.lpBasis_apply, comp_apply, headProjection_single, headWeight,
      if_neg (by omega), zero_smul, map_zero, inner_zero_right]

/-- **Compact observers see weak extinction.**  A weakly null trace-class sequence of bounded trace
norm has `tr(K R_n) → 0` for every compact `K`: split `K = K Q_r + K(1 - Q_r)`. -/
theorem tendsto_opTrace_comp_of_weaklyNull (R : ℕ → ℓ²ℕ →L[ℂ] ℓ²ℕ) (hS : ∀ n, MemSchattenClass 1 (R n))
    {B : ℝ} (hB : ∀ n, traceNorm ℓ²ℕ (R n) ≤ B)
    (hweak : ∀ x y, Tendsto (fun n => ⟪x, R n y⟫_ℂ) atTop (𝓝 0))
    (K : ℓ²ℕ →L[ℂ] ℓ²ℕ) (hK : IsCompactOperator K) :
    Tendsto (fun n => opTrace (K ∘L R n)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (traceNorm_nonneg _).trans (hB 0)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨r, hr⟩ : ∃ r, ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)‖ < δ / (2 * (B + 1)) :=
    ((tendsto_norm_comp_sub_headProjection K hK).eventually (gt_mem_nhds (by positivity))).exists
  have hhead : Tendsto (fun n => ∑ i ∈ Finset.range (r + 1),
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ℕ), R n (K (lp.single 2 i 1))⟫_ℂ) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ _i ∈ Finset.range (r + 1), (0 : ℂ) by simp]
    exact tendsto_finsetSum _ fun i _ => hweak _ _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hhead (δ / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdec : R n ∘L K = (R n ∘L K) ∘L headProjection r +
      R n ∘L (K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)) := by
    ext1 x
    simp only [comp_apply, add_apply, sub_apply, id_apply, map_sub]
    abel
  have hsplit : opTrace (K ∘L R n) = ∑ i ∈ Finset.range (r + 1),
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ℕ), R n (K (lp.single 2 i 1))⟫_ℂ +
      opTrace (R n ∘L (K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r))) := by
    rw [(hS n).one_opTrace_comp_comm K, hdec, opTrace_add_of_memSchattenClass_one
      (((hS n).one_comp_right K).one_comp_right _) ((hS n).one_comp_right _),
      opTrace_comp_headProjection ((hS n).one_comp_right K)]
    rfl
  have htail := norm_opTrace_comp_le_norm_mul_traceNorm (hS n)
    (K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r))
  rw [dist_zero_right, hsplit]
  have h1 := hN n hn
  rw [dist_zero_right] at h1
  have h2 : traceNorm ℓ²ℕ (R n) * ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)‖ ≤ δ / 2 := by
    calc traceNorm ℓ²ℕ (R n) * ‖K ∘L (ContinuousLinearMap.id ℂ ℓ²ℕ - headProjection r)‖
        ≤ B * (δ / (2 * (B + 1))) := mul_le_mul (hB n) hr.le (norm_nonneg _) hB0
      _ ≤ δ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  calc _ ≤ _ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add_of_lt_of_le h1 (htail.trans h2)
    _ = δ := by ring

end Head

/-! ## Theorem 3.3: compact extinction -/

section CompactTransience

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Theorem 3.3 (SC.10b) Coordinate-free source-complete transience.**  On a space with a Hilbert
basis indexed by `ℕ`, a trace-class sequence of bounded trace norm asymptotically commuting in trace
norm with a source-complete packet satisfies `tr(K R_n) → 0` for every compact `K`. -/
theorem tendsto_opTrace_comp_of_isSourceComplete (b : HilbertBasis ℕ ℂ E) {κ : Type*}
    {A : κ → E →L[ℂ] E} (hA : IsSourceComplete A) (R : ℕ → E →L[ℂ] E)
    (hS : ∀ n, MemSchattenClass 1 (R n)) {B : ℝ} (hB : ∀ n, traceNorm E (R n) ≤ B)
    (hcomm : ∀ a, Tendsto (fun n => traceNorm E (R n ∘L A a - A a ∘L R n)) atTop (𝓝 0))
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    Tendsto (fun n => opTrace (K ∘L R n)) atTop (𝓝 0) := by
  set U := basisIsometry b
  have hU := adjoint_basisIsometry_comp b
  have htr : ∀ n, opTrace (K ∘L R n) = opTrace (cornerConj U K ∘L cornerConj U (R n)) := fun n => by
    rw [← opTrace_cornerConj hU (memSchattenClass_one_comp_left (hS n) K)]
    congr 1
    simp only [cornerConj, comp_assoc]
    rw [← comp_assoc (adjoint U) U, hU, id_comp]
  simp_rw [htr]
  refine tendsto_opTrace_comp_of_weaklyNull (fun n => cornerConj U (R n))
    (fun n => (memSchattenClass_cornerConj_iff hU _).2 (hS n)) (B := B)
    (fun n => by rw [traceNorm_cornerConj hU]; exact hB n) (fun x y => ?_) _ ?_
  · have h := tendsto_inner_of_isSourceComplete b hA R hS hB hcomm (adjoint U x) (adjoint U y)
    refine h.congr fun n => ?_
    rw [cornerConj, comp_apply, comp_apply]
    exact adjoint_inner_left U _ x
  · exact (hK.comp_clm (adjoint U)).clm_comp U

/-- A separable infinite-dimensional Hilbert space has a Hilbert basis indexed by `ℕ`: a Hilbert basis
is a `√2`-separated set, hence countable, and it is infinite since its span is dense. -/
theorem exists_hilbertBasis_nat [TopologicalSpace.SeparableSpace E] (h : ¬ FiniteDimensional ℂ E) :
    Nonempty (HilbertBasis ℕ ℂ E) := by
  classical
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ E
  have hcount : w.Countable := by
    have hdisj : w.PairwiseDisjoint fun x => Metric.ball x (1 / 2) := by
      intro x hx y hy hxy
      refine Set.disjoint_left.2 fun z hzx hzy => ?_
      have hxy' : (⟨x, hx⟩ : w) ≠ ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
      have hd : ‖b ⟨x, hx⟩ - b ⟨y, hy⟩‖ ^ 2 = 2 := by
        rw [@norm_sub_sq ℂ, b.orthonormal.inner_eq_zero hxy', b.orthonormal.1, b.orthonormal.1]
        norm_num
      have hb' : ∀ v : w, b v = v := fun v => congrFun hb v
      rw [hb', hb'] at hd
      have hlt : ‖x - y‖ < 1 := by
        rw [← dist_eq_norm]
        calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
          _ < 1 / 2 + 1 / 2 := add_lt_add (by rw [dist_comm]; exact hzx) hzy
          _ = 1 := by norm_num
      nlinarith [norm_nonneg (x - y)]
    exact hdisj.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
      (fun x _ => ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  haveI : Countable w := hcount.to_subtype
  haveI : Infinite w := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI := Fintype.ofFinite w
    exact h (LinearEquiv.finiteDimensional b.repr.symm.toLinearEquiv)
  haveI := Encodable.ofCountable w
  haveI := Denumerable.ofEncodableOfInfinite w
  set e := Denumerable.eqv w
  refine ⟨HilbertBasis.mk (v := b ∘ e.symm) (b.orthonormal.comp _ e.symm.injective) ?_⟩
  rw [Set.range_comp, e.symm.range_eq_univ, Set.image_univ, b.dense_span]

/-- **Theorem 3.3 on an abstract separable infinite-dimensional space.** -/
theorem tendsto_opTrace_comp_of_isSourceComplete' [TopologicalSpace.SeparableSpace E]
    (hE : ¬ FiniteDimensional ℂ E) {κ : Type*} {A : κ → E →L[ℂ] E} (hA : IsSourceComplete A)
    (R : ℕ → E →L[ℂ] E) (hS : ∀ n, MemSchattenClass 1 (R n)) {B : ℝ} (hB : ∀ n, traceNorm E (R n) ≤ B)
    (hcomm : ∀ a, Tendsto (fun n => traceNorm E (R n ∘L A a - A a ∘L R n)) atTop (𝓝 0))
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    Tendsto (fun n => opTrace (K ∘L R n)) atTop (𝓝 0) :=
  tendsto_opTrace_comp_of_isSourceComplete (exists_hilbertBasis_nat hE).some hA R hS hB hcomm K hK

end CompactTransience

/-! ## Theorem 3.1: the explicit source-complete carrier -/

section Diagonal

variable {ι : Type*} [DecidableEq ι]

/-- **(SC.4)–(SC.6)** A simple diagonal label and a full-support rank-one projector have scalar common
commutant: the label kills the off-diagonal entries, the projector equalizes the diagonal. -/
theorem isSourceComplete_diag_rankOne (lam : ι → ℂ) (hlam : Function.Injective lam) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖lam i‖ ≤ M) (ω : lp (fun _ : ι => ℂ) 2) (hω : ∀ i, ω i ≠ 0) :
    IsSourceComplete ![LpDiagonal.lpDiag lam M hM hb, InnerProductSpace.rankOne ℂ ω ω] := by
  intro T hT
  have hD := hT 0
  have hP := hT 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hD hP
  set t : ι → ι → ℂ := fun i j => T (lp.single 2 j 1) i with htdef
  have hoff : ∀ i j, i ≠ j → t i j = 0 := by
    intro i j hij
    have h := congrArg (fun S : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 =>
      S (lp.single 2 j (1 : ℂ)) i) hD
    simp only [comp_apply, LpDiagonal.lpDiag_single, map_smul, LpDiagonal.lpDiag_coe, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at h
    have h2 : (lam j - lam i) * t i j = 0 := by
      simp only [htdef]
      linear_combination h
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hlam.ne (Ne.symm hij)))
  have hadj : ∀ i, adjoint T (lp.single 2 i (1 : ℂ)) = starRingEnd ℂ (t i i) • lp.single 2 i (1 : ℂ) := by
    intro i
    refine lp.ext (funext fun k => ?_)
    rw [← inner_single_one_left, adjoint_inner_right, ← inner_conj_symm, inner_single_one_left,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
    by_cases h : k = i
    · subst h
      simp [htdef]
    · have h0 : t i k = 0 := hoff i k (Ne.symm h)
      simp only [htdef] at h0
      simp [h0, Pi.single_eq_of_ne h]
  have hcoord : ∀ y i, T y i = t i i * y i := by
    intro y i
    rw [← inner_single_one_left, ← adjoint_inner_left, hadj, inner_smul_left, Complex.conj_conj,
      inner_single_one_left]
  have hTe : ∀ j, T (lp.single 2 j (1 : ℂ)) = t j j • lp.single 2 j (1 : ℂ) := by
    intro j
    refine lp.ext (funext fun k => ?_)
    rw [hcoord, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
    by_cases h : k = j
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hdiag : ∀ i j, t i i = t j j := by
    intro i j
    have h := congrArg (fun S : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 =>
      S (lp.single 2 j (1 : ℂ)) i) hP
    simp only [comp_apply, InnerProductSpace.rankOne_apply, map_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, hcoord, hTe, lp.inner_single_right] at h
    have h2 : (starRingEnd ℂ (ω j) * ω i) * (t i i - t j j) = 0 := by
      simp only [RCLike.inner_apply] at h
      linear_combination h
    have hne : starRingEnd ℂ (ω j) * ω i ≠ 0 := mul_ne_zero ((map_ne_zero _).2 (hω j)) (hω i)
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hne)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, ContinuousLinearMap.ext fun y => lp.ext (funext fun i => isEmptyElim i)⟩
  · refine ⟨t i₀ i₀, ContinuousLinearMap.ext fun y => lp.ext (funext fun i => ?_)⟩
    rw [hcoord, smul_apply, id_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hdiag i i₀]

end Diagonal

/-- **(SC.2)** The label eigenvalues `2^{-j}`. -/
def sourceLabelWeight (j : ℕ) : ℂ := (((1 / 2 : ℝ) ^ j : ℝ) : ℂ)

theorem norm_sourceLabelWeight_le (j : ℕ) : ‖sourceLabelWeight j‖ ≤ 1 := by
  rw [sourceLabelWeight, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem sourceLabelWeight_injective : Function.Injective sourceLabelWeight := fun i j h => by
  have h' : (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) ^ j := Complex.ofReal_injective h
  exact pow_right_injective₀ (by norm_num) (by norm_num) h'

/-- **(SC.2)** The compact positive label `L e_j = 2^{-j} e_j`. -/
def sourceLabel : ℓ²ℕ →L[ℂ] ℓ²ℕ :=
  LpDiagonal.lpDiag sourceLabelWeight 1 zero_le_one norm_sourceLabelWeight_le

/-- **(SC.2)** The fusion coefficients `Ω_j = √3 · 2^{-(j+1)}`. -/
def fusionCoeff (j : ℕ) : ℂ := ((Real.sqrt 3 * (1 / 2 : ℝ) ^ (j + 1) : ℝ) : ℂ)

theorem norm_fusionCoeff_sq (j : ℕ) : ‖fusionCoeff j‖ ^ 2 = 3 / 4 * (1 / 4 : ℝ) ^ j := by
  rw [fusionCoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by norm_num),
    ← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring, pow_add, pow_mul]
  norm_num
  ring

/-- **(SC.3)** `Σ_j |Ω_j|² = 3 Σ_j 4^{-(j+1)} = 1`. -/
theorem hasSum_norm_fusionCoeff_sq : HasSum (fun j => ‖fusionCoeff j‖ ^ 2) 1 := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left (3 / 4)
  simp_rw [norm_fusionCoeff_sq]
  rw [show (3 / 4 : ℝ) * (1 - 1 / 4)⁻¹ = 1 by norm_num] at h
  exact h

/-- **(SC.2)** The fusion vector `Ω`. -/
def fusionVector : ℓ²ℕ := ⟨fusionCoeff, memℓp_gen (by simpa using hasSum_norm_fusionCoeff_sq.summable)⟩

theorem fusionVector_apply (j : ℕ) : fusionVector j = fusionCoeff j := rfl

/-- **(SC.3)** `‖Ω‖ = 1`. -/
theorem norm_fusionVector : ‖fusionVector‖ = 1 := by
  have h : ‖fusionVector‖ ^ 2 = 1 := by
    rw [lp_two_norm_sq_eq_tsum]
    exact hasSum_norm_fusionCoeff_sq.tsum_eq
  nlinarith [norm_nonneg fusionVector, sq_nonneg (‖fusionVector‖ - 1)]

theorem fusionCoeff_ne_zero (j : ℕ) : fusionCoeff j ≠ 0 := by
  rw [fusionCoeff]
  exact Complex.ofReal_ne_zero.2 (by positivity)

/-- **(SC.2)** The fusion projector `P = |Ω⟩⟨Ω|`. -/
def fusionProjection : ℓ²ℕ →L[ℂ] ℓ²ℕ := InnerProductSpace.rankOne ℂ fusionVector fusionVector

/-- **(SC.3)** `P` is a rank-one orthogonal projection. -/
theorem fusionProjection_isProjection :
    fusionProjection ∘L fusionProjection = fusionProjection ∧ IsSelfAdjoint fusionProjection := by
  refine ⟨ContinuousLinearMap.ext fun x => ?_, (InnerProductSpace.isPositive_rankOne_self _).isSelfAdjoint⟩
  simp only [fusionProjection, comp_apply, InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, norm_fusionVector]
  simp

/-- **Theorem 3.1** The explicit pair `(L, P)` is source-complete. -/
theorem isSourceComplete_sourceLabel_fusion : IsSourceComplete ![sourceLabel, fusionProjection] :=
  isSourceComplete_diag_rankOne sourceLabelWeight sourceLabelWeight_injective zero_le_one
    norm_sourceLabelWeight_le fusionVector fusionCoeff_ne_zero

/-- **Theorem 3.1** A trace-class operator commuting with `L` and `P` vanishes. -/
theorem eq_zero_of_memSchattenClass_commute {T : ℓ²ℕ →L[ℂ] ℓ²ℕ} (hT : MemSchattenClass 1 T)
    (hL : T ∘L sourceLabel = sourceLabel ∘L T) (hP : T ∘L fusionProjection = fusionProjection ∘L T) :
    T = 0 := by
  obtain ⟨c, hc⟩ := isSourceComplete_sourceLabel_fusion T (by
    intro a
    fin_cases a
    · exact hL
    · exact hP)
  have hHS := hT.one_isHilbertSchmidt
  rw [hc] at hHS
  rw [hc, eq_zero_of_isHilbertSchmidt_smul_id (HilbertSchmidt.lpBasis ℕ) hHS, zero_smul]

/-- **Theorem 3.2 (SC.7)–(SC.8)** For positive trace-class `T_n` with `sup tr T_n < ∞` and
`‖[T_n, L]‖₁ + ‖[T_n, P]‖₁ → 0`, every compact observer sees `tr(K T_n) → 0`. -/
theorem tendsto_opTrace_comp_sourceLabel_fusion (T : ℕ → ℓ²ℕ →L[ℂ] ℓ²ℕ) (hpos : ∀ n, (T n).IsPositive)
    (hS : ∀ n, MemSchattenClass 1 (T n)) {B : ℝ} (hB : ∀ n, (opTrace (T n)).re ≤ B)
    (hcomm : Tendsto (fun n => traceNorm ℓ²ℕ (T n ∘L sourceLabel - sourceLabel ∘L T n) +
      traceNorm ℓ²ℕ (T n ∘L fusionProjection - fusionProjection ∘L T n)) atTop (𝓝 0))
    (K : ℓ²ℕ →L[ℂ] ℓ²ℕ) (hK : IsCompactOperator K) :
    Tendsto (fun n => opTrace (K ∘L T n)) atTop (𝓝 0) := by
  refine tendsto_opTrace_comp_of_isSourceComplete (HilbertSchmidt.lpBasis ℕ)
    isSourceComplete_sourceLabel_fusion T hS (B := B)
    (fun n => by rw [traceNorm_eq_re_opTrace_of_isPositive (hS n) (hpos n)]; exact hB n) (fun a => ?_) K hK
  fin_cases a
  · exact squeeze_zero (fun n => traceNorm_nonneg _)
      (fun n => le_add_of_nonneg_right (traceNorm_nonneg _)) hcomm
  · exact squeeze_zero (fun n => traceNorm_nonneg _)
      (fun n => le_add_of_nonneg_left (traceNorm_nonneg _)) hcomm

end GaloisForLFunctions.HTGeometry
