import GaloisForLFunctions.HTGeometry.WeightedOrbitInduction
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound
import GaloisForLFunctions.HTGeometry.RectangularApproximationNumberLowerBound
import GaloisForLFunctions.HTGeometry.RectangularGramSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Singular values of block-diagonal Hilbert operators

For a uniformly bounded family of compact blocks `T i : E i → F i`, the block-diagonal operator
`⊕ T i` on the Hilbert direct sums has as singular values the multiset union of the singular
values of its blocks.  This module proves that statement in the two forms needed for Schatten
classes, working directly with approximation numbers:

* `count_lt_rectApproxNumber_rectangularBlockOperator` — the **counting law**: for every level
  `t > 0`, the number of approximation numbers of `⊕ T i` above `t` is the sum over the blocks of
  the number of their approximation numbers above `t`;
* `tsum_ofReal_rpow_rectApproxNumber_rectangularBlockOperator` — the **energy law**: for every
  exponent `p > 0`, `∑ₙ aₙ(⊕ T i)^p = ∑ᵢ ∑ₙ aₙ(T i)^p` in `ℝ≥0∞`.

The upper half of the counting law glues block approximants of rank `kᵢ` into a global approximant
of rank `∑ kᵢ`.  The lower half glues the expanding subspaces of the blocks (spanned by the leading
singular vectors) into one global expanding subspace of dimension `∑ kᵢ`, which no operator of
smaller rank can approximate.  The energy law follows from the counting law by the layer-cake
formula for the counting measure on `ℕ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter RHTower MeasureTheory ContinuousLinearMap
open scoped ENNReal Topology InnerProductSpace

noncomputable section

/-! ## Rank-zero operators, rank of finite sums -/

section Rank

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An operator of rank at most zero vanishes. -/
theorem eq_zero_of_hasRectRankLE_zero {A : E →L[ℂ] F} (hA : HasRectRankLE A 0) : A = 0 := by
  obtain ⟨V, _, hdim, hrange⟩ := hA
  have hVbot : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hdim)
  ext x
  have hx := hrange x
  rw [hVbot, Submodule.mem_bot] at hx
  exact hx

theorem hasRectRankLE_finset_sum {κ : Type*} (s : Finset κ) (A : κ → E →L[ℂ] F) (k : κ → ℕ)
    (h : ∀ j ∈ s, HasRectRankLE (A j) (k j)) :
    HasRectRankLE (∑ j ∈ s, A j) (∑ j ∈ s, k j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRectRankLE_zero (E := E) (F := F) 0
  | insert j s hjs ih =>
      rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
      exact (h j (Finset.mem_insert_self j s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rank

/-! ## Isometric and scalar invariance of rectangular approximation numbers -/

section Invariance

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Approximation numbers are unchanged by unitary transport on both sides. -/
theorem rectApproxNumber_unitary_conj (D : E →L[ℂ] F) (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F)
    (n : ℕ) :
    rectApproxNumber (V.toLinearIsometry.toContinuousLinearMap ∘L D ∘L
        U.symm.toLinearIsometry.toContinuousLinearMap) n = rectApproxNumber D n := by
  have hle : ∀ (D' : E →L[ℂ] F) (U' : E ≃ₗᵢ[ℂ] E) (V' : F ≃ₗᵢ[ℂ] F),
      rectApproxNumber (V'.toLinearIsometry.toContinuousLinearMap ∘L D' ∘L
        U'.symm.toLinearIsometry.toContinuousLinearMap) n ≤ rectApproxNumber D' n := by
    intro D' U' V'
    calc rectApproxNumber (V'.toLinearIsometry.toContinuousLinearMap ∘L D' ∘L
          U'.symm.toLinearIsometry.toContinuousLinearMap) n
        ≤ ‖V'.toLinearIsometry.toContinuousLinearMap‖
            * rectApproxNumber (D' ∘L U'.symm.toLinearIsometry.toContinuousLinearMap) n :=
          rectApproxNumber_comp_le_left _ _ n
      _ ≤ 1 * (rectApproxNumber D' n * ‖U'.symm.toLinearIsometry.toContinuousLinearMap‖) := by
          refine mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _)
            (rectApproxNumber_comp_le_right _ _ n) (rectApproxNumber_nonneg _ n) zero_le_one
      _ ≤ 1 * (rectApproxNumber D' n * 1) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (LinearIsometry.norm_toContinuousLinearMap_le _) (rectApproxNumber_nonneg _ n))
            zero_le_one
      _ = rectApproxNumber D' n := by ring
  refine le_antisymm (hle D U V) ?_
  have hback : V.symm.toLinearIsometry.toContinuousLinearMap ∘L
      (V.toLinearIsometry.toContinuousLinearMap ∘L D ∘L
        U.symm.toLinearIsometry.toContinuousLinearMap) ∘L
      U.symm.symm.toLinearIsometry.toContinuousLinearMap = D := by
    ext x
    simp
  calc rectApproxNumber D n
      = rectApproxNumber (V.symm.toLinearIsometry.toContinuousLinearMap ∘L
          (V.toLinearIsometry.toContinuousLinearMap ∘L D ∘L
            U.symm.toLinearIsometry.toContinuousLinearMap) ∘L
          U.symm.symm.toLinearIsometry.toContinuousLinearMap) n := by rw [hback]
    _ ≤ _ := hle _ U.symm V.symm

/-- Approximation numbers are absolutely homogeneous. -/
theorem rectApproxNumber_smul_eq (c : ℂ) (D : E →L[ℂ] F) (n : ℕ) :
    rectApproxNumber (c • D) n = ‖c‖ * rectApproxNumber D n := by
  have hle : ∀ (c' : ℂ) (D' : E →L[ℂ] F),
      rectApproxNumber (c' • D') n ≤ ‖c'‖ * rectApproxNumber D' n := by
    intro c' D'
    have h := rectApproxNumber_comp_le_left (c' • ContinuousLinearMap.id ℂ F) D' n
    have hcomp : (c' • ContinuousLinearMap.id ℂ F) ∘L D' = c' • D' := by
      ext x
      simp
    rw [hcomp] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (rectApproxNumber_nonneg _ n))
    refine (norm_smul_le c' (ContinuousLinearMap.id ℂ F)).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg c') (ContinuousLinearMap.norm_id_le)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [rectApproxNumber_zero]
  refine le_antisymm (hle c D) ?_
  have hback : c⁻¹ • (c • D) = D := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h := hle c⁻¹ (c • D)
  rw [hback, norm_inv] at h
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [inv_mul_eq_div, le_div_iff₀ hcpos] at h
  linarith [h]

end Invariance

/-! ## Compactness and approximation numbers -/

section Compact

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem isCompactOperator_rectangularLowerBlock {T : E →L[ℂ] F} (hT : IsCompactOperator T) :
    IsCompactOperator (rectangularLowerBlock T) :=
  (hT.comp_clm (WithLp.fstL 2 ℂ E F)).clm_comp (rectangularRightInclusion (E := E) (F := F))

/-- A member of a rectangular Schatten class with positive exponent is compact. -/
theorem MemRectSchattenClass.isCompactOperator' {p : ℝ} (hp : 0 < p) {T : E →L[ℂ] F}
    (hT : MemRectSchattenClass p T) : IsCompactOperator T := by
  have hL : IsCompactOperator (rectangularLowerBlock T) :=
    ((memRectSchattenClass_iff_lowerBlock p T).mp hT).isCompactOperator hp
  have h : IsCompactOperator (rectangularCompression (rectangularLowerBlock T)) :=
    (hL.comp_clm (rectangularLeftInclusion (E := E) (F := F))).clm_comp (WithLp.sndL 2 ℂ E F)
  rwa [rectangularCompression_lowerBlock] at h

/-- The approximation numbers of a compact operator tend to zero. -/
theorem tendsto_rectApproxNumber_of_isCompactOperator {T : E →L[ℂ] F}
    (hT : IsCompactOperator T) :
    Tendsto (rectApproxNumber T) atTop (𝓝 0) := by
  have hL := isCompactOperator_rectangularLowerBlock hT
  have hsv : Tendsto (svVal (energyOp (rectangularLowerBlock T))) atTop (𝓝 0) :=
    svVal_tendsto_zero (energyOp_compact hL) (energyOp_symmetric _) (energyOp_pos _)
  have hsq : Tendsto (fun n => Real.sqrt (svVal (energyOp (rectangularLowerBlock T)) n))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsv
  refine hsq.congr fun n => ?_
  rw [rectApproxNumber_eq_approxNumber_lowerBlock, approxNumber_eq_singVal hL n]
  rfl

/-- **Expanding subspaces of a square compact operator.**  If the `n`-th approximation number is
positive, the leading `n + 1` singular vectors span a subspace on which the operator expands by at
least that approximation number. -/
theorem exists_expanding_subspace_square {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hcpt : IsCompactOperator T)
    (n : ℕ) (hpos : 0 < approxNumber T n) :
    ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧
      ∀ w ∈ W, approxNumber T n * ‖w‖ ≤ ‖T w‖ := by
  classical
  have hsym := energyOp_symmetric T
  have hposop := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  rw [approxNumber_eq_singVal hcpt n] at hpos ⊢
  have hne : svVal (energyOp T) n ≠ 0 := by
    intro h0
    rw [singVal, h0, Real.sqrt_zero] at hpos
    exact lt_irrefl _ hpos
  have hlive : ∀ m, m ≤ n → svVal (energyOp T) m ≠ 0 := by
    intro m hm h0'
    apply hne
    have h1 := svVal_antitone (energyOp T) hm
    have h2 := svVal_nonneg (energyOp T) n
    rw [h0'] at h1
    linarith
  have horth : Orthonormal ℂ (fun i : Fin (n + 1) => svVec (energyOp T) i) := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero hScpt hsym hposop (hlive i (Nat.lt_succ_iff.mp i.2))]
      norm_num
    · rw [if_neg hij]
      exact inner_svVec_svVec_of_ne (energyOp T) fun h => hij (Fin.val_injective h)
  set V := Submodule.span ℂ (Set.range fun i : Fin (n + 1) => svVec (energyOp T) i) with hV
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hdim : Module.finrank ℂ V = n + 1 := by
    rw [hV, finrank_span_eq_card horth.linearIndependent]
    simp
  refine ⟨V, inferInstance, hdim, fun z hzV => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzV
  have hSz : energyOp T z
      = ∑ i : Fin (n + 1), (c i * (svVal (energyOp T) i : ℂ)) • svVec (energyOp T) i := by
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, apply_svVec, smul_smul]
  have hre : RCLike.re (inner ℂ z (energyOp T z))
      = ∑ i : Fin (n + 1), ‖c i‖ ^ 2 * svVal (energyOp T) i := by
    rw [hSz, ← hc, horth.inner_sum c (fun i => c i * (svVal (energyOp T) i : ℂ)) Finset.univ,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (starRingEnd ℂ) (c i) * (c i * (svVal (energyOp T) i : ℂ))
        = ((starRingEnd ℂ) (c i) * c i) * (svVal (energyOp T) i : ℂ) from by ring,
      RCLike.conj_mul, RCLike.mul_re]
    simp [← Complex.ofReal_pow]
  have hz_norm_sq : ‖z‖ ^ 2 = ∑ i : Fin (n + 1), ‖c i‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hc, horth.inner_sum c c Finset.univ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hlow : svVal (energyOp T) n * ‖z‖ ^ 2 ≤ ‖T z‖ ^ 2 := by
    rw [← re_inner_energyOp_self T, hre, hz_norm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmono : svVal (energyOp T) n ≤ svVal (energyOp T) i :=
      svVal_antitone (energyOp T) (Nat.lt_succ_iff.mp i.2)
    nlinarith [sq_nonneg ‖c i‖, svVal_nonneg (energyOp T) n]
  have h1 : (singVal T n * ‖z‖) ^ 2 ≤ ‖T z‖ ^ 2 := by
    rw [mul_pow, singVal_sq]
    exact hlow
  have h2 : 0 ≤ singVal T n * ‖z‖ := mul_nonneg (singVal_nonneg T n) (norm_nonneg _)
  nlinarith [norm_nonneg (T z)]

/-- **Expanding subspaces of a rectangular compact operator.**  If the `n`-th approximation
number is positive, some `(n+1)`-dimensional subspace is expanded by at least that number. -/
theorem exists_expanding_subspace {T : E →L[ℂ] F} (hT : IsCompactOperator T) (n : ℕ)
    (hpos : 0 < rectApproxNumber T n) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧
      ∀ w ∈ W, rectApproxNumber T n * ‖w‖ ≤ ‖T w‖ := by
  classical
  set L := rectangularLowerBlock T with hLdef
  have hL : IsCompactOperator L := isCompactOperator_rectangularLowerBlock hT
  have hsL : rectApproxNumber T n = approxNumber L n :=
    rectApproxNumber_eq_approxNumber_lowerBlock T n
  rw [hsL] at hpos ⊢
  obtain ⟨W', hW'fd, hW'dim, hW'⟩ := exists_expanding_subspace_square hL n hpos
  haveI := hW'fd
  set f : W' →ₗ[ℂ] E := (WithLp.fstL 2 ℂ E F : rectangularHilbertSum E F →ₗ[ℂ] E) ∘ₗ W'.subtype
    with hf
  have hLz : ∀ z : rectangularHilbertSum E F, ‖L z‖ = ‖T z.fst‖ := by
    intro z
    rw [hLdef, rectangularLowerBlock_apply]
    exact norm_rectangularRightInclusion_apply (E := E) (F := F) (T z.fst)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz0 : (z : rectangularHilbertSum E F).fst = 0 := hz
    have h := hW' z z.2
    rw [hLz, hz0, map_zero, norm_zero] at h
    have hnz : ‖(z : rectangularHilbertSum E F)‖ = 0 := by
      have := mul_nonneg hpos.le (norm_nonneg (z : rectangularHilbertSum E F))
      have h0 : approxNumber L n * ‖(z : rectangularHilbertSum E F)‖ = 0 := le_antisymm h this
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hpos.ne'
      · exact h0
    exact Subtype.ext (norm_eq_zero.mp hnz)
  refine ⟨LinearMap.range f, LinearMap.finiteDimensional_range f, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, hW'dim]
  · rintro _ ⟨z, rfl⟩
    have h := hW' z z.2
    rw [hLz] at h
    have hfz : f z = (z : rectangularHilbertSum E F).fst := rfl
    rw [hfz]
    calc approxNumber L n * ‖(z : rectangularHilbertSum E F).fst‖
        ≤ approxNumber L n * ‖(z : rectangularHilbertSum E F)‖ :=
          mul_le_mul_of_nonneg_left (norm_fst_le_rectangularHilbertSum _)
            (approxNumber_nonneg L n)
      _ ≤ ‖T (z : rectangularHilbertSum E F).fst‖ := h

end Compact

/-! ## Counting the terms of an antitone sequence above a level -/

section Counting

theorem count_eq_ncard_of_finite {s : Set ℕ} (hs : s.Finite) :
    Measure.count s = (s.ncard : ℝ≥0∞) := by
  rw [Measure.count_apply_finite s hs, Set.ncard_eq_toFinset_card s hs]

/-- For an antitone sequence, a term at or below the level bounds the count above the level. -/
theorem count_lt_le_of_le {s : ℕ → ℝ} (hs : Antitone s) {t : ℝ} {k : ℕ} (hk : s k ≤ t) :
    Measure.count {n : ℕ | t < s n} ≤ k := by
  have hsub : {n : ℕ | t < s n} ⊆ ((Finset.range k : Finset ℕ) : Set ℕ) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hkn
    push Not at hkn
    exact absurd (lt_of_lt_of_le hn (hs hkn)) (not_lt.mpr hk)
  calc Measure.count {n : ℕ | t < s n}
      ≤ Measure.count ((Finset.range k : Finset ℕ) : Set ℕ) := measure_mono hsub
    _ = k := by rw [Measure.count_apply_finset, Finset.card_range]

/-- For an antitone sequence, a term above the level forces all earlier terms above it. -/
theorem le_count_lt_of_lt {s : ℕ → ℝ} (hs : Antitone s) {t : ℝ} {k : ℕ} (hk : t < s k) :
    ((k + 1 : ℕ) : ℝ≥0∞) ≤ Measure.count {n : ℕ | t < s n} := by
  have hsub : ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) ⊆ {n : ℕ | t < s n} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact lt_of_lt_of_le hk (hs (Nat.lt_succ_iff.mp hn))
  calc ((k + 1 : ℕ) : ℝ≥0∞)
      = Measure.count ((Finset.range (k + 1) : Finset ℕ) : Set ℕ) := by
        rw [Measure.count_apply_finset, Finset.card_range]
    _ ≤ _ := measure_mono hsub

theorem le_of_count_lt_eq {s : ℕ → ℝ} (hs : Antitone s) {t : ℝ} {k : ℕ}
    (h : Measure.count {n : ℕ | t < s n} = k) : s k ≤ t := by
  by_contra hlt
  push Not at hlt
  have h1 := le_count_lt_of_lt hs hlt
  rw [h] at h1
  have h2 : k + 1 ≤ k := by exact_mod_cast h1
  omega

theorem lt_of_count_lt_eq {s : ℕ → ℝ} (hs : Antitone s) {t : ℝ} {k : ℕ}
    (h : Measure.count {n : ℕ | t < s n} = k) (hk : 0 < k) : t < s (k - 1) := by
  by_contra hle
  push Not at hle
  have h1 := count_lt_le_of_le hs hle
  rw [h] at h1
  have h2 : k ≤ k - 1 := by exact_mod_cast h1
  omega

end Counting

/-! ## Block-diagonal operators -/

section Block

variable {ι : Type} [DecidableEq ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]

omit [DecidableEq ι] in
theorem norm_rectangularBlockOperator_le (T : ∀ i, E i →L[ℂ] F i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖rectangularBlockOperator T hC hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

omit [DecidableEq ι] in
theorem rectangularBlockOperator_sub (T A : ∀ i, E i →L[ℂ] F i) {C C' C'' : ℝ} (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hC'' : 0 ≤ C'') (hT : ∀ i, ‖T i‖ ≤ C) (hA : ∀ i, ‖A i‖ ≤ C')
    (hTA : ∀ i, ‖T i - A i‖ ≤ C'') :
    rectangularBlockOperator T hC hT - rectangularBlockOperator A hC' hA
      = rectangularBlockOperator (fun i => T i - A i) hC'' hTA := by
  refine ContinuousLinearMap.ext fun x => ?_
  ext i
  simp

/-- A block-diagonal operator with finitely many nonzero blocks is the finite sum of its
transported blocks. -/
theorem rectangularBlockOperator_eq_finset_sum (A : ∀ i, E i →L[ℂ] F i) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) (G : Finset ι) (hG : ∀ i ∉ G, A i = 0) :
    rectangularBlockOperator A hC hA
      = ∑ i ∈ G, lpSingleCLM (G := F) i ∘L A i ∘L lpEvalCLM (G := E) i := by
  refine ContinuousLinearMap.ext fun x => ?_
  ext j
  rw [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [comp_apply, lpSingleCLM_apply, lpEvalCLM_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single (f := fun i => A i ((x : ∀ i, E i) i)), rectangularBlockOperator_apply]
  split_ifs with hj
  · rfl
  · rw [hG j hj]
    rfl

/-- A near-optimal finite-rank approximant. -/
theorem exists_rank_approximant_lt {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] (T : E' →L[ℂ] F') (n : ℕ) {ε : ℝ}
    (hε : rectApproxNumber T n < ε) :
    ∃ A : E' →L[ℂ] F', HasRectRankLE A n ∧ ‖T - A‖ < ε := by
  obtain ⟨r, hrmem, hr⟩ :=
    (csInf_lt_iff (rectApproxNumber_set_bddBelow T n)
      (rectApproxNumber_set_nonempty T n)).mp hε
  obtain ⟨A, hA, rfl⟩ := hrmem
  exact ⟨A, hA, hr⟩

omit [DecidableEq ι] in
/-- **Counting law, upper half.**  Gluing block approximants of rank `kᵢ` gives a global
approximant of rank `∑ kᵢ`, so the global count above a level is at most the sum of the block
counts. -/
theorem count_lt_rectApproxNumber_block_le (T : ∀ i, E i →L[ℂ] F i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    Measure.count {n : ℕ | t < rectApproxNumber (rectangularBlockOperator T hC hT) n}
      ≤ ∑' i, Measure.count {n : ℕ | t < rectApproxNumber (T i) n} := by
  classical
  set N : ι → ℝ≥0∞ := fun i => Measure.count {n : ℕ | t < rectApproxNumber (T i) n} with hN
  by_cases htop : ∑' i, N i = ⊤
  · rw [htop]
    exact le_top
  have hfinS : ∀ i, {n : ℕ | t < rectApproxNumber (T i) n}.Finite := fun i =>
    Measure.count_apply_lt_top.mp (lt_top_iff_ne_top.mpr (ENNReal.ne_top_of_tsum_ne_top htop i))
  set k : ι → ℕ := fun i => {n : ℕ | t < rectApproxNumber (T i) n}.ncard with hk
  have hNk : ∀ i, N i = k i := fun i => count_eq_ncard_of_finite (hfinS i)
  have hsupp : {i | 1 ≤ N i}.Finite := ENNReal.finite_const_le_of_tsum_ne_top htop one_ne_zero
  set G : Finset ι := hsupp.toFinset with hGdef
  have hk0 : ∀ i ∉ G, k i = 0 := by
    intro i hi
    have hnot : ¬ 1 ≤ N i := by simpa [hGdef] using hi
    rw [hNk] at hnot
    have : ¬ 1 ≤ k i := by exact_mod_cast hnot
    omega
  have hsum : ∑' i, N i = ((∑ i ∈ G, k i : ℕ) : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := G) (fun i hi => by rw [hNk, hk0 i hi, Nat.cast_zero]), Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hNk i
  have hblk : ∀ i, rectApproxNumber (T i) (k i) ≤ t := fun i =>
    le_of_count_lt_eq (rectApproxNumber_antitone _) (hNk i)
  have hglob : rectApproxNumber (rectangularBlockOperator T hC hT) (∑ i ∈ G, k i) ≤ t := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hchoice : ∀ i, ∃ A : E i →L[ℂ] F i, HasRectRankLE A (k i) ∧ ‖T i - A‖ < t + ε :=
      fun i => exists_rank_approximant_lt (T i) (k i) (by linarith [hblk i])
    choose A hArank hAnorm using hchoice
    have hAbd : ∀ i, ‖A i‖ ≤ C + (t + ε) := by
      intro i
      have h1 : A i = T i - (T i - A i) := by abel
      calc ‖A i‖ = ‖T i - (T i - A i)‖ := by rw [← h1]
        _ ≤ ‖T i‖ + ‖T i - A i‖ := norm_sub_le _ _
        _ ≤ C + (t + ε) := add_le_add (hT i) (hAnorm i).le
    have hCA : 0 ≤ C + (t + ε) := by positivity
    have hA0 : ∀ i ∉ G, A i = 0 := fun i hi =>
      eq_zero_of_hasRectRankLE_zero (by simpa [hk0 i hi] using hArank i)
    have hrank : HasRectRankLE (rectangularBlockOperator A hCA hAbd) (∑ i ∈ G, k i) := by
      rw [rectangularBlockOperator_eq_finset_sum A hCA hAbd G hA0]
      exact hasRectRankLE_finset_sum G _ k fun i _ =>
        ((hArank i).comp_right (lpEvalCLM (G := E) i)).comp_left (lpSingleCLM (G := F) i)
    calc rectApproxNumber (rectangularBlockOperator T hC hT) (∑ i ∈ G, k i)
        ≤ ‖rectangularBlockOperator T hC hT - rectangularBlockOperator A hCA hAbd‖ :=
          rectApproxNumber_le _ _ _ hrank
      _ = ‖rectangularBlockOperator (fun i => T i - A i) (by positivity : (0 : ℝ) ≤ t + ε)
            (fun i => (hAnorm i).le)‖ := by
          rw [rectangularBlockOperator_sub]
      _ ≤ t + ε := norm_rectangularBlockOperator_le _ _ _
  calc Measure.count {n : ℕ | t < rectApproxNumber (rectangularBlockOperator T hC hT) n}
      ≤ ((∑ i ∈ G, k i : ℕ) : ℝ≥0∞) := count_lt_le_of_le (rectApproxNumber_antitone _) hglob
    _ = ∑' i, N i := hsum.symm

/-- The embedding of a finite family of block vectors, supported on a finite set of indices, into
the Hilbert direct sum. -/
def finsuppBlockEmbedding (G : Finset ι) (W : ∀ i, Submodule ℂ (E i)) :
    ((i : G) → W (i : ι)) →ₗ[ℂ] lp E 2 where
  toFun w := ⟨fun j => if h : j ∈ G then ((w ⟨j, h⟩ : W j) : E j) else 0, by
    refine memℓp_gen (summable_of_ne_finset_zero (s := G) fun j hj => ?_)
    simp [hj]⟩
  map_add' w w' := by
    ext j
    simp only [lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c w := by
    ext j
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem finsuppBlockEmbedding_apply (G : Finset ι) (W : ∀ i, Submodule ℂ (E i))
    (w : (i : G) → W (i : ι)) (j : ι) :
    (finsuppBlockEmbedding G W w : ∀ j, E j) j
      = if h : j ∈ G then ((w ⟨j, h⟩ : W j) : E j) else 0 := rfl

theorem finsuppBlockEmbedding_injective (G : Finset ι) (W : ∀ i, Submodule ℂ (E i)) :
    Function.Injective (finsuppBlockEmbedding G W) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext i
  have h := congrArg (fun z : lp E 2 => (z : ∀ j, E j) (i : ι)) hw
  simp only [finsuppBlockEmbedding_apply, dif_pos i.2, lp.coeFn_zero, Pi.zero_apply] at h
  exact Subtype.ext h

omit [DecidableEq ι] in
/-- **Counting law, lower half.**  The expanding subspaces of the compact blocks glue into one
global expanding subspace, so the sum of the block counts above a positive level is at most the
global count. -/
theorem tsum_count_le_count_lt_rectApproxNumber_block [∀ i, CompleteSpace (E i)]
    [∀ i, CompleteSpace (F i)] (T : ∀ i, E i →L[ℂ] F i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hcpt : ∀ i, IsCompactOperator (T i)) {t : ℝ} (ht : 0 < t) :
    ∑' i, Measure.count {n : ℕ | t < rectApproxNumber (T i) n}
      ≤ Measure.count {n : ℕ | t < rectApproxNumber (rectangularBlockOperator T hC hT) n} := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun G => ?_
  have hfinS : ∀ i, {n : ℕ | t < rectApproxNumber (T i) n}.Finite := by
    intro i
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, rectApproxNumber (T i) n₀ < t :=
      ((tendsto_rectApproxNumber_of_isCompactOperator (hcpt i)).eventually
        (gt_mem_nhds ht)).exists
    refine Measure.count_apply_lt_top.mp (lt_of_le_of_lt
      (count_lt_le_of_le (rectApproxNumber_antitone _) hn₀.le) (ENNReal.natCast_lt_top n₀))
  set k : ι → ℕ := fun i => {n : ℕ | t < rectApproxNumber (T i) n}.ncard with hk
  have hNk : ∀ i, Measure.count {n : ℕ | t < rectApproxNumber (T i) n} = k i := fun i =>
    count_eq_ncard_of_finite (hfinS i)
  rw [Finset.sum_congr rfl fun i _ => hNk i, ← Nat.cast_sum]
  set M := ∑ i ∈ G, k i with hM
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0, Nat.cast_zero]
    exact zero_le
  -- the level of each block and its expanding subspace
  set c : ι → ℝ := fun i => rectApproxNumber (T i) (k i - 1) with hc
  have hct : ∀ i, 0 < k i → t < c i := fun i hki =>
    lt_of_count_lt_eq (rectApproxNumber_antitone _) (hNk i) hki
  have hsub : ∀ i, ∃ W : Submodule ℂ (E i), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = k i ∧ ∀ w ∈ W, c i * ‖w‖ ≤ ‖T i w‖ := by
    intro i
    rcases Nat.eq_zero_or_pos (k i) with hki | hki
    · refine ⟨⊥, inferInstance, by rw [finrank_bot, hki], fun w hw => ?_⟩
      rw [Submodule.mem_bot] at hw
      simp [hw]
    · obtain ⟨W, hWfd, hWdim, hW⟩ := exists_expanding_subspace (hcpt i) (k i - 1)
        (lt_trans ht (hct i hki))
      exact ⟨W, hWfd, by rw [hWdim]; omega, hW⟩
  choose W hWfd hWdim hWexp using hsub
  haveI : ∀ i, FiniteDimensional ℂ (W i) := hWfd
  set G' : Finset ι := G.filter fun i => 0 < k i with hG'
  have hG'ne : G'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hzero : ∀ i ∈ G, k i = 0 := by
      intro i hi
      by_contra hne
      have : i ∈ G' := Finset.mem_filter.mpr ⟨hi, Nat.pos_of_ne_zero hne⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty i)
    have : M = 0 := Finset.sum_eq_zero hzero
    omega
  set c₀ : ℝ := G'.inf' hG'ne c with hc₀
  have htc₀ : t < c₀ := (Finset.lt_inf'_iff hG'ne).mpr fun i hi =>
    hct i (Finset.mem_filter.mp hi).2
  have hc₀le : ∀ i ∈ G', c₀ ≤ c i := fun i hi => Finset.inf'_le c hi
  -- the global expanding subspace
  set Φ := finsuppBlockEmbedding G' W with hΦ
  have hdimX : Module.finrank ℂ ((i : G') → W (i : ι)) = M := by
    rw [Module.finrank_pi_fintype, hM]
    rw [Finset.sum_coe_sort G' (fun i => Module.finrank ℂ (W i))]
    rw [hG', Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hki
    · exact hWdim i
    · omega
  have hlb : ∀ z ∈ LinearMap.range Φ,
      c₀ * ‖z‖ ≤ ‖rectangularBlockOperator T hC hT z‖ := by
    rintro _ ⟨w, rfl⟩
    refine lp_le_norm_of_blockwise (lt_trans ht htc₀).le _ _ fun j => ?_
    rw [rectangularBlockOperator_apply, hΦ, finsuppBlockEmbedding_apply]
    split_ifs with hj
    · have hw := hWexp j _ (w ⟨j, hj⟩).2
      calc c₀ * ‖((w ⟨j, hj⟩ : W j) : E j)‖ ≤ c j * ‖((w ⟨j, hj⟩ : W j) : E j)‖ :=
            mul_le_mul_of_nonneg_right (hc₀le j hj) (norm_nonneg _)
        _ ≤ _ := hw
    · simp
  haveI : FiniteDimensional ℂ (LinearMap.range Φ) := LinearMap.finiteDimensional_range Φ
  have hdim : M - 1 + 1 ≤ Module.finrank ℂ (LinearMap.range Φ) := by
    rw [LinearMap.finrank_range_of_inj (finsuppBlockEmbedding_injective G' W), hdimX]
    omega
  have hlow : c₀ ≤ rectApproxNumber (rectangularBlockOperator T hC hT) (M - 1) :=
    le_rectApproxNumber_of_subspace (LinearMap.range Φ) hdim hlb
  have hcount := le_count_lt_of_lt (rectApproxNumber_antitone _) (lt_of_lt_of_le htc₀ hlow)
  rwa [Nat.sub_add_cancel hMpos] at hcount

omit [DecidableEq ι] in
/-- **Counting law.**  At every positive level, the number of approximation numbers of a
block-diagonal operator with compact blocks above the level is the sum over the blocks of the
numbers of their approximation numbers above the level: the singular values of `⊕ T i` are the
multiset union of those of the blocks. -/
theorem count_lt_rectApproxNumber_rectangularBlockOperator [∀ i, CompleteSpace (E i)]
    [∀ i, CompleteSpace (F i)] (T : ∀ i, E i →L[ℂ] F i) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (hcpt : ∀ i, IsCompactOperator (T i)) {t : ℝ} (ht : 0 < t) :
    Measure.count {n : ℕ | t < rectApproxNumber (rectangularBlockOperator T hC hT) n}
      = ∑' i, Measure.count {n : ℕ | t < rectApproxNumber (T i) n} :=
  le_antisymm (count_lt_rectApproxNumber_block_le T hC hT ht.le)
    (tsum_count_le_count_lt_rectApproxNumber_block T hC hT hcpt ht)

end Block

/-! ## From counting laws to energy laws -/

section Energy

/-- The layer-cake formula for a nonnegative sequence: its `p`-energy is the integral of its
counting function against `p t^{p-1} dt`. -/
theorem tsum_ofReal_rpow_eq_layerCake {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {p : ℝ} (hp : 0 < p) :
    ∑' n, ENNReal.ofReal (s n ^ p)
      = ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0,
          Measure.count {n : ℕ | t < s n} * ENNReal.ofReal (t ^ (p - 1)) := by
  rw [← lintegral_count]
  exact lintegral_rpow_eq_lintegral_meas_lt_mul Measure.count (Eventually.of_forall hs)
    (measurable_of_countable s).aemeasurable hp

theorem measurable_count_lt (s : ℕ → ℝ) :
    Measurable fun t : ℝ => Measure.count {n : ℕ | t < s n} := by
  refine Antitone.measurable fun t t' htt' => measure_mono fun n hn => ?_
  exact lt_of_le_of_lt htt' hn

/-- **Counting laws give energy laws.**  If the counting function of one antitone nonnegative
sequence is, at every positive level, the sum of the counting functions of a countable family,
then the `p`-energies add, for every `p > 0`. -/
theorem tsum_ofReal_rpow_eq_of_count {κ : Type*} [Countable κ] {s : ℕ → ℝ} {u : κ → ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hu : ∀ i n, 0 ≤ u i n)
    (hcount : ∀ t : ℝ, 0 < t →
      Measure.count {n : ℕ | t < s n} = ∑' i, Measure.count {n : ℕ | t < u i n})
    {p : ℝ} (hp : 0 < p) :
    ∑' n, ENNReal.ofReal (s n ^ p) = ∑' i, ∑' n, ENNReal.ofReal (u i n ^ p) := by
  have hg : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (p - 1)) :=
    (measurable_id.pow_const (p - 1)).ennreal_ofReal
  rw [tsum_ofReal_rpow_eq_layerCake hs hp,
    setLIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hcount t ht])]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [lintegral_tsum (f := fun i (t : ℝ) =>
      Measure.count {n : ℕ | t < u i n} * ENNReal.ofReal (t ^ (p - 1)))
      fun i => ((measurable_count_lt (u i)).mul hg).aemeasurable, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => (tsum_ofReal_rpow_eq_layerCake (hu i) hp).symm

variable {ι : Type} [Countable ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]

/-- **Energy law for block-diagonal operators.**  For every exponent `p > 0`, the Schatten
`p`-energy of a block-diagonal operator with compact blocks is the sum of the `p`-energies of its
blocks. -/
theorem tsum_ofReal_rpow_rectApproxNumber_rectangularBlockOperator (T : ∀ i, E i →L[ℂ] F i)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) (hcpt : ∀ i, IsCompactOperator (T i)) {p : ℝ}
    (hp : 0 < p) :
    ∑' n, ENNReal.ofReal (rectApproxNumber (rectangularBlockOperator T hC hT) n ^ p)
      = ∑' i, ∑' n, ENNReal.ofReal (rectApproxNumber (T i) n ^ p) :=
  tsum_ofReal_rpow_eq_of_count (fun n => rectApproxNumber_nonneg _ n)
    (fun _ n => rectApproxNumber_nonneg _ n)
    (fun _ ht => count_lt_rectApproxNumber_rectangularBlockOperator T hC hT hcpt ht) hp

end Energy

end

end GaloisForLFunctions.HTGeometry
