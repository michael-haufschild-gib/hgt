import GaloisForLFunctions.HTGeometry.HilbertSchmidtLyapunovInverse

/-!
# The operator norm is dominated by the Hilbert–Schmidt norm

Expanding a vector in the canonical Hilbert basis and applying the Cauchy–Schwarz inequality for
real series gives `‖T x‖ ≤ ‖T‖_HS ‖x‖`, hence `‖T‖ ≤ ‖T‖_HS`.  This is the comparison that turns
Hilbert–Schmidt Cauchy sequences into operator-norm Cauchy sequences and, together with the Fatou
lemma `isHilbertSchmidt_of_tendsto`, gives completeness of the Hilbert–Schmidt class.
-/

open scoped BigOperators InnerProductSpace
open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Pointwise Hilbert–Schmidt bound**: `‖T x‖ ≤ ‖T‖_HS ‖x‖`. -/
theorem norm_apply_le_hsNorm {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (x : E) :
    ‖T x‖ ≤ hsNorm T * ‖x‖ := by
  set b := hsBasis 𝕜 E with hb
  have hrepr : HasSum (fun i => (inner 𝕜 (b i) x : 𝕜) • b i) x := by
    have h := b.hasSum_repr x
    refine h.congr_fun fun i => ?_
    rw [HilbertBasis.repr_apply_apply]
  have hTsum : HasSum (fun i => (inner 𝕜 (b i) x : 𝕜) • T (b i)) (T x) := by
    have h := T.hasSum hrepr
    refine h.congr_fun fun i => ?_
    rw [T.map_smul]
  have hsq1 : Summable (fun i => ‖(inner 𝕜 (b i) x : 𝕜)‖ ^ 2) := HilbertBasis.summable_norm_inner_sq b x
  have hsq2 : Summable (fun i => ‖T (b i)‖ ^ 2) := hT.summable b
  have hsummable : Summable (fun i => ‖(inner 𝕜 (b i) x : 𝕜)‖ * ‖T (b i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      ((hsq1.add hsq2).div_const 2)
    nlinarith [sq_nonneg (‖(inner 𝕜 (b i) x : 𝕜)‖ - ‖T (b i)‖)]
  have hnormsum : Summable (fun i => ‖(inner 𝕜 (b i) x : 𝕜) • T (b i)‖) := by
    refine hsummable.congr fun i => ?_
    rw [norm_smul]
  calc ‖T x‖ = ‖∑' i, (inner 𝕜 (b i) x : 𝕜) • T (b i)‖ := by rw [hTsum.tsum_eq]
    _ ≤ ∑' i, ‖(inner 𝕜 (b i) x : 𝕜) • T (b i)‖ := norm_tsum_le_tsum_norm hnormsum
    _ = ∑' i, ‖(inner 𝕜 (b i) x : 𝕜)‖ * ‖T (b i)‖ := by
        exact tsum_congr fun i => by rw [norm_smul]
    _ ≤ Real.sqrt (∑' i, ‖T (b i)‖ ^ 2) * Real.sqrt (∑' i, ‖(inner 𝕜 (b i) x : 𝕜)‖ ^ 2) := by
        rw [show (fun i => ‖(inner 𝕜 (b i) x : 𝕜)‖ * ‖T (b i)‖)
          = fun i => ‖T (b i)‖ * ‖(inner 𝕜 (b i) x : 𝕜)‖ from funext fun i => mul_comm _ _]
        exact tsum_mul_le_sqrt_mul_sqrt hsq2 hsq1
    _ = hsNorm T * ‖x‖ := by
        rw [HilbertBasis.tsum_norm_inner_sq b x, Real.sqrt_sq (norm_nonneg x)]
        congr 1

/-- **The operator norm is dominated by the Hilbert–Schmidt norm.** -/
theorem norm_le_hsNorm {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T :=
  T.opNorm_le_bound (hsNorm_nonneg T) (norm_apply_le_hsNorm hT)

omit [CompleteSpace F] in
/-- The Hilbert–Schmidt norm is absolutely homogeneous. -/
theorem hsNorm_smul (c : 𝕜) (T : E →L[𝕜] F) : hsNorm (c • T) = ‖c‖ * hsNorm T := by
  have hfun : (fun i => ‖(c • T) (hsBasis 𝕜 E i)‖ ^ 2)
      = fun i => ‖c‖ ^ 2 * ‖T (hsBasis 𝕜 E i)‖ ^ 2 := by
    funext i
    rw [smul_apply, norm_smul, mul_pow]
  have hsq : hsNormSq (c • T) = ‖c‖ ^ 2 * hsNormSq T := by
    show ∑' i, ‖(c • T) (hsBasis 𝕜 E i)‖ ^ 2 = ‖c‖ ^ 2 * ∑' i, ‖T (hsBasis 𝕜 E i)‖ ^ 2
    rw [hfun, tsum_mul_left]
  show Real.sqrt (hsNormSq (c • T)) = ‖c‖ * Real.sqrt (hsNormSq T)
  rw [hsq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

/-- Operator-norm bound for a sandwich, in `hsNorm` form. -/
theorem hsNorm_sandwich_le {S T Y : E →L[𝕜] E} (hY : IsHilbertSchmidt Y) :
    hsNorm (S ∘L (Y ∘L T)) ≤ ‖S‖ * ‖T‖ * hsNorm Y := by
  have h := Real.sqrt_le_sqrt (hsNormSq_sandwich_le (S := S) (T := T) hY)
  rw [Real.sqrt_mul (by positivity), show ‖S‖ ^ 2 * ‖T‖ ^ 2 = (‖S‖ * ‖T‖) ^ 2 by ring,
    Real.sqrt_sq (by positivity)] at h
  exact h

omit [CompleteSpace F] in
/-- The Hilbert–Schmidt norm of a finite sum is at most the sum of the norms. -/
theorem hsNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → E →L[𝕜] F}
    (hf : ∀ i ∈ s, IsHilbertSchmidt (f i)) :
    hsNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, hsNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsNorm_zero]
  | insert i s hi ih =>
    have hmem : ∀ j ∈ s, IsHilbertSchmidt (f j) := fun j hj =>
      hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (hsNorm_add_le (hf i (Finset.mem_insert_self i s))
      (IsHilbertSchmidt.sum s hmem)).trans ?_
    linarith [ih hmem]

omit [CompleteSpace F] in
/-- Left subtractivity of the Hilbert–Schmidt inner product. -/
theorem hsInner_neg_left (S T : E →L[𝕜] F) : hsInner (-S) T = -hsInner S T := by
  have h := hsInner_smul_left (-1 : 𝕜) S T
  rwa [neg_one_smul, map_neg, map_one, neg_one_mul] at h

/-- Left subtractivity of the Hilbert–Schmidt inner product. -/
theorem hsInner_sub_left {S₁ S₂ T : E →L[𝕜] F} (h₁ : IsHilbertSchmidt S₁)
    (h₂ : IsHilbertSchmidt S₂) (hT : IsHilbertSchmidt T) :
    hsInner (S₁ - S₂) T = hsInner S₁ T - hsInner S₂ T := by
  rw [sub_eq_add_neg, hsInner_add_left h₁ h₂.neg hT, hsInner_neg_left, ← sub_eq_add_neg]

omit [CompleteSpace F] in
/-- Right subtractivity of the Hilbert–Schmidt inner product. -/
theorem hsInner_neg_right (S T : E →L[𝕜] F) : hsInner S (-T) = -hsInner S T := by
  have h := hsInner_smul_right (-1 : 𝕜) S T
  rwa [neg_one_smul, neg_one_mul] at h

/-- Right subtractivity of the Hilbert–Schmidt inner product. -/
theorem hsInner_sub_right {S T₁ T₂ : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (h₁ : IsHilbertSchmidt T₁) (h₂ : IsHilbertSchmidt T₂) :
    hsInner S (T₁ - T₂) = hsInner S T₁ - hsInner S T₂ := by
  rw [sub_eq_add_neg, hsInner_add_right hS h₁ h₂.neg, hsInner_neg_right, ← sub_eq_add_neg]

/-- **Expansion of the squared Hilbert–Schmidt norm of a difference.** -/
theorem hsNormSq_sub {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNormSq (S - T) = hsNormSq S - 2 * RCLike.re (hsInner S T) + hsNormSq T := by
  have hST : IsHilbertSchmidt (S - T) := hS.sub hT
  have h1 : hsInner (S - T) (S - T)
      = (hsInner S S - hsInner S T) - (hsInner T S - hsInner T T) := by
    rw [hsInner_sub_left hS hT hST, hsInner_sub_right hS hS hT, hsInner_sub_right hT hS hT]
  have h2 : RCLike.re (hsInner T S) = RCLike.re (hsInner S T) := by
    rw [hsInner_conj_symm T S, RCLike.conj_re]
  rw [← hsInner_self_re hST, h1, map_sub, map_sub, map_sub, hsInner_self_re hS,
    hsInner_self_re hT, h2]
  ring

/-! ### Completeness of the Hilbert–Schmidt class -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- Operator-norm convergence gives pointwise convergence. -/
lemma tendsto_apply_of_tendsto {Tn : ℕ → E →L[𝕜] F} {T : E →L[𝕜] F}
    (h : Tendsto Tn atTop (nhds T)) (x : E) :
    Tendsto (fun n => Tn n x) atTop (nhds (T x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n => ‖Tn n - T‖ * ‖x‖) (fun n => norm_nonneg _)
    (fun n => (Tn n - T).le_opNorm x) ?_
  have h0 : Tendsto (fun n => ‖Tn n - T‖) atTop (nhds 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero] at *
    exact h
  simpa using h0.mul_const ‖x‖

/-- **Completeness of the Hilbert–Schmidt class**, stated without a bundled space: a
Hilbert–Schmidt Cauchy sequence has a Hilbert–Schmidt limit in the Hilbert–Schmidt norm. -/
theorem exists_hsNorm_limit {Tn : ℕ → E →L[𝕜] F} (hHS : ∀ n, IsHilbertSchmidt (Tn n))
    (hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hsNorm (Tn m - Tn n) ≤ ε) :
    ∃ T, IsHilbertSchmidt T ∧ Tendsto (fun n => hsNorm (Tn n - T)) atTop (nhds 0) := by
  have hopCauchy : CauchySeq Tn := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε/2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 : ‖Tn m - Tn n‖ ≤ hsNorm (Tn m - Tn n) := norm_le_hsNorm ((hHS m).sub (hHS n))
    have h2 := hN m hm n hn
    rw [dist_eq_norm]
    linarith
  obtain ⟨T, hTlim⟩ := cauchySeq_tendsto_of_complete hopCauchy
  have hkey : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      IsHilbertSchmidt (Tn n - T) ∧ hsNormSq (Tn n - T) ≤ ε ^ 2 := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hbd : ∀ k : ℕ, hsNormSq (Tn n - Tn (k + N)) ≤ ε ^ 2 := by
      intro k
      have h := hN n hn (k + N) (Nat.le_add_left N k)
      calc hsNormSq (Tn n - Tn (k + N)) = (hsNorm (Tn n - Tn (k + N))) ^ 2 := (sq_hsNorm _).symm
        _ ≤ ε ^ 2 := pow_le_pow_left₀ (hsNorm_nonneg _) h 2
    have hptw : ∀ x : E, Tendsto (fun k => (Tn n - Tn (k + N)) x) atTop
        (nhds ((Tn n - T) x)) := by
      intro x
      have hsub : Tendsto (fun k => Tn (k + N) x) atTop (nhds (T x)) :=
        (tendsto_apply_of_tendsto hTlim x).comp (tendsto_add_atTop_nat N)
      have hd := (tendsto_const_nhds (x := Tn n x) (f := atTop (α := ℕ))).sub hsub
      refine hd.congr fun k => ?_
      rw [sub_apply]
    have hHSk : ∀ k : ℕ, IsHilbertSchmidt (Tn n - Tn (k + N)) :=
      fun k => (hHS n).sub (hHS (k + N))
    exact ⟨isHilbertSchmidt_of_tendsto hHSk hbd hptw,
      hsNormSq_le_of_tendsto hHSk hbd hptw⟩
  refine ⟨T, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hkey 1 one_pos
    have h := (hN N le_rfl).1
    have hTeq : T = Tn N - (Tn N - T) := by abel
    rw [hTeq]
    exact (hHS N).sub h
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hkey (ε/2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have h := (hN n hn).2
    have hnn : 0 ≤ hsNorm (Tn n - T) := hsNorm_nonneg _
    have hsq : (hsNorm (Tn n - T)) ^ 2 ≤ (ε/2) ^ 2 := by rw [sq_hsNorm]; exact h
    have hle : hsNorm (Tn n - T) ≤ ε/2 := by nlinarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith

end ContinuousLinearMap
