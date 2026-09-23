import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Diagonal operators with eigenvalues tending to zero are compact

An operator diagonal in a Hilbert basis is the operator-norm limit of its finite truncations: the
defect on the complement of a finite set is an orthogonal combination whose norm is bounded by the
supremum of the eigenvalues outside that set.  If the eigenvalues tend to zero along the cofinite
filter, every threshold is exceeded only finitely often, so the truncations converge and the
operator is compact.

This is the compact-resolvent statement for a discrete spectrum: the resolvent of a self-adjoint
operator with eigenvalues `λⱼ` is diagonal with eigenvalues `(λⱼ - i)⁻¹`, and those tend to zero
exactly when every bounded spectral window contains finitely many eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap Filter

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for a finite orthonormal combination.** -/
theorem norm_sq_sum_smul_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (l : ι → 𝕜) (s : Finset ι) : ‖∑ i ∈ s, l i • v i‖ ^ (2 : ℕ) = ∑ i ∈ s, ‖l i‖ ^ (2 : ℕ) := by
  have h := hv.inner_sum l l s
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [Finset.sum_congr rfl fun i _ => RCLike.conj_mul (l i)] at h
  exact_mod_cast h

variable [CompleteSpace E]

/-- **The truncation defect of a diagonal operator is bounded by its tail eigenvalues.**  Outside
a finite set the operator acts as an orthogonal combination with coefficients `⟨bᵢ, x⟩ cᵢ`, so
Pythagoras and Bessel give `‖T - Tₛ‖ ≤ ε` whenever `‖cᵢ‖ ≤ ε` off `s`. -/
theorem norm_sub_hsTruncation_diag_le {ι : Type*} (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] E}
    {c : ι → 𝕜} (hdiag : ∀ i, T (b i) = c i • b i) (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ i, i ∉ s → ‖c i‖ ≤ ε) : ‖T - hsTruncation b T s‖ ≤ ε := by
  refine opNorm_le_bound _ hε fun x => ?_
  rw [sub_apply, sub_hsTruncation_apply]
  set f : {i // i ∉ s} → E := fun i => (inner 𝕜 (b i) x) • T (b i) with hf
  have hsummable : Summable f := ((hasSum_inner_smul b T x).summable).subtype _
  have hortho : Orthonormal 𝕜 fun i : {i // i ∉ s} => b (i : ι) :=
    b.orthonormal.comp _ Subtype.val_injective
  have hrewrite : ∀ i : {i // i ∉ s},
      f i = ((inner 𝕜 (b (i : ι)) x) * c (i : ι)) • b (i : ι) := by
    intro i
    rw [hf]
    simp only
    rw [hdiag, smul_smul]
  have hbound : ∀ u : Finset {i // i ∉ s}, ‖∑ i ∈ u, f i‖ ≤ ε * ‖x‖ := by
    intro u
    have hsq : ‖∑ i ∈ u, f i‖ ^ (2 : ℕ)
        = ∑ i ∈ u, ‖(inner 𝕜 (b (i : ι)) x) * c (i : ι)‖ ^ (2 : ℕ) := by
      rw [Finset.sum_congr rfl fun i _ => hrewrite i]
      exact norm_sq_sum_smul_orthonormal hortho _ u
    have hle : ∑ i ∈ u, ‖(inner 𝕜 (b (i : ι)) x) * c (i : ι)‖ ^ (2 : ℕ)
        ≤ ε ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := by
      have hstep : ∀ i ∈ u, ‖(inner 𝕜 (b (i : ι)) x) * c (i : ι)‖ ^ (2 : ℕ)
          ≤ ε ^ (2 : ℕ) * ‖inner 𝕜 (b (i : ι)) x‖ ^ (2 : ℕ) := by
        intro i _
        rw [norm_mul, mul_pow]
        have hcε : ‖c (i : ι)‖ ≤ ε := hc (i : ι) i.2
        have h1 : ‖c (i : ι)‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by nlinarith [norm_nonneg (c (i : ι))]
        nlinarith [sq_nonneg ‖inner 𝕜 (b (i : ι)) x‖, norm_nonneg (inner 𝕜 (b (i : ι)) x)]
      calc ∑ i ∈ u, ‖(inner 𝕜 (b (i : ι)) x) * c (i : ι)‖ ^ (2 : ℕ)
          ≤ ∑ i ∈ u, ε ^ (2 : ℕ) * ‖inner 𝕜 (b (i : ι)) x‖ ^ (2 : ℕ) := Finset.sum_le_sum hstep
        _ = ε ^ (2 : ℕ) * ∑ i ∈ u, ‖inner 𝕜 (b (i : ι)) x‖ ^ (2 : ℕ) := by rw [Finset.mul_sum]
        _ ≤ ε ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left (Orthonormal.sum_inner_products_le x hortho)
              (by positivity)
    have hfinal : ‖∑ i ∈ u, f i‖ ^ (2 : ℕ) ≤ (ε * ‖x‖) ^ (2 : ℕ) := by
      rw [hsq, mul_pow]
      exact hle
    have hnn : 0 ≤ ε * ‖x‖ := mul_nonneg hε (norm_nonneg x)
    nlinarith [norm_nonneg (∑ i ∈ u, f i)]
  have htend : Tendsto (fun u : Finset {i // i ∉ s} => ‖∑ i ∈ u, f i‖) atTop
      (nhds ‖∑' i, f i‖) :=
    (continuous_norm.tendsto _).comp hsummable.hasSum
  exact le_of_tendsto htend (Eventually.of_forall hbound)

/-- **A diagonal operator whose eigenvalues tend to zero is compact.**  Every threshold is
exceeded on a finite set only, so the finite-rank truncations converge to the operator in norm,
and the compact operators are norm closed. -/
theorem isCompactOperator_of_diag_tendsto_cofinite {ι : Type*} (b : HilbertBasis ι 𝕜 E)
    {T : E →L[𝕜] E} {c : ι → 𝕜} (hdiag : ∀ i, T (b i) = c i • b i)
    (hc : Tendsto (fun i => ‖c i‖) cofinite (nhds 0)) : IsCompactOperator T := by
  classical
  have hcl : T ∈ closure {W : E →L[𝕜] E | IsCompactOperator W} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    have hhalf : (0 : ℝ) < δ / 2 := by linarith
    have hev : ∀ᶠ i in cofinite, ‖c i‖ ≤ δ / 2 := by
      have := Metric.tendsto_nhds.mp hc (δ / 2) hhalf
      filter_upwards [this] with i hi
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi
      exact le_of_lt hi
    have hfin : {i | ¬ ‖c i‖ ≤ δ / 2}.Finite := Filter.eventually_cofinite.mp hev
    refine ⟨hsTruncation b T hfin.toFinset, isCompactOperator_hsTruncation _ _ _, ?_⟩
    rw [dist_eq_norm]
    have hbdd : ∀ i, i ∉ hfin.toFinset → ‖c i‖ ≤ δ / 2 := by
      intro i hi
      by_contra hcon
      exact hi (Set.Finite.mem_toFinset hfin |>.2 hcon)
    exact lt_of_le_of_lt
      (norm_sub_hsTruncation_diag_le b hdiag hfin.toFinset (le_of_lt hhalf) hbdd) (by linarith)
  exact isClosed_setOf_isCompactOperator.closure_subset hcl

section Resolvent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Compactness of the resolvent of a discrete spectrum.**  If the spectral points `λᵢ` leave
every bounded window — equivalently `|λᵢ| → ∞` along the cofinite filter — then the operator
diagonal in the eigenbasis with eigenvalues `(λᵢ - i)⁻¹` is compact.  This is clause 3: a
one-parameter unitary flow whose smoothings have finite-dimensional spectral windows has compact
resolvent. -/
theorem isCompactOperator_resolvent_of_tendsto_cofinite {ι : Type*} (b : HilbertBasis ι ℂ E)
    {R : E →L[ℂ] E} {lam : ι → ℝ}
    (hdiag : ∀ i, R (b i) = ((lam i : ℂ) - Complex.I)⁻¹ • b i)
    (hlam : Tendsto (fun i => |lam i|) cofinite atTop) : IsCompactOperator R := by
  refine isCompactOperator_of_diag_tendsto_cofinite b hdiag ?_
  have hge : ∀ i, |lam i| ≤ ‖(lam i : ℂ) - Complex.I‖ := by
    intro i
    have hre : ((lam i : ℂ) - Complex.I).re = lam i := by simp
    have := Complex.abs_re_le_norm ((lam i : ℂ) - Complex.I)
    rwa [hre] at this
  have hbig : Tendsto (fun i => ‖(lam i : ℂ) - Complex.I‖) cofinite atTop :=
    tendsto_atTop_mono hge hlam
  have hinv : Tendsto (fun i => (‖(lam i : ℂ) - Complex.I‖)⁻¹) cofinite (nhds 0) :=
    hbig.inv_tendsto_atTop
  refine hinv.congr fun i => ?_
  rw [norm_inv]

end Resolvent

end GaloisForLFunctions.HTGeometry
