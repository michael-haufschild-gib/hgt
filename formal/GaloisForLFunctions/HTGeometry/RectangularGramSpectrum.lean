/-
# Rectangular Gram spectra

This module proves the exact multiplicity-preserving bridge between rectangular
approximation numbers and the positive spectrum of the domain Gram operator.
-/
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.CompactAdjoint
import GaloisForLFunctions.RHTower.ApproximationNumberLowerBound
import GaloisForLFunctions.RHTower.SchattenTwoIdentity

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Approximation numbers of a compact positive operator are its greedy positive eigenvalues. -/
theorem approxNumber_eq_svVal_of_isPositive
    {S : H →L[ℂ] H} (hcpt : IsCompactOperator S) (hS : S.IsPositive) (n : ℕ) :
    approxNumber S n = svVal S n := by
  classical
  have hsym := hS.isSymmetric
  have hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x)) := by
    intro x
    have hx := hS.2 x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at hx
    rw [inner_re_symm]
    exact hx
  set e : ℕ → H := svVec S with he
  set F : H →L[ℂ] H :=
    ∑ m ∈ Finset.range n, (innerSL ℂ (e m)).smulRight (S (e m)) with hF
  have hrank : HasRankLE F n := by
    refine ⟨Submodule.span ℂ (((Finset.range n).image fun m => S (e m) : Finset H) : Set H),
      FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
    · refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
      simp
    · intro x
      rw [hF, sum_apply]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hm)))
  have hupp : approxNumber S n ≤ svVal S n := by
    refine (approxNumber_le S n F hrank).trans ?_
    refine opNorm_le_bound _ (svVal_nonneg S n) fun x => ?_
    set P : H := ∑ m ∈ Finset.range n, (inner ℂ (e m) x) • e m with hP
    have hFx : F x = S P := by
      rw [hF, sum_apply, hP, map_sum]
      exact Finset.sum_congr rfl fun m _ => by
        rw [smulRight_apply, innerSL_apply_apply, map_smul]
    have hunit_sq : ∀ m,
        (inner ℂ (e m) x) * ((‖e m‖ : ℂ)) ^ (2 : ℕ) = inner ℂ (e m) x := by
      intro m
      rcases eq_or_ne (svVal S m) 0 with h0 | hne0
      · rw [he, svVec_eq_zero_of_svVal_eq_zero S h0]
        simp
      · rw [he, norm_svVec_of_ne_zero hcpt hsym hpos hne0]
        simp
    have hy_orth : ∀ k < n, inner ℂ (e k) (x - P) = 0 := by
      intro k hk
      rw [inner_sub_right, hP, inner_sum]
      have hsum : ∑ m ∈ Finset.range n,
          inner ℂ (e k) ((inner ℂ (e m) x) • e m) = inner ℂ (e k) x := by
        rw [Finset.sum_eq_single k]
        · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
          exact hunit_sq k
        · intro m hm hmk
          rw [inner_smul_right, he,
            inner_svVec_svVec_of_ne S (Ne.symm hmk), mul_zero]
        · intro hk'
          exact absurd (Finset.mem_range.mpr hk) hk'
      rw [hsum, sub_self]
    have hy_le : ‖x - P‖ ≤ ‖x‖ := by
      have hyP : RCLike.re (inner ℂ (x - P) P) = 0 := by
        rw [hP, inner_sum]
        have hz : ∀ m ∈ Finset.range n,
            inner ℂ (x - P) ((inner ℂ (e m) x) • e m) = 0 := by
          intro m hm
          rw [inner_smul_right,
            show inner ℂ (x - P) (e m) =
                (starRingEnd ℂ) (inner ℂ (e m) (x - P)) from
              (inner_conj_symm _ _).symm,
            hy_orth m (Finset.mem_range.mp hm), map_zero, mul_zero]
        rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
        simp
      have hsq := norm_add_sq (𝕜 := ℂ) (x - P) P
      rw [hyP, sub_add_cancel] at hsq
      nlinarith [norm_nonneg (x - P), norm_nonneg x, sq_nonneg ‖P‖]
    calc
      ‖(S - F) x‖ = ‖S (x - P)‖ := by rw [sub_apply, hFx, ← map_sub]
      _ ≤ svVal S n * ‖x - P‖ := norm_apply_le_of_orth S n hy_orth
      _ ≤ svVal S n * ‖x‖ :=
        mul_le_mul_of_nonneg_left hy_le (svVal_nonneg S n)
  apply le_antisymm hupp
  rcases eq_or_ne (svVal S n) 0 with h0 | hne
  · rw [h0]
    exact approxNumber_nonneg S n
  · have hlive : ∀ m, m ≤ n → svVal S m ≠ 0 := by
      intro m hm h0'
      apply hne
      have h1 := svVal_antitone S hm
      have h2 := svVal_nonneg S n
      rw [h0'] at h1
      linarith
    have horth : Orthonormal ℂ (fun i : Fin (n + 1) => svVec S i) := by
      rw [orthonormal_iff_ite]
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
          norm_svVec_of_ne_zero hcpt hsym hpos
            (hlive i (Nat.lt_succ_iff.mp i.2))]
        norm_num
      · rw [if_neg hij]
        exact inner_svVec_svVec_of_ne S fun h => hij (Fin.val_injective h)
    let V := Submodule.span ℂ (Set.range fun i : Fin (n + 1) => svVec S i)
    haveI : FiniteDimensional ℂ V :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have hdim : Module.finrank ℂ V = n + 1 := by
      dsimp [V]
      rw [finrank_span_eq_card horth.linearIndependent]
      simp
    refine le_approxNumber_of_subspace V (by omega) ?_
    intro z hzV
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hzV
    have hSz : S z =
        ∑ i : Fin (n + 1), (c i * (svVal S i : ℂ)) • svVec S i := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, apply_svVec, smul_smul]
    have hnormSz : ‖S z‖ ^ (2 : ℕ) =
        ∑ i : Fin (n + 1), ‖c i‖ ^ (2 : ℕ) * svVal S i ^ (2 : ℕ) := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hSz,
        horth.inner_sum (fun i => c i * (svVal S i : ℂ))
          (fun i => c i * (svVal S i : ℂ)) Finset.univ,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (svVal_nonneg S i), mul_pow]
    have hnormz : ‖z‖ ^ (2 : ℕ) = ∑ i : Fin (n + 1), ‖c i‖ ^ (2 : ℕ) := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hc,
        horth.inner_sum c c Finset.univ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hsq : (svVal S n * ‖z‖) ^ (2 : ℕ) ≤ ‖S z‖ ^ (2 : ℕ) := by
      rw [hnormSz, mul_pow, hnormz, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hmono : svVal S n ≤ svVal S i :=
        svVal_antitone S (Nat.lt_succ_iff.mp i.2)
      have hsquare : svVal S n ^ (2 : ℕ) ≤ svVal S i ^ (2 : ℕ) :=
        pow_le_pow_left₀ (svVal_nonneg S n) hmono 2
      calc
        svVal S n ^ (2 : ℕ) * ‖c i‖ ^ (2 : ℕ) ≤ svVal S i ^ (2 : ℕ) * ‖c i‖ ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
        _ = ‖c i‖ ^ (2 : ℕ) * svVal S i ^ (2 : ℕ) := by ring
    have hnonneg : 0 ≤ svVal S n * ‖z‖ :=
      mul_nonneg (svVal_nonneg S n) (norm_nonneg z)
    nlinarith [norm_nonneg (S z)]

/-- Squaring an approximation number gives the corresponding approximation number of the
positive Gram operator. -/
theorem approxNumber_sq_eq_approxNumber_energyOp
    {T : H →L[ℂ] H} (hcpt : IsCompactOperator T) (n : ℕ) :
    approxNumber T n ^ (2 : ℕ) = approxNumber (energyOp T) n := by
  rw [approxNumber_eq_singVal hcpt n, singVal_sq,
    approxNumber_eq_svVal_of_isPositive (energyOp_compact hcpt)]
  simpa [energyOp] using ContinuousLinearMap.isPositive_adjoint_comp_self T

section Rectangular

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every rectangular finite-rank operator is compact. -/
theorem HasRectRankLE.isCompactOperator
    {T : E →L[ℂ] F} {n : ℕ} (hT : HasRectRankLE T n) :
    IsCompactOperator T := by
  obtain ⟨V, hV, -, hRange⟩ := hT
  letI : FiniteDimensional ℂ V := hV
  let S : E →L[ℂ] V := T.codRestrict V hRange
  have hS : IsCompactOperator S :=
    isCompactOperator_of_locallyCompactSpace_dom S
  have hfactor : V.subtypeL ∘L S = T := by
    ext x
    rfl
  rw [← hfactor]
  exact hS.clm_comp V.subtypeL

/-- Exact rectangular Gram-square law, retaining every zero and multiplicity. -/
theorem rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self
    (T : E →L[ℂ] F) (hcpt : IsCompactOperator T) (n : ℕ) :
    rectApproxNumber T n ^ (2 : ℕ) = approxNumber (adjoint T ∘L T) n := by
  let R : E →L[ℂ] E := rangeCovarianceRoot (adjoint T)
  obtain ⟨A, hA, hAdj⟩ := exists_factor_through_rangeCovarianceRoot (adjoint T)
  obtain ⟨B, hB, hR⟩ := exists_rangeCovarianceRoot_factor_through (adjoint T)
  have hAdj' : adjoint T = R ∘L A := by simpa [R] using hAdj
  have hR' : R = adjoint T ∘L B := by simpa [R] using hR
  have hprofile : rectApproxNumber (adjoint T) n = rectApproxNumber R n := by
    apply le_antisymm
    · rw [hAdj']
      calc
        rectApproxNumber (R ∘L A) n ≤ rectApproxNumber R n * ‖A‖ :=
          rectApproxNumber_comp_le_right R A n
        _ ≤ rectApproxNumber R n * 1 :=
          mul_le_mul_of_nonneg_left hA (rectApproxNumber_nonneg R n)
        _ = rectApproxNumber R n := by ring
    · rw [hR']
      calc
        rectApproxNumber (adjoint T ∘L B) n ≤
            rectApproxNumber (adjoint T) n * ‖B‖ :=
          rectApproxNumber_comp_le_right (adjoint T) B n
        _ ≤ rectApproxNumber (adjoint T) n * 1 :=
          mul_le_mul_of_nonneg_left hB
            (rectApproxNumber_nonneg (adjoint T) n)
        _ = rectApproxNumber (adjoint T) n := by ring
  have hTcptAdj : IsCompactOperator (adjoint T) :=
    GaloisForLFunctions.HTGeometry.isCompactOperator_adjoint_rectangular T hcpt
  have hRcpt : IsCompactOperator R := by
    rw [hR']
    exact hTcptAdj.comp_clm B
  have henergy : energyOp R = adjoint T ∘L T := by
    dsimp [R]
    rw [energyOp, rangeCovarianceRoot_adjoint,
      rangeCovarianceRoot_comp_self, rangeCovariance, adjoint_adjoint]
  have hrectR : rectApproxNumber R n = approxNumber R n := rfl
  calc
    rectApproxNumber T n ^ (2 : ℕ) = rectApproxNumber (adjoint T) n ^ (2 : ℕ) := by
      rw [rectApproxNumber_adjoint T n]
    _ = rectApproxNumber R n ^ (2 : ℕ) :=
      congrArg (fun x : ℝ => x ^ (2 : ℕ)) hprofile
    _ = approxNumber R n ^ (2 : ℕ) := by rw [hrectR]
    _ = approxNumber (energyOp R) n :=
      approxNumber_sq_eq_approxNumber_energyOp hRcpt n
    _ = approxNumber (adjoint T ∘L T) n := by rw [henergy]

end Rectangular

end RHTower
