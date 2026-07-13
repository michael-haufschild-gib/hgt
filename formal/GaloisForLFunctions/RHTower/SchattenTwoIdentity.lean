/-
The Schatten-2 identity: approximation numbers are singular values, and the Schatten 2-class is
exactly the Hilbert–Schmidt class.

The `n`-th approximation number of a compact operator equals its `n`-th singular value.  Upward:
the greedy truncation `x ↦ ∑_{m<n} ⟨eₘ, x⟩·T eₘ` along the greedy eigenvectors of `T†T` has rank
at most `n` and error exactly controlled by the constrained norm, `‖T − Tₙ‖ ≤ sₙ`.  Downward: any
operator of rank at most `n` kills a nonzero vector of the `(n+1)`-dimensional span of the first
`n+1` greedy vectors, where `‖T z‖² ≥ μₙ·‖z‖²` by the antitone eigenvalue expansion.

Combining with the master identity `∑ᵢ ‖T bᵢ‖² = ∑ₙ μₙ`, the Schatten 2-class coincides with the
Hilbert–Schmidt class, with `‖T‖²_HS = ∑ₙ aₙ(T)²`.
-/
import GaloisForLFunctions.HTGeometry.SingularValues
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.RHTower.SchattenApproximation

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- **The upward bound: `aₙ(T) ≤ sₙ(T)`.**  The greedy truncation has rank at most `n` and its
error is the constrained norm of `T` beyond the first `n` greedy vectors. -/
theorem approxNumber_le_singVal (hcpt : IsCompactOperator T) (n : ℕ) :
    approxNumber T n ≤ singVal T n := by
  classical
  have hsym := energyOp_symmetric T
  have hpos := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  set e : ℕ → H := svVec (energyOp T) with he
  set F : H →L[ℂ] H := ∑ m ∈ Finset.range n, (innerSL ℂ (e m)).smulRight (T (e m)) with hF
  have hrank : HasRankLE F n := by
    refine ⟨Submodule.span ℂ (((Finset.range n).image fun m => T (e m) : Finset H) : Set H),
      FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
    · refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
      simp
    · intro x
      rw [hF, sum_apply]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hm)))
  refine (approxNumber_le T n F hrank).trans ?_
  refine opNorm_le_bound _ (singVal_nonneg T n) fun x => ?_
  set P : H := ∑ m ∈ Finset.range n, (inner ℂ (e m) x) • e m with hP
  have hFx : F x = T P := by
    rw [hF, sum_apply, hP, map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smulRight_apply, innerSL_apply_apply, map_smul]
  have hunit_sq : ∀ m, (inner ℂ (e m) x) * ((‖e m‖ : ℂ)) ^ 2 = inner ℂ (e m) x := by
    intro m
    rcases eq_or_ne (svVal (energyOp T) m) 0 with h0 | hne0
    · rw [he, svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
      simp
    · rw [he, norm_svVec_of_ne_zero hScpt hsym hpos hne0]
      simp
  have hy_orth : ∀ k < n, inner ℂ (e k) (x - P) = 0 := by
    intro k hk
    rw [inner_sub_right, hP, inner_sum]
    have hsum : ∑ m ∈ Finset.range n, inner ℂ (e k) ((inner ℂ (e m) x) • e m)
        = inner ℂ (e k) x := by
      rw [Finset.sum_eq_single k]
      · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        exact hunit_sq k
      · intro m hm hmk
        rw [inner_smul_right, he, inner_svVec_svVec_of_ne (energyOp T) (Ne.symm hmk), mul_zero]
      · intro hk'
        exact absurd (Finset.mem_range.mpr hk) hk'
    rw [hsum, sub_self]
  have hy_le : ‖x - P‖ ≤ ‖x‖ := by
    have hyP : RCLike.re (inner ℂ (x - P) P) = 0 := by
      rw [hP, inner_sum]
      have hz : ∀ m ∈ Finset.range n, inner ℂ (x - P) ((inner ℂ (e m) x) • e m) = 0 := by
        intro m hm
        rw [inner_smul_right,
          show inner ℂ (x - P) (e m) = (starRingEnd ℂ) (inner ℂ (e m) (x - P)) from
            (inner_conj_symm _ _).symm,
          hy_orth m (Finset.mem_range.mp hm), map_zero, mul_zero]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      simp
    have hsq := norm_add_sq (𝕜 := ℂ) (x - P) P
    rw [hyP, sub_add_cancel] at hsq
    nlinarith [norm_nonneg (x - P), norm_nonneg x, sq_nonneg ‖P‖]
  calc ‖(T - F) x‖ = ‖T (x - P)‖ := by rw [sub_apply, hFx, ← map_sub]
    _ ≤ singVal T n * ‖x - P‖ := norm_apply_le_singVal_of_orth T n hy_orth
    _ ≤ singVal T n * ‖x‖ := mul_le_mul_of_nonneg_left hy_le (singVal_nonneg T n)

/-- **The downward bound: `sₙ(T) ≤ aₙ(T)`.**  Any rank-`≤ n` operator kills a nonzero vector of
the span of the first `n+1` greedy vectors, on which `‖T z‖² ≥ μₙ·‖z‖²`. -/
theorem singVal_le_approxNumber (hcpt : IsCompactOperator T) (n : ℕ) :
    singVal T n ≤ approxNumber T n := by
  classical
  have hsym := energyOp_symmetric T
  have hpos := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
  · rw [singVal, h0, Real.sqrt_zero]
    exact approxNumber_nonneg T n
  · have hlive : ∀ m, m ≤ n → svVal (energyOp T) m ≠ 0 := by
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
          norm_svVec_of_ne_zero hScpt hsym hpos (hlive i (Nat.lt_succ_iff.mp i.2))]
        norm_num
      · rw [if_neg hij]
        exact inner_svVec_svVec_of_ne (energyOp T) fun h => hij (Fin.val_injective h)
    refine le_csInf (approxNumber_set_nonempty T n) ?_
    rintro r ⟨F, hF, rfl⟩
    obtain ⟨W', hfd, hle, hmem⟩ := hF
    set V := Submodule.span ℂ (Set.range fun i : Fin (n + 1) => svVec (energyOp T) i) with hV
    haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have hdim : Module.finrank ℂ V = n + 1 := by
      rw [hV, finrank_span_eq_card horth.linearIndependent]
      simp
    set g : V →ₗ[ℂ] W' := LinearMap.codRestrict W' ((F : H →ₗ[ℂ] H).comp V.subtype)
      (fun v => hmem v) with hg
    have hker : g.ker ≠ ⊥ := by
      refine LinearMap.ker_ne_bot_of_finrank_lt ?_
      rw [hdim]
      exact Nat.lt_succ_of_le hle
    obtain ⟨z, hz_mem, hz_ne⟩ := (Submodule.ne_bot_iff _).mp hker
    have hFz : F (↑z : H) = 0 := by
      have h1 := LinearMap.mem_ker.mp hz_mem
      have h2 : ((g z : W') : H) = F (↑z : H) := by
        rw [hg, LinearMap.codRestrict_apply]
        rfl
      rw [h1] at h2
      simpa using h2.symm
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (show (↑z : H) ∈ Submodule.span ℂ (Set.range fun i : Fin (n + 1) => svVec (energyOp T) i)
        from z.2)
    have hSz : energyOp T (↑z : H)
        = ∑ i : Fin (n + 1), (c i * (svVal (energyOp T) i : ℂ)) • svVec (energyOp T) i := by
      rw [← hc, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, apply_svVec, smul_smul]
    have hre : RCLike.re (inner ℂ (↑z : H) (energyOp T ↑z))
        = ∑ i : Fin (n + 1), ‖c i‖ ^ 2 * svVal (energyOp T) i := by
      rw [hSz, ← hc, horth.inner_sum c (fun i => c i * (svVal (energyOp T) i : ℂ)) Finset.univ,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (starRingEnd ℂ) (c i) * (c i * (svVal (energyOp T) i : ℂ))
          = ((starRingEnd ℂ) (c i) * c i) * (svVal (energyOp T) i : ℂ) from by ring,
        RCLike.conj_mul, RCLike.mul_re]
      simp [← Complex.ofReal_pow]
    have hz_norm_sq : ‖(↑z : H)‖ ^ 2 = ∑ i : Fin (n + 1), ‖c i‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hc, horth.inner_sum c c Finset.univ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    have hlow : svVal (energyOp T) n * ‖(↑z : H)‖ ^ 2 ≤ ‖T (↑z : H)‖ ^ 2 := by
      rw [← re_inner_energyOp_self T, hre, hz_norm_sq, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hmono : svVal (energyOp T) n ≤ svVal (energyOp T) i :=
        svVal_antitone (energyOp T) (Nat.lt_succ_iff.mp i.2)
      nlinarith [sq_nonneg ‖c i‖, svVal_nonneg (energyOp T) n]
    have hz0 : (↑z : H) ≠ 0 := fun h => hz_ne (Submodule.coe_eq_zero.mp h)
    have hz_pos : (0 : ℝ) < ‖(↑z : H)‖ := norm_pos_iff.mpr hz0
    have hTz : singVal T n * ‖(↑z : H)‖ ≤ ‖T (↑z : H)‖ := by
      have h1 : (singVal T n * ‖(↑z : H)‖) ^ 2 ≤ ‖T (↑z : H)‖ ^ 2 := by
        rw [mul_pow, singVal_sq]
        exact hlow
      have h2 : 0 ≤ singVal T n * ‖(↑z : H)‖ :=
        mul_nonneg (singVal_nonneg T n) (norm_nonneg _)
      nlinarith [norm_nonneg (T (↑z : H))]
    have hband : singVal T n * ‖(↑z : H)‖ ≤ ‖T - F‖ * ‖(↑z : H)‖ :=
      calc singVal T n * ‖(↑z : H)‖ ≤ ‖T (↑z : H)‖ := hTz
        _ = ‖(T - F) (↑z : H)‖ := by rw [sub_apply, hFz, sub_zero]
        _ ≤ ‖T - F‖ * ‖(↑z : H)‖ := (T - F).le_opNorm _
    exact le_of_mul_le_mul_right hband hz_pos

/-- **Approximation numbers are singular values**: `aₙ(T) = sₙ(T) = √μₙ(T†T)` for compact `T`. -/
theorem approxNumber_eq_singVal (hcpt : IsCompactOperator T) (n : ℕ) :
    approxNumber T n = singVal T n :=
  le_antisymm (approxNumber_le_singVal hcpt n) (singVal_le_approxNumber hcpt n)

/-- **The Schatten 2-class is the Hilbert–Schmidt class.**  Both directions supply the
compactness needed to run the singular value decomposition: Schatten membership forces
compactness through vanishing approximation numbers, and Hilbert–Schmidt operators are norm
limits of finite-rank truncations. -/
theorem memSchattenClass_two_iff_isHilbertSchmidt (T : H →L[ℂ] H) :
    MemSchattenClass 2 T ↔ T.IsHilbertSchmidt := by
  constructor
  · intro hSch
    have hcpt : IsCompactOperator T := hSch.isCompactOperator two_pos
    rw [isHilbertSchmidt_iff_summable_svVal hcpt]
    refine hSch.congr fun n => ?_
    rw [approxNumber_eq_singVal hcpt n, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, singVal_sq]
  · intro hHS
    have hcpt : IsCompactOperator T := hHS.isCompactOperator
    have hsum : Summable (svVal (energyOp T)) :=
      (isHilbertSchmidt_iff_summable_svVal hcpt).mp hHS
    refine hsum.congr fun n => ?_
    rw [approxNumber_eq_singVal hcpt n, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, singVal_sq]

/-- **The Schatten-2 norm identity.**  `‖T‖²_HS = ∑ₙ aₙ(T)²`: the Hilbert–Schmidt norm is the
`ℓ²`-norm of the approximation numbers. -/
theorem hsNormSq_eq_tsum_approxNumber_sq (hHS : T.IsHilbertSchmidt) :
    ContinuousLinearMap.hsNormSq T = ∑' n, approxNumber T n ^ 2 := by
  have hcpt : IsCompactOperator T := hHS.isCompactOperator
  rw [hsNormSq_eq_tsum_svVal hcpt hHS]
  exact tsum_congr fun n => by rw [approxNumber_eq_singVal hcpt n, singVal_sq]

end RHTower
