/-
# The two-sided singular value decomposition

The greedy eigenbasis `eₙ` of `T†T` diagonalizes the absolute value — `|T| eₙ = sₙ eₙ`, by the
factorization `(|T| + sₙ)(|T| − sₙ) eₙ = (T†T − sₙ²) eₙ = 0` and strict injectivity of `|T| + sₙ`
for `sₙ > 0` — and the normalized images `fₙ = sₙ⁻¹·T eₙ` form a second orthonormal family, the
right singular vectors.  Expanding along a Hilbert-basis extension of the greedy family and using
that `T` kills its orthogonal complement gives the two-sided singular value decomposition
`T x = ∑ₙ sₙ·⟨eₙ, x⟩·fₙ` as a convergent sum for every `x`.

Proved here:
* `re_inner_absOp_nonneg` — `|T|` is positive in the quadratic-form sense.
* `absOp_apply_svVec` — `|T| eₙ = sₙ eₙ`: the greedy vectors are eigenvectors of `|T|`.
* `apply_svVec_eq_zero_of_svVal_eq_zero`, `inner_apply_svVec_of_ne` — `T` kills dead greedy
  vectors, and the images `T eₙ` are pairwise orthogonal.
* `svdVec` — the right singular vectors `fₙ`, zero or unit, pairwise orthogonal, with
  `T eₙ = sₙ • fₙ` and `⟨fₙ, T eₙ⟩ = sₙ`.
* `hasSum_inner_svVec_smul_apply`, `hasSum_svd` — **the two-sided SVD**:
  `HasSum (fun n => sₙ·⟨eₙ, x⟩ • fₙ) (T x)`.
-/
import GaloisForLFunctions.HTGeometry.OperatorAbsoluteValue

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The absolute value is positive as a quadratic form: `0 ≤ Re⟨x, |T| x⟩`. -/
theorem re_inner_absOp_nonneg (T : H →L[ℂ] H) (x : H) :
    0 ≤ RCLike.re (inner ℂ x (absOp T x)) := by
  have h1 : ((0 : H →L[ℂ] H) ≤ absOp T) := absOp_nonneg T
  rw [le_def, sub_zero] at h1
  exact h1.re_inner_nonneg_right x

/-- **The greedy vectors are eigenvectors of the absolute value**: `|T| eₙ = sₙ eₙ`.  For live
stages, `(|T| + sₙ)(|T| − sₙ) eₙ = (T†T − sₙ²) eₙ = 0` and `|T| + sₙ` is injective because `|T|`
is positive and `sₙ > 0`. -/
theorem absOp_apply_svVec (T : H →L[ℂ] H) (n : ℕ) :
    absOp T (svVec (energyOp T) n) = ((singVal T n : ℝ) : ℂ) • svVec (energyOp T) n := by
  rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
  · rw [svVec_eq_zero_of_svVal_eq_zero _ h0, map_zero, smul_zero]
  · have hs_pos : 0 < singVal T n := by
      rw [singVal]
      exact Real.sqrt_pos.mpr (lt_of_le_of_ne (svVal_nonneg _ n) (Ne.symm hne))
    set s : ℝ := singVal T n with hs
    set e : H := svVec (energyOp T) n with he
    set z : H := absOp T e - (s : ℂ) • e with hz
    have hz_eq : absOp T z + (s : ℂ) • z = 0 := by
      rw [hz, map_sub, map_smul, smul_sub, smul_smul]
      have h2 : absOp T (absOp T e) = energyOp T e := by
        rw [← comp_apply, absOp_comp_self]
      rw [h2, he, apply_svVec]
      have hμ : ((svVal (energyOp T) n : ℝ) : ℂ) = (s : ℂ) * (s : ℂ) := by
        rw [hs, ← singVal_sq T n]
        push_cast
        ring
      rw [hμ]
      abel
    have hz0 : z = 0 := by
      by_contra hzne
      have hpos1 : 0 ≤ RCLike.re (inner ℂ z (absOp T z)) := re_inner_absOp_nonneg T z
      have hpos2 : 0 < RCLike.re (inner ℂ z ((s : ℂ) • z)) := by
        rw [inner_smul_right, RCLike.mul_re]
        have him : RCLike.im ((s : ℝ) : ℂ) = 0 := by simp
        have hre : RCLike.re ((s : ℝ) : ℂ) = s := by simp
        rw [him, hre, inner_self_eq_norm_sq, inner_self_im, mul_zero, sub_zero]
        exact mul_pos hs_pos (pow_pos (norm_pos_iff.mpr hzne) 2)
      have hsum : RCLike.re (inner ℂ z (absOp T z + (s : ℂ) • z)) = 0 := by
        rw [hz_eq, inner_zero_right]
        simp
      rw [inner_add_right, map_add] at hsum
      linarith
    rw [← sub_eq_zero]
    exact hz0

/-- `T` kills the dead greedy vectors. -/
theorem apply_svVec_eq_zero_of_svVal_eq_zero (T : H →L[ℂ] H) {n : ℕ}
    (h : svVal (energyOp T) n = 0) : T (svVec (energyOp T) n) = 0 := by
  rw [svVec_eq_zero_of_svVal_eq_zero _ h, map_zero]

/-- The images of the greedy vectors under `T` are pairwise orthogonal:
`⟨T eₘ, T eₙ⟩ = ⟨eₘ, T†T eₙ⟩ = μₙ·⟨eₘ, eₙ⟩ = 0`. -/
theorem inner_apply_svVec_of_ne (T : H →L[ℂ] H) {m n : ℕ} (h : m ≠ n) :
    inner ℂ (T (svVec (energyOp T) m)) (T (svVec (energyOp T) n)) = 0 := by
  calc inner ℂ (T (svVec (energyOp T) m)) (T (svVec (energyOp T) n))
      = inner ℂ (svVec (energyOp T) m) (energyOp T (svVec (energyOp T) n)) := by
        rw [energyOp, comp_apply, adjoint_inner_right]
    _ = 0 := by
        rw [apply_svVec, inner_smul_right, inner_svVec_svVec_of_ne _ h, mul_zero]

/-- The **right singular vectors** `fₙ := sₙ⁻¹ • T eₙ`, zero at dead stages. -/
noncomputable def svdVec (T : H →L[ℂ] H) (n : ℕ) : H :=
  if singVal T n = 0 then 0
  else (((singVal T n)⁻¹ : ℝ) : ℂ) • T (svVec (energyOp T) n)

theorem svdVec_eq_zero_of_singVal_eq_zero (T : H →L[ℂ] H) {n : ℕ} (h : singVal T n = 0) :
    svdVec T n = 0 := by rw [svdVec, if_pos h]

/-- `T eₙ = sₙ • fₙ`: the defining relation of the right singular vectors. -/
theorem apply_svVec_eq_smul_svdVec (T : H →L[ℂ] H) (n : ℕ) :
    T (svVec (energyOp T) n) = ((singVal T n : ℝ) : ℂ) • svdVec T n := by
  rcases eq_or_ne (singVal T n) 0 with h0 | hne
  · rw [svdVec, if_pos h0, smul_zero]
    refine apply_svVec_eq_zero_of_svVal_eq_zero T ?_
    rw [← singVal_sq, h0]
    ring
  · rw [svdVec, if_neg hne, smul_smul]
    have hs : ((singVal T n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    have h1 : ((singVal T n : ℝ) : ℂ) * (((singVal T n)⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast
      exact mul_inv_cancel₀ hs
    rw [h1, one_smul]

/-- The squared norm of a live right singular vector is one, given the live unit greedy vector. -/
theorem norm_svdVec_sq {T : H →L[ℂ] H} (hcpt : IsCompactOperator T) {n : ℕ}
    (hne : singVal T n ≠ 0) : ‖svdVec T n‖ = 1 := by
  have hμne : svVal (energyOp T) n ≠ 0 := by
    intro h
    exact hne (by rw [singVal, h, Real.sqrt_zero])
  have hunit : ‖svVec (energyOp T) n‖ = 1 :=
    norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T) (energyOp_pos T) hμne
  have hTnorm : ‖T (svVec (energyOp T) n)‖ ^ 2 = singVal T n ^ 2 := by
    rw [norm_apply_svVec_sq, hunit, singVal_sq]
    ring
  have hs_pos : 0 < singVal T n :=
    lt_of_le_of_ne (singVal_nonneg T n) (Ne.symm hne)
  have hTn : ‖T (svVec (energyOp T) n)‖ = singVal T n := by
    nlinarith [norm_nonneg (T (svVec (energyOp T) n))]
  rw [svdVec, if_neg hne, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), hTn]
  field_simp

/-- The right singular vectors are pairwise orthogonal. -/
theorem inner_svdVec_svdVec_of_ne (T : H →L[ℂ] H) {m n : ℕ} (h : m ≠ n) :
    inner ℂ (svdVec T m) (svdVec T n) = 0 := by
  rw [svdVec, svdVec]
  split_ifs with h1 h2 h2
  · simp
  · simp
  · simp
  · rw [inner_smul_left, inner_smul_right, inner_apply_svVec_of_ne T h, mul_zero, mul_zero]

/-- The pairing that reads off the singular value: `⟨fₙ, T eₙ⟩ = sₙ`. -/
theorem inner_svdVec_apply {T : H →L[ℂ] H} (hcpt : IsCompactOperator T) (n : ℕ) :
    inner ℂ (svdVec T n) (T (svVec (energyOp T) n)) = ((singVal T n : ℝ) : ℂ) := by
  rcases eq_or_ne (singVal T n) 0 with h0 | hne
  · rw [svdVec, if_pos h0, inner_zero_left, h0]
    norm_num
  · rw [apply_svVec_eq_smul_svdVec, inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_svdVec_sq hcpt hne]
    norm_num

section Expansion

variable {T : H →L[ℂ] H}

/-- **The SVD expansion in image form.**  `T x = ∑ₙ ⟨eₙ, x⟩ • T eₙ`: expand `x` along a Hilbert
basis extending the live greedy family, apply `T`, and use that `T` kills the complement. -/
theorem hasSum_inner_svVec_smul_apply (hcpt : IsCompactOperator T) (x : H) :
    HasSum (fun n => inner ℂ (svVec (energyOp T) n) x • T (svVec (energyOp T) n)) (T x) := by
  classical
  have hsym := energyOp_symmetric T
  have hpos := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  have hinj : ∀ {m n : ℕ}, svVal (energyOp T) m ≠ 0 → svVal (energyOp T) n ≠ 0 →
      svVec (energyOp T) m = svVec (energyOp T) n → m = n := by
    intro m n hm hn hmn
    by_contra hne
    have h0 := inner_svVec_svVec_of_ne (energyOp T) hne
    rw [hmn, inner_self_eq_norm_sq_to_K,
      norm_svVec_of_ne_zero hScpt hsym hpos hn] at h0
    norm_num at h0
  have hA_orth : Orthonormal ℂ
      (Subtype.val : (svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}) → H) := by
    rw [orthonormal_subtype_iff_ite]
    rintro u ⟨m, hm, rfl⟩ v ⟨n, hn, rfl⟩
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero hScpt hsym hpos hm]
      norm_num
    · rw [if_neg fun h => hmn (hinj hm hn h), inner_svVec_svVec_of_ne (energyOp T) hmn]
  obtain ⟨w, b, hAw, hb⟩ := hA_orth.exists_hilbertBasis_extension
  have horthw : ∀ u ∈ w, ∀ v ∈ w, u ≠ v → inner ℂ u v = 0 := by
    have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
    rw [orthonormal_subtype_iff_ite] at hw_orth
    intro u hu v hv huv
    have h2 := hw_orth u hu v hv
    rwa [if_neg huv] at h2
  -- the basis expansion of T x
  have hbase : HasSum (fun v : w => inner ℂ (v : H) x • T (v : H)) (T x) := by
    have h1 := (b.hasSum_repr x).mapL T
    simp only [map_smul, HilbertBasis.repr_apply_apply] at h1
    simpa only [hb] using h1
  -- kill the complement
  have hker : ∀ v : w, (v : H) ∉ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0} →
      T (v : H) = 0 := by
    intro v hv
    have horth_all : ∀ n, inner ℂ (svVec (energyOp T) n) (v : H) = 0 := by
      intro n
      rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne0
      · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
        exact inner_zero_left _
      · have hmem : svVec (energyOp T) n ∈ w := hAw ⟨n, hne0, rfl⟩
        refine horthw _ hmem _ v.2 fun h => hv ?_
        rw [← h]
        exact ⟨n, hne0, rfl⟩
    have hSv : energyOp T (v : H) = 0 :=
      apply_eq_zero_of_forall_inner_svVec hScpt hsym hpos horth_all
    have hz : (‖T (v : H)‖ ^ 2 : ℝ) = 0 := by
      rw [← re_inner_energyOp_self T, hSv, inner_zero_right]
      simp
    simpa [pow_eq_zero_iff] using hz
  -- reindex onto the live indices
  set g : ℕ → H := fun n => inner ℂ (svVec (energyOp T) n) x • T (svVec (energyOp T) n) with hg
  have hg_dead : ∀ n, svVal (energyOp T) n = 0 → g n = 0 := by
    intro n h0
    rw [hg]
    simp only
    rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
    simp
  set F : w → H := fun v => inner ℂ (v : H) x • T (v : H) with hF
  set i : {n : ℕ // svVal (energyOp T) n ≠ 0} → w :=
    fun p => ⟨svVec (energyOp T) p.1, hAw ⟨p.1, p.2, rfl⟩⟩ with hi
  have hi_inj : Function.Injective i := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    exact Subtype.ext (hinj hm hn (congrArg Subtype.val h))
  have hF_supp : ∀ v ∉ Set.range i, F v = 0 := by
    intro v hv
    rw [hF]
    simp only
    have : (v : H) ∉ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0} := by
      rintro ⟨n, hn, hvn⟩
      exact hv ⟨⟨n, hn⟩, Subtype.ext hvn⟩
    rw [hker v this, smul_zero]
  have hFi : HasSum (F ∘ i) (T x) := (hi_inj.hasSum_iff hF_supp).mpr hbase
  have hFi' : HasSum (g ∘ (Subtype.val : {n : ℕ // svVal (energyOp T) n ≠ 0} → ℕ)) (T x) := hFi
  have hsupp : Function.support g ⊆ {n : ℕ | svVal (energyOp T) n ≠ 0} := by
    intro n hn
    by_contra h0
    simp only [Set.mem_setOf_eq, not_not] at h0
    exact hn (hg_dead n h0)
  exact (hasSum_subtype_iff_of_support_subset hsupp).mp hFi'

/-- **The two-sided singular value decomposition.**  `T x = ∑ₙ sₙ·⟨eₙ, x⟩ • fₙ` as a convergent
sum, with `eₙ` the greedy eigenbasis of `T†T` and `fₙ` the right singular vectors. -/
theorem hasSum_svd (hcpt : IsCompactOperator T) (x : H) :
    HasSum
      (fun n => (((singVal T n : ℝ) : ℂ) * inner ℂ (svVec (energyOp T) n) x) • svdVec T n)
      (T x) := by
  have hfun : (fun n => inner ℂ (svVec (energyOp T) n) x • T (svVec (energyOp T) n))
      = fun n => (((singVal T n : ℝ) : ℂ) * inner ℂ (svVec (energyOp T) n) x) • svdVec T n := by
    funext n
    rw [apply_svVec_eq_smul_svdVec, smul_smul, mul_comm]
  rw [← hfun]
  exact hasSum_inner_svVec_smul_apply hcpt x

end Expansion

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- The live greedy vectors extend to a Hilbert basis. -/
theorem exists_svVec_extension (hcpt : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis ↥w ℂ H),
      (svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}) ⊆ w ∧ ⇑b = Subtype.val := by
  classical
  have hsym := energyOp_symmetric T
  have hpos := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  have hinj : ∀ {m n : ℕ}, svVal (energyOp T) m ≠ 0 → svVal (energyOp T) n ≠ 0 →
      svVec (energyOp T) m = svVec (energyOp T) n → m = n := by
    intro m n hm hn hmn
    by_contra hne
    have h0 := inner_svVec_svVec_of_ne (energyOp T) hne
    rw [hmn, inner_self_eq_norm_sq_to_K,
      norm_svVec_of_ne_zero hScpt hsym hpos hn] at h0
    norm_num at h0
  have hA_orth : Orthonormal ℂ
      (Subtype.val : (svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}) → H) := by
    rw [orthonormal_subtype_iff_ite]
    rintro u ⟨m, hm, rfl⟩ v ⟨n, hn, rfl⟩
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero hScpt hsym hpos hm]
      norm_num
    · rw [if_neg fun h => hmn (hinj hm hn h), inner_svVec_svVec_of_ne (energyOp T) hmn]
  obtain ⟨w, b, hAw, hb⟩ := hA_orth.exists_hilbertBasis_extension
  exact ⟨w, b, hAw, hb⟩

/-- **Completeness of the greedy family for `T` itself**: a vector orthogonal to every greedy
vector of `T†T` is annihilated by `T`. -/
theorem apply_eq_zero_of_forall_inner_svVec_energyOp (hcpt : IsCompactOperator T) {x : H}
    (hx : ∀ n, inner ℂ (svVec (energyOp T) n) x = 0) : T x = 0 := by
  have hSx : energyOp T x = 0 :=
    apply_eq_zero_of_forall_inner_svVec (energyOp_compact hcpt) (energyOp_symmetric T)
      (energyOp_pos T) hx
  have hz : (‖T x‖ ^ 2 : ℝ) = 0 := by
    rw [← re_inner_energyOp_self T, hSx, inner_zero_right]
    simp
  simpa [pow_eq_zero_iff] using hz

/-- A right singular vector at a live index cannot coincide with one at any different index. -/
theorem svdVec_live_injective (hcpt : IsCompactOperator T) {m n : ℕ}
    (hn : singVal T n ≠ 0) (h : svdVec T m = svdVec T n) : m = n := by
  by_contra hne
  have h0 := inner_svdVec_svdVec_of_ne T hne
  rw [h, inner_self_eq_norm_sq_to_K, norm_svdVec_sq hcpt hn] at h0
  norm_num at h0

/-- A greedy vector at a live index cannot coincide with one at any different index. -/
theorem svVec_live_injective (hcpt : IsCompactOperator T) {m n : ℕ}
    (hn : svVal (energyOp T) n ≠ 0)
    (h : svVec (energyOp T) m = svVec (energyOp T) n) : m = n := by
  by_contra hne
  have h0 := inner_svVec_svVec_of_ne (energyOp T) hne
  rw [h, inner_self_eq_norm_sq_to_K,
    norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T) (energyOp_pos T) hn]
    at h0
  norm_num at h0

/-- Finite Bessel inequality along the greedy family. -/
theorem sum_inner_svVec_sq_le (hcpt : IsCompactOperator T) (x : H) (s : Finset ℕ) :
    ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  have hsplit : ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2
      = ∑ n ∈ s.filter (fun n => svVal (energyOp T) n ≠ 0),
          ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => svVal (energyOp T) n ≠ 0)]
    have hz : ∑ n ∈ s.filter (fun n => ¬svVal (energyOp T) n ≠ 0),
        ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have h0 := (Finset.mem_filter.mp hn).2
      rw [not_not] at h0
      rw [svVec_eq_zero_of_svVal_eq_zero _ h0, inner_zero_left]
      simp
    rw [hz, add_zero]
  rw [hsplit]
  set t := s.filter (fun n => svVal (energyOp T) n ≠ 0) with ht
  have horthsub : Orthonormal ℂ
      (fun p : {n : ℕ // n ∈ t} => svVec (energyOp T) p.1) := by
    rw [orthonormal_iff_ite]
    intro p q
    have hp : svVal (energyOp T) p.1 ≠ 0 := (Finset.mem_filter.mp p.2).2
    have hq : svVal (energyOp T) q.1 ≠ 0 := (Finset.mem_filter.mp q.2).2
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
          (energyOp_pos T) hp]
      norm_num
    · rw [if_neg hpq]
      refine inner_svVec_svVec_of_ne (energyOp T) fun h => hpq ?_
      exact Subtype.ext h
  have hbessel := horthsub.sum_inner_products_le (s := t.attach) x
  calc ∑ n ∈ t, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2
      = ∑ p ∈ t.attach, ‖inner ℂ (svVec (energyOp T) p.1) x‖ ^ 2 :=
        (Finset.sum_attach t (fun n => ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2)).symm
    _ ≤ ‖x‖ ^ 2 := hbessel

/-- Summability of the squared greedy Fourier coefficients. -/
theorem summable_inner_svVec_sq (hcpt : IsCompactOperator T) (x : H) :
    Summable (fun n => ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2) :=
  summable_of_sum_le (fun n => by positivity) (sum_inner_svVec_sq_le hcpt x)

/-- Bessel inequality along the greedy family. -/
theorem tsum_inner_svVec_sq_le (hcpt : IsCompactOperator T) (x : H) :
    ∑' n, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun n => by positivity) (sum_inner_svVec_sq_le hcpt x)

end ContinuousLinearMap
