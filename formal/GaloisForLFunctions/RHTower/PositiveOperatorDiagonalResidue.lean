import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison

/-!
# From the diagonal logarithmic mean to the singular-value logarithmic mean

For a positive compact operator the diagonal of any orthonormal basis is majorized by the singular
values (`sum_re_inner_le_sum_singVal`).  The reverse comparison costs only a Hilbert–Schmidt tail:
with `P_S` the projection onto finitely many basis vectors,

`∑_{n<N} s_n(T) ≤ ∑_{j∈S} ⟨b_j, T b_j⟩ + √N · √(2 ∑_{j∉S} ‖T b_j‖²)`,

because `P_S T P_S` is again positive compact with trace `∑_{j∈S} ⟨b_j, T b_j⟩`, and the remainder
`T − P_S T P_S` is Hilbert–Schmidt with norm at most twice the tail.

Taking `S = {j : j < N^{1+δ}}` and letting `δ → 0` afterwards turns a diagonal logarithmic mean
into the singular-value logarithmic mean whenever the tail decays like `M^{-1/2}` up to an
arbitrarily small power.  No modulation theory is used.
-/

namespace ContinuousLinearMap

open Finset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-! ## The finite basis truncation -/

/-- The orthogonal projection onto the span of the basis vectors indexed by `S`. -/
noncomputable def basisTruncation {ι : Type*} (b : HilbertBasis ι ℂ H) (S : Finset ι) :
    H →L[ℂ] H :=
  ∑ j ∈ S, (innerSL ℂ (b j)).smulRight (b j)

theorem basisTruncation_apply {ι : Type*} (b : HilbertBasis ι ℂ H) (S : Finset ι) (x : H) :
    basisTruncation b S x = ∑ j ∈ S, (inner ℂ (b j) x : ℂ) • b j := by
  simp [basisTruncation]

theorem inner_basis_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H) (i j : ι) :
    (inner ℂ (b i) (b j) : ℂ) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with h | h
  · subst h
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    norm_num
  · rw [if_neg h]
    exact b.orthonormal.2 h

theorem basisTruncation_apply_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (S : Finset ι) (j : ι) :
    basisTruncation b S (b j) = if j ∈ S then b j else 0 := by
  rw [basisTruncation_apply]
  rcases Finset.decidableMem j S with h | h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkj : k ≠ j := fun hkj => h (hkj ▸ hk)
    rw [inner_basis_basis, if_neg hkj, zero_smul]
  · rw [if_pos h]
    rw [Finset.sum_eq_single j]
    · rw [inner_basis_basis, if_pos rfl, one_smul]
    · intro k _ hkj
      rw [inner_basis_basis, if_neg hkj, zero_smul]
    · intro hj
      exact absurd h hj

theorem inner_basisTruncation_left {ι : Type*} (b : HilbertBasis ι ℂ H) (S : Finset ι) (x y : H) :
    (inner ℂ (basisTruncation b S x) y : ℂ) = inner ℂ x (basisTruncation b S y) := by
  rw [basisTruncation_apply, basisTruncation_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← inner_conj_symm (b j) x, Complex.conj_conj,
    mul_comm]

theorem adjoint_basisTruncation {ι : Type*} (b : HilbertBasis ι ℂ H) (S : Finset ι) :
    adjoint (basisTruncation b S) = basisTruncation b S := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (basisTruncation b S) (basisTruncation b S)).mpr
    fun x y => ?_).symm
  exact inner_basisTruncation_left b S x y

/-! ## Parseval in `ℝ≥0∞` -/

open scoped ENNReal

theorem hasSum_inner_sq_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun j : ι => ‖(inner ℂ x (b j) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have hcongr : ∀ j : ι, (inner ℂ x (b j) : ℂ) * inner ℂ (b j) x
      = ((‖(inner ℂ x (b j) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [← inner_conj_symm (b j) x, Complex.mul_conj']
    push_cast
    ring
  have h2 : HasSum (fun j : ι => ((‖(inner ℂ x (b j) : ℂ)‖ ^ 2 : ℝ) : ℂ)) (inner ℂ x x : ℂ) := by
    refine h.congr_fun fun j => ?_
    rw [← hcongr j]
  have h3 := h2.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous
  have hfun : (⇑(Complex.reCLM : ℂ →L[ℝ] ℝ) ∘
        fun j : ι => ((‖(inner ℂ x (b j) : ℂ)‖ ^ 2 : ℝ) : ℂ))
      = fun j : ι => ‖(inner ℂ x (b j) : ℂ)‖ ^ 2 := by
    funext j
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re]
  rw [hfun] at h3
  have hval : Complex.reCLM (inner ℂ x x : ℂ) = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.reCLM_apply]
    norm_cast
  rwa [hval] at h3

theorem tsum_ofReal_inner_sq_basis {ι : Type*} (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' j : ι, ENNReal.ofReal (‖(inner ℂ x (b j) : ℂ)‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hsum := hasSum_inner_sq_basis b x
  rw [← hsum.tsum_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum.summable).symm

/-! ## The truncated compression -/

variable {ι : Type*}

/-- The compression of `T` to the span of finitely many basis vectors. -/
noncomputable def basisCompression (b : HilbertBasis ι ℂ H) (S : Finset ι) (T : H →L[ℂ] H) :
    H →L[ℂ] H :=
  basisTruncation b S ∘L T ∘L basisTruncation b S

theorem basisCompression_isPositive {b : HilbertBasis ι ℂ H} {S : Finset ι} (hT : 0 ≤ T) :
    (basisCompression b S T).IsPositive := by
  have hpos : T.IsPositive := by
    rw [ContinuousLinearMap.le_def, sub_zero] at hT
    exact hT
  have h := hpos.conj_adjoint (basisTruncation b S)
  rwa [adjoint_basisTruncation] at h

theorem basisCompression_nonneg {b : HilbertBasis ι ℂ H} {S : Finset ι} (hT : 0 ≤ T) :
    0 ≤ basisCompression b S T := by
  rw [ContinuousLinearMap.le_def, sub_zero]
  exact basisCompression_isPositive hT

theorem basisCompression_compact {b : HilbertBasis ι ℂ H} {S : Finset ι}
    (hcpt : IsCompactOperator T) : IsCompactOperator (basisCompression b S T) := by
  rw [basisCompression]
  exact (hcpt.comp_clm _).clm_comp _

theorem re_inner_basisCompression_basis [DecidableEq ι] (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (T : H →L[ℂ] H) (j : ι) :
    RCLike.re (inner ℂ (b j) (basisCompression b S T (b j)) : ℂ)
      = if j ∈ S then RCLike.re (inner ℂ (b j) (T (b j)) : ℂ) else 0 := by
  rw [basisCompression]
  show RCLike.re (inner ℂ (b j) (basisTruncation b S (T (basisTruncation b S (b j)))) : ℂ) = _
  rw [basisTruncation_apply_basis]
  split_ifs with h
  · rw [← inner_basisTruncation_left, basisTruncation_apply_basis, if_pos h]
  · rw [map_zero, map_zero, inner_zero_right]
    simp

/-! ## The compression carries the truncated diagonal -/

set_option maxHeartbeats 1000000 in
theorem sum_singVal_basisCompression_le [DecidableEq ι] (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (hcpt : IsCompactOperator T) (hT : 0 ≤ T) (N : ℕ) :
    ∑ k ∈ Finset.range N, singVal (basisCompression b S T) k
      ≤ ∑ j ∈ S, RCLike.re (inner ℂ (b j) (T (b j)) : ℂ) := by
  classical
  set A : H →L[ℂ] H := basisCompression b S T with hA
  have hApos : 0 ≤ A := basisCompression_nonneg hT
  have hAcpt : IsCompactOperator A := basisCompression_compact hcpt
  have hTpos : T.IsPositive := by
    rw [ContinuousLinearMap.le_def, sub_zero] at hT
    exact hT
  have hd0 : ∀ j : ι, 0 ≤ RCLike.re (inner ℂ (b j) (T (b j)) : ℂ) := fun j =>
    hTpos.re_inner_nonneg_right (b j)
  have hdiag : ∀ j : ι, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (A (b j)) : ℂ))
      = if j ∈ S then ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)) else 0 := by
    intro j
    rw [hA, re_inner_basisCompression_basis]
    split_ifs with h
    · rfl
    · exact ENNReal.ofReal_zero
  have hfin : ∑' j : ι, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (A (b j)) : ℂ))
      = ∑ j ∈ S, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)) := by
    rw [tsum_congr hdiag]
    rw [tsum_eq_sum (s := S) (f := fun j : ι =>
      if j ∈ S then ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)) else 0)
      (fun j hj => if_neg hj)]
    exact Finset.sum_congr rfl fun j hj => if_pos hj
  have hsv := tsum_ofReal_re_inner_basis_eq_tsum_ofReal_singVal hAcpt hApos b
  have hpartial : ∑ k ∈ Finset.range N, ENNReal.ofReal (singVal A k)
      ≤ ∑' k : ℕ, ENNReal.ofReal (singVal A k) :=
    ENNReal.sum_le_tsum _
  have hchain : ENNReal.ofReal (∑ k ∈ Finset.range N, singVal A k)
      ≤ ENNReal.ofReal (∑ j ∈ S, RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => singVal_nonneg A k),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hd0 j)]
    refine le_trans hpartial ?_
    rw [← hsv, hfin]
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun j _ => hd0 j)).mp hchain

/-! ## The remainder is Hilbert–Schmidt small -/

set_option maxHeartbeats 1000000 in
theorem tsum_ofReal_norm_sq_remainder_le [DecidableEq ι] (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (hsa : IsSelfAdjoint T) :
    ∑' j : ι, ENNReal.ofReal (‖(T - basisCompression b S T) (b j)‖ ^ 2)
      ≤ 2 * ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2)) := by
  classical
  set P : H →L[ℂ] H := basisTruncation b S with hP
  set X : H →L[ℂ] H := T - basisCompression b S T with hX
  have hXval : ∀ j : ι, X (b j) = if j ∈ S then T (b j) - P (T (b j)) else T (b j) := by
    intro j
    have hAval : basisCompression b S T (b j) = if j ∈ S then P (T (b j)) else 0 := by
      rw [basisCompression]
      show P (T (P (b j))) = _
      rw [hP, basisTruncation_apply_basis]
      split_ifs with h
      · rfl
      · rw [map_zero, map_zero]
    show T (b j) - basisCompression b S T (b j) = _
    rw [hAval]
    split_ifs with h
    · rfl
    · rw [sub_zero]
  have hoff : ∀ j : ι, ENNReal.ofReal (‖T (b j) - P (T (b j))‖ ^ 2)
      = ∑' i : ι, (if i ∈ S then 0
        else ENNReal.ofReal (‖(inner ℂ (T (b j)) (b i) : ℂ)‖ ^ 2)) := by
    intro j
    rw [← tsum_ofReal_inner_sq_basis b (T (b j) - P (T (b j)))]
    refine tsum_congr fun i => ?_
    have hcoef : (inner ℂ (T (b j) - P (T (b j))) (b i) : ℂ)
        = if i ∈ S then 0 else inner ℂ (T (b j)) (b i) := by
      rw [inner_sub_left, hP, inner_basisTruncation_left, basisTruncation_apply_basis]
      split_ifs with h
      · rw [sub_self]
      · rw [inner_zero_right, sub_zero]
    rw [hcoef]
    split_ifs with h
    · rw [norm_zero]
      norm_num
    · rfl
  have hpars : ∀ i : ι, ∑' j : ι, ENNReal.ofReal (‖(inner ℂ (T (b j)) (b i) : ℂ)‖ ^ 2)
      = ENNReal.ofReal (‖T (b i)‖ ^ 2) := by
    intro i
    rw [← tsum_ofReal_inner_sq_basis b (T (b i))]
    refine tsum_congr fun j => ?_
    have hadj : ContinuousLinearMap.adjoint T = T := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact hsa.star_eq
    have hswap : (inner ℂ (T (b j)) (b i) : ℂ) = inner ℂ (b j) (T (b i)) := by
      conv_lhs => rw [← hadj]
      exact ContinuousLinearMap.adjoint_inner_left T (b i) (b j)
    rw [hswap, ← inner_conj_symm (T (b i)) (b j), RCLike.norm_conj]
  have hblock : ∑' j : ι, (if j ∈ S then ENNReal.ofReal (‖X (b j)‖ ^ 2) else 0)
      ≤ ∑' i : ι, (if i ∈ S then 0 else ENNReal.ofReal (‖T (b i)‖ ^ 2)) := by
    have hstep : ∀ j : ι, (if j ∈ S then ENNReal.ofReal (‖X (b j)‖ ^ 2) else 0)
        ≤ ∑' i : ι, (if i ∈ S then 0
          else ENNReal.ofReal (‖(inner ℂ (T (b j)) (b i) : ℂ)‖ ^ 2)) := by
      intro j
      split_ifs with h
      · rw [hXval j, if_pos h, hoff j]
      · exact _root_.zero_le
    refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
    rw [ENNReal.tsum_comm]
    refine le_of_eq (tsum_congr fun i => ?_)
    by_cases h : i ∈ S
    · simp only [if_pos h, tsum_zero]
    · simp only [if_neg h]
      exact hpars i
  have hsplit : ∀ j : ι, ENNReal.ofReal (‖X (b j)‖ ^ 2)
      = (if j ∈ S then ENNReal.ofReal (‖X (b j)‖ ^ 2) else 0)
        + (if j ∈ S then 0 else ENNReal.ofReal (‖X (b j)‖ ^ 2)) := by
    intro j
    split_ifs with h
    · rw [add_zero]
    · rw [zero_add]
  have hout : ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖X (b j)‖ ^ 2))
      = ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2)) := by
    refine tsum_congr fun j => ?_
    split_ifs with h
    · rfl
    · rw [hXval j, if_neg h]
  calc ∑' j : ι, ENNReal.ofReal (‖X (b j)‖ ^ 2)
      = ∑' j : ι, (if j ∈ S then ENNReal.ofReal (‖X (b j)‖ ^ 2) else 0)
        + ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖X (b j)‖ ^ 2)) := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr hsplit
    _ ≤ ∑' i : ι, (if i ∈ S then 0 else ENNReal.ofReal (‖T (b i)‖ ^ 2))
        + ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2)) := by
        rw [hout]
        exact add_le_add hblock le_rfl
    _ = 2 * ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2)) := by
        rw [two_mul]

/-! ## The upper comparison -/

theorem isSelfAdjoint_basisCompression [DecidableEq ι] (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (hsa : IsSelfAdjoint T) : IsSelfAdjoint (basisCompression b S T) := by
  have hadjT : ContinuousLinearMap.adjoint T = T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hsa.star_eq
  have hTsym : ∀ u v : H, (inner ℂ (T u) v : ℂ) = inner ℂ u (T v) := by
    intro u v
    conv_lhs => rw [← hadjT]
    exact ContinuousLinearMap.adjoint_inner_left T v u
  have h : ∀ x y : H, (inner ℂ (basisCompression b S T x) y : ℂ)
      = inner ℂ x (basisCompression b S T y) := by
    intro x y
    show (inner ℂ (basisTruncation b S (T (basisTruncation b S x))) y : ℂ)
      = inner ℂ x (basisTruncation b S (T (basisTruncation b S y)))
    rw [inner_basisTruncation_left, hTsym, ← inner_basisTruncation_left]
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  exact ((ContinuousLinearMap.eq_adjoint_iff (basisCompression b S T)
    (basisCompression b S T)).mpr h).symm

set_option maxHeartbeats 1000000 in
theorem sum_sq_norm_apply_svVec_le [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    {X : H →L[ℂ] H} (hXsa : IsSelfAdjoint X) (hcpt : IsCompactOperator T) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ENNReal.ofReal (‖X (svVec (energyOp T) n)‖ ^ 2)
      ≤ ∑' j : ι, ENNReal.ofReal (‖X (b j)‖ ^ 2) := by
  classical
  have hadjX : ContinuousLinearMap.adjoint X = X := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hXsa.star_eq
  set g : ℕ → H := fun n => svVec (energyOp T) n with hg
  have hgunit : ∀ n, g n = 0 ∨ ‖g n‖ = 1 := by
    intro n
    rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr (norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
        (energyOp_pos T) hne)
  have hgo : ∀ m n, m ≠ n → (inner ℂ (g m) (g n) : ℂ) = 0 := fun m n h =>
    inner_svVec_svVec_of_ne _ h
  have hpars : ∀ n : ℕ, ENNReal.ofReal (‖X (g n)‖ ^ 2)
      = ∑' j : ι, ENNReal.ofReal (‖(inner ℂ (g n) (X (b j)) : ℂ)‖ ^ 2) := by
    intro n
    rw [← tsum_ofReal_inner_sq_basis b (X (g n))]
    refine tsum_congr fun j => ?_
    have hswap : (inner ℂ (X (g n)) (b j) : ℂ) = inner ℂ (g n) (X (b j)) := by
      conv_lhs => rw [← hadjX]
      exact ContinuousLinearMap.adjoint_inner_left X (b j) (g n)
    rw [hswap]
  have hbessel : ∀ j : ι, ∑ n ∈ Finset.range N,
      ENNReal.ofReal (‖(inner ℂ (g n) (X (b j)) : ℂ)‖ ^ 2)
        ≤ ENNReal.ofReal (‖X (b j)‖ ^ 2) := by
    intro j
    have hreal := RHTower.sum_inner_sq_le_of_orthonormal_with_zeros g hgunit hgo (X (b j))
      (Finset.range N)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ∑ n ∈ Finset.range N, ENNReal.ofReal (‖X (g n)‖ ^ 2)
      = ∑ n ∈ Finset.range N, ∑' j : ι,
          ENNReal.ofReal (‖(inner ℂ (g n) (X (b j)) : ℂ)‖ ^ 2) :=
        Finset.sum_congr rfl fun n _ => hpars n
    _ = ∑' j : ι, ∑ n ∈ Finset.range N,
          ENNReal.ofReal (‖(inner ℂ (g n) (X (b j)) : ℂ)‖ ^ 2) := by
        rw [Summable.tsum_finsetSum (fun n _ => ENNReal.summable)]
    _ ≤ ∑' j : ι, ENNReal.ofReal (‖X (b j)‖ ^ 2) := ENNReal.tsum_le_tsum hbessel

/-! ## The upper comparison: singular values from a finite diagonal plus a tail -/

set_option maxHeartbeats 1000000 in
/-- **Upper comparison.**  For a positive compact operator, the sum of the first `N` singular
values is bounded by the diagonal over any finite set `S` of basis indices plus `√(2N)` times
the Hilbert–Schmidt size `E` of the off-`S` columns. -/
theorem sum_singVal_le_diagonal_add_tail [DecidableEq ι] (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (hcpt : IsCompactOperator T) (hT : 0 ≤ T) (N : ℕ) (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2))
      ≤ ENNReal.ofReal (E ^ 2)) :
    ∑ n ∈ Finset.range N, singVal T n
      ≤ (∑ j ∈ S, RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)) + Real.sqrt (2 * N) * E := by
  classical
  have hTpos : T.IsPositive := by
    rw [ContinuousLinearMap.le_def, sub_zero] at hT
    exact hT
  have hsa : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hTpos.1
  set A : H →L[ℂ] H := basisCompression b S T with hA
  set X : H →L[ℂ] H := T - A with hX
  have hXsa : IsSelfAdjoint X := by
    rw [hX, hA]
    exact hsa.sub (isSelfAdjoint_basisCompression b S hsa)
  set g : ℕ → H := fun n => svVec (energyOp T) n with hg
  have hgunit : ∀ n, g n = 0 ∨ ‖g n‖ = 1 := by
    intro n
    rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr (norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
        (energyOp_pos T) hne)
  have hgnorm : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    rcases hgunit n with h | h
    · rw [h, norm_zero]; norm_num
    · rw [h]
  have hgo : ∀ m n : ℕ, m ≠ n → (inner ℂ (g m) (g n) : ℂ) = 0 := fun m n h =>
    inner_svVec_svVec_of_ne _ h
  have hsplit : ∀ n, singVal T n
      = RCLike.re (inner ℂ (g n) (A (g n)) : ℂ)
        + RCLike.re (inner ℂ (g n) (X (g n)) : ℂ) := by
    intro n
    have h := re_inner_svVec_apply_of_nonneg hcpt hT n
    have hTAX : T (g n) = A (g n) + X (g n) := by
      rw [hX]
      simp
    rw [← h, hTAX, inner_add_right, map_add]
  have hApart : ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (g n) (A (g n)) : ℂ)
      ≤ ∑ j ∈ S, RCLike.re (inner ℂ (b j) (T (b j)) : ℂ) := by
    have hAcpt : IsCompactOperator A := by rw [hA]; exact basisCompression_compact hcpt
    have hApos : (0 : H →L[ℂ] H) ≤ A := by rw [hA]; exact basisCompression_nonneg hT
    refine le_trans (sum_re_inner_le_sum_singVal hAcpt hApos g hgunit hgo (Finset.range N)
      (le_of_eq (Finset.card_range N))) ?_
    rw [hA]
    exact sum_singVal_basisCompression_le b S hcpt hT N
  have hXbound : ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (g n) (X (g n)) : ℂ)
      ≤ Real.sqrt (2 * N) * E := by
    have hterm : ∀ n, RCLike.re (inner ℂ (g n) (X (g n)) : ℂ) ≤ ‖X (g n)‖ := by
      intro n
      calc RCLike.re (inner ℂ (g n) (X (g n)) : ℂ)
          ≤ ‖(inner ℂ (g n) (X (g n)) : ℂ)‖ := RCLike.re_le_norm _
        _ ≤ ‖g n‖ * ‖X (g n)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * ‖X (g n)‖ := mul_le_mul_of_nonneg_right (hgnorm n) (norm_nonneg _)
        _ = ‖X (g n)‖ := one_mul _
    have hsq : ∑ n ∈ Finset.range N, ‖X (g n)‖ ^ 2 ≤ 2 * E ^ 2 := by
      have h1 := sum_sq_norm_apply_svVec_le b hXsa hcpt N
      have h2 := tsum_ofReal_norm_sq_remainder_le b S hsa
      rw [← hA, ← hX] at h2
      have h3 : ∑ n ∈ Finset.range N, ENNReal.ofReal (‖X (g n)‖ ^ 2)
          ≤ ENNReal.ofReal (2 * E ^ 2) := by
        refine le_trans h1 (le_trans h2 ?_)
        calc (2 : ℝ≥0∞) * ∑' j : ι, (if j ∈ S then 0 else ENNReal.ofReal (‖T (b j)‖ ^ 2))
            ≤ 2 * ENNReal.ofReal (E ^ 2) := mul_le_mul_left' hE 2  -- 2 * · monotone
          _ = ENNReal.ofReal (2 * E ^ 2) := by
              rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
              norm_num
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
    have hcs : (∑ n ∈ Finset.range N, ‖X (g n)‖) ^ 2 ≤ (N : ℝ) * (2 * E ^ 2) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun _ => (1 : ℝ))
        (fun n => ‖X (g n)‖)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hsq (by positivity))
    have hnn : 0 ≤ ∑ n ∈ Finset.range N, ‖X (g n)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hrw : Real.sqrt ((N : ℝ) * (2 * E ^ 2)) = Real.sqrt (2 * N) * E := by
      rw [show (N : ℝ) * (2 * E ^ 2) = (2 * (N : ℝ)) * E ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hE0]
    refine le_trans (Finset.sum_le_sum fun n _ => hterm n) ?_
    rw [← hrw]
    calc ∑ n ∈ Finset.range N, ‖X (g n)‖
        = Real.sqrt ((∑ n ∈ Finset.range N, ‖X (g n)‖) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((N : ℝ) * (2 * E ^ 2)) := Real.sqrt_le_sqrt hcs
  calc ∑ n ∈ Finset.range N, singVal T n
      = ∑ n ∈ Finset.range N, (RCLike.re (inner ℂ (g n) (A (g n)) : ℂ)
          + RCLike.re (inner ℂ (g n) (X (g n)) : ℂ)) :=
        Finset.sum_congr rfl fun n _ => hsplit n
    _ = (∑ n ∈ Finset.range N, RCLike.re (inner ℂ (g n) (A (g n)) : ℂ))
        + ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (g n) (X (g n)) : ℂ) :=
        Finset.sum_add_distrib
    _ ≤ _ := add_le_add hApart hXbound

end ContinuousLinearMap
