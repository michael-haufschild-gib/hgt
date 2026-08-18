import GaloisForLFunctions.HTGeometry.SVDExpansion
import GaloisForLFunctions.RHTower.TraceNorm

/-!
# The diagonal of a positive compact operator is majorized by its singular values

For a positive compact operator `T` the greedy vectors of `T†T` are eigenvectors of `T` itself,
so the quadratic form has the exact expansion

`⟨x, T x⟩ = ∑ₖ sₖ |⟨eₖ, x⟩|²`.

Feeding an arbitrary orthonormal family into that expansion and applying Bessel on both sides
turns the comparison of a partial diagonal sum with a partial singular-value sum into the
elementary "bathtub" inequality for a decreasing weight against a `[0,1]`-valued profile of total
mass at most `N`.

This is the first half of the eigenvalue comparison the Gauss critical-residue card needs in its
§6: it gives `∑_{j<N} ⟨b_j, T b_j⟩ ≤ ∑_{n<N} s_n(T)` for *every* orthonormal family `b`, with no
modulation hypothesis at all.
-/

namespace ContinuousLinearMap

open Finset

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-! ## Positive operators: the greedy vectors are eigenvectors -/

theorem absOp_of_nonneg (hT : 0 ≤ T) : absOp T = T := by
  rw [absOp, hT.isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_self T hT

theorem apply_svVec_of_nonneg (hT : 0 ≤ T) (n : ℕ) :
    T (svVec (energyOp T) n) = ((singVal T n : ℝ) : ℂ) • svVec (energyOp T) n := by
  have h := absOp_apply_svVec T n
  rwa [absOp_of_nonneg hT] at h

/-- The diagonal of a positive operator at its own greedy vector is the singular value. -/
theorem re_inner_svVec_apply_of_nonneg (hcpt : IsCompactOperator T) (hT : 0 ≤ T) (n : ℕ) :
    RCLike.re (inner ℂ (svVec (energyOp T) n) (T (svVec (energyOp T) n)) : ℂ) = singVal T n := by
  rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
  · have hzero : svVec (energyOp T) n = 0 := svVec_eq_zero_of_svVal_eq_zero _ h0
    have hs : singVal T n = 0 := by
      rw [singVal, h0, Real.sqrt_zero]
    rw [hzero, hs]
    simp
  · have hnorm : ‖svVec (energyOp T) n‖ = 1 :=
      norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T) (energyOp_pos T) hne
    rw [apply_svVec_of_nonneg hT, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    simp

/-! ## The quadratic form expansion -/

theorem hasSum_re_inner_apply_of_nonneg (hcpt : IsCompactOperator T) (hT : 0 ≤ T) (x : H) :
    HasSum (fun n => singVal T n * ‖(inner ℂ (svVec (energyOp T) n) x : ℂ)‖ ^ 2)
      (RCLike.re (inner ℂ x (T x) : ℂ)) := by
  have hsvd := hasSum_svd hcpt x
  have hmap := hsvd.mapL (innerSL ℂ x)
  have hval : ∀ n, (innerSL ℂ x) ((((singVal T n : ℝ) : ℂ) *
        inner ℂ (svVec (energyOp T) n) x) • svdVec T n)
      = ((singVal T n : ℝ) : ℂ) * ‖(inner ℂ (svVec (energyOp T) n) x : ℂ)‖ ^ 2 := by
    intro n
    have hsv : svdVec T n = svVec (energyOp T) n := by
      rcases eq_or_ne (singVal T n) 0 with h0 | hne
      · rw [svdVec_eq_zero_of_singVal_eq_zero T h0]
        have h0' : svVal (energyOp T) n = 0 := by
          have := singVal_sq T n
          rw [h0] at this
          simpa using this.symm
        rw [svVec_eq_zero_of_svVal_eq_zero _ h0']
      · rw [svdVec, if_neg hne, apply_svVec_of_nonneg hT, smul_smul,
          ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one, one_smul]
    rw [hsv]
    show (inner ℂ x (((((singVal T n : ℝ) : ℂ) *
      inner ℂ (svVec (energyOp T) n) x) • svVec (energyOp T) n)) : ℂ) = _
    rw [inner_smul_right, mul_assoc]
    congr 1
    have hconj : (inner ℂ x (svVec (energyOp T) n) : ℂ)
        = starRingEnd ℂ (inner ℂ (svVec (energyOp T) n) x) := (inner_conj_symm _ _).symm
    rw [hconj, Complex.mul_conj']
  simp only [hval] at hmap
  have hre := hmap.map (Complex.reCLM : ℂ →L[ℝ] ℝ) Complex.reCLM.continuous
  have hfun : (⇑(Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ fun b : ℕ => ((singVal T b : ℝ) : ℂ) *
        ((‖(inner ℂ (svVec (energyOp T) b) x : ℂ)‖ : ℝ) : ℂ) ^ 2)
      = fun b : ℕ => singVal T b * ‖(inner ℂ (svVec (energyOp T) b) x : ℂ)‖ ^ 2 := by
    funext b
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hfun] at hre
  exact hre

/-! ## The bathtub inequality -/

/-- **Bathtub.**  A decreasing nonnegative weight paired against a `[0,1]`-valued profile of total
mass at most `N` is dominated by the sum of its first `N` values. -/
theorem tsum_mul_le_sum_range_of_antitone {μ c : ℕ → ℝ} (hμ0 : ∀ k, 0 ≤ μ k)
    (hanti : Antitone μ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1)
    (hcs : Summable c) (hmcs : Summable fun k => μ k * c k) (N : ℕ)
    (hN : ∑' k, c k ≤ (N : ℝ)) :
    ∑' k, μ k * c k ≤ ∑ n ∈ Finset.range N, μ n := by
  have hsplit_c : ∑ k ∈ Finset.range N, c k + ∑' k, c (k + N) = ∑' k, c k :=
    hcs.sum_add_tsum_nat_add N
  have hsplit_mc : ∑ k ∈ Finset.range N, μ k * c k + ∑' k, μ (k + N) * c (k + N)
      = ∑' k, μ k * c k := hmcs.sum_add_tsum_nat_add N
  have hcs' : Summable fun k => c (k + N) := hcs.comp_injective (add_left_injective N)
  have hmcs' : Summable fun k => μ (k + N) * c (k + N) :=
    hmcs.comp_injective (add_left_injective N)
  have htail : ∑' k, μ (k + N) * c (k + N) ≤ μ N * ∑' k, c (k + N) := by
    rw [← hcs'.tsum_mul_left]
    refine hmcs'.tsum_le_tsum (fun k => ?_) (hcs'.mul_left (μ N))
    exact mul_le_mul_of_nonneg_right (hanti (Nat.le_add_left N k)) (hc0 _)
  have hhead : ∑ k ∈ Finset.range N, μ k * c k
      ≤ ∑ k ∈ Finset.range N, μ k + μ N * (∑ k ∈ Finset.range N, c k - (N : ℝ)) := by
    have hterm : ∀ k ∈ Finset.range N, μ k * c k ≤ μ k + μ N * (c k - 1) := by
      intro k hk
      have hkN : k ≤ N := le_of_lt (Finset.mem_range.mp hk)
      have hμk : μ N ≤ μ k := hanti hkN
      nlinarith [hc1 k, hμk]
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    simp
  have hmass : ∑ k ∈ Finset.range N, c k - (N : ℝ) + ∑' k, c (k + N) ≤ 0 := by
    have := hsplit_c
    linarith [hN, this]
  have hμN : 0 ≤ μ N := hμ0 N
  calc ∑' k, μ k * c k
      = ∑ k ∈ Finset.range N, μ k * c k + ∑' k, μ (k + N) * c (k + N) := hsplit_mc.symm
    _ ≤ (∑ k ∈ Finset.range N, μ k + μ N * (∑ k ∈ Finset.range N, c k - (N : ℝ)))
        + μ N * ∑' k, c (k + N) := add_le_add hhead htail
    _ = ∑ k ∈ Finset.range N, μ k
        + μ N * ((∑ k ∈ Finset.range N, c k - (N : ℝ)) + ∑' k, c (k + N)) := by ring
    _ ≤ ∑ k ∈ Finset.range N, μ k := by nlinarith [hmass, hμN]

/-! ## The majorization theorem -/

set_option maxHeartbeats 1000000 in
/-- **The diagonal of a positive compact operator is majorized by its singular values.**  For
every orthonormal-with-zeros family and every finite index set of cardinality at most `N`,

`∑ ⟨g i, T (g i)⟩ ≤ ∑_{n<N} sₙ(T)`.

No modulation or basis hypothesis enters: this is Bessel on both sides of the singular-value
expansion of the quadratic form, followed by the bathtub inequality. -/
theorem sum_re_inner_le_sum_singVal (hcpt : IsCompactOperator T) (hT : 0 ≤ T)
    {ι : Type*} (g : ι → H) (hg : ∀ i, g i = 0 ∨ ‖g i‖ = 1)
    (hgo : ∀ i j, i ≠ j → inner ℂ (g i) (g j) = 0)
    (s : Finset ι) {N : ℕ} (hcard : s.card ≤ N) :
    ∑ i ∈ s, RCLike.re (inner ℂ (g i) (T (g i)) : ℂ) ≤ ∑ n ∈ Finset.range N, singVal T n := by
  classical
  set e : ℕ → H := fun k => svVec (energyOp T) k with he
  set c : ℕ → ℝ := fun k => ∑ i ∈ s, ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 with hc
  have hcsummable : Summable c := by
    refine summable_sum fun i _ => ?_
    exact summable_inner_svVec_sq hcpt (g i)
  have hmcsummable : Summable fun k => singVal T k * c k := by
    have : (fun k => singVal T k * c k)
        = fun k => ∑ i ∈ s, singVal T k * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
      funext k
      rw [hc, Finset.mul_sum]
    rw [this]
    refine summable_sum fun i _ => ?_
    exact (hasSum_re_inner_apply_of_nonneg hcpt hT (g i)).summable
  have hexpand : ∑ i ∈ s, RCLike.re (inner ℂ (g i) (T (g i)) : ℂ)
      = ∑' k, singVal T k * c k := by
    have hind : ∀ i ∈ s, RCLike.re (inner ℂ (g i) (T (g i)) : ℂ)
        = ∑' k, singVal T k * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := fun i _ =>
      ((hasSum_re_inner_apply_of_nonneg hcpt hT (g i)).tsum_eq).symm
    rw [Finset.sum_congr rfl hind]
    rw [← Summable.tsum_finsetSum (fun i _ => (hasSum_re_inner_apply_of_nonneg hcpt hT
      (g i)).summable)]
    refine tsum_congr fun k => ?_
    rw [hc, Finset.mul_sum]
  rw [hexpand]
  refine tsum_mul_le_sum_range_of_antitone (singVal_nonneg T) (singVal_antitone T)
    (fun k => by positivity) (fun k => ?_) hcsummable hmcsummable N ?_
  · show ∑ i ∈ s, ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 ≤ 1
    have hbessel := RHTower.sum_inner_sq_le_of_orthonormal_with_zeros g hg hgo (e k) s
    have hswap : ∀ i, ‖(inner ℂ (e k) (g i) : ℂ)‖ = ‖(inner ℂ (g i) (e k) : ℂ)‖ := by
      intro i
      rw [← inner_conj_symm, RCLike.norm_conj]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hswap i])]
    refine le_trans hbessel ?_
    rcases eq_or_ne (svVal (energyOp T) k) 0 with h0 | hne
    · rw [he]
      simp only []
      rw [svVec_eq_zero_of_svVal_eq_zero _ h0, norm_zero]
      norm_num
    · rw [he]
      simp only []
      rw [norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
        (energyOp_pos T) hne]
      norm_num
  · have hswapsum : ∑' k, c k = ∑ i ∈ s, ∑' k, ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
      rw [hc]
      exact Summable.tsum_finsetSum (fun i _ => summable_inner_svVec_sq hcpt (g i))
    rw [hswapsum]
    have hterm : ∀ i ∈ s, ∑' k, ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 ≤ 1 := by
      intro i _
      refine le_trans (tsum_inner_svVec_sq_le hcpt (g i)) ?_
      rcases hg i with h0 | h1
      · rw [h0, norm_zero]; norm_num
      · rw [h1]; norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hcard

/-! ## The trace of a positive compact operator is the sum of its singular values -/

open scoped ENNReal

set_option maxHeartbeats 1000000 in
/-- **Trace equals the singular-value sum**, in `ℝ≥0∞`, for a positive compact operator and any
Hilbert basis.  Both sides are the double sum `∑_k ∑_j sₖ |⟨eₖ, bⱼ⟩|²`, read in the two orders. -/
theorem tsum_ofReal_re_inner_basis_eq_tsum_ofReal_singVal (hcpt : IsCompactOperator T)
    (hT : 0 ≤ T) {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ∑' j : ι, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ))
      = ∑' k : ℕ, ENNReal.ofReal (singVal T k) := by
  have hdiag : ∀ j : ι, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ))
      = ∑' k : ℕ, ENNReal.ofReal (singVal T k *
        ‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2) := by
    intro j
    have hs := hasSum_re_inner_apply_of_nonneg hcpt hT (b j)
    rw [← hs.tsum_eq]
    refine ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) hs.summable
    exact mul_nonneg (singVal_nonneg T k) (by positivity)
  have hfactor : ∀ (j : ι) (k : ℕ),
      ENNReal.ofReal (singVal T k * ‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2)
        = ENNReal.ofReal (singVal T k) *
          ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2) := by
    intro j k
    rw [ENNReal.ofReal_mul (singVal_nonneg T k)]
  have hswap : ∑' j : ι, ∑' k : ℕ, ENNReal.ofReal (singVal T k) *
        ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2)
      = ∑' k : ℕ, ENNReal.ofReal (singVal T k) *
        ∑' j : ι, ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2) := by
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun k => ENNReal.tsum_mul_left
  have hpars : ∀ k : ℕ, ∑' j : ι,
      ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2)
      = ENNReal.ofReal (‖svVec (energyOp T) k‖ ^ 2) := by
    intro k
    set x : H := svVec (energyOp T) k with hx
    have hsum : HasSum (fun j : ι => ‖(inner ℂ x (b j) : ℂ)‖ ^ 2) (‖x‖ ^ 2) := by
      have h := b.hasSum_inner_mul_inner x x
      have hcongr : ∀ j : ι, (inner ℂ x (b j) : ℂ) * inner ℂ (b j) x
          = ((‖(inner ℂ x (b j) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
        intro j
        rw [← inner_conj_symm (b j) x, Complex.mul_conj']
        push_cast
        ring
      have h2 : HasSum (fun j : ι => ((‖(inner ℂ x (b j) : ℂ)‖ ^ 2 : ℝ) : ℂ))
          (inner ℂ x x : ℂ) := by
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
    rw [← hsum.tsum_eq]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum.summable).symm
  calc ∑' j : ι, ENNReal.ofReal (RCLike.re (inner ℂ (b j) (T (b j)) : ℂ))
      = ∑' j : ι, ∑' k : ℕ, ENNReal.ofReal (singVal T k) *
          ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2) := by
        refine tsum_congr fun j => ?_
        rw [hdiag j]
        exact tsum_congr fun k => hfactor j k
    _ = ∑' k : ℕ, ENNReal.ofReal (singVal T k) *
          ∑' j : ι, ENNReal.ofReal (‖(inner ℂ (svVec (energyOp T) k) (b j) : ℂ)‖ ^ 2) := hswap
    _ = ∑' k : ℕ, ENNReal.ofReal (singVal T k) := by
        refine tsum_congr fun k => ?_
        rw [hpars k]
        rcases eq_or_ne (svVal (energyOp T) k) 0 with h0 | hne
        · have hs : singVal T k = 0 := by rw [singVal, h0, Real.sqrt_zero]
          rw [hs]
          simp
        · rw [norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric T)
            (energyOp_pos T) hne]
          simp

end ContinuousLinearMap
