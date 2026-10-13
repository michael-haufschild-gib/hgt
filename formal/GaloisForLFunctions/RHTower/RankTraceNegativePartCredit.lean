import Zeta23.Assembly

/-!
# The rank–trace inequality with credit for the negative part

Let `P ⪰ 0` with `rank P ≤ r` and `Q` Hermitian with `n₊(Q) ≤ b`, and write `Q = Q₊ − Q₋` for the
spectral decomposition.  The rank–trace inequality used for the zeros of `ζ` reads

`c·tr P − (c²/4)·r + 2c·tr Q − c²·b ≤ ‖P + Q‖_F²`.

Its proof pairs the eigenvalues `p` of `P` with the eigenvalues `m` of `Q₋` (von Neumann) and bounds
`(p − m)² ≥ c p − c²/4 − 2c m`.  The sharp pointwise bound is `(p − m)² ≥ c p − c²/4 − c m`
(the difference is the square `(p − m − c/2)²`), so the inequality holds with the extra term `c·tr Q₋`
(`rank_trace_ineq_negPart`):

`c·tr P − (c²/4)·r + 2c·tr Q − c²·b + c·tr Q₋ ≤ ‖P + Q‖_F²`.

In the zero-side certificate `Q` is the sum of the blocks `f fᵀ + f̄ f̄ᵀ = 2(a aᵀ − b bᵀ)` of reflected
off-line pairs, `f = a + i b`, and `b` has size proportional to the distance of the pair from the critical
line.  The counting form (`zeroside_rank_core_negPart`)

`4 tr Â − 2N − ‖Â‖_F² + 2 tr Q₋ ≤ rank P`

therefore credits every off-line pair with twice the trace of its negative part.  The credit vanishes
exactly when the pairs coalesce on the line, which is the configuration that makes the plain certificate
sharp: any configuration attaining the bound `2N − ‖Â‖_F²` has `tr Q₋ = 0`.
-/

open Matrix Finset RHLinalg
open scoped ComplexOrder

noncomputable section

namespace RHTower

section Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sharp form of the paired-eigenvalue estimate**: for `m ≥ 0`, at most `r` indices with `p ≠ 0` and
`c ≥ 0`, `c·Σp − (c²/4)·r − c·Σm ≤ Σ(p − m)²`. -/
lemma sum_sq_diff_lower_sharp {p m : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    {r : ℕ} (hr : #{i | p i ≠ 0} ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - c ^ 2 / 4 * r - c * (∑ i, m i) ≤ ∑ i, (p i - m i) ^ 2 := by
  classical
  set s : Finset ι := {i | p i ≠ 0} with hs_def
  have hptwise : ∀ i ∈ (univ : Finset ι),
      c * p i - c * m i - (if i ∈ s then c ^ 2 / 4 else 0) ≤ (p i - m i) ^ 2 := by
    intro i _
    rcases eq_or_ne (p i) 0 with hi | hi
    · have his : i ∉ s := by simp [hs_def, mem_filter, hi]
      rw [if_neg his, hi]
      nlinarith [mul_nonneg hc (hm i), sq_nonneg (m i)]
    · have his : i ∈ s := by simp [hs_def, mem_filter, hi]
      rw [if_pos his]
      nlinarith [sq_nonneg (p i - m i - c / 2)]
  have hsum := sum_le_sum hptwise
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (#s : ℝ) * (c ^ 2 / 4) ≤ r * (c ^ 2 / 4) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hr) (by positivity)
  linarith

end Elementary

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The rank–trace inequality with credit for the negative part of `Q`.** -/
theorem rank_trace_ineq_negPart {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b + c * rtrace (hermNegPart hQ)
      ≤ frobSq (P + Q) := by
  classical
  set Qp := hermPosPart hQ with hQp_def
  set Qm := hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  set d := Fintype.card n
  set p : Fin d → ℝ := hP.isHermitian.eigenvalues₀
  set m : Fin d → ℝ := hQm_psd.isHermitian.eigenvalues₀
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm_psd.isHermitian.eigenvalues (eigEquiv k) from
      (eigenvalues_eigEquiv hQm_psd.isHermitian k).symm]
    exact hQm_psd.eigenvalues_nonneg _
  have hp_card : #{k | p k ≠ 0} ≤ r := by
    calc #{k | p k ≠ 0}
        = #{i | hP.isHermitian.eigenvalues i ≠ 0} :=
          (card_eigenvalues_reindex hP.isHermitian (· ≠ 0)).symm
      _ = P.rank := by
          rw [hP.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      _ ≤ r := hr
  have htraceP : rtrace P = ∑ k, p k := by
    rw [rtrace_eq_sum_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian id
  have htraceQm : rtrace Qm = ∑ k, m k := by
    rw [rtrace_eq_sum_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian id
  have hfrobP : frobSq P = ∑ k, (p k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hP.isHermitian]
    exact sum_eigenvalues_reindex hP.isHermitian (· ^ 2)
  have hfrobQm : frobSq Qm = ∑ k, (m k) ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian]
    exact sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2)
  -- the Frobenius expansion, using `Q₊Q₋ = 0`
  have hexpand : frobSq (P + Q)
      = frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace
        + frobSq Qp + frobSq Qm := by
    have h1 : frobSq (-Qm) = frobSq Qm := by
      unfold frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, frobSq_add_hermitian hP.isHermitian
        (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hPQp : 0 ≤ RCLike.re (P * Qp).trace := trace_mul_nonneg_of_posSemidef hP hQp_psd
  have hvN : RCLike.re (P * Qm).trace ≤ ∑ k, p k * m k :=
    vonNeumann_trace_ineq hP.isHermitian hQm_psd.isHermitian
  have hstep4 : ∑ k, (p k - m k) ^ 2
      ≤ frobSq P - 2 * RCLike.re (P * Qm).trace + frobSq Qm := by
    have hsplit : ∑ k, (p k - m k) ^ 2
        = ∑ k, (p k)^2 - 2 * ∑ k, p k * m k + ∑ k, (m k)^2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hsplit, hfrobP, hfrobQm]; linarith
  -- the sharp paired estimate
  have hstep5 : c * rtrace P - c ^ 2 / 4 * r - c * rtrace Qm ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm]
    exact sum_sq_diff_lower_sharp hm_nn hp_card hc.le
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart]
    refine sum_sq_lower_of_card_pos_le ?_ c
    calc #{i | (hQ.eigenvalues i)⁺ ≠ 0}
        = #{i | 0 < hQ.eigenvalues i} := by
          congr 1; ext i; simp [posPart_eq_zero, not_le]
      _ ≤ b := hb
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- **The `c = 2` form**: `2 tr P + 4 tr Q − 4b − ‖P + Q‖_F² + 2 tr Q₋ ≤ r`. -/
theorem rank_trace_ineq_two_negPart {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * (b : ℝ) - frobSq (P + Q) + 2 * rtrace (hermNegPart hQ)
      ≤ (r : ℝ) := by
  have h := rank_trace_ineq_negPart hP hQ hr hb (c := 2) (by norm_num)
  linarith

/-- **The counting step with credit for the negative part**: if `Â = P + Q` with `P ⪰ 0` of rank at most
`r` and trace at most `N_on`, `n₊(Q) ≤ b` and `N_on + 2b ≤ N`, then
`4 tr Â − 2N − ‖Â‖_F² + 2 tr Q₋ ≤ r`. -/
theorem zeroside_rank_core_negPart {Ahat P Q : Matrix n n 𝕜}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI' : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI') :
    4 * rtrace Ahat - 2 * NI' - frobSq Ahat + 2 * rtrace (hermNegPart hQ) ≤ r := by
  have h := rank_trace_ineq_two_negPart hP hQ hrank hpos
  subst hPQ
  rw [rtrace_add]
  linarith

/-- The credit is nonnegative, so the refined counting step implies the plain one. -/
theorem rtrace_hermNegPart_nonneg {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    0 ≤ rtrace (hermNegPart hQ) := by
  rw [rtrace_eq_sum_eigenvalues (hermNegPart_posSemidef hQ).isHermitian]
  exact Finset.sum_nonneg fun i _ => (hermNegPart_posSemidef hQ).eigenvalues_nonneg i

end RHTower
