import Zeta23.LinAlg
import Zeta23.ZeroSide

/-!
# The rank–trace inequality with its on-line and off-line spectral slack

Let `P ⪰ 0` with `rank P ≤ r`, let `Q` be Hermitian with `n₊(Q) ≤ b`, and let `c > 0`.  The
rank–trace inequality of Alpöge–Furman,

`c · tr P − (c²/4) · r + 2c · tr Q − c² · b ≤ ‖P + Q‖_F²`,

discards three nonnegative quantities in its elementary steps: half of the negative mass,
`c · tr Q₋`, the positive-spectrum slack `∑_{q > 0} (q − c)²` over the positive eigenvalues `q` of
`Q`, and the on-line slack `S_on = ∑_{p ≠ 0} (p − c/2 − m)²`, where `p` and `m` run over the
eigenvalues of `P` and of `Q₋` in decreasing order.

**Theorem** (`rank_trace_ineq_slack`).  With the same hypotheses,

`c · tr P − (c²/4) · r + 2c · tr Q − c² · b + c · tr Q₋ + ∑_{q > 0} (q − c)² + S_on ≤ ‖P + Q‖_F²`.

The first estimate becomes `(p − m)² − cp + c²/4 + cm = (p − c/2 − m)²`
(`sum_sq_diff_lower_slack`); the second keeps `q² − 2cq + c² = (q − c)²`
(`sum_sq_posPart_lower_slack`).  When `Q₋ = 0`, `S_on = ∑_{μ ∈ spec P, μ ≠ 0} (μ − c/2)²` measures how
far `(2/c) P` is from an orthogonal projection: equality in the rank–trace bound forces the
on-line frame vectors to be a Parseval frame of their span.

**Corollary** (`posSlack_ge_sq`).  The positive slack is at least `(‖Q₊‖_F − c √b)²` once
`‖Q₊‖_F ≥ c √b`: by Cauchy–Schwarz `tr Q₊ ≤ √(n₊(Q)) ‖Q₊‖_F`.

**Zero side** (`zeroside_rank_core_slack`).  For the zero-side decomposition `Â = P + Q` of the
two-thirds argument (`P` the on-line part, `Q` the off-line pair part, `tr P + 2b ≤ N`), at `c = 2`:

`4 tr Â − 2N − ‖Â‖_F² + 2 tr Q₋ + ∑_{q ∈ spec Q, q > 0} (q − 2)² + S_on ≤ r`.

An off-line pair `{ρ, 1 − ρ̄}` contributes the block `2m(x xᵀ − y yᵀ)` to `Q`, with
`u_ρ = x + i y`.  When the grid has no aliasing, `|x|² − |y|²` and `x · y` do not depend on the
displacement of the pair, so the block has eigenvalues `m(g + 1)` and `−m(g − 1)`, where
`g = |x|² + |y|² ≥ 1` grows with the displacement.  Both slack terms are therefore displacement
sensitive: an isolated pair at displacement `a = (β − ½) log T` adds about `2m(g − 1) + m²(g − 1)²`
to the on-line excess over the two-thirds bound, which vanishes only as `a → 0`.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHTower

open RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive-spectrum slack `∑_{q > 0} (q − c)²` of a Hermitian matrix. -/
def posSlack {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (c : ℝ) : ℝ :=
  ∑ i, if 0 < hQ.eigenvalues i then (hQ.eigenvalues i - c) ^ 2 else 0

lemma posSlack_nonneg {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) (c : ℝ) : 0 ≤ posSlack hQ c :=
  sum_nonneg fun i _ => by split_ifs <;> positivity

/-- The second elementary estimate of the rank–trace inequality with its slack retained:
`2c ∑ q⁺ − c² b + ∑_{q > 0} (q − c)² ≤ ∑ (q⁺)²` when at most `b` values are positive. -/
lemma sum_sq_posPart_lower_slack {ι : Type*} [Fintype ι] {e : ι → ℝ} {b : ℕ}
    (hb : #{i | 0 < e i} ≤ b) (c : ℝ) :
    2 * c * (∑ i, (e i)⁺) - c ^ 2 * b +
        (∑ i, if 0 < e i then (e i - c) ^ 2 else 0) ≤ ∑ i, ((e i)⁺) ^ 2 := by
  classical
  have hpt : ∀ i ∈ (univ : Finset ι),
      2 * c * (e i)⁺ - (if 0 < e i then c ^ 2 else 0) +
          (if 0 < e i then (e i - c) ^ 2 else 0) = ((e i)⁺) ^ 2 := by
    intro i _
    by_cases h : 0 < e i
    · rw [if_pos h, if_pos h, posPart_eq_self.mpr h.le]; ring
    · rw [if_neg h, if_neg h, posPart_eq_zero.mpr (not_lt.mp h)]; ring
  have hsum := sum_congr rfl hpt
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum] at hsum
  have hcard : (∑ i, if 0 < e i then c ^ 2 else (0 : ℝ)) ≤ c ^ 2 * b := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb) (sq_nonneg c)
  linarith

/-- The first elementary estimate of the rank–trace inequality with half of the negative mass
and the pointwise slack retained: for `p, m ≥ 0` with at most `r` nonzero `p`, and `c ≥ 0`,
`c ∑ p − (c²/4) r − c ∑ m + ∑_{p ≠ 0} (p − c/2 − m)² ≤ ∑ (p − m)²`.  Pointwise,
`(p−m)² − cp + c²/4 + cm = (p − c/2 − m)²` when `p ≠ 0`, and `m² + cm ≥ 0` when `p = 0`. -/
lemma sum_sq_diff_lower_slack {ι : Type*} [Fintype ι] {p m : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    {r : ℕ} (hr : #{i | p i ≠ 0} ≤ r) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - c ^ 2 / 4 * r - c * (∑ i, m i)
        + (∑ i, if p i ≠ 0 then (p i - c / 2 - m i) ^ 2 else 0) ≤ ∑ i, (p i - m i) ^ 2 := by
  classical
  set s : Finset ι := {i | p i ≠ 0} with hs_def
  have hptwise : ∀ i ∈ (univ : Finset ι),
      c * p i - c * m i - (if i ∈ s then c ^ 2 / 4 else 0)
          + (if p i ≠ 0 then (p i - c / 2 - m i) ^ 2 else 0) ≤ (p i - m i) ^ 2 := by
    intro i _
    rcases eq_or_ne (p i) 0 with hi | hi
    · have his : i ∉ s := by simp [hs_def, mem_filter, hi]
      rw [if_neg his, if_neg (not_not.mpr hi), hi]
      nlinarith [hm i, sq_nonneg (m i), mul_nonneg hc (hm i)]
    · have his : i ∈ s := by simp [hs_def, mem_filter, hi]
      rw [if_pos his, if_pos hi]
      ring_nf; exact le_rfl
  have hsum := sum_le_sum hptwise
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (#s : ℝ) * (c ^ 2 / 4) ≤ r * (c ^ 2 / 4) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hr) (by positivity)
  linarith

/-- The on-line slack of the rank–trace inequality: with `p` the eigenvalues of `P` and `m` those
of the negative part `Q₋`, both in decreasing order, `∑_{p ≠ 0} (p − c/2 − m)²`.  When `Q₋ = 0` it
is the defect `∑_{μ ∈ spec P, μ ≠ 0} (μ − c/2)²`, which vanishes exactly when `(2/c) P` is an
orthogonal projection. -/
def onSlack {P Q : Matrix n n 𝕜} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (c : ℝ) : ℝ :=
  ∑ k, if hP.eigenvalues₀ k ≠ 0 then
      (hP.eigenvalues₀ k - c / 2 - (hermNegPart_posSemidef hQ).isHermitian.eigenvalues₀ k) ^ 2
    else 0

lemma onSlack_nonneg {P Q : Matrix n n 𝕜} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (c : ℝ) :
    0 ≤ onSlack hP hQ c :=
  sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- **Rank–trace inequality with spectral slack.**  Hypotheses: `P ⪰ 0`, `rank P ≤ r`,
`Q` Hermitian with `n₊(Q) ≤ b`, `c > 0`.  Then
`c · tr P − (c²/4) · r + 2c · tr Q − c² · b + c · tr Q₋ + ∑_{q > 0} (q − c)² + S_on ≤ ‖P + Q‖_F²`,
with `S_on` the on-line slack `onSlack`. -/
theorem rank_trace_ineq_slack {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - c ^ 2 / 4 * r + 2 * c * rtrace Q - c ^ 2 * b
        + c * rtrace (hermNegPart hQ) + posSlack hQ c + onSlack hP.isHermitian hQ c
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
  have hon : onSlack hP.isHermitian hQ c
      = ∑ k, if p k ≠ 0 then (p k - c / 2 - m k) ^ 2 else 0 := rfl
  have hstep5 : c * rtrace P - c^2/4 * r - c * rtrace Qm + onSlack hP.isHermitian hQ c
      ≤ ∑ k, (p k - m k) ^ 2 := by
    rw [htraceP, htraceQm, hon]
    exact sum_sq_diff_lower_slack hm_nn hp_card hc.le
  have hstep6 : 2 * c * rtrace Qp - c ^ 2 * b + posSlack hQ c ≤ frobSq Qp := by
    rw [hQp_def, rtrace_hermPosPart, frobSq_hermPosPart, posSlack]
    exact sum_sq_posPart_lower_slack hb c
  have htraceQ : 2 * c * rtrace Q = 2 * c * rtrace Qp - 2 * c * rtrace Qm := by
    rw [hQdec, rtrace_sub]; ring
  linarith [hstep4, hstep5, hstep6, hPQp, hexpand, htraceQ]

/-- **Slack from the Frobenius norm of the positive part.**  If `n₊(Q) ≤ b` and
`c √b ≤ ‖Q₊‖_F`, then `(‖Q₊‖_F − c √b)² ≤ ∑_{q > 0} (q − c)²`. -/
theorem posSlack_ge_sq {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ}
    (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 ≤ c)
    (hbig : c * Real.sqrt b ≤ Real.sqrt (frobSq (hermPosPart hQ))) :
    (Real.sqrt (frobSq (hermPosPart hQ)) - c * Real.sqrt b) ^ 2 ≤ posSlack hQ c := by
  classical
  set e := hQ.eigenvalues
  set s : Finset n := {i | 0 < e i}
  have hs : #s ≤ b := hb
  have hF : frobSq (hermPosPart hQ) = ∑ i ∈ s, (e i) ^ 2 := by
    rw [frobSq_hermPosPart, ← sum_filter_add_sum_filter_not univ (fun i => 0 < e i)]
    rw [sum_eq_zero (s := filter (fun i => ¬ 0 < e i) univ) (fun i hi => by
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi
      rw [posPart_eq_zero.mpr hi]; ring), add_zero]
    exact sum_congr rfl fun i hi => by
      simp only [s, mem_filter, mem_univ, true_and] at hi
      rw [posPart_eq_self.mpr hi.le]
  have hS : posSlack hQ c = ∑ i ∈ s, (e i - c) ^ 2 := by
    rw [posSlack, ← sum_filter]
  set F := ∑ i ∈ s, (e i) ^ 2
  set A := ∑ i ∈ s, e i
  have hF_nn : 0 ≤ F := sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i ∈ s, (e i - c) ^ 2 = F - 2 * c * A + c ^ 2 * #s := by
    have hpt : ∀ i ∈ s, (e i - c) ^ 2 = e i ^ 2 - 2 * c * e i + c ^ 2 := fun _ _ => by ring
    rw [sum_congr rfl hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      nsmul_eq_mul]
    ring
  -- Cauchy–Schwarz: `A ≤ √#s · √F`.
  have hCS : A ≤ Real.sqrt #s * Real.sqrt F := by
    have h1 : A ^ 2 ≤ #s * F := sq_sum_le_card_mul_sum_sq
    have hA2 : A ≤ Real.sqrt (#s * F) := Real.le_sqrt_of_sq_le h1
    rwa [Real.sqrt_mul (by positivity)] at hA2
  rw [hF] at hbig ⊢
  rw [hS, hexp]
  have hsb : Real.sqrt #s ≤ Real.sqrt b := Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have hsqF : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF_nn
  have hsqs : Real.sqrt (#s : ℝ) ^ 2 = #s := Real.sq_sqrt (by positivity)
  have hsqb : Real.sqrt (b : ℝ) ^ 2 = b := Real.sq_sqrt (by positivity)
  have hsF_nn : 0 ≤ Real.sqrt F := Real.sqrt_nonneg _
  have hss_nn : 0 ≤ Real.sqrt (#s : ℝ) := Real.sqrt_nonneg _
  -- `F − 2cA + c²#s ≥ F − 2c√#s√F + c²#s = (√F − c√#s)² ≥ (√F − c√b)²`.
  have hkey : (Real.sqrt F - c * Real.sqrt #s) ^ 2 ≤ F - 2 * c * A + c ^ 2 * #s := by
    nlinarith [mul_le_mul_of_nonneg_left hCS (by positivity : (0 : ℝ) ≤ 2 * c)]
  have hmono : (Real.sqrt F - c * Real.sqrt b) ^ 2 ≤ (Real.sqrt F - c * Real.sqrt #s) ^ 2 := by
    have h1 : 0 ≤ Real.sqrt F - c * Real.sqrt b := by linarith
    have h2 : Real.sqrt F - c * Real.sqrt b ≤ Real.sqrt F - c * Real.sqrt #s := by
      nlinarith [mul_le_mul_of_nonneg_left hsb hc]
    exact pow_le_pow_left₀ h1 h2 2
  linarith

/-- **Zero-side rank–trace core with spectral slack** (`c = 2`).  For `Â = P + Q` with `P ⪰ 0`,
`rank P ≤ r`, `n₊(Q) ≤ b`, `tr P ≤ N_on` and `N_on + 2b ≤ N'`:

`4 tr Â − 2N' − ‖Â‖_F² + 2 tr Q₋ + ∑_{q ∈ spec Q, q > 0} (q − 2)² + S_on ≤ r`, with `S_on` the on-line
slack at `c = 2`. -/
theorem zeroside_rank_core_slack {Ahat P Q : Matrix n n 𝕜}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI' : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI') :
    4 * rtrace Ahat - 2 * NI' - frobSq Ahat + 2 * rtrace (hermNegPart hQ) + posSlack hQ 2
        + onSlack hP.isHermitian hQ 2 ≤ r := by
  have h := rank_trace_ineq_slack hP hQ hrank hpos (c := 2) (by norm_num)
  subst hPQ
  rw [rtrace_add]
  linarith

end RHTower
