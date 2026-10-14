import GaloisForLFunctions.RHTower.JointAncestryShellAmplitudeAbscissaDuality
import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound

/-!
# A power-sum criterion for RH from dyadic shells

For a zero `ρ` let `W_ρ(N)` be its large prime sum over the shell `(N, 2N]` at level one
(`W(1 − (ρ − ½))` right of the line, `W(1 + (ρ − ½))` left of it, `W(s) = Σ_{N<p≤2N} p^{−s}`), and put

`P_k(N) = Σ_ρ W_ρ(N)^k / (ρ(1−ρ))`   (`jasShellPowerSum`).

**Theorem** (`riemannHypothesis_iff_zerosApproachLine_and_shellPowerSum_growth`).

`RH ⟺ ZAL ∧ ∀ ε > 0, ∃ᶠ N, ∀ k ≥ 1, |P_k(N)| ≤ N^{εk}`,

and the same with "no off-line chain" in place of ZAL.

* Under RH every `|W_ρ(N)| ≤ Σ_{N<p≤2N} 1/p ≤ 1`, so `|P_k(N)| ≤ Σ_ρ |1/(ρ(1−ρ))|`.
* A maximal off-line zero at distance `δ` forces `|P_k(N)| ≥ c N^{kδ}/(log N)^k` for some bounded
  `k` at every large `N` (`eventually_exists_large_shellPowerSum_of_maximal_offLine`).  Turán's
  weighted power-sum theorem applies to the finite tie group of the largest shell sums; the other
  zeros of a fixed finite set have shell sums at most `ρ₂ < 1` times the top, and the remaining
  zeros carry little weight.  No anti-alignment and no kernel approximation are needed: the
  criterion is exact.

This is the power-sum (Turán) form of the dyadic-shell receiver: the growth rate of the zero power
sums of the shell prime sums is exactly the largest distance of a zero from the critical line.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- The zero power sum `P_k(N) = Σ_ρ W_ρ(N)^k/(ρ(1−ρ))` of the shell `(N, 2N]`. -/
def jasShellPowerSum (N k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, jasBigSum (jasPrimeWindow N (2 * N)) 1 (q.1 : ℂ) ^ k *
    (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))

theorem abs_re_sub_half_lt_half_xiZeroCopy (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  rw [abs_lt]; constructor <;> linarith

/-- The shell sum of a zero is at most `Σ_{p ∈ P} p^{−½}`. -/
theorem norm_jasBigSum_le_half (P : Finset Nat.Primes) (q : XiZeroCopy) :
    ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ ∑ p ∈ P, Real.exp (-(1 / 2) * Real.log p) := by
  refine (norm_jasBigSum_le P 1 _).trans (Finset.sum_le_sum fun p _ => ?_)
  have := abs_re_sub_half_lt_half_xiZeroCopy q
  exact exp_neg_mul_log_prime_anti (by linarith) p

theorem summable_jasShellPowerSum_terms (N k : ℕ) :
    Summable fun q : XiZeroCopy => jasBigSum (jasPrimeWindow N (2 * N)) 1 (q.1 : ℂ) ^ k *
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 / 2) * Real.log p) := ⟨_, rfl⟩
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left (C ^ k)) fun q => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (norm_nonneg _)
  rw [hC]; exact norm_jasBigSum_le_half _ q

/-- Under RH every shell sum has norm at most `1`. -/
theorem norm_jasBigSum_le_one_of_riemannHypothesis (hRH : RiemannHypothesis) (N : ℕ)
    (q : XiZeroCopy) : ‖jasBigSum (jasPrimeWindow N (2 * N)) 1 (q.1 : ℂ)‖ ≤ 1 := by
  have hq := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  refine (norm_jasBigSum_le _ 1 _).trans ?_
  rw [hq, sub_self, abs_zero, sub_zero]
  -- `Σ_{N < p ≤ 2N} 1/p ≤ #(N, 2N] / N ≤ 1`
  have hterm : ∀ p ∈ jasPrimeWindow N (2 * N), Real.exp (-1 * Real.log p) ≤ 1 / ((N : ℝ) + 1) := by
    intro p hp
    have hNp : N < (p : ℕ) := (mem_jasPrimeWindow.mp hp).1
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [neg_one_mul, Real.exp_neg, Real.exp_log hp0]
    have : ((N : ℝ) + 1) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hNp
    exact (inv_eq_one_div _).trans_le (one_div_le_one_div_of_le (by positivity) this)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((jasPrimeWindow N (2 * N)).card : ℝ) ≤ (N : ℝ) + 1 := by
    have h1 : (jasPrimeWindow N (2 * N)).card ≤ (Finset.Ioc N (2 * N)).card := by
      refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ)) (fun p hp => ?_)
        (Subtype.val_injective.injOn)
      have := mem_jasPrimeWindow.mp hp
      exact Finset.mem_Ioc.mpr this
    rw [Nat.card_Ioc] at h1
    have : ((2 * N - N : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by
      have : 2 * N - N = N := by omega
      rw [this]; linarith
    exact (Nat.cast_le.mpr h1).trans this
  rw [mul_one_div, div_le_one (by positivity)]
  exact hcard

/-- **Under RH the shell power sums stay bounded**: `|P_k(N)| ≤ Σ_ρ |1/(ρ(1−ρ))|`. -/
theorem norm_jasShellPowerSum_le_of_riemannHypothesis (hRH : RiemannHypothesis) (N k : ℕ) :
    ‖jasShellPowerSum N k‖ ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
  rw [jasShellPowerSum]
  refine (norm_tsum_le_tsum_norm (summable_jasShellPowerSum_terms N k).norm).trans ?_
  refine Summable.tsum_le_tsum (fun q => ?_) (summable_jasShellPowerSum_terms N k).norm
    summable_inv_mul_one_sub.norm
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_jasBigSum_le_one_of_riemannHypothesis hRH N q))

/-! ## One shell: Turán on the tie group -/

/-- **One shell, any zero function.**  Let `B` assign a complex number to every zero, with the
power sums `Σ_q B(q)^ν/(q(1−q))` absolutely convergent.  Let `G ⊆ F` be finite sets of zeros,
`Z = |B(qm)|` for some `qm ∈ G`, the other zeros of `F` with `|B| ≤ ρ₂ Z` (`ρ₂ ≤ 1`), and all zeros
outside `F` with `|B| ≤ K Z` (`K ≥ 1`).  With weights of uniform angle `c` and size `≥ w_min` on `G`, total weight `≤ W₁` on `F`,
tail weight `≤ T` outside `F`, and `W₁ ρ₂^{M+1} + T K^{M+n} ≤ β/(2D)` (`β = c w_min`, `n = |G|`,
`D` Turán's constant), some `ν ∈ [M+1, M+n]` has `|Σ_q B(q)^ν/(q(1−q))| ≥ β Z^ν/(2D)`. -/
theorem exists_norm_tsum_pow_mul_ge (B : XiZeroCopy → ℂ) {G F : Finset XiZeroCopy}
    {qm : XiZeroCopy} {Z ρ₂ K c wmin W₁ T : ℝ} (M : ℕ)
    (hsumm : ∀ ν : ℕ, Summable fun q : XiZeroCopy => B q ^ ν * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))))
    (hGF : G ⊆ F) (hqm : qm ∈ G)
    (hZ : Z = ‖B qm‖) (hZ0 : 0 < Z)
    (hcomp : ∀ q ∈ F, q ∉ G → ‖B q‖ ≤ ρ₂ * Z)
    (hρ₂0 : 0 ≤ ρ₂) (hρ₂1 : ρ₂ ≤ 1)
    (htail : ∀ q : XiZeroCopy, q ∉ F → ‖B q‖ ≤ K * Z)
    (hK : 1 ≤ K) (hc : 0 < c)
    (hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re)
    (hwmin : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) (hwmin0 : 0 < wmin)
    (hW₁ : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W₁)
    (hT : ∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖ ≤ T)
    (hMT : W₁ * ρ₂ ^ (M + 1) + T * K ^ (M + G.card) ≤ c * wmin /
      (2 * (2 * (Real.exp 1 * G.card * (6 * (G.card + 1) * ((M : ℝ) + 2 * G.card + 2)) ^ G.card)))) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + G.card ∧
      c * wmin / (2 * (2 * (Real.exp 1 * G.card * (6 * (G.card + 1) *
        ((M : ℝ) + 2 * G.card + 2)) ^ G.card))) * Z ^ ν ≤
        ‖∑' q : XiZeroCopy, B q ^ ν * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))‖ := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Real.exp 1 * G.card *
      (6 * (G.card + 1) * ((M : ℝ) + 2 * G.card + 2)) ^ G.card) := ⟨_, rfl⟩
  rw [← hD] at hMT ⊢
  have hn1 : (1 : ℝ) ≤ G.card := by exact_mod_cast Finset.card_pos.mpr ⟨qm, hqm⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  -- abbreviations
  set w : XiZeroCopy → ℂ := fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hw
  -- Turán on `G`
  have hβ0 : 0 < c * wmin := mul_pos hc hwmin0
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have htop : ∃ i ∈ G, 1 ≤ ‖B i / (Z : ℂ)‖ := by
    refine ⟨qm, hqm, ?_⟩
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ0.le, ← hZ, div_self hZ0.ne']
  have hβ : ∀ t : ℝ, 1 - 1 / ((M : ℝ) + 2 * G.card + 2) ≤ t → t ≤ 1 →
      c * wmin ≤ ‖∑ i ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖), w i‖ := by
    intro t _ ht1
    have hmem : qm ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖) := by
      refine Finset.mem_filter.mpr ⟨hqm, ?_⟩
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ0.le, ← hZ, div_self hZ0.ne']
      exact ht1
    have h1 : c * ∑ i ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖), ‖w i‖ ≤
        (∑ i ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖), w i).re := by
      rw [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => hcw i (Finset.mem_filter.mp hi).1
    have h2 : ‖w qm‖ ≤ ∑ i ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖), ‖w i‖ :=
      Finset.single_le_sum (f := fun i => ‖w i‖) (fun i _ => norm_nonneg _) hmem
    have h3 := Complex.re_le_norm (∑ i ∈ G.filter (fun i => t ≤ ‖B i / (Z : ℂ)‖), w i)
    have h4 := mul_le_mul_of_nonneg_left ((hwmin qm hqm).trans h2) hc.le
    linarith
  obtain ⟨ν, hν1, hν2, hν⟩ := GaloisForLFunctions.HTGeometry.exists_norm_weightedPowerSum_ge G
    (fun i => B i / (Z : ℂ)) w htop M hβ0 hβ
  rw [← hD] at hν
  refine ⟨ν, hν1, hν2, ?_⟩
  -- the tie-group sum
  have hGsum : c * wmin / D * Z ^ ν ≤ ‖∑ i ∈ G, B i ^ ν * w i‖ := by
    have e : ∑ i ∈ G, B i ^ ν * w i = (Z : ℂ) ^ ν * ∑ i ∈ G, w i * (B i / (Z : ℂ)) ^ ν := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_pow]; field_simp
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hZ0.le]
    have := mul_le_mul_of_nonneg_left hν (pow_nonneg hZ0.le ν)
    linarith
  -- the rest of `F`
  have hFG : ‖∑ i ∈ F \ G, B i ^ ν * w i‖ ≤ W₁ * ρ₂ ^ (M + 1) * Z ^ ν := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i ∈ F \ G, ‖B i ^ ν * w i‖ ≤ ‖w i‖ * (ρ₂ ^ (M + 1) * Z ^ ν) := by
      intro i hi
      obtain ⟨hiF, hiG⟩ := Finset.mem_sdiff.mp hi
      rw [norm_mul, norm_pow, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖B i‖ ^ ν ≤ (ρ₂ * Z) ^ ν := pow_le_pow_left₀ (norm_nonneg _) (hcomp i hiF hiG) ν
        _ = ρ₂ ^ ν * Z ^ ν := mul_pow _ _ _
        _ ≤ ρ₂ ^ (M + 1) * Z ^ ν :=
            mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ₂0 hρ₂1 hν1) (pow_nonneg hZ0.le _)
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.sum_mul]
    have h1 : ∑ i ∈ F \ G, ‖w i‖ ≤ W₁ :=
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => norm_nonneg _).trans
        hW₁
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ρ₂ ^ (M + 1) * Z ^ ν)
    linarith
  -- the tail
  have hsumm := hsumm ν
  have htl : ‖∑' i : {x // x ∉ F}, B i ^ ν * w i‖ ≤ T * K ^ (M + G.card) * Z ^ ν := by
    have hb : ∀ i : {x // x ∉ F}, ‖B i ^ ν * w i‖ ≤ ‖w i‖ * (K ^ (M + G.card) * Z ^ ν) := by
      intro i
      rw [norm_mul, norm_pow, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖B i‖ ^ ν ≤ (K * Z) ^ ν := pow_le_pow_left₀ (norm_nonneg _) (htail i i.2) ν
        _ = K ^ ν * Z ^ ν := mul_pow _ _ _
        _ ≤ K ^ (M + G.card) * Z ^ ν :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hν2) (pow_nonneg hZ0.le _)
    have hwsum : Summable fun i : {x // x ∉ F} => ‖w i‖ := summable_inv_mul_one_sub.norm.subtype _
    calc ‖∑' i : {x // x ∉ F}, B i ^ ν * w i‖ ≤ ∑' i : {x // x ∉ F}, ‖B i ^ ν * w i‖ :=
          norm_tsum_le_tsum_norm (hsumm.norm.subtype _)
      _ ≤ ∑' i : {x // x ∉ F}, ‖w i‖ * (K ^ (M + G.card) * Z ^ ν) :=
          Summable.tsum_le_tsum hb (hsumm.norm.subtype _) (hwsum.mul_right _)
      _ = (∑' i : {x // x ∉ F}, ‖w i‖) * (K ^ (M + G.card) * Z ^ ν) := tsum_mul_right
      _ ≤ T * (K ^ (M + G.card) * Z ^ ν) :=
          mul_le_mul_of_nonneg_right hT (by positivity)
      _ = T * K ^ (M + G.card) * Z ^ ν := by ring
  -- assemble
  have hsplit : ∑' q : XiZeroCopy, B q ^ ν * w q =
      (∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i) +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i := by
    rw [← hsumm.sum_add_tsum_subtype_compl F, ← Finset.sum_sdiff hGF, add_comm
      (∑ x ∈ F \ G, _)]
  rw [hsplit]
  have h1 := norm_sub_norm_le (∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i +
    ∑' i : {x // x ∉ F}, B i ^ ν * w i) (-(∑ i ∈ F \ G, B i ^ ν * w i +
    ∑' i : {x // x ∉ F}, B i ^ ν * w i))
  have e2 : ∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i - -(∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i) = ∑ i ∈ G, B i ^ ν * w i +
      2 * (∑ i ∈ F \ G, B i ^ ν * w i + ∑' i : {x // x ∉ F}, B i ^ ν * w i) := by ring
  have hrest : ‖∑ i ∈ F \ G, B i ^ ν * w i + ∑' i : {x // x ∉ F}, B i ^ ν * w i‖ ≤
      (W₁ * ρ₂ ^ (M + 1) + T * K ^ (M + G.card)) * Z ^ ν := by
    refine (norm_add_le _ _).trans ?_
    linarith
  have hlow : ‖∑ i ∈ G, B i ^ ν * w i‖ ≤ ‖∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i‖ + ‖∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i‖ := by
    have := norm_sub_le (∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i) (∑ i ∈ F \ G, B i ^ ν * w i +
      ∑' i : {x // x ∉ F}, B i ^ ν * w i)
    have e3 : ∑ i ∈ G, B i ^ ν * w i + ∑ i ∈ F \ G, B i ^ ν * w i +
        ∑' i : {x // x ∉ F}, B i ^ ν * w i - (∑ i ∈ F \ G, B i ^ ν * w i +
        ∑' i : {x // x ∉ F}, B i ^ ν * w i) = ∑ i ∈ G, B i ^ ν * w i := by ring
    rw [e3] at this
    exact this
  have hZν : 0 ≤ Z ^ ν := pow_nonneg hZ0.le ν
  have hmain : c * wmin / D * Z ^ ν - (W₁ * ρ₂ ^ (M + 1) + T * K ^ (M + G.card)) * Z ^ ν ≥
      c * wmin / (2 * D) * Z ^ ν := by
    have h2 := mul_le_mul_of_nonneg_right hMT hZν
    have e : c * wmin / D * Z ^ ν = 2 * (c * wmin / (2 * D) * Z ^ ν) := by field_simp
    linarith
  linarith

/-- A Turán window: for `0 < ρ < 1` the geometric decay beats the polynomial Turán constant. -/
theorem exists_turan_window (n : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A : ℝ) {B : ℝ}
    (hB : 0 < B) : ∃ M : ℕ, A * ρ ^ (M + 1) * (2 * (Real.exp 1 * n *
      (6 * (n + 1) * ((M : ℝ) + 2 * n + 2)) ^ n)) ≤ B := by
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one n
    (show |ρ| < 1 by rw [abs_of_pos hρ0]; exact hρ1)).comp
    (tendsto_add_atTop_nat (2 * n + 2))
  have h2 := h1.const_mul (A * ρ ^ (1 : ℕ) / ρ ^ (2 * n + 2) * (2 * (Real.exp 1 * n * 6 ^ n *
    ((n : ℝ) + 1) ^ n)))
  rw [mul_zero] at h2
  obtain ⟨M, hM⟩ := (h2.eventually (ge_mem_nhds hB)).exists
  refine ⟨M, le_of_eq_of_le ?_ hM⟩
  simp only [Function.comp]
  have hρn : ρ ^ (2 * n + 2) ≠ 0 := pow_ne_zero _ hρ0.ne'
  have e1 : (6 * ((n : ℝ) + 1) * ((M : ℝ) + 2 * n + 2)) ^ n =
      6 ^ n * ((n : ℝ) + 1) ^ n * ((M : ℝ) + 2 * n + 2) ^ n := by rw [mul_pow, mul_pow]
  have e2 : ρ ^ (M + (2 * n + 2)) = ρ ^ (M + 1) * ρ ^ (2 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have e3 : ρ ^ (2 * n + 2) = ρ ^ 1 * ρ ^ (2 * n + 1) := by rw [← pow_add]; congr 1; omega
  push_cast
  rw [e1, e2, e3]
  have hρ1' : ρ ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hρ0.ne'
  field_simp
  ring

/-! ## Every large shell -/

/-- **A maximal off-line zero makes the shell power sums grow.**  If a zero off the critical line
has the largest distance `δ` from it among all zeros and `ε < δ`, then for every sufficiently
large `N` some `k ≥ 1` has `|P_k(N)| > N^{εk}`. -/
theorem eventually_exists_large_shellPowerSum_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {ε : ℝ}
    (hε : ε < |(q₀.1 : ℂ).re - 1 / 2|) :
    ∀ᶠ N : ℕ in atTop, ∃ k : ℕ, 1 ≤ k ∧ (N : ℝ) ^ (ε * k) < ‖jasShellPowerSum N k‖ := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax hε
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : δ < 1 / 2 := hδ ▸ abs_re_sub_half_lt_half_xiZeroCopy q₀
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 - δ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  -- the tie group
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : ℝ, φ₀ = jasShellFactor α |(q₀.1 : ℂ).im| := ⟨_, rfl⟩
  have hφ0 : 0 < φ₀ := hφ₀ ▸ jasShellFactor_pos hα1 _
  have hdecay : ∀ q ∈ {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}, 6 / φ₀ < |(q.1 : ℂ).im| →
      jasShellFactor α |(q.1 : ℂ).im| ≤ φ₀ / 2 := by
    intro q _ hq
    have hpos : 0 < |(q.1 : ℂ).im| := (by positivity : (0 : ℝ) < 6 / φ₀).trans hq
    have h1 := jasShellFactor_mul_abs_le hα0 |(q.1 : ℂ).im|
    rw [abs_abs] at h1
    have h2 : jasShellFactor α |(q.1 : ℂ).im| ≤ 3 / |(q.1 : ℂ).im| := by
      rw [le_div_iff₀ hpos]; exact h1
    have h3 : 3 / |(q.1 : ℂ).im| ≤ 3 / (6 / φ₀) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hq.le
    have h4 : 3 / (6 / φ₀) = φ₀ / 2 := by field_simp; ring
    linarith
  obtain ⟨G, f₁, f₂, hGD, hGne, -, hhalf, hf₂, hGval, hrestD⟩ :=
    exists_top_group {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}
      (fun q => jasShellFactor α |(q.1 : ℂ).im|) (q₀ := q₀) hδ.symm (hφ₀ ▸ hφ0)
      (H := 6 / φ₀) (by positivity) (by rw [← hφ₀]; exact hdecay)
  obtain ⟨qs, hqs⟩ := hGne
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = (f₁ - f₂) / 4 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = f₁ - ε' := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁, hε']; linarith
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (f₂ + ε') / c₁ := ⟨_, rfl⟩
  have hρ₂0 : 0 < ρ₂ := by rw [hρ₂]; exact div_pos (by linarith) hc₁0
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂, div_lt_one hc₁0, hc₁, hε']; linarith
  have hρc : ρ₂ * c₁ = f₂ + ε' := by rw [hρ₂]; field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; nlinarith
  -- weights
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  obtain ⟨qw, -, hqwmin⟩ :=
    G.exists_min_image (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ⟨qs, hqs⟩
  obtain ⟨wmin, hwmin⟩ : ∃ wmin : ℝ, wmin = ‖1 / ((qw.1 : ℂ) * (1 - (qw.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwmin0 : 0 < wmin := by
    rw [hwmin]
    refine norm_pos_iff.mpr (one_div_ne_zero (mul_ne_zero ?_ ?_))
    · intro h
      have := xiZeroCopy_re_pos qw
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    · intro h
      have := xiZeroCopy_re_lt_one qw
      have h' : (qw.1 : ℂ) = 1 := by linear_combination -h
      rw [h', Complex.one_re] at this
      exact lt_irrefl _ this
  have hwminG : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q hq =>
    hwmin ▸ hqwmin q hq
  have hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := fun q _ =>
    hc ▸ quarter_sub_sq_mul_norm_le_re_one_div hδ1 (hmax q)
  -- the Turán window and the constants
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2 * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 (C₂ / c₁) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hKc : C₂ / c₁ ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨M, hM⟩ := exists_turan_window G.card hρ₂0 hρ₂1 W (show 0 < c * wmin / 4 by positivity)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Real.exp 1 * G.card *
      (6 * (G.card + 1) * ((M : ℝ) + 2 * G.card + 2)) ^ G.card) := ⟨_, rfl⟩
  rw [← hD] at hM
  have hn1 : (1 : ℝ) ≤ G.card := by exact_mod_cast Finset.card_pos.mpr ⟨qs, hqs⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  -- the finite set
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = c * wmin / (4 * D) / K ^ (M + G.card) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨F, hFtail, hGF⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) ≤ T ∧ G ⊆ F := by
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (ge_mem_nhds hT0)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, G ⊆ F := eventually_ge_atTop G
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    exact ⟨F, hF1, hF2⟩
  have hW₁ : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W :=
    hW ▸ summable_inv_mul_one_sub.norm.sum_le_tsum F fun _ _ => norm_nonneg _
  have hMT : W * ρ₂ ^ (M + 1) + T * K ^ (M + G.card) ≤ c * wmin / (2 * D) := by
    have h1 : W * ρ₂ ^ (M + 1) ≤ c * wmin / (4 * D) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : T * K ^ (M + G.card) = c * wmin / (4 * D) := by
      rw [hT]; field_simp
    have h3 : c * wmin / (4 * D) + c * wmin / (4 * D) = c * wmin / (2 * D) := by field_simp; ring
    linarith
  -- tolerances
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = (f₂ + ε') / C₂ := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; exact div_pos (by linarith) hC₂0
  have hε₂C : ε₂ * C₂ ≤ f₂ + ε' := le_of_eq (by rw [hε₂]; field_simp)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = c * wmin / (2 * D) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  -- eventual conditions
  have ev1 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ →
      |‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ -
        jasShellFactor α |(q.1 : ℂ).im| * jasMainScale α N| ≤ ε' * jasMainScale α N := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    filter_upwards [eventually_abs_norm_shell_sub_le hα0 hα1 |(q.1 : ℂ).im| hε'0] with N hN _
      using hN
  have ev2 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum α (2 * N) ≤ C₂ * jasMainScale α N := by
    filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos), eventually_ge_atTop 2] with N hN hN2
    have h0 : 0 ≤ 1 / (1 - α) + 1 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (jasMainScale_two_mul_le hα0.le hN2) h0
    have e : C₂ * jasMainScale α N = (1 / (1 - α) + 1) * (2 * jasMainScale α N) := by
      rw [hC₂]; ring
    rw [e]
    linarith
  have ev4 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      jasPrimeRpowSum (1 - |(q.1 : ℂ).re - 1 / 2|) (2 * N) ≤ ε₂ * jasPrimeRpowSum α (2 * N) := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    by_cases hq : |(q.1 : ℂ).re - 1 / 2| < δ
    · filter_upwards [tendsto_two_mul_atTop.eventually (eventually_jasPrimeRpowSum_le hα1.le
        (show α < 1 - |(q.1 : ℂ).re - 1 / 2| by rw [hα]; linarith) hε₂0)] with N hN _ using hN
    · exact Eventually.of_forall fun N h => absurd h hq
  have ev5 : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε / (c₁ * jasMainScale α N) ≤ min 1 (A / 2) := by
    have hγ : 0 < δ - ε := by linarith
    have hlim := (tendsto_natLog_div_rpow_atTop hγ).const_mul (1 / c₁)
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (ge_mem_nhds
      (show (0 : ℝ) < min 1 (A / 2) from lt_min one_pos (by positivity))),
      eventually_ge_atTop 2] with N hN hN2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hN1
    have e : (N : ℝ) ^ ε / (c₁ * jasMainScale α N) =
        1 / c₁ * (Real.log N / (N : ℝ) ^ (δ - ε)) := by
      simp only [jasMainScale]
      have h1 : (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (δ - ε) * (N : ℝ) ^ ε := by
        rw [← Real.rpow_add hNpos, hα]; ring_nf
      rw [h1]
      have : 0 < (N : ℝ) ^ (δ - ε) := Real.rpow_pos_of_pos hNpos _
      have : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      field_simp
    rw [e]; exact hN
  filter_upwards [ev1, ev2, ev4, ev5, eventually_ge_atTop 2] with N h1 h2 h4 h5 hN2
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = jasMainScale α N := ⟨_, rfl⟩
  rw [← hE] at h1 h2 h5
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, P = jasPrimeWindow N (2 * N) := ⟨_, rfl⟩
  -- the large sums at distance `δ`
  have hbigD : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      ‖jasBigSum P 1 (q.1 : ℂ)‖ =
        ‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ := by
    intro q hq
    rw [norm_jasBigSum_eq, hq, show (1 : ℝ) - δ = α from hα.symm, jasWindowSum_eq_jasCpowSum, hP]
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖jasBigSum P 1 (qs.1 : ℂ)‖ := ⟨_, rfl⟩
  have hZlow : c₁ * E ≤ Z := by
    have h3 := h1 qs (hGF hqs) (hGD qs hqs)
    rw [hGval qs hqs, ← hbigD qs (hGD qs hqs), ← hZ] at h3
    have h4 := (abs_le.mp h3).1
    have e : c₁ * E = f₁ * E - ε' * E := by rw [hc₁]; ring
    linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (mul_pos hc₁0 hE0) hZlow
  have hcomp : ∀ q ∈ F, q ∉ G → ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ ρ₂ * Z := by
    intro q hqF hqG
    have hgoal : ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ (f₂ + ε') * E := by
      rcases lt_or_eq_of_le (hmax q) with hlt | hd
      · have h3 := norm_jasBigSum_le P 1 (q.1 : ℂ)
        have h6 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (1 - |(q.1 : ℂ).re - 1 / 2|)
        rw [← hP] at h6
        have h7 := h4 q hqF hlt
        have h8 : ε₂ * jasPrimeRpowSum α (2 * N) ≤ ε₂ * (C₂ * E) :=
          mul_le_mul_of_nonneg_left h2 hε₂0.le
        have h9 : ε₂ * (C₂ * E) ≤ (f₂ + ε') * E := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hε₂C hE0.le
        linarith
      · have h3 := h1 q hqF hd
        rw [← hbigD q hd] at h3
        have h6 := (abs_le.mp h3).2
        have h7 : jasShellFactor α |(q.1 : ℂ).im| * E ≤ f₂ * E :=
          mul_le_mul_of_nonneg_right (hrestD q hd hqG) hE0.le
        have e : (f₂ + ε') * E = f₂ * E + ε' * E := by ring
        linarith
    calc ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ (f₂ + ε') * E := hgoal
      _ = ρ₂ * (c₁ * E) := by rw [← hρc]; ring
      _ ≤ ρ₂ * Z := mul_le_mul_of_nonneg_left hZlow hρ₂0.le
  have htail : ∀ q : XiZeroCopy, q ∉ F → ‖jasBigSum P 1 (q.1 : ℂ)‖ ≤ K * Z := by
    intro q _
    have h3 := norm_jasBigSum_le P 1 (q.1 : ℂ)
    have h6 : ∑ p ∈ P, Real.exp (-(1 - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
        ∑ p ∈ P, Real.exp (-α * Real.log p) :=
      Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti (by rw [hα]; linarith [hmax q]) p
    have h7 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) α
    rw [← hP] at h7
    have h8 : C₂ * E ≤ K * Z := by
      have : C₂ * E = C₂ / c₁ * (c₁ * E) := by field_simp
      rw [this]
      exact mul_le_mul hKc hZlow (by positivity) (by linarith)
    linarith
  rw [hP] at hZ hcomp htail
  obtain ⟨ν, hν1, -, hν⟩ := exists_norm_tsum_pow_mul_ge
    (fun q => jasBigSum (jasPrimeWindow N (2 * N)) 1 (q.1 : ℂ)) M
    (summable_jasShellPowerSum_terms N) hGF hqs hZ hZ0 hcomp hρ₂0.le
    hρ₂1.le htail hK1 hc0 hcw hwminG hwmin0 hW₁ hFtail (by rw [← hD]; exact hMT)
  rw [← hD, ← hA] at hν
  refine ⟨ν, by omega, ?_⟩
  -- `N^{εν} ≤ (A/2)(c₁E)^ν < A Z^ν`
  have hν0 : 1 ≤ ν := by omega
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (N : ℝ) ^ ε / (c₁ * E) := ⟨_, rfl⟩
  rw [← hx] at h5
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := h5.trans (min_le_left _ _)
  have hxA : x ≤ A / 2 := h5.trans (min_le_right _ _)
  have hxν : x ^ ν ≤ A / 2 := (pow_le_of_le_one hx0 hx1 (by omega)).trans hxA
  have hNν : (N : ℝ) ^ (ε * ν) = x ^ ν * (c₁ * E) ^ ν := by
    have hcE0 : (c₁ * E) ^ ν ≠ 0 := pow_ne_zero _ (by positivity)
    rw [hx, div_pow, Real.rpow_mul (by positivity), Real.rpow_natCast]
    field_simp
  have hZν : (c₁ * E) ^ ν ≤ Z ^ ν := pow_le_pow_left₀ (by positivity) hZlow ν
  have hcE : 0 < (c₁ * E) ^ ν := pow_pos (by positivity) ν
  rw [hNν]
  calc x ^ ν * (c₁ * E) ^ ν ≤ A / 2 * (c₁ * E) ^ ν := mul_le_mul_of_nonneg_right hxν hcE.le
    _ < A * (c₁ * E) ^ ν := by have := mul_pos hA0 hcE; linarith
    _ ≤ A * Z ^ ν := mul_le_mul_of_nonneg_left hZν hA0.le
    _ ≤ ‖jasShellPowerSum N ν‖ := hν

/-! ## Capstones -/

/-- **RH ⟺ the zeros approach the line ∧ subexponential growth of the shell power sums.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_shellPowerSum_growth :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellPowerSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH
    refine ⟨zerosApproachLine_of_riemannHypothesis hRH, fun ε hε => ?_⟩
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
      ⟨_, rfl⟩
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    refine ((hlim.eventually (eventually_ge_atTop W)).and (eventually_ge_atTop 1)).frequently.mono
      fun N ⟨hN, hN1⟩ k hk => ?_
    refine (norm_jasShellPowerSum_le_of_riemannHypothesis hRH N k).trans ?_
    rw [← hW]
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    refine hN.trans (Real.rpow_le_rpow_of_exponent_le hN1' ?_)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  · rintro ⟨hZ, hfr⟩
    by_contra hRH
    obtain ⟨Θ, hΘ, q₀, hq₀, hmaxq⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have habs : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := fun q => by
      rw [LindelofSparse.spectral_im_eq, abs_sub_comm]
    have hq₀' : |(q₀.1 : ℂ).re - 1 / 2| = Θ := by rw [← habs]; exact hq₀
    have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₀'; linarith
    have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := fun q => by
      rw [hq₀', ← habs]; exact hmaxq q
    have hev := eventually_exists_large_shellPowerSum_of_maximal_offLine q₀ hoff hmax
      (ε := Θ / 2) (by rw [hq₀']; linarith)
    obtain ⟨N, hN, k, hk, hlt⟩ := ((hfr (Θ / 2) (by linarith)).and_eventually hev).exists
    exact absurd (hN k hk) (not_le.mpr hlt)

/-- **RH ⟺ no off-line chain ∧ subexponential growth of the shell power sums.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_shellPowerSum_growth :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellPowerSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH
    exact ⟨fun ⟨⟨q, hq⟩, _⟩ => hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q),
      (riemannHypothesis_iff_zerosApproachLine_and_shellPowerSum_growth.mp hRH).2⟩
  · rintro ⟨hno, hfr⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    have hnot : ¬ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
        ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| :=
      fun h => hno ⟨⟨q₁, ne_of_gt hq₁⟩, h⟩
    push Not at hnot
    obtain ⟨q₀, hoff, hmax⟩ := hnot
    have hδ0 : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    have hev := eventually_exists_large_shellPowerSum_of_maximal_offLine q₀ hoff hmax
      (ε := |(q₀.1 : ℂ).re - 1 / 2| / 2) (by linarith)
    obtain ⟨N, hN, k, hk, hlt⟩ :=
      ((hfr (|(q₀.1 : ℂ).re - 1 / 2| / 2) (by linarith)).and_eventually hev).exists
    exact absurd (hN k hk) (not_le.mpr hlt)

end

end RHTower
