import GaloisForLFunctions.RHTower.ExponentialTuplesAndAnalyticMembershipInPrimeSpan
import GaloisForLFunctions.RHTower.PhasedEulerProductsApproximateExponentialsOfHardyFunctions

/-!
# Phased Euler products approximate exponentials of Hardy tuples on finitely many discs at once

Fix finitely many discs `|s − z i| < ρ i`, `i : ι`, with a common floor `σ₁ ≤ Re (z i) − ρ i`,
`σ₁ > 1/2`, and `Re (z i) + ρ i ≤ b < 1`.  For a tuple `L` of the closed span of the prime tuples
(`primeSpan`), every `r₁ < 1`, `ε > 0` and `y₀'`, there are `y ≥ y₀'` and *one* family of
unimodular phases `ω` with

  `‖exp (L_i(q)) − ∏_{p ≤ y} (1 − ω_p p^{−(z i + ρ i q)})^{−1}‖ < ε`  for all `i` and `|q| ≤ r₁`

(`exists_unimodular_eulerProduct_approx_exp_tuple`).  The proof is the single-disc argument run
componentwise: the Euler product is `exp` of the linear prime sum plus the remainders; the
remainders of the primes up to a cutoff `y₀` form the tuple of a function analytic on `Re s > 0`,
hence a tuple of `primeSpan`; the joint Pechersky approximation with the first `y₀` phases equal to
one makes the linear sum close to `L` minus that head remainder in every component at once; the
remainders beyond `y₀` are small by the tail majorant.
-/

open Complex Filter Topology Finset Metric
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-- The remainder of the primes up to `y₀` with all phases one, as a function of `s`. -/
def eulerHeadRemainderFun (y₀ : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ (range (y₀ + 1)).filter Nat.Prime, eulerLogRemainder 1 s n

theorem eulerHeadRemainderFun_apply (y₀ : ℕ) (z₀ : ℂ) (ρ : ℝ) (q : ℂ) :
    eulerHeadRemainderFun y₀ (z₀ + ρ * q) = eulerHeadRemainder z₀ ρ y₀ q := rfl

/-- The head remainder is analytic on `Re s > 0`. -/
theorem differentiableOn_eulerHeadRemainderFun (y₀ : ℕ) {U : Set ℂ} (hU : ∀ s ∈ U, 0 < s.re) :
    DifferentiableOn ℂ (eulerHeadRemainderFun y₀) U := by
  have hfun : eulerHeadRemainderFun y₀ = fun s =>
      ∑ n ∈ (range (y₀ + 1)).filter Nat.Prime, eulerLogRemainder 1 s n := rfl
  rw [hfun]
  refine DifferentiableOn.fun_sum fun n hn => ?_
  have hn2 : 2 ≤ n := (mem_filter.mp hn).2.two_le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcpow : DifferentiableOn ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) U :=
    differentiableOn_id.neg.const_cpow (Or.inl hn0)
  have hlin : DifferentiableOn ℂ (fun s : ℂ => 1 * (n : ℂ) ^ (-s)) U :=
    (differentiableOn_const _).mul hcpow
  have hlog : DifferentiableOn ℂ (fun s : ℂ => Complex.log (1 - 1 * (n : ℂ) ^ (-s))) U := by
    refine ((differentiableOn_const _).sub hlin).clog fun s hs => ?_
    exact one_sub_phase_cpow_mem_slitPlane (by simp) hn2 (hU s hs) le_rfl
  exact hlog.neg.sub hlin

/-- **Phased Euler products approximate the exponentials of a tuple of `primeSpan` on all the
discs at once.**  With `σ₁ ≤ Re (z i) − ρ i`, `σ₁ > 1/2`, `Re (z i) + ρ i ≤ b < 1`, `R > 1` and
`ρ i R < Re (z i)`: for `L ∈ primeSpan`, `r₁ < 1`, `ε > 0`, `y₀'` there are `y ≥ y₀'` and
unimodular phases `ω` with
`‖exp(L_i(q)) − ∏_{p ≤ y} (1 − ω_p p^{−(z i + ρ i q)})^{−1}‖ < ε` for all `i` and `|q| ≤ r₁`. -/
theorem exists_unimodular_eulerProduct_approx_exp_tuple (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) {σ₁ : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁le : ∀ i, σ₁ ≤ (z i).re - ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1)
    {R : ℝ} (hR : 1 < R) (hρR : ∀ i, ρ i * R < (z i).re)
    {L : DiscTuple ι} (hL : L ∈ primeSpan z (fun i => (hρ i).le))
    {r₁ : ℝ} (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) {ε : ℝ} (hε : 0 < ε) (y₀' : ℕ) :
    ∃ y : ℕ, y₀' ≤ y ∧ ∃ ω : ℕ → ℂ, (∀ n, ‖ω n‖ = 1) ∧ ∀ i, ∀ q : ℂ, ‖q‖ ≤ r₁ →
      ‖Complex.exp (hardyFun (L i) q) - ∏ n ∈ (range (y + 1)).filter Nat.Prime,
          (1 - ω n * (n : ℂ) ^ (-(z i + ρ i * q)))⁻¹‖ < ε := by
  have hρ' : ∀ i, 0 ≤ ρ i := fun i => (hρ i).le
  have hρσ : ∀ i, 2 * ρ i - 2 * (z i).re < -1 := fun i => by linarith [hσ₁le i]
  have hσ₁pos : 0 < σ₁ := by linarith
  -- the constants
  set K : ℝ := Real.sqrt ((1 - r₁ ^ 2)⁻¹) with hK
  have hKpos : 0 < K := by
    rw [hK]
    apply Real.sqrt_pos.mpr
    apply inv_pos.mpr
    nlinarith
  set M : ℝ := K * ‖L‖ with hM
  set δ : ℝ := min 1 (ε / (4 * Real.exp M)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (4 * Real.exp M) := min_le_right _ _
  set C₁ : ℝ := (1 - (2 : ℝ) ^ (-σ₁))⁻¹ / 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have := two_rpow_neg_lt_one hσ₁pos
    rw [hC₁]
    have h0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-σ₁))⁻¹ := inv_nonneg.mpr (by linarith)
    positivity
  -- the cutoff beyond which the remainder tail is small
  obtain ⟨y₀, hy₀', htail⟩ := exists_remainder_tail_le hσ₁ hC₁0 (by positivity : 0 < δ / 3) y₀'
  -- the head remainder tuple lies in the closed span
  obtain ⟨c₀, R₀, hsub, hre⟩ := exists_ball_re_gt_of_forall_lt z (r := fun i => ρ i * R) (α := 0)
    (fun i => by linarith [hρR i])
  have hFdiff : DifferentiableOn ℂ (eulerHeadRemainderFun y₀) (ball c₀ R₀) :=
    differentiableOn_eulerHeadRemainderFun y₀ fun s hs => hre s (ball_subset_closedBall hs)
  obtain ⟨R₀v, hR₀mem, hR₀fun⟩ :=
    exists_mem_primeSpan_of_differentiableOn_ball z hρ' hb hb1 hR hsub hFdiff
  -- the joint Pechersky approximation with the first phases equal to one
  obtain ⟨N, hN, ω, hω, hωone, hclose⟩ := exists_unimodular_primeTuple_sum_approx_extend z hρ'
    hρσ hb hb1 (Submodule.sub_mem _ hL hR₀mem) (by positivity : (0 : ℝ) < δ / 3 / K) (y₀ + 1)
    (fun _ => 1) (fun _ => by simp)
  refine ⟨N - 1, by omega, ω, hω, fun i q hq => ?_⟩
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1]
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq hr₁
  set zq : ℂ := z i + ρ i * q with hzq
  have hzre : σ₁ ≤ zq.re := by
    have := re_center_add_le (z₀ := z i) (R := 1) (hρ' i) hq1.le
    rw [hzq]
    linarith [hσ₁le i]
  -- the Euler product is the exponential of the logarithmic sum
  set S : Finset ℕ := (range N).filter Nat.Prime with hS
  have hprod : ∏ n ∈ S, (1 - ω n * (n : ℂ) ^ (-zq))⁻¹
      = Complex.exp (∑ n ∈ S, -Complex.log (1 - ω n * (n : ℂ) ^ (-zq))) :=
    prod_inv_one_sub_eq_exp_sum fun n hn =>
      one_sub_phase_cpow_ne_zero_nat (hω n) (mem_filter.mp hn).2.two_le hσ₁pos hzre
  rw [hprod, sum_neg_log_eq_sum_add_remainder]
  -- the linear sum is the `i`-th disc function of the Pechersky sum
  have hlin : ∑ n ∈ S, ω n * (n : ℂ) ^ (-zq)
      = hardyFun ((∑ n ∈ range N, ω n • primeTuple z hρ' n) i) q := by
    rw [WithLp.ofLp_sum, Finset.sum_apply, hardyFun_sum_apply _ _ hq1, hS, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    rw [PiLp.smul_apply, hardyFun_smul _ _ hq1, primeTuple_apply, hardyFun_primeTerm _ _ n hq1,
      mul_ite, mul_zero]
  -- the remainder splits into the fixed head and a small tail
  have hrem : ∑ n ∈ S, eulerLogRemainder (ω n) zq n
      = hardyFun (R₀v i) q
        + ∑ n ∈ Finset.Ico (y₀ + 1) N, if n.Prime then eulerLogRemainder (ω n) zq n else 0 := by
    rw [hR₀fun i q hq1, eulerHeadRemainderFun, hS, sum_filter, ← Finset.sum_range_add_sum_Ico _ hN,
      sum_filter]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [hωone n (mem_range.mp hn)]
  have htailq : ‖∑ n ∈ Finset.Ico (y₀ + 1) N,
      if n.Prime then eulerLogRemainder (ω n) zq n else 0‖ ≤ δ / 3 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n _ => ?_).trans (htail N))
    split_ifs with hn
    · exact norm_eulerLogRemainder_le (hω n) hn.two_le hσ₁pos hzre
    · rw [norm_zero]
      positivity
  -- the logarithmic sum is within `δ` of `L_i(q)`
  have hdiff : ‖hardyFun (L i) q - (∑ n ∈ S, ω n * (n : ℂ) ^ (-zq)
      + ∑ n ∈ S, eulerLogRemainder (ω n) zq n)‖ ≤ δ := by
    rw [hlin, hrem]
    have hker : hardyFun (L i) q - (hardyFun ((∑ n ∈ range N, ω n • primeTuple z hρ' n) i) q
        + (hardyFun (R₀v i) q + ∑ n ∈ Finset.Ico (y₀ + 1) N,
          if n.Prime then eulerLogRemainder (ω n) zq n else 0))
        = hardyFun ((L - R₀v - ∑ n ∈ range N, ω n • primeTuple z hρ' n) i) q
          - ∑ n ∈ Finset.Ico (y₀ + 1) N,
            if n.Prime then eulerLogRemainder (ω n) zq n else 0 := by
      rw [PiLp.sub_apply, PiLp.sub_apply, hardyFun_sub_apply _ _ hq1, hardyFun_sub_apply _ _ hq1]
      ring
    rw [hker]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖hardyFun ((L - R₀v - ∑ n ∈ range N, ω n • primeTuple z hρ' n) i) q‖ ≤ δ / 3 := by
      have hb := norm_hardyFun_le_of_norm_le ((L - R₀v - ∑ n ∈ range N, ω n • primeTuple z hρ' n) i)
        hr₁0 hr₁ hq
      rw [← hK] at hb
      calc _ ≤ K * ‖(L - R₀v - ∑ n ∈ range N, ω n • primeTuple z hρ' n) i‖ := hb
        _ ≤ K * ‖L - R₀v - ∑ n ∈ range N, ω n • primeTuple z hρ' n‖ := by
            gcongr
            exact PiLp.norm_apply_le _ i
        _ ≤ K * (δ / 3 / K) := by gcongr
        _ = δ / 3 := by field_simp
    linarith
  -- the exponential step
  have hML : ‖hardyFun (L i) q‖ ≤ M := by
    rw [hM, hK]
    refine (norm_hardyFun_le_of_norm_le (L i) hr₁0 hr₁ hq).trans ?_
    gcongr
    exact PiLp.norm_apply_le _ i
  have hexpM : Real.exp ‖hardyFun (L i) q‖ ≤ Real.exp M := Real.exp_le_exp.mpr hML
  rw [norm_sub_rev]
  calc ‖Complex.exp (∑ n ∈ S, ω n * (n : ℂ) ^ (-zq) + ∑ n ∈ S, eulerLogRemainder (ω n) zq n)
        - Complex.exp (hardyFun (L i) q)‖
      ≤ 2 * Real.exp ‖hardyFun (L i) q‖ * ‖(∑ n ∈ S, ω n * (n : ℂ) ^ (-zq)
          + ∑ n ∈ S, eulerLogRemainder (ω n) zq n) - hardyFun (L i) q‖ := by
        refine norm_cexp_sub_cexp_le_of_norm_sub_le_one ?_
        rw [norm_sub_rev]
        exact hdiff.trans hδ1
    _ ≤ 2 * Real.exp M * δ := by
        rw [norm_sub_rev]
        gcongr
    _ ≤ 2 * Real.exp M * (ε / (4 * Real.exp M)) := by gcongr
    _ = ε / 2 := by
        field_simp
        ring
    _ < ε := by linarith

end RHTower
