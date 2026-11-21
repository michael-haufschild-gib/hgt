import GaloisForLFunctions.ArtinMertens.TheTwistedVonMangoldtSeriesConvergesAtOne
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.WindowedLandauTheory.PeriodIntegrals.ExplicitFormula
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Analytic

/-! The normalized Cesàro sum is the tail integral of the Chebyshev error. -/

open Finset Filter Topology MeasureTheory WindowedLandauTheory.HC
open ArithmeticFunction (vonMangoldt)

namespace QH

section abel

variable {𝕜 : Type*} [RCLike 𝕜]

private lemma hasDerivAt_inv_coe (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => ((u : 𝕜))⁻¹) (-((t : 𝕜) ^ 2)⁻¹) t := by
  have h := (RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inv ht)
  have hfun : (fun u : ℝ => ((u : 𝕜))⁻¹) = (RCLike.ofRealCLM (K := 𝕜)) ∘ fun y : ℝ => y⁻¹ := by
    funext u
    simp
  rw [hfun]
  exact h.congr_deriv (by simp)

private lemma Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

private theorem continuousOn_inv_sq_Icc_of_pos {y U : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) := by
  refine ContinuousOn.inv₀ ((RCLike.continuous_ofReal (K := 𝕜)).pow 2).continuousOn ?_
  intro t ht
  have : (t : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
  exact pow_ne_zero 2 this

private lemma integrableOn_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2) (Set.Icc y U) := by
  have hg : IntegrableOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) :=
    (continuousOn_inv_sq_Icc_of_pos (by linarith)).integrableOn_Icc
  have := integrableOn_mul_sum_Icc c (m := 1) (by linarith : (0 : ℝ) ≤ y) hg
  refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [div_eq_inv_mul]

private theorem sum_Icc_zero_ite_eq_sum_Icc_one (c : ℕ → 𝕜) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then (0 : 𝕜) else c k) = ∑ k ∈ Icc 1 N, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, Icc_one_eq_Ioc_zero]
  simp only [↓reduceIte, zero_add]
  exact Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_Ioc.mp hk).1.ne'

private lemma integral_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : 𝕜) + (∑ n ∈ Icc 1 ⌊y⌋₊, c n) / (y : 𝕜) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => (show (0 : ℝ) < t by linarith [ht.1]).ne'
  have hf_diff : ∀ t ∈ Set.Icc y U, DifferentiableAt ℝ (fun u : ℝ => ((u : 𝕜))⁻¹) t :=
    fun t ht => (hasDerivAt_inv_coe t (hne t ht)).differentiableAt
  have hf_int : IntegrableOn (deriv (fun u : ℝ => ((u : 𝕜))⁻¹)) (Set.Icc y U) := by
    refine ((continuousOn_inv_sq_Icc_of_pos (𝕜 := 𝕜) (U := U) (by linarith)).neg.integrableOn_Icc).congr_fun
      (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_inv_coe t (hne t ht)).deriv).symm
  have key : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      ((U : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊U⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ((y : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊y⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
            ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) :=
    sum_mul_eq_sub_sub_integral_mul (fun n => if n = 0 then (0 : 𝕜) else c n) hy0 hU hf_diff hf_int
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜)) := by
    calc ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k)
        = ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, c k / (k : 𝕜) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk0 : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'
          rw [if_neg hk0, RCLike.ofReal_natCast]
          ring
      _ = _ := by
          rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero]
          exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hU))
  have hint_r : ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) =
      -∫ t in Set.Ioc y U, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / (t : 𝕜) ^ 2 := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
    simp only [(hasDerivAt_inv_coe (𝕜 := 𝕜) t ht0).deriv, sum_Icc_zero_ite_eq_sum_Icc_one]
    ring
  rw [intervalIntegral.integral_of_le hU]
  linear_combination -key + hL + hint_r - ((U : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊U⌋₊
    + ((y : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊y⌋₊

end abel

private theorem integral_psumR_sub_div_sq_eq_partial_sums (a : ℕ → ℝ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, ((∑ n ∈ Icc 1 ⌊u⌋₊, a n) - u) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y
        - (Real.log U - Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hU0 : 0 < U := by linarith
  have hsplit : (fun u : ℝ => ((∑ n ∈ Icc 1 ⌊u⌋₊, a n) - u) / u ^ 2) =
      fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 - u⁻¹ := by
    funext u
    rw [sub_div]
    congr 1
    rcases eq_or_ne u 0 with h | h
    · simp [h]
    · rw [pow_two, div_mul_eq_div_div, div_self h, one_div]
  have hA : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2) volume y U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr
      (integrableOn_partial_sum_div_sq (𝕜 := ℝ) a hy)
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume y U := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)
    rw [Set.uIcc_of_le hU] at hx
    exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
  have hA_eq : ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y :=
    integral_partial_sum_div_sq (𝕜 := ℝ) a hy hU
  rw [hsplit, intervalIntegral.integral_sub hA hinv, integral_inv_of_pos hy0 hU0,
    Real.log_div hU0.ne' hy0.ne', hA_eq]

private theorem ramp_eq {y : ℝ} (hy : 1 ≤ y) {n : ℕ} (hn : n ∈ Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨hn1, hny⟩ := mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hc : (n : ℝ) ≤ (⌊y⌋₊ : ℕ) := by exact_mod_cast hny
  exact max_eq_left (sub_nonneg.mpr ((le_div_iff₀ hn0).mpr
    (by simpa using hc.trans (Nat.floor_le (zero_le_one.trans hy)))))

private theorem G_integral (y : ℝ) (hy : 1 ≤ y) :
    An.G y = -y * ∫ u in Set.Ioi y, RHTower.chebyshevError u / u ^ 2 := by
  let S (u : ℝ) := ∑ n ∈ Icc 1 ⌊u⌋₊, vonMangoldt n / (n : ℝ)
  let P (u : ℝ) := ∑ n ∈ Icc 1 ⌊u⌋₊, vonMangoldt n
  have hS (u : ℝ) : (∑ n ∈ Icc 0 ⌊u⌋₊, vonMangoldt n / (n : ℝ)) = S u := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _), ← Icc_one_eq_Ioc_zero]
    simp [S]
  have hP (u : ℝ) : Chebyshev.psi u = P u := by
    rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _),
      ← Icc_one_eq_Ioc_zero]
    simp [P]
  have hs : Tendsto (fun u : ℝ => S u - Real.log u) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) :=
    RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.congr (fun u => by rw [hS u])
  have hp : Tendsto (fun u : ℝ => P u / u) atTop (𝓝 1) := by
    simpa only [zero_add] using
      (RHTower.tendsto_chebyshevError_div.add_const (1 : ℝ)).congr'
      (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
        change RHTower.chebyshevError u / u + 1 = P u / u
        rw [RHTower.chebyshevError, hP, sub_div, div_self hu.ne', sub_add_cancel])
  let I := -Real.eulerMascheroniConstant - 1 - S y + P y / y + Real.log y
  have hl : Tendsto (fun U : ℝ => ∫ u in y..U, RHTower.chebyshevError u / u ^ 2)
      atTop (𝓝 I) := by
    refine ((((hs.sub hp).sub_const (S y)).add_const (P y / y)).add_const
      (Real.log y)).congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    simp_rw [RHTower.chebyshevError, hP]
    rw [integral_psumR_sub_div_sq_eq_partial_sums vonMangoldt hy hU]
    simp only [S, P]
    ring
  have hi := RHTower.integrableOn_chebyshevError_div_sq.mono_set (Set.Ioi_subset_Ioi hy)
  have hI := tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi y hi tendsto_id) hl
  have hsum : (∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n * max (y / n - 1) 0) =
      y * S y - P y := by
    rw [S, P, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun n hn => by rw [ramp_eq hy hn]; ring
  unfold An.G An.abelian₂
  rw [hsum, hI, I]
  have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
  field_simp <;> ring

theorem g_integral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (y : ℝ) (hy : 1 ≤ y)
    (hi : IntegrableOn (fun u : ℝ => PI.psi0 χ u / (u : ℂ) ^ 2) (Set.Ioi y)) :
    An.gChi χ y = -(y : ℂ) * ∫ u in Set.Ioi y, PI.psi0 χ u / (u : ℂ) ^ 2 := by
  by_cases hχ : χ = 1
  · have hN : N = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    subst N
    have hψ (u : ℝ) : PI.psi0 χ u = (RHTower.chebyshevError u : ℂ) := by
      have hone (n : ℕ) : χ (n : ZMod 1) = 1 := hχ ▸ MulChar.one_apply (isUnit_of_subsingleton _)
      simp only [PI.psi0, if_pos hχ, hone, mul_one, RHTower.chebyshevError, Chebyshev.psi_eq_sum_Icc]
      push_cast
      rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _), ← Icc_one_eq_Ioc_zero]
      simp
    simp only [An.gChi, if_pos hχ, hψ]
    have hfun : (fun u : ℝ => (RHTower.chebyshevError u : ℂ) / (u : ℂ) ^ 2) =
        fun u => ((RHTower.chebyshevError u / u ^ 2 : ℝ) : ℂ) := by
      funext u
      push_cast <;> rfl
    rw [hfun, set_integral_ofReal, G_integral y hy]
    push_cast
    ring
  · let c (n : ℕ) := χ n * (vonMangoldt n : ℂ)
    let S (u : ℝ) := ∑ n ∈ Icc 1 ⌊u⌋₊, c n / (n : ℂ)
    let P (u : ℝ) := ∑ n ∈ Icc 1 ⌊u⌋₊, c n
    let I := -An.logDerivativeAtOne χ - S y + P y / (y : ℂ)
    have hψ (u : ℝ) : PI.psi0 χ u = P u := by
      simp only [PI.psi0, if_neg hχ, sub_zero, P, c]
      exact sum_congr rfl fun n _ => mul_comm _ _
    have hs : Tendsto S atTop (𝓝 (-An.logDerivativeAtOne χ)) := by
      simpa only [S, c, An.logDerivativeAtOne, neg_div] using
        GaloisForLFunctions.ArtinMertens.tendsto_sum_twist_vonMangoldt_div χ hχ
    have hP : Tendsto (fun u : ℝ => P u / (u : ℂ)) atTop (𝓝 0) :=
      GaloisForLFunctions.ArtinMertens.tendsto_twistPsi_div χ hχ
    have ht : Tendsto (fun U : ℝ => ∫ u in y..U, PI.psi0 χ u / (u : ℂ) ^ 2) atTop (𝓝 I) := by
      have h := (((hs.sub_const (S y)).sub hP).add_const (P y / (y : ℂ)))
      simp only [sub_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop y] with U hU
      simp_rw [hψ]
      exact (integral_partial_sum_div_sq c hy hU).symm
    have hz := tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi y hi tendsto_id) ht
    have hsum : An.sumLamChi χ y = (y : ℂ) * S y - P y := by
      rw [An.sumLamChi, S, P, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun n hn => ?_
      rw [ramp_eq hy hn]
      simp only [An.abelian₂, c]
      push_cast
      ring
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hy).ne'
    rw [An.gChi, if_neg hχ, hsum, hz, I]
    field_simp <;> ring

end QH

