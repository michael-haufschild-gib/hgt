import GaloisForLFunctions.RHTower.ChronologicalTailNormals
import GaloisForLFunctions.RHTower.ChronologicalHeatMellin

/-!
# The observation inequality for a proportional Möbius prefix

For `0 < θ < 1`, `N ≥ 1` and a tail profile `f`, the proportional prefix array is
`a_k = μ(k)` for `k ≤ θN` and `a_k = f(k/N)` for `θN < k ≤ N`, with actual residual
`r_{N,f}(t) = e^{-t} + Σ_{k ≤ N} a_k h(kt)`.

Rescaling `t = u/N` splits `r_{N,f}(u/N)` on `[1, 2]` into the target `e^{-u/N}`, the Möbius head
`Σ_{k ≤ θN} μ(k) h(ku/N)` and `N` times the discrete tail vector of `f`.  If `f` agrees on
`[θ, 1]` with `Σ cᵢ gᵢ` and `ψ_N` is a unit vector orthogonal to the discrete tails of the `gᵢ`,
pairing with `ψ_N` annihilates the tail exactly, whatever the size of the coefficients, and gives

  `|⟪ψ_N, head⟫| ≤ √N ‖r_{N,f}‖_{L²(0,∞)} + 1`,

using `∫₁² r(u/N)² du = N ∫_{1/N}^{2/N} r² ≤ N ‖r‖²`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology ComplexConjugate Moebius
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-- The proportional Möbius-prefix array: `μ(k)` for `k ≤ θN`, and tail samples `f(k/N)` above. -/
def prefixTailArray (θ : ℝ) (f : ℝ → ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  if (k : ℝ) ≤ θ * N then (μ k : ℝ) else f (k / N)

/-- The rescaled Möbius head `u ↦ Σ_{k ≤ θN} μ(k) h(ku/N)`. -/
def headFun (θ : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ioc 0 N,
    if (k : ℝ) ≤ θ * N then (μ k : ℂ) * ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0

theorem memLp_headFun (θ : ℝ) (N : ℕ) : MemLp (headFun θ N) 2 sampleMeasure := by
  have hterm : ∀ k : ℕ, MemLp (fun u : ℝ => if (k : ℝ) ≤ θ * N then (μ k : ℂ) *
      ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0) 2 sampleMeasure := by
    intro k
    by_cases hk : (k : ℝ) ≤ θ * N
    · simp only [hk, if_true]
      exact (memLp_sample_bose _).const_mul _
    · simp only [hk, if_false]
      exact MemLp.zero'
  exact memLp_finsetSum (Finset.Ioc 0 N) fun k _ => hterm k

/-- The head has norm at most `N` in `L²([1, 2])`. -/
theorem norm_toSample_headFun_le (θ : ℝ) (N : ℕ) : ‖toSample (headFun θ N)‖ ≤ N := by
  refine norm_toSample_le (Nat.cast_nonneg N) fun u _ => ?_
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Ioc 0 N, ‖if (k : ℝ) ≤ θ * N then (μ k : ℂ) *
        ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0‖
      ≤ ∑ _k ∈ Finset.Ioc 0 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        split_ifs
        · rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fusionBoseDefect_bounds _).1]
          have hμ : |((μ k : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
          exact (mul_le_mul hμ (fusionBoseDefect_bounds _).2.1 (fusionBoseDefect_bounds _).1
            zero_le_one).trans_eq (one_mul 1)
        · rw [norm_zero]; exact zero_le_one
    _ = N := by rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one]

/-! ### The rescaled residual -/

/-- **Rescaled `L²` bound.**  `‖u ↦ r(u/N)‖_{L²[1,2]} ≤ √N ‖r‖_{L²(0,∞)}`. -/
theorem norm_toSample_rescale_le {r : ℝ → ℝ} (hc : ContinuousOn r (Ioi 0))
    (hr : MemLp r 2 chronologicalPositiveVolume) {N : ℕ} (hN : 0 < N) :
    ‖toSample fun u : ℝ => ((r (u / N) : ℝ) : ℂ)‖ ≤ Real.sqrt N * chronologicalL2Norm r := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcu : ContinuousOn (fun u : ℝ => ((r (u / N) : ℝ) : ℂ)) (Icc 1 2) :=
    Complex.continuous_ofReal.comp_continuousOn
      (hc.comp (continuousOn_id.div_const _) fun u hu =>
        div_pos (lt_of_lt_of_le one_pos hu.1) hNpos)
  have hm := memLp_sample_of_continuousOn hcu
  have hsq : ‖toSample fun u : ℝ => ((r (u / N) : ℝ) : ℂ)‖ ^ 2 =
      ∫ u in Icc (1 : ℝ) 2, r (u / N) ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toSample hm hm]
    have : ∀ u : ℝ, conj ((r (u / N) : ℝ) : ℂ) * ((r (u / N) : ℝ) : ℂ) =
        ((r (u / N) ^ 2 : ℝ) : ℂ) := fun u => by rw [Complex.conj_ofReal]; push_cast; ring
    simp only [this, integral_complex_ofReal]
    exact Complex.ofReal_re _
  have hint : Integrable (fun t => r t ^ 2) chronologicalPositiveVolume := hr.integrable_sq
  have hsub : ∫ u in Icc (1 : ℝ) 2, r (u / N) ^ 2 ≤ N * ∫ t in Ioi (0 : ℝ), r t ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le one_le_two,
      intervalIntegral.integral_comp_div (fun t => r t ^ 2) hNpos.ne', smul_eq_mul,
      intervalIntegral.integral_of_le (div_le_div_of_nonneg_right one_le_two hNpos.le)]
    refine mul_le_mul_of_nonneg_left ?_ hNpos.le
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards with t using sq_nonneg _
    · exact Eventually.of_forall fun t ht => (div_pos one_pos hNpos).trans ht.1
  rw [chronologicalL2Norm_eq_sqrt hr.aestronglyMeasurable, ← Real.sqrt_mul hNpos.le,
    ← Real.sqrt_sq (norm_nonneg _), hsq]
  exact Real.sqrt_le_sqrt hsub

/-- **The rescaled residual splits into target, head and tail.** -/
theorem heatError_rescale_eq {θ : ℝ} {l : ℕ} {g : Fin l → ℝ → ℝ} {f : ℝ → ℝ}
    {c : Fin l → ℝ} (hf : ∀ x ∈ Icc θ 1, f x = ∑ i, c i * g i x) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ) =
      ((Real.exp (-(u / N)) : ℝ) : ℂ) + headFun θ N u +
        (N : ℂ) * ∑ i, (c i : ℂ) * tailSampleFun θ N (g i) u := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set hk : ℕ → ℂ := fun k => ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) with hhk
  have hterm : ∀ k ∈ Finset.Ioc 0 N,
      ((prefixTailArray θ f N k * fusionBoseDefect (k * (u / N)) : ℝ) : ℂ) =
        (if (k : ℝ) ≤ θ * N then (μ k : ℂ) * hk k else 0) +
          ∑ i, (c i : ℂ) * (if θ * N < k then (g i (k / N) : ℂ) * hk k else 0) := by
    intro k hk'
    have harg : (k : ℝ) * (u / N) = k / N * u := by ring
    rw [harg]
    by_cases hkθ : (k : ℝ) ≤ θ * N
    · have hnot : ¬ θ * N < k := not_lt.mpr hkθ
      simp only [prefixTailArray, hkθ, hnot, if_true, if_false, mul_zero, Finset.sum_const_zero,
        add_zero, hhk]
      push_cast; ring
    · have hlt : θ * N < k := lt_of_not_ge hkθ
      have hmem : (k : ℝ) / N ∈ Icc θ 1 := by
        refine ⟨(le_div_iff₀ hNpos).mpr hlt.le, (div_le_one hNpos).mpr ?_⟩
        exact_mod_cast (Finset.mem_Ioc.mp hk').2
      simp only [prefixTailArray, hkθ, hlt, if_true, if_false, zero_add, hhk, hf _ hmem]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
  simp only [chronologicalHeatError]
  rw [Complex.ofReal_add, Complex.ofReal_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    add_assoc]
  congr 2
  simp only [tailSampleFun, tailSampleSum, hhk]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, mul_left_comm (N : ℂ), ← mul_assoc (N : ℂ), mul_one_div_cancel hN0,
    one_mul]

/-- **The observation inequality.**  A unit vector annihilating the discrete tails of `g₁, …, g_l`
observes the Möbius head through the actual residual of every tail `f ≡ Σ cᵢ gᵢ` on `[θ, 1]`. -/
theorem norm_inner_headFun_le {θ : ℝ} {l : ℕ} {g : Fin l → ℝ → ℝ} {N : ℕ}
    (hN : 0 < N) {ψN : SampleSpace} (hψN1 : ‖ψN‖ = 1)
    (hψN : ∀ i, (inner ℂ ψN (tailSampleVec θ N (g i)) : ℂ) = 0) {f : ℝ → ℝ} {c : Fin l → ℝ}
    (hf : ∀ x ∈ Icc θ 1, f x = ∑ i, c i * g i x) :
    ‖(inner ℂ ψN (toSample (headFun θ N)) : ℂ)‖ ≤
      Real.sqrt N * chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) + 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set E : ℝ → ℂ := fun u => ((Real.exp (-(u / N)) : ℝ) : ℂ) with hE
  have hEm : MemLp E 2 sampleMeasure :=
    memLp_sample_of_continuousOn (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_id.div_const _).neg)).continuousOn
  have hEn : ‖toSample E‖ ≤ 1 := norm_toSample_le zero_le_one fun u hu => by
    rw [hE, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (by linarith [hu.1]) hNpos.le))
  have hTm : ∀ i, MemLp (tailSampleFun θ N (g i)) 2 sampleMeasure := fun i =>
    memLp_tailSampleFun θ N (g i)
  have hsplit : toSample (fun u : ℝ =>
      ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ)) =
      toSample E + toSample (headFun θ N) +
        (N : ℂ) • ∑ i, (c i : ℂ) • tailSampleVec θ N (g i) := by
    have hfun : (fun u : ℝ => ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ))
        = E + headFun θ N + (N : ℂ) • ∑ i, (c i : ℂ) • tailSampleFun θ N (g i) := by
      funext u
      rw [heatError_rescale_eq hf hN u]
      simp [hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hsum : MemLp (∑ i, (c i : ℂ) • tailSampleFun θ N (g i)) 2 sampleMeasure :=
      memLp_finsetSum' _ fun i _ => (hTm i).const_smul _
    rw [hfun, toSample_add (hEm.add (memLp_headFun θ N)) (hsum.const_smul _),
      toSample_add hEm (memLp_headFun θ N), toSample_smul _ hsum,
      toSample_sum _ fun i _ => (hTm i).const_smul _]
    simp only [tailSampleVec, toSample_smul _ (hTm _)]
  have hzero : (inner ℂ ψN ((N : ℂ) • ∑ i, (c i : ℂ) • tailSampleVec θ N (g i)) : ℂ) = 0 := by
    rw [inner_smul_right, inner_sum]
    simp only [inner_smul_right, hψN, mul_zero, Finset.sum_const_zero]
  have hid : (inner ℂ ψN (toSample (headFun θ N)) : ℂ) =
      inner ℂ ψN (toSample fun u : ℝ =>
        ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ)) -
        inner ℂ ψN (toSample E) := by
    rw [hsplit, inner_add_right, inner_add_right, hzero]
    ring
  have hres := norm_toSample_rescale_le
    (chronologicalHeatError_continuousOn (prefixTailArray θ f N) N)
    (chronologicalHeatError_memLp (prefixTailArray θ f N) N) hN
  rw [hid]
  calc ‖(inner ℂ ψN (toSample fun u : ℝ =>
          ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ)) : ℂ) -
        inner ℂ ψN (toSample E)‖
      ≤ ‖toSample fun u : ℝ =>
          ((chronologicalHeatError (prefixTailArray θ f N) N (u / N) : ℝ) : ℂ)‖ +
        ‖toSample E‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_inner_le_norm _ _).trans_eq (by rw [hψN1, one_mul])
        · exact (norm_inner_le_norm _ _).trans_eq (by rw [hψN1, one_mul])
    _ ≤ _ := add_le_add hres hEn

end RHTower
