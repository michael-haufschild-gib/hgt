import GaloisForLFunctions.RHTower.BaezDuarteDistancePlancherel
import GaloisForLFunctions.RHTower.ZetaShiftRatioMeanSquareLimit
import GaloisForLFunctions.RHTower.InverseZetaRieszPerronShift
import GaloisForLFunctions.RHTower.BaezDuarteDistance

/-!
# The Báez-Duarte criterion: RH implies `d_N → 0`

Let `d_N` be the distance from `1_{(0,1]}` to the span of the first `N` Báez-Duarte functions
`({u/n} − {u}/n)/u` (`bdDistDiscrete`).  The easy direction `d_N → 0 ⟹ RH` is
`riemannHypothesis_of_tendsto_bdDistDiscrete`.  This file proves the converse, so

`RH ⟺ d_N → 0`   (`riemannHypothesis_iff_tendsto_bdDistDiscrete`).

**Approximants.**  Fix `0 < δ ≤ 1/4`, `X = N + ½`, and take `c_n = −μ(n)(1 − n/X)n^{−δ}`
(`bdRieszCoeff`).  Then `P_c(s) = Σ c_n(n^{−s} − 1/n) = −Q_N(s + δ) + Q_N(1 + δ)` with
`Q_N(z) = Σ_{n ≤ N} μ(n)(1 − n/X) n^{−z}`, and on `s = ½ + it`

`1 + ζ(s)P_c(s) = (1 − ζ(s)/ζ(s + δ)) + ζ(s)(1/ζ(s + δ) − Q_N(s + δ)) + ζ(s)Q_N(1 + δ)`.

**Bounds under RH.** By the Plancherel formula the squared distance is `(1/2π)∫|1 + ζP_c|²/|s|²`.
The first piece integrates to the shift defect `F(δ)`, which tends to `0` as `δ ↓ 0`; the second is
`O(X^{−δ/2}(1 + |t|)^{3/8})` by the Riesz--Perron shift and `|ζ(½ + it)| ≪ (1 + |t|)^{1/4}`; the
third is `O(|Q_N(1 + δ)|(1 + |t|)^{1/4})` with `Q_N(1 + δ) → 1/ζ(1 + δ) → 0`. Hence

`d_N² ≤ (3/2π)(F(δ) + B₁X^{−δ} + B₂|Q_N(1 + δ)|²)`

(`exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh`), whose right side tends to
`(3/2π)(F(δ) + B₂|1/ζ(1 + δ)|²)` as `N → ∞` and then to `0` as `δ ↓ 0`.
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-! ## Elementary bounds -/

theorem rpow_abs_add_three_le (t : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (|t| + 3) ^ ε ≤ 3 * (1 + |t|) ^ ε := by
  have h : |t| + 3 ≤ 3 * (1 + |t|) := by linarith [abs_nonneg t]
  calc (|t| + 3) ^ ε ≤ (3 * (1 + |t|)) ^ ε := Real.rpow_le_rpow (by positivity) h hε0
    _ = 3 ^ ε * (1 + |t|) ^ ε := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ 3 * (1 + |t|) ^ ε := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (3 : ℝ) ^ ε ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
          _ = 3 := Real.rpow_one 3

/-- The weighted mean square of a function of polynomial growth `(1 + |t|)^a`, `a < ½`. -/
theorem integrable_and_integral_norm_sq_div_le {g : ℝ → ℂ} (hg : Measurable g) {C a : ℝ}
    (ha : a < 1 / 2) (hb : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ a) :
    Integrable (fun t : ℝ => ‖g t‖ ^ 2 / (1 / 4 + t ^ 2)) ∧
      ∫ t : ℝ, ‖g t‖ ^ 2 / (1 / 4 + t ^ 2) ≤
        8 * C ^ 2 * ∫ t : ℝ, (1 + |t|) ^ (-(2 - 2 * a)) := by
  have hbase : Integrable fun t : ℝ => (1 + |t|) ^ (-(2 - 2 * a)) := by
    have h : Integrable fun t : ℝ => (1 + ‖t‖) ^ (-(2 - 2 * a)) :=
      integrable_one_add_norm (by simp; linarith)
    exact h.congr (Eventually.of_forall fun t => by simp only [Real.norm_eq_abs])
  have hpt : ∀ t : ℝ, ‖g t‖ ^ 2 / (1 / 4 + t ^ 2) ≤ 8 * C ^ 2 * (1 + |t|) ^ (-(2 - 2 * a)) := by
    intro t
    have hpos : 0 < 1 + |t| := by positivity
    have hq := one_div_quarter_add_sq_le t
    have hg2 : ‖g t‖ ^ 2 ≤ C ^ 2 * (1 + |t|) ^ (2 * a) := by
      have h0 : 0 ≤ C * (1 + |t|) ^ a := (norm_nonneg _).trans (hb t)
      calc ‖g t‖ ^ 2 ≤ (C * (1 + |t|) ^ a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb t) 2
        _ = C ^ 2 * (1 + |t|) ^ (2 * a) := by
            rw [mul_pow, ← Real.rpow_natCast ((1 + |t|) ^ a), ← Real.rpow_mul hpos.le]
            norm_num [mul_comm]
    rw [div_eq_mul_one_div]
    calc ‖g t‖ ^ 2 * (1 / (1 / 4 + t ^ 2))
        ≤ C ^ 2 * (1 + |t|) ^ (2 * a) * (8 * (1 + |t|) ^ (-2 : ℝ)) :=
          mul_le_mul hg2 hq (by positivity) (by positivity)
      _ = 8 * C ^ 2 * ((1 + |t|) ^ (2 * a) * (1 + |t|) ^ (-2 : ℝ)) := by ring
      _ = 8 * C ^ 2 * (1 + |t|) ^ (-(2 - 2 * a)) := by
          rw [← Real.rpow_add hpos]; ring_nf
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖g t‖ ^ 2 / (1 / 4 + t ^ 2)) volume :=
    ((hg.norm.pow_const 2).div (by fun_prop)).aestronglyMeasurable
  have hint : Integrable (fun t : ℝ => ‖g t‖ ^ 2 / (1 / 4 + t ^ 2)) :=
    (hbase.const_mul (8 * C ^ 2)).mono' hmeas (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt t)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint (hbase.const_mul _) hpt

/-! ## The Riesz coefficients -/

/-- `c_n = −μ(n)(1 − n/X) n^{−δ}`. -/
def bdRieszCoeff (N : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  -((ArithmeticFunction.moebius n : ℤ) : ℝ) * (1 - (n : ℝ) / perronLength N) * (n : ℝ) ^ (-δ)

theorem natCast_rpow_neg_mul_cpow {n : ℕ} (hn : n ≠ 0) (δ : ℝ) (s : ℂ) :
    (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * (n : ℂ) ^ (-s) = (n : ℂ) ^ (-(s + δ)) := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hnc]
  push_cast
  ring_nf

/-- `P_c(s) = −Q_N(s + δ) + Q_N(1 + δ)` for the Riesz coefficients. -/
theorem bdMollPoly_bdRieszCoeff (N : ℕ) (δ : ℝ) (s : ℂ) :
    bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) s =
      -moebiusRieszPoly N (s + δ) + moebiusRieszPoly N (1 + δ) := by
  unfold bdMollPoly moebiusRieszPoly
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have h1 := natCast_rpow_neg_mul_cpow hn0 δ s
  have h2 := natCast_rpow_neg_mul_cpow hn0 δ 1
  rw [Complex.cpow_neg_one] at h2
  unfold bdRieszCoeff
  push_cast
  rw [show (1 : ℂ) + δ = 1 + (δ : ℂ) from rfl]
  linear_combination (-(((ArithmeticFunction.moebius n : ℤ) : ℂ)) *
    (1 - (n : ℂ) / (perronLength N : ℂ))) * h1 -
    (-(((ArithmeticFunction.moebius n : ℤ) : ℂ)) * (1 - (n : ℂ) / (perronLength N : ℂ))) * h2

/-! ## Growth of `ζ` under RH -/

/-- Under RH, `|ζ(σ + iv)| ≤ M (|v| + 3)^ε` for all real `v`, for `½ < σ ≤ 5/2`, `σ ≠ 1`. -/
theorem exists_norm_riemannZeta_vertical_le_of_rh (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ2 : σ ≤ 5 / 2) (hσ1 : σ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, ‖riemannZeta ((σ : ℂ) + (v : ℂ) * I)‖ ≤ M * (|v| + 3) ^ ε := by
  set d := min (σ - 1 / 2) (1 / 4) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
  have hd1 : d < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨T₀, hT₀⟩ := ZetaGrowth.exists_norm_riemannZeta_two_sided hRH hd0 hd1 hε
  have hcont := (continuous_riemannZeta_vertical hσ1).continuousOn (s := Icc (-|T₀|) |T₀|)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun v => ?_⟩
  have hp1 : 1 ≤ (|v| + 3) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg v]) hε.le
  rcases le_or_gt |v| |T₀| with hv | hv
  · calc ‖riemannZeta ((σ : ℂ) + (v : ℂ) * I)‖ ≤ C := hC v (abs_le.mp hv)
      _ ≤ max C 1 := le_max_left _ _
      _ ≤ max C 1 * (|v| + 3) ^ ε := le_mul_of_one_le_right (le_max_of_le_right zero_le_one) hp1
  · have h := (hT₀ v (le_trans (le_abs_self T₀) hv.le) σ
      (by linarith [min_le_left (σ - 1 / 2) (1 / 4)]) hσ2).2
    calc _ ≤ (|v| + 3) ^ ε := h
      _ ≤ max C 1 * (|v| + 3) ^ ε := le_mul_of_one_le_left (by positivity) (le_max_right _ _)

/-- Under RH, `|ζ(½ + it)| ≤ K (1 + |t|)^{1/4}`. -/
theorem exists_norm_riemannZeta_half_le_rpow_of_rh (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ,
      ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ K * (1 + |t|) ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_riemannZeta_half_le_of_rh hRH
  obtain ⟨M, hM0, hM⟩ := exists_norm_riemannZeta_vertical_le_of_rh hRH (σ := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (ε := 1 / 8) (by norm_num)
  refine ⟨3 * K * M, by positivity, fun t => ?_⟩
  have h1 := hK (1 / 4) (by norm_num) le_rfl t
  have he : (1 / 2 : ℂ) + ((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I = ((3 / 4 : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  rw [he] at h1
  have h2 := (hM t).trans (mul_le_mul_of_nonneg_left
    (rpow_abs_add_three_le t (by norm_num) (by norm_num)) hM0)
  have hpos : 0 < 1 + |t| := by positivity
  calc ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖
      ≤ K * (1 + |t|) ^ (1 / 8 : ℝ) * (M * (3 * (1 + |t|) ^ (1 / 8 : ℝ))) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = 3 * K * M * ((1 + |t|) ^ (1 / 8 : ℝ) * (1 + |t|) ^ (1 / 8 : ℝ)) := by ring
    _ = 3 * K * M * (1 + |t|) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hpos]; norm_num

/-! ## The decomposition of `1 + ζ P_c` -/

theorem norm_add_add_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := (norm_add_le (a + b) c).trans (by
    linarith [norm_add_le a b])
  have h0 : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖),
    norm_nonneg a, norm_nonneg b, norm_nonneg c]

theorem continuous_moebiusRieszPoly (N : ℕ) : Continuous (moebiusRieszPoly N) := by
  unfold moebiusRieszPoly
  refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (by omega : n ≠ 0)
  exact continuous_neg.const_cpow (Or.inl hn0)

/-- `1 + ζ(s)P_c(s) = (1 − ζ(s)/ζ(s + δ)) + ζ(s)(1/ζ(s + δ) − Q_N(s + δ)) + ζ(s)Q_N(1 + δ)`. -/
theorem one_add_riemannZeta_mul_bdMollPoly_bdRieszCoeff (N : ℕ) {δ : ℝ} (hδ1 : δ < 1 / 2)
    (t : ℝ) :
    1 + riemannZeta (1 / 2 + (t : ℂ) * I) *
        bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + (t : ℂ) * I) =
      (1 - riemannZeta (1 / 2 + (t : ℂ) * I) / riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)) +
        riemannZeta (1 / 2 + (t : ℂ) * I) *
          (invZetaCont (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) -
            moebiusRieszPoly N (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I)) +
        riemannZeta (1 / 2 + (t : ℂ) * I) * moebiusRieszPoly N (1 + δ) := by
  have he : (1 / 2 : ℂ) + (t : ℂ) * I + δ = ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  have he' : (1 / 2 : ℂ) + (δ : ℂ) + (t : ℂ) * I = ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast; ring
  have hne : ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [bdMollPoly_bdRieszCoeff, he, he', invZetaCont_eq hne, div_eq_mul_inv]
  ring

/-! ## The distance bound -/

/-- The shift-limit integral `F(δ) = ∫ |1 − ζ(½ + it)/ζ(½ + δ + it)|² dt/(¼ + t²)`. -/
def zetaShiftDefect (δ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖1 - riemannZeta (1 / 2 + (t : ℂ) * I) /
    riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2)

/-- **The distance bound under RH.**  There is `B₂` such that for each `0 < δ ≤ 1/4` there is `B₁`
with, for every `N`,
`d² ≤ (3/2π) (F(δ) + B₁ X^{−δ} + B₂ |Q_N(1 + δ)|²)`,
where `d` is the distance from the target to the Riesz combination of the first `N` generators. -/
theorem exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh (hRH : RiemannHypothesis) :
    ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∃ B₁ : ℝ, ∀ N : ℕ,
      ‖bdTarget - ∑ n ∈ Finset.Icc 1 N, (bdRieszCoeff N δ n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2 ≤
        (2 * Real.pi)⁻¹ * (3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
          B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_riemannZeta_half_le_rpow_of_rh hRH
  obtain ⟨K, hK0, hK⟩ := exists_norm_riemannZeta_half_le_of_rh hRH
  set L₁ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 - 2 * (1 / 4 : ℝ))) with hL₁
  set L₂ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(2 - 2 * (3 / 8 : ℝ))) with hL₂
  have hL₁0 : 0 ≤ L₁ := integral_nonneg fun t => by positivity
  refine ⟨8 * K₁ ^ 2 * L₁, by positivity, fun δ hδ hδ1 => ?_⟩
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_norm_moebiusRieszPoly_sub_le_of_rh hRH hδ (by linarith)
    (ε := 1 / 8) (by norm_num) (by norm_num)
  refine ⟨8 * (3 * K₁ * C₃) ^ 2 * L₂, fun N => ?_⟩
  set X : ℝ := perronLength N with hX
  have hX0 : 0 < X := perronLength_pos N
  have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨hint, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
  rw [heq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the three pieces
  set zs : ℝ → ℂ := fun t => riemannZeta (1 / 2 + (t : ℂ) * I) with hzs
  set zu : ℝ → ℂ := fun t => riemannZeta (1 / 2 + (δ : ℂ) + (t : ℂ) * I) with hzu
  set u' : ℝ → ℂ := fun t => ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hu'
  set Q1 : ℂ := moebiusRieszPoly N (1 + δ) with hQ1
  set ga : ℝ → ℂ := fun t => 1 - zs t / zu t with hga
  set gb : ℝ → ℂ := fun t => zs t * (invZetaCont (u' t) - moebiusRieszPoly N (u' t)) with hgb
  set gc : ℝ → ℂ := fun t => zs t * Q1 with hgc
  have hzsc : Continuous zs := by
    have := continuous_riemannZeta_vertical (σ := 1 / 2) (by norm_num)
    simpa [hzs] using this
  have hzuc : Continuous zu := by
    have := continuous_riemannZeta_vertical (σ := 1 / 2 + δ) (by linarith)
    simpa [hzu] using this
  have hinvc : Continuous fun t => invZetaCont (u' t) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ((differentiableAt_invZetaCont hRH (by simp [hu']; linarith)).continuousAt).comp
      (f := u') (by fun_prop)
  have hQc : Continuous fun t => moebiusRieszPoly N (u' t) :=
    (continuous_moebiusRieszPoly N).comp (by fun_prop)
  -- bounds
  have hbound_a : ∀ t, ‖ga t‖ ≤ (1 + K) * (1 + |t|) ^ (1 / 8 : ℝ) := by
    intro t
    have hr : ‖zs t / zu t‖ ≤ K * (1 + |t|) ^ (1 / 8 : ℝ) := by
      rw [norm_div]
      by_cases hz : ‖zu t‖ = 0
      · rw [hz, div_zero]; positivity
      · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
        exact hK δ hδ.le hδ1 t
    have hp1 : 1 ≤ (1 + |t|) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
    calc ‖ga t‖ ≤ ‖(1 : ℂ)‖ + ‖zs t / zu t‖ := norm_sub_le _ _
      _ ≤ 1 + K * (1 + |t|) ^ (1 / 8 : ℝ) := by rw [norm_one]; linarith
      _ ≤ (1 + K) * (1 + |t|) ^ (1 / 8 : ℝ) := by nlinarith
  have hbound_b : ∀ t, ‖gb t‖ ≤ (3 * K₁ * C₃ * X ^ (-(δ / 2))) * (1 + |t|) ^ (3 / 8 : ℝ) := by
    intro t
    have hpos : 0 < 1 + |t| := by positivity
    have h1 := hK₁ t
    have h2 := (hC₃ N t).trans (mul_le_mul_of_nonneg_left
      (rpow_abs_add_three_le t (by norm_num) (by norm_num)) (by positivity))
    calc ‖gb t‖ = ‖zs t‖ * ‖invZetaCont (u' t) - moebiusRieszPoly N (u' t)‖ := by
          rw [hgb, norm_mul]
      _ = ‖zs t‖ * ‖moebiusRieszPoly N (u' t) - invZetaCont (u' t)‖ := by rw [norm_sub_rev]
      _ ≤ (K₁ * (1 + |t|) ^ (1 / 4 : ℝ)) *
            (C₃ * X ^ (-(δ / 2)) * (3 * (1 + |t|) ^ (1 / 8 : ℝ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 3 * K₁ * C₃ * X ^ (-(δ / 2)) * ((1 + |t|) ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 8 : ℝ)) := by
          ring
      _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  have hbound_c : ∀ t, ‖gc t‖ ≤ (K₁ * ‖Q1‖) * (1 + |t|) ^ (1 / 4 : ℝ) := by
    intro t
    calc ‖gc t‖ = ‖zs t‖ * ‖Q1‖ := by rw [hgc, norm_mul]
      _ ≤ K₁ * (1 + |t|) ^ (1 / 4 : ℝ) * ‖Q1‖ := mul_le_mul_of_nonneg_right (hK₁ t) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨hia, -⟩ := integrable_and_integral_norm_sq_div_le
    (hga ▸ (measurable_const.sub (hzsc.measurable.div hzuc.measurable)))
    (by norm_num : (1 / 8 : ℝ) < 1 / 2) hbound_a
  obtain ⟨hib, hIb⟩ := integrable_and_integral_norm_sq_div_le
    (hgb ▸ (hzsc.measurable.mul (hinvc.measurable.sub hQc.measurable)))
    (by norm_num : (3 / 8 : ℝ) < 1 / 2) hbound_b
  obtain ⟨hic, hIc⟩ := integrable_and_integral_norm_sq_div_le
    (hgc ▸ (hzsc.measurable.mul measurable_const)) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hbound_c
  have hpt : ∀ t : ℝ, ‖1 + riemannZeta (1 / 2 + (t : ℂ) * I) *
      bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2)
      ≤ 3 * (‖ga t‖ ^ 2 / (1 / 4 + t ^ 2) + ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2) +
        ‖gc t‖ ^ 2 / (1 / 4 + t ^ 2)) := by
    intro t
    rw [one_add_riemannZeta_mul_bdMollPoly_bdRieszCoeff N (by linarith) t]
    have h := norm_add_add_sq_le (ga t) (gb t) (gc t)
    have hq : 0 < 1 / 4 + t ^ 2 := by positivity
    calc _ ≤ 3 * (‖ga t‖ ^ 2 + ‖gb t‖ ^ 2 + ‖gc t‖ ^ 2) / (1 / 4 + t ^ 2) :=
          div_le_div_of_nonneg_right h hq.le
      _ = _ := by ring
  have hab : Integrable (fun t : ℝ => ‖ga t‖ ^ 2 / (1 / 4 + t ^ 2) +
      ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2)) := hia.add hib
  have habc : Integrable (fun t : ℝ => ‖ga t‖ ^ 2 / (1 / 4 + t ^ 2) +
      ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2) + ‖gc t‖ ^ 2 / (1 / 4 + t ^ 2)) := hab.add hic
  have hsumint := habc.const_mul 3
  have hF : ∫ t : ℝ, ‖ga t‖ ^ 2 / (1 / 4 + t ^ 2) = zetaShiftDefect δ := by
    simp only [zetaShiftDefect, hga, hzs, hzu]
  calc ∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + (t : ℂ) * I) *
        bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + (t : ℂ) * I)‖ ^ 2 / (1 / 4 + t ^ 2)
      ≤ ∫ t : ℝ, 3 * (‖ga t‖ ^ 2 / (1 / 4 + t ^ 2) + ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2) +
          ‖gc t‖ ^ 2 / (1 / 4 + t ^ 2)) := integral_mono hint hsumint hpt
    _ = 3 * (zetaShiftDefect δ + (∫ t : ℝ, ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2)) +
          ∫ t : ℝ, ‖gc t‖ ^ 2 / (1 / 4 + t ^ 2)) := by
        rw [integral_const_mul, integral_add hab hic, integral_add hia hib, hF]
    _ ≤ 3 * (zetaShiftDefect δ + 8 * (3 * K₁ * C₃) ^ 2 * L₂ * X ^ (-δ) +
          8 * K₁ ^ 2 * L₁ * ‖Q1‖ ^ 2) := by
        have hXd : (X ^ (-(δ / 2))) ^ 2 = X ^ (-δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
        have hb' : ∫ t : ℝ, ‖gb t‖ ^ 2 / (1 / 4 + t ^ 2) ≤
            8 * (3 * K₁ * C₃) ^ 2 * L₂ * X ^ (-δ) := by
          refine hIb.trans (le_of_eq ?_)
          rw [hL₂, ← hXd]; ring
        have hc' : ∫ t : ℝ, ‖gc t‖ ^ 2 / (1 / 4 + t ^ 2) ≤ 8 * K₁ ^ 2 * L₁ * ‖Q1‖ ^ 2 := by
          refine hIc.trans (le_of_eq ?_)
          rw [hL₁]; ring
        linarith

/-! ## The limits -/

theorem tendsto_perronLength_atTop : Tendsto perronLength atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

theorem tendsto_perronLength_rpow_neg {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => perronLength N ^ (-δ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hδ).comp tendsto_perronLength_atTop

/-- Under RH, `Q_N(1 + δ) → 1/ζ(1 + δ)` for `0 < δ < ½`. -/
theorem tendsto_moebiusRieszPoly_one_add_of_rh (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    Tendsto (fun N : ℕ => moebiusRieszPoly N (1 + δ)) atTop (𝓝 (invZetaCont (1 + δ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_moebiusRieszPoly_sub_le_of_rh hRH (δ := 1 / 2 + δ)
    (by linarith) (by linarith) (ε := 1 / 2) (by norm_num) (by norm_num)
  have he : (((1 / 2 + (1 / 2 + δ) : ℝ)) : ℂ) + ((0 : ℝ) : ℂ) * I = 1 + δ := by push_cast; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => C * perronLength N ^ (-((1 / 2 + δ) / 2)) *
      (|(0 : ℝ)| + 3) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((tendsto_perronLength_rpow_neg (δ := (1 / 2 + δ) / 2) (by linarith)).const_mul
      C).mul_const ((|(0 : ℝ)| + 3) ^ (1 / 2 : ℝ))
    simpa using this
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hlim
  have h := hC N 0
  rw [he] at h
  exact h

/-- Under RH, `1/ζ(1 + δ) → 0` as `δ ↓ 0`. -/
theorem tendsto_invZetaCont_one_add_of_rh (hRH : RiemannHypothesis) :
    Tendsto (fun δ : ℝ => invZetaCont (1 + δ)) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt invZetaCont 1 :=
    (differentiableAt_invZetaCont hRH (by norm_num)).continuousAt
  have h1 : invZetaCont 1 = 0 := by simp [invZetaCont]
  have hl : Tendsto (fun δ : ℝ => (1 : ℂ) + δ) (𝓝[>] 0) (𝓝 1) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous fun δ : ℝ => (1 : ℂ) + δ := by fun_prop
    simpa using this.tendsto 0
  have := hc.tendsto.comp hl
  rwa [h1] at this

/-- The discrete distance is at most the distance to any combination of the first `N`
generators `θ = 1/n`, `1 ≤ n ≤ N`. -/
theorem bdDistDiscrete_le_norm_sub_sum (N : ℕ) (c : ℕ → ℝ) :
    bdDistDiscrete N ≤ ‖bdTarget - ∑ n ∈ Finset.Icc 1 N, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ := by
  unfold bdDistDiscrete bdDistFinset bdDist
  rw [← dist_eq_norm]
  refine Metric.infDist_le_dist_of_mem ?_
  unfold bdSpanSet
  rw [SetLike.mem_coe]
  refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  refine ⟨⟨n - 1, Finset.mem_range.mpr (by omega)⟩, ?_⟩
  simp only [bdDiscrete]
  congr 1
  rw [Nat.cast_sub hn1]
  push_cast
  ring

/-! ## The hard direction -/

/-- **Explicit approximants under RH.**  For every `ε > 0` some Riesz combination
`Σ_{n ≤ N} c_n bdGen(1/n)`, `c_n = −μ(n)(1 − n/X)n^{−δ}`, is within `ε` of the target. -/
theorem exists_bdRiesz_norm_lt_of_rh (hRH : RiemannHypothesis) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ δ < 1 / 4 ∧
      ‖bdTarget - ∑ n ∈ Finset.Icc 1 N, (bdRieszCoeff N δ n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ < ε := by
  obtain ⟨B₂, hB₂0, hB⟩ := exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh hRH
  -- choose `δ`
  have hRlim : Tendsto (fun δ : ℝ => (2 * Real.pi)⁻¹ *
      (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have hF : Tendsto zetaShiftDefect (𝓝[>] 0) (𝓝 0) :=
      tendsto_integral_one_sub_riemannZeta_ratio_of_rh hRH
    have hI := ((tendsto_invZetaCont_one_add_of_rh hRH).norm.pow 2).const_mul B₂
    have := ((hF.add hI).const_mul 3).const_mul (2 * Real.pi)⁻¹
    simpa using this
  obtain ⟨δ, hδR, hδ0, hδ1⟩ :=
    ((hRlim.eventually (gt_mem_nhds (pow_pos hε0 2))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num))).exists
  obtain ⟨B₁, hB₁⟩ := hB δ hδ0 hδ1.le
  -- choose `N`
  have hG : Tendsto (fun N : ℕ => (2 * Real.pi)⁻¹ * (3 * (zetaShiftDefect δ +
      B₁ * perronLength N ^ (-δ) + B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2))) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2)))) := by
    have h1 := (tendsto_perronLength_rpow_neg hδ0).const_mul B₁
    have h2 := ((tendsto_moebiusRieszPoly_one_add_of_rh hRH hδ0 (by linarith)).norm.pow
      2).const_mul B₂
    have := (((tendsto_const_nhds (x := zetaShiftDefect δ)).add h1).add h2).const_mul 3
      |>.const_mul (2 * Real.pi)⁻¹
    simpa using this
  obtain ⟨N, hN⟩ := (hG.eventually (gt_mem_nhds hδR)).exists
  refine ⟨N, δ, hδ0, hδ1, ?_⟩
  have hsq := (hB₁ N).trans_lt hN
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε0.le two_ne_zero).mp hsq

/-- **RH implies `d_N → 0`.**  Under the Riemann hypothesis the distances from `1_{(0,1]}` to the
spans of the first `N` functions `({u/n} − {u}/n)/u` tend to zero.  The approximants are the Riesz
combinations with coefficients `−μ(n)(1 − n/X)n^{−δ}`: by the Plancherel formula the squared
distance is at most `(3/2π)(F(δ) + B₁X^{−δ} + B₂|Q_N(1 + δ)|²)`, which tends to
`(3/2π)(F(δ) + B₂|1/ζ(1 + δ)|²)` as `N → ∞`, and this tends to `0` as `δ ↓ 0`. -/
theorem tendsto_bdDistDiscrete_zero_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Tendsto bdDistDiscrete atTop (𝓝 0) := by
  refine tendsto_bdDistDiscrete_zero_of_reciprocalWitnesses fun k => ?_
  obtain ⟨N, δ, -, -, hlt⟩ := exists_bdRiesz_norm_lt_of_rh hRH
    (ε := 1 / ((k + 1 : ℕ) : ℝ)) (by positivity)
  exact ⟨N, (bdDistDiscrete_le_norm_sub_sum N (bdRieszCoeff N δ)).trans_lt hlt⟩

/-- **The Báez-Duarte criterion.**  The Riemann hypothesis holds if and only if the distances from
`1_{(0,1]}` to the spans of the first `N` functions `({u/n} − {u}/n)/u` tend to zero. -/
theorem riemannHypothesis_iff_tendsto_bdDistDiscrete :
    RiemannHypothesis ↔ Tendsto bdDistDiscrete atTop (𝓝 0) :=
  ⟨tendsto_bdDistDiscrete_zero_of_riemannHypothesis, riemannHypothesis_of_tendsto_bdDistDiscrete⟩

end

end RHTower
