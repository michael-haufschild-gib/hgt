import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.RHTower.DirichletLLogStrip
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Local zero counts of a Dirichlet `L`-function

For a nonprincipal character `χ` the zeros of `Λ(s, χ)` with `Re ρ ≥ ½` and `|Im ρ − t| ≤ 1`
number `O(log(|t| + 3))`, with multiplicity (`card_zeros_near_le`).

Jensen's formula for the entire function `L(s, χ)` on the discs of radii `37/20 < 39/20` about
`2 + it`: the centre value has `|L(2 + it)| ≥ 1/3`, because `Σ_{n ≥ 2} n^{−2} < 2/3`, and on the
outer circle `Re s ≥ 1/20`, where the truncation bound of the corpus gives
`|L(s)| ≤ 2N(1 + 20|s|)`. Zeros of `Λ = Γ_ℝ L` in `Re s > 0` are zeros of `L` with the same
multiplicity.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- `Σ_{n ≥ 2} n^{−2} = π²/6 − 1 < 2/3`. -/
theorem tsum_ite_inv_sq_lt : ∑' n : ℕ, (if n = 1 then 0 else 1 / (n : ℝ) ^ 2) < 2 / 3 := by
  have h := hasSum_zeta_two
  have hsplit := h.summable.tsum_eq_add_tsum_ite 1
  rw [h.tsum_eq] at hsplit
  have hπ : Real.pi < 3.1416 := Real.pi_lt_d4
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
  rw [h1] at hsplit
  have : Real.pi ^ 2 / 6 < 1 + 2 / 3 := by nlinarith
  linarith

/-- **The centre value.** `|L(2 + it, χ)| ≥ 1/3`. -/
theorem one_third_le_norm_LFunction (t : ℝ) :
    1 / 3 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
  set s : ℂ := 2 + t * I
  have hs : 1 < s.re := by simp [s]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hre : s.re = 2 := by simp [s]
  have hsum : Summable (LSeries.term (fun n => χ n) s) := by
    refine Summable.of_norm_bounded hasSum_zeta_two.summable fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', norm_div, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn), hre, Real.rpow_two]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hterm1 : LSeries.term (fun n => χ n) s 1 = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]; simp
  have hnorm : ∀ n : ℕ, ‖(if n = 1 then 0 else LSeries.term (fun n => χ n) s n)‖ ≤
      (if n = 1 then 0 else 1 / (n : ℝ) ^ 2) := by
    intro n
    split_ifs with h1
    · simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      rw [LSeries.term_of_ne_zero hn.ne', norm_div, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
      rw [hre, Real.rpow_two]
      exact div_le_div_of_nonneg_right (χ.norm_le_one _) (by positivity)
  have hsummaj : Summable (fun n : ℕ => (if n = 1 then 0 else 1 / (n : ℝ) ^ 2)) :=
    (hasSum_zeta_two.summable).of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> simp)
  have hrest : ‖∑' n : ℕ, (if n = 1 then 0 else LSeries.term (fun n => χ n) s n)‖ < 2 / 3 :=
    lt_of_le_of_lt ((norm_tsum_le_tsum_norm (Summable.of_norm_bounded hsummaj hnorm).norm).trans
      (Summable.tsum_le_tsum hnorm (Summable.of_norm_bounded hsummaj hnorm).norm hsummaj))
      tsum_ite_inv_sq_lt
  rw [LSeries, hsum.tsum_eq_add_tsum_ite 1, hterm1]
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, (if n = 1 then 0 else
    LSeries.term (fun n => χ n) s n)))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- **Growth on the outer circle.** For `Re s ≥ 1/20`, `|L(s, χ)| ≤ 2N(1 + 20|s|)`. -/
theorem norm_LFunction_le_of_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 20 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 2 * N * (1 + 20 * ‖s‖) := by
  have hs0 : 0 < s.re := by linarith
  have h := RHTower.norm_LFunction_sub_character_partial_le hχ hs0 0
  simp only [RHTower.dirichletPartialSum, Finset.range_zero, Finset.sum_empty, sub_zero,
    Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at h
  refine h.trans ?_
  have : ‖s‖ / s.re ≤ 20 * ‖s‖ := by
    rw [div_le_iff₀ hs0]
    nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg s]

/-! ### Multiplicities -/

/-- `L` shifted to the anchor `2`. -/
def shiftedLFunction (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (z + 2)

theorem analyticOnNhd_shiftedLFunction (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ (shiftedLFunction χ) univ :=
  ((DirichletCharacter.differentiable_LFunction hχ).comp
    (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ

/-- Zeros of `Λ` and of `L` in `Re s > 0` have the same multiplicity. -/
theorem analyticOrderAt_shiftedL_eq (hχ : χ ≠ 1) {w : ℂ} (hw : 0 < (w + 2).re) :
    analyticOrderAt (shiftedL χ) w = analyticOrderAt (shiftedLFunction χ) w := by
  set U : Set ℂ := {z : ℂ | 0 < (z + 2).re}
  have hopen : IsOpen U :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_id.add continuous_const))
  have hdiff : DifferentiableOn ℂ (fun z => χ.gammaFactor (z + 2)) U := fun z hz =>
    ((differentiableAt_gammaFactor hz).comp z (differentiableAt_id.add_const 2)).differentiableWithinAt
  have hG : AnalyticAt ℂ (fun z => χ.gammaFactor (z + 2)) w :=
    hdiff.analyticAt (hopen.mem_nhds hw)
  have hL : AnalyticAt ℂ (shiftedLFunction χ) w := analyticOnNhd_shiftedLFunction hχ w (mem_univ w)
  have hev : shiftedL χ =ᶠ[𝓝 w] (fun z => χ.gammaFactor (z + 2)) * shiftedLFunction χ := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    simp only [shiftedL, shiftedLFunction, Pi.mul_apply]
    exact completedLFunction_eq_mul hz
  have hG0 : analyticOrderAt (fun z => χ.gammaFactor (z + 2)) w = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (gammaFactor_ne_zero hw))
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hG hL, hG0, zero_add]

/-! ### The count -/

theorem one_le_log_abs_add_three (t : ℝ) : 1 ≤ Real.log (|t| + 3) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith [abs_nonneg t])

/-- Zeros of `Λ(s, χ)` have `Re ρ < 1`. -/
theorem point_re_lt_one (hχ : χ ≠ 1) (q : LZero χ) : q.point.re < 1 := by
  by_contra hle
  exact completedLFunction_ne_zero_of_one_le_re hχ (not_lt.mp hle) (completedLFunction_point hχ q)

/-- The constant `(log(162N) + 1)/log(39/37)` of the local zero count. -/
def localCountConst (N : ℕ) : ℝ := (Real.log (162 * N) + 1) / Real.log ((39 / 20 : ℝ) / (37 / 20))

omit [NeZero N] in
theorem localCountConst_nonneg (hN : 1 ≤ N) : 0 ≤ localCountConst N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogRr : 0 < Real.log ((39 / 20 : ℝ) / (37 / 20)) := Real.log_pos (by norm_num)
  exact div_nonneg (by have := Real.log_nonneg (show (1 : ℝ) ≤ 162 * N by linarith); linarith)
    hlogRr.le

/-- **The local zero count, explicit constant.** The zeros of `Λ(s, χ)` with `Re ρ ≥ ½` and
`|Im ρ − t| ≤ 1` are finitely many and number at most `localCountConst N · log(|t| + 3)`, with
multiplicity. -/
theorem card_zeros_near_le_explicit (hχ : χ ≠ 1) (t : ℝ) :
    {q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1}.Finite ∧
      ({q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1}.ncard : ℝ) ≤
        localCountConst N * Real.log (|t| + 3) := by
  classical
  have hlogRr : 0 < Real.log ((39 / 20 : ℝ) / (37 / 20)) := Real.log_pos (by norm_num)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  unfold localCountConst
  set g := shiftedLFunction χ
  set c : ℂ := (t : ℂ) * I
  set r : ℝ := 37 / 20
  set R : ℝ := 39 / 20
  set M : ℝ := 2 * N * (1 + 20 * (|t| + 4))
  have han := analyticOnNhd_shiftedLFunction hχ
  have hloc := locallyFinite_zeroCopyPoint (analyticOnNhd_shiftedL hχ)
  have hcre : c.re = 0 := by simp [c]
  have hcn : ‖c‖ = |t| := by simp [c]
  -- the zeros near `t` lie in the closed disc of radius `r` about `c`
  set S := {q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1}
  set S' := {q : LZero χ | zeroCopyPoint (shiftedL χ) q ∈ closedBall c r}
  have hSS' : S ⊆ S' := by
    intro q hq
    obtain ⟨hre, him⟩ := hq
    have hlt := point_re_lt_one hχ q
    simp only [S', mem_setOf_eq, mem_closedBall, dist_eq_norm]
    have hw : zeroCopyPoint (shiftedL χ) q - c =
        ((q.point.re - 2 : ℝ) : ℂ) + ((q.point.im - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [c, LZero.point]
    rw [hw, Complex.norm_add_mul_I, Real.sqrt_le_left (by norm_num [r])]
    have him' : (q.point.im - t) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (q.point.im - t)]
    have hre' : (q.point.re - 2) ^ 2 ≤ 9 / 4 := by nlinarith
    simp only [r]
    linarith
  have hS'fin : S'.Finite := by
    refine (hloc (|t| + r)).subset fun q hq => ?_
    simp only [S', mem_setOf_eq, mem_closedBall, dist_eq_norm] at hq
    simp only [mem_setOf_eq]
    calc ‖zeroCopyPoint (shiftedL χ) q‖ = ‖(zeroCopyPoint (shiftedL χ) q - c) + c‖ := by ring_nf
      _ ≤ ‖zeroCopyPoint (shiftedL χ) q - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ |t| + r := by linarith
  refine ⟨hS'fin.subset hSS', ?_⟩
  -- Jensen on the discs `r < R` about `c`
  have hgc : 1 / 3 ≤ ‖g c‖ := by
    have := one_third_le_norm_LFunction (χ := χ) t
    rwa [show (2 : ℂ) + t * I = c + 2 by ring] at this
  have hgc0 : 0 < ‖g c‖ := lt_of_lt_of_le (by norm_num) hgc
  have hM1 : 1 ≤ M := by
    have : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hbound : ∀ z ∈ sphere c |R|, ‖g z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num [R] : (0 : ℝ) < R)] at hz
    have hre : 1 / 20 ≤ (z + 2).re := by
      have h1 := Complex.abs_re_le_norm (z - c)
      rw [hz, sub_re, hcre, sub_zero] at h1
      rw [add_re]
      have := neg_abs_le z.re
      norm_num [R] at h1 ⊢
      linarith
    have hz2 : ‖z + 2‖ ≤ |t| + 4 := by
      calc ‖z + 2‖ = ‖(z - c) + c + 2‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ + ‖(2 : ℂ)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ ≤ |t| + 4 := by rw [hz, hcn]; norm_num [R]; linarith
    refine (norm_LFunction_le_of_re hχ hre).trans ?_
    have : (0 : ℝ) ≤ 2 * N := by positivity
    simp only [M]
    gcongr
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (f := g)
    (by norm_num [r]) (by norm_num [r, R]) hM1 (han.mono (subset_univ _)) (norm_ne_zero_iff.mp hgc0.ne') hbound
  rw [abs_of_pos (by norm_num [r] : (0 : ℝ) < r)] at hJ
  -- the zero copies in the disc are counted by the divisor of `g` on the disc
  set D := MeromorphicOn.divisor g (closedBall c r)
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c r)
  set W : Finset ℂ := (hS'fin.toFinset).image (zeroCopyPoint (shiftedL χ))
  have hcount : (S'.ncard : ℝ) ≤ ∑ w ∈ W, (D w : ℝ) := by
    rw [Set.ncard_eq_toFinset_card S' hS'fin,
      Finset.card_eq_sum_card_image (zeroCopyPoint (shiftedL χ)) hS'fin.toFinset]
    push_cast
    refine Finset.sum_le_sum fun w hw => ?_
    have hfin : {q : LZero χ | zeroCopyPoint (shiftedL χ) q = w}.Finite :=
      (hloc ‖w‖).subset fun q hq => by
        simp only [mem_setOf_eq] at hq ⊢
        rw [hq]
    have hfib : (({q ∈ hS'fin.toFinset | zeroCopyPoint (shiftedL χ) q = w}).card : ℝ) ≤
        ({q : LZero χ | zeroCopyPoint (shiftedL χ) q = w}.ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact_mod_cast Finset.card_le_card fun q hq => by
        simp only [Finset.mem_filter] at hq
        simpa using hq.2
    refine hfib.trans ?_
    rw [ncard_zeroCopy_fiber]
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
    rw [Set.Finite.mem_toFinset] at hq
    simp only [S', mem_setOf_eq] at hq
    have hre : 0 < (zeroCopyPoint (shiftedL χ) q + 2).re := by
      have h1 := Complex.abs_re_le_norm (zeroCopyPoint (shiftedL χ) q - c)
      rw [mem_closedBall, dist_eq_norm] at hq
      rw [sub_re, hcre, sub_zero] at h1
      rw [add_re]
      have := neg_abs_le (zeroCopyPoint (shiftedL χ) q).re
      norm_num [r] at hq h1 ⊢
      linarith
    rw [divisor_univ_eq_analyticOrder (analyticOnNhd_shiftedL hχ),
      analyticOrderAt_shiftedL_eq hχ hre,
      MeromorphicOn.AnalyticOnNhd.divisor_apply (han.mono (subset_univ _)) hq]
    cases analyticOrderAt g (zeroCopyPoint (shiftedL χ) q) using ENat.recTopCoe <;> simp
  have hWsum : ∑ w ∈ W, (D w : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset D (s := hDfin.toFinset ∪ W) (by
      intro u hu; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hu)]
    push_cast
    refine Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun u _ _ => ?_
    have hD0 : 0 ≤ D u := by
      by_cases hu : u ∈ closedBall c r
      · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (han.mono (subset_univ _)) hu]
        cases analyticOrderAt g u using ENat.recTopCoe <;> simp
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu]
    exact_mod_cast hD0
  have hlog : Real.log (M / ‖g c‖) ≤ (Real.log (162 * N) + 1) * Real.log (|t| + 3) := by
    have h1 : M / ‖g c‖ ≤ 162 * N * (|t| + 3) := by
      rw [div_le_iff₀ hgc0]
      have : 0 ≤ |t| := abs_nonneg t
      simp only [M]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 162 * N * (|t| + 3)) (sub_nonneg.2 hgc)]
    have hl3 := one_le_log_abs_add_three t
    have hl162 : 0 ≤ Real.log (162 * N) := Real.log_nonneg (by linarith)
    calc Real.log (M / ‖g c‖) ≤ Real.log (162 * N * (|t| + 3)) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log (162 * N) + Real.log (|t| + 3) := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ (Real.log (162 * N) + 1) * Real.log (|t| + 3) := by nlinarith
  calc (S.ncard : ℝ) ≤ (S'.ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hSS' hS'fin
    _ ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := hcount.trans hWsum
    _ ≤ Real.log (M / ‖g c‖) / Real.log (R / r) := hJ
    _ ≤ (Real.log (162 * N) + 1) * Real.log (|t| + 3) / Real.log (R / r) :=
        div_le_div_of_nonneg_right hlog hlogRr.le
    _ = _ := by simp only [R, r]; ring

/-- **The local zero count.** The zeros of `Λ(s, χ)` with `Re ρ ≥ ½` and `|Im ρ − t| ≤ 1` are
finitely many and number at most `C log(|t| + 3)`, with multiplicity. -/
theorem card_zeros_near_le (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      {q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1}.Finite ∧
      ({q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1}.ncard : ℝ) ≤
        C * Real.log (|t| + 3) :=
  ⟨localCountConst N, localCountConst_nonneg (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)),
    card_zeros_near_le_explicit hχ⟩

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
