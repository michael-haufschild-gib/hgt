import GaloisForLFunctions.RHTower.PaperWoldPrimeRectangle

/-! # Logarithmic operator-norm growth of the actual finite Wold cutoffs

Two finite prime windows retain a positive rectangular matrix. Exact norms of
their characteristic vectors convert the arithmetic entry bound into a growing
operator-norm lower bound.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators InnerProductSpace ENNReal

private theorem finite_rectangle_norm_lower
    (A : PaperWoldHistory →L[ℂ] PaperWoldHistory) (s u : Finset ℕ)
    (L a : ℝ) (hL : 0 < L) (ha : 0 ≤ a)
    (hs : L ≤ (s.card : ℝ)) (hu : L ≤ (u.card : ℝ))
    (he : ∀ n ∈ s, ∀ j ∈ u, a ≤ (A (lp.single 2 j (1 : ℂ)) n).re) :
    a * L ≤ ‖A‖ := by
  let x : PaperWoldHistory := ∑ n ∈ s, lp.single 2 n (1 : ℂ)
  let y : PaperWoldHistory := ∑ j ∈ u, lp.single 2 j (1 : ℂ)
  have hx : ‖x‖ ^ 2 = (s.card : ℝ) := by
    simpa only [x, ENNReal.toReal_ofNat, Real.rpow_two, norm_one, one_pow, Finset.sum_const,
      nsmul_eq_mul, mul_one] using lp.norm_sum_single (p := 2)
        (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (fun _ : ℕ => (1 : ℂ)) s
  have hy : ‖y‖ ^ 2 = (u.card : ℝ) := by
    simpa only [y, ENNReal.toReal_ofNat, Real.rpow_two, norm_one, one_pow, Finset.sum_const,
      nsmul_eq_mul, mul_one] using lp.norm_sum_single (p := 2)
        (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (fun _ : ℕ => (1 : ℂ)) u
  have hxp : 0 < ‖x‖ := by nlinarith [norm_nonneg x]
  have hyp : 0 < ‖y‖ := by nlinarith [norm_nonneg y]
  have hm := mul_le_mul hs hu hL.le (Nat.cast_nonneg (α := ℝ) s.card)
  have hb : L ≤ ‖x‖ * ‖y‖ := by
    apply (sq_le_sq₀ hL.le (mul_nonneg (norm_nonneg x) (norm_nonneg y))).mp
    calc
      L ^ 2 ≤ (s.card : ℝ) * (u.card : ℝ) := by simpa only [pow_two] using hm
      _ = (‖x‖ * ‖y‖) ^ 2 := by rw [← hx, ← hy]; ring
  have hform : inner ℂ x (A y) =
      ∑ n ∈ s, ∑ j ∈ u, A (lp.single 2 j (1 : ℂ)) n := by
    simp only [x, y, map_sum, sum_inner, inner_sum, lp.inner_single_left,
      RCLike.inner_apply, map_one, mul_one]
    exact Finset.sum_comm
  have hmass : a * (s.card : ℝ) * (u.card : ℝ) ≤ (inner ℂ x (A y)).re := by
    rw [hform, Complex.re_sum]
    simp_rw [Complex.re_sum]
    calc
      _ = ∑ _n ∈ s, ∑ _j ∈ u, a := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun j hj => he n hn j hj
  have hbound : (inner ℂ x (A y)).re ≤ ‖A‖ * (‖x‖ * ‖y‖) := by
    calc
      _ ≤ ‖inner ℂ x (A y)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖A y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖A‖ * ‖y‖) := mul_le_mul_of_nonneg_left (A.le_opNorm y) (norm_nonneg _)
      _ = _ := by ring
  have hc : (a * (‖x‖ * ‖y‖)) * (‖x‖ * ‖y‖) ≤ ‖A‖ * (‖x‖ * ‖y‖) := by
    calc
      _ = a * (s.card : ℝ) * (u.card : ℝ) := by rw [← hx, ← hy]; ring
      _ ≤ _ := hmass.trans hbound
  exact (mul_le_mul_of_nonneg_left hb ha).trans
    (le_of_mul_le_mul_right hc (mul_pos hxp hyp))

private theorem eventual_prime_rectangle_operator_bound
    (t : {t : ℝ // 1 / 2 ≤ t}) (A : ℕ → PaperWoldHistory →L[ℂ] PaperWoldHistory)
    (he : ∀ N, ∀ n ∈ paperWoldPrimeIndices N, ∀ j ∈ paperWoldPrimeIndices (2 * N),
      A N (lp.single 2 j (1 : ℂ)) n = paperWoldDirectedKernel t (n, j)) :
    ∀ᶠ N : ℕ in atTop, Real.log N / 8192 ≤ ‖A N‖ := by
  filter_upwards [paperWoldPrimeIndices_eventual_pair_card,
    paperWoldPrimeRectangle_eventual_lower t] with N hN hentry
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogp : 0 < Real.log (N : ℝ) := by linarith [hN.2.1]
  have h := finite_rectangle_norm_lower (A N) (paperWoldPrimeIndices N)
    (paperWoldPrimeIndices (2 * N)) ((N : ℝ) / (2 * Real.log N))
    (Real.log N ^ 2 / (4096 * (N : ℝ))) (by positivity) (by positivity) hN.2.2.1 hN.2.2.2
    (fun n hn j hj => by rw [he N n hn j hj]; exact hentry n hn j hj)
  have hc : (Real.log N ^ 2 / (4096 * (N : ℝ))) * ((N : ℝ) / (2 * Real.log N)) =
      Real.log N / 8192 := by
    field_simp
    ring
  rwa [hc] at h

/-- A globally admitted realization would have to dominate arbitrarily large prime blocks. -/
theorem paperWoldRealization_eventual_prime_norm_lower
    (t : {t : ℝ // 1 / 2 ≤ t}) (T : PaperWoldRealization t) :
    ∀ᶠ N : ℕ in atTop, Real.log N / 8192 ≤ ‖T.val‖ :=
  eventual_prime_rectangle_operator_bound t (fun _ => T.val)
    (fun _ n _ j _ => paperWoldRealization_single t T n j)

/-- Unconditional growth on the literal finite square cutoffs, with every original entry retained. -/
theorem paperWoldFiniteCutoff_eventual_prime_norm_lower (t : {t : ℝ // 1 / 2 ≤ t}) :
    ∀ᶠ N : ℕ in atTop,
      Real.log N / 8192 ≤ ‖paperWoldFiniteCutoff t (Finset.range (4 * N))‖ := by
  apply eventual_prime_rectangle_operator_bound t
  intro N n hn j hj
  have hnhi := ((paperWoldPrimeIndices_mem N n).mp hn).2.2
  have hjhi := ((paperWoldPrimeIndices_mem (2 * N) j).mp hj).2.2
  rw [paperWoldFiniteCutoff_single, if_pos]
  exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

theorem paperWoldFiniteCutoff_norm_atTop (t : {t : ℝ // 1 / 2 ≤ t}) :
    Tendsto (fun N : ℕ => ‖paperWoldFiniteCutoff t (Finset.range (4 * N))‖) atTop atTop :=
  tendsto_atTop_mono' atTop (paperWoldFiniteCutoff_eventual_prime_norm_lower t)
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num))

end
end RHTower
