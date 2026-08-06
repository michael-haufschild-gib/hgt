import GaloisForLFunctions.RHTower.HurwitzZetaRightAsymptotics
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Periodic Dirichlet series far to the right of the critical strip

For a periodic coefficient function the Dirichlet series `∑_{n ≥ 1} Θ(n) n^{-w}`
is dominated by its first non-vanishing term.  If `Θ(n) = 0` for `1 ≤ n < n₀`,
normalising by `n₀^{w}` turns the series into `∑_{n ≥ n₀} Θ(n) (n₀/n)^{w}`, whose
leading term is `Θ(n₀)` and whose tail is bounded by a fixed constant times
`(n₀/(n₀+1))^{Re w}`.

So `n₀^{w} L(Θ,w) → Θ(n₀)` as `Re w → ∞`: the series grows exactly like the
geometric factor `n₀^{-Re w}`, and `n₀` is the first exponent of the underlying
Dirichlet series.
-/

open Complex Filter Topology

namespace RHTower

section PeriodicRight

variable {N : ℕ} [NeZero N]

theorem exists_bound_zmod (Θ : ZMod N → ℂ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖Θ j‖ ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun j => ‖Θ j‖)).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun j => le_trans (hM ⟨j, rfl⟩) (le_max_left _ _)⟩

omit [NeZero N] in
theorem norm_scaled_term (Θ : ZMod N → ℂ) {M : ℝ} (hM : ∀ j, ‖Θ j‖ ≤ M)
    {n₀ m : ℕ} (hn₀ : 0 < n₀) (hm : 0 < m) (w : ℂ) :
    ‖(n₀ : ℂ) ^ w * LSeries.term (fun n : ℕ => Θ (n : ZMod N)) w m‖
      ≤ M * (((n₀ : ℝ)) / ((m : ℝ))) ^ w.re := by
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpow : (0 : ℝ) < ((m : ℝ)) ^ w.re := Real.rpow_pos_of_pos hmR _
  have hn₀pow : (0 : ℝ) < ((n₀ : ℝ)) ^ w.re := Real.rpow_pos_of_pos hn₀R _
  rw [LSeries.term_of_ne_zero hm.ne' _ _, norm_mul, norm_div,
    Complex.norm_natCast_cpow_of_pos hn₀ w,
    Complex.norm_natCast_cpow_of_pos hm w, Real.div_rpow hn₀R.le hmR.le]
  calc ((n₀ : ℝ)) ^ w.re * (‖Θ (m : ZMod N)‖ / ((m : ℝ)) ^ w.re)
      ≤ ((n₀ : ℝ)) ^ w.re * (M / ((m : ℝ)) ^ w.re) := by
        gcongr
        exact hM _
    _ = M * (((n₀ : ℝ)) ^ w.re / ((m : ℝ)) ^ w.re) := by ring

/-- **The tail of the normalized periodic Dirichlet series is geometrically
small.** -/
theorem norm_normalizedLFunction_sub_le (Θ : ZMod N → ℂ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, ‖Θ j‖ ≤ M) {n₀ : ℕ} (hn₀ : 0 < n₀)
    (hvanish : ∀ n : ℕ, 0 < n → n < n₀ → Θ (n : ZMod N) = 0) {w : ℂ} (hw : 2 ≤ w.re) :
    ‖(n₀ : ℂ) ^ w * ZMod.LFunction Θ w - Θ ((n₀ : ℕ) : ZMod N)‖
      ≤ (M * ((n₀ : ℝ)) ^ (2 : ℝ) * hurwitzTailConst)
        * (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2) := by
  have hw1 : 1 < w.re := by linarith
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  set f : ℕ → ℂ := fun n : ℕ => Θ (n : ZMod N) with hf
  set g : ℕ → ℂ := fun m : ℕ => (n₀ : ℂ) ^ w * LSeries.term f w m with hg
  have hcpow : ((n₀ : ℂ)) ^ w ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact_mod_cast hn₀.ne'
  have hLS : ZMod.LFunction Θ w = LSeries f w := ZMod.LFunction_eq_LSeries Θ hw1
  have hHS : HasSum g ((n₀ : ℂ) ^ w * ZMod.LFunction Θ w) := by
    rw [hLS]
    exact ((ZMod.LSeriesSummable_of_one_lt_re Θ hw1).LSeriesHasSum).mul_left _
  have hzero : ∀ i : ℕ, i < n₀ → g i = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hg]
      simp
    · rw [hg]
      simp only
      rw [LSeries.term_of_ne_zero hipos.ne' _ _]
      show (n₀ : ℂ) ^ w * (Θ ((i : ℕ) : ZMod N) / (i : ℂ) ^ w) = 0
      rw [hvanish i hipos hi, zero_div, mul_zero]
  have hshift : HasSum (fun m : ℕ => g (m + n₀))
      ((n₀ : ℂ) ^ w * ZMod.LFunction Θ w) := by
    refine (hasSum_nat_add_iff (f := g) n₀).mpr ?_
    have hsum0 : ∑ i ∈ Finset.range n₀, g i = 0 :=
      Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_range.mp hi)
    rw [hsum0, add_zero]
    exact hHS
  have hlead : g (0 + n₀) = Θ ((n₀ : ℕ) : ZMod N) := by
    rw [zero_add, hg]
    simp only
    rw [LSeries.term_of_ne_zero hn₀.ne' _ _]
    show (n₀ : ℂ) ^ w * (Θ ((n₀ : ℕ) : ZMod N) / (n₀ : ℂ) ^ w) = Θ ((n₀ : ℕ) : ZMod N)
    field_simp
  have htail : HasSum (fun m : ℕ => g (m + 1 + n₀))
      ((n₀ : ℂ) ^ w * ZMod.LFunction Θ w - Θ ((n₀ : ℕ) : ZMod N)) := by
    refine (hasSum_nat_add_iff (f := fun m : ℕ => g (m + n₀)) 1).mpr ?_
    have hs1 : ∑ i ∈ Finset.range 1, g (i + n₀) = Θ ((n₀ : ℕ) : ZMod N) := by
      rw [Finset.sum_range_one, hlead]
    rw [hs1, sub_add_cancel]
    exact hshift
  have hbnd : ∀ m : ℕ, ‖g (m + 1 + n₀)‖
      ≤ (M * ((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ))
        * (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2) := by
    intro m
    have hmpos : 0 < m + 1 + n₀ := by omega
    have hstep := norm_scaled_term Θ hM hn₀ hmpos w
    have hmR : ((m : ℝ) + 1 + (n₀ : ℝ)) = ((m + 1 + n₀ : ℕ) : ℝ) := by push_cast; ring
    have hden : (0 : ℝ) < ((m + 1 + n₀ : ℕ) : ℝ) := by exact_mod_cast hmpos
    have hratio0 : (0 : ℝ) ≤ ((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ) :=
      div_nonneg hn₀R.le hden.le
    have hratio1 : ((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ) ≤ ((n₀ : ℝ)) / ((n₀ : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left hn₀R.le (by linarith)
      rw [← hmR]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hsplit : (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ w.re
        = (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ (w.re - 2)
          * (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ (2 : ℝ) := by
      rw [← Real.rpow_add' hratio0 (by intro hc; linarith)]
      ring_nf
    have hfirst : (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ (w.re - 2)
        ≤ (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2) :=
      Real.rpow_le_rpow hratio0 hratio1 (by linarith)
    have hsecond : (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ (2 : ℝ)
        ≤ ((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ) := by
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hle : ((m : ℝ)) + 1 ≤ (((m + 1 + n₀ : ℕ)) : ℝ) := by
        rw [← hmR]
        linarith
      rw [Real.div_rpow hn₀R.le hden.le, Real.rpow_neg hm1.le, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos hn₀R _).le
      rw [inv_le_inv₀ (Real.rpow_pos_of_pos hden _) (Real.rpow_pos_of_pos hm1 _)]
      exact Real.rpow_le_rpow hm1.le hle (by norm_num)
    have hprod : (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ w.re
        ≤ (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2)
          * (((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ)) := by
      rw [hsplit]
      refine mul_le_mul hfirst hsecond (Real.rpow_nonneg hratio0 _) ?_
      exact Real.rpow_nonneg (div_nonneg hn₀R.le (by linarith)) _
    calc ‖g (m + 1 + n₀)‖ ≤ M * (((n₀ : ℝ)) / (((m + 1 + n₀ : ℕ)) : ℝ)) ^ w.re := hstep
      _ ≤ M * ((((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2)
            * (((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hprod hM0
      _ = (M * ((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ))
            * (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2) := by ring
  have hmajor : Summable (fun m : ℕ =>
      (M * ((n₀ : ℝ)) ^ (2 : ℝ) * (((m : ℝ)) + 1) ^ (-2 : ℝ))
        * (((n₀ : ℝ)) / ((n₀ : ℝ) + 1)) ^ (w.re - 2)) :=
    (summable_shifted_rpow_neg_two.mul_left _).mul_right _
  have hnormsum : Summable (fun m : ℕ => ‖g (m + 1 + n₀)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbnd hmajor
  rw [← htail.tsum_eq]
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  refine le_trans (Summable.tsum_le_tsum hbnd hnormsum hmajor) ?_
  rw [tsum_mul_right, tsum_mul_left, ← hurwitzTailConst]

/-- **The periodic Dirichlet series grows exactly geometrically to the right.** -/
theorem tendsto_normalizedLFunction (Θ : ZMod N → ℂ) {n₀ : ℕ} (hn₀ : 0 < n₀)
    (hvanish : ∀ n : ℕ, 0 < n → n < n₀ → Θ (n : ZMod N) = 0) (w₀ : ℂ) :
    Tendsto (fun k : ℕ => (n₀ : ℂ) ^ (w₀ + (k : ℂ)) * ZMod.LFunction Θ (w₀ + (k : ℂ)))
      atTop (𝓝 (Θ ((n₀ : ℕ) : ZMod N))) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_zmod Θ
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  set θ : ℝ := ((n₀ : ℝ)) / ((n₀ : ℝ) + 1) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one (by linarith)]
    linarith
  set K : ℝ := M * ((n₀ : ℝ)) ^ (2 : ℝ) * hurwitzTailConst with hKdef
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hre : ∀ k : ℕ, (w₀ + (k : ℂ)).re = w₀.re + (k : ℝ) := by
    intro k; simp
  have hgeom : Tendsto (fun k : ℕ => K * θ ^ (w₀.re + (k : ℝ) - 2)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => θ ^ (k : ℕ)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1
    have hsplit : ∀ k : ℕ, K * θ ^ (w₀.re + (k : ℝ) - 2)
        = (K * θ ^ (w₀.re - 2)) * θ ^ (k : ℕ) := by
      intro k
      rw [show w₀.re + (k : ℝ) - 2 = (w₀.re - 2) + (k : ℝ) from by ring,
        Real.rpow_add hθ0, ← Real.rpow_natCast θ k]
      ring
    have hlim := hpow.const_mul (K * θ ^ (w₀.re - 2))
    rw [mul_zero] at hlim
    exact hlim.congr fun k => (hsplit k).symm
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hgeom
  filter_upwards [eventually_ge_atTop (⌈2 - w₀.re⌉₊ + 1)] with k hk
  have hkR : ((⌈2 - w₀.re⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.le_of_succ_le hk
  have h2 : 2 ≤ (w₀ + (k : ℂ)).re := by
    rw [hre k]
    have hc := Nat.le_ceil (2 - w₀.re)
    linarith
  have hb := norm_normalizedLFunction_sub_le Θ hM0 hM hn₀ hvanish h2
  rw [hre k] at hb
  exact hb

end PeriodicRight

end RHTower
