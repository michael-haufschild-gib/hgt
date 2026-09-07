import GaloisForLFunctions.RHTower.MontgomeryPrimeSideBounds

/-!
# The prime side as a Dirichlet series in the height

The prime side of Montgomery's lemma is `e^{it log x} Σ_n d_n e^{−it log n}` with the real
non-negative amplitudes `d_n = Λ(n)(x/n)^{−1/2}` for `n ≤ x` and `d_n = Λ(n)(x/n)^{3/2}` for `n > x`
(so `d_n = √x · Λ(n) n^{−1/2} min(n/x, x/n)`).  Its modulus is that of the conjugate series
`Σ_n d_n e^{it log n}`, a Dirichlet series in the convention of the corpus's `dirPoly`.

This module records the amplitudes, the uniform majorant `d_n ≤ 4x^{3/2} n^{−5/4}`, summability,
continuity of the series in `t`, and the truncation tail.
-/

open Complex Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-- The amplitude `d_n = Λ(n)(x/n)^{−1/2}` (`n ≤ x`) or `Λ(n)(x/n)^{3/2}` (`n > x`). -/
noncomputable def primeAmp (x : ℝ) (n : ℕ) : ℝ :=
  vonMangoldt n * (if (n : ℝ) ≤ x then (x / n) ^ (-(1 / 2 : ℝ)) else (x / n) ^ ((3 / 2 : ℝ)))

theorem primeAmp_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ primeAmp x n := by
  unfold primeAmp
  have : 0 ≤ x / n := div_nonneg hx (Nat.cast_nonneg n)
  split_ifs <;> exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg this _)

theorem primeAmp_zero (x : ℝ) : primeAmp x 0 = 0 := by simp [primeAmp]

/-- `y^{σ+it} = y^σ e^{it log y}` for `y > 0`. -/
theorem cpow_ofReal_pos_eq {y : ℝ} (hy : 0 < y) (σ t : ℝ) :
    (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)
      = ((y ^ σ : ℝ) : ℂ) * Complex.exp (((t * Real.log y : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hy.le]
  have : (Real.log y : ℂ) * ((σ : ℂ) + (t : ℂ) * I)
      = ((Real.log y * σ : ℝ) : ℂ) + ((t * Real.log y : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_add, Real.rpow_def_of_pos hy, Complex.ofReal_exp]

/-- The prime-side summand is `e^{it log x} · d_n · e^{−it log n}`. -/
theorem primeSideTerm_eq_amp {x : ℝ} (hx : 0 < x) (t : ℝ) (n : ℕ) :
    primeSideTerm x t n = Complex.exp (((t * Real.log x : ℝ) : ℂ) * I)
      * ((primeAmp x n : ℂ) * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeSideTerm, primeAmp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < x / n := by positivity
  have hlog : Real.log (x / n) = Real.log x - Real.log n := Real.log_div hx.ne' hn'.ne'
  have hphase : Complex.exp (((t * Real.log (x / n) : ℝ) : ℂ) * I)
      = Complex.exp (((t * Real.log x : ℝ) : ℂ) * I)
        * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_add, hlog]; congr 1; push_cast; ring
  unfold primeSideTerm primeAmp
  split_ifs with h
  · rw [show montgomeryPoleDown t = ((-(1 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * I by
      simp [montgomeryPoleDown]; norm_num, cpow_ofReal_pos_eq hy, hphase]
    push_cast; ring
  · rw [show montgomeryPoleUp t = (((3 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * I by simp [montgomeryPoleUp],
      cpow_ofReal_pos_eq hy, hphase]
    push_cast; ring

/-- The uniform majorant `d_n ≤ 4 x^{3/2} n^{−5/4}` for `x ≥ 1`. -/
theorem primeAmp_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    primeAmp x n ≤ 4 * x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primeAmp]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hΛ : vonMangoldt n ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := by
    refine (ArithmeticFunction.vonMangoldt_le_log).trans ?_
    have := Real.log_le_rpow_div hn'.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [div_eq_mul_inv, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at this
    linarith
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  unfold primeAmp
  split_ifs with h
  · -- `n ≤ x`: `(x/n)^{−1/2} ≤ 1` and `4 n^{1/4} ≤ 4 x^{3/2} n^{−5/4}`
    have h1 : (x / n) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by rw [le_div_iff₀ hn']; linarith) (by norm_num)
    have h2 : (n : ℝ) ^ ((1 / 4 : ℝ)) ≤ x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
      rw [← Real.rpow_neg hn'.le, ← div_le_iff₀ (Real.rpow_pos_of_pos hn' _),
        div_eq_mul_inv, ← Real.rpow_neg hn'.le, ← Real.rpow_add hn']
      norm_num
      exact Real.rpow_le_rpow hn'.le h (by norm_num)
    calc vonMangoldt n * (x / n) ^ (-(1 / 2 : ℝ)) ≤ vonMangoldt n * 1 :=
          mul_le_mul_of_nonneg_left h1 hΛ0
      _ = vonMangoldt n := mul_one _
      _ ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := hΛ
      _ ≤ 4 * (x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹) := by gcongr
      _ = 4 * x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by ring
  · -- `n > x`: `(x/n)^{3/2} = x^{3/2} n^{−3/2}`
    rw [Real.div_rpow hx0.le hn'.le]
    have hpos := Real.rpow_pos_of_pos hn' (3 / 2 : ℝ)
    calc vonMangoldt n * (x ^ ((3 / 2 : ℝ)) / (n : ℝ) ^ ((3 / 2 : ℝ)))
        ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) * (x ^ ((3 / 2 : ℝ)) / (n : ℝ) ^ ((3 / 2 : ℝ))) := by
          gcongr
      _ = 4 * x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((1 / 4 : ℝ)) / (n : ℝ) ^ ((3 / 2 : ℝ))) := by ring
      _ = 4 * x ^ ((3 / 2 : ℝ)) * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
          rw [← Real.rpow_sub hn', ← Real.rpow_neg hn'.le]; norm_num

theorem summable_primeAmp {x : ℝ} (hx : 1 ≤ x) : Summable (primeAmp x) :=
  Summable.of_nonneg_of_le (primeAmp_nonneg (by linarith)) (primeAmp_le hx)
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)).mul_left _)

/-- The total amplitude `S₀ = Σ_n d_n`. -/
noncomputable def primeAmpTotal (x : ℝ) : ℝ := ∑' n : ℕ, primeAmp x n

theorem primeAmpTotal_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ primeAmpTotal x := tsum_nonneg (primeAmp_nonneg hx)

/-! ## The phase series -/

/-- The phase series `Σ_n d_n e^{it log n}`. -/
noncomputable def primePhaseSum (x t : ℝ) : ℂ :=
  ∑' n : ℕ, (primeAmp x n : ℂ) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)

/-- The conjugate phase series `Σ_n d_n e^{−it log n}`. -/
noncomputable def primeConjSum (x t : ℝ) : ℂ :=
  ∑' n : ℕ, (primeAmp x n : ℂ) * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))

theorem norm_phaseTerm {x : ℝ} (hx : 0 ≤ x) (t : ℝ) (n : ℕ) :
    ‖(primeAmp x n : ℂ) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)‖ = primeAmp x n := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeAmp_nonneg hx n)]

theorem norm_conjTerm {x : ℝ} (hx : 0 ≤ x) (t : ℝ) (n : ℕ) :
    ‖(primeAmp x n : ℂ) * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))‖ = primeAmp x n := by
  rw [norm_mul, show -(((t * Real.log n : ℝ) : ℂ) * I) = ((-(t * Real.log n) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primeAmp_nonneg hx n)]

theorem summable_phaseTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun n : ℕ => (primeAmp x n : ℂ) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)) :=
  Summable.of_norm_bounded (summable_primeAmp hx) (fun n => (norm_phaseTerm (by linarith) t n).le)

theorem summable_conjTerm {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    Summable (fun n : ℕ => (primeAmp x n : ℂ) * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))) :=
  Summable.of_norm_bounded (summable_primeAmp hx) (fun n => (norm_conjTerm (by linarith) t n).le)

/-- `primeSide x t = e^{it log x} · Σ_n d_n e^{−it log n}`. -/
theorem primeSide_eq_conjSum {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    primeSide x t = Complex.exp (((t * Real.log x : ℝ) : ℂ) * I) * primeConjSum x t := by
  rw [primeSide, primeConjSum, ← tsum_mul_left]
  exact tsum_congr fun n => primeSideTerm_eq_amp (by linarith) t n

theorem conj_primeConjSum (x t : ℝ) : (starRingEnd ℂ) (primeConjSum x t) = primePhaseSum x t := by
  rw [primeConjSum, primePhaseSum, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

/-- `‖primeSide x t‖ = ‖Σ_n d_n e^{it log n}‖`. -/
theorem norm_primeSide_eq {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖primeSide x t‖ = ‖primePhaseSum x t‖ := by
  rw [primeSide_eq_conjSum hx, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    ← Complex.norm_conj, conj_primeConjSum]

theorem norm_primePhaseSum_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖primePhaseSum x t‖ ≤ primeAmpTotal x := by
  rw [primePhaseSum, primeAmpTotal]
  have hx0 : (0 : ℝ) ≤ x := by linarith
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simp_rw [norm_phaseTerm hx0]; exact summable_primeAmp hx
  · simp_rw [norm_phaseTerm hx0]; exact le_rfl

theorem continuous_primePhaseSum {x : ℝ} (hx : 1 ≤ x) : Continuous (primePhaseSum x) := by
  unfold primePhaseSum
  refine continuous_tsum (fun n => ?_) (summable_primeAmp hx)
    (fun n t => (norm_phaseTerm (by linarith) t n).le)
  fun_prop

/-! ## Truncation -/

/-- The truncated phase sum `Σ_{n<N} d_n e^{it log n}`. -/
noncomputable def primePhasePartial (x : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, (primeAmp x n : ℂ) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)

/-- The tail amplitude `τ_N = Σ_{n≥N} d_n`. -/
noncomputable def primeAmpTail (x : ℝ) (N : ℕ) : ℝ := ∑' k : ℕ, primeAmp x (k + N)

theorem primeAmpTail_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : 0 ≤ primeAmpTail x N :=
  tsum_nonneg fun _ => primeAmp_nonneg hx _

theorem tendsto_primeAmpTail (x : ℝ) : Tendsto (primeAmpTail x) atTop (nhds 0) :=
  tendsto_sum_nat_add (primeAmp x)

/-- `‖P(t) − P_N(t)‖ ≤ τ_N`. -/
theorem norm_primePhaseSum_sub_partial_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) (t : ℝ) :
    ‖primePhaseSum x t - primePhasePartial x N t‖ ≤ primeAmpTail x N := by
  have hs := summable_phaseTerm hx t
  have hsplit := hs.sum_add_tsum_nat_add N
  rw [primePhaseSum, primePhasePartial, ← hsplit, add_sub_cancel_left, primeAmpTail]
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs' : Summable (fun k : ℕ => ‖(primeAmp x (k + N) : ℂ)
      * Complex.exp (((t * Real.log (k + N : ℕ) : ℝ) : ℂ) * I)‖) := by
    simp_rw [norm_phaseTerm hx0]
    exact (summable_primeAmp hx).comp_injective (add_left_injective N)
  refine (norm_tsum_le_tsum_norm hs').trans ?_
  simp_rw [norm_phaseTerm hx0]
  exact le_rfl

theorem norm_primePhasePartial_le {x : ℝ} (hx : 1 ≤ x) (N : ℕ) (t : ℝ) :
    ‖primePhasePartial x N t‖ ≤ primeAmpTotal x := by
  rw [primePhasePartial]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_phaseTerm (by linarith : (0 : ℝ) ≤ x)]
  exact (summable_primeAmp hx).sum_le_tsum _ (fun n _ => primeAmp_nonneg (by linarith) n)

end RHTower
