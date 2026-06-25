/-
# Hurwitz N=2 — analyticity of the factored (cut-free) tail

The factored tail `tailFactored s k n` is analytic on the disk `{‖x‖ < 1/2}` (a nonempty open
`2πi`-pullback-deep left half-plane in `z`), discharging the `hanalytic` hypothesis of the N=2
`split_extend` continuation. Each term `(m−n)^{−(s+k)}·(1+x/(m−n))^{−(s+k)}` is holomorphic (its base
`1+x/(m−n)` sits in the right half-plane, hence the slit plane, where `z ↦ z^c` is holomorphic), and the
series converges by the Weierstrass M-test: `‖term_m‖ ≤ ‖(m−n)^{−(s+k)}‖·C`, summable via the parent's
`summable_hurwitzSeries` at shift `a = −n`.
-/
import GaloisForLFunctions.Hurwitz.N2Tail

open Complex HurwitzZetaShift

namespace HurwitzN2Tail

/-- **The factored tail is analytic on `{‖x‖ < 1/2}`** (for `1 < s.re`). Weierstrass M-test:
per-term holomorphy on the slit plane + a summable sup-norm bound. -/
theorem tailFactored_analytic {s : ℂ} (hs : 1 < s.re) (k n : ℕ) :
    AnalyticOnNhd ℂ (tailFactored s k n) {x : ℂ | ‖x‖ < 1 / 2} := by
  set c : ℂ := -(s + (k : ℂ)) with hc
  set U : Set ℂ := {x : ℂ | ‖x‖ < 1 / 2} with hU
  have hUopen : IsOpen U := by
    have : U = {x : ℂ | ‖x‖ < 1 / 2} := rfl
    rw [this]; exact isOpen_lt continuous_norm continuous_const
  -- exponent real/imag data
  have hcre : c.re = -(s.re + (k : ℝ)) := by rw [hc]; simp [Complex.add_re]
  have hcre_neg : c.re < 0 := by rw [hcre]; have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
  -- the uniform bound on the right-hand factor
  set C₁ : ℝ := (1 / 2 : ℝ) ^ c.re * Real.exp (Real.pi * ‖c‖) with hC₁
  have hC₁pos : 0 < C₁ := by
    apply mul_pos
    · exact Real.rpow_pos_of_pos (by norm_num) _
    · exact Real.exp_pos _
  -- per-term: m ≠ n ⟹ base in slit plane, term holomorphic, bounded
  have hbase_slit : ∀ {m : ℕ}, m ≠ n → ∀ {x : ℂ}, x ∈ U →
      (1 + x / ((m : ℂ) - (n : ℂ))) ∈ slitPlane := by
    intro m hm x hx
    refine mem_slitPlane_iff.mpr (Or.inl (tailTerm_base_re_pos hm ?_))
    have : ‖x‖ < 1 / 2 := hx
    linarith
  -- the term function
  set F : ℕ → ℂ → ℂ := fun m x =>
    if m = n then 0 else ((m : ℂ) - (n : ℂ)) ^ c * (1 + x / ((m : ℂ) - (n : ℂ))) ^ c with hF
  -- bound function
  set u : ℕ → ℝ := fun m => ‖((m : ℂ) - (n : ℂ)) ^ c‖ * C₁ with hu
  -- summability of u via summable_hurwitzSeries with a = -n
  have hsum_terms : Summable (fun m : ℕ => ((m : ℂ) + (-(n : ℂ))) ^ c) := by
    have := summable_hurwitzSeries (s := s + (k : ℂ))
      (by rw [Complex.add_re, Complex.natCast_re]
          have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
      (-(n : ℂ))
    simpa [hc] using this
  have hsum_norm : Summable (fun m : ℕ => ‖((m : ℂ) - (n : ℂ)) ^ c‖) := by
    have h2 : Summable (fun m : ℕ => ‖((m : ℂ) + (-(n : ℂ))) ^ c‖) := hsum_terms.norm
    refine h2.congr (fun m => ?_)
    rw [sub_eq_add_neg]
  have hsum_u : Summable u := hsum_norm.mul_right C₁
  -- per-term differentiability
  have hdiff : ∀ m : ℕ, DifferentiableOn ℂ (F m) U := by
    intro m
    by_cases hm : m = n
    · simp only [hF, hm, if_pos]; exact differentiableOn_const 0
    · intro x hx
      simp only [hF, if_neg hm]
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_mul
      have hb : (1 + x / ((m : ℂ) - (n : ℂ))) ∈ slitPlane := hbase_slit hm hx
      have haff : DifferentiableAt ℂ (fun y : ℂ => 1 + y / ((m : ℂ) - (n : ℂ))) x := by fun_prop
      exact ((hasStrictDerivAt_cpow_const hb).hasDerivAt.differentiableAt).comp x haff
  -- per-term sup-norm bound
  have hbound : ∀ m : ℕ, ∀ x ∈ U, ‖F m x‖ ≤ u m := by
    intro m x hx
    by_cases hm : m = n
    · simp only [hF, hm, if_pos, norm_zero, hu]
      positivity
    · simp only [hF, if_neg hm, hu, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      -- ‖(1+w)^c‖ ≤ C₁
      set w : ℂ := x / ((m : ℂ) - (n : ℂ)) with hw
      have hbre : 0 < (1 + w).re := tailTerm_base_re_pos hm (by have : ‖x‖ < 1/2 := hx; linarith)
      have hwlt : ‖w‖ < 1 / 2 := by
        rw [hw, norm_div]
        have hd1 : (1 : ℝ) ≤ ‖((m : ℂ) - (n : ℂ))‖ := by
          have hne : ((m : ℤ) - (n : ℤ)) ≠ 0 := fun h => hm (by omega)
          have hcast : ((m : ℂ) - (n : ℂ)) = (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) := by push_cast; ring
          rw [hcast, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hne
        calc ‖x‖ / ‖(m:ℂ)-(n:ℂ)‖ ≤ ‖x‖ / 1 := by
              apply div_le_div_of_nonneg_left (norm_nonneg x) (by norm_num) hd1
          _ = ‖x‖ := by ring
          _ < 1 / 2 := hx
      have hbnorm : (1 : ℝ) / 2 ≤ ‖1 + w‖ := by
        have h1 : ‖(1 : ℂ)‖ - ‖w‖ ≤ ‖1 + w‖ := by
          have := norm_sub_norm_le (1 : ℂ) (-w)
          simpa using this
        simp only [norm_one] at h1
        linarith
      calc ‖(1 + w) ^ c‖
          ≤ ‖1 + w‖ ^ c.re / Real.exp ((1 + w).arg * c.im) := norm_cpow_le _ _
        _ = ‖1 + w‖ ^ c.re * Real.exp (-((1 + w).arg * c.im)) := by
            rw [div_eq_mul_inv, ← Real.exp_neg]
        _ ≤ (1 / 2 : ℝ) ^ c.re * Real.exp (Real.pi * ‖c‖) := by
            apply mul_le_mul
            · exact Real.rpow_le_rpow_of_nonpos (by norm_num) hbnorm (le_of_lt hcre_neg)
            · apply Real.exp_le_exp.mpr
              have harg : |(1 + w).arg| ≤ Real.pi := abs_arg_le_pi _
              have hcim : |c.im| ≤ ‖c‖ := Complex.abs_im_le_norm c
              calc -((1 + w).arg * c.im) ≤ |(1 + w).arg * c.im| := neg_le_abs _
                _ = |(1 + w).arg| * |c.im| := abs_mul _ _
                _ ≤ Real.pi * ‖c‖ := mul_le_mul harg hcim (abs_nonneg _) Real.pi_pos.le
            · positivity
            · positivity
  -- assemble
  have hdiffOn : DifferentiableOn ℂ (fun x => ∑' m : ℕ, F m x) U :=
    differentiableOn_tsum_of_summable_norm hsum_u hdiff hUopen hbound
  have heq : (fun x => ∑' m : ℕ, F m x) = tailFactored s k n := by
    funext x; rfl
  rw [heq] at hdiffOn
  exact hdiffOn.analyticOnNhd hUopen

end HurwitzN2Tail
