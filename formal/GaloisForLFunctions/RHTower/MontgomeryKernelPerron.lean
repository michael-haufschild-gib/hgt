import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The Montgomery kernel on the line `Re s = 2`: Perron evaluations and the Dirichlet side

Montgomery's lemma behind the pair-correlation form pairs `−ζ'/ζ` against the rational kernel

`K_t(s) = x^{s} · (−2)/((s − a)(s − b))`,  `a = 3/2 + it`,  `b = −1/2 + it`,

whose two poles straddle the critical line at height `t`; note `a − b = 2` and
`(−2)/((s−a)(s−b)) = 2/(1 − (s − s₀)²)` with `s₀ = 1/2 + it`.  On the line `Re s = 2` both
poles lie to the left, so the generic two-pole Perron window evaluates every rational term of the
Mittag-Leffler expansion.  This module provides the kernel, its integrability, the two- and
three-pole Perron evaluations, and the **Dirichlet side**

`(1/2π) ∫ (Σ_n Λ(n) n^{−s}) K_t(s) dt' = −Σ_{n ≤ x} Λ(n) ((x/n)^{a} − (x/n)^{b})`,

the terms with `n = x` vanishing.  The Mittag-Leffler side and the assembly into Montgomery's
identity live in `MontgomeryLemmaOne`.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The upper Montgomery pole `a = 3/2 + it`. -/
def montgomeryPoleUp (t : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I

/-- The lower Montgomery pole `b = −1/2 + it`. -/
def montgomeryPoleDown (t : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I

theorem montgomeryPoleUp_re (t : ℝ) : (montgomeryPoleUp t).re = 3 / 2 := by
  simp [montgomeryPoleUp]

theorem montgomeryPoleDown_re (t : ℝ) : (montgomeryPoleDown t).re = -1 / 2 := by
  simp [montgomeryPoleDown]

theorem montgomeryPoleUp_im (t : ℝ) : (montgomeryPoleUp t).im = t := by
  simp [montgomeryPoleUp]

theorem montgomeryPoleDown_im (t : ℝ) : (montgomeryPoleDown t).im = t := by
  simp [montgomeryPoleDown]

theorem montgomeryPoleUp_re_lt (t : ℝ) : (montgomeryPoleUp t).re < 2 := by
  rw [montgomeryPoleUp_re]; norm_num

theorem montgomeryPoleDown_re_lt (t : ℝ) : (montgomeryPoleDown t).re < 2 := by
  rw [montgomeryPoleDown_re]; norm_num

theorem montgomeryPoleUp_sub_down (t : ℝ) : montgomeryPoleUp t - montgomeryPoleDown t = 2 := by
  unfold montgomeryPoleUp montgomeryPoleDown
  push_cast
  ring

theorem montgomeryPoleUp_ne_down (t : ℝ) : montgomeryPoleUp t ≠ montgomeryPoleDown t := by
  intro h
  have := congrArg Complex.re h
  rw [montgomeryPoleUp_re, montgomeryPoleDown_re] at this
  norm_num at this

/-- The Montgomery kernel on the line `Re s = 2`, as a function of the height `τ`. -/
def montgomeryLineKernel (x : ℝ) (t : ℝ) (τ : ℝ) : ℂ :=
  (-2) * ((x : ℂ) ^ lineTwo τ /
    ((lineTwo τ - montgomeryPoleUp t) * (lineTwo τ - montgomeryPoleDown t)))

theorem lineTwo_eq (τ : ℝ) : lineTwo τ = ((2 : ℝ) : ℂ) + τ * I := rfl

theorem integrable_montgomeryLineKernel {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Integrable (montgomeryLineKernel x t) := by
  have := (integrable_cpow_div_twoPole (σ := 2) (montgomeryPoleUp_re_lt t)
    (montgomeryPoleDown_re_lt t) hx).const_mul (-2 : ℂ)
  exact this

/-- **Two-pole evaluation**: `(1/2π)∫ K_t = −(x^{a} − x^{b})` for `x > 1`. -/
theorem perron_montgomery_basic {x : ℝ} (hx : 1 < x) (t : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, montgomeryLineKernel x t τ
      = -((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t) := by
  have h := perron_twoPole (σ := 2) (montgomeryPoleUp_re_lt t) (montgomeryPoleDown_re_lt t)
    (montgomeryPoleUp_ne_down t) (show 0 < x by linarith)
  rw [if_pos hx] at h
  unfold montgomeryLineKernel
  rw [integral_const_mul, Complex.real_smul] at *
  calc ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((-2) * ∫ τ : ℝ, (x : ℂ) ^ lineTwo τ /
        ((lineTwo τ - montgomeryPoleUp t) * (lineTwo τ - montgomeryPoleDown t)))
      = (-2) * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ τ : ℝ, (x : ℂ) ^ lineTwo τ /
        ((lineTwo τ - montgomeryPoleUp t) * (lineTwo τ - montgomeryPoleDown t))) := by ring
    _ = (-2) * (((x : ℂ) ^ montgomeryPoleUp t - (x : ℂ) ^ montgomeryPoleDown t) /
        (montgomeryPoleUp t - montgomeryPoleDown t)) := by rw [← h]; rfl
    _ = _ := by rw [montgomeryPoleUp_sub_down]; ring

/-- **Three-pole evaluation**: for a third pole `c` left of the line, distinct from `a`, `b`,
`(1/2π)∫ K_t(s)/(s − c) = −((x^c − x^a)/(c−a) − (x^c − x^b)/(c−b))`. -/
theorem perron_montgomery_threePole {x : ℝ} (hx : 1 < x) (t : ℝ) {c : ℂ} (hc : c.re < 2)
    (hca : c ≠ montgomeryPoleUp t) (hcb : c ≠ montgomeryPoleDown t) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, montgomeryLineKernel x t τ / (lineTwo τ - c)
      = -(((x : ℂ) ^ c - (x : ℂ) ^ montgomeryPoleUp t) / (c - montgomeryPoleUp t) -
          ((x : ℂ) ^ c - (x : ℂ) ^ montgomeryPoleDown t) / (c - montgomeryPoleDown t)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hare := montgomeryPoleUp_re_lt t
  have hbre := montgomeryPoleDown_re_lt t
  have hab := montgomeryPoleUp_sub_down t
  have hsa : ∀ τ : ℝ, lineTwo τ - montgomeryPoleUp t ≠ 0 := lineTwo_sub_ne_zero hare
  have hsc : ∀ τ : ℝ, lineTwo τ - c ≠ 0 := lineTwo_sub_ne_zero hc
  -- partial fractions: (−2)/((s−a)(s−b)(s−c)) = −[1/((s−c)(s−a)) − 1/((s−c)(s−b))]
  have hsplit : ∀ τ : ℝ, montgomeryLineKernel x t τ / (lineTwo τ - c)
      = -((x : ℂ) ^ lineTwo τ / ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleUp t))
          - (x : ℂ) ^ lineTwo τ / ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleDown t))) := by
    intro τ
    unfold montgomeryLineKernel
    have h1 := hsa τ
    have h3 := hsc τ
    have hab' : lineTwo τ - montgomeryPoleDown t = lineTwo τ - montgomeryPoleUp t + 2 := by
      rw [← hab]; ring
    have h2 : lineTwo τ - montgomeryPoleUp t + 2 ≠ 0 := by
      rw [← hab']; exact lineTwo_sub_ne_zero hbre τ
    rw [hab']
    field_simp
    ring
  simp_rw [hsplit]
  have hI1 : Integrable (fun τ : ℝ => (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleUp t))) :=
    integrable_cpow_div_twoPole (σ := 2) hc hare hx0
  have hI2 : Integrable (fun τ : ℝ => (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleDown t))) :=
    integrable_cpow_div_twoPole (σ := 2) hc hbre hx0
  have hP1 : (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleUp t))
      = ((x : ℂ) ^ c - (x : ℂ) ^ montgomeryPoleUp t) / (c - montgomeryPoleUp t) := by
    have h := perron_twoPole (σ := 2) hc hare hca hx0
    rw [if_pos hx] at h
    exact h
  have hP2 : (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, (x : ℂ) ^ lineTwo τ /
      ((lineTwo τ - c) * (lineTwo τ - montgomeryPoleDown t))
      = ((x : ℂ) ^ c - (x : ℂ) ^ montgomeryPoleDown t) / (c - montgomeryPoleDown t) := by
    have h := perron_twoPole (σ := 2) hc hbre hcb hx0
    rw [if_pos hx] at h
    exact h
  rw [integral_neg, integral_sub hI1 hI2, smul_neg, smul_sub, hP1, hP2]

/-- Below the cutoff the kernel integral vanishes. -/
theorem integral_montgomeryLineKernel_of_not_one_lt {y : ℝ} (hy : 0 < y) (hy1 : ¬ 1 < y) (t : ℝ) :
    ∫ τ : ℝ, montgomeryLineKernel y t τ = 0 := by
  have h := perron_twoPole (σ := 2) (montgomeryPoleUp_re_lt t) (montgomeryPoleDown_re_lt t)
    (montgomeryPoleUp_ne_down t) hy
  rw [if_neg hy1, Complex.real_smul] at h
  have hπ : ((1 / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 / (2 * Real.pi) : ℝ) ≠ 0 by positivity)
  have h' : ∫ τ : ℝ, (y : ℂ) ^ lineTwo τ /
      ((lineTwo τ - montgomeryPoleUp t) * (lineTwo τ - montgomeryPoleDown t)) = 0 :=
    (mul_eq_zero.mp h).resolve_left hπ
  unfold montgomeryLineKernel
  rw [integral_const_mul, h', mul_zero]

/-! ## The Dirichlet side -/

/-- The `n`-th Dirichlet term against the Montgomery kernel. -/
def montgomeryDirichletTerm (x : ℝ) (t : ℝ) (n : ℕ) (τ : ℝ) : ℂ :=
  LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) (lineTwo τ) n * montgomeryLineKernel x t τ

theorem montgomeryDirichletTerm_eq {x : ℝ} (hx : 0 < x) (t : ℝ) {n : ℕ} (hn : n ≠ 0) (τ : ℝ) :
    montgomeryDirichletTerm x t n τ =
      ((vonMangoldt n : ℝ) : ℂ) * montgomeryLineKernel (x / n) t τ := by
  unfold montgomeryDirichletTerm montgomeryLineKernel
  rw [LSeries.term_of_ne_zero hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcp : (((x / n : ℝ) : ℂ) ^ lineTwo τ) = (x : ℂ) ^ lineTwo τ / (n : ℂ) ^ lineTwo τ := by
    rw [show (x / n : ℝ) = x * (n : ℝ)⁻¹ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hx.le (by positivity), Complex.ofReal_inv,
      Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by
        rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hn0.le]
        exact Real.pi_pos.ne'.symm)]
    exact (div_eq_mul_inv _ _).symm
  rw [hcp]
  ring

theorem montgomeryDirichletTerm_zero (x t τ : ℝ) : montgomeryDirichletTerm x t 0 τ = 0 := by
  unfold montgomeryDirichletTerm; rw [LSeries.term_zero, zero_mul]

theorem integrable_montgomeryDirichletTerm {x : ℝ} (hx : 0 < x) (t : ℝ) (n : ℕ) :
    Integrable (montgomeryDirichletTerm x t n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : montgomeryDirichletTerm x t 0 = fun _ => 0 :=
      funext (montgomeryDirichletTerm_zero x t)
    rw [h0]; exact integrable_zero _ _ _
  · have hn0 : n ≠ 0 := hn.ne'
    have hXn : (0 : ℝ) < x / n := by positivity
    have := (integrable_montgomeryLineKernel hXn t).const_mul ((vonMangoldt n : ℝ) : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    rw [montgomeryDirichletTerm_eq hx t hn0]

/-- The kernel norm splits off the scale: `‖K(x/n)‖ = (x/n)² ‖K(1)‖`. -/
theorem norm_montgomeryLineKernel_eq {y : ℝ} (hy : 0 < y) (t τ : ℝ) :
    ‖montgomeryLineKernel y t τ‖ = y ^ 2 * ‖montgomeryLineKernel 1 t τ‖ := by
  simp only [montgomeryLineKernel, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    lineTwo_re, Complex.ofReal_one, Complex.one_cpow, norm_one]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

theorem integral_norm_montgomeryDirichletTerm {x : ℝ} (hx : 0 < x) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∫ τ : ℝ, ‖montgomeryDirichletTerm x t n τ‖ =
      vonMangoldt n * (x / n) ^ 2 * ∫ τ : ℝ, ‖montgomeryLineKernel 1 t τ‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hXn : (0 : ℝ) < x / n := by positivity
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  beta_reduce
  rw [montgomeryDirichletTerm_eq hx t hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_montgomeryLineKernel_eq hXn]
  ring

theorem summable_integral_norm_montgomeryDirichletTerm {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Summable (fun n : ℕ => ∫ τ : ℝ, ‖montgomeryDirichletTerm x t n τ‖) := by
  set C : ℝ := ∫ τ : ℝ, ‖montgomeryLineKernel 1 t τ‖
  have hbase : Summable (fun n : ℕ => (x ^ 2 * C) * (vonMangoldt n / (n : ℝ) ^ 2)) :=
    summable_vonMangoldt_div_sq.mul_left _
  refine hbase.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [montgomeryDirichletTerm_zero]
  · rw [integral_norm_montgomeryDirichletTerm hx t hn.ne']
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

/-- **The Dirichlet side.**
`(1/2π)∫ (Σ_n Λ(n) n^{−s}) K_t(s) dτ = −Σ_{n ≤ x} Λ(n) ((x/n)^{a} − (x/n)^{b})`. -/
theorem montgomery_dirichlet_side {x : ℝ} (hx : 1 < x) (t : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo τ) *
        montgomeryLineKernel x t τ
      = -∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((vonMangoldt n : ℝ) : ℂ) *
          (((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t) := by
  have hx0 : 0 < x := by linarith
  have hint : (fun τ : ℝ => LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (lineTwo τ) *
      montgomeryLineKernel x t τ) = fun τ : ℝ => ∑' n : ℕ, montgomeryDirichletTerm x t n τ := by
    funext τ
    unfold LSeries montgomeryDirichletTerm
    rw [tsum_mul_right]
  rw [hint, ← integral_tsum_of_summable_integral_norm (integrable_montgomeryDirichletTerm hx0 t)
    (summable_integral_norm_montgomeryDirichletTerm hx0 t)]
  -- termwise evaluation
  have hterm : ∀ n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, montgomeryDirichletTerm x t n τ =
      ((vonMangoldt n : ℝ) : ℂ) * (if 1 < x / n then
        -(((x / n : ℝ) : ℂ) ^ montgomeryPoleUp t - ((x / n : ℝ) : ℂ) ^ montgomeryPoleDown t)
        else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [montgomeryDirichletTerm_zero]
    · have hn0 : n ≠ 0 := hn.ne'
      have hXn : (0 : ℝ) < x / n := by positivity
      have hI : ∫ τ : ℝ, montgomeryDirichletTerm x t n τ = ((vonMangoldt n : ℝ) : ℂ) *
          ∫ τ : ℝ, montgomeryLineKernel (x / n) t τ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun τ =>
          montgomeryDirichletTerm_eq hx0 t hn0 τ)
      rw [hI, Complex.real_smul]
      by_cases h1 : 1 < x / n
      · rw [if_pos h1]
        have hB := perron_montgomery_basic h1 t
        rw [Complex.real_smul] at hB
        calc ((1 / (2 * Real.pi) : ℝ) : ℂ) * (((vonMangoldt n : ℝ) : ℂ) *
              ∫ τ : ℝ, montgomeryLineKernel (x / n) t τ)
            = ((vonMangoldt n : ℝ) : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              ∫ τ : ℝ, montgomeryLineKernel (x / n) t τ) := by ring
          _ = _ := by rw [hB]
      · rw [if_neg h1, mul_zero, integral_montgomeryLineKernel_of_not_one_lt hXn h1 t, mul_zero,
          mul_zero]
  have hsmul : (1 / (2 * Real.pi) : ℝ) • ∑' n : ℕ, ∫ τ : ℝ, montgomeryDirichletTerm x t n τ
      = ∑' n : ℕ, (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, montgomeryDirichletTerm x t n τ := by
    rw [Complex.real_smul, ← tsum_mul_left]
    exact tsum_congr fun n => Complex.real_smul.symm
  rw [hsmul]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊), ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hnX : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le hx0.le)
    by_cases h : 1 < x / n
    · rw [if_pos h]; ring
    · rw [if_neg h]
      have hle : x / n ≤ 1 := not_lt.mp h
      have heq : x / n = 1 := le_antisymm hle (by rw [le_div_iff₀ hn0]; linarith)
      rw [heq]
      simp
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · have hgt : ¬ (1 < x / n) := by
        intro h1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
        rw [one_lt_div hn0] at h1
        exact hn ⟨hnpos, Nat.le_floor h1.le⟩
      rw [if_neg hgt, mul_zero]

end

end RHTower
