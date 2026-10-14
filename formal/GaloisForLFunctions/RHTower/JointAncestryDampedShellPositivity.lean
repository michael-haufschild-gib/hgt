import GaloisForLFunctions.RHTower.JointAncestryDampedShellCriterion
import GaloisForLFunctions.RHTower.ExponentialWeilFormDichotomy

/-!
# A sparse Weil positivity criterion on damped shells

For the shell `(N, 2N]` let `V_s(N) = U_s(N)/(s+1)²` (`jasShellDampedSum`) and

`F_N(z) = Σ_ρ e^{z V_ρ(N) + z̄ V_{1−ρ}(N)}/(ρ(1−ρ))`   (`jasShellDampedWeilForm`).

With `ĝ_z(s) = e^{z V_s(N)}/s` and `ĝ^♯(s) = conj ĝ(1 − s̄)` this is the Weil form
`Σ_ρ ĝ_z(ρ) ĝ_z^♯(ρ)`, restricted to a two-real-parameter exponential family of test functions.

**Theorem** (`riemannHypothesis_iff_shellDamped_weilPositive`,
`riemannHypothesis_iff_forall_shellDamped_weilPositive`).

`RH ⟺ ∃ᶠ N, ∀ z ∈ ℂ, Re F_N(z) ≥ 0 ⟺ ∀ N, ∀ z ∈ ℂ, Re F_N(z) ≥ 0`.

**Proof.**  The shell values form a detecting family for the exponential Weil-form dichotomy
(`riemannHypothesis_iff_frequently_expWeilForm_nonneg`):
* `|U_s(N)| ≤ Σ_{N<p≤2N} p^{−1/2}` in the strip and `|s+1|² ≥ 1 + (Im s)²`, so the shell values
  are bounded and every loud set is finite;
* one of `|V_ρ|`, `|V_{1−ρ}|` is at most `1`, since `Σ_{N<p≤2N} 1/p ≤ 1`;
* under RH, `1 − ρ = ρ̄` and `V_{conj s} = conj V_s`;
* a zero right of the line has `|U_ρ(N)| > N^{δ/2}` on every large shell
  (`eventually_lt_norm_jasShellUniformSum`).

At an off-line zero the shell sum is, to leading order, its prime number theorem main term, i.e.
the pole shadow `N^{ρ−½}/(ρ+1)²` of `poleShadowWeilForm` up to a bounded factor.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- The damped shell Weil form `F_N(z) = Σ_ρ e^{z V_ρ(N) + z̄ V_{1−ρ}(N)}/(ρ(1−ρ))`. -/
def jasShellDampedWeilForm (N : ℕ) (z : ℂ) : ℂ :=
  expWeilForm (fun q => jasShellDampedSum N (q.1 : ℂ))
    (fun q => jasShellDampedSum N (1 - (q.1 : ℂ))) z

/-! ## Bounds -/

theorem norm_jasShellUniformSum_le_halfMass_of_re_le_one (N : ℕ) {s : ℂ} (hs : s.re ≤ 1) :
    ‖jasShellUniformSum N s‖ ≤ jasShellHalfMass N :=
  (norm_jasShellUniformSum_le N s).trans
    (Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti (by linarith) p)

theorem norm_jasShellDampedSum_le_of_re (N : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖jasShellDampedSum N s‖ ≤ jasShellHalfMass N / (1 + s.im ^ 2) := by
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rw [jasShellDampedSum, norm_div, norm_pow]
  calc ‖jasShellUniformSum N s‖ / ‖s + 1‖ ^ 2
      ≤ jasShellHalfMass N / ‖s + 1‖ ^ 2 :=
        div_le_div_of_nonneg_right (norm_jasShellUniformSum_le_halfMass_of_re_le_one N h1)
          (by positivity)
    _ ≤ jasShellHalfMass N / (1 + s.im ^ 2) :=
        div_le_div_of_nonneg_left (jasShellHalfMass_nonneg N) hpos
          (one_add_im_sq_le_norm_add_one_sq h0)

theorem norm_jasShellDampedSum_le_one_of_re (N : ℕ) {s : ℂ} (h0 : 0 ≤ s.re) (h : s.re ≤ 1 / 2) :
    ‖jasShellDampedSum N s‖ ≤ 1 := by
  have h1 := norm_jasShellUniformSum_le_one (N := N) h
  have h3 : 1 ≤ ‖s + 1‖ ^ 2 :=
    (by nlinarith [sq_nonneg s.im] : (1 : ℝ) ≤ 1 + s.im ^ 2).trans
      (one_add_im_sq_le_norm_add_one_sq h0)
  rw [jasShellDampedSum, norm_div, norm_pow, div_le_one (by linarith)]
  linarith

theorem norm_jasShellDampedSum_xiZeroCopy_le (N : ℕ) (q : XiZeroCopy) :
    ‖jasShellDampedSum N (q.1 : ℂ)‖ ≤ jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) ∧
      ‖jasShellDampedSum N (1 - (q.1 : ℂ))‖ ≤ jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) := by
  obtain ⟨h2, h3⟩ := re_one_sub_xiZeroCopy_mem q
  refine ⟨norm_jasShellDampedSum_le_of_re N (xiZeroCopy_re_pos q).le
    (xiZeroCopy_re_lt_one q).le, ?_⟩
  have := norm_jasShellDampedSum_le_of_re N h2 h3
  have him : (1 - (q.1 : ℂ)).im ^ 2 = (q.1 : ℂ).im ^ 2 := by simp
  rwa [him] at this

/-- The shell values are a detecting family: bounded, one side at most `1`, finite loud sets. -/
theorem jasShellDamped_bounds (N : ℕ) :
    (∃ C : ℝ, ∀ q : XiZeroCopy, ‖jasShellDampedSum N (q.1 : ℂ)‖ ≤ C ∧
      ‖jasShellDampedSum N (1 - (q.1 : ℂ))‖ ≤ C) ∧
    (∀ q : XiZeroCopy, ‖jasShellDampedSum N (q.1 : ℂ)‖ ≤ 1 ∨
      ‖jasShellDampedSum N (1 - (q.1 : ℂ))‖ ≤ 1) ∧
    {q : XiZeroCopy | 1 < ‖jasShellDampedSum N (q.1 : ℂ) +
      conj (jasShellDampedSum N (1 - (q.1 : ℂ)))‖}.Finite := by
  refine ⟨⟨jasShellHalfMass N, fun q => ?_⟩, fun q => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := norm_jasShellDampedSum_xiZeroCopy_le N q
    have h3 : jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) ≤ jasShellHalfMass N :=
      div_le_self (jasShellHalfMass_nonneg N) (by nlinarith [sq_nonneg (q.1 : ℂ).im])
    exact ⟨h1.trans h3, h2.trans h3⟩
  · by_cases h : (q.1 : ℂ).re ≤ 1 / 2
    · exact Or.inl (norm_jasShellDampedSum_le_one_of_re N (xiZeroCopy_re_pos q).le h)
    · push Not at h
      refine Or.inr (norm_jasShellDampedSum_le_one_of_re N (re_one_sub_xiZeroCopy_mem q).1 ?_)
      simp only [Complex.sub_re, Complex.one_re]
      linarith
  · refine (finite_xiZeroCopy_band 0 (r := √(2 * jasShellHalfMass N))
      (Real.sqrt_nonneg _)).subset fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq ⊢
    rw [sub_zero]
    obtain ⟨hA, hB⟩ := norm_jasShellDampedSum_xiZeroCopy_le N q
    have htri := (norm_add_le (jasShellDampedSum N (q.1 : ℂ))
      (conj (jasShellDampedSum N (1 - (q.1 : ℂ))))).trans_eq (by rw [Complex.norm_conj])
    have hpos : 0 < 1 + (q.1 : ℂ).im ^ 2 := by positivity
    have h2 : 1 < 2 * jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) := by
      have e : 2 * jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) =
          jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) +
            jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) := by ring
      rw [e]; linarith
    rw [lt_div_iff₀ hpos] at h2
    have h3 : (q.1 : ℂ).im ^ 2 ≤ 2 * jasShellHalfMass N := by nlinarith
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h3

/-! ## Symmetry under RH and detection off RH -/

theorem jasShellUniformSum_conj (N : ℕ) (s : ℂ) :
    jasShellUniformSum N (conj s) = conj (jasShellUniformSum N s) := by
  rw [jasShellUniformSum, jasShellUniformSum, jasCpowSum, jasCpowSum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_sub, Complex.conj_ofReal, map_div₀, map_ofNat]

theorem jasShellDampedSum_conj (N : ℕ) (s : ℂ) :
    jasShellDampedSum N (conj s) = conj (jasShellDampedSum N s) := by
  rw [jasShellDampedSum, jasShellDampedSum, jasShellUniformSum_conj, map_div₀, map_pow, map_add,
    map_one]

theorem jasShellDampedSum_one_sub_eq_conj_of_riemannHypothesis (hRH : RiemannHypothesis)
    (N : ℕ) (q : XiZeroCopy) :
    jasShellDampedSum N (1 - (q.1 : ℂ)) = conj (jasShellDampedSum N (q.1 : ℂ)) := by
  have hhalf := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hrefl : 1 - (q.1 : ℂ) = conj (q.1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hhalf]; norm_num
    · simp
  rw [hrefl, jasShellDampedSum_conj]

/-- Off RH, a zero right of the line is loud on every large shell. -/
theorem eventually_exists_two_lt_norm_jasShellDamped_sym (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ N : ℕ in atTop, ∃ q : XiZeroCopy, 2 < ‖jasShellDampedSum N (q.1 : ℂ) +
      conj (jasShellDampedSum N (1 - (q.1 : ℂ)))‖ := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖((q₁.1 : ℂ) + 1) ^ 2‖ := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]; refine norm_pos_iff.mpr (pow_ne_zero 2 fun h => ?_)
    have := xiZeroCopy_re_pos q₁
    have h' : ((q₁.1 : ℂ) + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at h'
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((q₁.1 : ℂ).re - 1 / 2) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop
  have hev := (eventually_lt_norm_jasShellUniformSum q₁ (ε := δ) hδ0.le
    (by rw [hδ]; linarith)).and (hgrow.eventually (eventually_gt_atTop (3 * c)))
  filter_upwards [hev] with N ⟨hloud, hbig⟩
  refine ⟨q₁, ?_⟩
  have hV : 3 < ‖jasShellDampedSum N (q₁.1 : ℂ)‖ := by
    rw [jasShellDampedSum, norm_div, ← hc, lt_div_iff₀ hc0]; linarith
  have hV' : ‖jasShellDampedSum N (1 - (q₁.1 : ℂ))‖ ≤ 1 :=
    norm_jasShellDampedSum_le_one_of_re N (re_one_sub_xiZeroCopy_mem q₁).1
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have htri := norm_sub_le (jasShellDampedSum N (q₁.1 : ℂ) +
    conj (jasShellDampedSum N (1 - (q₁.1 : ℂ)))) (conj (jasShellDampedSum N (1 - (q₁.1 : ℂ))))
  rw [add_sub_cancel_right, Complex.norm_conj] at htri
  linarith

/-! ## The criterion -/

/-- **RH ⟺ damped shell Weil positivity on infinitely many shells.** -/
theorem riemannHypothesis_iff_shellDamped_weilPositive :
    RiemannHypothesis ↔
      ∃ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 ≤ (jasShellDampedWeilForm N z).re :=
  riemannHypothesis_iff_frequently_expWeilForm_nonneg
    (fun N q => jasShellDampedSum N (q.1 : ℂ)) (fun N q => jasShellDampedSum N (1 - (q.1 : ℂ)))
    (fun N => (jasShellDamped_bounds N).1) (fun N => (jasShellDamped_bounds N).2.1)
    (fun N => (jasShellDamped_bounds N).2.2)
    (fun hRH N q => jasShellDampedSum_one_sub_eq_conj_of_riemannHypothesis hRH N q)
    eventually_exists_two_lt_norm_jasShellDamped_sym

/-- **Dichotomy.**  Damped shell Weil positivity on infinitely many shells forces it on all. -/
theorem riemannHypothesis_iff_forall_shellDamped_weilPositive :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ z : ℂ, 0 ≤ (jasShellDampedWeilForm N z).re :=
  riemannHypothesis_iff_forall_expWeilForm_nonneg
    (fun N q => jasShellDampedSum N (q.1 : ℂ)) (fun N q => jasShellDampedSum N (1 - (q.1 : ℂ)))
    (fun N => (jasShellDamped_bounds N).1) (fun N => (jasShellDamped_bounds N).2.1)
    (fun N => (jasShellDamped_bounds N).2.2)
    (fun hRH N q => jasShellDampedSum_one_sub_eq_conj_of_riemannHypothesis hRH N q)
    eventually_exists_two_lt_norm_jasShellDamped_sym

end

end RHTower
