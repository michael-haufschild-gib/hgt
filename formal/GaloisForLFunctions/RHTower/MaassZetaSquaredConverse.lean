import GaloisForLFunctions.RHTower.MaassConverseLevelOne
import GaloisForLFunctions.RHTower.MaassLevelOneCuspVanishing
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalBoundary

/-!
# A converse theorem for `ζ²`

Let `G(s) = Σ g_n n^{−s}` converge absolutely for `Re s > 1` with `g_1 = 1`, and suppose that
`Λ̂(s) = s²(s−1)²Γ_ℝ(s)² G(s)` extends to an entire function with `Λ̂(1 − s) = Λ̂(s)`, bounded on
`−1/2 ≤ Re s ≤ 3/2`.  Then `G = ζ²`: `g_n = d(n)` for every `n ≥ 1`
(`coeff_eq_divisorCount_of_functional_equation`).

**Proof.**
* The Maass functions `u_G` and `u_{ζ²}` attached to `G` and to `ζ²` are `SL₂(ℤ)`-invariant
  eigenfunctions with eigenvalue `1/4` (`MaassConverseLevelOne.maassFun_invS`).  For `ζ²` the
  completed function is `(2ξ)²`, bounded on the strip by the decay of `ξ`
  (`SelbergThetaHorizontalBoundary.xi_strip_decay`), and its constant-term coefficient is
  `a = (2ξ(1))² = 1`.
* The constant terms are proportional (`MaassConstantTermWronskian.constTerm_wronskian_eq_zero`),
  so with `c = a_G` the difference `u_G − c u_{ζ²}` has no constant term.  It is an `S`-invariant
  Bessel cosine series, hence zero (`MaassLevelOneCuspVanishing.coeff_eq_zero_of_invS`):
  `g_n = c d(n)`.  At `n = 1`, `c = 1`.

**The odd sign.**  If instead `Λ̂(1 − s) = −Λ̂(s)`, then `u(−1/z) = −u(z)` and `u(z + 1) = u(z)`;
since `(ST)³ = 1`, `u = −u`, so `u = 0` and every `g_n` vanishes
(`coeff_eq_zero_of_odd_functional_equation`).
-/

open Complex Set Filter
open scoped Topology

noncomputable section

namespace RHTower.MaassZetaSquaredConverse

open MaassBesselSeries MaassThetaRelation MaassConverseLevelOne MaassConstantTermWronskian
  MaassLevelOneCuspVanishing GaloisForLFunctions.RHTower.SelbergMaassMean

/-! ## Absolute convergence -/

theorem summable_of_LSeriesSummable {g : ℕ → ℂ} {σ : ℝ} (hσ : 1 < σ)
    (h : LSeriesSummable g σ) : Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ) := by
  refine h.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · rw [if_neg hn.ne', Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-! ## The reference function `ζ²` -/

/-- The divisor function `d = 1 ⋆ 1`, the coefficients of `ζ²`. -/
def divisorCount : ℕ → ℂ := LSeries.convolution 1 1

theorem divisorCount_one : divisorCount 1 = 1 := by
  simp [divisorCount, LSeries.convolution_def]

theorem LSeriesSummable_divisorCount {s : ℂ} (hs : 1 < s.re) : LSeriesSummable divisorCount s :=
  (LSeriesSummable_one_iff.mpr hs).convolution (LSeriesSummable_one_iff.mpr hs)

theorem LSeries_divisorCount {s : ℂ} (hs : 1 < s.re) :
    LSeries divisorCount s = riemannZeta s ^ 2 := by
  rw [divisorCount, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (LSeriesSummable_one_iff.mpr hs), LSeries_one_eq_riemannZeta hs, sq]

theorem summable_divisorCount {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖divisorCount n‖ * (n : ℝ) ^ (-σ) :=
  summable_of_LSeriesSummable hσ (LSeriesSummable_divisorCount (by simpa using hσ))

theorem differentiable_xi : Differentiable ℂ RHTower.xi := by
  have := differentiable_completedZeta₀
  intro s
  unfold RHTower.xi
  fun_prop

/-- `2ξ(s) = s(s − 1)Γ_ℝ(s)ζ(s)` on `Re s > 0`, `s ≠ 1`. -/
theorem two_xi_eq {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    2 * RHTower.xi s = s * (s - 1) * Complex.Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannZeta_def_of_ne_zero h0, completedRiemannZeta_eq]
  unfold RHTower.xi
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
  ring

/-- The completed function of `ζ²`: `(2ξ)²`. -/
def zetaSqCompleted (s : ℂ) : ℂ := (2 * RHTower.xi s) ^ 2

theorem differentiable_zetaSqCompleted : Differentiable ℂ zetaSqCompleted :=
  (differentiable_xi.const_mul 2).pow 2

theorem zetaSqCompleted_one_sub (s : ℂ) : zetaSqCompleted (1 - s) = zetaSqCompleted s := by
  simp only [zetaSqCompleted, RHTower.xi_one_sub]

theorem zetaSqCompleted_eq {s : ℂ} (hs : 1 < s.re) :
    zetaSqCompleted s =
      s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries divisorCount s := by
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [zetaSqCompleted, two_xi_eq (by linarith) h1, LSeries_divisorCount hs]
  ring

theorem coeffA_zetaSqCompleted : coeffA zetaSqCompleted = 1 := by
  simp [coeffA, zetaSqCompleted, RHTower.xi]

/-- `x^N e^{−πx/4} ≤ (4/π)^N N!` for `x ≥ 0`. -/
theorem pow_mul_exp_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    x ^ N * Real.exp (-(Real.pi * x / 4)) ≤ (4 / Real.pi) ^ N * N.factorial := by
  have hy : 0 ≤ Real.pi * x / 4 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hy N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf] at h
  have hx' : x ^ N = (4 / Real.pi) ^ N * (Real.pi * x / 4) ^ N := by
    rw [← mul_pow]; congr 1; field_simp
  rw [hx']
  have he := Real.exp_pos (Real.pi * x / 4)
  have hc : 0 < (4 / Real.pi) ^ N := by positivity
  calc (4 / Real.pi) ^ N * (Real.pi * x / 4) ^ N * Real.exp (-(Real.pi * x / 4))
      ≤ (4 / Real.pi) ^ N * (Real.exp (Real.pi * x / 4) * N.factorial) *
          Real.exp (-(Real.pi * x / 4)) := by gcongr
    _ = (4 / Real.pi) ^ N * N.factorial := by
        rw [show (4 / Real.pi) ^ N * (Real.exp (Real.pi * x / 4) * N.factorial) *
            Real.exp (-(Real.pi * x / 4)) = (4 / Real.pi) ^ N * N.factorial *
              (Real.exp (Real.pi * x / 4) * Real.exp (-(Real.pi * x / 4))) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- `ξ` is bounded on `−1/2 ≤ Re s ≤ 3/2`. -/
theorem exists_bound_xi_strip :
    ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖RHTower.xi s‖ ≤ B := by
  obtain ⟨C, N, hC, hdec⟩ := RHTower.SelbergThetaHorizontalBoundary.xi_strip_decay
  set box : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) ''
    (Icc (-1 / 2 : ℝ) (3 / 2) ×ˢ Icc (-2 : ℝ) 2) with hbox
  have hK : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn differentiable_xi.continuous.continuousOn
  set D : ℝ := C * ((4 / Real.pi) ^ N * N.factorial) with hD
  have hhigh : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 3 / 2 → 2 ≤ |z.im| → ‖RHTower.xi z‖ ≤ D := by
    intro z h1 h2 h3
    refine (hdec z h1 (by linarith) h3).trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_mul_exp_le (abs_nonneg _) N) hC
  refine ⟨max C₀ D, fun s h1 h2 => ?_⟩
  by_cases ht : |s.im| ≤ 2
  · refine (hC₀ s ⟨(s.re, s.im), ⟨⟨h1, h2⟩, abs_le.mp ht⟩, ?_⟩).trans (le_max_left _ _)
    exact Complex.re_add_im s
  · rw [not_le] at ht
    by_cases hr : 1 / 2 ≤ s.re
    · exact (hhigh s hr h2 ht.le).trans (le_max_right _ _)
    · rw [not_le] at hr
      rw [← RHTower.xi_one_sub]
      refine (hhigh (1 - s) (by simp; linarith) (by simp; linarith) ?_).trans (le_max_right _ _)
      simpa using ht.le

theorem exists_bound_zetaSqCompleted :
    ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖zetaSqCompleted s‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_xi_strip
  refine ⟨(2 * B) ^ 2, fun s h1 h2 => ?_⟩
  rw [zetaSqCompleted, norm_pow, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hB s h1 h2) (by norm_num)) 2

/-- **`u_{ζ²}` is `SL₂(ℤ)`-invariant.** -/
theorem maassFun_divisorCount_invS {z : ℂ} (hz : 0 < z.im) :
    maassFun divisorCount (coeffA zetaSqCompleted) (coeffB zetaSqCompleted) (invS z) =
      maassFun divisorCount (coeffA zetaSqCompleted) (coeffB zetaSqCompleted) z :=
  maassFun_invS (fun _ hσ => summable_divisorCount hσ) differentiable_zetaSqCompleted
    zetaSqCompleted_one_sub (fun _ hs => zetaSqCompleted_eq hs) exists_bound_zetaSqCompleted hz

/-! ## Linear combinations of Bessel series -/

theorem polyGrowth_sub_smul {g f : ℕ → ℂ} (hg : PolyGrowth g) (hf : PolyGrowth f) (c : ℂ) :
    PolyGrowth fun n => g n - c * f n := by
  obtain ⟨C₁, hC₁, A₁, h₁⟩ := hg
  obtain ⟨C₂, hC₂, A₂, h₂⟩ := hf
  refine ⟨C₁ + ‖c‖ * C₂, by positivity, A₁ + A₂, fun n => ?_⟩
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have e₁ : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) :=
    pow_le_pow_right₀ hn (by omega)
  have e₂ : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) :=
    pow_le_pow_right₀ hn (by omega)
  calc ‖g n - c * f n‖ ≤ ‖g n‖ + ‖c‖ * ‖f n‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr
        · exact h₁ n
        · exact h₂ n
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem cosSeries_sub_smul {g f : ℕ → ℂ} (hg : PolyGrowth g) (hf : PolyGrowth f) (c : ℂ)
    {z : ℂ} (hz : 0 < z.im) :
    cosSeries (fun n => g n - c * f n) z = cosSeries g z - c * cosSeries f z := by
  unfold cosSeries besselSeries
  rw [← tsum_mul_left, ← Summable.tsum_sub (summable_sterm hg _ _ _ _ hz)
    ((summable_sterm hf _ _ _ _ hz).mul_left c)]
  congr 1
  funext n
  simp only [sterm]
  ring

/-! ## The converse theorem -/

/-- **A converse theorem for `ζ²`.**  A Dirichlet series `G = Σ g_n n^{−s}` with `g_1 = 1`,
absolutely convergent on `Re s > 1`, whose completion `s²(s−1)²Γ_ℝ(s)²G(s)` extends to an entire
function invariant under `s ↦ 1 − s` and bounded on `−1/2 ≤ Re s ≤ 3/2`, is `ζ²`. -/
theorem coeff_eq_divisorCount_of_functional_equation {g : ℕ → ℂ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) (hg1 : g 1 = 1)
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = Λh s)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    g n = divisorCount n := by
  have hg := polyGrowth_of_summable hsum
  have hd := polyGrowth_of_summable (fun σ hσ => summable_divisorCount (σ := σ) hσ)
  set aG := coeffA Λh
  set bG := coeffB Λh
  set b₀ := coeffB zetaSqCompleted
  have hSG : ∀ z : ℂ, 0 < z.im → maassFun g aG bG (invS z) = maassFun g aG bG z :=
    fun z hz => maassFun_invS hsum hΛ hsym heq hbd hz
  have hS₀ : ∀ z : ℂ, 0 < z.im → maassFun divisorCount 1 b₀ (invS z) = maassFun divisorCount 1 b₀ z := by
    intro z hz
    have h := maassFun_divisorCount_invS hz
    rwa [coeffA_zetaSqCompleted] at h
  -- the constant terms are proportional
  have hW := constTerm_wronskian_eq_zero hg hd aG bG 1 b₀ hSG hS₀
  have hb : bG = aG * b₀ := by linear_combination hW
  -- the difference is an `S`-invariant Bessel cosine series
  set h : ℕ → ℂ := fun k => g k - aG * divisorCount k with hh
  have hhp : PolyGrowth h := polyGrowth_sub_smul hg hd aG
  have hdiff : ∀ z : ℂ, 0 < z.im →
      maassFun g aG bG z - aG * maassFun divisorCount 1 b₀ z = 4 * cosSeries h z := by
    intro z hz
    rw [hh, cosSeries_sub_smul hg hd aG hz]
    simp only [maassFun, constTerm, hb]
    ring
  have hSh : ∀ z : ℂ, 0 < z.im → cosSeries h (invS z) = cosSeries h z := by
    intro z hz
    have hSz : 0 < (invS z).im := invS_mem_upper hz
    have e := hdiff (invS z) hSz
    rw [hSG z hz, hS₀ z hz, hdiff z hz] at e
    exact (mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) e).symm
  have hzero : ∀ k : ℕ, 1 ≤ k → h k = 0 := fun k hk => coeff_eq_zero_of_invS hhp hSh hk
  have hc : aG = 1 := by
    have h1 := hzero 1 le_rfl
    simp only [hh, hg1, divisorCount_one, mul_one] at h1
    linear_combination -h1
  have hk := hzero n hn
  simp only [hh, hc, one_mul] at hk
  exact sub_eq_zero.mp hk

/-! ## The odd functional equation -/

/-- `(ST)³ = 1` on the upper half-plane: `S(S(S(z + 1) + 1) + 1) = z`. -/
theorem invS_cube {z : ℂ} (hz : 0 < z.im) : invS (invS (invS (z + 1) + 1) + 1) = z := by
  have h0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h1 : z + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have e1 : invS (z + 1) + 1 = z / (z + 1) := by
    unfold invS; field_simp; ring
  have e2 : invS (z / (z + 1)) + 1 = -z⁻¹ := by
    unfold invS; field_simp; ring
  rw [e1, e2]
  unfold invS
  simp

theorem upper_add_one {z : ℂ} (hz : 0 < z.im) : 0 < (z + 1).im := by simpa using hz

/-- **An odd functional equation forces `G = 0`.** -/
theorem coeff_eq_zero_of_odd_functional_equation {g : ℕ → ℂ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {Λh : ℂ → ℂ} (hΛ : Differentiable ℂ Λh) (hsym : ∀ s, Λh (1 - s) = -Λh s)
    (heq : ∀ s : ℂ, 1 < s.re → Λh s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s)
    (hbd : ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Λh s‖ ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    g m = 0 := by
  have hg := polyGrowth_of_summable hsum
  set a := (-1 : ℂ) * coeffA Λh
  set b := (-1 : ℂ) * coeffB Λh
  have hS : ∀ z : ℂ, 0 < z.im → maassFun g a b (invS z) = -1 * maassFun g a b z :=
    fun z hz => maassFun_invS_sign hsum hΛ (fun s => by rw [hsym]; ring) (by norm_num) heq hbd hz
  have hT : ∀ z : ℂ, maassFun g a b (z + 1) = maassFun g a b z := fun z => maassFun_add_one a b z
  -- `u` vanishes identically
  have hzero : ∀ z : ℂ, 0 < z.im → maassFun g a b z = 0 := by
    intro z hz
    have hz1 := upper_add_one hz
    have hS1 := invS_mem_upper hz1
    have hz2 := upper_add_one hS1
    have hS2 := invS_mem_upper hz2
    have hz3 := upper_add_one hS2
    have e1 := hS (z + 1) hz1
    have e2 := hS (invS (z + 1) + 1) hz2
    have e3 := hS (invS (invS (z + 1) + 1) + 1) hz3
    rw [invS_cube hz, hT] at e3
    rw [hT] at e2
    rw [hT] at e1
    rw [e2, e1] at e3
    linear_combination e3 / 2
  -- `W` is constant on horizontal lines
  have hy : (0 : ℝ) < 1 := one_pos
  have hline : ∀ x : ℝ, cosSeries g (point x 1) = -(constTerm a b (point x 1)) / 4 := by
    intro x
    have h := hzero (point x 1) (by rw [point_im]; exact hy)
    unfold maassFun at h
    linear_combination h / 4
  have hc : ∀ x : ℝ, constTerm a b (point x 1) = constTerm a b (point 0 1) := by
    intro x; simp [constTerm, point_im]
  have hint := integral_cosSeries_mul_cos_eq hg hm hy
  have hint0 : ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      cosSeries g (point x 1) * (Real.cos (2 * Real.pi * m * x) : ℂ) = 0 := by
    have hcos := integral_cos_two_pi_int (k := (m : ℤ)) (by exact_mod_cast (show m ≠ 0 by omega))
    push_cast at hcos
    simp_rw [hline, hc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hcos]
    simp
  rw [hint0] at hint
  have hyp := yPart_pos hm hy
  have hprod : g m * (yPart (1 / 2) 0 0 m 1 : ℂ) = 0 := by linear_combination (-2 : ℂ) * hint
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact h0
  · exact absurd h0 (by exact_mod_cast hyp.ne')

end RHTower.MaassZetaSquaredConverse
