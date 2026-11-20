import GaloisForLFunctions.TransMetzlerWeilPositivity.ZeroSideStratum

/-!
# A complex zero weighs linearly in the overlap

For a zero `ρ = 1/2 + σ + iγ₀` with `σ ≥ 0` and `γ₀ ≠ 0`, test the atomic family on the real
vector `x_n = cos(γ₀ log n)`. The zero summand factors as `m_ρ h(γ) conj(h(γ̄)) D(γ) conj(D(γ̄))`
(`γ = γ₀ - iσ`). The real parts of the two Dirichlet factors are `Σ n^{±σ} cos²(γ₀ log n)`, whose
product is at least `(Σ cos²(γ₀ log n))²` by Cauchy–Schwarz, and the real parts of the two bump
transforms are at least `(1/4) w ∫ φ` once the width `w = c/N` is small. Since
`Σ_{n ≤ N} cos²(γ₀ log n) ≥ κ N` (a whole multiplicative window below `N` has `2|γ₀| log n` within
`π/2` above a multiple of `2π`), the summand is at least `κ c` times the diagonal atomic energy:
the single-zero weight grows linearly in the overlap ratio `c`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology Complex Zeta23
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics
open ArithmeticCastelnuovoSeveri (cx)
open RenormalizedArithmeticPotentialTheory (atomDilate_facts)
open SpacingScaleHarmonicAnalysis (atomDilate integral_atomDilate_sq dirichletPoly
  Wsummand_atomicTest)

/-! ### 1. The cosine-square mass of `log n` -/

/-- For `t ≠ 0` the sums `Σ_{n ≤ N} cos²(t log n)` grow at least linearly. -/
theorem eventually_sum_cos_sq_log_ge {t : ℝ} (ht : t ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      κ * N ≤ ∑ n ∈ Icc 1 N, Real.cos (t * Real.log n) ^ 2 := by
  have hs0 : 0 < |t| := abs_pos.mpr ht
  have hr1 : 1 < Real.exp (Real.pi / (4 * |t|)) := by
    have h0 : 0 < Real.pi / (4 * |t|) := by positivity
    linarith only [Real.add_one_lt_exp h0.ne', h0]
  have hq : 0 < Real.exp (-(2 * Real.pi / |t|)) := Real.exp_pos _
  set r := Real.exp (Real.pi / (4 * |t|)) with hr
  set q := Real.exp (-(2 * Real.pi / |t|)) with hq_def
  have hqr : 0 < q * (r - 1) := mul_pos hq (by linarith only [hr1])
  refine ⟨q * (r - 1) / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈2 / (q * (r - 1))⌉₊, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNbig : 2 ≤ q * (r - 1) * N := by
    have h := (Nat.ceil_le.mp hN)
    rwa [div_le_iff₀ hqr, mul_comm] at h
  set k : ℤ := ⌊|t| * Real.log N / Real.pi⌋ - 1 with hk
  have hfl1 := Int.floor_le (|t| * Real.log N / Real.pi)
  have hfl2 := Int.lt_floor_add_one (|t| * Real.log N / Real.pi)
  have hk1 : (k : ℝ) * Real.pi ≤ |t| * Real.log N - Real.pi := by
    have h := mul_le_mul_of_nonneg_right hfl1 Real.pi_pos.le
    rw [div_mul_cancel₀ _ Real.pi_ne_zero] at h
    rw [hk]; push_cast; linarith only [h]
  have hk2 : |t| * Real.log N - 2 * Real.pi < (k : ℝ) * Real.pi := by
    have h := mul_lt_mul_of_pos_right hfl2 Real.pi_pos
    rw [add_mul, one_mul, div_mul_cancel₀ _ Real.pi_ne_zero] at h
    rw [hk]; push_cast; linarith only [h]
  set a := Real.exp ((k : ℝ) * Real.pi / |t|) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hlogN : Real.exp (Real.log N) = N := Real.exp_log hN0
  have har : a * r ≤ N := by
    rw [ha, hr, ← Real.exp_add, ← hlogN]
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right hk1 hs0.le
    have h2 : (|t| * Real.log N - Real.pi) / |t| = Real.log N - Real.pi / |t| := by
      field_simp
    have h3 : Real.pi / (4 * |t|) ≤ Real.pi / |t| :=
      div_le_div_of_nonneg_left Real.pi_pos.le hs0 (by linarith only [hs0])
    linarith only [h, h2, h3]
  have haN : N * q < a := by
    rw [ha, hq_def, ← hlogN, ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    have h := div_lt_div_of_pos_right hk2 hs0
    have h2 : (|t| * Real.log N - 2 * Real.pi) / |t| = Real.log N + -(2 * Real.pi / |t|) := by
      field_simp; ring
    linarith only [h, h2]
  have hgood : ∀ n : ℕ, a ≤ n → (n : ℝ) ≤ a * r → 1 / 2 ≤ Real.cos (t * Real.log n) ^ 2 := by
    intro n hn1 hn2
    have hn0 : (0 : ℝ) < n := ha0.trans_le hn1
    have hlog1 : (k : ℝ) * Real.pi / |t| ≤ Real.log n := by
      rw [← Real.log_exp ((k : ℝ) * Real.pi / |t|), ← ha]
      exact Real.log_le_log ha0 hn1
    have hlog2 : Real.log n ≤ (k : ℝ) * Real.pi / |t| + Real.pi / (4 * |t|) := by
      rw [← Real.log_exp ((k : ℝ) * Real.pi / |t| + Real.pi / (4 * |t|)), Real.exp_add, ← ha, ← hr]
      exact Real.log_le_log hn0 hn2
    have hn1 : (1 : ℝ) ≤ n := by
      have : n ≠ 0 := by rintro rfl; simp at hn0
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hcos2 : Real.cos (2 * (t * Real.log n)) = Real.cos (2 * |t| * Real.log n - k * (2 * Real.pi)) := by
      rw [Real.cos_sub_int_mul_two_pi, ← Real.cos_abs (2 * (t * Real.log n)), abs_mul, abs_mul,
        abs_of_pos two_pos, abs_of_nonneg hlogn0]
      ring_nf
    have hmem : 2 * |t| * Real.log n - k * (2 * Real.pi) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      have e1 := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ 2 * |t|)
      have e2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 2 * |t|)
      have f1 : 2 * |t| * ((k : ℝ) * Real.pi / |t|) = k * (2 * Real.pi) := by field_simp
      have f2 : 2 * |t| * ((k : ℝ) * Real.pi / |t| + Real.pi / (4 * |t|)) =
          k * (2 * Real.pi) + Real.pi / 2 := by field_simp; ring
      constructor <;> nlinarith only [e1, e2, f1, f2, Real.pi_pos]
    have hnn := Real.cos_nonneg_of_mem_Icc hmem
    rw [Real.cos_sq, hcos2]
    linarith only [hnn]
  set A := ⌈a⌉₊
  set B := ⌊a * r⌋₊
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ha0).ne'
  have hBN : B ≤ N := Nat.floor_le_of_le har
  have hsub : Icc A B ⊆ Icc 1 N := fun n hn => by
    have := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨hA1.trans this.1, this.2.trans hBN⟩
  have hsum_ge : (1 / 2 : ℝ) * (Icc A B).card ≤ ∑ n ∈ Icc 1 N, Real.cos (t * Real.log n) ^ 2 := by
    calc (1 / 2 : ℝ) * (Icc A B).card = ∑ _n ∈ Icc A B, (1 / 2 : ℝ) := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ n ∈ Icc A B, Real.cos (t * Real.log n) ^ 2 := by
          refine sum_le_sum fun n hn => hgood n ?_ ?_
          · exact (Nat.le_ceil a).trans (by exact_mod_cast (mem_Icc.mp hn).1)
          · exact (by exact_mod_cast (mem_Icc.mp hn).2 : (n : ℝ) ≤ B).trans (Nat.floor_le
              (by positivity))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sq_nonneg _
  have hcard : a * (r - 1) - 1 ≤ ((Icc A B).card : ℝ) := by
    rw [Nat.card_Icc]
    have hB : a * r - 1 < (B : ℝ) := by
      have := Nat.lt_floor_add_one (a * r)
      linarith only [this]
    have hA : (A : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0.le
    rcases le_total A (B + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith only [hB, hA]
    · rw [Nat.sub_eq_zero_of_le h]
      have : (B : ℝ) + 1 ≤ A := by exact_mod_cast h
      push_cast
      nlinarith only [this, hB, hA]
  have hfin : q * (r - 1) * N < a * (r - 1) := by
    have := mul_lt_mul_of_pos_right haN (by linarith only [hr1] : (0 : ℝ) < r - 1)
    linarith only [this]
  nlinarith only [hsum_ge, hcard, hfin, hNbig]

/-! ### 2. Real parts of the bump transform and of the Dirichlet polynomial -/

private theorem I_mul_sub_mul_I (a b u : ℝ) :
    Complex.I * ((b : ℂ) - (a : ℂ) * Complex.I) * (u : ℂ) =
      ((a * u : ℝ) : ℂ) + ((b * u : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem re_ofReal_add_mul_I (p s : ℝ) :
    ((p : ℂ) + (s : ℂ) * Complex.I).re = p := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

private theorem im_ofReal_add_mul_I (p s : ℝ) :
    ((p : ℂ) + (s : ℂ) * Complex.I).im = s := by
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  ring

private theorem re_paperFT_cx {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (a b : ℝ) :
    (paperFT (cx g) ((b : ℂ) - (a : ℂ) * Complex.I)).re =
      ∫ u, g u * (Real.exp (a * u) * Real.cos (b * u)) := by
  unfold paperFT
  have hc : Continuous fun u : ℝ =>
      cx g u * Complex.exp (Complex.I * ((b : ℂ) - (a : ℂ) * Complex.I) * (u : ℂ)) := by
    simp only [cx]; fun_prop
  have hint := hc.integrable_of_hasCompactSupport (μ := volume)
    ((hgc.comp_left Complex.ofReal_zero).mul_right
      (f' := fun u : ℝ => Complex.exp (Complex.I * ((b : ℂ) - (a : ℂ) * Complex.I) * (u : ℂ))))
  rw [show (∫ u : ℝ, cx g u * Complex.exp (Complex.I * ((b : ℂ) - (a : ℂ) * Complex.I) *
      (u : ℂ))).re = ∫ u : ℝ, (cx g u * Complex.exp (Complex.I * ((b : ℂ) - (a : ℂ) * Complex.I) *
        (u : ℂ))).re from (integral_re hint).symm]
  congr 1
  funext u
  rw [cx, I_mul_sub_mul_I, Complex.re_ofReal_mul, Complex.exp_re, re_ofReal_add_mul_I,
    im_ofReal_add_mul_I]

private theorem re_dirichletPoly (N : ℕ) (x : ℕ → ℝ) (a b : ℝ) :
    (dirichletPoly N x ((b : ℂ) - (a : ℂ) * Complex.I)).re =
      ∑ n ∈ Icc 1 N, x n * (Real.exp (a * Real.log n) * Real.cos (b * Real.log n)) := by
  unfold dirichletPoly
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [I_mul_sub_mul_I, Complex.re_ofReal_mul, Complex.exp_re, re_ofReal_add_mul_I,
    im_ofReal_add_mul_I]

private theorem integral_mul_exp_cos_ge {g : ℝ → ℝ} {w a b : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hgn : ∀ u, 0 ≤ g u) (hbw : |b| * w ≤ Real.pi / 2) :
    Real.exp (-(|a| * w)) * Real.cos (|b| * w) * ∫ u, g u ≤
      ∫ u, g u * (Real.exp (a * u) * Real.cos (b * u)) := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hint2 : Integrable fun u => g u * (Real.exp (a * u) * Real.cos (b * u)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport (hgc.mul_right)
  rw [← integral_const_mul]
  refine integral_mono (hint.const_mul _) hint2 fun u => ?_
  by_cases hu : u ∈ Set.Icc 0 w
  · have hu0 := hu.1
    have hcw : 0 ≤ Real.cos (|b| * w) := Real.cos_nonneg_of_mem_Icc
      ⟨by nlinarith only [abs_nonneg b, hu0, hu.2, Real.pi_pos], hbw⟩
    have hcu : Real.cos (|b| * w) ≤ Real.cos (b * u) := by
      rw [← Real.cos_abs (b * u), abs_mul, abs_of_nonneg hu0]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (abs_nonneg b) hu0)
        (by linarith only [hbw, Real.pi_pos]) (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg b))
    have heu : Real.exp (-(|a| * w)) ≤ Real.exp (a * u) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(|a| * w) ≤ -(|a| * u) := by
        nlinarith only [mul_le_mul_of_nonneg_left hu.2 (abs_nonneg a)]
      have h2 : -(|a| * u) ≤ a * u := by
        nlinarith only [neg_abs_le a, hu0, mul_le_mul_of_nonneg_right (neg_abs_le a) hu0]
      linarith only [h1, h2]
    have hprod := mul_le_mul heu hcu hcw (Real.exp_pos _).le
    calc Real.exp (-(|a| * w)) * Real.cos (|b| * w) * g u =
          g u * (Real.exp (-(|a| * w)) * Real.cos (|b| * w)) := by ring
      _ ≤ g u * (Real.exp (a * u) * Real.cos (b * u)) := mul_le_mul_of_nonneg_left hprod (hgn u)
  · simp [hgsupp u hu]

/-! ### 3. Linear growth of a complex zero summand -/

/-- **A complex zero weighs linearly in the overlap.** For a zero `ρ` with `Re ρ ≥ 1/2` and
`Im ρ ≠ 0` and a nonnegative profile, there is `κ > 0` such that at every overlap `c > 0`, for all
large `N`, the zero summand on `x_n = cos(Im ρ · log n)` has modulus at least
`κ m_ρ ((∫ φ)²/∫ φ²) c` times the diagonal atomic energy `(Σ x_n²) ∫ g²`. -/
theorem eventually_norm_Wsummand_atomicTest_cos_ge (Z : ZeroConfig)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hnonneg : ∀ u, 0 ≤ φ u) (hM : 0 < ∫ u, φ u ^ 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re) (him : ρ.im ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : ℝ, 0 < c → ∀ᶠ N : ℕ in atTop,
      κ * (Z.mult ρ : ℝ) * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * c *
          ((∑ n ∈ Icc 1 N, Real.cos (ρ.im * Real.log n) ^ 2) *
            ∫ u, atomDilate φ (c / N) u ^ 2) ≤
        ‖Z.Wsummand
          (cx (atomicTest N (fun n => Real.cos (ρ.im * Real.log n)) (atomDilate φ (c / N))))
          (cx (atomicTest N (fun n => Real.cos (ρ.im * Real.log n)) (atomDilate φ (c / N)))) ρ‖ := by
  obtain ⟨κ₁, hκ₁, hcount⟩ := eventually_sum_cos_sq_log_ge him
  refine ⟨κ₁ / 16, by positivity, fun c hc => ?_⟩
  set σ := ρ.re - 1 / 2 with hσ_def
  set γ₀ := ρ.im with hγ₀
  have hσ : 0 ≤ σ := sub_nonneg.mpr hre
  have hw0 : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hcos_ev : ∀ᶠ N : ℕ in atTop, 1 / 2 < Real.cos (|γ₀| * (c / N)) := by
    have h : Tendsto (fun N : ℕ => Real.cos (|γ₀| * (c / N))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun N : ℕ => |γ₀| * (c / N)) atTop (𝓝 0) := by
        simpa using hw0.const_mul |γ₀|
      have h1 := (Real.continuous_cos.tendsto 0).comp h0
      rw [Real.cos_zero] at h1
      exact h1
    exact h.eventually_const_lt (by norm_num)
  have hexp_ev : ∀ᶠ N : ℕ in atTop, 1 / 2 < Real.exp (-(|σ| * (c / N))) := by
    have h : Tendsto (fun N : ℕ => Real.exp (-(|σ| * (c / N)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun N : ℕ => -(|σ| * (c / N))) atTop (𝓝 0) := by
        simpa using (hw0.const_mul |σ|).neg
      have h1 := (Real.continuous_exp.tendsto 0).comp h0
      rw [Real.exp_zero] at h1
      exact h1
    exact h.eventually_const_lt (by norm_num)
  have hpi_ev : ∀ᶠ N : ℕ in atTop, |γ₀| * (c / N) < Real.pi / 2 := by
    have h : Tendsto (fun N : ℕ => |γ₀| * (c / N)) atTop (𝓝 0) := by
      simpa using hw0.const_mul |γ₀|
    exact h.eventually_lt_const (by positivity)
  filter_upwards [hcount, hcos_ev, hexp_ev, hpi_ev, eventually_ge_atTop 1] with
    N hcN hcosN hexpN hpiN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set w := c / (N : ℝ) with hw_def
  have hw : 0 < w := div_pos hc hN0
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hgn : ∀ u, 0 ≤ atomDilate φ w u := fun u => hnonneg (u / w)
  set x : ℕ → ℝ := fun n => Real.cos (γ₀ * Real.log n) with hx
  set S := ∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun n _ => sq_nonneg _
  have hγ : gammaOf ρ = (γ₀ : ℂ) - (σ : ℂ) * Complex.I := by
    rw [gammaOf, div_eq_iff Complex.I_ne_zero]
    apply Complex.ext <;> simp [hσ_def, hγ₀]
  have hγc : conj (gammaOf ρ) = (γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I := by
    rw [hγ, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [Wsummand_atomicTest Z hg.continuous hgc, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_conj, Complex.norm_conj, Complex.norm_natCast, hγc, hγ]
  -- bump transforms
  have hint_g : ∫ u, atomDilate φ w u = w * ∫ u, φ u := by
    simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
      MeasureTheory.Measure.integral_comp_div φ w
  have hφi : 0 ≤ ∫ u, φ u := integral_nonneg hnonneg
  have hbw : |γ₀| * w ≤ Real.pi / 2 := hpiN.le
  have hA1 : (1 / 4 : ℝ) * (w * ∫ u, φ u) ≤
      ‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [re_paperFT_cx hg.continuous hgc σ γ₀]
    refine le_trans ?_ (integral_mul_exp_cos_ge hg.continuous hgc hgsupp hgn hbw)
    rw [hint_g]
    have hprod : (1 / 4 : ℝ) ≤ Real.exp (-(|σ| * w)) * Real.cos (|γ₀| * w) := by
      nlinarith only [hexpN, hcosN]
    exact mul_le_mul_of_nonneg_right hprod (mul_nonneg hw.le hφi)
  have hA2 : (1 / 4 : ℝ) * (w * ∫ u, φ u) ≤
      ‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [re_paperFT_cx hg.continuous hgc (-σ) γ₀]
    refine le_trans ?_ (integral_mul_exp_cos_ge hg.continuous hgc hgsupp hgn hbw)
    rw [hint_g, abs_neg]
    have hprod : (1 / 4 : ℝ) ≤ Real.exp (-(|σ| * w)) * Real.cos (|γ₀| * w) := by
      nlinarith only [hexpN, hcosN]
    exact mul_le_mul_of_nonneg_right hprod (mul_nonneg hw.le hφi)
  -- Dirichlet factors
  have hD1 : (∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (σ * Real.log n)) ≤
      ‖dirichletPoly N x ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    rw [re_dirichletPoly]
    exact sum_congr rfl fun n _ => by simp only [hx]; ring
  have hD2 : (∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (-σ * Real.log n)) ≤
      ‖dirichletPoly N x ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖ := by
    refine le_trans (le_of_eq ?_) (Complex.re_le_norm _)
    rw [re_dirichletPoly]
    exact sum_congr rfl fun n _ => by simp only [hx]; ring
  have hCS : S ^ 2 ≤
      (∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (σ * Real.log n)) *
        (∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (-σ * Real.log n)) := by
    have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N)
      (fun n => |Real.cos (γ₀ * Real.log n)| * Real.exp (σ * Real.log n / 2))
      (fun n => |Real.cos (γ₀ * Real.log n)| * Real.exp (-σ * Real.log n / 2))
    have h1 : ∀ n ∈ Icc 1 N, (|Real.cos (γ₀ * Real.log n)| * Real.exp (σ * Real.log n / 2)) *
        (|Real.cos (γ₀ * Real.log n)| * Real.exp (-σ * Real.log n / 2)) =
          Real.cos (γ₀ * Real.log n) ^ 2 := by
      intro n _
      rw [show (|Real.cos (γ₀ * Real.log n)| * Real.exp (σ * Real.log n / 2)) *
          (|Real.cos (γ₀ * Real.log n)| * Real.exp (-σ * Real.log n / 2)) =
            |Real.cos (γ₀ * Real.log n)| ^ 2 *
              (Real.exp (σ * Real.log n / 2) * Real.exp (-σ * Real.log n / 2)) by ring,
        ← Real.exp_add, sq_abs]
      rw [show σ * Real.log n / 2 + -σ * Real.log n / 2 = 0 by ring, Real.exp_zero, mul_one]
    have h2 : ∀ n ∈ Icc 1 N, (|Real.cos (γ₀ * Real.log n)| * Real.exp (σ * Real.log n / 2)) ^ 2 =
        Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (σ * Real.log n) := by
      intro n _
      have he : Real.exp (σ * Real.log n / 2) ^ 2 = Real.exp (σ * Real.log n) := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [mul_pow, sq_abs, he]
    have h3 : ∀ n ∈ Icc 1 N, (|Real.cos (γ₀ * Real.log n)| * Real.exp (-σ * Real.log n / 2)) ^ 2 =
        Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (-σ * Real.log n) := by
      intro n _
      have he : Real.exp (-σ * Real.log n / 2) ^ 2 = Real.exp (-σ * Real.log n) := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [mul_pow, sq_abs, he]
    rw [sum_congr rfl h1, sum_congr rfl h2, sum_congr rfl h3] at hcs
    exact hcs
  have hP1 : 0 ≤ ∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (σ * Real.log n) :=
    sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hP2 : 0 ≤ ∑ n ∈ Icc 1 N, Real.cos (γ₀ * Real.log n) ^ 2 * Real.exp (-σ * Real.log n) :=
    sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hDD : S ^ 2 ≤ ‖dirichletPoly N x ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ *
      ‖dirichletPoly N x ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖ :=
    hCS.trans (mul_le_mul hD1 hD2 hP2 (hP1.trans hD1))
  have hAA : (1 / 16 : ℝ) * (w * ∫ u, φ u) ^ 2 ≤
      ‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ *
        ‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖ := by
    have h0 : 0 ≤ (1 / 4 : ℝ) * (w * ∫ u, φ u) := by positivity
    calc (1 / 16 : ℝ) * (w * ∫ u, φ u) ^ 2 =
          ((1 / 4 : ℝ) * (w * ∫ u, φ u)) * ((1 / 4 : ℝ) * (w * ∫ u, φ u)) := by ring
      _ ≤ _ := mul_le_mul hA1 hA2 h0 (h0.trans hA1)
  -- assemble
  rw [integral_atomDilate_sq hw]
  have hcN' : κ₁ * N ≤ S := hcN
  have hm0 : (0 : ℝ) ≤ (Z.mult ρ : ℝ) := Nat.cast_nonneg _
  have hlhs : κ₁ / 16 * (Z.mult ρ : ℝ) * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) * c *
      (S * (w * ∫ u, φ u ^ 2)) = (Z.mult ρ : ℝ) * (∫ u, φ u) ^ 2 * w * S * (κ₁ * c / 16) := by
    field_simp
  rw [hlhs]
  have hkey : (Z.mult ρ : ℝ) * (∫ u, φ u) ^ 2 * w * S * (κ₁ * c / 16) ≤
      (Z.mult ρ : ℝ) * ((1 / 16 : ℝ) * (w * ∫ u, φ u) ^ 2) * S ^ 2 := by
    have hwS : κ₁ * c ≤ w * S := by
      rw [hw_def, div_mul_eq_mul_div, le_div_iff₀ hN0]
      nlinarith only [mul_le_mul_of_nonneg_left hcN' hc.le]
    have hbase : 0 ≤ (Z.mult ρ : ℝ) * (∫ u, φ u) ^ 2 * w * S := by positivity
    calc (Z.mult ρ : ℝ) * (∫ u, φ u) ^ 2 * w * S * (κ₁ * c / 16) ≤
          (Z.mult ρ : ℝ) * (∫ u, φ u) ^ 2 * w * S * (w * S / 16) :=
        mul_le_mul_of_nonneg_left (by linarith only [hwS]) hbase
      _ = _ := by ring
  calc _ ≤ _ := hkey
    _ ≤ (Z.mult ρ : ℝ) *
          (‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ *
            ‖paperFT (cx (atomDilate φ w)) ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖) *
          (‖dirichletPoly N x ((γ₀ : ℂ) - (σ : ℂ) * Complex.I)‖ *
            ‖dirichletPoly N x ((γ₀ : ℂ) - ((-σ : ℝ) : ℂ) * Complex.I)‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hAA hm0) hDD (sq_nonneg _) ?_
        exact mul_nonneg hm0 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

#print axioms eventually_sum_cos_sq_log_ge
#print axioms eventually_norm_Wsummand_atomicTest_cos_ge

end GaloisForLFunctions.TransMetzlerWeilPositivity
