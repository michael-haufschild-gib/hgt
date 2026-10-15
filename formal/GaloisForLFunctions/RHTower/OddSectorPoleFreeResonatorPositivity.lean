import GaloisForLFunctions.RHTower.EvenSectorPoleFreeResonatorPositivity
import GaloisForLFunctions.RHTower.OddSectorWeightGrowth

/-!
# Pole-free odd positivity transfers to resonators with an odd profile

Let `lam` be Weil-positive at some pole weight `β` on the autocorrelations of odd compactly
supported `C²` tests.  On odd tests whose transform vanishes at `±i/2` the pole weight drops out.

**Theorem** (`re_weilFullFunctional_derivTranslateSum_nonneg_of_weilPositiveOddAt`).  For every even
real `C³` profile `g` of compact support with `ĝ(i/2) = 0`, all points `x_k` and all coefficients
`c_k ≥ 0`, the resonator `R = Σ_k c_k g'(· − x_k)`, whose profile `g'` is odd, satisfies
`Re W(R ⋆ R̃) ≥ 0`.  The resonator is in general neither odd nor even.

The transform of an odd real test is `−iz A(z)` with `A` even and real on the line; its spectral
square is `z² · A A^#`.  The odd functional `K ↦ L(z² K)` is therefore represented, for every
pole-free even strip function `A`, by a finite positive measure `ν_A` on the `ρ`-line
(`exists_cosineShift_measure_oddLift`): the cosine and sine combinations of `A` give the odd strip
functions `−iz Σ c_j cos(t_j ρ) A` and `−iz Σ c_j sin(t_j ρ) A`.  For the resonator,
`R̂ = −iz ĝ · D` with `D(z) = Σ c_k e^{izx_k}`, so after Gaussian smoothing
`L(R̂ R̂^#) = L(z² ĝĝ^# · D D̃ e^{−εz²}) = ∫ (D D̃ e^{−εz²})~ dν ≥ 0`, because the lifted
multiplier is nonnegative on the whole `ρ`-line (`re_rhoLift_gaussDamped_pairExp_nonneg`).

The odd profile is essential.  An even profile in the odd sector would need the weight `1/z²`,
which is negative on the imaginary segment.  An odd profile carries its own factor `z²`.

General tools (any spectral density `K` that is holomorphic and decaying on `|Im z| ≤ 5/4`, even and
real on the line): continuity of `y ↦ L(cos(yρ) K)` (`continuous_cosineShiftK`), the kernel
identity (`evenWeilDensity_mul_kernel_of_good`), and the multiplier form
(`evenWeilDensity_mul_multiplier_of_good`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.OddSector

open WeilOneSided WeilSpectral SeparatedBump EvenSector WeilPoleWeight

/-! ## Growth at every pole weight -/

/-- The pole term of a test is at most `2B²` in absolute value when `‖f̂(σ i)‖ ≤ B` for
`|σ| ≤ 1/2`. -/
theorem abs_re_weilPoleTerm_le {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {B : ℝ}
    (hB : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤ B) :
    |(weilPoleTerm (EF.weilTest f f)).re| ≤ 2 * B ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  have h1 := hB (1 / 2) (by norm_num [abs_of_pos])
  have h2 := hB (-(1 / 2)) (by norm_num [abs_of_pos])
  rw [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at h1
  rw [show ((-(1 / 2) : ℝ) : ℂ) * I = -I / 2 by push_cast; ring] at h2
  rw [weilPoleTerm_weilTest_eq hf hfc]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have := mul_le_mul h1 h2 (norm_nonneg _) hB0
  have := mul_le_mul h2 h1 (norm_nonneg _) hB0
  nlinarith

theorem abs_re_weilPoleTerm_node_le (n : ℕ) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hb : ∀ r : ℝ, ‖paperFT f r‖ ≤ 4 * ‖paperFT (fun u => (nodeBump n u : ℂ)) r‖)
    (hi : ∀ σ : ℝ, |σ| ≤ 1 / 2 → ‖paperFT f ((σ : ℂ) * I)‖ ≤
      4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) :
    |(weilPoleTerm (EF.weilTest f f)).re| ≤
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
        8 / (Real.pi * nodeScale n) *
          ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) := by
  have hm0 := nodeScale_pos n
  have h1 := abs_re_weilPoleTerm_le hf hfc hi
  have e1 : 2 * (4 * Real.exp (Real.log n / 4 + 1 / 4) * ((nodeScale n)⁻¹ * bumpPoleConst)) ^ 2 =
      32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    field_simp
    ring_nf
  have hX : 0 ≤ (gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst := by
    have h2 := integral_normSq_mul_abs_gammaBracket_le n hb
    have h3 : 0 ≤ ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * |EF.gammaBracket r| :=
      integral_nonneg fun r => by positivity
    by_contra hneg
    push Not at hneg
    have : 16 / nodeScale n *
        ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  have hY : 0 ≤ 8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) :=
    mul_nonneg (by positivity) hX
  linarith

theorem pole_arch_le_of_node_abs {A P Bd β : ℝ} (hA : |A| ≤ Bd) (hP : |P| ≤ Bd) :
    A + (β - 1) * P ≤ (1 + |β - 1|) * Bd := by
  have h1 := le_abs_self A
  have h2 : (β - 1) * P ≤ |β - 1| * Bd := by
    calc (β - 1) * P ≤ |(β - 1) * P| := le_abs_self _
      _ = |β - 1| * |P| := abs_mul _ _
      _ ≤ |β - 1| * Bd := mul_le_mul_of_nonneg_left hP (abs_nonneg _)
  nlinarith

/-- **Odd-positive weights grow at most like `√n log n`, at every pole weight.** -/
theorem exists_abs_le_of_weilPositiveOddAt_any {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → |lam n| ≤ C * Real.sqrt n * (1 + Real.log n) := by
  have hJ : 0 < ∫ u, narrowBump 0 u ^ 2 := integral_narrowBump_sq_pos 0
  set X := 16 * Real.exp (1 / 2) * bumpPoleConst ^ 2 / (∫ u, narrowBump 0 u ^ 2) +
    4 * ((|gammaLogConst| + 3) * bumpMassConst + bumpLogConst) /
      (Real.pi * ∫ u, narrowBump 0 u ^ 2) with hX
  have hX0 : 0 ≤ X := add_nonneg (by positivity)
    (div_nonneg (by have := bumpMassConst_nonneg; have := bumpLogConst_nonneg; positivity)
      (by positivity))
  set k := 1 + |β - 1| with hk
  have hk1 : 1 ≤ k := by rw [hk]; linarith [abs_nonneg (β - 1)]
  refine ⟨k * X, mul_nonneg (by linarith) hX0, fun n hn => ?_⟩
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hm0 := nodeScale_pos n
  have hmeq : nodeScale n = 2 * (n : ℝ) + 3 := rfl
  set Bd := 32 * Real.exp (Real.log n / 2 + 1 / 2) * bumpPoleConst ^ 2 / nodeScale n ^ 2 +
    8 / (Real.pi * nodeScale n) *
      ((gammaLogConst + Real.log (nodeScale n)) * bumpMassConst + bumpLogConst) with hBd
  have hWp := h (oddPlus n).1.1 (oddPlus n).1.2.1 (oddPlus n).1.2.2 (oddPlus n).2
  rw [re_weilPoleWeightFunctional_eq β lam (oddPlus n).1,
    logVector_oddPlus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWp
  have hWm := h (oddMinus n).1.1 (oddMinus n).1.2.1 (oddMinus n).1.2.2 (oddMinus n).2
  rw [re_weilPoleWeightFunctional_eq β lam (oddMinus n).1,
    logVector_oddMinus ⟨n, hn⟩, Finsupp.linearCombination_single] at hWm
  simp only [poleWeightArchRe, smul_eq_mul] at hWp hWm
  have hAp : |weilArchRe (EF.weilTest (oddPlus n).1.1 (oddPlus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (oddPlus n).1.2.1.continuous (oddPlus n).1.2.2
      (norm_paperFT_oddPlus_le n) fun σ hσ => norm_paperFT_oddPlus_imag_le n hσ
  have hAm : |weilArchRe (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1)| ≤ Bd :=
    abs_weilArchRe_node_le n (oddMinus n).1.2.1.continuous (oddMinus n).1.2.2
      (norm_paperFT_oddMinus_le n) fun σ hσ => norm_paperFT_oddMinus_imag_le n hσ
  have hPp : |(weilPoleTerm (EF.weilTest (oddPlus n).1.1 (oddPlus n).1.1)).re| ≤ Bd :=
    abs_re_weilPoleTerm_node_le n (oddPlus n).1.2.1.continuous (oddPlus n).1.2.2
      (norm_paperFT_oddPlus_le n) fun σ hσ => norm_paperFT_oddPlus_imag_le n hσ
  have hPm : |(weilPoleTerm (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1)).re| ≤ Bd :=
    abs_re_weilPoleTerm_node_le n (oddMinus n).1.2.1.continuous (oddMinus n).1.2.2
      (norm_paperFT_oddMinus_le n) fun σ hσ => norm_paperFT_oddMinus_imag_le n hσ
  have hBd0 : 0 ≤ Bd := (abs_nonneg _).trans hAp
  have hkBd : 0 ≤ k * Bd := mul_nonneg (by linarith) hBd0
  have hAp' : _ ≤ k * Bd := pole_arch_le_of_node_abs (β := β) hAp hPp
  have hAm' : _ ≤ k * Bd := pole_arch_le_of_node_abs (β := β) hAm hPm
  set c₀ := 2 * ((nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2) / Real.sqrt n with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  -- the upper bound, from the test with positive node value
  have hcp : c₀ ≤ 2 * (∫ u, oddProfile n u ^ 2) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith [le_integral_oddProfile_sq n]) hsq.le
  have hup : lam n ≤ k * Bd / c₀ :=
    (le_div_of_node_le (lt_of_lt_of_le hc₀0 hcp) hWp hAp').trans
      (div_le_div_of_nonneg_left hkBd hc₀0 hcp)
  -- the lower bound, from the test with negative node value
  have hcm : c₀ ≤ 2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n := by
    rw [integral_evenProfile_sq_eq]
    refine div_le_div_of_nonneg_right ?_ hsq.le
    have : 0 ≤ (nodeScale n)⁻¹ * ∫ u, narrowBump 0 u ^ 2 := by positivity
    linarith
  have hWm' : 0 ≤ weilArchRe (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1) +
      (β - 1) * (weilPoleTerm (EF.weilTest (oddMinus n).1.1 (oddMinus n).1.1)).re -
      2 * (∫ u, evenProfile n u ^ 2) / Real.sqrt n * (-lam n) := by linarith
  have hlo : -lam n ≤ k * Bd / c₀ :=
    (le_div_of_node_le (lt_of_lt_of_le hc₀0 hcm) hWm' hAm').trans
      (div_le_div_of_nonneg_left hkBd hc₀0 hcm)
  have hfin : Bd / c₀ = Bd * (Real.sqrt n * nodeScale n / (2 * ∫ u, narrowBump 0 u ^ 2)) := by
    rw [hc₀]
    field_simp
  have hkey := node_bound_le (n := n) (J₀ := ∫ u, narrowBump 0 u ^ 2) (P := bumpPoleConst)
    (K := gammaLogConst) (I₀ := bumpMassConst) (I₁ := bumpLogConst) hn1 hJ bumpMassConst_nonneg
    bumpLogConst_nonneg
  rw [← hmeq, ← hBd, ← hfin, ← hX] at hkey
  have hfinal : k * Bd / c₀ ≤ k * X * Real.sqrt n * (1 + Real.log n) := by
    calc k * Bd / c₀ = k * (Bd / c₀) := by ring
      _ ≤ k * (X * Real.sqrt n * (1 + Real.log n)) :=
          mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = k * X * Real.sqrt n * (1 + Real.log n) := by ring
  rw [abs_le]
  constructor <;> linarith

/-! ## General spectral densities: continuity, kernel identity, multipliers -/

/-- `y ↦ L(cos(yρ) K)`. -/
def cosineShiftK (lam : ℕ → ℝ) (K : ℂ → ℂ) (y : ℝ) : ℝ :=
  evenWeilDensity lam (fun z => Complex.cos (y * rhoC z) * K z)

theorem cosineShiftFn_eq_cosineShiftK (lam : ℕ → ℝ) (Φ : ℂ → ℂ) :
    cosineShiftFn lam Φ = cosineShiftK lam (specSq Φ) := rfl

theorem cos_mul_rhoC_mul_ofReal_re (y r : ℝ) (K : ℂ → ℂ) :
    (Complex.cos (y * rhoC r) * K r).re = Real.cos (y * Real.sqrt (r ^ 2 + 2)) * (K r).re := by
  rw [rhoC_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]

theorem continuous_cosineShiftK {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) : Continuous (cosineShiftK lam K) := by
  obtain ⟨ε, C, hε, hs⟩ := hK.strip
  have hC := hs.const_nonneg (by norm_num)
  have hKc : Continuous fun r : ℝ => (K r).re :=
    Complex.continuous_re.comp hK.continuous_ofReal
  have hint : Integrable fun r : ℝ => |(K r).re| * |EF.gammaBracket r| := by
    have h := hK.integrable_mul continuous_abs_gammaBracket (M := |gammaLogConst| + 2)
      abs_abs_gammaBracket_le_linear
    refine h.norm.congr (Eventually.of_forall fun r => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
  have hint1 : Integrable fun r : ℝ => |(K r).re| := by
    have h := hK.integrable_mul (P := fun _ => 1) continuous_const (M := 1) fun r => by simp
    refine h.norm.congr (Eventually.of_forall fun r => ?_)
    simp only [Real.norm_eq_abs, mul_one]
  -- the pole part
  have h1 : Continuous fun y : ℝ => (Complex.cos (y * rhoC (I / 2)) * K (I / 2) +
      Complex.cos (y * rhoC (-I / 2)) * K (-I / 2)).re := by
    exact Complex.continuous_re.comp (((Complex.continuous_cos.comp
      (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const).add
      ((Complex.continuous_cos.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const))
  -- the archimedean part
  have h2 : Continuous fun y : ℝ =>
      ∫ r : ℝ, (Complex.cos (y * rhoC r) * K r).re * EF.gammaBracket r := by
    simp_rw [cos_mul_rhoC_mul_ofReal_re]
    refine continuous_of_dominated (bound := fun r => |(K r).re| * |EF.gammaBracket r|)
      (fun y => ?_) (fun y => Filter.Eventually.of_forall fun r => ?_) hint
      (Filter.Eventually.of_forall fun r => ?_)
    · exact (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)))).mul
        hKc |>.mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have := Real.abs_cos_le_one (y * Real.sqrt (r ^ 2 + 2))
      have h0 : 0 ≤ |(K r).re| * |EF.gammaBracket r| := by positivity
      nlinarith [abs_nonneg (EF.gammaBracket r), abs_nonneg (K r).re]
    · exact (by fun_prop : Continuous fun y : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)) *
        (K r).re * EF.gammaBracket r)
  -- the prime part, locally uniformly
  have h3 : Continuous fun y : ℝ => ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (1 / Real.pi * ∫ r : ℝ, (Complex.cos (y * rhoC r) * K r).re *
        Real.cos (r * Real.log n)) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    set R := |y₀| + 1
    have hball : Set.Ioo (-R) R ∈ 𝓝 y₀ := Ioo_mem_nhds (by
      have := neg_abs_le y₀; linarith) (by have := le_abs_self y₀; linarith)
    refine (ContinuousOn.continuousAt ?_ hball)
    set D := 2 * (Real.exp (R * (5 / 4)) * C * (∫ r : ℝ, Real.exp (-(ε * |r|))) /
      (2 * Real.pi))
    have hD : 0 ≤ D := by
      have : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
      positivity
    have hCg := growthConst_nonneg hg
    refine continuousOn_tsum (u := fun n : ℕ => Cg * D * ((1 + Real.log n) *
      (n : ℝ) ^ (-(5 / 4 : ℝ)))) (fun n => ?_)
      ((summable_one_add_log_mul_rpow (b₁ := 5 / 4) (by norm_num)).mul_left _)
      (fun n y hy => ?_)
    · refine (continuous_const.mul (continuous_const.mul ?_)).continuousOn
      simp_rw [cos_mul_rhoC_mul_ofReal_re]
      refine continuous_of_dominated (bound := fun r => |(K r).re|)
        (fun y => ?_) (fun y => Filter.Eventually.of_forall fun r => ?_) hint1
        (Filter.Eventually.of_forall fun r => ?_)
      · exact (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)))).mul
          hKc |>.mul (by fun_prop)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := Real.abs_cos_le_one (y * Real.sqrt (r ^ 2 + 2))
        have h2 := Real.abs_cos_le_one (r * Real.log n)
        have h0 := abs_nonneg (K r).re
        calc |Real.cos (y * Real.sqrt (r ^ 2 + 2))| * |(K r).re| * |Real.cos (r * Real.log n)|
            ≤ 1 * |(K r).re| * 1 := by gcongr
          _ = |(K r).re| := by ring
      · exact (by fun_prop : Continuous fun y : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2)) *
          (K r).re * Real.cos (r * Real.log n))
    · rw [Real.norm_eq_abs, abs_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hgy := goodDensity_cos_mul y hK
      have hsy : StripDecay (fun z => Complex.cos (y * rhoC z) * K z) (5 / 4) ε
          (Real.exp (R * (5 / 4)) * C) := by
        refine ⟨(hgy.strip.choose_spec.choose_spec.2).diff, fun z hz => ?_⟩
        rw [norm_mul]
        have hyR : |y| ≤ R := by
          rw [abs_le]; exact ⟨hy.1.le, hy.2.le⟩
        have h1 : ‖Complex.cos (y * rhoC z)‖ ≤ Real.exp (R * (5 / 4)) :=
          (norm_cos_mul_rhoC_le y).trans (Real.exp_le_exp.mpr
            (mul_le_mul hyR hz (abs_nonneg _) (by positivity)))
        calc ‖Complex.cos (y * rhoC z)‖ * ‖K z‖
            ≤ Real.exp (R * (5 / 4)) * (C * Real.exp (-(ε * |z.re|))) :=
              mul_le_mul h1 (hs.bound z hz) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      have hb := abs_prime_le_of_strip hε hsy hgy hn
      calc |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
            |1 / Real.pi * ∫ r : ℝ, (Complex.cos (y * rhoC r) * K r).re *
              Real.cos (r * Real.log n)|
          ≤ (Cg * (1 + Real.log n)) * (D * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by
            refine mul_le_mul (abs_weight_le hg n) (hb.trans (le_of_eq ?_)) (abs_nonneg _)
              (by have := Real.log_natCast_nonneg n; positivity)
            ring
        _ = Cg * D * ((1 + Real.log n) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by ring
  unfold cosineShiftK evenWeilDensity
  exact (h1.add (continuous_const.mul h2)).sub h3

theorem abs_cosineShiftK_le {lam : ℕ → ℝ} {K : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftK lam K y : ℂ)) (t : ℝ) :
    |cosineShiftK lam K t| ≤ ν.real univ := by
  have h : cosineShiftK lam K t = ∫ ρ, Real.cos (t * ρ) ∂ν := by
    rw [← re_charFun_eq_integral_cos_of_finite, hν, Complex.ofReal_re]
  rw [h]
  calc |∫ ρ, Real.cos (t * ρ) ∂ν| ≤ ∫ _ρ, (1 : ℝ) ∂ν := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (integrable_const 1) (Eventually.of_forall fun ρ => ?_)
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    _ = ν.real univ := by simp

/-- **The kernel identity for a general density.**  If `τ(ρ) = ∫ κ(t) cos(tρ) dt` with
`|κ(t)| ≤ C e^{−b|t|}`, `b > 5/4`, then `L(K τ(ρ)) = ∫ τ dν`. -/
theorem evenWeilDensity_mul_kernel_of_good {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftK lam K y : ℂ)) {κ : ℝ → ℝ} (hκc : Continuous κ)
    {Cκ b : ℝ} (hb : 5 / 4 < b) (hκb : ∀ t, |κ t| ≤ Cκ * Real.exp (-(b * |t|))) :
    evenWeilDensity lam (fun z => K z * ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z)) =
      ∫ ρ, (∫ t : ℝ, κ t * Real.cos (t * ρ)) ∂ν := by
  have hκ : Integrable κ := integrable_of_exp_bound hκc (by linarith) hκb
  set P : ℝ → ℝ := fun t => evenPolePart (fun z => Complex.cos (t * rhoC z) * K z) with hP
  set A : ℝ → ℝ := fun t => evenArchPart (fun z => Complex.cos (t * rhoC z) * K z) with hA
  set Q : ℝ → ℝ := fun t => evenPrimePart lam (fun z => Complex.cos (t * rhoC z) * K z)
    with hQ
  have hsplit : ∀ t, cosineShiftK lam K t = P t + 1 / (2 * Real.pi) * A t - Q t :=
    fun t => rfl
  have hPe : ∀ t, P t = Real.cos (t * Real.sqrt (7 / 4)) * (K (I / 2) + K (-I / 2)).re :=
    fun t => by
      simp only [hP, evenPolePart, rhoC_I_div_two, rhoC_neg_I_div_two]
      rw [← mul_add, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.re_ofReal_mul]
  have hPi : Integrable fun t => κ t * P t := by
    simp_rw [hPe, ← mul_assoc]
    exact (integrable_mul_cos_of_integrable hκc hκ _ (by fun_prop)).mul_const _
  have hAi : Integrable fun t => κ t * A t := by
    have hint := integrable_prod_bound hK hκc hκ WeilHerglotz.continuous_gammaBracket
      (M := |gammaLogConst| + 2) (fun r => by
        have := abs_abs_gammaBracket_le_linear r; rwa [abs_abs] at this)
      (fun r t => Real.cos (t * Real.sqrt (r ^ 2 + 2))) (by fun_prop)
      (fun r t => Real.abs_cos_le_one _)
    refine hint.integral_prod_right.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair, hA, evenArchPart]
    rw [← integral_const_mul]
    congr 1; funext r
    rw [re_cos_mul_ofReal]
  have hφi : Integrable fun t => κ t * cosineShiftK lam K t :=
    (hκ.norm.mul_const (ν.real univ)).mono'
      ((hκc.mul (continuous_cosineShiftK hg hK)).aestronglyMeasurable)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_cosineShiftK_le hν t) (abs_nonneg _))
  have hQi : Integrable fun t => κ t * Q t := by
    have := (hPi.add (hAi.const_mul (1 / (2 * Real.pi)))).sub hφi
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hsplit]
    ring
  have hφ : ∀ t, cosineShiftK lam K t = ∫ ρ, Real.cos (t * ρ) ∂ν := fun t => by
    rw [← re_charFun_eq_integral_cos_of_finite, hν, Complex.ofReal_re]
  have hswap : ∫ ρ, (∫ t : ℝ, κ t * Real.cos (t * ρ)) ∂ν =
      ∫ t : ℝ, κ t * cosineShiftK lam K t := by
    have hint : Integrable (Function.uncurry fun (ρ t : ℝ) => κ t * Real.cos (t * ρ))
        (ν.prod volume) := by
      refine ((integrable_const (1 : ℝ)).mul_prod hκ.norm).mono'
        (by unfold Function.uncurry; fun_prop) (Eventually.of_forall fun p => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, one_mul]
      have := Real.abs_cos_le_one (p.2 * p.1)
      have := abs_nonneg (κ p.2)
      nlinarith
    rw [integral_integral_swap hint]
    congr 1; funext t
    rw [hφ, integral_const_mul]
  rw [hswap, evenWeilDensity_eq_parts, evenPolePart_mul_integral,
    evenArchPart_mul_integral hK hκc hκ, evenPrimePart_mul_integral hg hK hκc hb hκb]
  simp_rw [hsplit]
  have e : ∀ t, κ t * (P t + 1 / (2 * Real.pi) * A t - Q t) =
      κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) - κ t * Q t := fun t => by ring
  simp_rw [e]
  have h1 : Integrable fun t => κ t * P t + 1 / (2 * Real.pi) * (κ t * A t) :=
    hPi.add (hAi.const_mul _)
  rw [integral_sub h1 hQi, integral_add hPi (hAi.const_mul _), integral_const_mul]

/-- **Multiplier form for a general density.**  `L(K T) = ∫ Re T̃ dν`. -/
theorem evenWeilDensity_mul_multiplier_of_good {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {K : ℂ → ℂ}
    (hK : GoodDensity K) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftK lam K y : ℂ)) {T : ℂ → ℂ} (hT : Multiplier T) :
    evenWeilDensity lam (fun z => K z * T z) = ∫ ρ, (rhoLift T ρ).re ∂ν := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift hT
  set κ := stripTest (rhoLift T) with hκdef
  have hκc : Continuous κ := continuous_stripTest (by norm_num) hε hs
  have hκb : ∀ t, |κ t| ≤ C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) *
      Real.exp (-(3 / 2 * |t|)) := abs_stripTest_le (by norm_num) hε hs
  have hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = (rhoLift T s).re := fun s =>
    integral_stripTest_mul_cos (by norm_num) hε hs (rhoLift_neg T) (rhoLift_im_ofReal hT) s
  rw [evenWeilDensity_congr (K₂ := fun z => K z * ∫ t : ℝ, (κ t : ℂ) *
      Complex.cos (t * rhoC z))
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_I_div_two])
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_neg_I_div_two])
    (fun r => by rw [multiplier_eq_kernel_integral hT hκs (rhoC_ofReal r)]),
    evenWeilDensity_mul_kernel_of_good hg hK hν hκc (by norm_num : (5 / 4 : ℝ) < 3 / 2) hκb]
  congr 1; funext ρ
  exact hκs ρ

/-! ## Odd strip functions -/

/-- The odd strip function `−iz A(z)`: the transform of an odd real test. -/
def oddLift (A : ℂ → ℂ) (z : ℂ) : ℂ := -I * z * A z

theorem specSq_oddLift (A : ℂ → ℂ) (z : ℂ) : specSq (oddLift A) z = z ^ 2 * specSq A z := by
  unfold specSq oddLift
  rw [map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_conj]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem oddLift_neg {A : ℂ → ℂ} (heven : ∀ z, A (-z) = A z) (z : ℂ) :
    oddLift A (-z) = -oddLift A z := by
  unfold oddLift; rw [heven]; ring

theorem oddLift_sym {A : ℂ → ℂ} (hA : EvenStrip A) (r : ℝ) :
    oddLift A (-(r : ℂ)) = conj (oddLift A r) := by
  unfold oddLift
  rw [hA.even, map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_eq_iff_im.mpr (hA.real r)]
  ring

theorem stripDecay_oddLift {A : ℂ → ℂ} {ε C : ℝ} (hs : StripDecay A (5 / 4) ε C) (hε : 0 < ε) :
    StripDecay (oddLift A) (5 / 4) (ε / 2) (C * (2 / ε + 5 / 4)) :=
  hs.neg_I_mul_id (by norm_num) hε

theorem goodDensity_specSq_oddLift {A : ℂ → ℂ} (hA : EvenStrip A) :
    GoodDensity (specSq (oddLift A)) := by
  obtain ⟨ε, C, hε, hs⟩ := hA.strip
  have hs' := stripDecay_oddLift hs hε
  refine ⟨⟨2 * (ε / 2), (C * (2 / ε + 5 / 4)) ^ 2, by positivity, fun z hz => ?_,
    fun z hz => ?_⟩, fun z => ?_, fun r => specSq_im_ofReal r⟩
  · exact differentiableAt_specSq hs' hz
  · exact norm_specSq_le hs' hz
  · rw [specSq_oddLift, specSq_oddLift, specSq_neg_of_even hA.even, neg_sq]

theorem goodDensity_cosShift_oddLift (y : ℝ) {A : ℂ → ℂ} (hA : EvenStrip A) :
    GoodDensity (rhoCosShift y (oddLift A)) :=
  goodDensity_cos_mul y (goodDensity_specSq_oddLift hA)

/-! ## Strip positivity on odd strip functions -/

theorem stripTest_neg_of_odd {Φ : ℂ → ℂ} (hodd : ∀ z, Φ (-z) = -Φ z) (x : ℝ) :
    stripTest Φ (-x) = -stripTest Φ x := by
  have hI : (∫ r : ℝ, Φ r * cexp (-(I * r * ((-x : ℝ) : ℂ)))) =
      -∫ r : ℝ, Φ r * cexp (-(I * r * x)) := by
    rw [← integral_neg,
      ← integral_neg_eq_self (fun r : ℝ => Φ r * cexp (-(I * r * ((-x : ℝ) : ℂ))))]
    congr 1; funext r
    rw [Complex.ofReal_neg, hodd]
    push_cast
    ring_nf
  unfold stripTest stripInvFT
  rw [hI, mul_neg, Complex.neg_re]

theorem truncTest_neg_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (L x : ℝ) :
    truncTest F L (-x) = -truncTest F L x := by
  unfold truncTest
  rw [hodd, bulkCutoff_neg]
  ring

theorem archPoleEnergy_truncTest_sub_pole_nonneg_of_odd {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hodd : ∀ x, F (-x) = -F x) (L : ℝ) :
    0 ≤ archPoleEnergy (truncTest F L) -
        atomPairing lam (crossCorr (truncTest F L) (truncTest F L)) -
      (β - 1) * (2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2) := by
  have hc : ContDiff ℝ 2 fun u => (truncTest F L u : ℂ) := contDiff_ofReal_truncTest hF L
  have hcs : HasCompactSupport fun u => (truncTest F L u : ℂ) :=
    (hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero
  have hod : ∀ x, (fun u => (truncTest F L u : ℂ)) (-x) = -(fun u => (truncTest F L u : ℂ)) x :=
    fun x => by simp only [truncTest_neg_of_odd hodd]; push_cast; ring
  have hpos := h _ hc hcs hod
  have hpole := re_weilPoleTerm_weilTest_of_odd hc.continuous hcs hod
  rw [paperFT_ofRealFun_I_div_two, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpole
  unfold WeilPoleWeight.weilPoleWeightFunctional at hpos
  rw [Complex.add_re, re_weilFullFunctional_ofReal, weilArchRe_weilTest_truncTest_eq hF L] at hpos
  have e : (((β : ℂ) - 1) *
      (paperFT (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))
          (I / 2) +
        paperFT (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))
          (-I / 2))).re =
      (β - 1) * (-2 * (∫ u, truncTest F L u * Real.exp (-u / 2)) ^ 2) := by
    rw [show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    congr 1
  linarith

/-- **Strip positivity on odd strip functions at pole weight `β`.**
`L(Θ Θ^#) − 2(β − 1)|Θ(i/2)|² ≥ 0`. -/
theorem evenWeilDensity_specSq_sub_pole_nonneg_of_odd {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Θ : ℂ → ℂ}
    {b ε C : ℝ} (hb : 1 < b) (hε : 0 < ε) (hΘ : StripDecay Θ b ε C)
    (hsym : ∀ r : ℝ, Θ (-(r : ℂ)) = conj (Θ r)) (hodd : ∀ z, Θ (-z) = -Θ z) :
    0 ≤ evenWeilDensity lam (specSq Θ) - (β - 1) * (2 * ‖Θ (I / 2)‖ ^ 2) := by
  have hb0 : 0 < b := by linarith
  have hδ : 0 < b - 1 / 2 := by linarith
  rw [evenWeilDensity_specSq (by linarith) hε hΘ hsym]
  have hD := decayBound_stripTest (by linarith : 1 / 2 < b) hε hΘ
  have hE : ExpDecayTest (stripTest Θ) := hD.expDecayTest hδ
  have hFodd : ∀ x, stripTest Θ (-x) = -stripTest Θ x := stripTest_neg_of_odd hodd
  have hdec : ∀ x, |stripTest Θ x| ≤ C * stripDecayConst b ε * Real.exp (-(b * |x|)) := by
    intro x
    have h1 := (hD.2.2 x).1
    rwa [show 1 / 2 + (b - 1 / 2) = b by ring] at h1
  have hpole : Tendsto (fun L => ∫ u, truncTest (stripTest Θ) L u * Real.exp (-u / 2)) atTop
      (𝓝 (∫ u, stripTest Θ u * Real.exp (-u / 2))) := by
    have h1 := WeilPoleWeight.tendsto_integral_truncTest_mul_exp hδ hD (c := -(1 / 2))
      (by norm_num [abs_of_pos])
    have e : ∀ u : ℝ, -(1 / 2) * u = -u / 2 := fun u => by ring
    simp_rw [e] at h1
    exact h1
  have hval : ((∫ u, stripTest Θ u * Real.exp (-u / 2) : ℝ) : ℂ) = Θ (I / 2) := by
    rw [← paperFT_ofRealFun_I_div_two]
    exact paperFT_stripTest hb0 hε hΘ hsym (by simp; linarith)
  have hnorm : ‖Θ (I / 2)‖ ^ 2 = (∫ u, stripTest Θ u * Real.exp (-u / 2)) ^ 2 := by
    rw [← hval, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hlim := ((tendsto_archPoleEnergy_truncTest hE).sub
    (tendsto_atomPairing_truncTest_of_growth hg hE hb hD.2.1 hdec)).sub
    (((hpole.pow 2).const_mul 2).const_mul (β - 1))
  exact ge_of_tendsto' hlim fun L =>
    archPoleEnergy_truncTest_sub_pole_nonneg_of_odd h hD.1 hFodd L

/-- **Pole-free odd strip positivity.**  At every pole weight, `L(z² A A^#) ≥ 0` for every even
strip function `A` with `A(i/2) = 0`. -/
theorem evenWeilDensity_specSq_oddLift_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveOddAt β lam) {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {A : ℂ → ℂ}
    (hA : EvenStrip A) (hA0 : A (I / 2) = 0) : 0 ≤ evenWeilDensity lam (specSq (oddLift A)) := by
  obtain ⟨ε, C, hε, hs⟩ := hA.strip
  have h1 := evenWeilDensity_specSq_sub_pole_nonneg_of_odd h hg (by norm_num : (1 : ℝ) < 5 / 4)
    (half_pos hε) (stripDecay_oddLift hs hε) (oddLift_sym hA) (oddLift_neg hA.even)
  have h0 : oddLift A (I / 2) = 0 := by unfold oddLift; rw [hA0, mul_zero]
  simpa [h0] using h1

/-! ## The odd cosine-shift measure -/

theorem rhoCosShift_oddLift (y : ℝ) (A : ℂ → ℂ) (z : ℂ) :
    rhoCosShift y (oddLift A) z = z ^ 2 * rhoCosShift y A z := by
  unfold rhoCosShift; rw [specSq_oddLift]; ring

/-- **Positive definiteness from pole-free odd positivity.** -/
theorem sum_sum_cosineShiftFn_oddLift_nonneg {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 →
      0 ≤ evenWeilDensity lam (specSq (oddLift A)))
    {A : ℂ → ℂ} (hA : EvenStrip A) (hA0 : A (I / 2) = 0) {N : ℕ} (t c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * cosineShiftFn lam (oddLift A) (t j - t i) := by
  have hgood : ∀ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      GoodDensity (rhoCosShift (t p.2 - t p.1) (oddLift A)) :=
    fun p _ => goodDensity_cosShift_oddLift _ hA
  have hlin := evenWeilDensity_sum hg ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ)
    (fun p => c p.1 * c p.2) hgood
  have hsum : ∑ i, ∑ j, c i * c j * cosineShiftFn lam (oddLift A) (t j - t i) =
      ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
        c p.1 * c p.2 * evenWeilDensity lam (rhoCosShift (t p.2 - t p.1) (oddLift A)) := by
    rw [Finset.sum_product]; rfl
  have hC := evenStrip_cosComb t c hA
  have hS := evenStrip_sinComb t c hA
  have hcongr : evenWeilDensity lam (fun z => ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ
      Finset.univ, ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) (oddLift A) z) =
      evenWeilDensity lam (fun z => specSq (oddLift (cosComb t c A)) z +
        specSq (oddLift (sinComb t c A)) z) := by
    have key : ∀ z : ℂ, |z.im| < Real.sqrt 2 →
        ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
          ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) (oddLift A) z =
        specSq (oddLift (cosComb t c A)) z + specSq (oddLift (sinComb t c A)) z := by
      intro z hz
      simp_rw [rhoCosShift_oddLift, specSq_oddLift]
      rw [← mul_add, specSq_cosComb_add_specSq_sinComb t c A hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    have hI1 : |(I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    have hI2 : |(-I / 2 : ℂ).im| < Real.sqrt 2 := abs_im_lt_sqrt_two (by norm_num [abs_of_pos])
    refine evenWeilDensity_congr (key _ hI1) (key _ hI2) fun r => key _ ?_
    exact abs_im_lt_sqrt_two (by simp; norm_num)
  have hC0 : cosComb t c A (I / 2) = 0 := cosComb_I_div_two t c hA0
  have hS0 : sinComb t c A (I / 2) = 0 := sinComb_I_div_two t c hA0
  rw [hsum, ← hlin, hcongr, evenWeilDensity_add hg (goodDensity_specSq_oddLift hC)
    (goodDensity_specSq_oddLift hS)]
  exact add_nonneg (hpos _ hC hC0) (hpos _ hS hS0)

/-- **The odd cosine-shift measure of a pole-free strip function.** -/
theorem exists_cosineShift_measure_oddLift {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 →
      0 ≤ evenWeilDensity lam (specSq (oddLift A)))
    {A : ℂ → ℂ} (hA : EvenStrip A) (hA0 : A (I / 2) = 0) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ y, charFun ν y = (cosineShiftK lam (specSq (oddLift A)) y : ℂ) :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefiniteOnReal_of_real (cosineShiftFn_neg lam (oddLift A))
      fun _ t c => sum_sum_cosineShiftFn_oddLift_nonneg hg hpos hA hA0 t c)
    (Complex.continuous_ofReal.comp
      (continuous_cosineShiftK hg (goodDensity_specSq_oddLift hA)))

/-- **Multipliers with a nonnegative lift are nonnegative on odd pole-free spectral squares.** -/
theorem evenWeilDensity_specSq_oddLift_mul_multiplier_nonneg {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 →
      0 ≤ evenWeilDensity lam (specSq (oddLift A)))
    {A : ℂ → ℂ} (hA : EvenStrip A) (hA0 : A (I / 2) = 0) {T : ℂ → ℂ} (hT : Multiplier T)
    (hTpos : ∀ ρ : ℝ, 0 ≤ (rhoLift T ρ).re) :
    0 ≤ evenWeilDensity lam (fun z => specSq (oddLift A) z * T z) := by
  obtain ⟨ν, hfin, hν⟩ := exists_cosineShift_measure_oddLift hg hpos hA hA0
  rw [evenWeilDensity_mul_multiplier_of_good hg (goodDensity_specSq_oddLift hA) hν hT]
  exact integral_nonneg hTpos

/-! ## Resonators with an odd profile -/

theorem paperFT_ofReal_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (z : ℂ) :
    paperFT (fun u => ((deriv g u : ℝ) : ℂ)) z = oddLift (paperFT fun u => (g u : ℂ)) z := by
  have hgC : ContDiff ℝ 1 fun u => (g u : ℂ) := (contDiff_ofReal_comp hg).of_le (by norm_num)
  have hgcC : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have e : (fun u => ((deriv g u : ℝ) : ℂ)) = deriv fun u => (g u : ℂ) := by
    funext u
    have hd : HasDerivAt g (deriv g u) u :=
      ((hg.differentiable (by norm_num)) u).hasDerivAt
    exact (hd.ofReal_comp).deriv.symm
  rw [e, paperFT_deriv_of_compact hgC hgcC]
  unfold oddLift
  ring

/-- **Pole-free odd positivity is positivity on nonnegative resonators with an odd profile.**
Let `g` be an even real `C³` profile of compact support with `ĝ(i/2) = 0`.  If `L` is nonnegative
on odd pole-free spectral squares, then `Re W(R ⋆ R̃) ≥ 0` for `R = Σ_k c_k g'(· − x_k)` with
`c_k ≥ 0`. -/
theorem re_weilFullFunctional_derivTranslateSum_nonneg {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n))
    (hpos : ∀ A : ℂ → ℂ, EvenStrip A → A (I / 2) = 0 →
      0 ≤ evenWeilDensity lam (specSq (oddLift A)))
    {ι : Type*} (s : Finset ι) {c : ι → ℝ} (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ)
    {g : ℝ → ℝ} (hg3 : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * deriv g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * deriv g (u - x k) : ℝ) : ℂ)))).re := by
  have hg2 : ContDiff ℝ 2 g := hg3.of_le (by norm_num)
  have hd2 : ContDiff ℝ 2 (deriv g) := hg3.deriv'
  have hdc : HasCompactSupport (deriv g) := hgc.deriv
  set f : ℝ → ℝ := fun u => ∑ k ∈ s, c k * deriv g (u - x k) with hfdef
  have hf2 : ContDiff ℝ 2 f :=
    ContDiff.sum fun k _ => contDiff_const.mul (hd2.comp (contDiff_id.sub contDiff_const))
  have hfc : HasCompactSupport f := hasCompactSupport_finset_sum s fun k _ =>
    (hdc.comp_homeomorph (Homeomorph.subRight (x k))).mul_left
  rw [re_weilFullFunctional_ofReal_eq_evenWeilDensity lam hf2 hfc]
  refine ge_of_tendsto (tendsto_evenWeilDensity_gaussDamped hg hf2 hfc)
    (Eventually.of_forall fun k => ?_)
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hgcc : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have hdcc : HasCompactSupport fun u => ((deriv g u : ℝ) : ℂ) :=
    hdc.comp_left Complex.ofReal_zero
  set G := paperFT fun u => (g u : ℂ) with hGdef
  have hF : paperFT (fun u => (f u : ℂ)) = fun z => translateExpSum s c x z * oddLift G z := by
    funext z
    have h1 := paperFT_sum_translate s (fun k => (c k : ℂ)) x
      (contDiff_ofReal_comp hd2).continuous hdcc z
    have e : (fun u => (f u : ℂ)) =
        fun u => ∑ k ∈ s, (c k : ℂ) * ((deriv g (u - x k) : ℝ) : ℂ) := by
      funext u; simp only [hfdef]; push_cast; rfl
    rw [e, h1, paperFT_ofReal_deriv hg2 hgc]
    rfl
  have hGe : ∀ z, G (-z) = G z := paperFT_neg_of_even fun u => by simp only [hge]
  have hG0' : G (-I / 2) = 0 := by rw [neg_div, hGe]; exact hg0
  have hGr : ∀ r : ℝ, (G r).im = 0 := fun r => by
    have h1 := paperFT_ofReal_neg_conj g (r : ℂ)
    rw [Complex.conj_ofReal, ← hGdef, hGe] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  -- the pole-free even profile `Φ = ĝ e^{−εz²/2}`
  set Φ := gaussDamped G (ε / 2) with hΦdef
  obtain ⟨N, hN, hb⟩ := exists_norm_paperFT_le_of_compact (contDiff_ofReal_comp hg2) hgcc (9 / 4)
  have hGb : ∀ z : ℂ, |z.im| ≤ 9 / 4 → ‖G z‖ ≤ N := fun z hz =>
    (hb z hz).trans (div_le_self hN (by nlinarith [sq_nonneg ‖z‖]))
  have hS := stripDecay_gaussDamped (differentiable_paperFT_of_compact
    (contDiff_ofReal_comp hg2).continuous hgcc) hN hGb (half_pos hε)
  have hΦ : EvenStrip Φ := by
    refine ⟨⟨1, _, one_pos, fun z hz => hS.diff z (by linarith),
      fun z hz => hS.bound z (by linarith)⟩, fun z => ?_, fun r => ?_⟩
    · simp only [hΦdef, gaussDamped, hGe, neg_sq]
    · simp only [hΦdef, gaussDamped]
      rw [cexp_neg_mul_sq_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hGr r]
      ring
  have hΦ0 : Φ (I / 2) = 0 := by simp [hΦdef, gaussDamped, hg0]
  have hcongr : evenWeilDensity lam (specSq (gaussDamped (paperFT fun u => (f u : ℂ)) ε)) =
      evenWeilDensity lam (fun z => specSq (oddLift Φ) z *
        gaussDamped (translatePairExp s c x) ε z) := by
    refine evenWeilDensity_congr ?_ ?_ fun r => ?_
    · simp [specSq, gaussDamped, hF, hΦdef, oddLift, hg0]
    · have hc2 : conj (-I / 2 : ℂ) = I / 2 := by
        rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
      simp only [specSq, gaussDamped, hF, hΦdef, oddLift, hG0', hc2, hg0]
      simp
    · rw [specSq_gaussDamped, specSq_oddLift, specSq_gaussDamped, specSq_ofReal_eq,
        specSq_ofReal_eq, hF]
      simp only [gaussDamped]
      rw [translatePairExp_ofReal, cexp_neg_mul_sq_ofReal, cexp_neg_mul_sq_ofReal,
        cexp_neg_mul_sq_ofReal, norm_mul, mul_pow]
      have hoddr : ‖oddLift G r‖ ^ 2 = r ^ 2 * ‖G r‖ ^ 2 := by
        unfold oddLift
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hoddr]
      push_cast
      have e : Complex.exp (-((2 * ε : ℝ) : ℂ) * (r : ℂ) ^ 2) =
          Complex.exp (-((2 * (ε / 2) : ℝ) : ℂ) * (r : ℂ) ^ 2) *
            Complex.exp (-(ε : ℂ) * (r : ℂ) ^ 2) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp only [cexp_neg_mul_sq_ofReal] at e ⊢
      push_cast at e ⊢
      rw [e]
      ring
  rw [hcongr]
  exact evenWeilDensity_specSq_oddLift_mul_multiplier_nonneg hg hpos hΦ hΦ0
    (multiplier_gaussDamped_pairExp s c x hε) (re_rhoLift_gaussDamped_pairExp_nonneg s hc x ε)

/-- **Odd positivity at any pole weight is positivity on nonnegative resonators with an odd
profile.**  If `lam` is Weil-positive at pole weight `β` on all odd tests, then
`Re W(R ⋆ R̃) ≥ 0` for every resonator `R = Σ_k c_k g'(· − x_k)` with `c_k ≥ 0` and an even real
`C³` profile `g` of compact support with `ĝ(i/2) = 0`. -/
theorem re_weilFullFunctional_derivTranslateSum_nonneg_of_weilPositiveOddAt {β : ℝ}
    {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) {ι : Type*} (s : Finset ι) {c : ι → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (x : ι → ℝ) {g : ℝ → ℝ} (hg3 : ContDiff ℝ 3 g)
    (hgc : HasCompactSupport g) (hge : ∀ u, g (-u) = g u)
    (hg0 : paperFT (fun u => (g u : ℂ)) (I / 2) = 0) :
    0 ≤ (weilFullFunctional lam
      (EF.weilTest (fun u => ((∑ k ∈ s, c k * deriv g (u - x k) : ℝ) : ℂ))
        (fun u => ((∑ k ∈ s, c k * deriv g (u - x k) : ℝ) : ℂ)))).re := by
  obtain ⟨Cg, -, hgr⟩ := exists_abs_le_of_weilPositiveOddAt_any h
  exact re_weilFullFunctional_derivTranslateSum_nonneg hgr
    (fun A hA hA0 => evenWeilDensity_specSq_oddLift_nonneg h hgr hA hA0) s hc x hg3 hgc hge hg0

end RHTower.OddSector

end
