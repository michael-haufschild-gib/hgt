import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalSmallTimeRegime
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailBounds
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Chen–Gupta–Li Lemma 6.2, principal character: the deep line with the sharp exponent

On the deep line `Re s = −2k` of the principal tail contour, the far-tail integrand is
`H(s) N^s χ_reg(s − it) E_q(s − it) Σ_{n>M} n^{−(1−s+it)}`.  This module bounds it pointwise with
the *sharp* growth exponent of the functional factor:

* `‖χ_reg(z)‖ ≤ C_k (1+|Im z|)^{2k+1/2}` on `Re z = −2k`, where
  `χ_reg(z) = 2(2π)^{−(1−z)} Γ(1−z) cos(π(1−z)/2)` (corpus two-sided Stirling bound
  `norm_Gamma_one_add_nat_bounds` on `Re = 1 + 2k`, `‖cos w‖ ≤ e^{|Im w|}`, and the corpus
  all-heights bound below unit height);
* `‖Σ_{n>M} χ(n) n^{−s}‖ ≤ M^{−2k}/(2k)` on `Re s = 1 + 2k` for every Dirichlet character
  (the proof of the corpus `cglLemma62_far_dirichletTail_norm_le`, which is stated for induced
  nonprincipal characters, uses only `|χ(n)| ≤ 1`);
* the deep Euler budget `∏_{p | q} 4(1 + p^{2k}) ≤ 2 q^{2k+2}` (`8 ≤ p²` for `p ≥ 3`).
-/

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped LSeries.notation

noncomputable section

namespace RHTower

/-- The constant of the sharp far-line bound at heights `≥ 1`. -/
def cglPrincipalFarLineConst (k : ℕ) : ℝ :=
  2 * (2 * Real.pi) ^ (-(1 + 2 * (k : ℝ))) * Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) *
    ((2 : ℝ) + ((2 * k : ℕ) : ℝ)) ^ (2 * k)

theorem cglPrincipalFarLineConst_nonneg (k : ℕ) : 0 ≤ cglPrincipalFarLineConst k := by
  unfold cglPrincipalFarLineConst
  positivity

/-- **Sharp far-line bound, high part.**  On `Re z = −2k`, `|Im z| ≥ 1`:
`‖χ_reg(z)‖ ≤ C_k √|Im z| |Im z|^{2k}`. -/
theorem norm_cglLemma62PrincipalRegularizedFunctionalFactor_far_high (k : ℕ) {z : ℂ}
    (hre : z.re = -2 * (k : ℝ)) (him : 1 ≤ |z.im|) :
    ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
      cglPrincipalFarLineConst k * (Real.sqrt |z.im| * |z.im| ^ (2 * k)) := by
  have h1z : (1 : ℂ) - z = 1 + ((-z.im : ℝ) : ℂ) * I + ((2 * k : ℕ) : ℂ) := by
    apply Complex.ext <;> simp [hre]
  obtain ⟨-, hΓ⟩ := GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_nat_bounds (2 * k)
    (t := -z.im) (by rwa [abs_neg])
  rw [abs_neg, ← h1z] at hΓ
  have hcpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ = (2 * Real.pi) ^ (-(1 + 2 * (k : ℝ))) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp [hre]
    ring
  have hcos : ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤ Real.exp (Real.pi * |z.im| / 2) := by
    refine (norm_cos_le_exp_abs_im _).trans (le_of_eq ?_)
    congr 1
    have him' : (Real.pi * (1 - z) / 2 : ℂ).im = -(Real.pi * z.im / 2) := by
      simp
      ring
    rw [him', abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  have hy0 : 0 ≤ |z.im| := abs_nonneg _
  have hc : 0 < 1 - Real.exp (-2) := by
    have := Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0)
    rw [Real.exp_zero] at this
    linarith
  have hsqrt : Real.sqrt (2 * Real.pi * |z.im| / (1 - Real.exp (-2))) =
      Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |z.im| := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
  rw [norm_mul, norm_mul, norm_mul, hcpow, show ‖(2 : ℂ)‖ = 2 by norm_num]
  calc 2 * (2 * Real.pi) ^ (-(1 + 2 * (k : ℝ))) * ‖Complex.Gamma (1 - z)‖ *
        ‖Complex.cos (Real.pi * (1 - z) / 2)‖
      ≤ 2 * (2 * Real.pi) ^ (-(1 + 2 * (k : ℝ))) *
          (Real.sqrt (2 * Real.pi * |z.im| / (1 - Real.exp (-2))) *
            (((2 : ℝ) + ((2 * k : ℕ) : ℝ)) * |z.im|) ^ (2 * k) *
              Real.exp (-(Real.pi * |z.im| / 2))) *
          Real.exp (Real.pi * |z.im| / 2) := by
        gcongr
    _ = cglPrincipalFarLineConst k * (Real.sqrt |z.im| * |z.im| ^ (2 * k)) := by
        rw [hsqrt, mul_pow, cglPrincipalFarLineConst]
        have hexp : Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = 2 * (2 * Real.pi) ^ (-(1 + 2 * (k : ℝ))) *
              (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |z.im| *
                (((2 : ℝ) + ((2 * k : ℕ) : ℝ)) ^ (2 * k) * |z.im| ^ (2 * k))) *
              (Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2)) := by ring
          _ = _ := by rw [hexp]; ring

/-- `√y · y^{2k} ≤ (1+y)^{2k+1/2}` for `y ≥ 0`. -/
theorem sqrt_mul_pow_le_one_add_rpow (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y * y ^ (2 * k) ≤ (1 + y) ^ (2 * (k : ℝ) + 1 / 2) := by
  have h1 : 0 < 1 + y := by linarith
  rw [Real.rpow_add h1, Real.sqrt_eq_rpow, show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, mul_comm (y ^ (1 / 2 : ℝ))]
  exact mul_le_mul (pow_le_pow_left₀ hy (by linarith) _)
    (Real.rpow_le_rpow hy (by linarith) (by norm_num)) (by positivity) (by positivity)

/-- **Sharp far-line bound.**  `‖χ_reg(z)‖ ≤ C (1+|Im z|)^{2k+1/2}` on the whole line `Re z = −2k`. -/
theorem cglLemma62_principalRegularizedFactor_far_sharp (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re = -2 * (k : ℝ) →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
        C * (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) := by
  obtain ⟨C₀, n, hC₀, hlow⟩ := cglLemma62_exists_bound_principalRegularizedFactor_all_heights
    (a := -2 * (k : ℝ)) (b := -2 * (k : ℝ)) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hck := cglPrincipalFarLineConst_nonneg k
  refine ⟨C₀ * 2 ^ n + cglPrincipalFarLineConst k, by positivity, ?_⟩
  intro z hre
  have hpow1 : 1 ≤ (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) :=
    Real.one_le_rpow (by linarith [abs_nonneg z.im]) (by positivity)
  by_cases him : 1 ≤ |z.im|
  · have h := norm_cglLemma62PrincipalRegularizedFunctionalFactor_far_high k hre him
    have hs := sqrt_mul_pow_le_one_add_rpow k (abs_nonneg z.im)
    calc _ ≤ cglPrincipalFarLineConst k * (Real.sqrt |z.im| * |z.im| ^ (2 * k)) := h
      _ ≤ cglPrincipalFarLineConst k * (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ C₀ * 2 ^ n * (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) := by positivity
          nlinarith
  · have h := hlow z hre.ge hre.le
    have hy : 1 + |z.im| ≤ 2 := by linarith [not_le.mp him]
    have h2 : C₀ * (1 + |z.im|) ^ n ≤ C₀ * 2 ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy n) hC₀
    have h3 : C₀ * 2 ^ n ≤ C₀ * 2 ^ n * (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) :=
      le_mul_of_one_le_right (by positivity) hpow1
    have h4 : 0 ≤ cglPrincipalFarLineConst k * (1 + |z.im|) ^ (2 * (k : ℝ) + 1 / 2) := by
      positivity
    nlinarith

/-- The far-line Dirichlet tail of any character: `‖Σ_{n>M} χ(n) n^{−s}‖ ≤ M^{−2k}/(2k)` on
`Re s = 1 + 2k` (same proof as the corpus `cglLemma62_far_dirichletTail_norm_le`). -/
theorem cglLemma62_far_dirichletTail_norm_le_of_character {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (d : CGLLemma62TailContourDepth) (J : CGLLemma62TailCutoff) (v : ℝ) :
    ‖cglLemma62DirichletTail χ J.value (cglLemma62FarRightPointAC t d v)‖ ≤
      (J.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)) := by
  let s := cglLemma62FarRightPointAC t d v
  have hsre : s.1.re = 1 + 2 * (d.value : ℝ) := by
    unfold s cglLemma62FarRightPointAC cglLemma62FarRightPoint cglLemma62FarLeftPoint
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    norm_num
  have hdpos : (0 : ℝ) < d.value := by exact_mod_cast d.positive
  let q' : ℝ := -2 * (d.value : ℝ)
  have hq : q' < 0 := by dsimp [q']; linarith
  have hweight : Summable (fun k : ℕ => ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q' - 1)) :=
    GaloisForLFunctions.HTGeometry.summable_shift_rpow hq J.value
  have hterm : Summable (fun n : ℕ => LSeries.term (↗χ) s.1 n) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ s.2
  have htailnorm : Summable (fun k : ℕ => ‖LSeries.term (↗χ) s.1 (k + (J.value + 1))‖) :=
    (summable_nat_add_iff (f := fun n : ℕ => ‖LSeries.term (↗χ) s.1 n‖) (J.value + 1)).mpr
      hterm.norm
  rw [cglLemma62_dirichletTail_eq_tsum_shift χ J.value s]
  refine (norm_tsum_le_tsum_norm htailnorm).trans ?_
  refine (htailnorm.tsum_mono hweight ?_).trans ?_
  · intro k
    let n : ℕ := k + (J.value + 1)
    have hn : n ≠ 0 := by dsimp [n]; omega
    have hχ : ‖χ n‖ ≤ ‖(1 : ℂ)‖ := by simpa using χ.norm_le_one n
    have hle : ‖LSeries.term (↗χ) s.1 n‖ ≤ ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ :=
      LSeries.norm_term_le (f := (↗χ)) (g := fun _ : ℕ => (1 : ℂ)) s.1 hχ
    have hnorm : ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ = 1 / (n : ℝ) ^ s.1.re := by
      rw [LSeries.norm_term_eq, if_neg hn]
      norm_num
    change ‖LSeries.term (↗χ) s.1 n‖ ≤ _
    calc ‖LSeries.term (↗χ) s.1 n‖ ≤ ‖LSeries.term (fun _ : ℕ => (1 : ℂ)) s.1 n‖ := hle
      _ = 1 / (n : ℝ) ^ s.1.re := hnorm
      _ = ((J.value : ℝ) + 1 + (k : ℝ)) ^ (q' - 1) := by
        rw [hsre]
        have hncast : (n : ℝ) = (J.value : ℝ) + 1 + (k : ℝ) := by dsimp [n]; push_cast; ring
        rw [hncast, one_div, ← Real.rpow_neg (by positivity : 0 ≤ (J.value : ℝ) + 1 + (k : ℝ))]
        dsimp [q']
        congr 1
        ring
  · simpa only [q', neg_mul, neg_neg] using
      GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le hq J.one_le

/-- The deep Euler budget: `∏_{p | q} 4(1 + p^{2k}) ≤ 2 q^{2k+2}`. -/
theorem cglLemma62PrincipalCorrectionDeepBudget_le (Q : CGLPositiveModulus)
    (d : CGLLemma62TailContourDepth) :
    cglLemma62PrincipalCorrectionDeepBudget Q d ≤ 2 * (Q.value : ℝ) ^ (2 * d.value + 2) := by
  classical
  set k := d.value
  have hfac : ∀ p ∈ Q.value.primeFactors, 4 * (1 + (p : ℝ) ^ (2 * (k : ℝ))) ≤
      (if p = 2 then (2 : ℝ) else 1) * (p : ℝ) ^ (2 * k + 2) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpow : (p : ℝ) ^ (2 * (k : ℝ)) = (p : ℝ) ^ (2 * k) := by
      rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hpow]
    have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (2 * k) := one_le_pow₀ (by linarith)
    have h8 : 4 * (1 + (p : ℝ) ^ (2 * k)) ≤ 8 * (p : ℝ) ^ (2 * k) := by linarith
    rw [pow_add]
    split_ifs with h2
    · subst h2; push_cast at h8 ⊢; nlinarith
    · have hp3 : (3 : ℝ) ≤ p := by
        have := hpp.two_le
        have : p ≠ 2 := h2
        exact_mod_cast (by omega : 3 ≤ p)
      have hp9 : (9 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      have hx := mul_le_mul_of_nonneg_left hp9 (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ (2 * k))
      linarith
  have hprod : ∏ p ∈ Q.value.primeFactors, ((if p = 2 then (2 : ℝ) else 1) * (p : ℝ) ^ (2 * k + 2)) =
      (if 2 ∈ Q.value.primeFactors then (2 : ℝ) else 1) *
        ((∏ p ∈ Q.value.primeFactors, p : ℕ) : ℝ) ^ (2 * k + 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Q.value.primeFactors 2, Finset.prod_pow]
    push_cast
    rfl
  have hrad : ((∏ p ∈ Q.value.primeFactors, p : ℕ) : ℝ) ≤ Q.value := by
    exact_mod_cast Nat.le_of_dvd Q.positive (Nat.prod_primeFactors_dvd Q.value)
  unfold cglLemma62PrincipalCorrectionDeepBudget
  calc ∏ p ∈ Q.value.primeFactors, (4 * (1 + (p : ℝ) ^ (2 * (k : ℝ))))
      ≤ ∏ p ∈ Q.value.primeFactors, ((if p = 2 then (2 : ℝ) else 1) * (p : ℝ) ^ (2 * k + 2)) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = _ := hprod
    _ ≤ 2 * (Q.value : ℝ) ^ (2 * k + 2) := by
        gcongr
        · split_ifs <;> norm_num

/-- **Pointwise far-tail bound, Mellin factor kept.**  With `C_χ` a sharp far-line constant,
`‖FarTail(v)‖ ≤ ‖H(−2k+iv)‖ N^{−2k} C_χ (1+|v−t|)^{2k+1/2} · 2q^{2k+2} · M^{−2k}/(2k)`. -/
theorem norm_cglLemma62PrincipalFarTailIntegrand_le_mellin (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (J : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) {Cχ : ℝ}
    (hχ : ∀ z : ℂ, z.re = -2 * (d.value : ℝ) →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
        Cχ * (1 + |z.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) (v : ℝ) :
    ‖cglLemma62PrincipalFarTailIntegrand w N Q t J.value d v‖ ≤
      ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ *
        (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (Cχ * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2)) *
            (2 * (Q.value : ℝ) ^ (2 * d.value + 2)) *
              ((J.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) := by
  have hpt : cglLemma62FarLeftPoint d v = (((-2 * (d.value : ℝ)) : ℝ) : ℂ) + (v : ℂ) * I := by
    unfold cglLemma62FarLeftPoint; push_cast; ring
  have hN : ‖(N.value : ℂ) ^ (cglLemma62FarLeftPoint d v)‖ = (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive, hpt]
    simp
  have hzre : (cglLemma62FarLeftPoint d v - (t : ℂ) * I).re = -2 * (d.value : ℝ) := by
    rw [hpt]; simp
  have hzim : (cglLemma62FarLeftPoint d v - (t : ℂ) * I).im = v - t := by
    rw [hpt]; simp
  have hχz := hχ _ hzre
  rw [hzim] at hχz
  have hE := norm_cglLemma62PrincipalEulerCorrectionAt_le_deep Q d
    (z := cglLemma62FarLeftPoint d v - (t : ℂ) * I) hzre.ge
    (by rw [hzre]; have : (0 : ℝ) ≤ d.value := Nat.cast_nonneg _; linarith)
  have hB := cglLemma62PrincipalCorrectionDeepBudget_le Q d
  have hT := cglLemma62_far_dirichletTail_norm_le_of_character
    (1 : DirichletCharacter ℂ Q.value) t d J v
  unfold cglLemma62PrincipalFarTailIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hN]
  have hχ0 : 0 ≤ Cχ * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) :=
    (norm_nonneg _).trans hχz
  have hH0 : 0 ≤ ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ := norm_nonneg _
  have hN0 : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hq0 : 0 ≤ 2 * (Q.value : ℝ) ^ (2 * d.value + 2) := by positivity
  exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul le_rfl le_rfl hN0 hH0) hχz (norm_nonneg _)
    (mul_nonneg hH0 hN0)) (hE.trans hB) (norm_nonneg _) (mul_nonneg (mul_nonneg hH0 hN0) hχ0))
    hT (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hH0 hN0) hχ0) hq0)

/-- **Pointwise far-tail bound.**  With `C_χ` a sharp far-line constant,
`‖FarTail(v)‖ ≤ B_H N^{−2k} C_χ (1+|v−t|)^{2k+1/2} · 2q^{2k+2} · M^{−2k}/(2k)`. -/
theorem norm_cglLemma62PrincipalFarTailIntegrand_le (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (t : ℝ) (J : CGLLemma62TailCutoff)
    (d : CGLLemma62TailContourDepth) {Cχ : ℝ}
    (hχ : ∀ z : ℂ, z.re = -2 * (d.value : ℝ) →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤
        Cχ * (1 + |z.im|) ^ (2 * (d.value : ℝ) + 1 / 2)) (v : ℝ) :
    ‖cglLemma62PrincipalFarTailIntegrand w N Q t J.value d v‖ ≤
      cglLemma62MellinLineDecayBudget w (-2 * (d.value : ℝ)) 0 *
        (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (Cχ * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2)) *
            (2 * (Q.value : ℝ) ^ (2 * d.value + 2)) *
              ((J.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) := by
  have hH := cglLemma62_mellinTransform_vertical_rapidDecay w (-2 * (d.value : ℝ)) 0 v
  rw [pow_zero, one_mul] at hH
  have hpt : cglLemma62FarLeftPoint d v = (((-2 * (d.value : ℝ)) : ℝ) : ℂ) + (v : ℂ) * I := by
    unfold cglLemma62FarLeftPoint; push_cast; ring
  rw [← hpt] at hH
  have h := norm_cglLemma62PrincipalFarTailIntegrand_le_mellin w N Q t J d hχ v
  have hzre : (cglLemma62FarLeftPoint d v - (t : ℂ) * I).re = -2 * (d.value : ℝ) := by
    rw [hpt]; simp
  have hzim : (cglLemma62FarLeftPoint d v - (t : ℂ) * I).im = v - t := by
    rw [hpt]; simp
  have hχ0 : 0 ≤ Cχ * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    have := hχ _ hzre
    rw [hzim] at this
    exact (norm_nonneg _).trans this
  have hN0 : 0 ≤ (N.value : ℝ) ^ (-2 * (d.value : ℝ)) := by positivity
  have hq0 : 0 ≤ 2 * (Q.value : ℝ) ^ (2 * d.value + 2) := by positivity
  have hJ0 : 0 ≤ (J.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ)) := by positivity
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH hN0) hχ0) hq0) hJ0)

end RHTower

end
