import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalCriticalIntegrability
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalDecay
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# Chen--Gupta--Li Lemma 6.2: principal finite carrier on the displacement strip

Polynomial envelopes for every factor of the regularized principal finite
carrier, uniformly on the strip `-1 ≤ Re s ≤ 1/2`: the Gamma--cosine
multiplier grows polynomially (Stirling decay of `Γ` against the exponential
growth of the cosine), the finite Euler correction is bounded, the Dirichlet
head is bounded by its length, and the Mellin kernel decays to every order.
Together they give the quadratic decay `‖F(x+iy)‖ ≤ C/y²` on horizontal
segments of the strip.
-/

open Complex MeasureTheory Filter Set
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Polynomial growth of the regular Gamma--cosine multiplier on the
displacement strip, above unit height. -/
theorem cglLemma62_exists_bound_principalRegularizedFactor_strip :
    ∃ C : ℝ, ∃ n : ℕ, 0 ≤ C ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 / 2 → 1 ≤ |z.im| →
      ‖cglLemma62PrincipalRegularizedFunctionalFactor z‖ ≤ C * |z.im| ^ n := by
  obtain ⟨C, n, hC, hΓ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (a := 1 / 2) (by norm_num) 2
  refine ⟨2 * C, n, by positivity, ?_⟩
  intro z hlo hhi him
  have hpoint : (1 : ℂ) - z = ((1 - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hΓz : ‖Complex.Gamma (1 - z)‖ ≤
      C * |z.im| ^ n * Real.exp (-(Real.pi * |z.im| / 2)) := by
    have h := hΓ (1 - z.re) (-z.im) (by linarith) (by linarith) (by rwa [abs_neg])
    rw [abs_neg] at h
    rwa [hpoint]
  have hbase : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-(1 - z)).re = -(1 - z.re) := by simp
    rw [hre]
    calc
      (2 * Real.pi) ^ (-(1 - z.re)) ≤ (2 * Real.pi) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = 1 := Real.rpow_zero _
  have hcos : ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤
      Real.exp (Real.pi * |z.im| / 2) := by
    refine (norm_cos_le_exp_abs_im _).trans ?_
    apply Real.exp_le_exp.mpr
    have him' : ((Real.pi : ℂ) * (1 - z) / 2).im = -(Real.pi * z.im / 2) := by
      simp
      ring
    rw [him', abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  unfold cglLemma62PrincipalRegularizedFunctionalFactor
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  have hexp : Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hΓ0 : 0 ≤ ‖Complex.Gamma (1 - z)‖ := norm_nonneg _
  have hcos0 : 0 ≤ ‖Complex.cos (Real.pi * (1 - z) / 2)‖ := norm_nonneg _
  calc
    2 * ‖((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - z))‖ * ‖Complex.Gamma (1 - z)‖ *
        ‖Complex.cos (Real.pi * (1 - z) / 2)‖ ≤
      2 * 1 * (C * |z.im| ^ n * Real.exp (-(Real.pi * |z.im| / 2))) *
        Real.exp (Real.pi * |z.im| / 2) := by
          gcongr
    _ = 2 * C * |z.im| ^ n *
        (Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im| / 2)) := by ring
    _ = 2 * C * |z.im| ^ n := by rw [hexp, mul_one]

/-- Uniform budget for the principal finite Euler correction on the
displacement strip. -/
def cglLemma62PrincipalCorrectionStripBudget (Q : CGLPositiveModulus) : ℝ :=
  ∏ p ∈ Q.value.primeFactors, (4 * (1 + (p : ℝ)))

theorem cglLemma62PrincipalCorrectionStripBudget_nonneg (Q : CGLPositiveModulus) :
    0 ≤ cglLemma62PrincipalCorrectionStripBudget Q := by
  unfold cglLemma62PrincipalCorrectionStripBudget
  exact Finset.prod_nonneg fun p _ => by positivity

theorem cglLemma62_principal_leftFactor_norm_le
    (Q : CGLPositiveModulus) {z : ℂ} (hz : -1 ≤ z.re) :
    ‖cglLemma62PrincipalEulerLeftFactorAt Q z‖ ≤
      ∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ)) := by
  unfold cglLemma62PrincipalEulerLeftFactorAt
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) ?_
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  have hpow : ‖(p : ℂ) ^ (-z)‖ ≤ (p : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos hpprime.pos]
    have hre : (-z).re = -z.re := by simp
    rw [hre]
    calc
      (p : ℝ) ^ (-z.re) ≤ (p : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpone (by linarith)
      _ = p := Real.rpow_one _
  calc
    ‖1 - (p : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) := by rw [norm_one]; linarith

theorem cglLemma62_principal_rightFactor_factor_ge
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z.re ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ ‖1 - (p : ℂ) ^ (-(1 - z))‖ := by
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hptwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpow : ‖(p : ℂ) ^ (-(1 - z))‖ ≤ 3 / 4 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    have hre : (-(1 - z)).re = -(1 - z.re) := by simp
    rw [hre]
    set a : ℝ := (p : ℝ) ^ (-(1 - z.re)) with ha
    have ha0 : 0 ≤ a := by positivity
    have hsq : a ^ 2 ≤ 1 / 2 := by
      have hsq' : a ^ 2 = (p : ℝ) ^ (-(1 - z.re) * 2) := by
        rw [ha, Real.rpow_mul (by positivity)]
        norm_cast
      rw [hsq']
      calc
        (p : ℝ) ^ (-(1 - z.re) * 2) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hpone (by linarith)
        _ = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
        _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) hptwo
    nlinarith
  calc
    (1 / 4 : ℝ) ≤ ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-(1 - z))‖ := by
      rw [norm_one]; linarith
    _ ≤ ‖1 - (p : ℂ) ^ (-(1 - z))‖ := norm_sub_norm_le _ _

theorem cglLemma62_principal_rightFactor_norm_ge
    (Q : CGLPositiveModulus) {z : ℂ} (hz : z.re ≤ 1 / 2) :
    (1 / 4 : ℝ) ^ Q.value.primeFactors.card ≤
      ‖cglLemma62PrincipalEulerRightFactorAt Q z‖ := by
  unfold cglLemma62PrincipalEulerRightFactorAt
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by norm_num) ?_
  intro p hp
  exact cglLemma62_principal_rightFactor_factor_ge (Nat.prime_of_mem_primeFactors hp) hz

/-- The principal finite Euler correction is uniformly bounded on the
displacement strip. -/
theorem norm_cglLemma62PrincipalEulerCorrectionAt_le_strip
    (Q : CGLPositiveModulus) {z : ℂ} (hlo : -1 ≤ z.re) (hhi : z.re ≤ 1 / 2) :
    ‖cglLemma62PrincipalEulerCorrectionAt Q z‖ ≤
      cglLemma62PrincipalCorrectionStripBudget Q := by
  have hleft := cglLemma62_principal_leftFactor_norm_le Q hlo
  have hright := cglLemma62_principal_rightFactor_norm_ge Q hhi
  have hq : (0 : ℝ) < (1 / 4 : ℝ) ^ Q.value.primeFactors.card := by positivity
  have hbudget : cglLemma62PrincipalCorrectionStripBudget Q =
      (∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ))) / (1 / 4 : ℝ) ^ Q.value.primeFactors.card := by
    unfold cglLemma62PrincipalCorrectionStripBudget
    rw [Finset.prod_mul_distrib, Finset.prod_const, eq_div_iff (ne_of_gt hq)]
    have h4 : (4 : ℝ) ^ Q.value.primeFactors.card * (1 / 4 : ℝ) ^ Q.value.primeFactors.card = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      (4 : ℝ) ^ Q.value.primeFactors.card * (∏ x ∈ Q.value.primeFactors, (1 + (x : ℝ))) *
          (1 / 4 : ℝ) ^ Q.value.primeFactors.card =
        (∏ x ∈ Q.value.primeFactors, (1 + (x : ℝ))) *
          ((4 : ℝ) ^ Q.value.primeFactors.card * (1 / 4 : ℝ) ^ Q.value.primeFactors.card) := by ring
      _ = _ := by rw [h4, mul_one]
  unfold cglLemma62PrincipalEulerCorrectionAt
  rw [norm_div, hbudget]
  have hrpos : 0 < ‖cglLemma62PrincipalEulerRightFactorAt Q z‖ := lt_of_lt_of_le hq hright
  rw [div_le_div_iff₀ hrpos hq]
  calc
    ‖cglLemma62PrincipalEulerLeftFactorAt Q z‖ * (1 / 4 : ℝ) ^ Q.value.primeFactors.card ≤
        (∏ p ∈ Q.value.primeFactors, (1 + (p : ℝ))) * ‖cglLemma62PrincipalEulerRightFactorAt Q z‖ :=
      mul_le_mul hleft hright hq.le (Finset.prod_nonneg fun p _ => by positivity)

/-- Nonnegativity of the uniform all-order Mellin budget on the first strip. -/
theorem cglLemma62MellinFirstShiftUniformBudget_nonneg (w : CGLRealSmoothBump) (n : ℕ) :
    0 ≤ cglLemma62MellinFirstShiftUniformBudget w n := by
  dsimp [cglLemma62MellinFirstShiftUniformBudget]
  apply integral_nonneg
  intro u
  unfold deningerMeyerUniformStripMajorant
  positivity

/-- Quadratic decay of the regularized principal finite carrier on horizontal
segments of the displacement strip, above unit height and unit displaced
height. -/
theorem cglLemma62_exists_principalRegularizedFinite_strip_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (t : ℝ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, -1 ≤ x → x ≤ 1 / 2 → 1 ≤ |y| → 1 ≤ |y - t| →
      ‖cglLemma62PrincipalRegularizedFiniteContourIntegrand w N Q t M
        ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / |y| ^ 2 := by
  obtain ⟨Cχ, n, hCχ, hχ⟩ := cglLemma62_exists_bound_principalRegularizedFactor_strip
  have hB := cglLemma62MellinFirstShiftUniformBudget_nonneg w (n + 2)
  have hE := cglLemma62PrincipalCorrectionStripBudget_nonneg Q
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hNone : 1 ≤ (N.value : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive))
  refine ⟨cglLemma62MellinFirstShiftUniformBudget w (n + 2) * (N.value : ℝ) ^ (1 / 2 : ℝ) *
    (Cχ * (1 + |t|) ^ n) * cglLemma62PrincipalCorrectionStripBudget Q * (M + 1),
    by positivity, ?_⟩
  intro x y hxlo hxhi hy hyt
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
  let sigma : CGLLemma62FirstShiftAbscissa := ⟨x, hxlo, by linarith⟩
  have hkernel0 := cglLemma62_mellinTransform_firstShift_uniformAllOrderDecay w (n + 2) sigma y
  have hkernel : ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2) := by
    apply (le_div_iff₀ (pow_pos hypos (n + 2))).mpr
    simpa [sigma, mul_comm] using hkernel0
  have hNpow : ‖(N.value : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ ≤ (N.value : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos N.positive]
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_exponent_le hNone hxhi
  have hshift : ((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I = (x : ℂ) + ((y - t : ℝ) : ℂ) * I := by
    push_cast; ring
  have hχz : ‖cglLemma62PrincipalRegularizedFunctionalFactor
      (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ n * |y| ^ n := by
    rw [hshift]
    have h := hχ ((x : ℂ) + ((y - t : ℝ) : ℂ) * I) (by simpa using hxlo) (by simpa using hxhi)
      (by simpa using hyt)
    have him : (((x : ℂ) + ((y - t : ℝ) : ℂ) * I)).im = y - t := by simp
    rw [him] at h
    refine h.trans ?_
    have hyt' : |y - t| ≤ (1 + |t|) * |y| := by
      calc
        |y - t| ≤ |y| + |t| := abs_sub _ _
        _ ≤ |y| + |t| * |y| := by nlinarith [abs_nonneg t]
        _ = (1 + |t|) * |y| := by ring
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hyt' n
    rw [mul_pow] at hpow
    calc
      Cχ * |y - t| ^ n ≤ Cχ * ((1 + |t|) ^ n * |y| ^ n) :=
        mul_le_mul_of_nonneg_left hpow hCχ
      _ = _ := by ring
  have hEz : ‖cglLemma62PrincipalEulerCorrectionAt Q (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤
      cglLemma62PrincipalCorrectionStripBudget Q := by
    rw [hshift]
    exact norm_cglLemma62PrincipalEulerCorrectionAt_le_strip Q (by simpa using hxlo)
      (by simpa using hxhi)
  have hD : ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
      (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I)‖ ≤ M + 1 := by
    apply norm_cglLemma62DirichletHead_le
    simp
    linarith
  unfold cglLemma62PrincipalRegularizedFiniteContourIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ *
        ‖(N.value : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ *
        ‖cglLemma62PrincipalRegularizedFunctionalFactor (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ *
        ‖cglLemma62PrincipalEulerCorrectionAt Q (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ *
        ‖cglLemma62DirichletHead (1 : DirichletCharacter ℂ Q.value) M
          (1 - ((x : ℂ) + (y : ℂ) * I) + (t : ℂ) * I)‖ ≤
      (cglLemma62MellinFirstShiftUniformBudget w (n + 2) / |y| ^ (n + 2)) *
        (N.value : ℝ) ^ (1 / 2 : ℝ) * (Cχ * (1 + |t|) ^ n * |y| ^ n) *
        cglLemma62PrincipalCorrectionStripBudget Q * (M + 1) := by
          gcongr
    _ = cglLemma62MellinFirstShiftUniformBudget w (n + 2) * (N.value : ℝ) ^ (1 / 2 : ℝ) *
        (Cχ * (1 + |t|) ^ n) * cglLemma62PrincipalCorrectionStripBudget Q * (M + 1) /
        |y| ^ 2 := by
          field_simp
          have hp : |y| ^ n * |y| ^ 2 = |y| ^ (n + 2) := (pow_add |y| n 2).symm
          rw [← hp]
          ring

end

end RHTower
