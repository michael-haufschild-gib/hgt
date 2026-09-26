import GaloisForLFunctions.RHTower.ThetaPowerCoefficientMass
import GaloisForLFunctions.RHTower.ThetaPowerChiEightLFunction
import GaloisForLFunctions.RHTower.ThetaPowerZerosOffCriticalStrip

/-!
# The Dirichlet split of the theta-power family

`M(z) = ∫₀^∞ F_a(iy) y^{z-1} dy` is entire (it is `4 Λ_a(i(2z - 1/2))`), and `D(z) = π^z M(z)/Γ(z)` is
entire.  For `δ > 0` and `Re z > 0` the shifted transform `M_δ(z) = ∫₀^∞ F_a(i(y+δ)) y^{z-1} dy` is computed
termwise from `F_a(i(y+δ)) = Σ b_n e^{-π(n+α)(y+δ)}`:

  `M_δ(z) = Γ(z) π^{-z} D^δ(z)`,   `D^δ(z) = Σ b_n e^{-π(n+α)δ} (n+α)^{-z}`,

an everywhere absolutely convergent series.  Hence `D = D^δ + E^δ` on `Re z > 0` with
`E^δ = π^z (M - M_δ)/Γ`, and a zero of `D` with `Re z ≠ 1/4` is an off-line zero of `Λ_a`.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open Bottcher

variable {a : ℝ}

/-- `M(z) = ∫₀^∞ F_a(iy) y^{z-1} dy`. -/
def thetaPowerMellin (a : ℝ) (z : ℂ) : ℂ := mellin (fun y : ℝ => thetaPowerForm a (I * (y : ℂ))) z

/-- `M_δ(z) = ∫₀^∞ F_a(i(y+δ)) y^{z-1} dy`. -/
def thetaPowerShiftMellin (a δ : ℝ) (z : ℂ) : ℂ :=
  mellin (fun y : ℝ => thetaPowerForm a (I * ((y + δ : ℝ) : ℂ))) z

/-- `D(z) = π^z M(z) / Γ(z)`. -/
def thetaPowerDirichlet (a : ℝ) (z : ℂ) : ℂ := (π : ℂ) ^ z * thetaPowerMellin a z / Complex.Gamma z

/-- The frequencies `λ_n = π(n + a/4)`. -/
def thetaPowerFreq (a : ℝ) (n : ℕ) : ℝ := π * ((n : ℝ) + a / 4)

/-- `D^δ(z) = Σ b_n e^{-π(n+α)δ} (n+α)^{-z}`. -/
def thetaPowerSmoothDirichlet (a δ : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, thetaPowerCoeff a n * ((Real.exp (-(thetaPowerFreq a n * δ)) : ℝ) : ℂ) *
    (((n : ℝ) + a / 4 : ℝ) : ℂ) ^ (-z)

/-- `E^δ(z) = π^z (M(z) - M_δ(z)) / Γ(z)`. -/
def thetaPowerDirichletError (a δ : ℝ) (z : ℂ) : ℂ :=
  (π : ℂ) ^ z * (thetaPowerMellin a z - thetaPowerShiftMellin a δ z) / Complex.Gamma z

theorem thetaPowerFreq_pos (ha : 0 < a) (n : ℕ) : 0 < thetaPowerFreq a n := by
  unfold thetaPowerFreq; positivity

theorem thetaPowerMellin_eq (a : ℝ) (z : ℂ) :
    thetaPowerMellin a z = 4 * thetaPowerXiC a (I * (2 * z - 1 / 2)) := by
  rw [thetaPowerXiC_eq_mellin]
  unfold thetaPowerMellin
  have : (1 / 2 - I * (I * (2 * z - 1 / 2))) / 2 = z := by ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem differentiable_thetaPowerMellin (ha : 0 < a) : Differentiable ℂ (thetaPowerMellin a) := by
  intro z
  rw [show thetaPowerMellin a = fun z => 4 * thetaPowerXiC a (I * (2 * z - 1 / 2)) from
    funext (thetaPowerMellin_eq a)]
  exact ((differentiable_thetaPowerXiC ha).comp (by fun_prop : Differentiable ℂ
    fun z : ℂ => I * (2 * z - 1 / 2)) z).const_mul 4

/-- **`D` is entire.** -/
theorem differentiable_thetaPowerDirichlet (ha : 0 < a) : Differentiable ℂ (thetaPowerDirichlet a) := by
  intro z
  unfold thetaPowerDirichlet
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ z) z :=
    (differentiableAt_id.const_cpow (Or.inl hπ))
  have h2 := (h1.mul (differentiable_thetaPowerMellin ha z)).mul
    (Complex.differentiable_one_div_Gamma z)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [div_eq_mul_inv]

/-- **Off-line zeros of `D` are off-line zeros of `Λ_a`.** -/
theorem thetaPowerXiC_eq_zero_of_dirichlet {z : ℂ} (hz : 0 < z.re) (hD : thetaPowerDirichlet a z = 0) :
    thetaPowerXiC a (I * (2 * z - 1 / 2)) = 0 := by
  unfold thetaPowerDirichlet at hD
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hπ : (π : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero] <;> [exact_mod_cast Real.pi_ne_zero; exact
      fun h => by rw [h] at hz; simp at hz]
  rw [div_eq_zero_iff] at hD
  rcases hD with hD | hD
  · rcases mul_eq_zero.mp hD with h | h
    · exact absurd h hπ
    · rw [thetaPowerMellin_eq] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · exact absurd hD hG

theorem im_I_mul_two_mul_sub (z : ℂ) : (I * (2 * z - 1 / 2)).im = 2 * z.re - 1 / 2 := by simp

/-- The Fourier expansion on the shifted axis. -/
theorem thetaPowerForm_shift_axis (ha : 0 ≤ a) {y δ : ℝ} (hyδ : 0 < y + δ) :
    HasSum (fun n : ℕ => thetaPowerCoeff a n * ((Real.exp (-(thetaPowerFreq a n * (y + δ))) : ℝ) : ℂ))
      (thetaPowerForm a (I * ((y + δ : ℝ) : ℂ))) := by
  have hτ : 0 < (I * ((y + δ : ℝ) : ℂ)).im := by simpa using hyδ
  refine (hasSum_thetaPowerForm ha hτ).congr_fun (fun n => ?_)
  congr 1
  rw [Complex.ofReal_exp]; congr 1
  unfold thetaPowerFreq
  push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- **Termwise Mellin transform.** `M_δ(z) = Γ(z) π^{-z} D^δ(z)` for `Re z > 0`. -/
theorem thetaPowerShiftMellin_eq (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.re) :
    thetaPowerShiftMellin a δ z =
      Complex.Gamma z * (π : ℂ) ^ (-z) * thetaPowerSmoothDirichlet a δ z := by
  set lam := thetaPowerFreq a with hlam
  have hlpos : ∀ n, 0 < lam n := thetaPowerFreq_pos ha
  set term : ℕ → ℝ → ℂ := fun n y => (y : ℂ) ^ (z - 1) *
    (thetaPowerCoeff a n * ((Real.exp (-(lam n * (y + δ))) : ℝ) : ℂ)) with hterm
  -- the integrand as a series
  have hint_eq : ∀ y ∈ Ioi (0 : ℝ), (y : ℂ) ^ (z - 1) • thetaPowerForm a (I * ((y + δ : ℝ) : ℂ)) =
      ∑' n, term n y := by
    intro y hy
    have hyδ : 0 < y + δ := by have : (0 : ℝ) < y := hy; linarith
    rw [(thetaPowerForm_shift_axis ha.le hyδ).tsum_eq.symm, smul_eq_mul, ← tsum_mul_left]
  -- norms of the terms
  have hnorm : ∀ n, ∀ y ∈ Ioi (0 : ℝ), ‖term n y‖ = ‖thetaPowerCoeff a n‖ *
      Real.exp (-(lam n * δ)) * (y ^ (z.re - 1) * Real.exp (-(lam n * y))) := by
    intro n y hy
    have hy0 : (0 : ℝ) < y := hy
    simp only [hterm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    simp only [Complex.sub_re, Complex.one_re]
    rw [show -(lam n * (y + δ)) = -(lam n * δ) + -(lam n * y) by ring, Real.exp_add]; ring
  have hinteg : ∀ n, Integrable (term n) (volume.restrict (Ioi 0)) := by
    intro n
    have hdom : IntegrableOn (fun y : ℝ => ‖thetaPowerCoeff a n‖ * Real.exp (-(lam n * δ)) *
        (y ^ (z.re - 1) * Real.exp (-(lam n * y)))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := z.re - 1) (b := lam n)
        (by linarith) le_rfl (hlpos n)
      refine IntegrableOn.congr_fun (Integrable.const_mul h (‖thetaPowerCoeff a n‖ *
        Real.exp (-(lam n * δ)))) (fun y _ => ?_) measurableSet_Ioi
      simp only [Real.rpow_one, neg_mul]
    have hcont : ContinuousOn (term n) (Ioi 0) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      refine ContinuousAt.continuousWithinAt ?_
      simp only [hterm]
      refine ContinuousAt.mul ?_ (by fun_prop)
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))
    refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun y hy => (hnorm n y hy).le
  have hintnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖term n y‖ =
      ‖thetaPowerCoeff a n‖ * Real.exp (-(lam n * δ)) * ((1 / lam n) ^ z.re * Real.Gamma z.re) := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (hnorm n), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hz (hlpos n)]
  have hsumm : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖term n y‖ := by
    simp_rw [hintnorm]
    have hr1 : Real.exp (-(π * δ)) < 1 := by
      rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
    have hs := summable_norm_thetaPowerCoeff_mul_pow ha.le (Real.exp_pos _).le hr1
    set K : ℝ := Real.exp (-(π * (a / 4) * δ)) * ((1 / (π * (a / 4))) ^ z.re * Real.Gamma z.re)
    have hG0 : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.exp_pos _).le) (mul_nonneg (Real.rpow_nonneg (by have := hlpos n; positivity) _) hG0))
      (fun n => ?_) (hs.mul_right K)
    have hexp : Real.exp (-(lam n * δ)) = Real.exp (-(π * δ)) ^ n * Real.exp (-(π * (a / 4) * δ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; simp only [hlam, thetaPowerFreq]; ring
    have hpow : (1 / lam n) ^ z.re ≤ (1 / (π * (a / 4))) ^ z.re := by
      apply Real.rpow_le_rpow (by have := hlpos n; positivity) _ hz.le
      apply one_div_le_one_div_of_le (by positivity)
      simp only [hlam, thetaPowerFreq]
      have := Real.pi_pos; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    rw [hexp]
    have hG : 0 ≤ Real.Gamma z.re := (Real.Gamma_pos_of_pos hz).le
    calc ‖thetaPowerCoeff a n‖ * (Real.exp (-(π * δ)) ^ n * Real.exp (-(π * (a / 4) * δ))) *
          ((1 / lam n) ^ z.re * Real.Gamma z.re)
        ≤ ‖thetaPowerCoeff a n‖ * (Real.exp (-(π * δ)) ^ n * Real.exp (-(π * (a / 4) * δ))) *
          ((1 / (π * (a / 4))) ^ z.re * Real.Gamma z.re) := by gcongr
      _ = ‖thetaPowerCoeff a n‖ * Real.exp (-(π * δ)) ^ n * K := by ring
  -- swap sum and integral
  unfold thetaPowerShiftMellin mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hint_eq]
  rw [← integral_tsum_of_summable_integral_norm hinteg hsumm]
  -- each term
  have hterm_int : ∀ n, ∫ y in Ioi (0 : ℝ), term n y =
      Complex.Gamma z * (π : ℂ) ^ (-z) * (thetaPowerCoeff a n *
        ((Real.exp (-(thetaPowerFreq a n * δ)) : ℝ) : ℂ) * (((n : ℝ) + a / 4 : ℝ) : ℂ) ^ (-z)) := by
    intro n
    have hsplit : ∀ y : ℝ, term n y = (thetaPowerCoeff a n * ((Real.exp (-(lam n * δ)) : ℝ) : ℂ)) *
        ((y : ℂ) ^ (z - 1) * Complex.exp (-((lam n : ℂ) * y))) := by
      intro y
      simp only [hterm]
      rw [show -(lam n * (y + δ)) = -(lam n * δ) + -(lam n * y) by ring, Real.exp_add,
        Complex.ofReal_mul, Complex.ofReal_exp (-(lam n * y))]
      push_cast; ring
    simp_rw [hsplit]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hz (hlpos n)]
    have hl : (1 / (lam n : ℂ)) ^ z = (π : ℂ) ^ (-z) * (((n : ℝ) + a / 4 : ℝ) : ℂ) ^ (-z) := by
      have hlam' : (lam n : ℂ) = (π : ℂ) * (((n : ℝ) + a / 4 : ℝ) : ℂ) := by
        simp only [hlam, thetaPowerFreq]; push_cast; ring
      have hn0 : (0 : ℝ) ≤ (n : ℝ) + a / 4 := by positivity
      rw [one_div, hlam', Complex.inv_cpow _ _ (by
        rw [← Complex.ofReal_mul, Complex.arg_ofReal_of_nonneg (by positivity)]
        exact Real.pi_ne_zero.symm), Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hn0,
        Complex.cpow_neg, Complex.cpow_neg, mul_inv]
    rw [hl]; ring
  simp_rw [hterm_int]
  rw [tsum_mul_left]
  rfl

/-- **The Dirichlet split** `D = D^δ + E^δ` on `Re z > 0`. -/
theorem thetaPowerDirichlet_split (ha : 0 < a) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : 0 < z.re) :
    thetaPowerDirichlet a z = thetaPowerSmoothDirichlet a δ z + thetaPowerDirichletError a δ z := by
  unfold thetaPowerDirichlet thetaPowerDirichletError
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hπ : (π : ℂ) ^ z * (π : ℂ) ^ (-z) = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero), add_neg_cancel, Complex.cpow_zero]
  rw [thetaPowerShiftMellin_eq ha hδ hz]
  field_simp
  linear_combination (Complex.Gamma z * thetaPowerSmoothDirichlet a δ z) * hπ

end

end RHTower
