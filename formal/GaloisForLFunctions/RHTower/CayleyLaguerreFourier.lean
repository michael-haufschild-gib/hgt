import GaloisForLFunctions.HTGeometry.CauchyKernelFourier
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

open MeasureTheory Set Complex
open scoped FourierTransform RealInnerProductSpace

namespace RHTower

noncomputable section

/-- Continuous one-sided Gamma density of shape `j+2`. -/
def routeUGammaDatum (j : ℕ) (t : ℝ) : ℂ :=
  (((max t 0 : ℝ) : ℂ) ^ (j + 1) *
      Complex.exp (-((max t 0 : ℝ) : ℂ)) / ((j + 1).factorial : ℂ))

theorem continuous_routeUGammaDatum (j : ℕ) :
    Continuous (routeUGammaDatum j) := by
  unfold routeUGammaDatum
  fun_prop

theorem routeUGammaDatum_eq_indicator (j : ℕ) (t : ℝ) :
    routeUGammaDatum j t = Set.indicator (Set.Ioi (0 : ℝ))
      (fun s : ℝ => ((s : ℂ) ^ (j + 1) * Complex.exp (-(s : ℂ)) /
        ((j + 1).factorial : ℂ))) t := by
  rcases lt_or_ge 0 t with ht | ht
  · have htmem : t ∈ Set.Ioi (0 : ℝ) := ht
    rw [routeUGammaDatum, Set.indicator_of_mem htmem, max_eq_left ht.le]
  · have htmem : t ∉ Set.Ioi (0 : ℝ) := by simpa using ht
    rw [routeUGammaDatum, Set.indicator_of_notMem htmem,
      max_eq_right ht]
    simp

theorem integrable_routeUGammaDatum (j : ℕ) :
    Integrable (routeUGammaDatum j) := by
  have hraw := GaloisForLFunctions.HTGeometry.integrableOn_natPow_mul_cexp
    (c := (1 : ℂ)) (by norm_num) (j + 1)
  have hdiv : IntegrableOn (fun s : ℝ =>
      (s : ℂ) ^ (j + 1) * Complex.exp (-((1 : ℂ) * s)) /
        ((j + 1).factorial : ℂ)) (Set.Ioi (0 : ℝ)) :=
    hraw.div_const _
  have hind : Integrable (Set.indicator (Set.Ioi (0 : ℝ))
      (fun s : ℝ => (s : ℂ) ^ (j + 1) * Complex.exp (-(s : ℂ)) /
        ((j + 1).factorial : ℂ))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact hdiv.congr_fun (fun s _ => by
      ring) measurableSet_Ioi
  exact hind.congr (Filter.Eventually.of_forall fun t =>
    (routeUGammaDatum_eq_indicator j t).symm)

theorem fourier_routeUGammaDatum (j : ℕ) (w : ℝ) :
    𝓕 (routeUGammaDatum j) w =
      ((1 : ℂ) + 2 * (Real.pi : ℂ) * I * (w : ℂ))⁻¹ ^ (j + 2) := by
  let c : ℂ := 1 + 2 * (Real.pi : ℂ) * I * (w : ℂ)
  have hc : 0 < c.re := by
    dsimp only [c]
    simp [Complex.mul_re]
  rw [Real.fourier_eq']
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  have hpt : ∀ t : ℝ,
      Complex.exp (((-2 * Real.pi * (w * t) : ℝ) : ℂ) * I) *
          routeUGammaDatum j t =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun t : ℝ => (t : ℂ) ^ (j + 1) *
            Complex.exp (-(c * (t : ℂ))) / ((j + 1).factorial : ℂ)) t := by
    intro t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [routeUGammaDatum_eq_indicator, Set.indicator_of_mem ht,
        Set.indicator_of_mem ht]
      rw [show Complex.exp (((-2 * Real.pi * (w * t) : ℝ) : ℂ) * I) *
            ((t : ℂ) ^ (j + 1) * Complex.exp (-(t : ℂ)) /
              ((j + 1).factorial : ℂ)) =
          (t : ℂ) ^ (j + 1) *
            (Complex.exp (((-2 * Real.pi * (w * t) : ℝ) : ℂ) * I) *
              Complex.exp (-(t : ℂ))) / ((j + 1).factorial : ℂ) by ring]
      rw [← Complex.exp_add]
      congr 2
      dsimp only [c]
      push_cast
      ring
    · rw [routeUGammaDatum_eq_indicator, Set.indicator_of_notMem ht,
        Set.indicator_of_notMem ht, mul_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    MeasureTheory.integral_div]
  rw [GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp hc (j + 1)]
  have hfac : (((j + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (j + 1)
  have hcne : c ≠ 0 := by
    intro hzero
    rw [hzero] at hc
    simp at hc
  dsimp only [c]
  field_simp [hfac, hcne]
  simp only [one_div]
  rw [inv_pow]

theorem integrable_fourier_routeUGammaDatum (j : ℕ) :
    Integrable (𝓕 (routeUGammaDatum j)) := by
  have hbase : Integrable (fun w : ℝ =>
      (1 + (2 * Real.pi * w) ^ 2)⁻¹) := by
    have h := (GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq
      (by norm_num : (0 : ℝ) < 1)).comp_mul_left'
        (R := 2 * Real.pi) (by positivity)
    simpa only [one_pow] using h
  refine Integrable.mono' hbase ?_ ?_
  · have heq : 𝓕 (routeUGammaDatum j) = fun w : ℝ =>
        ((1 : ℂ) + 2 * (Real.pi : ℂ) * I * (w : ℂ))⁻¹ ^ (j + 2) := by
      funext w
      exact fourier_routeUGammaDatum j w
    rw [heq]
    fun_prop
  · filter_upwards with w
    rw [fourier_routeUGammaDatum, norm_pow]
    let c : ℂ := 1 + 2 * (Real.pi : ℂ) * I * (w : ℂ)
    have hsq : ‖c‖ ^ 2 = 1 + (2 * Real.pi * w) ^ 2 := by
      have hcre : c.re = 1 := by
        dsimp only [c]
        simp [Complex.mul_re]
      have hcim : c.im = 2 * Real.pi * w := by
        dsimp only [c]
        simp [Complex.mul_im]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, hcre, hcim]
      ring
    have hcnorm : 1 ≤ ‖c‖ := by
      nlinarith [norm_nonneg c, sq_nonneg (2 * Real.pi * w)]
    have hu : ‖c⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (by positivity)).2 hcnorm
    have hpow : ‖c⁻¹‖ ^ (j + 2) ≤ ‖c⁻¹‖ ^ 2 :=
      pow_le_pow_of_le_one (norm_nonneg _) hu (by omega)
    have htwo : ‖c⁻¹‖ ^ 2 = (1 + (2 * Real.pi * w) ^ 2)⁻¹ := by
      rw [norm_inv, inv_pow, hsq]
    change ‖c⁻¹‖ ^ (j + 2) ≤ (1 + (2 * Real.pi * w) ^ 2)⁻¹
    exact hpow.trans_eq htwo

theorem fourierInv_fourier_routeUGammaDatum (j : ℕ) (t : ℝ) :
    𝓕⁻ (𝓕 (routeUGammaDatum j)) t = routeUGammaDatum j t :=
  (integrable_routeUGammaDatum j).fourierInv_fourier_eq
    (integrable_fourier_routeUGammaDatum j)
    (continuous_routeUGammaDatum j).continuousAt

/-- Pole power whose no-`2π` transform is a one-sided Gamma density. -/
def routeUCayleyPolePower (j : ℕ) (x : ℝ) : ℂ :=
  ((1 : ℂ) - I * (x : ℂ))⁻¹ ^ (j + 2)

theorem routeUCayleyPolePower_eq_scaledFourier (j : ℕ) (x : ℝ) :
    routeUCayleyPolePower j x =
      𝓕 (routeUGammaDatum j) (-x / (2 * Real.pi)) := by
  rw [fourier_routeUGammaDatum, routeUCayleyPolePower]
  congr 2
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt Real.pi_pos
  field_simp [hpi]
  ring

theorem integrable_routeUCayleyPolePower (j : ℕ) :
    Integrable (routeUCayleyPolePower j) := by
  let c : ℝ := -(1 / (2 * Real.pi))
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact neg_ne_zero.mpr (one_div_ne_zero
      (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)))
  have hscaled : Integrable (fun x : ℝ =>
      𝓕 (routeUGammaDatum j) (c * x)) :=
    (integrable_fourier_routeUGammaDatum j).comp_mul_left' hc
  refine hscaled.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [routeUCayleyPolePower_eq_scaledFourier]
  dsimp only [c]
  field_simp [ne_of_gt Real.pi_pos]

/-- Fourier integral in Route U's convention `exp(-i ξ x)`. -/
def routeUFourierIntegral (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))

theorem routeUFourierIntegral_cayleyPolePower (j : ℕ) (ξ : ℝ) :
    routeUFourierIntegral (routeUCayleyPolePower j) ξ =
      (2 * (Real.pi : ℂ)) * routeUGammaDatum j ξ := by
  have hinv := fourierInv_fourier_routeUGammaDatum j ξ
  rw [Real.fourierInv_eq'] at hinv
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul] at hinv
  let G : ℝ → ℂ := fun w =>
    Complex.exp (((2 * Real.pi * (ξ * w) : ℝ) : ℂ) * I) *
      𝓕 (routeUGammaDatum j) w
  have hscale := MeasureTheory.Measure.integral_comp_div G (-2 * Real.pi)
  have habs : |(-2 * Real.pi : ℝ)| = 2 * Real.pi := by
    have hneg : (-2 : ℝ) * Real.pi < 0 := by nlinarith [Real.pi_pos]
    rw [abs_of_neg hneg]
    ring
  rw [habs, hinv, Complex.real_smul] at hscale
  rw [routeUFourierIntegral]
  calc
    (∫ x : ℝ, routeUCayleyPolePower j x *
        Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      ∫ x : ℝ, G (x / (-2 * Real.pi)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [routeUCayleyPolePower_eq_scaledFourier]
        dsimp only [G]
        have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
        have hw : -x / (2 * Real.pi) = x / (-2 * Real.pi) := by
          field_simp [hpi]
        have hexp :
            Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) =
              Complex.exp (((2 * Real.pi * (ξ * (x / (-2 * Real.pi))) : ℝ) : ℂ) * I) := by
          congr 1
          push_cast
          field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast hpi]
        rw [hw, hexp, mul_comm]
    _ = (2 * (Real.pi : ℂ)) * routeUGammaDatum j ξ := by
      simpa using hscale

theorem routeUFourierIntegral_cayleyPolePower_pos
    (j : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (routeUCayleyPolePower j) ξ =
      (2 * (Real.pi : ℂ)) *
        (((ξ ^ (j + 1) * Real.exp (-ξ) /
          (j + 1).factorial : ℝ) : ℂ)) := by
  rw [routeUFourierIntegral_cayleyPolePower, routeUGammaDatum,
    max_eq_left hξ.le]
  rw [show -((ξ : ℝ) : ℂ) = (((-ξ : ℝ) : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_exp]
  push_cast
  ring

theorem routeUFourierIntegral_cayleyPolePower_neg
    (j : ℕ) {ξ : ℝ} (hξ : ξ < 0) :
    routeUFourierIntegral (routeUCayleyPolePower j) ξ = 0 := by
  rw [routeUFourierIntegral_cayleyPolePower, routeUGammaDatum,
    max_eq_right hξ.le]
  simp

/-! ## Finite Cayley-mode expansion -/

def routeUCayleyModeKernel (m : ℕ) (x : ℝ) : ℂ :=
  ((((1 : ℂ) + I * (x : ℂ)) / ((1 : ℂ) - I * (x : ℂ))) ^ m) /
    ((1 : ℂ) + (x : ℂ) ^ 2)

def routeUCayleyPoleCoefficient (m k : ℕ) : ℂ :=
  (-1 : ℂ) ^ (k + (m - 1)) * (2 : ℂ) ^ k *
    (Nat.choose (m - 1) k : ℂ)

theorem routeUCayleyModeKernel_eq_sum_poles
    {m : ℕ} (hm : 0 < m) (x : ℝ) :
    routeUCayleyModeKernel m x =
      ∑ k ∈ Finset.range m,
        routeUCayleyPoleCoefficient m k * routeUCayleyPolePower k x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let u : ℂ := 1 - I * (x : ℂ)
  let v : ℂ := 1 + I * (x : ℂ)
  have hu : u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [u] at hre
    norm_num [Complex.mul_re] at hre
  have hv : v ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [v] at hre
    norm_num [Complex.mul_re] at hre
  have hden : (1 : ℂ) + (x : ℂ) ^ 2 = v * u := by
    symm
    calc
      v * u = 1 - (I * (x : ℂ)) ^ 2 := by
        dsimp only [u, v]
        ring
      _ = (1 : ℂ) + (x : ℂ) ^ 2 := by
        rw [mul_pow, Complex.I_sq]
        ring
  have hmode : routeUCayleyModeKernel (n + 1) x =
      v ^ n * u⁻¹ ^ (n + 2) := by
    rw [routeUCayleyModeKernel, hden]
    change (v / u) ^ (n + 1) / (v * u) = _
    rw [div_pow]
    field_simp [hu, hv]
    simp only [pow_succ]
    have hunit : u ^ 2 * u ^ n * u⁻¹ ^ 2 * u⁻¹ ^ n = 1 := by
      calc
        _ = (u ^ 2 * u⁻¹ ^ 2) * (u ^ n * u⁻¹ ^ n) := by ring
        _ = (u * u⁻¹) ^ 2 * (u * u⁻¹) ^ n := by
          rw [mul_pow, mul_pow]
        _ = 1 := by simp [hu]
    calc
      v ^ n * v = v ^ n * v *
          (u ^ 2 * u ^ n * u⁻¹ ^ 2 * u⁻¹ ^ n) := by rw [hunit]; ring
      _ = _ := by ring
  rw [hmode]
  have hv_sub : v = 2 - u := by
    dsimp only [u, v]
    ring
  rw [hv_sub, sub_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hpow : u ^ (n - k) * u⁻¹ ^ (n + 2) = u⁻¹ ^ (k + 2) := by
    rw [inv_pow, inv_pow]
    field_simp [hu]
    rw [← pow_add]
    congr 1
    omega
  rw [routeUCayleyPoleCoefficient, routeUCayleyPolePower]
  simp only [Nat.succ_sub_one]
  change
    (-1 : ℂ) ^ (k + n) * 2 ^ k * u ^ (n - k) *
        (Nat.choose n k : ℂ) * u⁻¹ ^ (n + 2) =
      (-1 : ℂ) ^ (k + n) * 2 ^ k * (Nat.choose n k : ℂ) *
        u⁻¹ ^ (k + 2)
  calc
    _ = ((-1 : ℂ) ^ (k + n) * 2 ^ k * (Nat.choose n k : ℂ)) *
          (u ^ (n - k) * u⁻¹ ^ (n + 2)) := by ring
    _ = ((-1 : ℂ) ^ (k + n) * 2 ^ k * (Nat.choose n k : ℂ)) *
          u⁻¹ ^ (k + 2) := by rw [hpow]
    _ = _ := by ring

theorem integrable_routeUCayleyPoleOscillation (j : ℕ) (ξ : ℝ) :
    Integrable (fun x : ℝ => routeUCayleyPolePower j x *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) := by
  apply (integrable_routeUCayleyPolePower j).mul_bdd (by fun_prop)
  filter_upwards with x
  rw [show -I * ((ξ * x : ℝ) : ℂ) = (((-(ξ * x) : ℝ) : ℂ) * I) by
    push_cast
    ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

theorem routeUFourierIntegral_cayleyModeKernel_eq_sum
    {m : ℕ} (hm : 0 < m) (ξ : ℝ) :
    routeUFourierIntegral (routeUCayleyModeKernel m) ξ =
      ∑ k ∈ Finset.range m, routeUCayleyPoleCoefficient m k *
        routeUFourierIntegral (routeUCayleyPolePower k) ξ := by
  rw [routeUFourierIntegral]
  have hfun : routeUCayleyModeKernel m = fun x : ℝ =>
      ∑ k ∈ Finset.range m,
        routeUCayleyPoleCoefficient m k * routeUCayleyPolePower k x := by
    funext x
    exact routeUCayleyModeKernel_eq_sum_poles hm x
  rw [hfun]
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [routeUFourierIntegral]
    calc
      (∫ a : ℝ, routeUCayleyPoleCoefficient m k *
          routeUCayleyPolePower k a * Complex.exp (-I * ((ξ * a : ℝ) : ℂ))) =
        ∫ a : ℝ, routeUCayleyPoleCoefficient m k *
          (routeUCayleyPolePower k a * Complex.exp (-I * ((ξ * a : ℝ) : ℂ))) := by
            apply integral_congr_ae
            filter_upwards with a
            ring
      _ = routeUCayleyPoleCoefficient m k *
          ∫ a : ℝ, routeUCayleyPolePower k a *
            Complex.exp (-I * ((ξ * a : ℝ) : ℂ)) :=
        MeasureTheory.integral_const_mul _ _
  · intro k hk
    have h := (integrable_routeUCayleyPoleOscillation k ξ).const_mul
      (routeUCayleyPoleCoefficient m k)
    convert h using 1
    funext x
    ring

/-- Associated Laguerre polynomial in Route U normalization.  Index `k` is
`j-1`, so this is exactly `∑_{j=1}^m (-1)^j choose(m-1,j-1)x^j/j!`. -/
def routeUAssociatedLaguerreMinusOne (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m,
    (-1 : ℝ) ^ (k + 1) * (Nat.choose (m - 1) k : ℝ) * x ^ (k + 1) /
      ((k + 1).factorial : ℝ)

private theorem routeUNegOnePowerCoefficient {m : ℕ} (hm : 0 < m) (k : ℕ) :
    (-1 : ℂ) ^ (k + (m - 1)) =
      (-1 : ℂ) ^ m * (-1 : ℂ) ^ (k + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one]
  rw [← pow_add]
  calc
    (-1 : ℂ) ^ (k + n) = (-1 : ℂ) ^ (k + n) * (-1 : ℂ) ^ 2 := by
      norm_num
    _ = (-1 : ℂ) ^ (k + n + 2) := by rw [← pow_add]
    _ = (-1 : ℂ) ^ (n + 1 + (k + 1)) := by
      congr 1
      omega

theorem routeUFourierIntegral_cayleyModeKernel_pos
    {m : ℕ} (hm : 0 < m) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (routeUCayleyModeKernel m) ξ =
      (Real.pi : ℂ) * (-1 : ℂ) ^ m * Complex.exp (-((ξ : ℝ) : ℂ)) *
        (routeUAssociatedLaguerreMinusOne m (2 * ξ) : ℂ) := by
  rw [routeUFourierIntegral_cayleyModeKernel_eq_sum hm]
  simp_rw [routeUFourierIntegral_cayleyPolePower_pos _ hξ,
    routeUCayleyPoleCoefficient, routeUNegOnePowerCoefficient hm]
  rw [routeUAssociatedLaguerreMinusOne]
  push_cast
  rw [show (Real.pi : ℂ) * (-1 : ℂ) ^ m * Complex.exp (-((ξ : ℝ) : ℂ)) *
      ∑ k ∈ Finset.range m,
        (-1 : ℂ) ^ (k + 1) * (Nat.choose (m - 1) k : ℂ) *
          (2 * (ξ : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ) =
      ∑ k ∈ Finset.range m,
        ((Real.pi : ℂ) * (-1 : ℂ) ^ m * Complex.exp (-((ξ : ℝ) : ℂ))) *
          ((-1 : ℂ) ^ (k + 1) * (Nat.choose (m - 1) k : ℂ) *
            (2 * (ξ : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ)) by
    rw [Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, pow_succ (2 : ℂ) k]
  ring

theorem routeUFourierIntegral_cayleyModeKernel_neg
    {m : ℕ} (hm : 0 < m) {ξ : ℝ} (hξ : ξ < 0) :
    routeUFourierIntegral (routeUCayleyModeKernel m) ξ = 0 := by
  rw [routeUFourierIntegral_cayleyModeKernel_eq_sum hm]
  simp_rw [routeUFourierIntegral_cayleyPolePower_neg _ hξ, mul_zero]
  simp

def routeUCayleyInverseModeKernel (m : ℕ) (x : ℝ) : ℂ :=
  ((((1 : ℂ) - I * (x : ℂ)) / ((1 : ℂ) + I * (x : ℂ))) ^ m) /
    ((1 : ℂ) + (x : ℂ) ^ 2)

theorem routeUCayleyInverseModeKernel_eq_reflect (m : ℕ) (x : ℝ) :
    routeUCayleyInverseModeKernel m x = routeUCayleyModeKernel m (-x) := by
  rw [routeUCayleyInverseModeKernel, routeUCayleyModeKernel]
  push_cast
  ring

theorem routeUFourierIntegral_reflect (f : ℝ → ℂ) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ => f (-x)) ξ =
      routeUFourierIntegral f (-ξ) := by
  let G : ℝ → ℂ := fun y =>
    f y * Complex.exp (-I * (((-ξ) * y : ℝ) : ℂ))
  have hscale := MeasureTheory.Measure.integral_comp_mul_left G (-1)
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at hscale
  rw [routeUFourierIntegral, routeUFourierIntegral]
  calc
    (∫ x : ℝ, f (-x) * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
        ∫ x : ℝ, G ((-1) * x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [G]
      congr 2
      · ring
      · have harg : ξ * x = (-ξ) * ((-1 : ℝ) * x) := by ring
        rw [harg]
    _ = ∫ y : ℝ, G y := hscale
    _ = ∫ y : ℝ, f y * Complex.exp (-I * (((-ξ) * y : ℝ) : ℂ)) := by
      rfl

theorem routeUFourierIntegral_cayleyInverseModeKernel_neg
    {m : ℕ} (hm : 0 < m) {ξ : ℝ} (hξ : ξ < 0) :
    routeUFourierIntegral (routeUCayleyInverseModeKernel m) ξ =
      (Real.pi : ℂ) * (-1 : ℂ) ^ m * Complex.exp (((ξ : ℝ) : ℂ)) *
        (routeUAssociatedLaguerreMinusOne m (-2 * ξ) : ℂ) := by
  have hpos : 0 < -ξ := neg_pos.mpr hξ
  rw [show routeUCayleyInverseModeKernel m =
      fun x : ℝ => routeUCayleyModeKernel m (-x) by
    funext x
    exact routeUCayleyInverseModeKernel_eq_reflect m x]
  rw [routeUFourierIntegral_reflect]
  have h := routeUFourierIntegral_cayleyModeKernel_pos hm hpos
  have hexp : -(((-ξ : ℝ) : ℂ)) = ((ξ : ℝ) : ℂ) := by
    push_cast
    ring
  have hlag : 2 * (-ξ) = -2 * ξ := by ring
  rw [hexp, hlag] at h
  exact h

theorem routeUFourierIntegral_cayleyInverseModeKernel_pos
    {m : ℕ} (hm : 0 < m) {ξ : ℝ} (hξ : 0 < ξ) :
    routeUFourierIntegral (routeUCayleyInverseModeKernel m) ξ = 0 := by
  have hneg : -ξ < 0 := neg_neg_of_pos hξ
  rw [show routeUCayleyInverseModeKernel m =
      fun x : ℝ => routeUCayleyModeKernel m (-x) by
    funext x
    exact routeUCayleyInverseModeKernel_eq_reflect m x]
  rw [routeUFourierIntegral_reflect,
    routeUFourierIntegral_cayleyModeKernel_neg hm hneg]

theorem routeUFourierIntegral_cayleyModeKernel_zero
    {m : ℕ} (hm : 0 < m) :
    routeUFourierIntegral (routeUCayleyModeKernel m) 0 = 0 := by
  rw [routeUFourierIntegral_cayleyModeKernel_eq_sum hm]
  simp_rw [routeUFourierIntegral_cayleyPolePower, routeUGammaDatum]
  simp

theorem routeUFourierIntegral_cayleyInverseModeKernel_zero
    {m : ℕ} (hm : 0 < m) :
    routeUFourierIntegral (routeUCayleyInverseModeKernel m) 0 = 0 := by
  rw [show routeUCayleyInverseModeKernel m =
      fun x : ℝ => routeUCayleyModeKernel m (-x) by
    funext x
    exact routeUCayleyInverseModeKernel_eq_reflect m x]
  rw [routeUFourierIntegral_reflect, neg_zero,
    routeUFourierIntegral_cayleyModeKernel_zero hm]

def routeUCauchyKernel (x : ℝ) : ℂ :=
  ((1 : ℂ) + (x : ℂ) ^ 2)⁻¹

theorem routeUFourierIntegral_cauchyKernel (ξ : ℝ) :
    routeUFourierIntegral routeUCauchyKernel ξ =
      (Real.pi * Real.exp (-|ξ|) : ℝ) := by
  have h := GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq_mul_cexp_neg
    (a := (1 : ℝ)) (by norm_num) ξ
  rw [routeUFourierIntegral]
  simp only [routeUCauchyKernel]
  rw [show (∫ x : ℝ, ((1 : ℂ) + (x : ℂ) ^ 2)⁻¹ *
      Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      ∫ x : ℝ, (((1 : ℝ) ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ *
        Complex.exp (((-(ξ * x) : ℝ) : ℂ) * I) by
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    congr 2 <;> ring]
  simpa using h

theorem integrable_routeUCayleyModeKernel {m : ℕ} (hm : 0 < m) :
    Integrable (routeUCayleyModeKernel m) := by
  have hsum : Integrable (fun x : ℝ =>
      ∑ k ∈ Finset.range m,
        routeUCayleyPoleCoefficient m k * routeUCayleyPolePower k x) := by
    apply integrable_finsetSum
    intro k hk
    exact (integrable_routeUCayleyPolePower k).const_mul _
  exact hsum.congr (Filter.Eventually.of_forall fun x =>
    (routeUCayleyModeKernel_eq_sum_poles hm x).symm)

theorem integrable_routeUCayleyInverseModeKernel {m : ℕ} (hm : 0 < m) :
    Integrable (routeUCayleyInverseModeKernel m) := by
  have hreflect : Integrable (fun x : ℝ => routeUCayleyModeKernel m (-x)) := by
    have h := (integrable_routeUCayleyModeKernel hm).comp_mul_left'
      (R := (-1 : ℝ)) (by norm_num)
    simpa using h
  exact hreflect.congr (Filter.Eventually.of_forall fun x =>
    (routeUCayleyInverseModeKernel_eq_reflect m x).symm)

theorem integrable_routeUCauchyKernel : Integrable routeUCauchyKernel := by
  have hreal := GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq
    (a := (1 : ℝ)) (by norm_num)
  have hcomplex := hreal.ofReal (𝕜 := ℂ)
  convert hcomplex using 1
  funext x
  rw [routeUCauchyKernel]
  push_cast
  norm_num

private theorem integrable_routeUFourierIntegrand
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ => f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) := by
  apply hf.mul_bdd (by fun_prop)
  filter_upwards with x
  rw [show -I * ((ξ * x : ℝ) : ℂ) = (((-(ξ * x) : ℝ) : ℂ) * I) by
    push_cast
    ring]
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)

private theorem routeUFourierIntegral_add
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    routeUFourierIntegral (fun x => f x + g x) ξ =
      routeUFourierIntegral f ξ + routeUFourierIntegral g ξ := by
  rw [routeUFourierIntegral, routeUFourierIntegral, routeUFourierIntegral]
  have hfi := integrable_routeUFourierIntegrand hf ξ
  have hgi := integrable_routeUFourierIntegrand hg ξ
  rw [show (∫ x : ℝ, (f x + g x) * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      ∫ x : ℝ, f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) +
        g x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ)) by
    apply integral_congr_ae
    filter_upwards with x
    ring]
  exact integral_add hfi hgi

private theorem routeUFourierIntegral_const_mul
    (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    routeUFourierIntegral (fun x => c * f x) ξ =
      c * routeUFourierIntegral f ξ := by
  rw [routeUFourierIntegral, routeUFourierIntegral]
  rw [show (∫ x : ℝ, c * f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) =
      ∫ x : ℝ, c * (f x * Complex.exp (-I * ((ξ * x : ℝ) : ℂ))) by
    apply integral_congr_ae
    filter_upwards with x
    ring]
  exact MeasureTheory.integral_const_mul _ _

/-- Algebraic Cayley form of `cos(m arctan x)^2 / (1+x^2)`. -/
def routeUCayleyCosineSquareKernel (m : ℕ) (x : ℝ) : ℂ :=
  (2 * routeUCauchyKernel x + routeUCayleyModeKernel m x +
    routeUCayleyInverseModeKernel m x) / 4

theorem routeUFourierIntegral_cayleyCosineSquareKernel
    {m : ℕ} (hm : 0 < m) (ξ : ℝ) :
    routeUFourierIntegral (routeUCayleyCosineSquareKernel m) ξ =
      ((Real.pi / 4 * Real.exp (-|ξ|) *
        (2 + (-1 : ℝ) ^ m * routeUAssociatedLaguerreMinusOne m (2 * |ξ|)) : ℝ) : ℂ) := by
  have hC : Integrable (fun x : ℝ => (2 : ℂ) * routeUCauchyKernel x) :=
    integrable_routeUCauchyKernel.const_mul _
  have hM := integrable_routeUCayleyModeKernel hm
  have hI := integrable_routeUCayleyInverseModeKernel hm
  rw [show routeUCayleyCosineSquareKernel m = fun x : ℝ =>
      (1 / 4 : ℂ) * (((2 : ℂ) * routeUCauchyKernel x +
        routeUCayleyModeKernel m x) + routeUCayleyInverseModeKernel m x) by
    funext x
    rw [routeUCayleyCosineSquareKernel]
    ring]
  rw [routeUFourierIntegral_const_mul]
  change (1 / 4 : ℂ) *
      routeUFourierIntegral (fun x : ℝ =>
        ((2 : ℂ) * routeUCauchyKernel x + routeUCayleyModeKernel m x) +
          routeUCayleyInverseModeKernel m x) ξ = _
  rw [routeUFourierIntegral_add (f := fun x : ℝ =>
      (2 : ℂ) * routeUCauchyKernel x + routeUCayleyModeKernel m x)
    (g := routeUCayleyInverseModeKernel m) (hC.add hM) hI]
  rw [routeUFourierIntegral_add (f := fun x : ℝ =>
      (2 : ℂ) * routeUCauchyKernel x) (g := routeUCayleyModeKernel m) hC hM]
  rw [routeUFourierIntegral_const_mul,
    routeUFourierIntegral_cauchyKernel]
  rcases lt_trichotomy ξ 0 with hneg | hzero | hpos
  · rw [abs_of_neg hneg,
      routeUFourierIntegral_cayleyModeKernel_neg hm hneg,
      routeUFourierIntegral_cayleyInverseModeKernel_neg hm hneg]
    have hexp : Complex.exp (((ξ : ℝ) : ℂ)) =
        ((Real.exp ξ : ℝ) : ℂ) := by rw [Complex.ofReal_exp]
    rw [hexp]
    push_cast
    ring

  · subst ξ
    rw [routeUFourierIntegral_cayleyModeKernel_zero hm,
      routeUFourierIntegral_cayleyInverseModeKernel_zero hm]
    have hlag : routeUAssociatedLaguerreMinusOne m 0 = 0 := by
      simp [routeUAssociatedLaguerreMinusOne]
    norm_num [hlag]
    ring
  · rw [abs_of_pos hpos,
      routeUFourierIntegral_cayleyModeKernel_pos hm hpos,
      routeUFourierIntegral_cayleyInverseModeKernel_pos hm hpos]
    have hexp : Complex.exp (-((ξ : ℝ) : ℂ)) =
        ((Real.exp (-ξ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    rw [hexp]
    push_cast
    ring

private theorem routeUCayleyRatio_eq_trigSquare (x : ℝ) :
    ((1 : ℂ) + I * (x : ℂ)) / ((1 : ℂ) - I * (x : ℂ)) =
      (((Real.cos (Real.arctan x) : ℝ) : ℂ) +
        ((Real.sin (Real.arctan x) : ℝ) : ℂ) * I) ^ 2 := by
  let r : ℝ := Real.sqrt (1 + x ^ 2)
  have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr : r ^ 2 = 1 + x ^ 2 := by
    dsimp only [r]
    exact Real.sq_sqrt (by positivity)
  have hu : (1 : ℂ) - I * (x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.mul_re] at hre
  rw [Real.cos_arctan, Real.sin_arctan]
  change ((1 : ℂ) + I * (x : ℂ)) / ((1 : ℂ) - I * (x : ℂ)) =
    (((1 / r : ℝ) : ℂ) + (((x / r : ℝ) : ℂ) * I)) ^ 2
  push_cast
  field_simp [hu, ne_of_gt hrpos]
  have hrc : (r : ℂ) ^ 2 = 1 + (x : ℂ) ^ 2 := by exact_mod_cast hr
  have hfactor : (1 : ℂ) + (x : ℂ) ^ 2 =
      (1 + I * (x : ℂ)) * (1 - I * (x : ℂ)) := by
    linear_combination ((x : ℂ) ^ 2) * Complex.I_sq
  rw [hrc, hfactor]
  ring

private theorem routeUCayleyModeKernel_eq_trig (m : ℕ) (x : ℝ) :
    routeUCayleyModeKernel m x =
      (((Real.cos ((2 * m : ℕ) * Real.arctan x) : ℝ) : ℂ) +
        ((Real.sin ((2 * m : ℕ) * Real.arctan x) : ℝ) : ℂ) * I) *
        routeUCauchyKernel x := by
  rw [routeUCayleyModeKernel, routeUCauchyKernel,
    routeUCayleyRatio_eq_trigSquare]
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← pow_mul,
    Complex.cos_add_sin_mul_I_pow]
  push_cast
  ring

private theorem routeUCayleyInverseModeKernel_eq_trig (m : ℕ) (x : ℝ) :
    routeUCayleyInverseModeKernel m x =
      (((Real.cos ((2 * m : ℕ) * Real.arctan x) : ℝ) : ℂ) -
        ((Real.sin ((2 * m : ℕ) * Real.arctan x) : ℝ) : ℂ) * I) *
        routeUCauchyKernel x := by
  rw [routeUCayleyInverseModeKernel_eq_reflect,
    routeUCayleyModeKernel_eq_trig]
  simp only [Real.arctan_neg, Nat.cast_mul, Nat.cast_ofNat, mul_neg,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul]
  rw [show routeUCauchyKernel (-x) = routeUCauchyKernel x by
    rw [routeUCauchyKernel, routeUCauchyKernel]
    push_cast
    ring]
  ring

theorem routeUCayleyCosineSquareKernel_eq (m : ℕ) (x : ℝ) :
    routeUCayleyCosineSquareKernel m x =
      ((Real.cos ((m : ℝ) * Real.arctan x) ^ 2 / (1 + x ^ 2) : ℝ) : ℂ) := by
  rw [routeUCayleyCosineSquareKernel,
    routeUCayleyModeKernel_eq_trig,
    routeUCayleyInverseModeKernel_eq_trig,
    routeUCauchyKernel]
  rw [Real.cos_sq]
  push_cast
  ring

/-- Exact no-`2π` Fourier transform of the Route U cosine-square kernel. -/
theorem routeUFourierIntegral_cosineSquareKernel
    {m : ℕ} (hm : 0 < m) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      ((Real.cos ((m : ℝ) * Real.arctan x) ^ 2 / (1 + x ^ 2) : ℝ) : ℂ)) ξ =
      ((Real.pi / 4 * Real.exp (-|ξ|) *
        (2 + (-1 : ℝ) ^ m * routeUAssociatedLaguerreMinusOne m (2 * |ξ|)) : ℝ) : ℂ) := by
  rw [show (fun x : ℝ =>
      ((Real.cos ((m : ℝ) * Real.arctan x) ^ 2 / (1 + x ^ 2) : ℝ) : ℂ)) =
      routeUCayleyCosineSquareKernel m by
    funext x
    exact (routeUCayleyCosineSquareKernel_eq m x).symm]
  exact routeUFourierIntegral_cayleyCosineSquareKernel hm ξ

/-- Even-mode specialization used by Route U. -/
theorem routeUFourierIntegral_cosineSquareKernel_even
    {n : ℕ} (hn : 0 < n) (ξ : ℝ) :
    routeUFourierIntegral (fun x : ℝ =>
      ((Real.cos ((2 * n : ℕ) * Real.arctan x) ^ 2 /
        (1 + x ^ 2) : ℝ) : ℂ)) ξ =
      ((Real.pi / 4 * Real.exp (-|ξ|) *
        (2 + routeUAssociatedLaguerreMinusOne (2 * n) (2 * |ξ|)) : ℝ) : ℂ) := by
  rw [routeUFourierIntegral_cosineSquareKernel (m := 2 * n) (by omega)]
  have heven : (-1 : ℝ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, one_mul]

end

end RHTower

