import GaloisForLFunctions.RHTower.MontgomeryBlockSplit
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanBandPerturbation

/-!
# The zero power sum as a band sum

At scale `x = T^α e^{−ξ}` the zero power sum `Σ_{ρ∈A} x^{ρ−1/2}` is `T^{α(σ−1/2)}` times the
band sum with frequencies `u_ρ = γ log T / 2π` (mean-spacing units), coefficients
`d_ρ(ξ) = e^{−(ρ−1/2)ξ}` and exponents `θ_ρ = (Re ρ − σ) log T`.  The Bochner integrand of the
pair form is integrable, and restricting the Laplace variable to `|ξ| ≤ 1` costs a factor `e^{−2}`.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Frequency of a zero copy in mean-spacing units at height scale `T`. -/
def bandFreq (T : ℝ) (j : XiZeroCopy) : ℝ := (j.1 : ℂ).im * Real.log T / (2 * Real.pi)

/-- Laplace-variable coefficient `e^{−(ρ−1/2)ξ}`. -/
def bandCoeff (ξ : ℝ) (j : XiZeroCopy) : ℂ := cexp (-(((j.1 : ℂ) - 1 / 2) * ξ))

/-- Band exponent `(Re ρ − σ) log T`. -/
def bandTheta (T σ : ℝ) (j : XiZeroCopy) : ℝ := ((j.1 : ℂ).re - σ) * Real.log T

/-- The zero power sum at scale `T^α e^{−ξ}` is the band sum times the common amplitude. -/
theorem zeroPowerSum_eq_bandSum (A : Finset XiZeroCopy) {T : ℝ} (hT : 0 < T) (σ ξ α : ℝ) :
    zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ)) =
      ((Real.exp (α * (σ - 1 / 2) * Real.log T) : ℝ) : ℂ) *
        GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α := by
  unfold zeroPowerSum GaloisForLFunctions.HTGeometry.mvBandSum
  rw [Finset.sum_coe_sort A (fun j => bandCoeff ξ j * ((Real.exp (bandTheta T σ j * α) : ℝ) : ℂ) *
    GaloisForLFunctions.HTGeometry.mvExp (bandFreq T j) α), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT α
  rw [cpow_mul_exp_neg hx ξ ((j.1 : ℂ) - 1 / 2)]
  have hxne : ((T ^ α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hxne, ← Complex.ofReal_log hx.le, Real.log_rpow hT]
  unfold bandCoeff bandTheta bandFreq GaloisForLFunctions.HTGeometry.mvExp
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hρ := Complex.re_add_im (j.1 : ℂ)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfreq : (2 * (Real.pi : ℂ) * I * (((j.1 : ℂ).im * Real.log T / (2 * Real.pi) : ℝ) : ℂ)) * (α : ℂ)
      = I * ((j.1 : ℂ).im : ℂ) * (Real.log T : ℂ) * (α : ℂ) := by
    push_cast
    field_simp
  rw [hfreq]
  push_cast
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im]
    ring

/-- Squared modulus form of the identification. -/
theorem normSq_zeroPowerSum_eq_bandSum (A : Finset XiZeroCopy) {T : ℝ} (hT : 0 < T) (σ ξ α : ℝ) :
    ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2 =
      Real.exp (2 * (α * (σ - 1 / 2) * Real.log T)) *
        ‖GaloisForLFunctions.HTGeometry.mvBandSum (fun j : A => bandFreq T j)
          (fun j : A => bandCoeff ξ j) (fun j : A => bandTheta T σ j) α‖ ^ 2 := by
  rw [zeroPowerSum_eq_bandSum A hT σ ξ α, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The band coefficients have modulus at least `e^{−|ξ|/2}`. -/
theorem normSq_bandCoeff_ge (ξ : ℝ) (j : XiZeroCopy) :
    Real.exp (-|ξ|) ≤ ‖bandCoeff ξ j‖ ^ 2 := by
  unfold bandCoeff
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hre : (-(((j.1 : ℂ) - 1 / 2) * ξ)).re = -(((j.1 : ℂ).re - 1 / 2) * ξ) := by simp
  rw [hre]
  have h0 := xiZeroCopy_re_pos j
  have h1 := xiZeroCopy_re_lt_one j
  push_cast
  have : |((j.1 : ℂ).re - 1 / 2) * ξ| ≤ |ξ| / 2 := by
    rw [abs_mul]
    have hb : |(j.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |(j.1 : ℂ).re - 1 / 2| * |ξ| ≤ 1 / 2 * |ξ| := by gcongr
      _ = |ξ| / 2 := by ring
  have := (abs_le.mp this).2
  linarith [abs_nonneg ξ]


/-- The band coefficients have modulus at most `e^{|ξ|/2}`. -/
theorem normSq_bandCoeff_le (ξ : ℝ) (j : XiZeroCopy) :
    ‖bandCoeff ξ j‖ ^ 2 ≤ Real.exp |ξ| := by
  unfold bandCoeff
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hre : (-(((j.1 : ℂ) - 1 / 2) * ξ)).re = -(((j.1 : ℂ).re - 1 / 2) * ξ) := by simp
  rw [hre]
  have h0 := xiZeroCopy_re_pos j
  have h1 := xiZeroCopy_re_lt_one j
  push_cast
  have : |((j.1 : ℂ).re - 1 / 2) * ξ| ≤ |ξ| / 2 := by
    rw [abs_mul]
    have hb : |(j.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |(j.1 : ℂ).re - 1 / 2| * |ξ| ≤ 1 / 2 * |ξ| := by gcongr
      _ = |ξ| / 2 := by ring
  have := (abs_le.mp this).1
  linarith [abs_nonneg ξ]

/-- The real Bochner integrand of the pair form is integrable. -/
theorem integrable_bochner_integrand (s : Finset XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    Integrable (fun ξ : ℝ => Real.exp (-2 * |ξ|) *
      ‖zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))‖ ^ 2) := by
  classical
  set ρ : XiZeroCopy → ℂ := fun q => (q.1 : ℂ) with hρdef
  have hstrip : ∀ j ∈ s, ∀ k ∈ s, |(ρ j + (starRingEnd ℂ) (ρ k) - 1).re| < 2 := by
    intro j _ k _
    have hj0 := xiZeroCopy_re_pos j
    have hj1 := xiZeroCopy_re_lt_one j
    have hk0 := xiZeroCopy_re_pos k
    have hk1 := xiZeroCopy_re_lt_one k
    rw [abs_lt]
    simp only [hρdef, Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
    constructor <;> linarith
  have hpair : ∀ ξ : ℝ, ((Real.exp (-2 * |ξ|) * ‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ s, ∑ k ∈ s, (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
          (((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-((ρ j + (starRingEnd ℂ) (ρ k) - 1) * ξ))) := by
    intro ξ
    have hz : zeroPowerSum s ρ (x * Real.exp (-ξ))
        = ∑ j ∈ s, (x : ℂ) ^ (ρ j - 1 / 2) * cexp (-((ρ j - 1 / 2) * ξ)) := by
      unfold zeroPowerSum
      refine Finset.sum_congr rfl fun j _ => ?_
      exact cpow_mul_exp_neg hx ξ (ρ j - 1 / 2)
    have hnorm : ((‖zeroPowerSum s ρ (x * Real.exp (-ξ))‖ ^ 2 : ℝ) : ℂ)
        = zeroPowerSum s ρ (x * Real.exp (-ξ)) *
            (starRingEnd ℂ) (zeroPowerSum s ρ (x * Real.exp (-ξ))) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_mul, hnorm, hz, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pair_term_eq hx ξ (ρ j) (ρ k)]
    ring
  have hint : Integrable (fun ξ : ℝ => ∑ j ∈ s, ∑ k ∈ s, (x : ℂ) ^ (ρ j + (starRingEnd ℂ) (ρ k) - 1) *
      (((Real.exp (-2 * |ξ|) : ℝ) : ℂ) * cexp (-((ρ j + (starRingEnd ℂ) (ρ k) - 1) * ξ)))) := by
    refine integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun k hk => ?_
    exact (integrable_exp_neg_two_abs_mul_cexp (hstrip j hj k hk)).const_mul _
  have hre := hint.re
  refine hre.congr ?_
  filter_upwards with ξ
  rw [← hpair ξ, RCLike.re_to_complex, Complex.ofReal_re]

/-- The zero power sum is continuous in the Laplace variable. -/
theorem continuous_zeroPowerSum_exp (s : Finset XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    Continuous (fun ξ : ℝ => zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))) := by
  have hfun : (fun ξ : ℝ => zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ)))
      = fun ξ : ℝ => ∑ j ∈ s, (x : ℂ) ^ ((j.1 : ℂ) - 1 / 2) * cexp (-(((j.1 : ℂ) - 1 / 2) * ξ)) := by
    funext ξ
    unfold zeroPowerSum
    exact Finset.sum_congr rfl fun j _ => cpow_mul_exp_neg hx ξ _
  rw [hfun]
  fun_prop

/-- Restricting the Laplace variable to `|ξ| ≤ 1` bounds the pair form from below. -/
theorem montgomeryForm_re_ge_window (s : Finset XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    Real.exp (-2) * ∫ ξ in (-1 : ℝ)..1,
        ‖zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))‖ ^ 2
      ≤ (montgomeryForm s (fun q : XiZeroCopy => (q.1 : ℂ)) x).re := by
  rw [montgomeryForm_eq_ofReal s _ hx (fun q _ => ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩),
    Complex.ofReal_re]
  set f : ℝ → ℝ := fun ξ => Real.exp (-2 * |ξ|) *
    ‖zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))‖ ^ 2 with hf
  set g : ℝ → ℝ := fun ξ => Real.exp (-2) *
    ‖zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))‖ ^ 2 with hg
  have hfi : Integrable f := integrable_bochner_integrand s hx
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by simp only [hf]; positivity
  have hgcont : Continuous g := by
    simp only [hg]
    exact continuous_const.mul ((continuous_zeroPowerSum_exp s hx).norm.pow 2)
  have hgi : IntegrableOn g (Ioc (-1 : ℝ) 1) :=
    (hgcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h1 : ∫ ξ in Ioc (-1 : ℝ) 1, f ξ ≤ ∫ ξ, f ξ :=
    setIntegral_le_integral hfi (Filter.Eventually.of_forall hf0)
  have h2 : ∫ ξ in Ioc (-1 : ℝ) 1, g ξ ≤ ∫ ξ in Ioc (-1 : ℝ) 1, f ξ := by
    refine setIntegral_mono_on hgi hfi.integrableOn measurableSet_Ioc ?_
    intro ξ hξ
    simp only [hf, hg]
    have hξ1 : |ξ| ≤ 1 := by
      rw [abs_le]; exact ⟨hξ.1.le, hξ.2⟩
    have : Real.exp (-2) ≤ Real.exp (-2 * |ξ|) := by
      apply Real.exp_le_exp.mpr; linarith
    gcongr
  have h3 : Real.exp (-2) * ∫ ξ in (-1 : ℝ)..1,
      ‖zeroPowerSum s (fun q : XiZeroCopy => (q.1 : ℂ)) (x * Real.exp (-ξ))‖ ^ 2
      = ∫ ξ in Ioc (-1 : ℝ) 1, g ξ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), ← integral_const_mul]
  rw [h3]
  linarith

end

end RHTower
