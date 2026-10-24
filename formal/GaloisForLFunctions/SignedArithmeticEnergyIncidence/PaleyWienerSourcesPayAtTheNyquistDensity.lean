import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Paley–Wiener sources pay at the Nyquist density

Beyond the local polynomial model the signed sampling law is exact for Paley–Wiener sources
sampled on a lattice.  A source of aperture `A` is `f(x) = ∫ F(ξ) e^{ixξ} dξ` with an `L²`
spectral density `F` vanishing for `|ξ| ≥ A` (`pwSource`); its derivative is
`f'(t) = ∫ iξ F(ξ) e^{itξ} dξ` (`pwDeriv`, `hasDerivAt_pwSource`).  On-line companions sit on the
lattice `t₀ + hℤ`, an off-line depth mass `w` at an arbitrary height `t`.

* **Lattice Parseval** (`hasSum_sq_pwSource_lattice`): for `A h ≤ π`,
  `Σ_k |f(t₀ + kh)|² = (2π/h) ∫ |F|²`; the companion values are `2π/h` times the Fourier
  coefficients of `F e^{it₀ξ}` on `[−π/h, π/h]`.
* **Companions pay** (`pwCompanions_pay`): then `w |f'(t)|² ≤ Σ_k |f(t₀ + kh)|²` whenever
  `w A³h/(3π) ≤ 1`, at every height and offset, since `|f'(t)|² ≤ (2A³/3) ∫ |F|²`
  (`norm_sq_pwDeriv_le`).
* **The price is exact** (`pwCompanions_price_sharp`): the density `−iξ e^{−itξ}` on `(−A, A)`
  defeats every `w` with `w A³h/(3π) > 1`.
* **Below the Nyquist density companions never pay** (`pwCompanions_never_pay`): for `A h > π`
  the density `ψ − ψ(· − 2π/h)` vanishes at every companion while `f'(t) = ∫ |κ|² > 0`.

So a companion lattice pays off-line depth for every source of aperture `A`, uniformly in the
height, iff its density `1/h` is at least the Nyquist density `A/π`, and then exactly at the price
`A³h/(3π)`: the continuum form of the companion count law, companions per unit height against
degrees of freedom per unit height.
-/

open MeasureTheory Complex Set Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- The Paley–Wiener source with spectral density `F`: `f(x) = ∫ F(ξ) e^{ixξ} dξ`. -/
def pwSource (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, F ξ * exp (((x * ξ : ℝ) : ℂ) * I)

/-- Its derivative `f'(x) = ∫ iξ F(ξ) e^{ixξ} dξ`. -/
def pwDeriv (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, ((ξ : ℂ) * I) * F ξ * exp (((x * ξ : ℝ) : ℂ) * I)

/-! ### Densities of aperture `A` -/

variable {F : ℝ → ℂ} {A : ℝ}

/-- A density of aperture `A` is integrable. -/
theorem integrable_of_aperture (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) :
    Integrable F := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hon : IntegrableOn F (Icc (-A) A) := (hF.restrict _).integrable (by norm_num)
  refine (integrableOn_iff_integrable_of_support_subset fun ξ hξ => ?_).mp hon
  rw [mem_Icc]
  by_contra hc
  apply hξ
  refine hsupp ξ ?_
  rcases not_and_or.mp hc with h | h
  · push Not at h; linarith [neg_le_abs ξ]
  · push Not at h; linarith [le_abs_self ξ]

/-- Integrals of densities of aperture `A` live on any interval containing `[−A, A]`. -/
theorem integral_eq_intervalIntegral_of_aperture {g : ℝ → ℂ} (hg : ∀ ξ, A ≤ |ξ| → g ξ = 0)
    {a b : ℝ} (ha : a ≤ -A) (hb : A ≤ b) (ha0 : a ≤ 0) (hb0 : 0 ≤ b) :
    ∫ ξ in a..b, g ξ = ∫ ξ : ℝ, g ξ := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => hg ξ ?_
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
  rcases hξ with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The derivative formula: `pwDeriv F` is the derivative of `pwSource F`. -/
theorem hasDerivAt_pwSource (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) (t : ℝ) :
    HasDerivAt (pwSource F) (pwDeriv F t) t := by
  have hFi := integrable_of_aperture hF hsupp
  have hmeas : AEStronglyMeasurable F volume := hF.1
  have hcont : ∀ x : ℝ, Continuous fun ξ : ℝ => exp (((x * ξ : ℝ) : ℂ) * I) := fun x => by
    fun_prop
  have hderiv : ∀ ξ x : ℝ, HasDerivAt (fun x : ℝ => F ξ * exp (((x * ξ : ℝ) : ℂ) * I))
      (((ξ : ℂ) * I) * F ξ * exp (((x * ξ : ℝ) : ℂ) * I)) x := by
    intro ξ x
    have h1 : HasDerivAt (fun x : ℝ => ((x * ξ : ℝ) : ℂ) * I) ((ξ : ℂ) * I) x := by
      have := ((hasDerivAt_id x).mul_const ξ).ofReal_comp.mul_const I
      simpa using this
    exact ((h1.cexp).const_mul (F ξ)).congr_deriv (by ring)
  have hbound : ∀ ξ x : ℝ, ‖((ξ : ℂ) * I) * F ξ * exp (((x * ξ : ℝ) : ℂ) * I)‖ ≤ |A| * ‖F ξ‖ := by
    intro ξ x
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
    by_cases hξ : A ≤ |ξ|
    · rw [hsupp ξ hξ, norm_zero, mul_zero, mul_zero]
    · push Not at hξ
      exact mul_le_mul_of_nonneg_right (hξ.le.trans (le_abs_self A)) (norm_nonneg _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun x ξ => F ξ * exp (((x * ξ : ℝ) : ℂ) * I))
    (F' := fun x ξ => ((ξ : ℂ) * I) * F ξ * exp (((x * ξ : ℝ) : ℂ) * I))
    (bound := fun ξ => |A| * ‖F ξ‖) (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x => hmeas.mul (hcont x).aestronglyMeasurable)
    (hFi.norm.mono' (hmeas.mul (hcont t).aestronglyMeasurable)
      (ae_of_all _ fun ξ => by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]))
    (((continuous_ofReal.mul continuous_const).aestronglyMeasurable.mul hmeas).mul
      (hcont t).aestronglyMeasurable)
    (ae_of_all _ fun ξ x _ => hbound ξ x) (hFi.norm.const_mul _)
    (ae_of_all _ fun ξ x _ => hderiv ξ x)
  exact h.2

/-! ### Lattice Parseval -/

/-- **Lattice Parseval**: for `A h ≤ π` the companion values on `t₀ + hℤ` have
`Σ_k |f(t₀ + kh)|² = (2π/h) ∫ |F|²`. -/
theorem hasSum_sq_pwSource_lattice (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ : ℝ) :
    HasSum (fun k : ℤ => ‖pwSource F (t₀ + k * h)‖ ^ 2)
      (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by
  have hA : A ≤ Real.pi / h := by rw [le_div_iff₀ hh]; exact hAh
  have hpih : 0 < Real.pi / h := div_pos Real.pi_pos hh
  have hh0 : h ≠ 0 := hh.ne'
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hab : -(Real.pi / h) < Real.pi / h := by linarith
  have hT : Real.pi / h - -(Real.pi / h) = 2 * Real.pi / h := by ring
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℂ, G = fun ξ => F ξ * exp (((t₀ * ξ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hGnorm : ∀ ξ, ‖G ξ‖ = ‖F ξ‖ := fun ξ => by
    rw [hGdef, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  have hGmeas : AEStronglyMeasurable G volume := by
    rw [hGdef]
    exact hF.1.mul (by fun_prop : Continuous fun ξ : ℝ =>
      exp (((t₀ * ξ : ℝ) : ℂ) * I)).aestronglyMeasurable
  have hG2 : MemLp G 2 (volume.restrict (Ioc (-(Real.pi / h)) (Real.pi / h))) :=
    (hF.restrict _).of_le hGmeas.restrict (ae_of_all _ fun ξ => le_of_eq (hGnorm ξ))
  have hpar := hasSum_sq_fourierCoeffOn hab hG2
  -- the companion values are Fourier coefficients of `G`
  have hcoeff : ∀ k : ℤ, pwSource F (t₀ + k * h) =
      ((2 * Real.pi / h : ℝ) : ℂ) * fourierCoeffOn hab G (-k) := by
    intro k
    rw [← hT, fourierCoeffOn_eq_integral, neg_neg, Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, mul_one_div_cancel (by linarith : (0 : ℝ) < Real.pi / h - -(Real.pi / h)).ne',
      Complex.ofReal_one, one_mul]
    have hpt : ∀ ξ : ℝ, fourier k (ξ : AddCircle (Real.pi / h - -(Real.pi / h))) • G ξ =
        F ξ * exp ((((t₀ + k * h) * ξ : ℝ) : ℂ) * I) := by
      intro ξ
      rw [fourier_coe_apply, smul_eq_mul, hT, hGdef, mul_comm, mul_assoc, ← Complex.exp_add]
      congr 2
      have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh0
      have hπ' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ0
      push_cast
      field_simp
    rw [intervalIntegral.integral_congr fun ξ _ => hpt ξ]
    exact (integral_eq_intervalIntegral_of_aperture
      (fun ξ hξ => by rw [hsupp ξ hξ, zero_mul]) (by linarith) hA (by linarith) hpih.le).symm
  have hnorm : ∀ k : ℤ, ‖pwSource F (t₀ + k * h)‖ ^ 2 =
      (2 * Real.pi / h) ^ 2 * ‖fourierCoeffOn hab G (-k)‖ ^ 2 := by
    intro k
    rw [hcoeff k, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
      mul_pow]
  have hneg := ((Equiv.neg ℤ).hasSum_iff.mpr hpar).mul_left ((2 * Real.pi / h) ^ 2)
  have hI : ∫ ξ in -(Real.pi / h)..Real.pi / h, ‖G ξ‖ ^ 2 = ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
    rw [intervalIntegral.integral_congr (g := fun ξ => (‖F ξ‖ ^ 2 : ℝ)) fun ξ _ => by
      simp only [hGnorm ξ]]
    have h := integral_eq_intervalIntegral_of_aperture (g := fun ξ => ((‖F ξ‖ ^ 2 : ℝ) : ℂ))
      (a := -(Real.pi / h)) (b := Real.pi / h)
      (fun ξ hξ => by rw [hsupp ξ hξ, norm_zero, zero_pow two_ne_zero, Complex.ofReal_zero])
      (by linarith) hA (by linarith) hpih.le
    rw [intervalIntegral.integral_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h
  have hval : (2 * Real.pi / h) ^ 2 * ((Real.pi / h - -(Real.pi / h))⁻¹ •
      ∫ ξ in -(Real.pi / h)..Real.pi / h, ‖G ξ‖ ^ 2) =
      2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
    rw [hI, smul_eq_mul, hT]
    field_simp
  rw [hval] at hneg
  refine hneg.congr_fun fun k => ?_
  simp only [Function.comp_apply, Equiv.neg_apply]
  exact hnorm k

/-! ### Cauchy–Schwarz for the derivative -/

/-- `∫_{−A}^{A} ξ² dξ = 2A³/3`. -/
theorem integral_sq_Ioo_eq {A : ℝ} (hA : 0 ≤ A) :
    ∫ ξ in Ioo (-A) A, ξ ^ 2 = 2 * A ^ 3 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), integral_pow]
  ring

/-- **The derivative at any height**: `|f'(t)|² ≤ (2A³/3) ∫ |F|²`. -/
theorem norm_sq_pwDeriv_le (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0)
    (hA : 0 ≤ A) (t : ℝ) :
    ‖pwDeriv F t‖ ^ 2 ≤ 2 * A ^ 3 / 3 * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
  set u : ℝ → ℝ := (Ioo (-A) A).indicator fun ξ => |ξ| with hu
  have hpt : ∀ ξ : ℝ, ‖((ξ : ℂ) * I) * F ξ * exp (((t * ξ : ℝ) : ℂ) * I)‖ = u ξ * ‖F ξ‖ := by
    intro ξ
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
    by_cases hξ : ξ ∈ Ioo (-A) A
    · rw [hu, indicator_of_mem hξ]
    · rw [hu, indicator_of_notMem hξ, zero_mul]
      have : A ≤ |ξ| := by
        simp only [mem_Ioo, not_and_or, not_lt] at hξ
        rcases hξ with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; exact h
      rw [hsupp ξ this, norm_zero, mul_zero]
  haveI : IsFiniteMeasure (volume.restrict (Ioo (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hu2 : MemLp u 2 volume := by
    rw [hu, memLp_indicator_iff_restrict measurableSet_Ioo]
    refine MemLp.of_bound (continuous_abs.aestronglyMeasurable) A ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ fun ξ hξ => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_le.mpr ⟨hξ.1.le, hξ.2.le⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := u) (g := fun ξ => ‖F ξ‖)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun ξ => by simp only [hu]; exact indicator_nonneg (fun _ _ => abs_nonneg _) ξ)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa using hu2) (by simpa using hF.norm)
  have hholder' : (∫ ξ : ℝ, u ξ * ‖F ξ‖) ≤
      Real.sqrt (∫ ξ : ℝ, u ξ ^ 2) * Real.sqrt (∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hholder
  have hU : ∫ ξ : ℝ, u ξ ^ 2 = 2 * A ^ 3 / 3 := by
    have e : (fun ξ => u ξ ^ 2) = (Ioo (-A) A).indicator fun ξ => ξ ^ 2 := by
      funext ξ
      by_cases hξ : ξ ∈ Ioo (-A) A
      · rw [hu, indicator_of_mem hξ, indicator_of_mem hξ, sq_abs]
      · rw [hu, indicator_of_notMem hξ, indicator_of_notMem hξ, zero_pow two_ne_zero]
    rw [e, integral_indicator measurableSet_Ioo, integral_sq_Ioo_eq hA]
  have hnorm : ‖pwDeriv F t‖ ≤ ∫ ξ : ℝ, u ξ * ‖F ξ‖ := by
    unfold pwDeriv
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (ae_of_all _ hpt)
  have hU0 : 0 ≤ ∫ ξ : ℝ, u ξ ^ 2 := integral_nonneg fun ξ => sq_nonneg _
  have hV0 : 0 ≤ ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := integral_nonneg fun ξ => sq_nonneg _
  calc ‖pwDeriv F t‖ ^ 2
      ≤ (Real.sqrt (∫ ξ : ℝ, u ξ ^ 2) * Real.sqrt (∫ ξ : ℝ, ‖F ξ‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder') 2
    _ = (∫ ξ : ℝ, u ξ ^ 2) * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hU0, Real.sq_sqrt hV0]
    _ = 2 * A ^ 3 / 3 * ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := by rw [hU]

/-! ### The signed sampling law -/

/-- **A companion lattice of spacing `h ≤ π/A` pays off-line depth** at every height and offset:
`w |f'(t)|² ≤ Σ_k |f(t₀ + kh)|²` whenever `w A³h/(3π) ≤ 1`. -/
theorem pwCompanions_pay (hF : MemLp F 2 volume) (hsupp : ∀ ξ, A ≤ |ξ| → F ξ = 0) (hA : 0 ≤ A)
    {h : ℝ} (hh : 0 < h) (hAh : A * h ≤ Real.pi) (t₀ t : ℝ) {w : ℝ} (hw : 0 ≤ w)
    (hprice : w * (A ^ 3 * h / (3 * Real.pi)) ≤ 1) :
    w * ‖pwDeriv F t‖ ^ 2 ≤ ∑' k : ℤ, ‖pwSource F (t₀ + k * h)‖ ^ 2 := by
  rw [(hasSum_sq_pwSource_lattice hF hsupp hh hAh t₀).tsum_eq]
  have hD := norm_sq_pwDeriv_le hF hsupp hA t
  have hV0 : 0 ≤ ∫ ξ : ℝ, ‖F ξ‖ ^ 2 := integral_nonneg fun ξ => sq_nonneg _
  have hh0 : h ≠ 0 := hh.ne'
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e : 2 * A ^ 3 / 3 = (A ^ 3 * h / (3 * Real.pi)) * (2 * Real.pi / h) := by
    field_simp
  calc w * ‖pwDeriv F t‖ ^ 2 ≤ w * (2 * A ^ 3 / 3 * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hD hw
    _ = (w * (A ^ 3 * h / (3 * Real.pi))) * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) := by
        rw [e]; ring
    _ ≤ 1 * (2 * Real.pi / h * ∫ ξ : ℝ, ‖F ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hprice (mul_nonneg (by positivity) hV0)
    _ = _ := one_mul _

/-- The extremal density `−iξ e^{−itξ}` on `(−A, A)`. -/
def pwExtremal (A t : ℝ) : ℝ → ℂ :=
  (Ioo (-A) A).indicator fun ξ => -((ξ : ℂ) * I) * exp (((-(t * ξ) : ℝ) : ℂ) * I)

/-- **The Nyquist price is exact**: for `w A³h/(3π) > 1` the extremal density of aperture `A`
has `Σ_k |f(t₀ + kh)|² < w |f'(t)|²`. -/
theorem pwCompanions_price_sharp {A : ℝ} (hA : 0 < A) {h : ℝ} (hh : 0 < h)
    (hAh : A * h ≤ Real.pi) (t₀ t : ℝ) {w : ℝ} (hprice : 1 < w * (A ^ 3 * h / (3 * Real.pi))) :
    MemLp (pwExtremal A t) 2 volume ∧ (∀ ξ, A ≤ |ξ| → pwExtremal A t ξ = 0) ∧
      ∑' k : ℤ, ‖pwSource (pwExtremal A t) (t₀ + k * h)‖ ^ 2 <
        w * ‖pwDeriv (pwExtremal A t) t‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hnormpt : ∀ ξ ∈ Ioo (-A) A,
      ‖-((ξ : ℂ) * I) * exp (((-(t * ξ) : ℝ) : ℂ) * I)‖ = |ξ| := fun ξ _ => by
    rw [norm_mul, norm_neg, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
  have hmem : MemLp (pwExtremal A t) 2 volume := by
    unfold pwExtremal
    rw [memLp_indicator_iff_restrict measurableSet_Ioo]
    refine MemLp.of_bound (by fun_prop : Continuous fun ξ : ℝ =>
      -((ξ : ℂ) * I) * exp (((-(t * ξ) : ℝ) : ℂ) * I)).aestronglyMeasurable A ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ fun ξ hξ => by
      rw [hnormpt ξ hξ]; exact abs_le.mpr ⟨hξ.1.le, hξ.2.le⟩
  have hsupp : ∀ ξ, A ≤ |ξ| → pwExtremal A t ξ = 0 := by
    intro ξ hξ
    unfold pwExtremal
    refine indicator_of_notMem (fun hmem => ?_) _
    have := abs_lt.mpr ⟨hmem.1, hmem.2⟩
    linarith
  refine ⟨hmem, hsupp, ?_⟩
  rw [(hasSum_sq_pwSource_lattice hmem hsupp hh hAh t₀).tsum_eq]
  -- `∫ |F|² = 2A³/3` and `f'(t) = 2A³/3`
  have hV : ∫ ξ : ℝ, ‖pwExtremal A t ξ‖ ^ 2 = 2 * A ^ 3 / 3 := by
    have e : (fun ξ => ‖pwExtremal A t ξ‖ ^ 2) = (Ioo (-A) A).indicator fun ξ => ξ ^ 2 := by
      funext ξ
      unfold pwExtremal
      by_cases hξ : ξ ∈ Ioo (-A) A
      · rw [indicator_of_mem hξ, indicator_of_mem hξ, hnormpt ξ hξ, sq_abs]
      · rw [indicator_of_notMem hξ, indicator_of_notMem hξ, norm_zero, zero_pow two_ne_zero]
    rw [e, integral_indicator measurableSet_Ioo, integral_sq_Ioo_eq hA.le]
  have hD : pwDeriv (pwExtremal A t) t = ((2 * A ^ 3 / 3 : ℝ) : ℂ) := by
    have e : (fun ξ : ℝ => ((ξ : ℂ) * I) * pwExtremal A t ξ * exp (((t * ξ : ℝ) : ℂ) * I)) =
        (Ioo (-A) A).indicator fun ξ => ((ξ ^ 2 : ℝ) : ℂ) := by
      funext ξ
      unfold pwExtremal
      by_cases hξ : ξ ∈ Ioo (-A) A
      · rw [indicator_of_mem hξ, indicator_of_mem hξ]
        have hexp : exp (((-(t * ξ) : ℝ) : ℂ) * I) * exp (((t * ξ : ℝ) : ℂ) * I) = 1 := by
          rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, neg_add_cancel,
            Complex.ofReal_zero, zero_mul, Complex.exp_zero]
        calc ((ξ : ℂ) * I) * (-((ξ : ℂ) * I) * exp (((-(t * ξ) : ℝ) : ℂ) * I)) *
              exp (((t * ξ : ℝ) : ℂ) * I)
            = -((ξ : ℂ) ^ 2 * (I * I)) * (exp (((-(t * ξ) : ℝ) : ℂ) * I) *
                exp (((t * ξ : ℝ) : ℂ) * I)) := by ring
          _ = ((ξ ^ 2 : ℝ) : ℂ) := by rw [hexp, Complex.I_mul_I]; push_cast; ring
      · rw [indicator_of_notMem hξ, indicator_of_notMem hξ, mul_zero, zero_mul]
    unfold pwDeriv
    rw [e, integral_indicator measurableSet_Ioo, integral_complex_ofReal, integral_sq_Ioo_eq hA.le]
  rw [hV, hD, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hh0 : h ≠ 0 := hh.ne'
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have e : w * (2 * A ^ 3 / 3) ^ 2 =
      (w * (A ^ 3 * h / (3 * Real.pi))) * (2 * Real.pi / h * (2 * A ^ 3 / 3)) := by
    field_simp
  rw [e]
  exact lt_mul_of_one_lt_left (by positivity) hprice

/-! ### Below the Nyquist density -/

/-- The wave `iξ e^{iτξ}` that a density is paired with in `f'`. -/
def nyquistWave (τ ξ : ℝ) : ℂ := ((ξ : ℂ) * I) * exp (((τ * ξ : ℝ) : ℂ) * I)

theorem norm_nyquistWave (τ ξ : ℝ) : ‖nyquistWave τ ξ‖ = |ξ| := by
  unfold nyquistWave
  rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    mul_one, mul_one]

theorem continuous_nyquistWave (τ : ℝ) : Continuous (nyquistWave τ) := by
  unfold nyquistWave; fun_prop

/-- The defect `κ(ξ) = iξ e^{iτξ} − i(ξ + c) e^{iτ(ξ+c)}` of a density and its translate. -/
def nyquistDefect (τ c ξ : ℝ) : ℂ := nyquistWave τ ξ - nyquistWave τ (ξ + c)

theorem continuous_nyquistDefect (τ c : ℝ) : Continuous (nyquistDefect τ c) :=
  (continuous_nyquistWave τ).sub ((continuous_nyquistWave τ).comp (continuous_id.add continuous_const))

/-- `κ(ξ) ≠ 0` left of `−c/2`: `|κ(ξ)| ≥ |ξ| − |ξ + c| > 0`. -/
theorem norm_nyquistDefect_pos {τ c ξ : ℝ} (hc : 0 < c) (hξ : ξ < -(c / 2)) :
    0 < ‖nyquistDefect τ c ξ‖ := by
  have hlt : |ξ + c| < |ξ| := by
    rw [abs_of_neg (by linarith : ξ < 0)]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have := norm_sub_norm_le (nyquistWave τ ξ) (nyquistWave τ (ξ + c))
  rw [norm_nyquistWave, norm_nyquistWave] at this
  unfold nyquistDefect
  linarith

/-- The bump `ψ = conj κ` on `(α, β)`. -/
def nyquistBump (τ c α β : ℝ) : ℝ → ℂ :=
  (Ioo α β).indicator fun ξ => (starRingEnd ℂ) (nyquistDefect τ c ξ)

theorem continuous_conj_nyquistDefect (τ c : ℝ) :
    Continuous fun ξ => (starRingEnd ℂ) (nyquistDefect τ c ξ) :=
  Complex.continuous_conj.comp (continuous_nyquistDefect τ c)

theorem integrable_nyquistBump (τ c α β : ℝ) : Integrable (nyquistBump τ c α β) := by
  unfold nyquistBump
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact (continuous_conj_nyquistDefect τ c).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem memLp_nyquistBump (τ c α β : ℝ) : MemLp (nyquistBump τ c α β) 2 volume := by
  haveI : IsFiniteMeasure (volume.restrict (Ioo α β)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn
    (continuous_nyquistDefect τ c).continuousOn
  unfold nyquistBump
  rw [memLp_indicator_iff_restrict measurableSet_Ioo]
  refine MemLp.of_bound (continuous_conj_nyquistDefect τ c).aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact ae_of_all _ fun ξ hξ => by
    rw [RCLike.norm_conj]; exact hC ξ ⟨hξ.1.le, hξ.2.le⟩

/-- A continuous factor times the bump is integrable. -/
theorem integrable_mul_nyquistBump {p : ℝ → ℂ} (hp : Continuous p) (τ c α β : ℝ) :
    Integrable fun ξ => p ξ * nyquistBump τ c α β ξ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := α) (b := β)).exists_bound_of_continuousOn hp.continuousOn
  refine ((integrable_nyquistBump τ c α β).norm.const_mul C).mono'
    (hp.aestronglyMeasurable.mul (integrable_nyquistBump τ c α β).1) (ae_of_all _ fun ξ => ?_)
  rw [norm_mul]
  by_cases hξ : ξ ∈ Ioo α β
  · exact mul_le_mul_of_nonneg_right (hC ξ ⟨hξ.1.le, hξ.2.le⟩) (norm_nonneg _)
  · rw [show nyquistBump τ c α β ξ = 0 from indicator_of_notMem hξ _, norm_zero, mul_zero,
      mul_zero]

/-- The translate `ξ ↦ p ξ ψ(ξ − c)` is integrable and has the integral of `η ↦ p(η + c) ψ(η)`. -/
theorem integral_mul_nyquistBump_sub {p : ℝ → ℂ} (hp : Continuous p) (τ c α β : ℝ) :
    Integrable (fun ξ => p ξ * nyquistBump τ c α β (ξ - c)) ∧
      ∫ ξ : ℝ, p ξ * nyquistBump τ c α β (ξ - c) =
        ∫ η : ℝ, p (η + c) * nyquistBump τ c α β η := by
  have hq : Continuous fun η => p (η + c) := hp.comp (continuous_id.add continuous_const)
  have hi := (integrable_mul_nyquistBump hq τ c α β).comp_sub_right c
  refine ⟨by simpa only [sub_add_cancel] using hi, ?_⟩
  have h := integral_sub_right_eq_self (μ := volume)
    (fun η => p (η + c) * nyquistBump τ c α β η) c
  simpa only [sub_add_cancel] using h

/-- The two-sided density `(ψ − ψ(· − c)) e^{−it₀ξ}`. -/
def nyquistDensity (t₀ τ c α β : ℝ) (ξ : ℝ) : ℂ :=
  (nyquistBump τ c α β ξ - nyquistBump τ c α β (ξ - c)) * exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)

/-- **Below the Nyquist density companions never pay**: for `A h > π`, at every height `t` and
offset `t₀`, some density of aperture `A` vanishes at every companion `t₀ + kh` while
`f'(t) ≠ 0`. -/
theorem pwCompanions_never_pay {A h : ℝ} (hh : 0 < h) (hAh : Real.pi < A * h) (t₀ t : ℝ) :
    ∃ F : ℝ → ℂ, MemLp F 2 volume ∧ (∀ ξ, A ≤ |ξ| → F ξ = 0) ∧
      (∀ k : ℤ, pwSource F (t₀ + k * h) = 0) ∧ pwDeriv F t ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * Real.pi / h := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcA : c < 2 * A := by rw [hc, div_lt_iff₀ hh]; linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = -A + (2 * A - c) / 8 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -A + 3 * (2 * A - c) / 8 := ⟨_, rfl⟩
  have hαβ : α < β := by rw [hα, hβ]; linarith
  have hβc : β < -(c / 2) := by rw [hβ]; linarith
  have hαA : -A < α := by rw [hα]; linarith
  have hβA : β + c < A := by rw [hβ]; linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = t - t₀ := ⟨_, rfl⟩
  have hψ0 : ∀ ξ, ξ ∉ Ioo α β → nyquistBump τ c α β ξ = 0 := fun ξ hξ => indicator_of_notMem hξ _
  have hmp := measurePreserving_sub_right (volume : Measure ℝ) c
  have hψ2 := memLp_nyquistBump τ c α β
  refine ⟨nyquistDensity t₀ τ c α β, ?_, ?_, ?_, ?_⟩
  · -- `L²`
    have hg : MemLp (fun ξ => ‖nyquistBump τ c α β ξ‖ + ‖nyquistBump τ c α β (ξ - c)‖) 2 volume :=
      hψ2.norm.add (hψ2.comp_measurePreserving hmp).norm
    refine hg.of_le ((hψ2.1.sub (hψ2.1.comp_measurePreserving hmp)).mul
      (by fun_prop : Continuous fun ξ : ℝ =>
        exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    unfold nyquistDensity
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_sub_le _ _
  · -- aperture `A`
    intro ξ hξ
    unfold nyquistDensity
    have h1 : ξ ∉ Ioo α β := fun hm => by
      have : |ξ| < A := abs_lt.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
      linarith
    have h2 : ξ - c ∉ Ioo α β := fun hm => by
      have : |ξ| < A := abs_lt.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
      linarith
    rw [hψ0 ξ h1, hψ0 (ξ - c) h2, sub_zero, zero_mul]
  · -- the companion values vanish: `e^{ikh(η + c)} = e^{ikhη}`
    intro k
    set E : ℝ → ℂ := fun ξ => exp ((((k : ℝ) * h * ξ : ℝ) : ℂ) * I) with hE
    have hEc : Continuous E := by simp only [hE]; fun_prop
    have hper : ∀ η : ℝ, E (η + c) = E η := by
      intro η
      have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have e : ((((k : ℝ) * h * (η + c) : ℝ) : ℂ) * I) =
          ((((k : ℝ) * h * η : ℝ) : ℂ) * I) + (k : ℂ) * (2 * Real.pi * I) := by
        rw [hc]; push_cast; field_simp
      simp only [hE]
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hpt : ∀ ξ : ℝ, nyquistDensity t₀ τ c α β ξ * exp ((((t₀ + k * h) * ξ : ℝ) : ℂ) * I) =
        E ξ * nyquistBump τ c α β ξ - E ξ * nyquistBump τ c α β (ξ - c) := by
      intro ξ
      unfold nyquistDensity
      simp only [hE]
      rw [mul_assoc, ← Complex.exp_add]
      have e : (((-(t₀ * ξ) : ℝ) : ℂ) * I) + ((((t₀ + k * h) * ξ : ℝ) : ℂ) * I) =
          ((((k : ℝ) * h * ξ : ℝ) : ℂ) * I) := by push_cast; ring
      rw [e]
      ring
    obtain ⟨hi2, hshift⟩ := integral_mul_nyquistBump_sub hEc τ c α β
    unfold pwSource
    simp_rw [hpt]
    rw [integral_sub (integrable_mul_nyquistBump hEc τ c α β) hi2, hshift]
    simp_rw [hper]
    exact sub_self _
  · -- `f'(t) = ∫_{(α, β)} |κ|² > 0`
    set W := nyquistWave τ
    have hWc : Continuous W := continuous_nyquistWave τ
    have hpt : ∀ ξ : ℝ, ((ξ : ℂ) * I) * nyquistDensity t₀ τ c α β ξ *
        exp (((t * ξ : ℝ) : ℂ) * I) =
        W ξ * nyquistBump τ c α β ξ - W ξ * nyquistBump τ c α β (ξ - c) := by
      intro ξ
      unfold nyquistDensity
      simp only [W, nyquistWave]
      have e : exp (((-(t₀ * ξ) : ℝ) : ℂ) * I) * exp (((t * ξ : ℝ) : ℂ) * I) =
          exp (((τ * ξ : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, hτ]; congr 1; push_cast; ring
      calc ((ξ : ℂ) * I) * ((nyquistBump τ c α β ξ - nyquistBump τ c α β (ξ - c)) *
            exp (((-(t₀ * ξ) : ℝ) : ℂ) * I)) * exp (((t * ξ : ℝ) : ℂ) * I)
          = ((ξ : ℂ) * I) * (exp (((-(t₀ * ξ) : ℝ) : ℂ) * I) * exp (((t * ξ : ℝ) : ℂ) * I)) *
              (nyquistBump τ c α β ξ - nyquistBump τ c α β (ξ - c)) := by ring
        _ = _ := by rw [e]; ring
    obtain ⟨hi2, hshift⟩ := integral_mul_nyquistBump_sub hWc τ c α β
    have hκ : ∀ η : ℝ, (W η - W (η + c)) * nyquistBump τ c α β η =
        (Ioo α β).indicator (fun η => ((‖nyquistDefect τ c η‖ ^ 2 : ℝ) : ℂ)) η := by
      intro η
      unfold nyquistBump
      by_cases hη : η ∈ Ioo α β
      · rw [indicator_of_mem hη, indicator_of_mem hη,
          show W η - W (η + c) = nyquistDefect τ c η from rfl, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      · rw [indicator_of_notMem hη, indicator_of_notMem hη, mul_zero]
    have hD : pwDeriv (nyquistDensity t₀ τ c α β) t =
        ((∫ η in Ioo α β, ‖nyquistDefect τ c η‖ ^ 2 : ℝ) : ℂ) := by
      unfold pwDeriv
      simp_rw [hpt]
      rw [integral_sub (integrable_mul_nyquistBump hWc τ c α β) hi2, hshift,
        ← integral_sub (integrable_mul_nyquistBump hWc τ c α β)
          (integrable_mul_nyquistBump (p := fun η => W (η + c))
            (hWc.comp (continuous_id.add continuous_const)) τ c α β)]
      simp_rw [← sub_mul, hκ]
      rw [integral_indicator measurableSet_Ioo, integral_complex_ofReal]
    have hpos : 0 < ∫ η in Ioo α β, ‖nyquistDefect τ c η‖ ^ 2 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hαβ.le]
      have hκc := continuous_nyquistDefect τ c
      exact intervalIntegral.intervalIntegral_pos_of_pos_on
        ((by fun_prop : Continuous fun x => ‖nyquistDefect τ c x‖ ^ 2).intervalIntegrable α β)
        (fun η hη => pow_pos (norm_nyquistDefect_pos hc0 (lt_trans hη.2 hβc)) 2) hαβ
    rw [hD]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
