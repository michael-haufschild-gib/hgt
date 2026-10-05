import GaloisForLFunctions.RHTower.ZetaFractionalPartGramCriterion
import GaloisForLFunctions.RHTower.BaezDuarteDistance
import GaloisForLFunctions.RHTower.WeilLagFunctionOneSided
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality

/-!
# The Báez--Duarte distance on the critical line

In the Nyman--Beurling carrier `L²((1,∞), du)` the target is `1/u` and the generator for
`θ = 1/n` is `({u/n} - {u}/n)/u`.  The substitution `u = e^v` (with the factor `e^{v/2}`) is an
isometry onto functions on `v > 0`: the target becomes `e^{-v/2}` and the generator becomes
`φ_n - φ_1/n` with `φ_n(v) = e^{-v/2}{e^v/n}`.  Each generator vanishes on `v < 0`, where
`{e^v/n} = e^v/n` and `{e^v} = e^v`, so the residual extends by zero to the whole line.

Its Fourier transform at `t/2π` is the Mellin transform on `Re s = ½`: the target gives `1/s`,
the generators give `-(ζ(s)/s)(n^{-s} - 1/n)`.  Plancherel then yields, for finitely many real
coefficients,

`‖bdTarget - Σ c_n bdGen(1/n)‖² = (1/2π) ∫ |1 + ζ(s)P_c(s)|² dt/(¼ + t²)`,
`P_c(s) = Σ c_n(n^{-s} - 1/n)`.

This identifies the discrete Báez--Duarte distances with a weighted critical-line mean square, the
form in which the hard direction RH ⇒ `d_N → 0` is proved.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## The pulled-back residual -/

/-- The pulled target `e^{-v/2} 1_{v ≥ 0}` (the image of `1/u` on `u > 1` under `u = e^v`). -/
def bdTargetLogPull (v : ℝ) : ℂ :=
  Set.indicator (Ici 0) (fun w : ℝ => ((Real.exp (-(w / 2)) : ℝ) : ℂ)) v

/-- The pulled generator `φ_n - φ_1/n` (the image of `ρ_{1/n}`). -/
def bdGenLogPull (n : ℕ) (v : ℝ) : ℂ :=
  fractLogPullDilate n v - (n : ℂ)⁻¹ * fractLogPullDilate 1 v

/-- The pulled residual `e^{-v/2}1_{v ≥ 0} - Σ c_n (φ_n - φ_1/n)`. -/
def bdResidualLogPull (S : Finset ℕ) (c : ℕ → ℝ) (v : ℝ) : ℂ :=
  bdTargetLogPull v - ∑ n ∈ S, (c n : ℂ) * bdGenLogPull n v

/-- The Dirichlet polynomial `P_c(s) = Σ c_n (n^{-s} - 1/n)`. -/
def bdMollPoly (S : Finset ℕ) (c : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (c n : ℂ) * ((n : ℂ) ^ (-s) - (n : ℂ)⁻¹)

theorem norm_bdTargetLogPull_le (v : ℝ) : ‖bdTargetLogPull v‖ ≤ Real.exp (-(1 / 2) * |v|) := by
  unfold bdTargetLogPull
  by_cases hv : v ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (show (0 : ℝ) ≤ v from hv)]
    ring_nf; exact le_rfl
  · rw [indicator_of_notMem hv, norm_zero]; exact (Real.exp_pos _).le

theorem measurable_bdTargetLogPull : Measurable bdTargetLogPull :=
  (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_id.div_const 2).neg)).indicator measurableSet_Ici

theorem integrable_bdTargetLogPull : Integrable bdTargetLogPull :=
  Integrable.mono' integrable_exp_neg_half_mul_abs measurable_bdTargetLogPull.aestronglyMeasurable
    (Eventually.of_forall norm_bdTargetLogPull_le)

/-- The generators vanish on `v < 0`: there `{e^v/n} = e^v/n` and `{e^v} = e^v`. -/
theorem bdGenLogPull_of_neg {n : ℕ} (hn : 1 ≤ n) {v : ℝ} (hv : v < 0) : bdGenLogPull n v = 0 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp v < 1 := Real.exp_lt_one_iff.mpr hv
  have he0 := Real.exp_pos v
  have hf1 : Int.fract (Real.exp v / (1 : ℕ)) = Real.exp v := by
    rw [Nat.cast_one, div_one, Int.fract_eq_self.mpr ⟨he0.le, he⟩]
  have hfn : Int.fract (Real.exp v / n) = Real.exp v / n := by
    rw [Int.fract_eq_self.mpr ⟨by positivity, (div_le_self he0.le hn').trans_lt he⟩]
  unfold bdGenLogPull fractLogPullDilate
  rw [hf1, hfn]
  push_cast
  field_simp
  ring

theorem norm_bdGenLogPull_le {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    ‖bdGenLogPull n v‖ ≤ 2 * Real.exp (-(1 / 2) * |v|) := by
  unfold bdGenLogPull
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := norm_fractLogPullDilate_le hn v
  have h2 := norm_fractLogPullDilate_le le_rfl v
  have h3 : ‖(n : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]; exact inv_le_one_of_one_le₀ hn'
  calc ‖fractLogPullDilate n v - (n : ℂ)⁻¹ * fractLogPullDilate 1 v‖
      ≤ ‖fractLogPullDilate n v‖ + ‖(n : ℂ)⁻¹‖ * ‖fractLogPullDilate 1 v‖ :=
        (norm_sub_le _ _).trans (by rw [norm_mul])
    _ ≤ Real.exp (-(1 / 2) * |v|) + 1 * Real.exp (-(1 / 2) * |v|) := by gcongr
    _ = 2 * Real.exp (-(1 / 2) * |v|) := by ring

theorem integrable_bdGenLogPull {n : ℕ} (hn : 1 ≤ n) : Integrable (bdGenLogPull n) :=
  (integrable_fractLogPullDilate hn).sub ((integrable_fractLogPullDilate le_rfl).const_mul _)

/-! ## Fourier transforms -/

theorem integrable_fourierChar_smul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun v : ℝ => Real.fourierChar (-(v * ξ)) • f v) :=
  Integrable.mono' hf.norm
    (((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
      hf.aestronglyMeasurable) (Eventually.of_forall fun v => by rw [Circle.norm_smul])

theorem fourier_sub_of_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun v => f v - g v) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq, ← integral_sub
    (integrable_fourierChar_smul hf ξ) (integrable_fourierChar_smul hg ξ)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_sub]

theorem fourier_const_mul_fun (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun v => c * f v) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

theorem fourier_finsetSum_of_integrable {ι : Type*} (S : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ S, Integrable (g i)) (ξ : ℝ) :
    𝓕 (fun v => ∑ i ∈ S, g i v) ξ = ∑ i ∈ S, 𝓕 (g i) ξ := by
  rw [Real.fourier_real_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ fun i hi => integrable_fourierChar_smul (hg i hi) ξ]
  exact Finset.sum_congr rfl fun i _ => (Real.fourier_real_eq _ _).symm

/-- `𝓕(e^{-v/2}1_{v≥0})(t/2π) = 1/(½ + it)`. -/
theorem fourier_bdTargetLogPull (t : ℝ) :
    𝓕 bdTargetLogPull (t / (2 * π)) = 1 / (1 / 2 + t * I) := by
  rw [Real.fourier_real_eq]
  have hpt : (fun v : ℝ => Real.fourierChar (-(v * (t / (2 * π)))) • bdTargetLogPull v) =
      Set.indicator (Ici 0) (fun v : ℝ => Complex.exp (-(1 / 2 + t * I) * (v : ℂ))) := by
    funext v
    unfold bdTargetLogPull
    by_cases hv : v ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem hv, indicator_of_mem hv, Circle.smul_def, Real.fourierChar_apply,
        smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    · rw [indicator_of_notMem hv, indicator_of_notMem hv, smul_zero]
  rw [hpt, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_cexp_neg_mul_Ioi (by simp)]

/-- `𝓕(φ_n - φ_1/n)(t/2π) = -(ζ(s)/s)(n^{-s} - 1/n)`. -/
theorem fourier_bdGenLogPull {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    𝓕 (bdGenLogPull n) (t / (2 * π)) =
      -(riemannZeta (1 / 2 + t * I) / (1 / 2 + t * I)) *
        ((n : ℂ) ^ (-(1 / 2 + t * I)) - (n : ℂ)⁻¹) := by
  have h := fourier_sub_of_integrable (integrable_fractLogPullDilate hn)
    ((integrable_fractLogPullDilate le_rfl).const_mul ((n : ℂ)⁻¹)) (t / (2 * π))
  have hfun : (fun v => fractLogPullDilate n v - (n : ℂ)⁻¹ * fractLogPullDilate 1 v) =
      bdGenLogPull n := rfl
  rw [hfun] at h
  rw [h, fourier_const_mul_fun, fourier_fractLogPullDilate hn, fourier_fractLogPullDilate le_rfl,
    Nat.cast_one, Complex.one_cpow]
  ring

/-- **The Fourier transform of the residual.**
`𝓕(target - Σ c_n gen_n)(t/2π) = (1 + ζ(s)P_c(s))/s`, `s = ½ + it`. -/
theorem fourier_bdResidualLogPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) (t : ℝ) :
    𝓕 (bdResidualLogPull S c) (t / (2 * π)) =
      (1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)) / (1 / 2 + t * I) := by
  have hsum : Integrable (fun v => ∑ n ∈ S, (c n : ℂ) * bdGenLogPull n v) :=
    integrable_finsetSum _ fun n hn => (integrable_bdGenLogPull (hS n hn)).const_mul _
  have h := fourier_sub_of_integrable integrable_bdTargetLogPull hsum (t / (2 * π))
  have hfun : (fun v => bdTargetLogPull v - ∑ n ∈ S, (c n : ℂ) * bdGenLogPull n v) =
      bdResidualLogPull S c := rfl
  rw [hfun] at h
  rw [h, fourier_bdTargetLogPull, fourier_finsetSum_of_integrable S
    (fun n hn => (integrable_bdGenLogPull (hS n hn)).const_mul _)]
  simp_rw [fourier_const_mul_fun]
  rw [Finset.sum_congr rfl fun n hn => by rw [fourier_bdGenLogPull (hS n hn)]]
  unfold bdMollPoly
  rw [Finset.mul_sum, add_div, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ## The carrier norm as a pulled integral -/

theorem norm_bdResidualLogPull_le {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) (v : ℝ) :
    ‖bdResidualLogPull S c v‖ ≤ (1 + 2 * ∑ n ∈ S, |c n|) * Real.exp (-(1 / 2) * |v|) := by
  unfold bdResidualLogPull
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_bdTargetLogPull_le v
  have h2 : ‖∑ n ∈ S, (c n : ℂ) * bdGenLogPull n v‖ ≤
      (2 * ∑ n ∈ S, |c n|) * Real.exp (-(1 / 2) * |v|) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_comm 2, mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_bdGenLogPull_le (hS n hn) v) (abs_nonneg _)
  linarith

theorem integrable_bdResidualLogPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    Integrable (bdResidualLogPull S c) :=
  integrable_bdTargetLogPull.sub
    (integrable_finsetSum _ fun n hn => (integrable_bdGenLogPull (hS n hn)).const_mul _)

theorem memLp_two_bdResidualLogPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    MemLp (bdResidualLogPull S c) 2 := by
  have hmeas := (integrable_bdResidualLogPull hS c).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  set C : ℝ := 1 + 2 * ∑ n ∈ S, |c n| with hC
  have hC0 : 0 ≤ C := by have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (c n); linarith
  refine Integrable.mono' (integrable_exp_neg_half_mul_abs.const_mul (C ^ 2))
    (hmeas.norm.pow 2) (Eventually.of_forall fun u => ?_)
  have h1 := norm_bdResidualLogPull_le hS c u
  have h2 : Real.exp (-(1 / 2) * |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg u; nlinarith)
  have h3 : 0 ≤ Real.exp (-(1 / 2) * |u|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖bdResidualLogPull S c u‖ ^ 2 ≤ (C * Real.exp (-(1 / 2) * |u|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * (Real.exp (-(1 / 2) * |u|) * Real.exp (-(1 / 2) * |u|)) := by ring
    _ ≤ C ^ 2 * (Real.exp (-(1 / 2) * |u|) * 1) := by gcongr
    _ = C ^ 2 * Real.exp (-(1 / 2) * |u|) := by ring

/-- The residual vanishes on `v < 0`. -/
theorem bdResidualLogPull_of_neg {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) {v : ℝ}
    (hv : v < 0) : bdResidualLogPull S c v = 0 := by
  unfold bdResidualLogPull bdTargetLogPull
  rw [indicator_of_notMem (show v ∉ Ici (0 : ℝ) from fun h => absurd (show (0:ℝ) ≤ v from h)
    (not_le.mpr hv)), zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun n hn => by rw [bdGenLogPull_of_neg (hS n hn) hv, mul_zero]

theorem exp_image_Ioi_zero_eq_Ioi_one : Real.exp '' Ioi 0 = Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Real.one_lt_exp_iff.mpr hx
  · intro hy
    have hy1 : (1 : ℝ) < y := hy
    exact ⟨Real.log y, Real.log_pos hy1, Real.exp_log (by linarith)⟩

/-- The pulled residual is `e^{v/2}` times the carrier residual at `u = e^v`. -/
theorem bdResidualLogPull_eq {S : Finset ℕ} (c : ℕ → ℝ) {v : ℝ} (hv : 0 < v) :
    bdResidualLogPull S c v = ((Real.exp (v / 2) : ℝ) : ℂ) *
      (bdTargetFun (Real.exp v) - ∑ n ∈ S, (c n : ℂ) * bdGenFun ((n : ℝ)⁻¹) (Real.exp v)) := by
  unfold bdResidualLogPull bdTargetLogPull bdGenLogPull fractLogPullDilate bdTargetFun bdGenFun
  rw [indicator_of_mem (show v ∈ Ici (0 : ℝ) from hv.le), mul_sub, Finset.mul_sum]
  have hh : Complex.exp (-((v : ℂ) / 2)) = Complex.exp ((v : ℂ) / 2) * (Complex.exp (v : ℂ))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; ring_nf
  congr 1
  · push_cast; rw [hh]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (n : ℝ)⁻¹ * Real.exp v = Real.exp v / n by ring]
    push_cast
    simp only [div_one]
    rw [hh]
    ring

/-- **The carrier norm as a pulled integral.**
`‖bdTarget - Σ c_n bdGen(1/n)‖² = ∫ |e^{-v/2}1_{v≥0} - Σ c_n(φ_n - φ_1/n)|²`. -/
theorem norm_sq_bdTarget_sub_sum_bdGen {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ) :
    ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2 =
      ∫ v : ℝ, ‖bdResidualLogPull S c v‖ ^ 2 := by
  set f : ℝ → ℂ := fun u => bdTargetFun u - ∑ n ∈ S, (c n : ℂ) * bdGenFun ((n : ℝ)⁻¹) u
    with hf
  have hae : ((bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹) : BDCarrier) : ℝ → ℂ)
      =ᵐ[bdMeasure] f := by
    have h1 := Lp.coeFn_sub bdTarget (∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹))
    have h2 := Lp.coeFn_finsetSum S (fun n => (c n : ℂ) • bdGen ((n : ℝ)⁻¹))
    have h3 : ∀ n ∈ S, ((((c n : ℂ) • bdGen ((n : ℝ)⁻¹)) : BDCarrier) : ℝ → ℂ)
        =ᵐ[bdMeasure] fun u => (c n : ℂ) * bdGenFun ((n : ℝ)⁻¹) u := by
      intro n _
      filter_upwards [Lp.coeFn_smul (c n : ℂ) (bdGen ((n : ℝ)⁻¹)),
        (memLp_bdGenFun ((n : ℝ)⁻¹)).coeFn_toLp] with u hu hu'
      rw [hu, Pi.smul_apply, smul_eq_mul, bdGen, hu']
    have h3' : ∀ᵐ u ∂bdMeasure, ∀ n ∈ S, ((((c n : ℂ) • bdGen ((n : ℝ)⁻¹)) : BDCarrier) :
        ℝ → ℂ) u = (c n : ℂ) * bdGenFun ((n : ℝ)⁻¹) u :=
      (Filter.eventually_all_finset S).mpr fun n hn => h3 n hn
    filter_upwards [h1, h2, h3', memLp_bdTargetFun.coeFn_toLp] with u hu1 hu2 hu3 hu4
    rw [hu1, Pi.sub_apply, hu2, Finset.sum_apply]
    simp only [hf]
    congr 1
    exact Finset.sum_congr rfl fun n hn => hu3 n hn
  rw [GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral,
    integral_congr_ae (hae.mono fun u hu => by rw [hu])]
  show ∫ u in Ioi (1 : ℝ), ‖f u‖ ^ 2 = _
  rw [← exp_image_Ioi_zero_eq_Ioi_one, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  have hpt : ∀ v ∈ Ioi (0 : ℝ), |Real.exp v| • ‖f (Real.exp v)‖ ^ 2 =
      ‖bdResidualLogPull S c v‖ ^ 2 := by
    intro v hv
    rw [bdResidualLogPull_eq c hv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), smul_eq_mul, mul_pow,
      ← Real.exp_nat_mul]
    simp only [hf]
    congr 2
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  have h0 : ∀ᵐ v : ℝ ∂volume, v ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h0] with v hv hvS
  have hv' : v < 0 := lt_of_le_of_ne (not_lt.mp hvS) hv
  rw [bdResidualLogPull_of_neg hS c hv', norm_zero]
  norm_num

/-! ## The Plancherel distance formula -/

/-- **The Báez--Duarte distance on the critical line.**  For finitely many coefficients `c_n`
(`n ≥ 1`),
`‖bdTarget - Σ c_n bdGen(1/n)‖² = (1/2π) ∫ |1 + ζ(s)P_c(s)|² dt/(¼ + t²)`, `s = ½ + it`,
`P_c(s) = Σ c_n(n^{-s} - 1/n)`. -/
theorem integrable_and_norm_sq_bdTarget_sub_sum_bdGen {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℕ → ℝ) :
    Integrable (fun t : ℝ => ‖1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖ ^ 2
        / (1 / 4 + t ^ 2)) ∧
      ‖bdTarget - ∑ n ∈ S, (c n : ℂ) • bdGen ((n : ℝ)⁻¹)‖ ^ 2 =
        (2 * π)⁻¹ * ∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖ ^ 2
          / (1 / 4 + t ^ 2) := by
  have hπ : 0 < 2 * π := by positivity
  set φ := bdResidualLogPull S c with hφ
  have hint := integrable_bdResidualLogPull hS c
  have hL2 := memLp_two_bdResidualLogPull hS c
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier hint hL2
  have hFint : Integrable (fun ξ : ℝ => ‖𝓕 φ ξ‖ ^ 2) := by
    by_cases h0 : ∫ u : ℝ, ‖φ u‖ ^ 2 = 0
    · have hae : φ =ᵐ[volume] 0 := by
        have hnn : 0 ≤ᵐ[volume] fun u => ‖φ u‖ ^ 2 :=
          Eventually.of_forall fun u => by positivity
        have hi : Integrable (fun u => ‖φ u‖ ^ 2) := by
          rw [← memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable]
          exact hL2
        have := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp h0
        exact this.mono fun u hu => by simpa using hu
      have hF0 : ∀ ξ, 𝓕 φ ξ = 0 := by
        intro ξ
        rw [Real.fourier_real_eq]
        have h0' : (fun v : ℝ => Real.fourierChar (-(v * ξ)) • φ v)
            =ᵐ[volume] fun _ => (0 : ℂ) := hae.mono fun u hu => by simp [hu]
        rw [integral_congr_ae h0', integral_zero]
      simp_rw [hF0]
      simp
    · by_contra hni
      rw [integral_undef hni] at hP
      exact h0 hP.symm
  have hpt : ∀ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) * bdMollPoly S c (1 / 2 + t * I)‖ ^ 2
      / (1 / 4 + t ^ 2) = ‖𝓕 φ (t / (2 * π))‖ ^ 2 := by
    intro t
    rw [hφ, fourier_bdResidualLogPull hS, norm_div, div_pow, norm_half_add_mul_I,
      Real.sq_sqrt (by positivity)]
  simp_rw [hpt]
  refine ⟨hFint.comp_div hπ.ne', ?_⟩
  rw [norm_sq_bdTarget_sub_sum_bdGen hS c, ← hφ,
    Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 φ ξ‖ ^ 2) (2 * π), hP,
    abs_of_pos hπ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]

end

end RHTower
