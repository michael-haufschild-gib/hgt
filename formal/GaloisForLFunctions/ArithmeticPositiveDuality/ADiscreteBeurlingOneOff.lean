import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries

/-!
# A discrete Beurling one-off

Let `w ≥ 0` be the logarithmic prime density of the continuous one-off `overRegularZeta`
(`1/3 < μ < 1/2`, `0 < ν < 3μ − 1`), `W(x) = ∫_{(0,x]} w`, and let `t_k` be the point with
`W(t_k) = k + 1`. The discrete primes `p_k = e^{t_k}` follow the continuous ones to within one:
`#{k : t_k ≤ x} = ⌊W(x)⌋` (`atomCount_eq`).

* **Laplace transforms of counting functions** (`tsum_cexp_atoms`, `integral_cexp_density`):
  `Σ_k e^{-s t_k} = s ∫ e^{-sx} N(x) dx` and `∫ e^{-su} w(u) du = s ∫ e^{-sx} W(x) dx`, by Fubini.
* **Continuation** (`discreteZeta_eq_tprod`, `discreteZeta_eq_continuation`,
  `differentiableOn_continuation`). With `Λ(s) = ∫ e^{-sx}(N − W)(x) dx`, holomorphic on
  `Re s > 0` because `|N − W| ≤ 1`, and the prime-power remainder
  `R(s) = Σ_k (−log(1 − e^{-st_k}) − e^{-st_k})`, holomorphic on `Re s > 1/2`, the Euler product
  `Π_k (1 − p_k^{-s})^{-1}` equals `ζ_c(s) e^{sΛ(s) + R(s)}` on `Re s > 1`.
* **One-off** (`continuation_eq_zero_iff`, `zeros_right_of_eq_pair`). On `Re s > 1/2`, `s ≠ 1`,
  the continuation vanishes exactly at `(1 − μ) ± iγ`: finitely many zeros right of `1/2 + h` for
  `h < 1/2 − μ`, and at least one.
* **No functional-equation defect** (`not_summable_exp_neg_atom`,
  `tendsto_norm_continuation_half`). The prime squares give `R(σ) ≥ ½ Σ_k p_k^{-2σ} → ∞` as
  `σ → 1/2⁺`, because `Σ 1/p_k = ∞`. So the continuation blows up at `s = 1/2` and has no
  continuous extension to the critical line, where a functional-equation defect is measured.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ### Laplace transforms of counting functions -/

theorem integral_Ici_cexp_neg {s : ℂ} (hs : 0 < s.re) (u : ℝ) :
    ∫ x in Ici u, cexp (-(s * x)) = cexp (-(s * u)) / s := by
  have h := integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) u
  rw [integral_Ici_eq_integral_Ioi]
  simp only [neg_mul] at h
  rw [h, neg_div_neg_eq]

theorem integrableOn_Ici_cexp_neg {s : ℂ} (hs : 0 < s.re) (u : ℝ) :
    IntegrableOn (fun x : ℝ => cexp (-(s * x))) (Ici u) := by
  have h := integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) u
  simp only [neg_mul] at h
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h

theorem integral_Ici_exp_neg {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    ∫ x in Ici u, Real.exp (-(σ * x)) = Real.exp (-(σ * u)) / σ := by
  have h := integral_exp_mul_Ioi (a := -σ) (by linarith) u
  rw [integral_Ici_eq_integral_Ioi]
  simp only [neg_mul] at h
  rw [h, neg_div_neg_eq]

theorem norm_cexp_neg_mul (s : ℂ) (x : ℝ) : ‖cexp (-(s * x))‖ = Real.exp (-(s.re * x)) := by
  rw [Complex.norm_exp]
  simp

/-- An atom `u > 0` as a Laplace transform: `e^{-su} = s ∫_{x > 0} 1_{x ≥ u} e^{-sx} dx`. -/
theorem setIntegral_indicator_Ici {s : ℂ} (hs : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    ∫ x in Ioi (0 : ℝ), (Ici u).indicator (fun x : ℝ => cexp (-(s * x))) x =
      cexp (-(s * u)) / s := by
  rw [setIntegral_indicator measurableSet_Ici, inter_eq_right.mpr (Ici_subset_Ioi.mpr hu),
    integral_Ici_cexp_neg hs]

theorem setIntegral_norm_indicator_Ici {s : ℂ} (hs : 0 < s.re) {u : ℝ} (hu : 0 < u) :
    ∫ x in Ioi (0 : ℝ), ‖(Ici u).indicator (fun x : ℝ => cexp (-(s * x))) x‖ =
      Real.exp (-(s.re * u)) / s.re := by
  simp_rw [norm_indicator_eq_indicator_norm, norm_cexp_neg_mul]
  rw [setIntegral_indicator measurableSet_Ici, inter_eq_right.mpr (Ici_subset_Ioi.mpr hu),
    integral_Ici_exp_neg hs]

/-- The counting function `#{k : t_k ≤ x}` of a sequence of atoms. -/
def atomCount (t : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, if t k ≤ x then (1 : ℝ) else 0

/-- **The discrete Laplace transform** `Σ_k e^{-s t_k} = s ∫_{x>0} e^{-sx} N(x) dx`. -/
theorem tsum_cexp_atoms {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) {s : ℂ} (hs : 0 < s.re)
    (hsum : Summable fun k => Real.exp (-(s.re * t k))) :
    ∑' k, cexp (-(s * t k)) = s * ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (atomCount t x : ℂ) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  set F : ℕ → ℝ → ℂ := fun k => (Ici (t k)).indicator (fun x : ℝ => cexp (-(s * x))) with hF
  have hF_int : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    ((integrableOn_Ici_cexp_neg hs (t k)).integrable_indicator measurableSet_Ici).restrict
  have hF_sum : Summable fun k => ∫ x in Ioi (0 : ℝ), ‖F k x‖ := by
    simp_rw [hF, setIntegral_norm_indicator_Ici hs (ht _)]
    exact hsum.div_const _
  have key := integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hpt : ∀ x, ∑' k, F k x = cexp (-(s * x)) * (atomCount t x : ℂ) := by
    intro x
    simp only [hF, Set.indicator_apply, mem_Ici, atomCount]
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    congr 1
    funext k
    split_ifs <;> simp
  calc ∑' k, cexp (-(s * t k)) = ∑' k, s * ∫ x in Ioi (0 : ℝ), F k x := by
        congr 1
        funext k
        rw [hF, setIntegral_indicator_Ici hs (ht k)]
        field_simp
    _ = s * ∑' k, ∫ x in Ioi (0 : ℝ), F k x := tsum_mul_left
    _ = s * ∫ x in Ioi (0 : ℝ), ∑' k, F k x := by rw [key]
    _ = _ := by simp_rw [hpt]

/-- The distribution function `W(x) = ∫_{(0,x]} w`. -/
def distribution (w : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in Ioc 0 x, w u

/-- **The continuous Laplace transform** `∫_{u>0} e^{-su} w(u) du = s ∫_{x>0} e^{-sx} W(x) dx`,
with `x ↦ e^{-sx} W(x)` integrable. -/
theorem integral_cexp_density {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ u, 0 < u → 0 ≤ w u)
    {s : ℂ} (hs : 0 < s.re)
    (hint : IntegrableOn (fun u => Real.exp (-(s.re * u)) * w u) (Ioi 0)) :
    IntegrableOn (fun x : ℝ => cexp (-(s * x)) * (distribution w x : ℂ)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (w u : ℂ) =
        s * ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (distribution w x : ℂ) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set G : ℝ → ℝ → ℂ := fun u x =>
    (w u : ℂ) * (Ici u).indicator (fun x : ℝ => cexp (-(s * x))) x with hG
  have hGm : AEStronglyMeasurable (Function.uncurry G) (μ.prod μ) := by
    have h1 : Measurable fun p : ℝ × ℝ => (w p.1 : ℂ) :=
      Complex.measurable_ofReal.comp (hwm.comp measurable_fst)
    have h2 : Measurable fun p : ℝ × ℝ =>
        ({q : ℝ × ℝ | q.1 ≤ q.2}).indicator (fun q : ℝ × ℝ => cexp (-(s * q.2))) p :=
      (by fun_prop : Measurable fun q : ℝ × ℝ => cexp (-(s * q.2))).indicator
        (measurableSet_le measurable_fst measurable_snd)
    refine (h1.mul h2).aestronglyMeasurable.congr (Eventually.of_forall fun p => ?_)
    simp only [hG, Function.uncurry, Set.indicator_apply, mem_Ici, mem_setOf_eq, Pi.mul_apply]
  have hinner_norm : ∀ u, 0 < u → ∫ x, ‖G u x‖ ∂μ = w u * (Real.exp (-(s.re * u)) / s.re) := by
    intro u hu
    simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 u hu)]
    rw [integral_const_mul, setIntegral_norm_indicator_Ici hs hu]
  have hGint : Integrable (Function.uncurry G) (μ.prod μ) := by
    rw [integrable_prod_iff hGm]
    refine ⟨Eventually.of_forall fun u => ?_, ?_⟩
    · show Integrable (fun x => G u x) μ
      exact (((integrableOn_Ici_cexp_neg hs u).integrable_indicator measurableSet_Ici).restrict
        ).const_mul _
    · have hbd : Integrable (fun u => w u * (Real.exp (-(s.re * u)) / s.re)) μ := by
        have := hint.div_const s.re
        refine this.congr (Eventually.of_forall fun u => ?_)
        simp only
        ring
      refine hbd.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (hinner_norm u hu).symm
  have hswap := integral_integral_swap hGint
  have hleft : ∀ u, 0 < u → ∫ x, G u x ∂μ = (w u : ℂ) * (cexp (-(s * u)) / s) := by
    intro u hu
    simp only [hG]
    rw [integral_const_mul, setIntegral_indicator_Ici hs hu]
  have hright : ∀ x, 0 < x → ∫ u, G u x ∂μ = cexp (-(s * x)) * (distribution w x : ℂ) := by
    intro x hx
    have hpt : ∀ u, G u x = (Iic x).indicator (fun u => cexp (-(s * x)) * (w u : ℂ)) u := by
      intro u
      simp only [hG, Set.indicator_apply, mem_Ici, mem_Iic]
      split_ifs <;> ring
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Iic, show Ioi (0 : ℝ) ∩ Iic x = Ioc 0 x by
      ext; simp [and_comm], integral_const_mul, distribution, integral_complex_ofReal]
  have hR : IntegrableOn (fun x : ℝ => cexp (-(s * x)) * (distribution w x : ℂ)) (Ioi 0) := by
    have h := hGint.integral_prod_right
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hright x hx
  refine ⟨hR, ?_⟩
  have hL : ∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (w u : ℂ) = s * ∫ u, ∫ x, G u x ∂μ ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [hleft u hu]
    field_simp
  rw [hL, hswap]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hright x hx

/-! ### Holomorphy -/

/-- The Laplace transform of a bounded measurable function on `(0, ∞)`. -/
def boundedLaplace (E : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (E x : ℂ)

/-- **The Laplace transform of a function bounded by `1` is holomorphic on `Re s > 0`.** Shift by
`ε = Re s/2` and use the half-line Laplace transform of the `L²` datum `E(x) e^{-εx}`. -/
theorem differentiableOn_boundedLaplace {E : ℝ → ℝ} (hEm : Measurable E) (hE : ∀ x, |E x| ≤ 1) :
    DifferentiableOn ℂ (boundedLaplace E) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  set ε : ℝ := s.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  set φ : ℝ → ℂ := fun x => (E x : ℂ) * expRay (ε : ℂ) x with hφ
  have hφL : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := by
    refine (memLp_two_expRay_restrict (w := (ε : ℂ)) (by simpa using hε0) 0).of_le ?_ ?_
    · exact ((Complex.measurable_ofReal.comp hEm).mul
        (continuous_expRay _).measurable).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      simp only [hφ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |E x| * ‖expRay (ε : ℂ) x‖ ≤ 1 * ‖expRay (ε : ℂ) x‖ :=
            mul_le_mul_of_nonneg_right (hE x) (norm_nonneg _)
        _ = ‖expRay (ε : ℂ) x‖ := one_mul _
  have heq : boundedLaplace E = laplaceRay φ ∘ fun z : ℂ => z - (ε : ℂ) := by
    funext z
    unfold boundedLaplace laplaceRay
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hφ, expRay]
    rw [mul_assoc, ← Complex.exp_add]
    rw [mul_comm]
    congr 2
    ring
  have hmem : s - (ε : ℂ) ∈ {w : ℂ | 0 < w.re} := by
    show 0 < (s - (ε : ℂ)).re
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hg : DifferentiableAt ℂ (laplaceRay φ) (s - (ε : ℂ)) :=
    (differentiableOn_laplaceRay hφL).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)
  have hf : DifferentiableAt ℂ (fun z : ℂ => z - (ε : ℂ)) s := differentiableAt_id.sub_const _
  have hd : DifferentiableAt ℂ (laplaceRay φ ∘ fun z : ℂ => z - (ε : ℂ)) s := hg.comp s hf
  rw [heq]
  exact hd.differentiableWithinAt

/-- The prime-power part `R(s) = Σ_k (−log(1 − e^{-st_k}) − e^{-st_k})` of the Euler product. -/
def primePowerRemainder (t : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' k, (-Complex.log (1 - cexp (-(s * t k))) - cexp (-(s * t k)))

theorem norm_primePowerTerm_le {t : ℝ} (ht : 0 < t) {σ₀ : ℝ} {z : ℂ}
    (hz : σ₀ ≤ z.re) {q : ℝ} (hq : Real.exp (-(σ₀ * t)) ≤ q) (hq1 : q < 1) :
    ‖-Complex.log (1 - cexp (-(z * t))) - cexp (-(z * t))‖ ≤
      Real.exp (-(2 * σ₀ * t)) * (1 - q)⁻¹ / 2 := by
  set x := cexp (-(z * t)) with hx
  have hxn : ‖x‖ = Real.exp (-(z.re * t)) := norm_cexp_neg_mul z t
  have hxle : ‖x‖ ≤ Real.exp (-(σ₀ * t)) := by
    rw [hxn]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hx1 : ‖-x‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le hx1
  rw [norm_neg] at h
  have h' : -Complex.log (1 - x) - x = -(Complex.log (1 + -x) - -x) := by
    rw [← sub_eq_add_neg]
    ring
  rw [h', norm_neg]
  refine h.trans ?_
  have hq0 : 0 < 1 - q := by linarith
  have hsq : ‖x‖ ^ 2 ≤ Real.exp (-(2 * σ₀ * t)) := by
    calc ‖x‖ ^ 2 ≤ Real.exp (-(σ₀ * t)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxle 2
      _ = Real.exp (-(2 * σ₀ * t)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hinv : (1 - ‖x‖)⁻¹ ≤ (1 - q)⁻¹ :=
    inv_anti₀ hq0 (by linarith)
  have hn1 : 0 ≤ (1 - ‖x‖)⁻¹ := inv_nonneg.mpr (by linarith)
  calc ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ / 2 ≤ Real.exp (-(2 * σ₀ * t)) * (1 - q)⁻¹ / 2 := by
        gcongr

/-- **The prime-power remainder is holomorphic on `Re s > 1/2`.** -/
theorem differentiableOn_primePowerRemainder {t : ℕ → ℝ} (ht : ∀ k, 0 < t k)
    (hmono : ∀ k, t 0 ≤ t k) (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) :
    DifferentiableOn ℂ (primePowerRemainder t) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  set σ₀ : ℝ := (1 / 2 + s.re) / 2 with hσ₀
  have hσ₀0 : 0 < σ₀ := by linarith
  set q : ℝ := Real.exp (-(σ₀ * t 0)) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := ht 0
    nlinarith
  set U : Set ℂ := {z : ℂ | σ₀ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by show σ₀ < s.re; linarith
  have hdiff : ∀ k, DifferentiableOn ℂ
      (fun z : ℂ => -Complex.log (1 - cexp (-(z * t k))) - cexp (-(z * t k))) U := by
    intro k z hz
    have hz' : σ₀ < z.re := hz
    have hre : 0 < (1 - cexp (-(z * t k))).re := by
      have h1 : (cexp (-(z * t k))).re ≤ ‖cexp (-(z * t k))‖ := Complex.re_le_norm _
      have h2 : ‖cexp (-(z * t k))‖ < 1 := by
        rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
        have := ht k
        nlinarith
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hexp : DifferentiableAt ℂ (fun z : ℂ => cexp (-(z * t k))) z := by fun_prop
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((differentiableAt_const _ |>.sub hexp).clog
      (Complex.mem_slitPlane_iff.mpr (Or.inl hre))).neg.sub hexp
  have hbound : ∀ k (z : ℂ), z ∈ U →
      ‖-Complex.log (1 - cexp (-(z * t k))) - cexp (-(z * t k))‖ ≤
        Real.exp (-(2 * σ₀ * t k)) * (1 - q)⁻¹ / 2 := by
    intro k z hz
    have hz' : σ₀ < z.re := hz
    refine norm_primePowerTerm_le (ht k) hz'.le ?_ hq1
    rw [hq]
    exact Real.exp_le_exp.mpr (by nlinarith [hmono k])
  have hsumU : Summable fun k => Real.exp (-(2 * σ₀ * t k)) * (1 - q)⁻¹ / 2 := by
    have h := hsum (2 * σ₀) (by linarith)
    exact (h.mul_right _).div_const _
  have hD := differentiableOn_tsum_of_summable_norm hsumU hdiff hUo hbound
  exact (hD.differentiableAt (hUo.mem_nhds hsU)).differentiableWithinAt

/-- The Euler logarithm converges absolutely on `Re s > 1`. -/
theorem summable_neg_log {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) (hmono : ∀ k, t 0 ≤ t k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k => cexp (-(s * t k))) ∧
      Summable (fun k => -Complex.log (1 - cexp (-(s * t k))) - cexp (-(s * t k))) := by
  have h1 : Summable fun k => cexp (-(s * t k)) := by
    refine Summable.of_norm ?_
    simp_rw [norm_cexp_neg_mul]
    exact hsum s.re hs
  set q : ℝ := Real.exp (-(s.re * t 0)) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := ht 0
    nlinarith
  refine ⟨h1, Summable.of_norm_bounded ((((hsum (2 * s.re) (by linarith)).mul_right
    ((1 - q)⁻¹)).div_const 2)) fun k => ?_⟩
  have hle : Real.exp (-(s.re * t k)) ≤ q := by
    rw [hq]
    exact Real.exp_le_exp.mpr (by nlinarith [hmono k])
  exact norm_primePowerTerm_le (ht k) le_rfl hle hq1

/-- **The Euler logarithm splits** into the prime sum and the prime-power remainder on `Re s > 1`. -/
theorem tsum_neg_log_eq {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) (hmono : ∀ k, t 0 ≤ t k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) {s : ℂ} (hs : 1 < s.re) :
    ∑' k, -Complex.log (1 - cexp (-(s * t k))) =
      ∑' k, cexp (-(s * t k)) + primePowerRemainder t s := by
  obtain ⟨h1, h2⟩ := summable_neg_log ht hmono hsum hs
  rw [primePowerRemainder, ← h1.tsum_add h2]
  congr 1
  funext k
  ring

/-! ### The prime density of the continuous one-off -/

open RHTower.BeurlingOverRegularIntegers

/-- The parameters of the continuous one-off. -/
structure Params where
  μ : ℝ
  ν : ℝ
  γ : ℝ
  hμ1 : 1 / 3 < μ
  hμ2 : μ < 1 / 2
  hν0 : 0 < ν
  hν : ν < 3 * μ - 1

namespace Params

variable (P : Params)

/-- The logarithmic prime density. -/
def w : ℝ → ℝ := primeDensity P.μ P.ν P.γ

theorem hlow : 0 ≤ 3 * P.μ - 1 - P.ν := by linarith [P.hν]
theorem hhigh : 0 ≤ 3 * P.μ - 1 + P.ν := by linarith [P.hν, P.hν0]
theorem h4 : 0 ≤ 4 * P.μ - 1 := by linarith [P.hμ1]

/-- The numerator as a sum of squares, `x = e^{μt}`, `y = e^{νt}`, `z = e^{-(3μ-1)t}`. -/
theorem primeNumerator_eq (μ ν γ t : ℝ) :
    primeNumerator μ ν γ t = Real.exp (-((3 * μ - 1) * t)) *
      (2 * Real.exp (μ * t) ^ 2 * (1 - Real.cos (γ * t)) +
        (Real.exp (ν * t) - 1) ^ 2 / Real.exp (ν * t) +
        (Real.exp (μ * t) - 1) ^ 3 * (Real.exp (μ * t) + 1) / Real.exp (μ * t)) := by
  have e1 : Real.exp t = Real.exp (-((3 * μ - 1) * t)) * Real.exp (μ * t) ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e2 : Real.exp ((1 - μ) * t) = Real.exp (-((3 * μ - 1) * t)) * Real.exp (μ * t) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e3 : Real.exp (-((3 * μ - 1 - ν) * t)) =
      Real.exp (-((3 * μ - 1) * t)) * Real.exp (ν * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e4 : Real.exp (-((3 * μ - 1 + ν) * t)) =
      Real.exp (-((3 * μ - 1) * t)) / Real.exp (ν * t) := by
    rw [← Real.exp_sub]; congr 1; ring
  have e5 : Real.exp (-((4 * μ - 1) * t)) =
      Real.exp (-((3 * μ - 1) * t)) / Real.exp (μ * t) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [primeNumerator, e1, e2, e3, e4, e5]
  have hx0 : 0 < Real.exp (μ * t) := Real.exp_pos _
  have hy0 : 0 < Real.exp (ν * t) := Real.exp_pos _
  field_simp
  ring

/-- The density is positive on `(0, ∞)`. -/
theorem w_pos {t : ℝ} (ht : 0 < t) : 0 < P.w t := by
  have hμ0 : 0 < P.μ := by linarith [P.hμ1]
  have hx1 : 1 < Real.exp (P.μ * t) := Real.one_lt_exp_iff.mpr (mul_pos hμ0 ht)
  have hx0 : 0 < Real.exp (P.μ * t) := Real.exp_pos _
  have hy0 : 0 < Real.exp (P.ν * t) := Real.exp_pos _
  have h1 : 0 ≤ 2 * Real.exp (P.μ * t) ^ 2 * (1 - Real.cos (P.γ * t)) :=
    mul_nonneg (by positivity) (by linarith [Real.cos_le_one (P.γ * t)])
  have h2 : 0 ≤ (Real.exp (P.ν * t) - 1) ^ 2 / Real.exp (P.ν * t) := by positivity
  have h3 : 0 < (Real.exp (P.μ * t) - 1) ^ 3 * (Real.exp (P.μ * t) + 1) / Real.exp (P.μ * t) :=
    div_pos (mul_pos (pow_pos (by linarith) 3) (by linarith)) hx0
  have hN : 0 < primeNumerator P.μ P.ν P.γ t := by
    rw [primeNumerator_eq]
    exact mul_pos (Real.exp_pos _) (by linarith)
  exact div_pos hN ht

/-- **Lower bound.** `w(t) ≥ c₀ e^t/t` for `t ≥ 1`, `c₀ = (1 − e^{-μ})³`. -/
theorem w_ge {t : ℝ} (ht : 1 ≤ t) :
    (1 - Real.exp (-P.μ)) ^ 3 * Real.exp t / t ≤ P.w t := by
  have hμ0 : 0 < P.μ := by linarith [P.hμ1]
  have ht0 : 0 < t := by linarith
  set x := Real.exp (P.μ * t) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hxμ : Real.exp P.μ ≤ x := Real.exp_le_exp.mpr (by nlinarith)
  have hc : 0 ≤ 1 - Real.exp (-P.μ) := by
    have := Real.exp_le_one_iff.mpr (by linarith : -P.μ ≤ 0)
    linarith
  have hlin : (1 - Real.exp (-P.μ)) * x ≤ x - 1 := by
    have h : Real.exp (-P.μ) * x ≥ 1 := by
      have : Real.exp (-P.μ) * Real.exp P.μ = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-P.μ)]
    nlinarith
  have hcube : (1 - Real.exp (-P.μ)) ^ 3 * x ^ 3 ≤ (x - 1) ^ 3 := by
    have := pow_le_pow_left₀ (mul_nonneg hc hx0.le) hlin 3
    rwa [mul_pow] at this
  have hz : Real.exp (-((3 * P.μ - 1) * t)) * x ^ 3 = Real.exp t := by
    rw [hx, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hthird : (x - 1) ^ 3 ≤ (x - 1) ^ 3 * (x + 1) / x := by
    rw [le_div_iff₀ hx0]
    have : 0 ≤ (x - 1) ^ 3 := pow_nonneg (by nlinarith [Real.one_le_exp (le_of_lt hμ0)]) 3
    nlinarith
  have h1 : 0 ≤ 2 * x ^ 2 * (1 - Real.cos (P.γ * t)) :=
    mul_nonneg (by positivity) (by linarith [Real.cos_le_one (P.γ * t)])
  have h2 : 0 ≤ (Real.exp (P.ν * t) - 1) ^ 2 / Real.exp (P.ν * t) := by positivity
  have hN : (1 - Real.exp (-P.μ)) ^ 3 * Real.exp t ≤ primeNumerator P.μ P.ν P.γ t := by
    rw [primeNumerator_eq, ← hx]
    have hz0 : 0 < Real.exp (-((3 * P.μ - 1) * t)) := Real.exp_pos _
    calc (1 - Real.exp (-P.μ)) ^ 3 * Real.exp t
        = Real.exp (-((3 * P.μ - 1) * t)) * ((1 - Real.exp (-P.μ)) ^ 3 * x ^ 3) := by
          rw [← hz]; ring
      _ ≤ Real.exp (-((3 * P.μ - 1) * t)) * (2 * x ^ 2 * (1 - Real.cos (P.γ * t)) +
          (Real.exp (P.ν * t) - 1) ^ 2 / Real.exp (P.ν * t) + (x - 1) ^ 3 * (x + 1) / x) := by
          gcongr
          linarith
  unfold w primeDensity
  exact div_le_div_of_nonneg_right hN ht0.le

theorem measurable_w : Measurable P.w := by
  unfold w primeDensity primeNumerator
  fun_prop

/-- The complex Laplace integrand is integrable on `(0, ∞)` for `Re s > 1`. -/
theorem integrableOn_cexp_mul_w {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (P.w t : ℂ)) (Ioi 0) := by
  have hb : 0 < (s - (1 - P.μ)).re := by
    simpa using re_sub_pos (a := 1 - P.μ) (by linarith [P.hμ1]) hs
  have h1 : 0 < (s - 1).re := by simpa using re_sub_pos (a := 1) le_rfl hs
  have hm : 0 < (s - (1 - P.μ) - P.γ * I).re := by simpa using hb
  have hp : 0 < (s - (1 - P.μ) + P.γ * I).re := by simpa using hb
  have hl : 0 < (s + (3 * P.μ - 1 - P.ν)).re := by
    simpa using re_add_pos (a := 3 * P.μ - 1 - P.ν) P.hlow hs
  have hh : 0 < (s + (3 * P.μ - 1 + P.ν)).re := by
    simpa using re_add_pos (a := 3 * P.μ - 1 + P.ν) P.hhigh hs
  have hq : 0 < (s + (4 * P.μ - 1)).re := by
    simpa using re_add_pos (a := 4 * P.μ - 1) P.h4 hs
  refine ((integrableOn_frullani h1 hm).add ((integrableOn_frullani hl hp).add
    (integrableOn_frullani hh hq))).congr_fun (fun t ht => ?_) measurableSet_Ioi
  exact (cexp_mul_primeDensity P.μ P.ν P.γ s ht).symm

/-- The real Laplace integrand `e^{-σu} w(u)` is integrable on `(0, ∞)` for `σ > 1`. -/
theorem integrableOn_exp_mul_w {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * P.w u) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => RCLike.re (cexp (-((σ : ℂ) * u)) * (P.w u : ℂ))) (Ioi 0) :=
    (P.integrableOn_cexp_mul_w (s := (σ : ℂ)) (by simpa using hσ)).re
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  show RCLike.re (cexp (-((σ : ℂ) * u)) * (P.w u : ℂ)) = _
  rw [RCLike.re_to_complex, show -((σ : ℂ) * (u : ℂ)) = ((-(σ * u) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ### The distribution function and the atoms -/

/-- The distribution function `W(x) = ∫_{(0,x]} w` of the continuous primes. -/
def W (x : ℝ) : ℝ := distribution P.w x

/-- `w` on `(0, ∞)`, zero elsewhere. -/
def wt : ℝ → ℝ := (Ioi (0 : ℝ)).indicator P.w

theorem integrableOn_w_Ioc (b : ℝ) : IntegrableOn P.w (Ioc 0 b) := by
  have h := (P.integrableOn_exp_mul_w (σ := 2) (by norm_num)).mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) b ⊆ Ioi 0)
  have hIcc : IntegrableOn (fun u => Real.exp (-(2 * u)) * P.w u) (Icc 0 b) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc h
  have hc : ContinuousOn (fun u : ℝ => Real.exp (2 * u)) (Icc 0 b) := by fun_prop
  have h2 := (hIcc.mul_continuousOn hc isCompact_Icc).mono_set Ioc_subset_Icc_self
  refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioc
  show Real.exp (-(2 * u)) * P.w u * Real.exp (2 * u) = P.w u
  rw [mul_right_comm, ← Real.exp_add]
  simp

theorem integrableOn_wt_Icc (b : ℝ) : IntegrableOn P.wt (Icc 0 b) := by
  refine Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc ?_
  refine (P.integrableOn_w_Ioc b).congr_fun (fun u hu => ?_) measurableSet_Ioc
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_eq_intervalIntegral {x : ℝ} (hx : 0 ≤ x) : P.W x = ∫ u in (0 : ℝ)..x, P.wt u := by
  rw [intervalIntegral.integral_of_le hx, W, distribution]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu.1)]

theorem W_of_nonpos {x : ℝ} (hx : x ≤ 0) : P.W x = 0 := by
  rw [W, distribution, Ioc_eq_empty (not_lt.mpr hx)]
  simp

theorem W_nonneg (x : ℝ) : 0 ≤ P.W x :=
  setIntegral_nonneg measurableSet_Ioc fun _ hu => (P.w_pos hu.1).le

theorem intervalIntegrable_wt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable P.wt volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((P.integrableOn_wt_Icc b).mono_set (Icc_subset_Icc_left ha))

theorem continuousOn_W {M : ℝ} (hM : 0 ≤ M) : ContinuousOn P.W (Icc 0 M) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := M)
    (f := P.wt) (by rw [uIcc_of_le hM]; exact P.integrableOn_wt_Icc M)
  rw [uIcc_of_le hM] at h
  exact h.congr fun x hx => P.W_eq_intervalIntegral hx.1

/-- `W` is strictly increasing on `[0, ∞)`. -/
theorem W_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : P.W a < P.W b := by
  rw [P.W_eq_intervalIntegral ha, P.W_eq_intervalIntegral (ha.trans hab.le)]
  have hpos : 0 < ∫ u in a..b, P.wt u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (P.intervalIntegrable_wt ha hab.le)
      (fun u hu => ?_) hab
    have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
    simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    exact P.w_pos hu0
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (P.intervalIntegrable_wt le_rfl ha) (P.intervalIntegrable_wt ha hab.le)
  linarith

theorem W_le_W {a b : ℝ} (hab : a ≤ b) : P.W a ≤ P.W b := by
  rcases le_or_gt a 0 with ha | ha
  · rw [P.W_of_nonpos ha]
    exact P.W_nonneg b
  · rcases hab.lt_or_eq with h | h
    · exact (P.W_lt ha.le h).le
    · rw [h]

/-- The constant `c₀ = (1 − e^{-μ})³ > 0`. -/
theorem c₀_pos : 0 < (1 - Real.exp (-P.μ)) ^ 3 := by
  have : Real.exp (-P.μ) < 1 := Real.exp_lt_one_iff.mpr (by linarith [P.hμ1])
  have : 0 < 1 - Real.exp (-P.μ) := by linarith
  positivity

/-- `W(x) ≥ c₀ (x − 1)` for `x ≥ 1`. -/
theorem W_ge {x : ℝ} (hx : 1 ≤ x) : (1 - Real.exp (-P.μ)) ^ 3 * (x - 1) ≤ P.W x := by
  have h01 := P.intervalIntegrable_wt (a := 0) (b := 1) le_rfl zero_le_one
  have h1x := P.intervalIntegrable_wt (a := 1) (b := x) zero_le_one hx
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h1x
  have hW1 : 0 ≤ ∫ u in (0 : ℝ)..1, P.wt u := by
    rw [← P.W_eq_intervalIntegral zero_le_one]
    exact P.W_nonneg 1
  have hmono : ∫ u in (1 : ℝ)..x, (1 - Real.exp (-P.μ)) ^ 3 ≤ ∫ u in (1 : ℝ)..x, P.wt u := by
    refine intervalIntegral.integral_mono_on hx intervalIntegrable_const h1x fun u hu => ?_
    have hu0 : 0 < u := by linarith [hu.1]
    simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    refine le_trans ?_ (P.w_ge hu.1)
    rw [le_div_iff₀ hu0]
    have : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have := P.c₀_pos
    nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [P.W_eq_intervalIntegral (by linarith), ← hadd]
  nlinarith

/-- `W(x) ≤ e^{bx} ∫_{(0,∞)} e^{-bu} w(u) du` for `b > 1`, `x ≥ 0`. -/
theorem W_le_exp {b : ℝ} (hb : 1 < b) (x : ℝ) :
    P.W x ≤ Real.exp (b * x) * ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u := by
  have hint := P.integrableOn_exp_mul_w hb
  have hstep : P.W x ≤ ∫ u in Ioc 0 x, Real.exp (b * x) * (Real.exp (-(b * u)) * P.w u) := by
    refine setIntegral_mono_on (P.integrableOn_w_Ioc x)
      ((hint.mono_set Ioc_subset_Ioi_self).const_mul _) measurableSet_Ioc fun u hu => ?_
    have hw := (P.w_pos hu.1).le
    have he : 1 ≤ Real.exp (b * x) * Real.exp (-(b * u)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [hu.2])
    nlinarith
  rw [integral_const_mul] at hstep
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  refine setIntegral_mono_set hint ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (Real.exp_pos _).le (P.w_pos hu).le

theorem exists_atom (k : ℕ) : ∃ x, 0 < x ∧ P.W x = k + 1 := by
  set c := (1 - Real.exp (-P.μ)) ^ 3 with hc
  have hc0 : 0 < c := P.c₀_pos
  set M : ℝ := 1 + (k + 1) / c with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ((k : ℝ) + 1) / c := by positivity
    linarith
  have hWM : (k : ℝ) + 1 ≤ P.W M := by
    have h := P.W_ge hM1
    have : c * (M - 1) = (k : ℝ) + 1 := by rw [hM]; field_simp; ring
    linarith
  obtain ⟨x, hx, hWx⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ M) (P.continuousOn_W (by linarith))
    ⟨by rw [P.W_of_nonpos le_rfl]; positivity, hWM⟩
  refine ⟨x, ?_, hWx⟩
  rcases hx.1.lt_or_eq with h | h
  · exact h
  · rw [← h, P.W_of_nonpos le_rfl] at hWx
    have : (0 : ℝ) < k + 1 := by positivity
    linarith

/-- The `k`-th discrete prime in logarithmic coordinate: `W(t_k) = k + 1`. -/
def atom (k : ℕ) : ℝ := (P.exists_atom k).choose

theorem atom_pos (k : ℕ) : 0 < P.atom k := (P.exists_atom k).choose_spec.1

theorem W_atom (k : ℕ) : P.W (P.atom k) = k + 1 := (P.exists_atom k).choose_spec.2

theorem atom_le_iff (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : P.atom k ≤ x ↔ (k : ℝ) + 1 ≤ P.W x := by
  constructor
  · intro h
    rw [← P.W_atom k]
    exact P.W_le_W h
  · intro h
    by_contra hlt
    push Not at hlt
    have := P.W_lt hx hlt
    rw [P.W_atom] at this
    linarith

theorem atom_strictMono : StrictMono P.atom := by
  intro j k hjk
  by_contra hle
  push Not at hle
  have h := P.W_le_W hle
  rw [P.W_atom, P.W_atom] at h
  have : (j : ℝ) < k := by exact_mod_cast hjk
  linarith

theorem atom_le_iff_lt_floor (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : P.atom k ≤ x ↔ k < ⌊P.W x⌋₊ := by
  rw [P.atom_le_iff k hx, Nat.lt_iff_add_one_le, Nat.le_floor_iff (P.W_nonneg x)]
  push_cast
  rfl

/-- **The discrete primes follow the continuous ones**: `#{k : t_k ≤ x} = ⌊W(x)⌋`. -/
theorem atomCount_eq (x : ℝ) : atomCount P.atom x = (⌊P.W x⌋₊ : ℝ) := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [P.W_of_nonpos hx.le, atomCount]
    simp only [Nat.floor_zero, Nat.cast_zero]
    convert tsum_zero with k
    rw [if_neg (not_le.mpr (lt_trans hx (P.atom_pos k)))]
  · have hiff : ∀ k : ℕ, P.atom k ≤ x ↔ k < ⌊P.W x⌋₊ := fun k => P.atom_le_iff_lt_floor k hx
    rw [atomCount, tsum_eq_sum (s := Finset.range ⌊P.W x⌋₊) fun k hk => by
      rw [if_neg (by rw [hiff]; simpa using hk)]]
    rw [Finset.sum_congr rfl fun k hk => if_pos ((hiff k).mpr (Finset.mem_range.mp hk))]
    simp

/-- `|N(x) − W(x)| ≤ 1`. -/
theorem abs_atomCount_sub_W_le (x : ℝ) : |atomCount P.atom x - P.W x| ≤ 1 := by
  rw [P.atomCount_eq, abs_le]
  have h1 := Nat.floor_le (P.W_nonneg x)
  have h2 := Nat.lt_floor_add_one (P.W x)
  constructor <;> linarith

/-- The discrete prime sum `Σ_k e^{-a t_k}` converges for `a > 1`. -/
theorem summable_exp_atom {a : ℝ} (ha : 1 < a) : Summable fun k => Real.exp (-(a * P.atom k)) := by
  set b := (1 + a) / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  have hab : 1 < a / b := by rw [lt_div_iff₀ (by linarith)]; linarith
  set C := ∫ u in Ioi (0 : ℝ), Real.exp (-(b * u)) * P.w u with hC
  have hC0 : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.exp_pos _).le (P.w_pos hu).le
  have hk : ∀ k : ℕ, Real.exp (-(b * P.atom k)) ≤ C / ((k : ℝ) + 1) := by
    intro k
    have h := P.W_le_exp hb1 (P.atom k)
    rw [P.W_atom] at h
    rw [le_div_iff₀ (by positivity)]
    have he : Real.exp (-(b * P.atom k)) * Real.exp (b * P.atom k) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(b * P.atom k))]
  have hsum : Summable fun k : ℕ => C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -(a / b) < -1))
    refine (h.mul_left (C ^ (a / b))).congr fun k => ?_
    push_cast
    rfl
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hsum
  have hexp : Real.exp (-(a * P.atom k)) = Real.exp (-(b * P.atom k)) ^ (a / b) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [hexp]
  calc Real.exp (-(b * P.atom k)) ^ (a / b) ≤ (C / ((k : ℝ) + 1)) ^ (a / b) :=
        Real.rpow_le_rpow (Real.exp_pos _).le (hk k) (by positivity)
    _ = C ^ (a / b) * ((k : ℝ) + 1) ^ (-(a / b)) := by
        rw [Real.div_rpow hC0 (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]

/-! ### The discrete one-off -/

theorem atom_zero_le (k : ℕ) : P.atom 0 ≤ P.atom k := P.atom_strictMono.monotone (Nat.zero_le k)

/-- The discrepancy `N − W` between the discrete and the continuous prime counts. -/
def discrepancy (x : ℝ) : ℝ := atomCount P.atom x - P.W x

theorem measurable_discrepancy : Measurable P.discrepancy := by
  have hW : Monotone P.W := fun a b h => P.W_le_W h
  have hF : Monotone fun x => (⌊P.W x⌋₊ : ℝ) := fun a b h =>
    Nat.cast_le.mpr (Nat.floor_le_floor (P.W_le_W h))
  have heq : P.discrepancy = fun x => (⌊P.W x⌋₊ : ℝ) - P.W x := by
    funext x
    rw [discrepancy, P.atomCount_eq]
  rw [heq]
  exact hF.measurable.sub hW.measurable

theorem abs_discrepancy_le (x : ℝ) : |P.discrepancy x| ≤ 1 := P.abs_atomCount_sub_W_le x

/-- The Euler logarithm `Σ_k −log(1 − p_k^{-s})` of the discrete primes `p_k = e^{t_k}`. -/
def eulerLog (s : ℂ) : ℂ := ∑' k, -Complex.log (1 - cexp (-(s * P.atom k)))

/-- **The zeta function of the discrete primes**, `exp` of the Euler logarithm. -/
def discreteZeta (s : ℂ) : ℂ := cexp (P.eulerLog s)

/-- **It is the Euler product** `Π_k (1 − p_k^{-s})^{-1}` on `Re s > 1`. -/
theorem discreteZeta_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    P.discreteZeta s = ∏' k, (1 - cexp (-(s * P.atom k)))⁻¹ := by
  have hre : ∀ k, 0 < (1 - cexp (-(s * P.atom k))).re := by
    intro k
    have h1 : (cexp (-(s * P.atom k))).re ≤ ‖cexp (-(s * P.atom k))‖ := Complex.re_le_norm _
    have h2 : ‖cexp (-(s * P.atom k))‖ < 1 := by
      rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
      have := P.atom_pos k
      nlinarith
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hlog : ∀ k, Complex.log (1 - cexp (-(s * P.atom k)))⁻¹ =
      -Complex.log (1 - cexp (-(s * P.atom k))) := by
    intro k
    refine Complex.log_inv _ fun h => ?_
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [hre k]
  have hne : ∀ k, (1 - cexp (-(s * P.atom k)))⁻¹ ≠ 0 := by
    intro k
    refine inv_ne_zero fun h => ?_
    have := hre k
    rw [h] at this
    simp at this
  obtain ⟨h1, h2⟩ := summable_neg_log P.atom_pos P.atom_zero_le
    (fun a ha => P.summable_exp_atom ha) hs
  have hsum : Summable fun k => Complex.log (1 - cexp (-(s * P.atom k)))⁻¹ := by
    simp_rw [hlog]
    exact (h1.add h2).congr fun k => by ring
  rw [discreteZeta, eulerLog, ← Complex.cexp_tsum_eq_tprod hne hsum]
  simp_rw [hlog]

/-- **The continuation** `ζ_c(s) e^{sΛ(s) + R(s)}`, with `Λ` the Laplace transform of `N − W`
and `R` the prime-power remainder. -/
def continuation (s : ℂ) : ℂ :=
  overRegularZeta P.μ P.ν P.γ s *
    cexp (s * boundedLaplace P.discrepancy s + primePowerRemainder P.atom s)

/-- **The discrete zeta function is the continuation on `Re s > 1`.** -/
theorem discreteZeta_eq_continuation {s : ℂ} (hs : 1 < s.re) :
    P.discreteZeta s = P.continuation s := by
  have hs0 : 0 < s.re := by linarith
  have hsplit := tsum_neg_log_eq P.atom_pos P.atom_zero_le (fun a ha => P.summable_exp_atom ha) hs
  have hdisc := tsum_cexp_atoms P.atom_pos hs0 (P.summable_exp_atom hs)
  have hint : IntegrableOn (fun u => Real.exp (-(s.re * u)) * P.w u) (Ioi 0) :=
    P.integrableOn_exp_mul_w hs
  obtain ⟨hWint, hcont⟩ := integral_cexp_density P.measurable_w (fun u hu => (P.w_pos hu).le)
    hs0 hint
  have hEint : IntegrableOn (fun x : ℝ => cexp (-(s * x)) * (P.discrepancy x : ℂ)) (Ioi 0) := by
    have hb : IntegrableOn (fun x : ℝ => Real.exp (-s.re * x)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine hb.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(s * x))).measurable.mul
        (Complex.measurable_ofReal.comp P.measurable_discrepancy)).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs]
      have := P.abs_discrepancy_le x
      have he := Real.exp_pos (-(s.re * x))
      rw [show -s.re * x = -(s.re * x) by ring]
      nlinarith
  have hN : ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (atomCount P.atom x : ℂ) =
      boundedLaplace P.discrepancy s +
        ∫ x in Ioi (0 : ℝ), cexp (-(s * x)) * (distribution P.w x : ℂ) := by
    rw [boundedLaplace, ← integral_add hEint hWint]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [discrepancy, W]
    push_cast
    ring
  have hlog : P.eulerLog s = (∫ u in Ioi (0 : ℝ), cexp (-(s * u)) * (P.w u : ℂ)) +
      (s * boundedLaplace P.discrepancy s + primePowerRemainder P.atom s) := by
    rw [eulerLog, hsplit, hdisc, hN, hcont]
    ring
  rw [discreteZeta, hlog, Complex.exp_add, continuation]
  congr 1
  exact cexp_integral_primeDensity P.hlow P.hhigh P.h4 hs

theorem overRegularZeta_denom_ne {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    (s - 1) * (s + (3 * P.μ - 1 - P.ν)) * (s + (3 * P.μ - 1 + P.ν)) ≠ 0 :=
  overRegularZeta_denom_ne_zero P.hν0.le (by linarith [P.hν]) hs1

/-- **The continuation is holomorphic on `Re s > 1/2`, away from the pole `s = 1`.** -/
theorem differentiableOn_continuation :
    DifferentiableOn ℂ P.continuation {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1} := by
  rintro s ⟨hs, hs1⟩
  have hζ : DifferentiableAt ℂ (overRegularZeta P.μ P.ν P.γ) s := by
    unfold overRegularZeta
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (P.overRegularZeta_denom_ne hs hs1)
  have hΛ : DifferentiableAt ℂ (boundedLaplace P.discrepancy) s :=
    (differentiableOn_boundedLaplace P.measurable_discrepancy P.abs_discrepancy_le).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show 0 < s.re; linarith))
  have hR : DifferentiableAt ℂ (primePowerRemainder P.atom) s :=
    (differentiableOn_primePowerRemainder P.atom_pos P.atom_zero_le
      (fun a ha => P.summable_exp_atom ha)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact (hζ.mul ((differentiableAt_id.mul hΛ).add hR).cexp).differentiableWithinAt

/-- **The zeros right of `1/2` are exactly the off-line pair `(1 − μ) ± iγ`.** -/
theorem continuation_eq_zero_iff {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    P.continuation s = 0 ↔
      s = ((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I ∨ s = ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I := by
  have hden := P.overRegularZeta_denom_ne hs hs1
  have h4 : s + (4 * P.μ - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [P.hμ1]
  have hfac : (s - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2 =
      (s - (((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I)) * (s - (((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I)) := by
    push_cast
    linear_combination ((P.γ : ℂ) ^ 2) * Complex.I_sq
  rw [continuation, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), overRegularZeta,
    div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_left h4, hfac, mul_eq_zero,
    sub_eq_zero, sub_eq_zero]

/-- **The one-off.** For `0 ≤ h < 1/2 − μ` the zeros of the continuation with real part
`> 1/2 + h` are exactly the pair `(1 − μ) ± iγ`: finitely many, and not none. -/
theorem zeros_right_of_eq_pair {h : ℝ} (hh : h < 1 / 2 - P.μ) (h0 : 0 ≤ h) :
    {s : ℂ | 1 / 2 + h < s.re ∧ s ≠ 1 ∧ P.continuation s = 0} =
      {((1 - P.μ : ℝ) : ℂ) + (P.γ : ℂ) * I, ((1 - P.μ : ℝ) : ℂ) - (P.γ : ℂ) * I} := by
  ext s
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hs, hs1, hz⟩
    exact (P.continuation_eq_zero_iff (by linarith) hs1).mp hz
  · intro hz
    have hre : s.re = 1 - P.μ := by rcases hz with rfl | rfl <;> simp
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hre
      simp at hre
      linarith [P.hμ1]
    exact ⟨by rw [hre]; linarith, hs1, (P.continuation_eq_zero_iff (by rw [hre]; linarith [P.hμ2])
      hs1).mpr hz⟩

/-! ### The singularity at `s = 1/2` -/

/-- `W(j + 1) − W(j) ≥ c₀ e^j/(j + 1)` for `j ≥ 1`. -/
theorem W_succ_sub_ge {j : ℝ} (hj : 1 ≤ j) :
    (1 - Real.exp (-P.μ)) ^ 3 * Real.exp j / (j + 1) ≤ P.W (j + 1) - P.W j := by
  have hj0 : 0 ≤ j := by linarith
  have h0j := P.intervalIntegrable_wt le_rfl hj0
  have hj1 := P.intervalIntegrable_wt hj0 (by linarith : j ≤ j + 1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0j hj1
  rw [P.W_eq_intervalIntegral hj0, P.W_eq_intervalIntegral (by linarith), ← hadd]
  have hc := P.c₀_pos
  have hmono : ∫ _u in j..j + 1, (1 - Real.exp (-P.μ)) ^ 3 * Real.exp j / (j + 1) ≤
      ∫ u in j..j + 1, P.wt u := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hj1
      fun u hu => ?_
    have hu1 : 1 ≤ u := le_trans hj hu.1
    have hu0 : 0 < u := by linarith
    simp only [wt, Set.indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu0)]
    refine le_trans ?_ (P.w_ge hu1)
    calc (1 - Real.exp (-P.μ)) ^ 3 * Real.exp j / (j + 1)
        ≤ (1 - Real.exp (-P.μ)) ^ 3 * Real.exp u / (j + 1) := by
          gcongr
          exact hu.1
      _ ≤ (1 - Real.exp (-P.μ)) ^ 3 * Real.exp u / u :=
          div_le_div_of_nonneg_left (by positivity) hu0 hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

/-- `e^{-(j+2)} ≤ (1/2)^j`. -/
theorem exp_neg_le_half_pow (j : ℕ) : Real.exp (-((j : ℝ) + 2)) ≤ (1 / 2) ^ j := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (2 : ℝ) ^ j ≤ Real.exp (j : ℝ) := by
    rw [show (j : ℝ) = j * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) he j
  have h2 : Real.exp (j : ℝ) ≤ Real.exp ((j : ℝ) + 2) := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, one_div, inv_pow]
  exact inv_anti₀ (by positivity) (h1.trans h2)

/-- **The discrete primes have `Σ_k 1/p_k = ∞`.** Layer `t_k ∈ (j, j+1]` holds at least
`W(j+1) − W(j) − 1 ≥ c₀ e^j/(j+1) − 1` atoms, each contributing at least `e^{-(j+1)}`. -/
theorem not_summable_exp_neg_atom : ¬ Summable fun k => Real.exp (-(P.atom k)) := by
  intro hsum
  set f : ℕ → ℝ := fun k => Real.exp (-(P.atom k)) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => (Real.exp_pos _).le
  set N : ℕ → ℕ := fun j => ⌊P.W j⌋₊ with hN
  have hNmono : Monotone N := fun a b h =>
    Nat.floor_le_floor (P.W_le_W (by exact_mod_cast h))
  set c : ℝ := (1 - Real.exp (-P.μ)) ^ 3 * Real.exp (-1) with hc
  have hc0 : 0 < c := mul_pos P.c₀_pos (Real.exp_pos _)
  have hlayer : ∀ j : ℕ, 1 ≤ j →
      c / ((j : ℝ) + 1) - Real.exp (-((j : ℝ) + 1)) ≤ ∑ k ∈ Finset.Ico (N j) (N (j + 1)), f k := by
    intro j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hk : ∀ k ∈ Finset.Ico (N j) (N (j + 1)), Real.exp (-((j : ℝ) + 1)) ≤ f k := by
      intro k hk
      have hlt : k < ⌊P.W ((j + 1 : ℕ) : ℝ)⌋₊ := (Finset.mem_Ico.mp hk).2
      have hle := (P.atom_le_iff_lt_floor k (by positivity)).mpr hlt
      push_cast at hle
      exact Real.exp_le_exp.mpr (by linarith)
    have hcard := Finset.card_nsmul_le_sum _ _ _ hk
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (hNmono (Nat.le_succ j))] at hcard
    have hN1 : P.W ((j + 1 : ℕ) : ℝ) - 1 < (N (j + 1) : ℝ) := by
      have := Nat.lt_floor_add_one (P.W ((j + 1 : ℕ) : ℝ))
      simp only [hN]
      linarith
    have hN0 : (N j : ℝ) ≤ P.W j := Nat.floor_le (P.W_nonneg _)
    have hgap := P.W_succ_sub_ge hj'
    push_cast at hN1
    have hpos := Real.exp_pos (-((j : ℝ) + 1))
    have hprod : Real.exp j / ((j : ℝ) + 1) * Real.exp (-((j : ℝ) + 1)) =
        Real.exp (-1) / ((j : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    have hkey : ((1 - Real.exp (-P.μ)) ^ 3 * Real.exp j / (j + 1) - 1) *
        Real.exp (-((j : ℝ) + 1)) ≤ ((N (j + 1) : ℝ) - N j) * Real.exp (-((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    have hexpand : ((1 - Real.exp (-P.μ)) ^ 3 * Real.exp j / (j + 1) - 1) *
        Real.exp (-((j : ℝ) + 1)) = c / ((j : ℝ) + 1) - Real.exp (-((j : ℝ) + 1)) := by
      rw [hc, sub_mul, one_mul, mul_div_assoc, mul_assoc, hprod]
      ring
    linarith
  have hpartial : ∀ J : ℕ, ∑ j ∈ Finset.range J, (c / ((j : ℝ) + 2) - Real.exp (-((j : ℝ) + 2))) ≤
      ∑ k ∈ Finset.range (N (J + 1)), f k := by
    intro J
    induction J with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_nonneg fun k _ => hf0 k
    | succ J ih =>
      rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico f (hNmono (Nat.le_succ (J + 1)))]
      have hl := hlayer (J + 1) (by omega)
      push_cast at hl
      have : (J : ℝ) + 1 + 1 = J + 2 := by ring
      rw [this] at hl
      linarith
  have hharm := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.mp ((tendsto_atTop.mp hharm) ((∑' k, f k + 3) / c + 1))
  have hJ := hJ₀ (J₀ + 1) (by omega)
  have hshift : ∑ i ∈ Finset.range (J₀ + 1), (1 / ((i : ℝ) + 1)) =
      ∑ j ∈ Finset.range J₀, (1 / ((j : ℝ) + 2)) + 1 := by
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring_nf
    · simp
  have hgeom : ∑ j ∈ Finset.range J₀, Real.exp (-((j : ℝ) + 2)) ≤ 2 :=
    (Finset.sum_le_sum fun j _ => exp_neg_le_half_pow j).trans (sum_geometric_two_le J₀)
  have hsplit : ∑ j ∈ Finset.range J₀, (c / ((j : ℝ) + 2) - Real.exp (-((j : ℝ) + 2))) =
      c * ∑ j ∈ Finset.range J₀, (1 / ((j : ℝ) + 2)) -
        ∑ j ∈ Finset.range J₀, Real.exp (-((j : ℝ) + 2)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hle := (hpartial J₀).trans (hsum.sum_le_tsum _ (fun k _ => hf0 k))
  rw [hsplit] at hle
  have hH : (∑' k, f k + 3) / c ≤ ∑ j ∈ Finset.range J₀, (1 / ((j : ℝ) + 2)) := by
    linarith
  have := (div_le_iff₀ hc0).mp hH
  linarith

/-- `−log(1 − x) − x ≥ x²/2` on `[0, 1)`. -/
theorem neg_log_one_sub_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ^ 2 / 2 ≤ -Real.log (1 - x) - x := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_nonneg hx0]; exact hx1)
  have hle := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  simp [Finset.sum_range_succ] at hle
  linarith

/-- On the real axis each prime-power term is real. -/
theorem primePowerTerm_ofReal {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) :
    -Complex.log (1 - cexp (-((σ : ℂ) * P.atom k))) - cexp (-((σ : ℂ) * P.atom k)) =
      ((-Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k)) : ℝ) : ℂ) := by
  have he : cexp (-((σ : ℂ) * (P.atom k : ℂ))) = ((Real.exp (-(σ * P.atom k)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hpos : 0 ≤ 1 - Real.exp (-(σ * P.atom k)) := by
    have := Real.exp_le_one_iff.mpr (by nlinarith [P.atom_pos k] : -(σ * P.atom k) ≤ 0)
    linarith
  rw [he, show (1 : ℂ) - ((Real.exp (-(σ * P.atom k)) : ℝ) : ℂ) =
      ((1 - Real.exp (-(σ * P.atom k)) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_log hpos]
  push_cast
  ring

/-- On the real axis the prime-power remainder is real. -/
theorem primePowerRemainder_ofReal {σ : ℝ} (hσ : 0 ≤ σ) :
    primePowerRemainder P.atom σ =
      ((∑' k, (-Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k))) : ℝ) :
        ℂ) := by
  rw [primePowerRemainder, Complex.ofReal_tsum]
  exact congrArg tsum (funext fun k => P.primePowerTerm_ofReal hσ k)

theorem primePowerTerm_real_ge {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    Real.exp (-(2 * σ * P.atom k)) / 2 ≤
      -Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k)) := by
  have hx1 : Real.exp (-(σ * P.atom k)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [P.atom_pos k])
  have h := neg_log_one_sub_sub_ge (Real.exp_pos _).le hx1
  have hsq : Real.exp (-(σ * P.atom k)) ^ 2 = Real.exp (-(2 * σ * P.atom k)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq] at h
  exact h

/-- The real prime-power terms are summable for `σ > 1/2`. -/
theorem summable_primePowerTerm_real {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun k =>
      -Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k)) := by
  have hσ0 : 0 < σ := by linarith
  set q : ℝ := Real.exp (-(σ * P.atom 0)) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [P.atom_pos 0])
  refine Summable.of_nonneg_of_le (fun k => le_trans (by positivity) (P.primePowerTerm_real_ge hσ0 k))
    (fun k => ?_) (((P.summable_exp_atom (a := 2 * σ) (by linarith)).mul_right
      ((1 - q)⁻¹)).div_const 2)
  have hle : Real.exp (-(σ * P.atom k)) ≤ q := by
    rw [hq]
    exact Real.exp_le_exp.mpr (by nlinarith [P.atom_zero_le k])
  have h := norm_primePowerTerm_le (P.atom_pos k) (z := (σ : ℂ)) (by simp) hle hq1
  rw [P.primePowerTerm_ofReal hσ0.le k, Complex.norm_real, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (by simpa [mul_assoc] using h)

/-- **The continuation blows up at `s = 1/2`.** Along the real axis `‖ζ_P(σ)‖ → ∞` as
`σ → 1/2⁺`: the prime squares give `R(σ) ≥ ½ Σ_k p_k^{-2σ}`, which diverges since `Σ 1/p_k = ∞`,
while `ζ_c(1/2) ≠ 0` and `sΛ(s)` is continuous at `1/2`. So the discrete zeta function has no
continuous extension to the critical line and admits no functional-equation defect there. -/
theorem tendsto_norm_continuation_half :
    Tendsto (fun σ : ℝ => ‖P.continuation σ‖) (𝓝[>] (1 / 2)) atTop := by
  set ζc := overRegularZeta P.μ P.ν P.γ with hζc
  set F : ℂ → ℂ := fun s => s * boundedLaplace P.discrepancy s with hF
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  -- continuity of `ζ_c` and `F` at `1/2`
  have hden : ((1 / 2 : ℂ) - 1) * ((1 / 2 : ℂ) + (3 * P.μ - 1 - P.ν)) *
      ((1 / 2 : ℂ) + (3 * P.μ - 1 + P.ν)) ≠ 0 :=
    overRegularZeta_denom_ne_zero P.hν0.le (by norm_num; linarith [P.hν]) (by norm_num)
  have hζd : DifferentiableAt ℂ ζc (1 / 2) := by
    rw [hζc]
    unfold overRegularZeta
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) hden
  have hζ0 : ζc (1 / 2) ≠ 0 := by
    rw [hζc, overRegularZeta]
    refine div_ne_zero (mul_ne_zero ?_ ?_) hden
    · have : ((1 / 2 : ℂ) - (1 - P.μ)) ^ 2 + (P.γ : ℂ) ^ 2 =
          (((P.μ - 1 / 2) ^ 2 + P.γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      have : 0 < (P.μ - 1 / 2) ^ 2 + P.γ ^ 2 := by nlinarith [P.hμ2, sq_nonneg P.γ]
      exact_mod_cast this.ne'
    · have : (1 / 2 : ℂ) + (4 * P.μ - 1) = ((4 * P.μ - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      have : 0 < 4 * P.μ - 1 / 2 := by linarith [P.hμ1]
      exact_mod_cast this.ne'
  have hζc_cont : ContinuousAt (fun σ : ℝ => ζc σ) (1 / 2) := by
    have := hζd.continuousAt
    rw [← hhalf] at this
    exact this.comp Complex.continuous_ofReal.continuousAt
  have hFd : DifferentiableAt ℂ F (1 / 2) := by
    have hΛ := (differentiableOn_boundedLaplace P.measurable_discrepancy
      P.abs_discrepancy_le).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by show (0 : ℝ) < (1 / 2 : ℂ).re; norm_num))
    exact differentiableAt_id.mul hΛ
  have hF_cont : ContinuousAt (fun σ : ℝ => (F σ).re) (1 / 2) := by
    have := hFd.continuousAt
    rw [← hhalf] at this
    exact Complex.continuous_re.continuousAt.comp (this.comp Complex.continuous_ofReal.continuousAt)
  set A := ‖ζc (1 / 2)‖ / 2 with hA
  have hA0 : 0 < A := by rw [hA]; exact half_pos (norm_pos_iff.mpr hζ0)
  set B := (F (1 / 2)).re - 1 with hB
  have hζev : ∀ᶠ σ : ℝ in 𝓝 (1 / 2), A < ‖ζc σ‖ := by
    have h := hζc_cont.norm
    have hval : ‖ζc ((1 / 2 : ℝ) : ℂ)‖ = ‖ζc (1 / 2)‖ := by rw [hhalf]
    refine h.eventually (Ioi_mem_nhds ?_)
    show A < ‖ζc ((1 / 2 : ℝ) : ℂ)‖
    rw [hval, hA]
    exact half_lt_self (norm_pos_iff.mpr hζ0)
  have hFev : ∀ᶠ σ : ℝ in 𝓝 (1 / 2), B < (F σ).re := by
    have hval : (F ((1 / 2 : ℝ) : ℂ)).re = (F (1 / 2)).re := by rw [hhalf]
    refine hF_cont.eventually (Ioi_mem_nhds ?_)
    show B < (F ((1 / 2 : ℝ) : ℂ)).re
    rw [hval, hB]
    linarith
  rw [tendsto_atTop]
  intro M
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set T := Real.log M' - Real.log A - B with hT
  -- partial sums of `1/p_k` are unbounded
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => (Real.exp_pos _).le)).mp
    P.not_summable_exp_neg_atom
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ((tendsto_atTop.mp hdiv) (2 * T + 1))
  have hKK := hK K le_rfl
  set g : ℝ → ℝ := fun σ => ∑ k ∈ Finset.range K, Real.exp (-(2 * σ * P.atom k)) with hg
  have hg_cont : ContinuousAt g (1 / 2) := by
    rw [hg]
    fun_prop
  have hg_half : g (1 / 2) = ∑ k ∈ Finset.range K, Real.exp (-(P.atom k)) := by
    rw [hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring
  have hgev : ∀ᶠ σ : ℝ in 𝓝 (1 / 2), 2 * T < g σ :=
    hg_cont.eventually (Ioi_mem_nhds (by rw [hg_half]; linarith))
  have hall := (hζev.and (hFev.and hgev))
  filter_upwards [nhdsWithin_le_nhds hall, self_mem_nhdsWithin] with σ hσ hσ12
  obtain ⟨h1, h2, h3⟩ := hσ
  have hσ' : 1 / 2 < σ := hσ12
  have hσ0 : 0 < σ := by linarith
  -- `R(σ) ≥ g(σ)/2`
  set r := ∑' k, (-Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k)))
    with hr
  have hr_ge : g σ / 2 ≤ r := by
    have hsumm := P.summable_primePowerTerm_real hσ'
    have hpart := hsumm.sum_le_tsum (Finset.range K) (fun k _ =>
      le_trans (by positivity) (P.primePowerTerm_real_ge hσ0 k))
    have hterm : g σ / 2 ≤ ∑ k ∈ Finset.range K,
        (-Real.log (1 - Real.exp (-(σ * P.atom k))) - Real.exp (-(σ * P.atom k))) := by
      rw [hg, Finset.sum_div]
      exact Finset.sum_le_sum fun k _ => P.primePowerTerm_real_ge hσ0 k
    linarith
  have hnorm : ‖P.continuation σ‖ = ‖ζc σ‖ * Real.exp ((F σ).re + r) := by
    rw [continuation, norm_mul, Complex.norm_exp, P.primePowerRemainder_ofReal hσ0.le, Complex.add_re,
      Complex.ofReal_re]
  rw [hnorm]
  have hexp : Real.exp (Real.log M' - Real.log A) ≤ Real.exp ((F σ).re + r) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_sub, Real.exp_log hM'0, Real.exp_log hA0] at hexp
  calc M ≤ M' := le_max_left _ _
    _ = A * (M' / A) := by field_simp
    _ ≤ ‖ζc σ‖ * Real.exp ((F σ).re + r) :=
        mul_le_mul h1.le hexp (by positivity) (norm_nonneg _)

end Params

end

end GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
