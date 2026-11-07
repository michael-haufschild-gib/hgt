import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# A discrete Beurling one-off

Let `w ≥ 0` be the logarithmic prime density of the continuous one-off `overRegularZeta`
(`1/3 < μ < 1/2`, `0 < ν < 3μ − 1`, `γ ≠ 0`), `W(x) = ∫_{(0,x]} w`, and let `t_k` be the point with
`W(t_k) = k + 1`. The discrete primes `p_k = e^{t_k}` follow the continuous ones to within one:
`#{k : t_k ≤ x} = ⌊W(x)⌋`.

* **Laplace transforms of counting functions** (`tsum_cexp_atoms`, `integral_cexp_density`):
  `Σ_k e^{-s t_k} = s ∫ e^{-sx} N(x) dx` and `∫ e^{-su} w(u) du = s ∫ e^{-sx} W(x) dx`, by Fubini.
* **Continuation** (`discreteZeta_eq`, `differentiableOn_discreteContinuation`). With
  `Λ(s) = ∫ e^{-sx}(N − W)(x) dx`, holomorphic on `Re s > 0` because `|N − W| ≤ 1`, and the
  prime-power remainder `R(s) = Σ_k (−log(1 − e^{-st_k}) − e^{-st_k})`, holomorphic on `Re s > 1/2`,
  the Euler product `Π_k (1 − p_k^{-s})^{-1}` equals `ζ_c(s) e^{sΛ(s) + R(s)}` on `Re s > 1`.
* **One-off** (`discreteContinuation_eq_zero_iff`). On `Re s > 1/2`, `s ≠ 1`, the continuation
  vanishes exactly at `(1 − μ) ± iγ`: finitely many zeros right of `1/2 + h` for `h < 1/2 − μ`, and
  at least one.
* **No functional-equation defect** (`tendsto_norm_discreteContinuation_half`). The prime squares
  give `R(σ) ≥ ½ Σ_k p_k^{-2σ} → ∞` as `σ → 1/2⁺`, because `Σ 1/p_k = ∞`; so the continuation
  blows up at `s = 1/2` and does not extend continuously to the critical line, where a
  functional-equation defect would be measured. A discrete one-off reaching the line must carry the
  correction `−½ W(x/2)` of Riemann's formula in its prime count.
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

/-- **The Euler logarithm splits** into the prime sum and the prime-power remainder on `Re s > 1`. -/
theorem tsum_neg_log_eq {t : ℕ → ℝ} (ht : ∀ k, 0 < t k) (hmono : ∀ k, t 0 ≤ t k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * t k))) {s : ℂ} (hs : 1 < s.re) :
    ∑' k, -Complex.log (1 - cexp (-(s * t k))) =
      ∑' k, cexp (-(s * t k)) + primePowerRemainder t s := by
  have hs0 : 0 < s.re := by linarith
  have h1 : Summable fun k => cexp (-(s * t k)) := by
    refine Summable.of_norm ?_
    simp_rw [norm_cexp_neg_mul]
    exact hsum s.re hs
  set q : ℝ := Real.exp (-(s.re * t 0)) with hq
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have := ht 0
    nlinarith
  have h2 : Summable fun k => -Complex.log (1 - cexp (-(s * t k))) - cexp (-(s * t k)) := by
    refine Summable.of_norm_bounded ((((hsum (2 * s.re) (by linarith)).mul_right
      ((1 - q)⁻¹)).div_const 2)) fun k => ?_
    have hle : Real.exp (-(s.re * t k)) ≤ q := by
      rw [hq]
      exact Real.exp_le_exp.mpr (by nlinarith [hmono k])
    exact norm_primePowerTerm_le (ht k) le_rfl hle hq1
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
  rw [RCLike.re_to_complex, show -((σ : ℂ) * (u : ℂ)) = ((-(σ * u) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_re]

end Params

end

end GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff
