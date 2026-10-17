import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.PrimeBlindKernelSpectral
import GaloisForLFunctions.RHTower.RiemannKernelTruncationEnergyOrder
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy
import GaloisForLFunctions.HTGeometry.GammaLogDeriv
import Zeta23.WeilEF.VerticalLine

/-!
# Prime-blind positivity at dilated nodes

Keep the archimedean datum of `ζ` (pole `2cosh(x/2)`, density `Ω(r) = Re ψ(¼ + ir/2) − log π`)
and dilate the node set: `PrimeBlindPositiveDilated t` says that the pole and archimedean part
`A = weilArchRe` is nonnegative on every nonnegative combination of autocorrelations whose
symmetric values vanish at `±t·log n`, `n ≥ 2`.  At `t = 1` this is prime-blind positivity, i.e. RH.

* **Dilation formula** (`weilArchRe_comp_div`): for `f_t = f(·/t)`,
  `A(k_{f_t}) = Re(t²(k̂(ti/2) + k̂(−ti/2)) + (t/2π)∫ k̂(s) Ω(s/t) ds)`, and it is continuous at
  `t = 1` (`tendsto_weilArchRe_comp_div`).
* **Dilation continuity** (`riemannHypothesis_of_tendsto`): if `PBAP(t_k)` holds along some
  `t_k → 1`, then RH.  So RH holds iff the good set accumulates at `1`
  (`riemannHypothesis_iff_exists_tendsto`).
* **Reciprocal integers** (`primeBlindPositiveDilated_one_div_of_one`): the nodes `(1/k)·log n`
  contain `log ℕ`, so `PBAP(1) ⟹ PBAP(1/k)` and RH gives `PBAP(1/k)` for every `k ≥ 1`.
* **Dilated data** (`primeBlindPositiveDilated_iff`): `PBAP(t)` is blind positivity at the original
  nodes `log n` for the dilated datum `A_t`.  For `t = ½` its density is
  `Ω(2s) = log 2 + ½(D_{−1/4}(s) + D_{3/4}(s))` with `D_μ` the density of `Γℝ(s + μ)`
  (`gammaBracket_two_mul`, digamma duplication), and `Γℝ(s − ¼)Γℝ(s + ¾) = Γℂ(s − ¼)`
  (`Gammaℝ_sub_quarter_mul`): `PBAP(½)` is blind positivity for the weight-½ (theta) datum.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower.NodeDilation

open WeilOneSided

noncomputable section

/-! ### Dilating a test -/

theorem hasCompactSupport_comp_div {f : ℝ → ℂ} (hf : HasCompactSupport f) {t : ℝ} (ht : t ≠ 0) :
    HasCompactSupport fun x => f (x / t) := by
  have e : (fun x => f (x / t)) = fun x => f (t⁻¹ • x) :=
    funext fun x => by rw [smul_eq_mul, div_eq_inv_mul]
  rw [e]
  exact hf.comp_smul (inv_ne_zero ht)

/-- The dilate `f(·/t)` of a Weil test (`f` itself at `t = 0`). -/
def dilateTest (t : ℝ) (f : WeilTestFn) : WeilTestFn :=
  if ht : t = 0 then f else
    ⟨fun x => f.1 (x / t), f.2.1.comp (contDiff_id.div_const t), hasCompactSupport_comp_div f.2.2 ht⟩

theorem dilateTest_apply {t : ℝ} (ht : t ≠ 0) (f : WeilTestFn) :
    (dilateTest t f).1 = fun x => f.1 (x / t) := by
  simp [dilateTest, ht]

/-- `k_{f(·/t)}(y) = t · k_f(y/t)`. -/
theorem weilTest_comp_div (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    EF.weilTest (fun x => f (x / t)) (fun x => f (x / t)) y = t * EF.weilTest f f (y / t) := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde]
  have h := Measure.integral_comp_mul_left
    (fun s : ℝ => f (s / t) * conj (f (-(y - s) / t))) t
  rw [abs_inv, abs_of_pos ht] at h
  have e : (fun x : ℝ => f (t * x / t) * conj (f (-(y - t * x) / t))) =
      fun x => f x * conj (f (-(y / t - x))) := by
    funext x
    rw [mul_div_cancel_left₀ x ht.ne', show -(y - t * x) / t = -(y / t - x) by field_simp]
  rw [e] at h
  rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne',
    Complex.ofReal_one, one_mul]

/-- `k̂_{f(·/t)}(z) = t² k̂_f(tz)`. -/
theorem paperFT_weilTest_comp_div (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    paperFT (EF.weilTest (fun x => f (x / t)) (fun x => f (x / t))) z =
      (t : ℂ) ^ 2 * paperFT (EF.weilTest f f) (t * z) := by
  have e : EF.weilTest (fun x => f (x / t)) (fun x => f (x / t)) =
      fun y => (t : ℂ) * EF.weilTest f f (y / t) := funext (weilTest_comp_div f ht)
  have hlin : paperFT (fun y => (t : ℂ) * EF.weilTest f f (y / t)) z =
      (t : ℂ) * paperFT (fun y => EF.weilTest f f (y / t)) z := by
    unfold paperFT
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  rw [e, hlin, paperFT_comp_div ht]
  ring

/-- **Dilation formula** for the pole and archimedean part. -/
theorem weilArchRe_comp_div (f : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    weilArchRe (EF.weilTest (fun x => f (x / t)) (fun x => f (x / t))) =
      ((t : ℂ) ^ 2 * (paperFT (EF.weilTest f f) (t * (I / 2)) +
          paperFT (EF.weilTest f f) (t * (-I / 2))) +
        ((t / (2 * π) : ℝ) : ℂ) *
          ∫ s : ℝ, paperFT (EF.weilTest f f) s * (EF.gammaBracket (s / t) : ℂ)).re := by
  set k := EF.weilTest f f with hk
  have hsub : ∫ r : ℝ, paperFT k ((t : ℂ) * r) * (EF.gammaBracket r : ℂ) =
      ((t⁻¹ : ℝ) : ℂ) * ∫ s : ℝ, paperFT k s * (EF.gammaBracket (s / t) : ℂ) := by
    have h := Measure.integral_comp_mul_left
      (fun s : ℝ => paperFT k s * (EF.gammaBracket (s / t) : ℂ)) t
    rw [abs_inv, abs_of_pos ht, Complex.real_smul] at h
    rw [← h]
    congr 1
    funext x
    rw [mul_div_cancel_left₀ x ht.ne', Complex.ofReal_mul]
  rw [weilArchRe]
  simp_rw [paperFT_weilTest_comp_div f ht]
  have hint : ∫ r : ℝ, (t : ℂ) ^ 2 * paperFT k ((t : ℂ) * r) * (EF.gammaBracket r : ℂ) =
      (t : ℂ) ^ 2 * ∫ r : ℝ, paperFT k ((t : ℂ) * r) * (EF.gammaBracket r : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext r
    ring
  rw [← hk, hint, hsub]
  congr 1
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp

theorem paperFT_weilTest_ofReal_eq_normSq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (r : ℝ) : ‖paperFT (EF.weilTest f f) r‖ = ‖paperFT f r‖ ^ 2 := by
  rw [paperFT_weilTest_self_eq_normSq hf hfc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- The archimedean integral is continuous in the dilation parameter at `t = 1`. -/
theorem continuousAt_integral_gammaBracket_div {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ContinuousAt (fun t : ℝ => ∫ s : ℝ, paperFT (EF.weilTest f f) s * (EF.gammaBracket (s / t) : ℂ))
      1 := by
  have hkc : Continuous (EF.weilTest f f) :=
    (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hkcs : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hkd : Continuous fun s : ℝ => paperFT (EF.weilTest f f) s :=
    (WeilEF.differentiable_paperFT hkc hkcs).continuous.comp Complex.continuous_ofReal
  obtain ⟨C, hC0, hC⟩ := exists_abs_gammaBracket_le
  obtain ⟨D, hD0, hD⟩ := exists_norm_paperFT_le_decay (⟨f, hf, hfc⟩ : WeilTestFn)
  have hbi : Integrable fun s : ℝ => D ^ 2 * (C + 2) * (1 + ‖s‖) ^ (-(3 : ℝ)) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by simp)).const_mul _
  refine continuousAt_of_dominated ?_ ?_ hbi ?_
  · filter_upwards [lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with t ht
    exact (hkd.mul (Complex.continuous_ofReal.comp
      (WeilHerglotz.continuous_gammaBracket.comp (continuous_id.div_const t)))).aestronglyMeasurable
  · filter_upwards [lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with t ht
    refine Eventually.of_forall fun s => ?_
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      paperFT_weilTest_ofReal_eq_normSq hf.continuous hfc]
    have h1s : 0 < 1 + |s| := by positivity
    have hst : |s / t| ≤ 2 * |s| := by
      rw [abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      nlinarith [abs_nonneg s]
    have hΩ : |EF.gammaBracket (s / t)| ≤ (C + 2) * (1 + |s|) := by
      nlinarith [hC (s / t), abs_nonneg s]
    have hsq : ‖paperFT f s‖ ^ 2 ≤ (D / (1 + |s|) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hD s) 2
    have hrpow : (1 + ‖s‖) ^ (-(3 : ℝ)) = ((1 + |s|) ^ 3)⁻¹ := by
      rw [Real.norm_eq_abs, Real.rpow_neg h1s.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    rw [hrpow]
    calc ‖paperFT f s‖ ^ 2 * |EF.gammaBracket (s / t)| ≤
          (D / (1 + |s|) ^ 2) ^ 2 * ((C + 2) * (1 + |s|)) :=
          mul_le_mul hsq hΩ (abs_nonneg _) (sq_nonneg _)
      _ = D ^ 2 * (C + 2) * ((1 + |s|) ^ 3)⁻¹ := by
          field_simp
  · refine Eventually.of_forall fun s => ?_
    have h1 : ContinuousAt (fun t : ℝ => s / t) 1 :=
      continuousAt_const.div continuousAt_id one_ne_zero
    exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      (WeilHerglotz.continuous_gammaBracket.continuousAt.comp h1))

/-- **Continuity of the pole and archimedean part under dilation**, at `t = 1`. -/
theorem tendsto_weilArchRe_comp_div {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun t : ℝ => weilArchRe (EF.weilTest (fun x => f (x / t)) (fun x => f (x / t)))) (𝓝 1)
      (𝓝 (weilArchRe (EF.weilTest f f))) := by
  have hkc : Continuous (EF.weilTest f f) :=
    (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hkcs : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hK := (WeilEF.differentiable_paperFT hkc hkcs).continuous
  set G : ℝ → ℝ := fun t => ((t : ℂ) ^ 2 * (paperFT (EF.weilTest f f) (t * (I / 2)) +
      paperFT (EF.weilTest f f) (t * (-I / 2))) + ((t / (2 * π) : ℝ) : ℂ) *
        ∫ s : ℝ, paperFT (EF.weilTest f f) s * (EF.gammaBracket (s / t) : ℂ)).re with hG
  have hGc : ContinuousAt G 1 := by
    have h1 : ContinuousAt (fun t : ℝ => (t : ℂ)) 1 := Complex.continuous_ofReal.continuousAt
    have h2 : ContinuousAt (fun t : ℝ => paperFT (EF.weilTest f f) (t * (I / 2))) 1 :=
      hK.continuousAt.comp (h1.mul continuousAt_const)
    have h3 : ContinuousAt (fun t : ℝ => paperFT (EF.weilTest f f) (t * (-I / 2))) 1 :=
      hK.continuousAt.comp (h1.mul continuousAt_const)
    have h4 : ContinuousAt (fun t : ℝ => ((t / (2 * π) : ℝ) : ℂ)) 1 :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.div_const _)
    exact Complex.continuous_re.continuousAt.comp
      (((h1.pow 2).mul (h2.add h3)).add (h4.mul (continuousAt_integral_gammaBracket_div hf hfc)))
  have hG1 : G 1 = weilArchRe (EF.weilTest f f) := by
    simp only [hG, weilArchRe, Complex.ofReal_one, one_pow, one_mul, div_one]
    congr 2
    push_cast
    ring
  have hev : G =ᶠ[𝓝 1] fun t => weilArchRe (EF.weilTest (fun x => f (x / t)) (fun x => f (x / t))) := by
    filter_upwards [lt_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [weilArchRe_comp_div f ht]
  rw [← hG1]
  exact (hGc.tendsto).congr' hev

/-! ### Prime-blind positivity at dilated nodes -/

/-- The symmetric value of the autocorrelation of `f` at `±y`. -/
def symmValue (f : WeilTestFn) (y : ℝ) : ℝ := (EF.weilTest f.1 f.1 y + EF.weilTest f.1 f.1 (-y)).re

/-- **Prime-blind positivity at the dilated nodes `±t·log n`.** -/
def PrimeBlindPositiveDilated (t : ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun f a => a * symmValue f (t * Real.log n)) = 0) →
    0 ≤ c.sum fun f a => a * weilArchRe (EF.weilTest f.1 f.1)

theorem logValue_eq_symmValue (f : WeilTestFn) (n : ℕ) :
    logValue f.1 n = symmValue f (Real.log n) / Real.sqrt n := rfl

/-- At `t = 1` the dilated condition is prime-blind positivity. -/
theorem primeBlindPositiveDilated_one_iff : PrimeBlindPositiveDilated 1 ↔ WeilOneSided.PrimeBlindPositive := by
  have key : ∀ (c : WeilTestFn →₀ ℝ) (n : ℕ), 2 ≤ n →
      ((c.sum fun f a => a * logValue f.1 n) = 0 ↔
        (c.sum fun f a => a * symmValue f (1 * Real.log n)) = 0) := by
    intro c n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    have e : (c.sum fun f a => a * logValue f.1 n) =
        (c.sum fun f a => a * symmValue f (1 * Real.log n)) / Real.sqrt n := by
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [logValue_eq_symmValue, one_mul]
      ring
    rw [e, div_eq_zero_iff, or_iff_left hs.ne']
  constructor
  · intro h c hc hnull
    exact h c hc fun n hn => (key c n hn).mp (hnull n hn)
  · intro h c hc hnull
    exact h c hc fun n hn => (key c n hn).mpr (hnull n hn)

theorem riemannHypothesis_iff_primeBlindPositiveDilated_one :
    RiemannHypothesis ↔ PrimeBlindPositiveDilated 1 :=
  riemannHypothesis_iff_primeBlindPositive_unconditional.trans primeBlindPositiveDilated_one_iff.symm

/-- **Reciprocal integers**: the nodes `(1/k)·log n` contain `log ℕ`, so `PBAP(1) ⟹ PBAP(1/k)`. -/
theorem primeBlindPositiveDilated_one_div_of_one {k : ℕ} (hk : 1 ≤ k)
    (h : PrimeBlindPositiveDilated 1) : PrimeBlindPositiveDilated (1 / k) := by
  intro c hc hnull
  refine h c hc fun m hm => ?_
  have hpow : 2 ≤ m ^ k := le_trans hm (Nat.le_self_pow (by omega) m)
  have := hnull (m ^ k) hpow
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rwa [Nat.cast_pow, Real.log_pow, show 1 / (k : ℝ) * ((k : ℝ) * Real.log m) = 1 * Real.log m by
    field_simp] at this

theorem primeBlindPositiveDilated_one_div_of_riemannHypothesis (hRH : RiemannHypothesis) {k : ℕ}
    (hk : 1 ≤ k) : PrimeBlindPositiveDilated (1 / k) :=
  primeBlindPositiveDilated_one_div_of_one hk (riemannHypothesis_iff_primeBlindPositiveDilated_one.mp hRH)

theorem symmValue_dilateTest {t : ℝ} (ht : 0 < t) (f : WeilTestFn) (y : ℝ) :
    symmValue (dilateTest t f) (t * y) = t * symmValue f y := by
  rw [symmValue, symmValue, dilateTest_apply ht.ne', weilTest_comp_div _ ht, weilTest_comp_div _ ht,
    mul_div_cancel_left₀ y ht.ne', show -(t * y) / t = -y by field_simp]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  ring

theorem mapDomain_nonneg (g : WeilTestFn → WeilTestFn) {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (f : WeilTestFn) : 0 ≤ Finsupp.mapDomain g c f := by
  classical
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  exact Finset.sum_nonneg fun x _ => by
    show 0 ≤ if g x = f then c x else 0
    split_ifs
    · exact hc x
    · exact le_rfl

/-- Dilating a blind combination by `t > 0` moves its nodes from `±y` to `±t·y`. -/
theorem sum_symmValue_mapDomain {t : ℝ} (ht : 0 < t) (c : WeilTestFn →₀ ℝ) (y : ℝ) :
    ((Finsupp.mapDomain (dilateTest t) c).sum fun f a => a * symmValue f (t * y)) =
      t * c.sum fun f a => a * symmValue f y := by
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [symmValue_dilateTest ht]
  ring

theorem sum_weilArchRe_mapDomain (t : ℝ) (c : WeilTestFn →₀ ℝ) :
    ((Finsupp.mapDomain (dilateTest t) c).sum fun f a => a * weilArchRe (EF.weilTest f.1 f.1)) =
      c.sum fun f a => a * weilArchRe (EF.weilTest (dilateTest t f).1 (dilateTest t f).1) :=
  Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- **Dilation continuity.**  If prime-blind positivity holds at the dilated nodes along some
sequence `t_k → 1`, it holds at `t = 1`. -/
theorem primeBlindPositive_of_tendsto {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 1))
    (h : ∀ k, PrimeBlindPositiveDilated (t k)) : WeilOneSided.PrimeBlindPositive := by
  intro c hc hnull
  have hpos : ∀ᶠ k in atTop, 0 < t k := ht.eventually (lt_mem_nhds one_pos)
  -- every dilated combination is blind at the dilated nodes, hence nonnegative
  have hnn : ∀ᶠ k in atTop,
      0 ≤ c.sum fun f a => a * weilArchRe (EF.weilTest (dilateTest (t k) f).1 (dilateTest (t k) f).1) := by
    filter_upwards [hpos] with k hk
    rw [← sum_weilArchRe_mapDomain]
    refine h k _ (mapDomain_nonneg _ hc) fun n hn => ?_
    rw [sum_symmValue_mapDomain hk]
    have h0 := hnull n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    have e : (c.sum fun f a => a * logValue f.1 n) =
        (c.sum fun f a => a * symmValue f (Real.log n)) / Real.sqrt n := by
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun f _ => by rw [logValue_eq_symmValue]; ring
    rw [e, div_eq_zero_iff, or_iff_left hs.ne'] at h0
    rw [h0, mul_zero]
  -- and the dilated values converge to the undilated ones
  have hlim : Tendsto (fun k =>
      c.sum fun f a => a * weilArchRe (EF.weilTest (dilateTest (t k) f).1 (dilateTest (t k) f).1))
      atTop (𝓝 (c.sum fun f a => a * weilArchRe (EF.weilTest f.1 f.1))) := by
    refine tendsto_finsetSum _ fun f _ => (tendsto_const_nhds.mul ?_)
    have h1 := (tendsto_weilArchRe_comp_div f.2.1 f.2.2).comp ht
    refine h1.congr' ?_
    filter_upwards [hpos] with k hk
    simp only [Function.comp_apply]
    rw [dilateTest_apply hk.ne']
  exact ge_of_tendsto hlim hnn

/-- **RH from dilated nodes accumulating at `1`.** -/
theorem riemannHypothesis_of_tendsto {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 1))
    (h : ∀ k, PrimeBlindPositiveDilated (t k)) : RiemannHypothesis :=
  riemannHypothesis_iff_primeBlindPositive_unconditional.mpr (primeBlindPositive_of_tendsto ht h)

/-- RH holds iff the set of good dilation parameters accumulates at `1`. -/
theorem riemannHypothesis_iff_exists_tendsto :
    RiemannHypothesis ↔ ∃ t : ℕ → ℝ, Tendsto t atTop (𝓝 1) ∧ ∀ k, PrimeBlindPositiveDilated (t k) :=
  ⟨fun hRH => ⟨fun _ => 1, tendsto_const_nhds, fun _ =>
      riemannHypothesis_iff_primeBlindPositiveDilated_one.mp hRH⟩,
    fun ⟨_, ht, h⟩ => riemannHypothesis_of_tendsto ht h⟩

/-! ### Dilated data -/

/-- The `t`-dilated pole and archimedean datum:
`A_t(f) = Re(t²(k̂(ti/2) + k̂(−ti/2)) + (t/2π)∫ k̂(s) Ω(s/t) ds)`. -/
def dilatedArch (t : ℝ) (f : WeilTestFn) : ℝ :=
  ((t : ℂ) ^ 2 * (paperFT (EF.weilTest f.1 f.1) (t * (I / 2)) +
      paperFT (EF.weilTest f.1 f.1) (t * (-I / 2))) +
    ((t / (2 * π) : ℝ) : ℂ) * ∫ s : ℝ, paperFT (EF.weilTest f.1 f.1) s * (EF.gammaBracket (s / t) : ℂ)).re

theorem weilArchRe_dilateTest {t : ℝ} (ht : 0 < t) (f : WeilTestFn) :
    weilArchRe (EF.weilTest (dilateTest t f).1 (dilateTest t f).1) = dilatedArch t f := by
  rw [dilateTest_apply ht.ne', weilArchRe_comp_div _ ht, dilatedArch]

theorem dilateTest_dilateTest {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (f : WeilTestFn) :
    dilateTest s (dilateTest t f) = dilateTest (s * t) f := by
  apply Subtype.ext
  rw [dilateTest_apply hs, dilateTest_apply ht, dilateTest_apply (mul_ne_zero hs ht)]
  funext x
  simp only [div_div]

theorem dilateTest_one (f : WeilTestFn) : dilateTest 1 f = f := by
  apply Subtype.ext
  rw [dilateTest_apply one_ne_zero]
  simp

/-- **`PBAP(t)` is blind positivity of the dilated datum `A_t` at the original nodes `log n`.** -/
theorem primeBlindPositiveDilated_iff {t : ℝ} (ht : 0 < t) :
    PrimeBlindPositiveDilated t ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
        (∀ n : ℕ, 2 ≤ n → (c.sum fun f a => a * symmValue f (Real.log n)) = 0) →
        0 ≤ c.sum fun f a => a * dilatedArch t f := by
  constructor
  · intro h c hc hnull
    have := h (Finsupp.mapDomain (dilateTest t) c) (mapDomain_nonneg _ hc) fun n hn => by
      rw [sum_symmValue_mapDomain ht, hnull n hn, mul_zero]
    rw [sum_weilArchRe_mapDomain] at this
    refine this.trans (le_of_eq ?_)
    rw [Finsupp.sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun f _ => by rw [weilArchRe_dilateTest ht]
  · intro h c hc hnull
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    have := h (Finsupp.mapDomain (dilateTest t⁻¹) c) (mapDomain_nonneg _ hc) fun n hn => by
      have e := sum_symmValue_mapDomain hinv c (t * Real.log n)
      rw [inv_mul_cancel_left₀ ht.ne', hnull n hn, mul_zero] at e
      exact e
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at this
    refine this.trans (le_of_eq ?_)
    rw [Finsupp.sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← weilArchRe_dilateTest ht, dilateTest_dilateTest ht.ne' (inv_ne_zero ht.ne'),
      mul_inv_cancel₀ ht.ne', dilateTest_one]

/-- **Density of the half-dilated datum**: `Ω(2r) = log 2 + ½(D_{−1/4}(r) + D_{3/4}(r))`, where
`D_μ(r) = Re ψ((½ + μ)/2 + ir/2) − log π` is the archimedean density of `Γℝ(s + μ)`. -/
theorem gammaBracket_two_mul (r : ℝ) :
    EF.gammaBracket (2 * r) = Real.log 2 +
      (((Complex.digamma (1 / 8 + I * r / 2)).re - Real.log π) +
        ((Complex.digamma (5 / 8 + I * r / 2)).re - Real.log π)) / 2 := by
  have hcond : ∀ n : ℕ, 2 * (1 / 8 + I * r / 2) ≠ -(n : ℂ) := fun n h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hdup := HTGeometry.digamma_duplication (1 / 8 + I * r / 2) hcond
  have e1 : 2 * (1 / 8 + I * r / 2) = 1 / 4 + I * ((2 * r : ℝ) : ℂ) / 2 := by push_cast; ring
  have e2 : (1 / 8 + I * r / 2) + 1 / 2 = 5 / 8 + I * r / 2 := by ring
  rw [e1, e2] at hdup
  have hre := congrArg Complex.re hdup
  have hlog : (Complex.log 2).re = Real.log 2 := by
    rw [Complex.log_re]; norm_num
  simp only [Complex.mul_re, Complex.add_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, hlog] at hre
  rw [EF.gammaBracket]
  linarith

/-- **The weight-½ (theta) gamma factor**: `Γℝ(s − ¼) Γℝ(s + ¾) = Γℂ(s − ¼)`. -/
theorem Gammaℝ_sub_quarter_mul (s : ℂ) :
    Complex.Gammaℝ (s - 1 / 4) * Complex.Gammaℝ (s + 3 / 4) = Complex.Gammaℂ (s - 1 / 4) := by
  rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one (s - 1 / 4)]
  congr 2
  ring

/-- **`PBAP(½)` is blind positivity for the half-dilated (theta) datum**: pole weight `¼` at
`±i/4` and archimedean density `Ω(2s)` on the half-scaled spectrum. -/
theorem primeBlindPositiveDilated_half_iff :
    PrimeBlindPositiveDilated (1 / 2) ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
        (∀ n : ℕ, 2 ≤ n → (c.sum fun f a => a * symmValue f (Real.log n)) = 0) →
        0 ≤ c.sum fun f a => a * ((1 / 4 : ℂ) * (paperFT (EF.weilTest f.1 f.1) (I / 4) +
            paperFT (EF.weilTest f.1 f.1) (-I / 4)) +
          ((1 / (4 * π) : ℝ) : ℂ) *
            ∫ s : ℝ, paperFT (EF.weilTest f.1 f.1) s * (EF.gammaBracket (2 * s) : ℂ)).re := by
  rw [primeBlindPositiveDilated_iff (by norm_num : (0 : ℝ) < 1 / 2)]
  have e : ∀ f : WeilTestFn, dilatedArch (1 / 2) f =
      ((1 / 4 : ℂ) * (paperFT (EF.weilTest f.1 f.1) (I / 4) + paperFT (EF.weilTest f.1 f.1) (-I / 4)) +
        ((1 / (4 * π) : ℝ) : ℂ) *
          ∫ s : ℝ, paperFT (EF.weilTest f.1 f.1) s * (EF.gammaBracket (2 * s) : ℂ)).re := by
    intro f
    rw [dilatedArch]
    have h1 : (((1 / 2 : ℝ) : ℂ)) ^ 2 = 1 / 4 := by push_cast; norm_num
    have h2 : (((1 / 2 : ℝ) : ℂ)) * (I / 2) = I / 4 := by push_cast; ring
    have h3 : (((1 / 2 : ℝ) : ℂ)) * (-I / 2) = -I / 4 := by push_cast; ring
    have h4 : ((1 / 2 / (2 * π) : ℝ)) = 1 / (4 * π) := by ring
    have h5 : ∀ s : ℝ, s / (1 / 2) = 2 * s := fun s => by ring
    simp_rw [h1, h2, h3, h4, h5]
  simp_rw [e]

end

end RHTower.NodeDilation
