import GaloisForLFunctions.BiScaleUncertainty.HyperbolicGaugeChebyshevEnergyRepresentation

/-!
# The causal exponential response and the Laplace Gram energy of the signed prime–polar measure

Let `ν_N = Σ_{n ≤ N+2} Λ(n) n^{-1/2} δ_{log n} − 2cosh(t/2) 1_{[0,L]} dt` be the signed prime–polar
measure of cutoff `L = log(N+2)`, read through the field's pairing `pairing N h = ∫ h dν_N`, and let
`K(x) = e^{−x/2} 1_{x ≥ 0}` be the causal exponential kernel.  The causal response
`(K ⋆ ν_N)(t) = pairing N (K(t − ·))` is explicit:

* on the window `0 ≤ t ≤ L` it is the normalized Chebyshev error plus a universal transient,
  `(K ⋆ ν_N)(t) = e^{−t/2}(ψ(e^t) − e^t) + (1 − t) e^{−t/2}`;
* it vanishes for `t < 0` and decays as `e^{−(t−L)/2} (K ⋆ ν_N)(L)` beyond the cutoff.

The autocorrelation of the causal kernel is the Laplace kernel, `∫ K(t−a) K(t−b) dt = e^{−|a−b|/2}`,
so the `L²` norm of the response is the Gram energy of `ν_N` against the Laplace kernel:

`∫_ℝ (K ⋆ ν_N)² = ∬ e^{−|s−t|/2} dν_N(s) dν_N(t) =: laplaceEnergy N`.

Consequently

`laplaceEnergy N = ∫_0^L (Ẽ(t) + (1 − t)e^{−t/2})² dt + (Ẽ(L) + (1 − L)e^{−L/2})²`,

and the mean-square normalized Chebyshev error `∫_0^L Ẽ²` and `laplaceEnergy N` control each other up
to a factor `2` and additive constants.  Thus the square-root barrier for the Chebyshev function is,
inside the field, the growth of the Gram energy of the signed prime–polar measure against the
positive-definite Laplace kernel, the same kind of object as the packet energy
`∬ autocorr f (s − t) dν_N dν_N` of a compact source.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The causal kernel and the Laplace kernel -/

/-- The causal exponential kernel `K(x) = e^{−x/2}` for `x ≥ 0`, and `0` for `x < 0`. -/
def causalKernel (x : ℝ) : ℝ := if 0 ≤ x then Real.exp (-x / 2) else 0

/-- The Laplace kernel `e^{−|x|/2}`. -/
def laplaceKernel (x : ℝ) : ℝ := Real.exp (-|x| / 2)

theorem causalKernel_nonneg (x : ℝ) : 0 ≤ causalKernel x := by
  unfold causalKernel; split_ifs <;> positivity

theorem causalKernel_le_one (x : ℝ) : causalKernel x ≤ 1 := by
  unfold causalKernel
  split_ifs with h
  · rw [Real.exp_le_one_iff]; linarith
  · exact zero_le_one

theorem abs_causalKernel_le_one (x : ℝ) : |causalKernel x| ≤ 1 := by
  rw [abs_of_nonneg (causalKernel_nonneg x)]; exact causalKernel_le_one x

theorem causalKernel_of_nonneg {x : ℝ} (hx : 0 ≤ x) : causalKernel x = Real.exp (-x / 2) := by
  unfold causalKernel; rw [if_pos hx]

theorem causalKernel_of_neg {x : ℝ} (hx : x < 0) : causalKernel x = 0 := by
  unfold causalKernel; rw [if_neg (not_le.2 hx)]

theorem causalKernel_eq_indicator :
    causalKernel = (Ici (0 : ℝ)).indicator fun x => Real.exp (-x / 2) := by
  funext x
  unfold causalKernel
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, Set.indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
  · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]

theorem measurable_causalKernel : Measurable causalKernel := by
  rw [causalKernel_eq_indicator]
  exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).indicator measurableSet_Ici

theorem integrable_causalKernel : Integrable causalKernel := by
  rw [causalKernel_eq_indicator]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ici
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := exp_neg_integrableOn_Ioi (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only; congr 1; ring

theorem integral_Ioi_exp_neg_shift (c : ℝ) :
    (∫ t in Ioi c, Real.exp (-(t - c))) = 1 := by
  have h := integral_exp_neg_Ioi c
  have : (fun t : ℝ => Real.exp (-(t - c))) = fun t => Real.exp c * Real.exp (-t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [this, integral_const_mul, h, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- **The Laplace kernel is the autocorrelation of the causal kernel:**
`∫ K(t − a) K(t − b) dt = e^{−|a−b|/2}`. -/
theorem integral_causalKernel_mul (a b : ℝ) :
    (∫ t, causalKernel (t - a) * causalKernel (t - b)) = laplaceKernel (a - b) := by
  -- reduce to `a ≤ b`
  suffices key : ∀ a b : ℝ, a ≤ b →
      (∫ t, causalKernel (t - a) * causalKernel (t - b)) = laplaceKernel (a - b) by
    rcases le_total a b with h | h
    · exact key a b h
    · have := key b a h
      rw [show (fun t => causalKernel (t - a) * causalKernel (t - b)) =
          fun t => causalKernel (t - b) * causalKernel (t - a) from funext fun t => mul_comm _ _,
        this, laplaceKernel, laplaceKernel, abs_sub_comm]
  intro a b hab
  have hcongr : ∀ᵐ t ∂(volume : Measure ℝ), causalKernel (t - a) * causalKernel (t - b) =
      (Ioi b).indicator (fun t => Real.exp ((a + b) / 2) * Real.exp (-t)) t := by
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by rw [ae_iff]; simp
    filter_upwards [hne] with t ht
    by_cases htb : b < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi b from htb), causalKernel_of_nonneg (by linarith),
        causalKernel_of_nonneg (by linarith), ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    · have htb' : t < b := lt_of_le_of_ne (not_lt.1 htb) ht
      rw [Set.indicator_of_notMem (show t ∉ Ioi b from not_lt.2 htb'.le),
        causalKernel_of_neg (x := t - b) (by linarith), mul_zero]
  rw [integral_congr_ae hcongr, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_neg_Ioi, laplaceKernel, abs_of_nonpos (by linarith), ← Real.exp_add]
  congr 1; ring

/-- The Laplace kernel is the autocorrelation of the causal kernel in the field's sense. -/
theorem autocorr_causalKernel (x : ℝ) : autocorr causalKernel x = laplaceKernel x := by
  have h := integral_causalKernel_mul 0 (-x)
  unfold autocorr
  rw [show laplaceKernel x = laplaceKernel (0 - -x) by rw [zero_sub, neg_neg], ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show causalKernel t * causalKernel (t + x) = causalKernel (t - 0) * causalKernel (t - -x)
  rw [sub_zero, sub_neg_eq_add]

/-! ## Elementary pairing calculus -/

theorem pairing_const_mul (N : ℕ) (c : ℝ) (h : ℝ → ℝ) :
    pairing N (fun s => c * h s) = c * pairing N h := by
  unfold pairing
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun n _ => by ring
  · rw [← integral_const_mul c (fun x => polarDensity x * h x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)

theorem pairing_mul_const (N : ℕ) (c : ℝ) (h : ℝ → ℝ) :
    pairing N (fun s => h s * c) = pairing N h * c := by
  have h1 : (fun s => h s * c) = fun s => c * h s := funext fun s => mul_comm _ _
  calc pairing N (fun s => h s * c) = pairing N (fun s => c * h s) := congrArg (pairing N) h1
    _ = c * pairing N h := pairing_const_mul N c h
    _ = pairing N h * c := mul_comm _ _

/-- The pairing only reads its argument on the window `[0, L]`. -/
theorem pairing_congr_window (N : ℕ) {h h' : ℝ → ℝ}
    (hh : ∀ s ∈ Icc (0 : ℝ) (cutoff N), h s = h' s) : pairing N h = pairing N h' := by
  unfold pairing
  congr 1
  · exact Finset.sum_congr rfl fun n hn => by
      rw [hh _ ⟨(node_bounds N n hn).1, (node_bounds N n hn).2⟩]
  · exact setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hh s hs]

/-! ## The causal response -/

/-- The causal response `(K ⋆ ν_N)(t) = pairing N (K(t − ·))`. -/
def causalResponse (N : ℕ) (t : ℝ) : ℝ := pairing N fun s => causalKernel (t - s)

theorem primeWeight_mul_causalKernel {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    primeWeight n * causalKernel (t - Real.log n) =
      Real.exp (-t / 2) * (if Real.log (n : ℝ) ≤ t then ArithmeticFunction.vonMangoldt n else 0) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold primeWeight causalKernel
  by_cases h : Real.log (n : ℝ) ≤ t
  · rw [if_pos (by linarith), if_pos h]
    have hsq : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
    have he : Real.exp (-(t - Real.log (n : ℝ)) / 2) = Real.exp (-t / 2) * Real.sqrt n := by
      rw [← exp_half_log_eq_sqrt hn0, ← Real.exp_add]; congr 1; ring
    rw [he]
    field_simp
  · rw [if_neg (by linarith), if_neg h]; ring

/-- **The response on the window is the normalized Chebyshev error plus the universal transient.** -/
theorem causalResponse_eq_on_window (N : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ cutoff N) :
    causalResponse N t = normalizedLogError t + (1 - t) * Real.exp (-t / 2) := by
  unfold causalResponse pairing
  -- the atomic part
  have hatom : (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * causalKernel (t - Real.log n)) =
      Real.exp (-t / 2) * Chebyshev.psi (Real.exp t) := by
    rw [← step_eq N htL, step, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n hn => primeWeight_mul_causalKernel (Finset.mem_Icc.mp hn).1 t
  -- the polar part
  have hpolar : (∫ s in Icc 0 (cutoff N), polarDensity s * causalKernel (t - s)) =
      Real.exp (-t / 2) * (Real.exp t - 1 + t) := by
    have hvan : ∀ s ∈ Icc 0 (cutoff N) \ Icc 0 t, polarDensity s * causalKernel (t - s) = 0 := by
      intro s hs
      have : t < s := by
        by_contra h
        push Not at h
        exact hs.2 ⟨hs.1.1, h⟩
      rw [causalKernel_of_neg (x := t - s) (by linarith), mul_zero]
    have hsub : (∫ s in Icc 0 (cutoff N), polarDensity s * causalKernel (t - s)) =
        ∫ s in Icc 0 t, polarDensity s * causalKernel (t - s) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
        (Icc_subset_Icc_right htL) hvan
    have hcongr : ∀ s ∈ Icc (0 : ℝ) t, polarDensity s * causalKernel (t - s) =
        Real.exp (-t / 2) * (Real.exp s + 1) := by
      intro s hs
      rw [causalKernel_of_nonneg (by linarith [hs.2]), polarDensity, Real.cosh_eq]
      have h1 : Real.exp (-(t - s) / 2) = Real.exp (-t / 2) * Real.exp (s / 2) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp (s / 2) * Real.exp (s / 2) = Real.exp s := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
        rw [← Real.exp_add]; simp
      rw [h1]
      linear_combination (Real.exp (-t / 2)) * h2 + (Real.exp (-t / 2)) * h3
    rw [hsub, setIntegral_congr_fun measurableSet_Icc hcongr, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht0]
    congr 1
    rw [intervalIntegral.integral_add (Real.continuous_exp.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), integral_exp, intervalIntegral.integral_const]
    simp only [Real.exp_zero, smul_eq_mul, sub_zero, mul_one]
  rw [hatom, hpolar]
  unfold normalizedLogError logError
  ring

theorem causalResponse_eq_zero_of_neg (N : ℕ) {t : ℝ} (ht : t < 0) : causalResponse N t = 0 := by
  unfold causalResponse
  rw [pairing_congr_window N (h' := fun _ => (0 : ℝ)) (fun s hs => by
    rw [causalKernel_of_neg (by linarith [hs.1])])]
  unfold pairing
  simp

/-- Beyond the cutoff the response decays exponentially from its cutoff value. -/
theorem causalResponse_tail (N : ℕ) {t : ℝ} (ht : cutoff N ≤ t) :
    causalResponse N t = Real.exp (-(t - cutoff N) / 2) * causalResponse N (cutoff N) := by
  unfold causalResponse
  rw [← pairing_const_mul]
  refine pairing_congr_window N fun s hs => ?_
  rw [causalKernel_of_nonneg (by linarith [hs.2]), causalKernel_of_nonneg (by linarith [hs.2]),
    ← Real.exp_add]
  congr 1; ring

/-- Uniform exponential bound: `|K ⋆ ν_N| ≤ mass N · e^{L/2} · K`. -/
theorem abs_causalResponse_le (N : ℕ) (t : ℝ) :
    |causalResponse N t| ≤ mass N * Real.exp (cutoff N / 2) * causalKernel t := by
  by_cases ht : t < 0
  · rw [causalResponse_eq_zero_of_neg N ht, abs_zero, causalKernel_of_neg ht, mul_zero]
  · push Not at ht
    unfold causalResponse
    rw [pairing_congr_window N (h' := (Icc (0 : ℝ) (cutoff N)).indicator fun s =>
      causalKernel (t - s)) (fun s hs => by rw [Set.indicator_of_mem hs]), mul_assoc]
    refine abs_pairing_le_mass_mul N _ _ fun s => ?_
    by_cases hs : s ∈ Icc (0 : ℝ) (cutoff N)
    · rw [Set.indicator_of_mem hs, abs_of_nonneg (causalKernel_nonneg _),
        causalKernel_of_nonneg ht]
      by_cases hts : s ≤ t
      · rw [causalKernel_of_nonneg (by linarith)]
        have : Real.exp (-(t - s) / 2) = Real.exp (s / 2) * Real.exp (-t / 2) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hs.2])) (Real.exp_pos _).le
      · rw [causalKernel_of_neg (by linarith)]; positivity
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact mul_nonneg (Real.exp_pos _).le (causalKernel_nonneg _)

theorem measurable_causalResponse (N : ℕ) : Measurable (causalResponse N) := by
  unfold causalResponse pairing
  refine Measurable.sub ?_ ?_
  · exact Finset.measurable_sum _ fun n _ =>
      measurable_const.mul (measurable_causalKernel.comp (measurable_id.sub_const _))
  · have hm : Measurable fun p : ℝ × ℝ => polarDensity p.2 * causalKernel (p.1 - p.2) :=
      (continuous_polarDensity.measurable.comp measurable_snd).mul
        (measurable_causalKernel.comp (measurable_fst.sub measurable_snd))
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Icc 0 (cutoff N)))).measurable

theorem integrable_causalResponse (N : ℕ) : Integrable (causalResponse N) := by
  refine Integrable.mono' (integrable_causalKernel.const_mul (mass N * Real.exp (cutoff N / 2)))
    (measurable_causalResponse N).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  exact abs_causalResponse_le N t

theorem integrable_sq_causalKernel : Integrable fun x => causalKernel x ^ 2 := by
  have : (fun x => causalKernel x ^ 2) = (Ici (0 : ℝ)).indicator fun x => Real.exp (-x) := by
    funext x
    unfold causalKernel
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), sq, ← Real.exp_add]
      congr 1; ring
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), zero_pow two_ne_zero]
  rw [this]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ici
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_neg_Ioi 0

theorem integrable_sq_causalResponse (N : ℕ) : Integrable fun t => causalResponse N t ^ 2 := by
  refine Integrable.mono' (integrable_sq_causalKernel.const_mul
    ((mass N * Real.exp (cutoff N / 2)) ^ 2))
    ((measurable_causalResponse N).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_causalResponse_le N t) 2

/-! ## Integrating a pairing against the line -/

theorem polarDensity_le_window {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) L) :
    polarDensity s ≤ 2 * Real.cosh (L / 2) := by
  unfold polarDensity
  have h1 : |s / 2| ≤ |L / 2| := by
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith [hs.1, hs.2])]
    linarith [hs.2]
  have := Real.cosh_le_cosh.2 h1
  linarith

/-- **Exchange of the pairing with a dominated line integral.**  If `|F t s| ≤ |w t| C` with `w`
integrable, then `∫ t, pairing N (F t ·) = pairing N (fun s => ∫ t, F t s)`. -/
theorem integral_pairing_of_dominated (N : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Measurable (Function.uncurry F)) {w : ℝ → ℝ} (hw : Integrable w) {C : ℝ}
    (hb : ∀ t s, |F t s| ≤ |w t| * C) :
    (∫ t, pairing N fun s => F t s) = pairing N fun s => ∫ t, F t s := by
  set Cp : ℝ := 2 * Real.cosh (cutoff N / 2) with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  -- the atoms
  have hatom : ∀ n : ℕ, Integrable fun t => primeWeight n * F t (Real.log n) := by
    intro n
    refine ((hw.norm.mul_const C).const_mul (primeWeight n)).mono'
      (((hF.comp (measurable_id.prodMk measurable_const))).const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeWeight_nonneg n), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb t _) (primeWeight_nonneg n)
  -- the polar part, with the window indicator built in
  set pw : ℝ → ℝ := (Icc 0 (cutoff N)).indicator polarDensity with hpw
  have hpwb : ∀ s, |pw s| ≤ Cp := by
    intro s
    by_cases hs : s ∈ Icc 0 (cutoff N)
    · rw [hpw, Set.indicator_of_mem hs, abs_of_nonneg (polarDensity_nonneg s)]
      exact polarDensity_le_window hs
    · rw [hpw, Set.indicator_of_notMem hs, abs_zero]; exact hCp0
  have hpwm : Measurable pw := continuous_polarDensity.measurable.indicator measurableSet_Icc
  have hprod : Integrable (Function.uncurry fun t s => pw s * F t s)
      (volume.prod (volume.restrict (Icc 0 (cutoff N)))) := by
    refine Integrable.mono' ((hw.norm.mul_const (C * Cp)).mul_prod
      (integrable_const (1 : ℝ) (μ := volume.restrict (Icc 0 (cutoff N))))) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hpwm.comp measurable_snd).mul hF).aestronglyMeasurable
    · show |pw p.2 * F p.1 p.2| ≤ ‖w p.1‖ * (C * Cp) * 1
      rw [abs_mul, Real.norm_eq_abs, mul_one]
      calc |pw p.2| * |F p.1 p.2| ≤ Cp * (|w p.1| * C) :=
            mul_le_mul (hpwb _) (hb _ _) (abs_nonneg _) hCp0
        _ = |w p.1| * (C * Cp) := by ring
  have hpolar_eq : ∀ t, (∫ s in Icc 0 (cutoff N), polarDensity s * F t s) =
      ∫ s in Icc 0 (cutoff N), pw s * F t s :=
    fun t => setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hpw, Set.indicator_of_mem hs]
  have hpolar_int : Integrable fun t => ∫ s in Icc 0 (cutoff N), pw s * F t s :=
    hprod.integral_prod_left
  have hswap : (∫ t, ∫ s in Icc 0 (cutoff N), pw s * F t s) =
      ∫ s in Icc 0 (cutoff N), ∫ t, pw s * F t s :=
    integral_integral_swap hprod
  -- assemble
  have hsum_int : Integrable fun t => ∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * F t (Real.log n) :=
    integrable_finsetSum _ fun n _ => hatom n
  calc (∫ t, pairing N fun s => F t s)
      = ∫ t, ((∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * F t (Real.log n)) -
          ∫ s in Icc 0 (cutoff N), pw s * F t s) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        show pairing N (fun s => F t s) = _
        unfold pairing
        simp only
        rw [hpolar_eq t]
    _ = (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * ∫ t, F t (Real.log n)) -
          ∫ s in Icc 0 (cutoff N), polarDensity s * ∫ t, F t s := by
        rw [integral_sub hsum_int hpolar_int, integral_finsetSum _ fun n _ => hatom n, hswap]
        congr 1
        · exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _
        · refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          rw [integral_const_mul, hpw, Set.indicator_of_mem hs]
    _ = _ := rfl

/-! ## The Laplace Gram energy -/

/-- The Gram energy of the signed prime–polar measure against the Laplace kernel. -/
def laplaceEnergy (N : ℕ) : ℝ :=
  pairing N fun t => pairing N fun s => laplaceKernel (s - t)

/-- **The `L²` norm of the causal response is the Laplace Gram energy.** -/
theorem integral_sq_causalResponse_eq_laplaceEnergy (N : ℕ) :
    (∫ t, causalResponse N t ^ 2) = laplaceEnergy N := by
  have hR := integrable_causalResponse N
  have hRm := measurable_causalResponse N
  have h1 : ∀ t, causalResponse N t ^ 2 =
      pairing N fun s => causalResponse N t * causalKernel (t - s) := by
    intro t
    rw [pairing_const_mul, sq]
    rfl
  have h2 : (∫ t, pairing N fun s => causalResponse N t * causalKernel (t - s)) =
      pairing N fun s => ∫ t, causalResponse N t * causalKernel (t - s) := by
    refine integral_pairing_of_dominated N _ ?_ hR.abs (C := 1) fun t s => ?_
    · exact (hRm.comp measurable_fst).mul (measurable_causalKernel.comp (measurable_fst.sub measurable_snd))
    · rw [abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left (abs_causalKernel_le_one _) (abs_nonneg _)
  have h3 : ∀ s, (∫ t, causalResponse N t * causalKernel (t - s)) =
      pairing N fun s' => laplaceKernel (s' - s) := by
    intro s
    have e1 : ∀ t, causalResponse N t * causalKernel (t - s) =
        pairing N fun s' => causalKernel (t - s') * causalKernel (t - s) := fun t => by
      rw [pairing_mul_const]; rfl
    have e2 : (∫ t, pairing N fun s' => causalKernel (t - s') * causalKernel (t - s)) =
        pairing N fun s' => ∫ t, causalKernel (t - s') * causalKernel (t - s) := by
      refine integral_pairing_of_dominated N _ ?_
        (integrable_causalKernel.comp_sub_right s) (C := 1) fun t s' => ?_
      · exact (measurable_causalKernel.comp (measurable_fst.sub measurable_snd)).mul
          (measurable_causalKernel.comp (measurable_fst.sub_const s))
      · rw [abs_mul, mul_comm, mul_one]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_causalKernel_le_one _)
    rw [show (fun t => causalResponse N t * causalKernel (t - s)) =
      fun t => pairing N fun s' => causalKernel (t - s') * causalKernel (t - s) from funext e1, e2]
    exact congrArg (pairing N) (funext fun s' => integral_causalKernel_mul s' s)
  calc (∫ t, causalResponse N t ^ 2)
      = ∫ t, pairing N fun s => causalResponse N t * causalKernel (t - s) := by
        exact integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = pairing N fun s => ∫ t, causalResponse N t * causalKernel (t - s) := h2
    _ = laplaceEnergy N := congrArg (pairing N) (funext h3)

theorem laplaceEnergy_nonneg (N : ℕ) : 0 ≤ laplaceEnergy N := by
  rw [← integral_sq_causalResponse_eq_laplaceEnergy]
  exact integral_nonneg fun t => sq_nonneg _

/-! ## The window decomposition of the Laplace energy -/

/-- The response energy splits into the window `[0, L]` and the exponential tail. -/
theorem integral_sq_causalResponse_eq_window_add_tail (N : ℕ) :
    (∫ t, causalResponse N t ^ 2) =
      (∫ t in Icc 0 (cutoff N), (normalizedLogError t + (1 - t) * Real.exp (-t / 2)) ^ 2) +
        causalResponse N (cutoff N) ^ 2 := by
  set L := cutoff N with hL
  have hint := integrable_sq_causalResponse N
  have hsplit := integral_add_compl (μ := volume) measurableSet_Ioi (f := fun t => causalResponse N t ^ 2)
    (s := Ioi L) hint
  rw [compl_Ioi] at hsplit
  -- the window part
  have hvan : ∀ t ∈ Iic L \ Icc 0 L, causalResponse N t ^ 2 = 0 := by
    intro t ht
    have : t < 0 := by
      by_contra h
      push Not at h
      exact ht.2 ⟨h, ht.1⟩
    rw [causalResponse_eq_zero_of_neg N this, zero_pow two_ne_zero]
  have hwin : (∫ t in Iic L, causalResponse N t ^ 2) =
      ∫ t in Icc 0 L, (normalizedLogError t + (1 - t) * Real.exp (-t / 2)) ^ 2 := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Icc_subset_Iic_self hvan]
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [causalResponse_eq_on_window N ht.1 ht.2]
  -- the tail part
  have htail : (∫ t in Ioi L, causalResponse N t ^ 2) = causalResponse N L ^ 2 := by
    have hcongr : ∀ t ∈ Ioi L, causalResponse N t ^ 2 =
        causalResponse N L ^ 2 * Real.exp (-(t - L)) := by
      intro t ht
      have he : Real.exp (-(t - L) / 2) ^ 2 = Real.exp (-(t - L)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [causalResponse_tail N (le_of_lt ht), mul_pow, he]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_Ioi_exp_neg_shift, mul_one]
  rw [← hsplit, hwin, htail, add_comm]

/-- **The Laplace Gram energy is the transient-corrected mean-square Chebyshev error.** -/
theorem laplaceEnergy_eq_window_add_tail (N : ℕ) :
    laplaceEnergy N =
      (∫ t in Icc 0 (cutoff N), (normalizedLogError t + (1 - t) * Real.exp (-t / 2)) ^ 2) +
        (normalizedLogError (cutoff N) + (1 - cutoff N) * Real.exp (-cutoff N / 2)) ^ 2 := by
  rw [← integral_sq_causalResponse_eq_laplaceEnergy, integral_sq_causalResponse_eq_window_add_tail,
    causalResponse_eq_on_window N (cutoff_nonneg N) le_rfl]

/-- The transient has total energy at most `1`: `∫_0^L (1−t)² e^{−t} dt = 1 − (L²+1)e^{−L}`. -/
theorem integral_transient_sq_le {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in Icc 0 L, ((1 - t) * Real.exp (-t / 2)) ^ 2) ≤ 1 := by
  have hfun : ∀ t : ℝ, ((1 - t) * Real.exp (-t / 2)) ^ 2 = (1 - t) ^ 2 * Real.exp (-t) := by
    intro t
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -Real.exp (-t) * (t ^ 2 + 1)) ((1 - t) ^ 2 * Real.exp (-t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (Real.exp (-t)) t := by
      have h0 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
        ((hasDerivAt_neg t).exp).neg
      exact h0.congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const 1
    refine (h1.mul h2).congr_deriv ?_
    ring
  simp_rw [hfun]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((((continuous_const.sub continuous_id).pow 2).mul
        (Real.continuous_exp.comp continuous_neg)).intervalIntegrable _ _)]
  have : 0 ≤ Real.exp (-L) * (L ^ 2 + 1) := by positivity
  simp only [neg_zero, Real.exp_zero]
  linarith

/-- **Two-sided comparison of the Laplace energy with the mean-square Chebyshev error.** -/
theorem chebyshev_mean_square_le_laplaceEnergy (N : ℕ) :
    (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) ≤ 2 * laplaceEnergy N + 2 := by
  set L := cutoff N with hL
  have hL0 : 0 ≤ L := cutoff_nonneg N
  set T : ℝ → ℝ := fun t => (1 - t) * Real.exp (-t / 2) with hT
  have hTc : Continuous T := by rw [hT]; fun_prop
  have hE2 := integrableOn_normalizedLogError_sq L
  have hT2 : IntegrableOn (fun t => T t ^ 2) (Icc 0 L) := (hTc.pow 2).integrableOn_Icc
  have hET2 : IntegrableOn (fun t => (normalizedLogError t + T t) ^ 2) (Icc 0 L) := by
    refine ((hE2.add hT2).const_mul 2).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact ((measurable_normalizedLogError.add hTc.measurable).pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (normalizedLogError t - T t)]
  have hpt : ∀ t, normalizedLogError t ^ 2 ≤ 2 * (normalizedLogError t + T t) ^ 2 + 2 * T t ^ 2 :=
    fun t => by nlinarith [sq_nonneg (normalizedLogError t + 2 * T t)]
  have h1 : (∫ t in Icc 0 L, normalizedLogError t ^ 2) ≤
      ∫ t in Icc 0 L, (2 * (normalizedLogError t + T t) ^ 2 + 2 * T t ^ 2) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => sq_nonneg _)
      ((hET2.const_mul 2).add (hT2.const_mul 2)) (Filter.Eventually.of_forall hpt)
  rw [integral_add (hET2.const_mul 2) (hT2.const_mul 2), integral_const_mul, integral_const_mul] at h1
  have h2 : (∫ t in Icc 0 L, (normalizedLogError t + T t) ^ 2) ≤ laplaceEnergy N := by
    rw [laplaceEnergy_eq_window_add_tail]
    nlinarith [sq_nonneg (normalizedLogError L + (1 - L) * Real.exp (-L / 2))]
  have h3 := integral_transient_sq_le hL0
  linarith

theorem laplaceEnergy_le_chebyshev_mean_square (N : ℕ) :
    laplaceEnergy N ≤ 2 * (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) + 2 +
      (normalizedLogError (cutoff N) + (1 - cutoff N) * Real.exp (-cutoff N / 2)) ^ 2 := by
  set L := cutoff N with hL
  have hL0 : 0 ≤ L := cutoff_nonneg N
  set T : ℝ → ℝ := fun t => (1 - t) * Real.exp (-t / 2) with hT
  have hTc : Continuous T := by rw [hT]; fun_prop
  have hE2 := integrableOn_normalizedLogError_sq L
  have hT2 : IntegrableOn (fun t => T t ^ 2) (Icc 0 L) := (hTc.pow 2).integrableOn_Icc
  have hpt : ∀ t, (normalizedLogError t + T t) ^ 2 ≤ 2 * normalizedLogError t ^ 2 + 2 * T t ^ 2 :=
    fun t => by nlinarith [sq_nonneg (normalizedLogError t - T t)]
  have h1 : (∫ t in Icc 0 L, (normalizedLogError t + T t) ^ 2) ≤
      ∫ t in Icc 0 L, (2 * normalizedLogError t ^ 2 + 2 * T t ^ 2) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => sq_nonneg _)
      ((hE2.const_mul 2).add (hT2.const_mul 2)) (Filter.Eventually.of_forall hpt)
  rw [integral_add (hE2.const_mul 2) (hT2.const_mul 2), integral_const_mul, integral_const_mul] at h1
  have h3 := integral_transient_sq_le hL0
  rw [laplaceEnergy_eq_window_add_tail]
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
