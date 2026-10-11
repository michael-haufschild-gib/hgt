import GaloisForLFunctions.RHTower.XiSliceHeatHermiteRepresentation
import GaloisForLFunctions.RHTower.XiSliceRealAxisGrowth
import GaloisForLFunctions.RHTower.XiSliceCoeffPositivitySharpWindow
import GaloisForLFunctions.RHTower.XiSliceHeatThresholdTouching

/-!
# Effective slice Ki–Kim–Lee: heat `100/log t` makes every heated slice coefficient positive

**Theorem** (`exists_xiSliceHeatTransfer_pos_heat_over_log`).  There is `t₀` such that for all
`|t| ≥ t₀`, all `λ ≥ 100/log |t|` and all `m`,

  `T_{2m}(λ, 0, t) > 0`.

So the WD heat threshold restricted to heights `|t| ≥ T` is at most `100/log T`: the slice
Ki–Kim–Lee theorem holds with an explicit rate.

Proof.  Orders `2m ≥ log t` follow from the quarter-log window: every slice coefficient they
involve is positive (`exists_xiSliceCoeff_pos_above_quarter_log`).  For `N = 2m < log t` and
`λ = 100/log t`, use the Hermite representation `∫ g_N(w) f_t(√λ w) dw = √(2π) λ^{N/2} N! T_N`
(`integral_hermiteGauss_mul_xiSliceProduct`), where `f_t(y) = |ξ(½+y+it)|²`.  Split the line
(`hermite_integral_pos_of_window`):

* on `|w| ≥ 2√N` the Hermite–Gaussian is `≥ 0`, so the integrand is `≥ 0`;
* on the window `√λ w ∈ [99, 100]` it is `≥ (w/2)^N e^{−w²/2} f_t(√λ w)`, and
  `f_t ≥ f_t(1) e^{98(log(t/2) − 2K)}` there (`xiSliceReal_growth`);
* on `|w| < 2√N` its absolute value is `≤ (4√N)^N f_t(√λ w)`, and `|√λ w| ≤ 20`, so
  `f_t ≤ f_t(1 + |y|) ≤ f_t(1) e^{20(log t + 2K)}` (Euler-edge majorant `xiSliceReal_le_one_add_abs`).

The window wins by `e^{28 log t − O(1)}`.  Monotonicity in `λ` comes from the heat shift with
positive weights.
-/

open Complex MeasureTheory Filter Topology Polynomial
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- `He_n(−x) = (−1)ⁿ He_n(x)`. -/
theorem aeval_hermite_neg (n : ℕ) (x : ℝ) :
    aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) := by
  suffices h : ∀ n, aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) ∧
      aeval (-x) (hermite (n + 1)) = (-1) ^ (n + 1) * aeval x (hermite (n + 1)) from (h n).1
  intro n
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [aeval_hermite_add_two, aeval_hermite_add_two, ih.1, ih.2]
    ring

theorem xiSliceReal_neg (t y : ℝ) : xiSliceReal t (-y) = xiSliceReal t y := by
  have h := xiSliceProduct_neg t (y : ℂ)
  rw [← Complex.ofReal_neg, xiSliceProduct_ofReal_eq_xiSliceReal,
    xiSliceProduct_ofReal_eq_xiSliceReal] at h
  exact_mod_cast h

/-- For even `N` the Hermite–Gaussian is `≥ 0` on `|w| ≥ 2√N`. -/
theorem hermiteGauss_nonneg_of_le_abs {N : ℕ} (hN : Even N) {w : ℝ}
    (hw : 2 * Real.sqrt N ≤ |w|) : 0 ≤ hermiteGauss N w := by
  unfold hermiteGauss
  refine mul_nonneg ?_ (Real.exp_pos _).le
  rcases le_total 0 w with h | h
  · rw [abs_of_nonneg h] at hw
    exact le_trans (by positivity) ((pow_half_le_aeval_hermite hw N le_rfl).1)
  · rw [abs_of_nonpos h] at hw
    have h1 := (pow_half_le_aeval_hermite hw N le_rfl).1
    have h2 := aeval_hermite_neg N (-w)
    rw [neg_neg, hN.neg_one_pow, one_mul] at h2
    rw [h2]
    exact le_trans (pow_nonneg (div_nonneg (by linarith) (by norm_num)) N) h1

/-- For `w ≥ 2√N`: `(w/2)^N e^{−w²/2} ≤ g_N(w)`. -/
theorem pow_half_mul_le_hermiteGauss {N : ℕ} {w : ℝ} (hw : 2 * Real.sqrt N ≤ w) :
    (w / 2) ^ N * Real.exp (-(w ^ 2 / 2)) ≤ hermiteGauss N w := by
  unfold hermiteGauss
  exact mul_le_mul_of_nonneg_right (pow_half_le_aeval_hermite hw N le_rfl).1 (Real.exp_pos _).le

/-- For `|w| ≤ 2√N`: `|g_N(w)| ≤ (4√N)^N`. -/
theorem abs_hermiteGauss_le {N : ℕ} {w : ℝ} (hw : |w| ≤ 2 * Real.sqrt N) :
    |hermiteGauss N w| ≤ (4 * Real.sqrt N) ^ N := by
  unfold hermiteGauss
  rw [abs_mul, Real.abs_exp]
  have h1 := (abs_aeval_hermite_le (n := N) w N le_rfl).1
  have h2 : (|w| + 2 * Real.sqrt N) ^ N ≤ (4 * Real.sqrt N) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  have h3 : Real.exp (-(w ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w])
  calc |aeval w (hermite N)| * Real.exp (-(w ^ 2 / 2)) ≤ (4 * Real.sqrt N) ^ N * 1 :=
        mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (by positivity)
    _ = _ := mul_one _

/-- **Hermite-integral positivity from window bounds.**  Let `N` be even, `s > 0` with
`s² N ≤ 100`, and let `f ≥ 0` with `Lf ≤ f` on `[99, 100]` and `f ≤ Uf` on
`[−20, 20]`.  If `40 Uf < e^{−5000/s²} Lf` and `w ↦ g_N(w) f(sw)` is integrable, then
`∫ g_N(w) f(sw) dw > 0`. -/
theorem hermite_integral_pos_of_window {N : ℕ} (hN : Even N) {s : ℝ} (hs : 0 < s)
    (hsN : s ^ 2 * N ≤ 100) {f : ℝ → ℝ} (hf0 : ∀ y, 0 ≤ f y)
    {Lf Uf : ℝ} (hLf : ∀ y ∈ Set.Icc (99 : ℝ) 100, Lf ≤ f y)
    (hUf : ∀ y, |y| ≤ 20 → f y ≤ Uf) (hLU : 40 * Uf < Real.exp (-(5000 / s ^ 2)) * Lf)
    (hint : Integrable fun w => hermiteGauss N w * f (s * w)) :
    0 < ∫ w, hermiteGauss N w * f (s * w) := by
  set A := 2 * Real.sqrt N with hA
  have hA0 : 0 ≤ A := by positivity
  set Q := (4 * Real.sqrt N) ^ N with hQ
  have hQ0 : 0 < Q := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [hQ, h]
    · have : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast h)
      positivity
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  -- the window lies beyond `2√N`
  have hW : A ≤ 99 / s := by
    rw [hA, le_div_iff₀ hs]
    have h1 : (2 * Real.sqrt N * s) ^ 2 ≤ 99 ^ 2 := by nlinarith
    have h2 : 0 ≤ 2 * Real.sqrt N * s := by positivity
    nlinarith
  have hsA : s * A ≤ 20 := by
    have h1 : (s * A) ^ 2 ≤ 20 ^ 2 := by rw [hA]; nlinarith
    have h2 : 0 ≤ s * A := by positivity
    nlinarith
  have hQwin : Q ≤ (99 / (2 * s)) ^ N := by
    refine pow_le_pow_left₀ (by positivity) ?_ N
    rw [le_div_iff₀ (by positivity)]
    have h1 : (4 * Real.sqrt N * (2 * s)) ^ 2 ≤ 99 ^ 2 := by nlinarith
    have h2 : 0 ≤ 4 * Real.sqrt N * (2 * s) := by positivity
    nlinarith
  set L := (99 / (2 * s)) ^ N * Real.exp (-(5000 / s ^ 2)) * Lf with hL
  set U := Q * Uf with hU
  set W := Set.Icc (99 / s) (100 / s) with hWdef
  set Inn := Set.Ioo (-A) A with hInn
  have hUf0 : 0 ≤ Uf := le_trans (hf0 0) (hUf 0 (by simp))
  have hLf0 : 0 < Lf := by
    have := mul_pos_iff.mp (lt_of_le_of_lt (by positivity) hLU)
    rcases this with h | h
    · exact h.2
    · exact absurd h.1 (not_lt.mpr (Real.exp_pos _).le)
  -- pointwise lower bound by indicators
  have hpt : ∀ w, W.indicator (fun _ => L) w - Inn.indicator (fun _ => U) w ≤
      hermiteGauss N w * f (s * w) := by
    intro w
    by_cases hwW : w ∈ W
    · have hwA : A ≤ w := le_trans hW hwW.1
      have hwI : w ∉ Inn := fun h => by linarith [h.2]
      rw [Set.indicator_of_mem hwW, Set.indicator_of_notMem hwI, sub_zero]
      have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwW.1
      have hsw : s * w ∈ Set.Icc (99 : ℝ) 100 := by
        constructor
        · have := mul_le_mul_of_nonneg_left hwW.1 hs.le
          rwa [mul_div_cancel₀ _ hs.ne'] at this
        · have := mul_le_mul_of_nonneg_left hwW.2 hs.le
          rwa [mul_div_cancel₀ _ hs.ne'] at this
      have hg := pow_half_mul_le_hermiteGauss (N := N) hwA
      have hpow : (99 / (2 * s)) ^ N ≤ (w / 2) ^ N := by
        refine pow_le_pow_left₀ (by positivity) ?_ N
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := hwW.1
        rw [div_le_iff₀ hs] at this
        nlinarith
      have hexp : Real.exp (-(5000 / s ^ 2)) ≤ Real.exp (-(w ^ 2 / 2)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : w ≤ 100 / s := hwW.2
        have h2 : w ^ 2 ≤ (100 / s) ^ 2 := pow_le_pow_left₀ hw0.le h1 2
        have h3 : (100 / s) ^ 2 / 2 = 5000 / s ^ 2 := by field_simp; ring
        linarith
      calc L = (99 / (2 * s)) ^ N * Real.exp (-(5000 / s ^ 2)) * Lf := rfl
        _ ≤ (w / 2) ^ N * Real.exp (-(w ^ 2 / 2)) * f (s * w) := by
          gcongr
          exact hLf _ hsw
        _ ≤ hermiteGauss N w * f (s * w) := mul_le_mul_of_nonneg_right hg (hf0 _)
    · rw [Set.indicator_of_notMem hwW, zero_sub]
      by_cases hwI : w ∈ Inn
      · rw [Set.indicator_of_mem hwI]
        have habs : |w| ≤ A := abs_le.mpr ⟨hwI.1.le, hwI.2.le⟩
        have hg := abs_hermiteGauss_le (N := N) habs
        have hsw : |s * w| ≤ 20 := by
          rw [abs_mul, abs_of_pos hs]
          exact le_trans (mul_le_mul_of_nonneg_left habs hs.le) hsA
        have hfb := hUf _ hsw
        have : |hermiteGauss N w * f (s * w)| ≤ U := by
          rw [abs_mul, abs_of_nonneg (hf0 _), hU]
          exact mul_le_mul hg hfb (hf0 _) hQ0.le
        linarith [neg_abs_le (hermiteGauss N w * f (s * w))]
      · rw [Set.indicator_of_notMem hwI, neg_zero]
        have habs : A ≤ |w| := by
          by_contra h
          push Not at h
          exact hwI ⟨by linarith [neg_abs_le w], lt_of_le_of_lt (le_abs_self w) h⟩
        exact mul_nonneg (hermiteGauss_nonneg_of_le_abs hN habs) (hf0 _)
  -- integrate
  have hiW : Integrable (W.indicator fun _ => L) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have hiI : Integrable (Inn.indicator fun _ => U) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have hmono := integral_mono (hiW.sub hiI) hint hpt
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub hiW hiI, integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioo] at hmono
  have hvW : volume.real W = 1 / s := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by
      rw [sub_nonneg]; exact div_le_div_of_nonneg_right (by norm_num) hs.le)]
    field_simp
    ring
  have hvI : volume.real Inn = 2 * A := by
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvW, hvI, smul_eq_mul, smul_eq_mul] at hmono
  -- `L / s > 2A U`
  have hkey : 2 * A * U < 1 / s * L := by
    have h1 : 2 * A * U ≤ 40 / s * (Q * Uf) := by
      rw [hU]
      have h2A : 2 * A ≤ 40 / s := by
        rw [le_div_iff₀ hs]
        linarith
      exact mul_le_mul_of_nonneg_right h2A (by positivity)
    have h2 : 40 / s * (Q * Uf) < 1 / s * (Q * (Real.exp (-(5000 / s ^ 2)) * Lf)) := by
      have : 40 * Uf < Real.exp (-(5000 / s ^ 2)) * Lf := hLU
      have hs1 : 0 < 1 / s := by positivity
      calc 40 / s * (Q * Uf) = 1 / s * (Q * (40 * Uf)) := by ring
        _ < 1 / s * (Q * (Real.exp (-(5000 / s ^ 2)) * Lf)) := by gcongr
    have h3 : 1 / s * (Q * (Real.exp (-(5000 / s ^ 2)) * Lf)) ≤ 1 / s * L := by
      rw [hL]
      have : 0 ≤ Real.exp (-(5000 / s ^ 2)) * Lf := by positivity
      have h := mul_le_mul_of_nonneg_right hQwin this
      have hs1 : 0 ≤ 1 / s := by positivity
      calc 1 / s * (Q * (Real.exp (-(5000 / s ^ 2)) * Lf))
          ≤ 1 / s * ((99 / (2 * s)) ^ N * (Real.exp (-(5000 / s ^ 2)) * Lf)) :=
            mul_le_mul_of_nonneg_left h hs1
        _ = _ := by ring
    linarith
  linarith

/-- **Effective slice Ki–Kim–Lee at heat `100/log t`.** -/
theorem exists_xiSliceHeatTransfer_pos_at_heat_over_log :
    ∃ t₀ : ℝ, 200 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer (100 / Real.log t) 0 t (2 * m) := by
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  set K := xiEulerConstant (1 / 2) with hK
  have hK0 : 0 < K := xiEulerConstant_pos (by norm_num)
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl40 : 0 < Real.log 40 := Real.log_pos (by norm_num)
  set L₀ := max (2 * |K₁| + 2) (max (Real.log 200)
    ((98 * Real.log 2 + 236 * K + Real.log 40) / 28 + Real.log 2 + 2 * K + 1)) with hL₀
  refine ⟨Real.exp L₀, ?_, fun t ht m => ?_⟩
  · calc (200 : ℝ) = Real.exp (Real.log 200) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp L₀ := Real.exp_le_exp.mpr (le_trans (le_max_left _ _) (le_max_right _ _))
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  set ℓ := Real.log t with hℓ
  have hℓL : L₀ ≤ ℓ := by
    rw [hℓ, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) ht
  have hℓ1 : 2 * |K₁| + 2 ≤ ℓ := le_trans (le_max_left _ _) hℓL
  have hℓ200 : Real.log 200 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓL
  have hℓ3 : (98 * Real.log 2 + 236 * K + Real.log 40) / 28 + Real.log 2 + 2 * K + 1 ≤ ℓ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hℓL
  have hℓ0 : 0 < ℓ := by linarith [abs_nonneg K₁]
  have ht200 : 200 ≤ t := by
    rw [← Real.exp_log ht0, ← Real.exp_log (by norm_num : (0 : ℝ) < 200)]
    exact Real.exp_le_exp.mpr hℓ200
  have hlam0 : 0 ≤ 100 / ℓ := by positivity
  by_cases hm : (1 / 2 : ℝ) * ℓ ≤ m
  · -- high orders: every slice coefficient involved is positive
    have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
      intro k hk
      refine hK₁ t ht0.le k (max_le ?_ ?_)
      · have : (K₁ : ℝ) ≤ |K₁| := le_abs_self K₁
        have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [abs_nonneg K₁]
      · have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
        have : (1 / 4 + 1 / 4) * Real.log t = 1 / 2 * ℓ := by rw [hℓ]; ring
        linarith
    have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam0 0 t (2 * m)
    simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
    have hterm : ∀ k : ℕ, 0 ≤ (((((100 / ℓ) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceCoeff t (2 * m + 2 * k)) := by
      intro k
      refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
      rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
      exact (hcoef (m + k) (by omega)).le
    have h0 := le_hasSum hT 0 fun j _ => hterm j
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
      div_self hfac, one_mul, Complex.ofReal_one] at h0
    exact lt_of_lt_of_le (hcoef m le_rfl) h0
  · -- low orders: the Hermite representation
    push Not at hm
    set N := 2 * m with hNdef
    have hNℓ : (N : ℝ) ≤ ℓ := by
      rw [hNdef]
      push_cast
      linarith
    set lam := 100 / ℓ with hlam
    set s := Real.sqrt lam with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = 100 / ℓ := Real.sq_sqrt hlam0
    set f := xiSliceReal t with hf
    have hf1 : 0 < f 1 := xiSliceReal_pos t (by norm_num)
    have ht8 : (8 : ℝ) ≤ t := by linarith
    have hlogt2 : Real.log (t / 2) = ℓ - Real.log 2 := by
      rw [Real.log_div ht0.ne' (by norm_num), hℓ]
    -- window lower bound
    set Lf := f 1 * Real.exp ((Real.log (t / 2) - 2 * K) * 98) with hLf
    have hLfb : ∀ y ∈ Set.Icc (99 : ℝ) 100, Lf ≤ f y := by
      intro y hy
      obtain ⟨hg, -⟩ := xiSliceReal_growth (t := t) ht8 (y₁ := 1) (y₂ := y) le_rfl
        (by linarith [hy.1]) (by linarith [hy.2])
      have hc : 0 ≤ Real.log (t / 2) - 2 * K := by rw [hlogt2]; linarith
      have : Real.exp ((Real.log (t / 2) - 2 * K) * 98) ≤
          Real.exp ((Real.log (t / 2) - 2 * K) * (y - 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hy.1]) hc)
      calc Lf ≤ f 1 * Real.exp ((Real.log (t / 2) - 2 * K) * (y - 1)) :=
            mul_le_mul_of_nonneg_left this hf1.le
        _ ≤ f y := hg
    -- inner upper bound
    set Uf := f 1 * Real.exp ((ℓ + 2 * K) * 20) with hUf
    have hUfb : ∀ y, |y| ≤ 20 → f y ≤ Uf := by
      intro y hy
      have h1 := xiSliceReal_le_one_add_abs t y
      obtain ⟨-, hg⟩ := xiSliceReal_growth (t := t) ht8 (y₁ := 1) (y₂ := 1 + |y|) le_rfl
        (by linarith [abs_nonneg y]) (by linarith)
      have hc : 0 ≤ ℓ + 2 * K := by linarith
      have : Real.exp ((Real.log t + 2 * K) * (1 + |y| - 1)) ≤ Real.exp ((ℓ + 2 * K) * 20) := by
        refine Real.exp_le_exp.mpr ?_
        rw [← hℓ]
        exact mul_le_mul_of_nonneg_left (by linarith) hc
      calc f y ≤ f (1 + |y|) := h1
        _ ≤ f 1 * Real.exp ((Real.log t + 2 * K) * (1 + |y| - 1)) := hg
        _ ≤ Uf := mul_le_mul_of_nonneg_left this hf1.le
    -- the comparison `40 Uf < e^{−5000/s²} Lf`
    have hLU : 40 * Uf < Real.exp (-(5000 / s ^ 2)) * Lf := by
      have h5000 : 5000 / s ^ 2 = 50 * ℓ := by rw [hs2]; field_simp; ring
      rw [h5000, hLf, hUf, hlogt2]
      have hexp : 40 < Real.exp (28 * ℓ - 98 * Real.log 2 - 236 * K) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 40)]
        exact Real.exp_lt_exp.mpr (by linarith)
      have e : Real.exp (-(50 * ℓ)) * (f 1 * Real.exp ((ℓ - Real.log 2 - 2 * K) * 98)) =
          Real.exp (28 * ℓ - 98 * Real.log 2 - 236 * K) * (f 1 * Real.exp ((ℓ + 2 * K) * 20)) := by
        rw [mul_left_comm, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      rw [e]
      have : 0 < f 1 * Real.exp ((ℓ + 2 * K) * 20) := by positivity
      nlinarith
    -- integrability and the representation
    have hcplx := integrable_hermiteGauss_mul_xiSliceProduct hlam0 t N
    have hreal : (fun w : ℝ => (hermiteGauss N w : ℂ) * xiSliceProduct t ((s * w : ℝ) : ℂ)) =
        fun w => ((hermiteGauss N w * f (s * w) : ℝ) : ℂ) := by
      funext w
      rw [xiSliceProduct_ofReal_eq_xiSliceReal]
      push_cast
      rfl
    have hint : Integrable fun w => hermiteGauss N w * f (s * w) := by
      rw [hreal] at hcplx
      exact hcplx.re
    have hpos := hermite_integral_pos_of_window (N := N) (by rw [hNdef]; exact even_two_mul m) hs0
      (by rw [hs2]; field_simp; linarith) (fun y => xiSliceReal_nonneg t y) hLfb hUfb hLU hint
    have hrep := integral_hermiteGauss_mul_xiSliceProduct hlam0 t N
    rw [← hs, hreal, integral_complex_ofReal] at hrep
    have hC : 0 < Real.sqrt (2 * Real.pi) * s ^ N * (N.factorial : ℝ) := by
      have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have hT : xiSliceHeatTransfer lam 0 t N =
        (((∫ w, hermiteGauss N w * f (s * w)) / (Real.sqrt (2 * Real.pi) * s ^ N *
          (N.factorial : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, hrep]
      field_simp [Complex.ofReal_ne_zero.mpr hC.ne']
    rw [hT]
    exact Complex.zero_lt_real.mpr (div_pos hpos hC)

/-- **Effective slice Ki–Kim–Lee.**  There is `t₀` such that for `|t| ≥ t₀`, every heat
`λ ≥ 100/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_over_log :
    ∃ t₀ : ℝ, 200 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, 100 / Real.log |t| ≤ lam → ∀ m : ℕ,
      0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, h⟩ := exists_xiSliceHeatTransfer_pos_at_heat_over_log
  refine ⟨t₀, ht₀, fun t ht lam hlam m => ?_⟩
  have hu0 : 0 < |t| := by linarith
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have key : 0 < xiSliceHeatTransfer lam 0 |t| (2 * m) := by
    have hshift := hasSum_xiSliceHeatTransfer_shift hlam 0 |t| (2 * m)
    have hd : 0 ≤ (lam - 100 / Real.log |t|) / 2 := by linarith
    have hterm : ∀ k : ℕ, 0 ≤ ((((lam - 100 / Real.log |t|) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer (100 / Real.log |t|) 0 |t| (2 * m + 2 * k) := by
      intro k
      refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
      rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
      exact (h |t| ht (m + k)).le
    have h0 := le_hasSum hshift 0 fun j _ => hterm j
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
      div_self hfac, one_mul, Complex.ofReal_one] at h0
    exact lt_of_lt_of_le (h |t| ht m) h0
  rcases le_total 0 t with htn | htn
  · rwa [abs_of_nonneg htn] at key
  · rw [abs_of_nonpos htn] at key
    rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]
    exact key

end

end RHTower.DeBruijn
