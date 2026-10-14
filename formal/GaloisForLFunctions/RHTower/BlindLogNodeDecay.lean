import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Blindness at `log ℕ` forces exponential decay

The nodes `log n`, `n ≥ 2`, have spacing `log(1 + 1/n) < e^{-x}` near `x = log n`.  A smooth function
vanishing at every node is therefore small between them: `k + 1` consecutive nodes near `x` lie in
an interval of length at most `2k e^{-x}`, and the Rolle cascade bounds the function there by
`sup |f^{(k)}|` times the `k`-th power of that length.

* `abs_le_of_zeros_of_iteratedDeriv_le`: a real `C^k` function vanishing at `k + 1` distinct points
  of `[a, b]` satisfies `|f| ≤ M (b - a)^k` on `[a, b]`, where `|f^{(k)}| ≤ M`.
* `abs_le_of_logNat_zero`: a real `C^k` function with `|f^{(k)}| ≤ M` and `f(log n) = 0` for every
  `n ≥ 2` satisfies `|f(x)| ≤ M (2k)^k e^{-kx}` for `x ≥ log 2`.
* `norm_charFun_le_of_logNat_blind`: if a finite measure `μ` on `ℝ` has a finite moment of order `k`
  and its characteristic function vanishes at every `log n`, `n ≥ 2`, then
  `‖φ_μ(x)‖ ≤ 2 (∫ |t|^k dμ) (2k)^k e^{-k|x|}` for `|x| ≥ log 2`.

Sharp form.  The generalised Rolle theorem (`exists_iteratedDeriv_eq_zero`) gives the Lagrange
interpolation bound `|f(y)| ≤ (M / k!) ∏ |y - x_i|` (`abs_le_div_factorial_mul_prod`).  At the nodes
`log(n + i)`, `i < k`, the product is at most `k!/n^k`, so `|f(y)| ≤ M (2e^{-y})^k`
(`abs_le_of_logNat_zero_sharp`, `norm_charFun_le_of_logNat_blind_sharp`).  Optimising over `k`
against the moments of an exponential tail gives
`‖φ_μ(x)‖ ≤ 4 (∫ e^{a|t|} dμ) exp(-(a log 2 / 4) e^{|x|})` (`norm_charFun_le_doubleExp_of_logNat_blind`):
blindness turns exponential spectral tails into doubly exponential decay, so the spectral density
of such a test extends to an entire function.

For a prime-blind positive-definite test `h = φ_μ` (spectral measure `μ`), one spectral moment already
gives decay at rate `1 > ½`, so the test lies in the Weil decay class without any decay hypothesis;
with all moments `h` decays faster than every exponential.  This is the converse direction to the
Carlson threshold, where spectral decay at rate `π/2` forces a blind measure to vanish.
-/

open Set Real MeasureTheory Complex

namespace RHTower.BlindLogNodeDecay

noncomputable section

/-- **Rolle cascade.**  A real `C^k` function with `|f^{(k)}| ≤ M` that vanishes at `k + 1` distinct
points of `[a, b]` satisfies `|f| ≤ M (b - a)^k` on `[a, b]`. -/
theorem abs_le_of_zeros_of_iteratedDeriv_le {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) {M : ℝ}
    (hM : ∀ x, |iteratedDeriv k f x| ≤ M) {a b : ℝ} (s : Fin (k + 1) → ℝ) (hs : StrictMono s)
    (hsI : ∀ i, s i ∈ Icc a b) (hz : ∀ i, f (s i) = 0) : ∀ y ∈ Icc a b, |f y| ≤ M * (b - a) ^ k := by
  induction k generalizing f with
  | zero =>
    intro y _
    simpa using hM y
  | succ k ih =>
    have hf' : ContDiff ℝ (k + 1 : ℕ) f := hf
    rw [Nat.cast_succ, contDiff_succ_iff_deriv] at hf'
    obtain ⟨hdiff, -, hderiv⟩ := hf'
    have hrolle : ∀ i : Fin (k + 1), ∃ c ∈ Ioo (s i.castSucc) (s i.succ), deriv f c = 0 := by
      intro i
      refine exists_deriv_eq_zero (hs (Fin.castSucc_lt_succ (i := i))) hdiff.continuous.continuousOn ?_
      rw [hz, hz]
    choose t ht hzt using hrolle
    have htm : StrictMono t := by
      intro i j hij
      have h1 := (ht i).2
      have h2 := (ht j).1
      have hle : s i.succ ≤ s j.castSucc := hs.monotone (by
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact hij)
      linarith
    have htI : ∀ i, t i ∈ Icc a b := fun i =>
      ⟨(hsI i.castSucc).1.trans (ht i).1.le, (ht i).2.le.trans (hsI i.succ).2⟩
    have hMd : ∀ x, |iteratedDeriv k (deriv f) x| ≤ M := fun x => by
      rw [← iteratedDeriv_succ']
      exact hM x
    have hbound := ih hderiv hMd t htm htI hzt
    intro y hy
    have hs0 := hsI 0
    have hC : 0 ≤ M * (b - a) ^ k := (abs_nonneg _).trans (hbound a ⟨le_rfl, hy.1.trans hy.2⟩)
    have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hdiff x) (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx) hs0 hy
    rw [hz, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hd : |y - s 0| ≤ b - a := abs_le.mpr ⟨by linarith [hy.1, hs0.2], by linarith [hy.2, hs0.1]⟩
    calc |f y| ≤ M * (b - a) ^ k * |y - s 0| := hmv
      _ ≤ M * (b - a) ^ k * (b - a) := mul_le_mul_of_nonneg_left hd hC
      _ = M * (b - a) ^ (k + 1) := by ring

/-- Near `x ≥ log 2` the node `log ⌊e^x⌋` and the next `k` nodes span at most `2k e^{-x}`. -/
theorem log_add_sub_log_le {x : ℝ} (hx : Real.log 2 ≤ x) (k : ℕ) :
    Real.log ((⌊Real.exp x⌋₊ : ℝ) + k) - Real.log ⌊Real.exp x⌋₊ ≤ 2 * k * Real.exp (-x) := by
  set n : ℕ := ⌊Real.exp x⌋₊ with hn
  have h2 : (2 : ℝ) ≤ Real.exp x := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hx
  have hn1 : Real.exp x < n + 1 := Nat.lt_floor_add_one _
  have hnpos : (0 : ℝ) < n := by
    have : 2 ≤ n := Nat.le_floor (by exact_mod_cast h2)
    exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log ((n : ℝ) + k) - Real.log n ≤ k / n := by
    rw [← Real.log_div (by positivity) hnpos.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + k) / n by positivity)
    have he : ((n : ℝ) + k) / n - 1 = k / n := by field_simp; ring
    linarith
  have hk : (k : ℝ) / n ≤ 2 * k * Real.exp (-x) := by
    rw [Real.exp_neg, div_le_iff₀ hnpos]
    have hex : 0 < Real.exp x := Real.exp_pos x
    have : Real.exp x ≤ 2 * n := by linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc (k : ℝ) = k * Real.exp x * (Real.exp x)⁻¹ := by field_simp
      _ ≤ k * (2 * n) * (Real.exp x)⁻¹ := by gcongr
      _ = 2 * k * (Real.exp x)⁻¹ * n := by ring
  linarith

/-- **Blindness at `log ℕ` forces decay at rate `k`.**  A real `C^k` function with `|f^{(k)}| ≤ M`
vanishing at every `log n`, `n ≥ 2`, satisfies `|f(x)| ≤ M (2k)^k e^{-kx}` for `x ≥ log 2`. -/
theorem abs_le_of_logNat_zero {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) {M : ℝ}
    (hM : ∀ x, |iteratedDeriv k f x| ≤ M) (hz : ∀ n : ℕ, 2 ≤ n → f (Real.log n) = 0) {x : ℝ}
    (hx : Real.log 2 ≤ x) : |f x| ≤ M * (2 * k) ^ k * Real.exp (-(k * x)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hM x
  set n : ℕ := ⌊Real.exp x⌋₊ with hn
  have h2 : (2 : ℝ) ≤ Real.exp x := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hx
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast h2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnle : (n : ℝ) ≤ Real.exp x := Nat.floor_le (Real.exp_pos x).le
  have hn1 : Real.exp x < n + 1 := Nat.lt_floor_add_one _
  set s : Fin (k + 1) → ℝ := fun i => Real.log ((n : ℝ) + i) with hs
  have hsm : StrictMono s := fun i j hij => by
    simp only [hs]
    refine Real.log_lt_log (by positivity) ?_
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  have hsI : ∀ i, s i ∈ Icc (Real.log n) (Real.log ((n : ℝ) + k)) := fun i => by
    have hik : (i : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
    exact ⟨Real.log_le_log hnpos (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]),
      Real.log_le_log (by positivity) (by linarith)⟩
  have hzs : ∀ i, f (s i) = 0 := fun i => by
    have := hz (n + i) (by omega)
    simpa [hs] using this
  have hxI : x ∈ Icc (Real.log n) (Real.log ((n : ℝ) + k)) := by
    refine ⟨?_, ?_⟩
    · rw [← Real.log_exp x]
      exact Real.log_le_log hnpos hnle
    · rw [← Real.log_exp x]
      refine Real.log_le_log (Real.exp_pos x) ?_
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
  have hb := abs_le_of_zeros_of_iteratedDeriv_le hf hM s hsm hsI hzs x hxI
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hδ := log_add_sub_log_le hx k
  have hδ0 : 0 ≤ Real.log ((n : ℝ) + k) - Real.log n := by
    have := hsI 0
    simp only [hs, Fin.val_zero, Nat.cast_zero, add_zero] at this
    linarith [this.2]
  calc |f x| ≤ M * (Real.log ((n : ℝ) + k) - Real.log n) ^ k := hb
    _ ≤ M * (2 * k * Real.exp (-x)) ^ k := by gcongr
    _ = M * (2 * k) ^ k * Real.exp (-(k * x)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf

/-- The `k`-th derivative of the characteristic function is bounded by the `k`-th absolute
moment. -/
theorem norm_iteratedDeriv_charFun_le {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ}
    (hint : MemLp id k μ) (t : ℝ) :
    ‖iteratedDeriv k (charFun μ) t‖ ≤ ∫ y, |y| ^ k ∂μ := by
  rw [iteratedDeriv_charFun hint, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [show (t : ℂ) * y * I = ((t * y : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
    mul_one]

/-- Real and imaginary parts commute with iterated derivatives. -/
theorem iteratedDeriv_clm_comp {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f) (L : ℂ →L[ℝ] ℝ) (t : ℝ) :
    iteratedDeriv k (L ∘ f) t = L (iteratedDeriv k f t) := by
  rw [iteratedDeriv, L.iteratedFDeriv_comp_left hf.contDiffAt le_rfl, iteratedDeriv]
  rfl

/-- **Blind characteristic functions decay.**  If a finite measure `μ` on `ℝ` has a finite moment
of order `k` and its characteristic function vanishes at every `log n`, `n ≥ 2`, then for
`|x| ≥ log 2`, `‖φ_μ(x)‖ ≤ 2 (∫ |t|^k dμ) (2k)^k e^{-k|x|}`. -/
theorem norm_charFun_le_of_logNat_blind {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ}
    (hint : MemLp id k μ) (hblind : ∀ n : ℕ, 2 ≤ n → charFun μ (Real.log n) = 0) {x : ℝ}
    (hx : Real.log 2 ≤ |x|) :
    ‖charFun μ x‖ ≤ 2 * (∫ y, |y| ^ k ∂μ) * (2 * k) ^ k * Real.exp (-(k * |x|)) := by
  have hF : ContDiff ℝ k (charFun μ) := contDiff_charFun hint
  set M := ∫ y, |y| ^ k ∂μ
  have part : ∀ L : ℂ →L[ℝ] ℝ, ‖L‖ ≤ 1 →
      |L (charFun μ |x|)| ≤ M * (2 * k) ^ k * Real.exp (-(k * |x|)) := by
    intro L hL
    have hLf : ContDiff ℝ k (L ∘ charFun μ) := L.contDiff.comp hF
    refine abs_le_of_logNat_zero hLf (fun t => ?_) (fun n hn => ?_) hx
    · rw [iteratedDeriv_clm_comp hF L t, ← Real.norm_eq_abs]
      exact (L.le_opNorm _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (norm_iteratedDeriv_charFun_le hint t))
    · simp [hblind n hn]
  have hre := part Complex.reCLM (by rw [Complex.reCLM_norm])
  have him := part Complex.imCLM (by rw [Complex.imCLM_norm])
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  have habs : ‖charFun μ x‖ = ‖charFun μ |x|‖ := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, charFun_neg, Complex.norm_conj]
  rw [habs]
  calc ‖charFun μ |x|‖ ≤ |(charFun μ |x|).re| + |(charFun μ |x|).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by linarith

private theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * |x|))) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).congr_fun (fun x hx => ?_)
      measurableSet_Ioi
    rw [abs_of_pos hx]
    ring_nf
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-(c * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := c) hc 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    rw [abs_of_nonpos hx]
    ring_nf
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- **Blind tests lie in every decay class below their moment order.**  Under the hypotheses of
`norm_charFun_le_of_logNat_blind`, `‖φ_μ(x)‖ e^{a|x|}` is integrable for every `a < k`.  For `k = 1`
this contains the Weil decay class `e^{-(½+δ)|x|}`, `0 < δ < ½`. -/
theorem integrable_norm_charFun_mul_exp_of_logNat_blind {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ}
    (hint : MemLp id k μ) (hblind : ∀ n : ℕ, 2 ≤ n → charFun μ (Real.log n) = 0) {a : ℝ}
    (ha : a < k) : Integrable (fun x => ‖charFun μ x‖ * Real.exp (a * |x|)) := by
  set c := (k : ℝ) - a with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set M := ∫ y, |y| ^ k ∂μ
  have hM0 : 0 ≤ M := integral_nonneg fun y => by positivity
  set B := max (2 * M * (2 * k) ^ k) (μ.real univ * Real.exp (k * Real.log 2))
  refine ((integrable_exp_neg_mul_abs hc0).const_mul B).mono'
    ((continuous_charFun.norm.mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsplit : Real.exp (a * |x|) = Real.exp (-(c * |x|)) * Real.exp (k * |x|) := by
    rw [← Real.exp_add, hc]; ring_nf
  rcases le_or_gt (Real.log 2) |x| with hx | hx
  · have hb := norm_charFun_le_of_logNat_blind hint hblind hx
    calc ‖charFun μ x‖ * Real.exp (a * |x|)
        ≤ 2 * M * (2 * k) ^ k * Real.exp (-(k * |x|)) * Real.exp (a * |x|) := by gcongr
      _ = 2 * M * (2 * k) ^ k * Real.exp (-(c * |x|)) := by
          rw [mul_assoc, ← Real.exp_add, hc]; ring_nf
      _ ≤ B * Real.exp (-(c * |x|)) := by gcongr; exact le_max_left _ _
  · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc ‖charFun μ x‖ * Real.exp (a * |x|)
        ≤ μ.real univ * (Real.exp (-(c * |x|)) * Real.exp (k * Real.log 2)) := by
          rw [hsplit]
          gcongr
          exact norm_charFun_le x
      _ = μ.real univ * Real.exp (k * Real.log 2) * Real.exp (-(c * |x|)) := by ring
      _ ≤ B * Real.exp (-(c * |x|)) := by gcongr; exact le_max_right _ _

/-! ### The sharp interpolation bound -/

open Polynomial in
theorem iteratedDeriv_eval_poly (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun t => p.eval t) = fun t => (derivative^[k] p).eval t := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have h : deriv (fun t => p.eval t) = fun t => (derivative p).eval t :=
      funext fun t => Polynomial.deriv p
    rw [h, ih, Function.iterate_succ_apply]

open Polynomial in
theorem contDiff_eval_poly (p : ℝ[X]) (n : WithTop ℕ∞) : ContDiff ℝ n (fun t => p.eval t) := by
  simpa [Polynomial.coe_aeval_eq_eval] using p.contDiff_aeval (𝕜 := ℝ) n

/-- The node polynomial `∏ (X - x_i)`. -/
def nodePoly {k : ℕ} (x : Fin k → ℝ) : Polynomial ℝ := ∏ i, (Polynomial.X - Polynomial.C (x i))

open Polynomial in
theorem nodePoly_monic {k : ℕ} (x : Fin k → ℝ) : (nodePoly x).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)

open Polynomial in
theorem natDegree_nodePoly {k : ℕ} (x : Fin k → ℝ) : (nodePoly x).natDegree = k := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)]
  simp

open Polynomial in
theorem eval_nodePoly {k : ℕ} (x : Fin k → ℝ) (y : ℝ) : (nodePoly x).eval y = ∏ i, (y - x i) := by
  simp [nodePoly, eval_prod]

open Polynomial in
theorem iteratedDeriv_nodePoly {k : ℕ} (x : Fin k → ℝ) (t : ℝ) :
    iteratedDeriv k (fun t => (nodePoly x).eval t) t = k.factorial := by
  simp only [iteratedDeriv_eval_poly]
  have hdeg : (derivative^[k] (nodePoly x)).natDegree = 0 := by
    have := natDegree_iterate_derivative (nodePoly x) k
    rw [natDegree_nodePoly] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, eval_C, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self]
  have h1 : (nodePoly x).coeff k = 1 := by
    have := (nodePoly_monic x).coeff_natDegree
    rwa [natDegree_nodePoly] at this
  rw [h1, nsmul_eq_mul, mul_one]

/-- **Generalised Rolle.**  A real `C^k` function vanishing at `k + 1` distinct points has a zero
of its `k`-th derivative. -/
theorem exists_iteratedDeriv_eq_zero {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (s : Fin (k + 1) → ℝ) (hs : StrictMono s) (hz : ∀ i, f (s i) = 0) :
    ∃ ξ, iteratedDeriv k f ξ = 0 := by
  induction k generalizing f with
  | zero => exact ⟨s 0, by simpa using hz 0⟩
  | succ k ih =>
    have hf' : ContDiff ℝ (k + 1 : ℕ) f := hf
    rw [Nat.cast_succ, contDiff_succ_iff_deriv] at hf'
    obtain ⟨hdiff, -, hderiv⟩ := hf'
    have hrolle : ∀ i : Fin (k + 1), ∃ c ∈ Ioo (s i.castSucc) (s i.succ), deriv f c = 0 := by
      intro i
      refine exists_deriv_eq_zero (hs (Fin.castSucc_lt_succ (i := i))) hdiff.continuous.continuousOn ?_
      rw [hz, hz]
    choose t ht hzt using hrolle
    have htm : StrictMono t := by
      intro i j hij
      have h1 := (ht i).2
      have h2 := (ht j).1
      have hle : s i.succ ≤ s j.castSucc := hs.monotone (by
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact hij)
      linarith
    obtain ⟨ξ, hξ⟩ := ih hderiv t htm hzt
    exact ⟨ξ, by rw [iteratedDeriv_succ']; exact hξ⟩

/-- **Lagrange interpolation bound.**  A real `C^k` function with `|f^{(k)}| ≤ M` vanishing at `k`
distinct nodes `x_i` satisfies `|f(y)| ≤ (M / k!) ∏ |y - x_i|`. -/
theorem abs_le_div_factorial_mul_prod {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) {M : ℝ}
    (hM : ∀ x, |iteratedDeriv k f x| ≤ M) (x : Fin k → ℝ) (hx : Function.Injective x)
    (hz : ∀ i, f (x i) = 0) (y : ℝ) : |f y| ≤ M / k.factorial * ∏ i, |y - x i| := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hy : ∃ i, x i = y
  · obtain ⟨i, rfl⟩ := hy
    rw [hz i, abs_zero]
    positivity
  push Not at hy
  set P := nodePoly x
  have hPy : P.eval y ≠ 0 := by
    rw [eval_nodePoly]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hy i).symm
  set c := f y / P.eval y with hc
  set g : ℝ → ℝ := fun t => f t - c * P.eval t with hg
  have hPsmooth := contDiff_eval_poly P k
  have hgc : ContDiff ℝ k g := hf.sub (contDiff_const.mul hPsmooth)
  set S : Finset ℝ := insert y (Finset.univ.image x) with hS
  have hyS : y ∉ Finset.univ.image x := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hy
  have hcard : S.card = k + 1 := by
    rw [hS, Finset.card_insert_of_notMem hyS, Finset.card_image_of_injective _ hx,
      Finset.card_univ, Fintype.card_fin]
  have hgz : ∀ z ∈ S, g z = 0 := by
    intro z hz'
    rw [hS, Finset.mem_insert, Finset.mem_image] at hz'
    rcases hz' with rfl | ⟨i, -, rfl⟩
    · simp only [hg, hc]
      field_simp
      ring
    · have hP0 : P.eval (x i) = 0 := by
        rw [eval_nodePoly]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
      simp [hg, hz i, hP0]
  obtain ⟨ξ, hξ⟩ := exists_iteratedDeriv_eq_zero hgc (fun i => S.orderEmbOfFin hcard i)
    (S.orderEmbOfFin hcard).strictMono (fun i => hgz _ (S.orderEmbOfFin_mem hcard i))
  have hderiv : iteratedDeriv k g ξ = iteratedDeriv k f ξ - c * k.factorial := by
    have h1 : g = f - fun t => c * P.eval t := rfl
    rw [h1, iteratedDeriv_sub hf.contDiffAt (contDiff_const.mul hPsmooth).contDiffAt,
      iteratedDeriv_const_mul c hPsmooth.contDiffAt, iteratedDeriv_nodePoly]
  have hck : |c| * k.factorial ≤ M := by
    have : c * k.factorial = iteratedDeriv k f ξ := by linarith [hderiv.symm.trans hξ]
    calc |c| * k.factorial = |c * k.factorial| := by
          rw [abs_mul, Nat.abs_cast]
      _ = |iteratedDeriv k f ξ| := by rw [this]
      _ ≤ M := hM ξ
  have hfy : f y = c * P.eval y := by rw [hc]; field_simp
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [hfy, abs_mul, eval_nodePoly, Finset.abs_prod]
  have hc' : |c| ≤ M / k.factorial := by rw [le_div_iff₀ hfac]; exact hck
  exact mul_le_mul_of_nonneg_right hc' (Finset.prod_nonneg fun i _ => abs_nonneg _)

/-- **Sharp decay from blindness at `log ℕ`.**  A real `C^k` function with `|f^{(k)}| ≤ M`
vanishing at every `log n`, `n ≥ 2`, satisfies `|f(x)| ≤ M (2 e^{-x})^k` for `x ≥ log 2`. -/
theorem abs_le_of_logNat_zero_sharp {k : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ k f) {M : ℝ}
    (hM : ∀ x, |iteratedDeriv k f x| ≤ M) (hz : ∀ n : ℕ, 2 ≤ n → f (Real.log n) = 0) {y : ℝ}
    (hy : Real.log 2 ≤ y) : |f y| ≤ M * (2 * Real.exp (-y)) ^ k := by
  set n : ℕ := ⌊Real.exp y⌋₊ with hn
  have h2 : (2 : ℝ) ≤ Real.exp y := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hy
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast h2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnle : (n : ℝ) ≤ Real.exp y := Nat.floor_le (Real.exp_pos y).le
  have hn1 : Real.exp y < n + 1 := Nat.lt_floor_add_one _
  have hylo : Real.log n ≤ y := by
    rw [← Real.log_exp y]; exact Real.log_le_log hnpos hnle
  have hyhi : y < Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_exp y]; exact Real.log_lt_log (Real.exp_pos y) hn1
  set x : Fin k → ℝ := fun i => Real.log ((n : ℝ) + i) with hx
  have hxinj : Function.Injective x := fun i j hij => by
    simp only [hx] at hij
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hij
    exact Fin.ext (by exact_mod_cast (add_left_cancel this : ((i : ℕ) : ℝ) = j))
  have hxz : ∀ i, f (x i) = 0 := fun i => by
    have := hz (n + i) (by omega)
    simpa [hx] using this
  have hb := abs_le_div_factorial_mul_prod hf hM x hxinj hxz y
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hnode : ∀ i : Fin k, |y - x i| ≤ ((i : ℝ) + 1) / n := fun i => by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hup : Real.log ((n : ℝ) + (i + 1)) - Real.log n ≤ ((i : ℝ) + 1) / n := by
      rw [← Real.log_div (by positivity) hnpos.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + (i + 1)) / n by positivity)
      have he : ((n : ℝ) + (i + 1)) / n - 1 = ((i : ℝ) + 1) / n := by field_simp; ring
      linarith
    have hxi : x i = Real.log ((n : ℝ) + i) := rfl
    have hxi_lo : Real.log n ≤ x i := by
      rw [hxi]; exact Real.log_le_log hnpos (by linarith)
    have hxi_hi : x i ≤ Real.log ((n : ℝ) + (i + 1)) := by
      rw [hxi]; exact Real.log_le_log (by positivity) (by linarith)
    have hy_hi : y ≤ Real.log ((n : ℝ) + (i + 1)) :=
      hyhi.le.trans (Real.log_le_log (by positivity) (by linarith))
    rw [abs_le]
    constructor <;> linarith
  have hprod : ∏ i : Fin k, |y - x i| ≤ k.factorial / (n : ℝ) ^ k := by
    calc ∏ i : Fin k, |y - x i| ≤ ∏ i : Fin k, (((i : ℝ) + 1) / n) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hnode i)
      _ = k.factorial / (n : ℝ) ^ k := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Fin.prod_univ_eq_prod_range (fun i => (i : ℝ) + 1) k]
          congr 1
          exact_mod_cast Finset.prod_range_add_one_eq_factorial k
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hninv : (n : ℝ)⁻¹ ≤ 2 * Real.exp (-y) := by
    rw [Real.exp_neg, inv_le_comm₀ hnpos (by positivity), mul_inv, inv_inv]
    linarith
  calc |f y| ≤ M / k.factorial * ∏ i, |y - x i| := hb
    _ ≤ M / k.factorial * (k.factorial / (n : ℝ) ^ k) := by gcongr
    _ = M * ((n : ℝ)⁻¹) ^ k := by rw [inv_pow]; field_simp
    _ ≤ M * (2 * Real.exp (-y)) ^ k := by gcongr

/-- **Sharp decay of blind characteristic functions.**  Under the hypotheses of
`norm_charFun_le_of_logNat_blind`, `‖φ_μ(x)‖ ≤ 2 (∫ |t|^k dμ) (2 e^{-|x|})^k` for `|x| ≥ log 2`. -/
theorem norm_charFun_le_of_logNat_blind_sharp {μ : Measure ℝ} [IsFiniteMeasure μ] {k : ℕ}
    (hint : MemLp id k μ) (hblind : ∀ n : ℕ, 2 ≤ n → charFun μ (Real.log n) = 0) {x : ℝ}
    (hx : Real.log 2 ≤ |x|) :
    ‖charFun μ x‖ ≤ 2 * (∫ y, |y| ^ k ∂μ) * (2 * Real.exp (-|x|)) ^ k := by
  have hF : ContDiff ℝ k (charFun μ) := contDiff_charFun hint
  set M := ∫ y, |y| ^ k ∂μ
  have part : ∀ L : ℂ →L[ℝ] ℝ, ‖L‖ ≤ 1 → |L (charFun μ |x|)| ≤ M * (2 * Real.exp (-|x|)) ^ k := by
    intro L hL
    have hLf : ContDiff ℝ k (L ∘ charFun μ) := L.contDiff.comp hF
    refine abs_le_of_logNat_zero_sharp hLf (fun t => ?_) (fun n hn => ?_) hx
    · rw [iteratedDeriv_clm_comp hF L t, ← Real.norm_eq_abs]
      exact (L.le_opNorm _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (norm_iteratedDeriv_charFun_le hint t))
    · simp [hblind n hn]
  have hre := part Complex.reCLM (by rw [Complex.reCLM_norm])
  have him := part Complex.imCLM (by rw [Complex.imCLM_norm])
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  have habs : ‖charFun μ x‖ = ‖charFun μ |x|‖ := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, charFun_neg, Complex.norm_conj]
  rw [habs]
  calc ‖charFun μ |x|‖ ≤ |(charFun μ |x|).re| + |(charFun μ |x|).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by linarith

/-! ### Exponential spectral tails give doubly exponential decay -/

theorem pow_abs_le_factorial_mul_exp {a : ℝ} (ha : 0 < a) (k : ℕ) (t : ℝ) :
    |t| ^ k ≤ k.factorial / a ^ k * Real.exp (a * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a * |t|) (by positivity) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfac, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem memLp_id_of_integrable_exp {μ : Measure ℝ} [IsFiniteMeasure μ] {a : ℝ} (ha : 0 < a)
    (hexp : Integrable (fun t => Real.exp (a * |t|)) μ) (k : ℕ) : MemLp id k μ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using (memLp_zero_iff_aestronglyMeasurable.mpr aestronglyMeasurable_id :
      MemLp (id : ℝ → ℝ) 0 μ)
  rw [← integrable_norm_rpow_iff aestronglyMeasurable_id (by exact_mod_cast hk.ne')
    (ENNReal.natCast_ne_top k)]
  simp only [id, ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  refine (hexp.const_mul (k.factorial / a ^ k)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_abs_le_factorial_mul_exp ha k t

/-- **Blindness turns exponential spectral tails into doubly exponential decay.**  If
`∫ e^{a|t|} dμ < ∞` for some `a > 0` and the characteristic function of `μ` vanishes at every
`log n`, `n ≥ 2`, then `‖φ_μ(x)‖ ≤ 4 (∫ e^{a|t|} dμ) exp(-(a log 2 / 4) e^{|x|})` for
`|x| ≥ log 2`. -/
theorem norm_charFun_le_doubleExp_of_logNat_blind {μ : Measure ℝ} [IsFiniteMeasure μ] {a : ℝ}
    (ha : 0 < a) (hexp : Integrable (fun t => Real.exp (a * |t|)) μ)
    (hblind : ∀ n : ℕ, 2 ≤ n → charFun μ (Real.log n) = 0) {x : ℝ} (hx : Real.log 2 ≤ |x|) :
    ‖charFun μ x‖ ≤
      4 * (∫ t, Real.exp (a * |t|) ∂μ) * Real.exp (-(a * Real.log 2 / 4 * Real.exp |x|)) := by
  set E := ∫ t, Real.exp (a * |t|) ∂μ with hE
  have hE0 : 0 ≤ E := integral_nonneg fun t => (Real.exp_pos _).le
  set u := a * Real.exp |x| / 4 with hu
  have hu0 : 0 < u := by positivity
  set k : ℕ := ⌊u⌋₊ with hk
  have hku : (k : ℝ) ≤ u := Nat.floor_le hu0.le
  have hku' : u < k + 1 := Nat.lt_floor_add_one u
  have hmom : ∫ y, |y| ^ k ∂μ ≤ k.factorial / a ^ k * E := by
    rw [hE, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
      (hexp.const_mul _) (Filter.Eventually.of_forall fun y => pow_abs_le_factorial_mul_exp ha k y)
  have hsharp := norm_charFun_le_of_logNat_blind_sharp (memLp_id_of_integrable_exp ha hexp k) hblind hx
  have hq : (k.factorial : ℝ) / a ^ k * (2 * Real.exp (-|x|)) ^ k ≤ (1 / 2 : ℝ) ^ k := by
    have hbase : 2 * Real.exp (-|x|) / a = 1 / (2 * u) := by
      rw [hu, Real.exp_neg]; field_simp; ring
    have hrw : (k.factorial : ℝ) / a ^ k * (2 * Real.exp (-|x|)) ^ k =
        k.factorial * (1 / (2 * u)) ^ k := by
      rw [← hbase, div_pow]; ring
    rw [hrw]
    rcases Nat.eq_zero_or_pos k with h0 | hkpos
    · rw [h0]; simp
    · have hfk : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
      have hkpos' : (0 : ℝ) < k := by exact_mod_cast hkpos
      calc (k.factorial : ℝ) * (1 / (2 * u)) ^ k ≤ (k : ℝ) ^ k * (1 / (2 * u)) ^ k := by gcongr
        _ = ((k : ℝ) / (2 * u)) ^ k := by rw [← mul_pow, mul_one_div]
        _ ≤ (1 / 2 : ℝ) ^ k := by
            refine pow_le_pow_left₀ (by positivity) ?_ k
            rw [div_le_iff₀ (by positivity)]
            linarith
  have hhalf : (1 / 2 : ℝ) ^ k ≤ 2 * Real.exp (-(a * Real.log 2 / 4 * Real.exp |x|)) := by
    have h1 : (1 / 2 : ℝ) ^ k = Real.exp (-(k * Real.log 2)) := by
      rw [neg_mul_eq_mul_neg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have h2 : 2 * Real.exp (-(a * Real.log 2 / 4 * Real.exp |x|)) =
        Real.exp (-((u - 1) * Real.log 2)) := by
      rw [show -((u - 1) * Real.log 2) = Real.log 2 + -(u * Real.log 2) by ring, Real.exp_add,
        Real.exp_log (by norm_num), hu]
      congr 2
      ring
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  calc ‖charFun μ x‖ ≤ 2 * (∫ y, |y| ^ k ∂μ) * (2 * Real.exp (-|x|)) ^ k := hsharp
    _ ≤ 2 * (k.factorial / a ^ k * E) * (2 * Real.exp (-|x|)) ^ k := by gcongr
    _ = 2 * E * ((k.factorial : ℝ) / a ^ k * (2 * Real.exp (-|x|)) ^ k) := by ring
    _ ≤ 2 * E * (2 * Real.exp (-(a * Real.log 2 / 4 * Real.exp |x|))) :=
        mul_le_mul_of_nonneg_left (hq.trans hhalf) (by positivity)
    _ = 4 * E * Real.exp (-(a * Real.log 2 / 4 * Real.exp |x|)) := by ring

end

end RHTower.BlindLogNodeDecay
