import GaloisForLFunctions.HTGeometry.IteratedDerivativeGrowth
import GaloisForLFunctions.HTGeometry.ValuePreimageInfinite
import GaloisForLFunctions.HTGeometry.EulerWildProximity
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.CompositionInnerDecomposition

/-!
# A function vanishing on many level sets of a transcendental entire function

Let `g` be a transcendental entire function and let

`N(z) = Σ_μ P_μ(g(z)) · H_μ(z, g(z), g'(z), …, g^{(n)}(z))`

with polynomials `P_μ` of degree at most `D` and polynomials `H_μ`.  If `N` vanishes wherever `g`
takes one of `s` distinct values `t_j`, and `s` exceeds `D` by a margin depending only on `n` and
the degrees of the `H_μ`, then `N ≡ 0`.

At a point where `g = t_j` with multiplicity `k`, `N` vanishes and `g'` vanishes to order `k − 1`,
so `Σ_j N(r, t_j, g) ≤ N(r, 0, N) + N(r, 0, g')`.  The first main theorem bounds the right side by
`m(r, N) + T(r, g')`, and `m(r, N) ≤ D·T(r,g) + (small multiples of the jet characteristics)`.
Along one sequence of radii the jet characteristics are at most `2^{n+2} T(r,g)` and the error of
the second main theorem `(s − 2)T(r,g) ≤ Σ_j N(r, t_j, g) + S(r,g)` is negligible, which leaves an
impossible inequality.  This is the analytic step of Steinmetz's reduction theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn Filter Set

noncomputable section

/-! ### Pointwise `log⁺` bounds for polynomial expressions -/

/-- The value of a polynomial of degree at most `D`: `log⁺|P(w)| ≤ D·log⁺|w| + log⁺ Σ|a_i|`. -/
theorem posLog_norm_polynomial_eval_le (P : Polynomial ℂ) {D : ℕ} (hD : P.natDegree ≤ D)
    (w : ℂ) :
    log⁺ ‖P.eval w‖ ≤ D * log⁺ ‖w‖ + log⁺ (∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖) := by
  set M : ℝ := max 1 ‖w‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hwM : ‖w‖ ≤ M := le_max_right _ _
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hbound : ‖P.eval w‖ ≤ (∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖) * M ^ D := by
    rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < D + 1), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_pow]
    gcongr ‖P.coeff i‖ * ?_
    have hi : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc ‖w‖ ^ i ≤ M ^ i := pow_le_pow_left₀ (norm_nonneg _) hwM i
      _ ≤ M ^ D := pow_le_pow_right₀ hM1 hi
  have hlogM : log⁺ M = log⁺ ‖w‖ := by
    rw [posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hM1),
      posLog_eq_log_max_one (norm_nonneg _)]
  calc log⁺ ‖P.eval w‖
      ≤ log⁺ ((∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖) * M ^ D) :=
        posLog_le_posLog (norm_nonneg _) hbound
    _ ≤ log⁺ (∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖) + log⁺ (M ^ D) := posLog_mul
    _ = D * log⁺ ‖w‖ + log⁺ (∑ i ∈ Finset.range (D + 1), ‖P.coeff i‖) := by
        rw [posLog_pow, hlogM]
        ring

/-- The value of a multivariate polynomial:
`log⁺|H(y)| ≤ deg H · Σ_i log⁺|y_i| + log⁺ Σ|coefficients|`. -/
theorem posLog_norm_mvPolynomial_eval_le {σ : Type*} [Fintype σ] (H : MvPolynomial σ ℂ)
    (y : σ → ℂ) :
    log⁺ ‖MvPolynomial.eval y H‖
      ≤ H.totalDegree * ∑ i, log⁺ ‖y i‖ + log⁺ (∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖) := by
  classical
  set M : σ → ℝ := fun i => max 1 ‖y i‖ with hM
  have hM1 : ∀ i, 1 ≤ M i := fun i => le_max_left _ _
  have hyM : ∀ i, ‖y i‖ ≤ M i := fun i => le_max_right _ _
  set d := H.totalDegree with hd
  have hA0 : 0 ≤ ∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖ :=
    Finset.sum_nonneg fun α _ => norm_nonneg _
  have hmono : ∀ α ∈ H.support, ‖∏ i ∈ α.support, y i ^ α i‖ ≤ ∏ i, M i ^ d := by
    intro α hα
    rw [norm_prod]
    refine (Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_).trans
      (Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
        (fun i _ => pow_nonneg (zero_le_one.trans (hM1 i)) d)
        fun i _ _ => one_le_pow₀ (hM1 i))
    rw [norm_pow]
    have hαi : α i ≤ d := by
      have h1 : α i ≤ α.sum fun _ e => e := by
        rw [Finsupp.sum]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) hi
        · rw [Finsupp.notMem_support_iff.mp hi]
          exact Nat.zero_le _
      exact h1.trans (MvPolynomial.le_totalDegree hα)
    calc ‖y i‖ ^ α i ≤ M i ^ α i := pow_le_pow_left₀ (norm_nonneg _) (hyM i) _
      _ ≤ M i ^ d := pow_le_pow_right₀ (hM1 i) hαi
  have hbound : ‖MvPolynomial.eval y H‖
      ≤ (∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖) * ∏ i, M i ^ d := by
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
    rw [norm_mul]
    gcongr ‖MvPolynomial.coeff α H‖ * ?_
    exact hmono α hα
  have hprod1 : 1 ≤ ∏ i, M i ^ d := Finset.one_le_prod fun i _ => one_le_pow₀ (hM1 i)
  have hlogM : ∀ i, Real.log (M i) = log⁺ ‖y i‖ := fun i =>
    (posLog_eq_log_max_one (norm_nonneg _)).symm
  have hlogprod : log⁺ (∏ i, M i ^ d) = d * ∑ i, log⁺ ‖y i‖ := by
    rw [posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hprod1),
      Real.log_prod (fun i _ => (pow_pos (by linarith [hM1 i]) d).ne'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow, hlogM]
  calc log⁺ ‖MvPolynomial.eval y H‖
      ≤ log⁺ ((∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖) * ∏ i, M i ^ d) :=
        posLog_le_posLog (norm_nonneg _) hbound
    _ ≤ log⁺ (∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖) + log⁺ (∏ i, M i ^ d) := posLog_mul
    _ = d * ∑ i, log⁺ ‖y i‖ + log⁺ (∑ α ∈ H.support, ‖MvPolynomial.coeff α H‖) := by
        rw [hlogprod]
        ring

/-- A common `log⁺` bound on the terms bounds the sum up to `log⁺` of their number. -/
theorem posLog_norm_sum_le_of_forall {ι : Type*} (s : Finset ι) (x : ι → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i ∈ s, log⁺ ‖x i‖ ≤ B) :
    log⁺ ‖∑ i ∈ s, x i‖ ≤ log⁺ (s.card : ℝ) + B := by
  have hx : ∀ i ∈ s, ‖x i‖ ≤ Real.exp B := by
    intro i hi
    have h1 := h i hi
    rcases le_total ‖x i‖ 1 with hle | hle
    · exact hle.trans (Real.one_le_exp hB)
    · rw [posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; exact hle)] at h1
      calc ‖x i‖ = Real.exp (Real.log ‖x i‖) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp B := Real.exp_le_exp.mpr h1
  have hsum : ‖∑ i ∈ s, x i‖ ≤ (s.card : ℝ) * Real.exp B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ s, ‖x i‖ ≤ ∑ _i ∈ s, Real.exp B := Finset.sum_le_sum hx
      _ = (s.card : ℝ) * Real.exp B := by rw [Finset.sum_const, nsmul_eq_mul]
  calc log⁺ ‖∑ i ∈ s, x i‖ ≤ log⁺ ((s.card : ℝ) * Real.exp B) :=
        posLog_le_posLog (norm_nonneg _) hsum
    _ ≤ log⁺ (s.card : ℝ) + log⁺ (Real.exp B) := posLog_mul
    _ = log⁺ (s.card : ℝ) + B := by
        have hexp : log⁺ (Real.exp B) = B := by
          rw [posLog_eq_log (by rw [abs_of_pos (Real.exp_pos B)]; exact Real.one_le_exp hB),
            Real.log_exp]
        rw [hexp]

/-- **Pointwise `log⁺` bounds integrate to proximity bounds.** -/
theorem proximity_top_le_of_forall_posLog_le {f : ℂ → ℂ} (hf : Meromorphic f) {ι : Type*}
    (s : Finset ι) (φ : ι → ℂ → ℂ) (hφ : ∀ i ∈ s, Meromorphic (φ i)) (c : ι → ℝ) (C : ℝ)
    (h : ∀ z, log⁺ ‖f z‖ ≤ ∑ i ∈ s, c i * log⁺ ‖φ i z‖ + C) (r : ℝ) :
    proximity f ⊤ r ≤ ∑ i ∈ s, c i * proximity (φ i) ⊤ r + C := by
  have hint : ∀ i ∈ s, CircleIntegrable (fun z => log⁺ ‖φ i z‖) 0 r :=
    fun i hi => MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hφ i hi x)
  have hint' : ∀ i ∈ s, CircleIntegrable (fun z => c i * log⁺ ‖φ i z‖) 0 r :=
    fun i hi => (hint i hi).const_fun_smul (a := c i)
  rw [proximity_top]
  calc circleAverage (fun z => log⁺ ‖f z‖) 0 r
      ≤ circleAverage (fun z => ∑ i ∈ s, c i * log⁺ ‖φ i z‖ + C) 0 r := by
        apply circleAverage_mono
        · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x _ => hf x)
        · exact (CircleIntegrable.fun_sum s hint').add (circleIntegrable_const _ _ _)
        · exact fun z _ => h z
    _ = ∑ i ∈ s, c i * proximity (φ i) ⊤ r + C := by
        have hsplit : (fun z => ∑ i ∈ s, c i * log⁺ ‖φ i z‖ + C)
            = (fun z => ∑ i ∈ s, c i * log⁺ ‖φ i z‖) + fun _ => C := rfl
        rw [hsplit, circleAverage_add (CircleIntegrable.fun_sum s hint')
          (circleIntegrable_const _ _ _), circleAverage_const, ← Finset.sum_fn,
          circleAverage_sum hint']
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [proximity_top]
        exact circleAverage_fun_smul (a := c i) (f := fun z => log⁺ ‖φ i z‖)

/-! ### Counting the level sets -/

/-- An entire function that is nonzero somewhere has finite order everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) {w : ℂ}
    (hw : F w ≠ 0) (z : ℂ) : analyticOrderAt F z ≠ ⊤ := by
  have hFan : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  refine hFan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ w)
    (mem_univ z) ?_
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hw)]
  exact ENat.zero_ne_top

/-- The divisor of an entire function at a point of finite order. -/
theorem divisor_entire_apply {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z : ℂ} {k : ℕ}
    (hk : analyticOrderAt F z = k) : MeromorphicOn.divisor F univ z = k := by
  have hmero : MeromorphicOn F univ := fun x _ => (hF.analyticAt x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (mem_univ z), (hF.analyticAt z).meromorphicOrderAt_eq, hk]
  simp

/-- **The level sets of `g` are counted by the zeros of `N` and of `g'`.**  If an entire `N ≢ 0`
vanishes wherever the nonconstant entire `g` takes one of the distinct values `t_j`, then
`Σ_j N(r, t_j, g) ≤ N(r, 0, N) + N(r, 0, g')`. -/
theorem sum_logCounting_le_of_vanishing {g N : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hN : Differentiable ℂ N) (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) {w₀ : ℂ} (hw₀ : N w₀ ≠ 0)
    {s : ℕ} (t : Fin s → ℂ) (ht : Function.Injective t) (hvan : ∀ z j, g z = t j → N z = 0)
    {r : ℝ} (hr : 1 ≤ r) :
    ∑ j, logCounting g (t j : WithTop ℂ) r ≤ logCounting N 0 r + logCounting (deriv g) 0 r := by
  classical
  have hgd : Differentiable ℂ (deriv g) := by
    simpa [iteratedDeriv_one] using differentiable_iteratedDeriv_entire hg 1
  have hgan : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hNan : AnalyticOnNhd ℂ N univ := hN.differentiableOn.analyticOnNhd isOpen_univ
  have hgdan : AnalyticOnNhd ℂ (deriv g) univ := hgd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨w₁, hw₁⟩ : ∃ w, deriv g w ≠ 0 := exists_deriv_ne_zero hg hgnc
  have hshift : ∀ j, ∃ w, g w - t j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    exact hgnc ⟨t j, fun z => sub_eq_zero.mp (hcon z)⟩
  have hgt : ∀ j, Differentiable ℂ fun z => g z - t j := fun j => hg.sub_const (t j)
  have hgtan : ∀ j, AnalyticOnNhd ℂ (fun z => g z - t j) univ :=
    fun j => (hgt j).differentiableOn.analyticOnNhd isOpen_univ
  -- the divisors
  set Dj : Fin s → Function.locallyFinsupp ℂ ℤ :=
    fun j => MeromorphicOn.divisor (fun z => g z - t j) univ with hDjdef
  set DN := MeromorphicOn.divisor N univ with hDN
  set Dg := MeromorphicOn.divisor (deriv g) univ with hDg
  have hDj0 : ∀ j, 0 ≤ Dj j := fun j => AnalyticOnNhd.divisor_nonneg (hgtan j)
  have hDN0 : 0 ≤ DN := AnalyticOnNhd.divisor_nonneg hNan
  have hDg0 : 0 ≤ Dg := AnalyticOnNhd.divisor_nonneg hgdan
  -- the pointwise inequality
  have hle : ∑ j, Dj j ≤ DN + Dg := by
    intro z
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    by_cases hz : ∃ j, g z = t j
    · obtain ⟨j₀, hj₀⟩ := hz
      have hother : ∀ j, j ≠ j₀ → Dj j z = 0 := by
        intro j hj
        have hne : g z - t j ≠ 0 := by
          rw [hj₀, sub_ne_zero]
          exact fun h => hj (ht h).symm
        rw [hDjdef]
        exact divisor_entire_apply (hgt j) (analyticOrderAt_eq_zero.mpr (Or.inr hne))
      rw [Finset.sum_eq_single j₀ (fun j _ hj => hother j hj) (fun h => absurd
        (Finset.mem_univ j₀) h)]
      -- orders at `z`
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
        (analyticOrderAt_ne_top_of_entire (hgt j₀) (hshift j₀).choose_spec z)
      obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_entire hgd hw₁ z)
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_entire hN hw₀ z)
      have hderiv := (hgan z (mem_univ z)).analyticOrderAt_deriv_add_one
      have hfun : (fun w => g w - g z) = fun w => g w - t j₀ := by
        funext w
        rw [hj₀]
      rw [hfun, ← hk, ← he] at hderiv
      have hke : e + 1 = k := by exact_mod_cast hderiv
      have ha1 : 1 ≤ a := by
        by_contra ha0
        have ha0' : a = 0 := by omega
        rw [ha0'] at ha
        have := analyticOrderAt_eq_zero.mp ha.symm
        rcases this with hna | hne
        · exact hna (hN.analyticAt z)
        · exact hne (hvan z j₀ hj₀)
      rw [show Dj j₀ z = k from divisor_entire_apply (hgt j₀) hk.symm,
        show DN z = a from divisor_entire_apply hN ha.symm,
        show Dg z = e from divisor_entire_apply hgd he.symm]
      omega
    · push Not at hz
      have hzero : ∀ j, Dj j z = 0 := by
        intro j
        have hne : g z - t j ≠ 0 := sub_ne_zero.mpr (hz j)
        exact divisor_entire_apply (hgt j) (analyticOrderAt_eq_zero.mpr (Or.inr hne))
      simp only [hzero, Finset.sum_const_zero]
      exact add_nonneg (hDN0 z) (hDg0 z)
  -- counting functions
  have hlhs : ∑ j, logCounting g (t j : WithTop ℂ) r
      = Function.locallyFinsuppWithin.logCounting (∑ j, Dj j) r := by
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logCounting_coe, posPart_eq_self.mpr (hDj0 j)]
  have hNc : logCounting N 0 r = Function.locallyFinsuppWithin.logCounting DN r := by
    have h0 : (0 : WithTop ℂ) = ((0 : ℂ) : WithTop ℂ) := rfl
    rw [h0, logCounting_coe]
    simp only [sub_zero]
    rw [posPart_eq_self.mpr hDN0]
  have hgc : logCounting (deriv g) 0 r = Function.locallyFinsuppWithin.logCounting Dg r := by
    have h0 : (0 : WithTop ℂ) = ((0 : ℂ) : WithTop ℂ) := rfl
    rw [h0, logCounting_coe]
    simp only [sub_zero]
    rw [posPart_eq_self.mpr hDg0]
  rw [hlhs, hNc, hgc, ← Pi.add_apply (Function.locallyFinsuppWithin.logCounting DN), ← map_add]
  exact Function.locallyFinsuppWithin.logCounting_le hle hr

/-! ### The contradiction -/

/-- The first main theorem for an entire function: `N(r, 0, F) ≤ m(r, F) + O(1)`. -/
theorem logCounting_zero_le_proximity_add {F : ℂ → ℂ} (hF : Differentiable ℂ F) (r : ℝ) :
    logCounting F 0 r
      ≤ proximity F ⊤ r + max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
  have hm : Meromorphic F := fun z => (hF.analyticAt z).meromorphicAt
  have hFan : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have h := proximity_inv_top_le hm (r := r)
  have hnn : 0 ≤ proximity (fun z => (F z)⁻¹) ⊤ r := proximity_nonneg r
  rw [characteristic_top_eq_proximity_of_analyticOnNhd hFan] at h
  linarith

/-- Finitely many distinct points are uniformly separated. -/
theorem exists_pos_le_norm_sub_of_injective {s : ℕ} (t : Fin s → ℂ)
    (ht : Function.Injective t) : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ ‖t i - t j‖ := by
  classical
  set S := (Finset.univ : Finset (Fin s × Fin s)).filter (fun p => p.1 ≠ p.2) with hS
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun p => ‖t p.1 - t p.2‖) hne
    have hp2 := (Finset.mem_filter.mp hp).2
    refine ⟨‖t p.1 - t p.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hp2 (ht h)),
      fun i j hij => hmin (i, j) (by simp [hS, hij])⟩
  · exact ⟨1, one_pos, fun i j hij => absurd ⟨(i, j), by simp [hS, hij]⟩ hne⟩

/-- A polynomial in entire functions is entire. -/
theorem differentiable_mvPolynomial_eval_comp {σ : Type*} {v : σ → ℂ → ℂ}
    (hv : ∀ i, Differentiable ℂ (v i)) (H : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z => MvPolynomial.eval (fun i => v i z) H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa using hp.fun_add hq
  | mul_X p i hp => simpa using hp.fun_mul (hv i)

/-- **A function vanishing on `s` level sets of a transcendental entire function is zero.**  Let
`N = Σ_μ P_μ(g) · H_μ(z, g, …, g^{(n)})` with `deg P_μ ≤ D`.  If `N` vanishes wherever `g` takes one
of `s` distinct values and `s ≥ D + 4 + ((n+1)·Σ_μ deg H_μ + 1)·2^{n+2}`, then `N ≡ 0`. -/
theorem sum_eq_zero_of_vanishing_on_levels {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) {m n s D : ℕ}
    (P : Fin (m + 1) → Polynomial ℂ) (hPD : ∀ μ, (P μ).natDegree ≤ D)
    (H : Fin (m + 1) → MvPolynomial (Fin (n + 2)) ℂ) (t : Fin s → ℂ)
    (ht : Function.Injective t)
    (hs : D + 4 + ((n + 1) * ∑ μ, (H μ).totalDegree + 1) * 2 ^ (n + 2) ≤ s)
    (hvan : ∀ z j, g z = t j → ∑ μ, (P μ).eval (g z)
      * MvPolynomial.eval (Fin.cons z fun i : Fin (n + 1) => iteratedDeriv i g z) (H μ) = 0)
    (z₀ : ℂ) :
    ∑ μ, (P μ).eval (g z₀)
      * MvPolynomial.eval (Fin.cons z₀ fun i : Fin (n + 1) => iteratedDeriv i g z₀) (H μ) = 0 := by
  classical
  by_contra hz₀
  set N : ℂ → ℂ := fun w => ∑ μ, (P μ).eval (g w)
    * MvPolynomial.eval (Fin.cons w fun i : Fin (n + 1) => iteratedDeriv i g w) (H μ) with hNdef
  have hgd : ∀ j, Differentiable ℂ (iteratedDeriv j g) := differentiable_iteratedDeriv_entire hg
  have hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c :=
    fun ⟨c, hc⟩ => hgnp ⟨Polynomial.C c, fun z => by simpa using hc z⟩
  -- `N` is entire
  have hjet : ∀ i : Fin (n + 2), Differentiable ℂ
      (fun w => (Fin.cons w fun j : Fin (n + 1) => iteratedDeriv j g w : Fin (n + 2) → ℂ) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using hgd j
  have hNd : Differentiable ℂ N := by
    refine Differentiable.fun_sum fun μ _ => ?_
    exact ((P μ).differentiable.comp hg).mul
      (differentiable_mvPolynomial_eval_comp hjet (H μ))
  -- constants of the pointwise bound
  set E : ℕ := ∑ μ, (H μ).totalDegree with hE
  set A : ℝ := ∑ μ, log⁺ (∑ i ∈ Finset.range (D + 1), ‖(P μ).coeff i‖) with hA
  set B : ℝ := ∑ μ, log⁺ (∑ α ∈ (H μ).support, ‖MvPolynomial.coeff α (H μ)‖) with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun μ _ => posLog_nonneg
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun μ _ => posLog_nonneg
  have hpt : ∀ w, log⁺ ‖N w‖ ≤ D * log⁺ ‖g w‖ + E * log⁺ ‖w‖
      + E * ∑ j : Fin (n + 1), log⁺ ‖iteratedDeriv j g w‖ + (log⁺ ((m + 1 : ℕ) : ℝ) + A + B) := by
    intro w
    set J : ℝ := log⁺ ‖w‖ + ∑ j : Fin (n + 1), log⁺ ‖iteratedDeriv j g w‖ with hJ
    have hJ0 : 0 ≤ J := add_nonneg posLog_nonneg (Finset.sum_nonneg fun j _ => posLog_nonneg)
    have hterm : ∀ μ ∈ (Finset.univ : Finset (Fin (m + 1))),
        log⁺ ‖(P μ).eval (g w) * MvPolynomial.eval
          (Fin.cons w fun i : Fin (n + 1) => iteratedDeriv i g w) (H μ)‖
          ≤ D * log⁺ ‖g w‖ + A + (E * J + B) := by
      intro μ _
      have h1 := posLog_norm_polynomial_eval_le (P μ) (hPD μ) (g w)
      have h2 := posLog_norm_mvPolynomial_eval_le (H μ)
        (Fin.cons w fun i : Fin (n + 1) => iteratedDeriv i g w)
      rw [Fin.sum_univ_succ] at h2
      simp only [Fin.cons_zero, Fin.cons_succ] at h2
      have hAμ : log⁺ (∑ i ∈ Finset.range (D + 1), ‖(P μ).coeff i‖) ≤ A :=
        Finset.single_le_sum (f := fun ν => log⁺ (∑ i ∈ Finset.range (D + 1), ‖(P ν).coeff i‖))
          (fun _ _ => posLog_nonneg) (Finset.mem_univ μ)
      have hBμ : log⁺ (∑ α ∈ (H μ).support, ‖MvPolynomial.coeff α (H μ)‖) ≤ B :=
        Finset.single_le_sum
          (f := fun ν => log⁺ (∑ α ∈ (H ν).support, ‖MvPolynomial.coeff α (H ν)‖))
          (fun _ _ => posLog_nonneg) (Finset.mem_univ μ)
      have hdeg : ((H μ).totalDegree : ℝ) ≤ E := by
        rw [hE]
        exact_mod_cast Finset.single_le_sum (f := fun ν => (H ν).totalDegree)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
      have h3 : ((H μ).totalDegree : ℝ) * J ≤ E * J := mul_le_mul_of_nonneg_right hdeg hJ0
      calc log⁺ ‖(P μ).eval (g w) * MvPolynomial.eval
            (Fin.cons w fun i : Fin (n + 1) => iteratedDeriv i g w) (H μ)‖
          ≤ log⁺ ‖(P μ).eval (g w)‖ + log⁺ ‖MvPolynomial.eval
            (Fin.cons w fun i : Fin (n + 1) => iteratedDeriv i g w) (H μ)‖ := by
            rw [norm_mul]
            exact posLog_mul
        _ ≤ D * log⁺ ‖g w‖ + A + (E * J + B) := by
            rw [hJ]
            linarith
    have hbnd0 : 0 ≤ D * log⁺ ‖g w‖ + A + (E * J + B) := by
      have : 0 ≤ (D : ℝ) * log⁺ ‖g w‖ := mul_nonneg (Nat.cast_nonneg _) posLog_nonneg
      have : 0 ≤ (E : ℝ) * J := mul_nonneg (Nat.cast_nonneg _) hJ0
      linarith
    have hsum := posLog_norm_sum_le_of_forall Finset.univ _ hbnd0 hterm
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    change log⁺ ‖N w‖ ≤ _ at hsum
    rw [hJ, mul_add] at hsum
    linarith
  -- the proximity bound
  have hgm : Meromorphic g := fun z => (hg.analyticAt z).meromorphicAt
  have hgjm : ∀ j, Meromorphic (iteratedDeriv j g) :=
    fun j z => ((hgd j).analyticAt z).meromorphicAt
  have hNm : Meromorphic N := fun z => (hNd.analyticAt z).meromorphicAt
  set φ : Option (Option (Fin (n + 1))) → ℂ → ℂ := fun o =>
    Option.elim o g (fun o' => Option.elim o' (fun w => w) (fun j => iteratedDeriv j g)) with hφ
  set c : Option (Option (Fin (n + 1))) → ℝ := fun o => Option.elim o (D : ℝ) (fun _ => (E : ℝ))
    with hc
  have hφm : ∀ o ∈ (Finset.univ : Finset (Option (Option (Fin (n + 1))))), Meromorphic (φ o) := by
    rintro (_ | _ | j) _
    · exact hgm
    · exact fun z => analyticAt_id.meromorphicAt
    · exact hgjm j
  set C₀ : ℝ := log⁺ ((m + 1 : ℕ) : ℝ) + A + B with hC₀
  have hpt' : ∀ w, log⁺ ‖N w‖ ≤ ∑ o, c o * log⁺ ‖φ o w‖ + C₀ := by
    intro w
    simp only [Fintype.sum_option, hφ, hc, Option.elim, ← Finset.mul_sum]
    linarith [hpt w]
  have hprox : ∀ r, proximity N ⊤ r ≤ D * proximity g ⊤ r + E * Real.posLog |r|
      + E * ∑ j : Fin (n + 1), proximity (iteratedDeriv j g) ⊤ r + C₀ := by
    intro r
    have h := proximity_top_le_of_forall_posLog_le hNm Finset.univ φ hφm c C₀ hpt' r
    simp only [Fintype.sum_option, hφ, hc, Option.elim, ← Finset.mul_sum] at h
    rw [proximity_id_eq] at h
    linarith
  -- the second main theorem at the values `t_j`
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_injective t ht
  have hgo : ∀ z, meromorphicOrderAt g z ≠ ⊤ :=
    fun z => meromorphicOrderAt_iteratedDeriv_ne_top hg hgnp 0 z
  obtain ⟨Csmt, hsmt⟩ := exists_sub_two_characteristic_le_sum_logCounting hg t hδ hsep hgo
  have hgdo : ∀ z, meromorphicOrderAt (deriv g) z ≠ ⊤ := by
    intro z
    simpa [iteratedDeriv_one] using meromorphicOrderAt_iteratedDeriv_ne_top hg hgnp 1 z
  have hcod : ∀ r : ℝ, ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv g z ≠ 0 := by
    intro r
    have hdan : AnalyticOnNhd ℂ (deriv g) Set.univ :=
      (hg.differentiableOn.analyticOnNhd isOpen_univ).deriv
    have hmero : MeromorphicOn (deriv g) (sphere (0 : ℂ) |r|) :=
      fun x _ => (hdan x (Set.mem_univ x)).meromorphicAt
    exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmero fun u _ => hgdo u
  -- one sequence of radii for the jets and the error
  obtain ⟨rn, Cj, hrn, -, hCj0, hjb, herr⟩ :=
    exists_radii_jet_bound_and_error hg hgnp (n + 1) t (Z := ∅) MeasureTheory.measure_empty
  -- the growth of the characteristic along the radii
  have hdiv := (tendsto_characteristic_div_log_atTop hg hgnp).comp hrn
  have hTtop := (tendsto_characteristic_atTop_of_not_polynomial hg hgnp).comp hrn
  -- constants
  obtain ⟨w₀, hw₀⟩ : ∃ w, N w ≠ 0 := ⟨z₀, hz₀⟩
  set K : ℝ := 2 ^ (n + 1 + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set CN : ℝ := max |Real.log ‖N 0‖| |Real.log ‖meromorphicTrailingCoeffAt N 0‖| with hCN
  set Cg : ℝ := max |Real.log ‖deriv g 0‖| |Real.log ‖meromorphicTrailingCoeffAt (deriv g) 0‖|
    with hCg
  have hgdiff : Differentiable ℂ (deriv g) := by simpa [iteratedDeriv_one] using hgd 1
  have hgan : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hgdan : AnalyticOnNhd ℂ (deriv g) univ := hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hsR : ((D : ℝ) + 4 + (((n : ℝ) + 1) * E + 1) * K) ≤ s := by
    have := hs
    rw [hK]
    exact_mod_cast this
  -- eventually all estimates hold
  have hev : ∀ᶠ k in atTop, characteristic g ⊤ (rn k)
      ≤ 4 * (E * ((n : ℝ) + 1) * Cj + Cj + CN + Cg + C₀ + Csmt) := by
    have hlogsmall : ∀ᶠ k in atTop, (E : ℝ) * Real.log (rn k) ≤ characteristic g ⊤ (rn k) / 4 := by
      rcases Nat.eq_zero_or_pos E with hE0 | hEpos
      · filter_upwards [hTtop.eventually_ge_atTop 0] with k hk
        simp only [Function.comp_apply] at hk
        rw [hE0]
        simp only [Nat.cast_zero, zero_mul]
        linarith
      · have hEr : (0 : ℝ) < E := by exact_mod_cast hEpos
        filter_upwards [hdiv.eventually_ge_atTop (4 * E), hrn.eventually_ge_atTop (Real.exp 1)]
          with k hk hr
        have hlog : 0 < Real.log (rn k) := by
          have : (1 : ℝ) < rn k := lt_of_lt_of_le (by
            have := Real.add_one_le_exp 1
            linarith) hr
          exact Real.log_pos this
        simp only [Function.comp_apply] at hk
        rw [le_div_iff₀ hlog] at hk
        linarith
    filter_upwards [hjb, herr (1 / 2) (by norm_num), hlogsmall, hrn.eventually_ge_atTop 1,
      hTtop.eventually_ge_atTop 0] with k hjk herrk hlogk hr1 hT0
    set r := rn k with hr
    set T := characteristic g ⊤ r with hT
    -- the second main theorem
    have h1 := hsmt r hr1 (hcod r)
    -- counting the level sets
    have h2 := sum_logCounting_le_of_vanishing hg hNd hgnc hw₀ t ht (fun z j hzj => hvan z j hzj)
      hr1
    have h3 := logCounting_zero_le_proximity_add hNd r
    have h4 := logCounting_zero_le_proximity_add hgdiff r
    have h5 := hprox r
    -- characteristics of the jets
    have hTg : proximity g ⊤ r = T := by
      rw [hT, characteristic_top_eq_proximity_of_analyticOnNhd hgan]
    have hjetT : ∀ j : Fin (n + 1), proximity (iteratedDeriv j g) ⊤ r ≤ K * T + Cj := by
      intro j
      have h := hjk j (by omega)
      rw [characteristic_top_eq_proximity_of_analyticOnNhd
        ((hgd j).differentiableOn.analyticOnNhd isOpen_univ)] at h
      rw [hK]
      exact h
    have hsumj : ∑ j : Fin (n + 1), proximity (iteratedDeriv j g) ⊤ r
        ≤ ((n : ℝ) + 1) * (K * T + Cj) := by
      calc ∑ j : Fin (n + 1), proximity (iteratedDeriv j g) ⊤ r
          ≤ ∑ _j : Fin (n + 1), (K * T + Cj) := Finset.sum_le_sum fun j _ => hjetT j
        _ = ((n : ℝ) + 1) * (K * T + Cj) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hgT : proximity (deriv g) ⊤ r ≤ K * T + Cj := by
      have h := hjk 1 (by omega)
      rw [iteratedDeriv_one, characteristic_top_eq_proximity_of_analyticOnNhd hgdan] at h
      rw [hK]
      exact h
    have hlogr : Real.posLog |r| = Real.log r := by
      rw [abs_of_nonneg (by linarith),
        posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hr1)]
    rw [hlogr, hTg] at h5
    -- assemble
    have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    have hsumE : (E : ℝ) * ∑ j : Fin (n + 1), proximity (iteratedDeriv j g) ⊤ r
        ≤ E * (((n : ℝ) + 1) * (K * T + Cj)) := mul_le_mul_of_nonneg_left hsumj hE0
    have herrT : (∑ i : Fin s, proximity (fun z => deriv g z / (g z - t i)) ⊤ r)
        + proximity (fun z => deriv g z / g z) ⊤ r ≤ T / 2 := by
      have := herrk
      rw [one_div, ← div_eq_inv_mul] at this
      exact this
    have hkey : ((s : ℝ) - 2) * T ≤ D * T + E * (((n : ℝ) + 1) * (K * T + Cj)) + (K * T + Cj)
        + T / 2 + T / 4 + (CN + Cg + C₀ + Csmt) := by
      linarith
    have hT0' : 0 ≤ T := by simpa using hT0
    have hcoef : 2 * T ≤ ((s : ℝ) - 2 - D - E * ((n : ℝ) + 1) * K - K) * T := by
      have hc2 : (2 : ℝ) ≤ (s : ℝ) - 2 - D - E * ((n : ℝ) + 1) * K - K := by
        have h := hsR
        have hexp : ((n : ℝ) + 1) * E * K = E * ((n : ℝ) + 1) * K := by ring
        rw [add_mul, one_mul, hexp] at h
        linarith
      exact mul_le_mul_of_nonneg_right hc2 hT0'
    have hexp1 : ((s : ℝ) - 2 - D - E * ((n : ℝ) + 1) * K - K) * T
        = ((s : ℝ) - 2) * T - D * T - E * ((n : ℝ) + 1) * (K * T) - K * T := by ring
    have hexp2 : (E : ℝ) * (((n : ℝ) + 1) * (K * T + Cj))
        = E * ((n : ℝ) + 1) * (K * T) + E * ((n : ℝ) + 1) * Cj := by ring
    rw [hexp1] at hcoef
    rw [hexp2] at hkey
    linarith
  obtain ⟨k, hk⟩ := (hev.and (hTtop.eventually_gt_atTop
    (4 * (E * ((n : ℝ) + 1) * Cj + Cj + CN + Cg + C₀ + Csmt)))).exists
  exact absurd hk.1 (not_le.mpr hk.2)

end

end GaloisForLFunctions.HTGeometry
