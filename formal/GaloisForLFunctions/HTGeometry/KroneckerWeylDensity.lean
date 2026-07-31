import GaloisForLFunctions.HTGeometry.BohrParseval

/-!
# Kronecker's approximation theorem for a rationally independent frequency family

If `λ₁, …, λ_m` are linearly independent over `ℚ`, the line `t ↦ (e^{iλ₁t}, …, e^{iλ_mt})` comes
arbitrarily close to every point of the `m`-torus.  Mathlib has neither Kronecker's theorem nor Weyl
equidistribution; this file proves the approximation form from the Bohr mean value.

The mechanism is a positive kernel.  For `K : ℕ` the function `((1+cos x)/2)^K` is a nonnegative
trigonometric polynomial of degree `K`, equal to `(1+z)^{2K}/(4^K z^K)` for `z = e^{ix}`, so its
Fourier coefficients are the binomial coefficients `binom(2K,r)/4^K`.  Its mean along the line picks
out the constant coefficient, and rational independence makes the constant coefficient the *only*
surviving term of the `m`-fold product: the mean of `∏_j ((1+cos(λ_j t − θ_j))/2)^K` is exactly
`(binom(2K,K)/4^K)^m ≥ (2K+1)^{-m}`.  If the line avoided the `ε`-ball around `θ`, the same product
would be bounded by `(1 − ε²/4)^K` at every time, and an exponentially small bound cannot dominate a
polynomially small one.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- The character `t ↦ e^{iμt}`. -/
noncomputable def expChar (mu : ℝ) (t : ℝ) : ℂ := Complex.exp ((mu * t : ℝ) * Complex.I)

theorem expChar_eq_bohrChar (mu t : ℝ) : expChar mu t = bohrChar (-mu) t := by
  simp only [expChar, bohrChar]
  congr 2
  push_cast
  ring

theorem continuous_expChar (mu : ℝ) : Continuous (expChar mu) := by
  unfold expChar
  fun_prop

theorem isBohrAlmostPeriodic_expChar (mu : ℝ) :
    HTGeometry.IsBohrAlmostPeriodic (expChar mu) := by
  have h : expChar mu = bohrChar (-mu) := funext fun t => expChar_eq_bohrChar mu t
  rw [h]
  exact isBohrAlmostPeriodic_bohrChar _

@[simp] theorem norm_expChar (mu t : ℝ) : ‖expChar mu t‖ = 1 := by
  rw [expChar_eq_bohrChar]
  exact norm_bohrChar _ _

theorem expChar_add (a b t : ℝ) : expChar a t * expChar b t = expChar (a + b) t := by
  simp only [expChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The mean of a nontrivial character vanishes. -/
theorem bohrMean_expChar (mu : ℝ) : bohrMean (expChar mu) = if mu = 0 then 1 else 0 := by
  have h : expChar mu = bohrChar (-mu) := funext fun t => expChar_eq_bohrChar mu t
  rw [h, bohrMean_bohrChar]
  by_cases hmu : mu = 0
  · rw [if_pos (by rw [hmu]; ring), if_pos hmu]
  · rw [if_neg (fun hz => hmu (by linarith [neg_eq_zero.mp hz])), if_neg hmu]

/-- The mean of a finite linear combination of characters is the sum of the coefficients at the
zero frequency. -/
theorem bohrMean_sum_expChar {ι : Type*} (s : Finset ι) (c : ι → ℂ) (mu : ι → ℝ) :
    bohrMean (fun t => ∑ i ∈ s, c i * expChar (mu i) t)
      = ∑ i ∈ s, if mu i = 0 then c i else 0 := by
  rw [bohrMean_sum (F := fun i => fun t => c i * expChar (mu i) t) s
    (fun i _ => continuous_const.mul (continuous_expChar (mu i)))
    (fun i _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar (mu i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bohrMean_const_mul (f := expChar (mu i)) _ (continuous_expChar (mu i))
    (isBohrAlmostPeriodic_expChar (mu i)), bohrMean_expChar]
  by_cases h : mu i = 0 <;> simp [h]

/-! ### The positive kernel -/

/-- The Fejér-type positive kernel `((1 + cos x)/2)^K`. -/
noncomputable def cosKernel (K : ℕ) (x : ℝ) : ℝ := ((1 + Real.cos x) / 2) ^ K

theorem cosKernel_base_nonneg (x : ℝ) : 0 ≤ (1 + Real.cos x) / 2 := by
  have := Real.neg_one_le_cos x
  linarith

theorem cosKernel_base_le_one (x : ℝ) : (1 + Real.cos x) / 2 ≤ 1 := by
  have := Real.cos_le_one x
  linarith

theorem cosKernel_nonneg (K : ℕ) (x : ℝ) : 0 ≤ cosKernel K x :=
  pow_nonneg (cosKernel_base_nonneg x) K

theorem cosKernel_le_one (K : ℕ) (x : ℝ) : cosKernel K x ≤ 1 := by
  have h := pow_le_pow_left₀ (cosKernel_base_nonneg x) (cosKernel_base_le_one x) K
  rw [one_pow] at h
  exact h

theorem cosKernel_le_pow {K : ℕ} {q x : ℝ} (h : (1 + Real.cos x) / 2 ≤ q) :
    cosKernel K x ≤ q ^ K :=
  pow_le_pow_left₀ (cosKernel_base_nonneg x) h K

/-- The kernel as a trigonometric polynomial: its Fourier coefficients are the binomial
coefficients `binom(2K,r)/4^K`. -/
theorem ofReal_cosKernel_eq_sum (K : ℕ) (x : ℝ) :
    ((cosKernel K x : ℝ) : ℂ)
      = ∑ r ∈ Finset.range (2 * K + 1),
          ((Nat.choose (2 * K) r : ℂ) / 4 ^ K) * expChar ((r : ℝ) - (K : ℝ)) x := by
  have hz : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  set z : ℂ := Complex.exp ((x : ℂ) * Complex.I) with hzdef
  have hexp : ∀ n : ℕ, Complex.exp (((n * x : ℝ) : ℂ) * Complex.I) = z ^ n := by
    intro n
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcosz : z + z⁻¹ = 2 * ((Real.cos x : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos, hzdef]
    have hinv : (Complex.exp ((x : ℂ) * Complex.I))⁻¹
        = Complex.exp (-(x : ℂ) * Complex.I) := by
      rw [← Complex.exp_neg]
      congr 1
      ring
    rw [hinv]
    ring
  have hbase : (((1 + Real.cos x) / 2 : ℝ) : ℂ) = (1 + z) ^ 2 / (4 * z) := by
    have h : (1 + z) ^ 2 / (4 * z) = (z + z⁻¹ + 2) / 4 := by
      field_simp
      ring
    rw [h, hcosz]
    push_cast
    ring
  have hpow : ((cosKernel K x : ℝ) : ℂ) = (1 + z) ^ (2 * K) / (4 ^ K * z ^ K) := by
    rw [cosKernel, Complex.ofReal_pow, hbase, div_pow, mul_pow, pow_mul]
  have hbinom : (1 + z) ^ (2 * K)
      = ∑ r ∈ Finset.range (2 * K + 1), z ^ r * (Nat.choose (2 * K) r : ℂ) := by
    rw [add_comm (1 : ℂ) z, add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one]
  rw [hpow, hbinom, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hkey : expChar ((r : ℝ) - (K : ℝ)) x = z ^ r / z ^ K := by
    rw [expChar, ← hexp r, ← hexp K, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [hkey]
  field_simp

/-- A finite product of characters is the character of the summed frequency. -/
theorem prod_expChar {ι : Type*} (s : Finset ι) (a : ι → ℝ) (t : ℝ) :
    ∏ i ∈ s, expChar (a i) t = expChar (∑ i ∈ s, a i) t := by
  classical
  induction s using Finset.induction with
  | empty => simp [expChar]
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, expChar_add]

/-- The `m`-fold kernel product along the line, expanded as a finite combination of characters. -/
theorem ofReal_prod_cosKernel_eq_sum {m : ℕ} (lam θ : Fin m → ℝ) (K : ℕ) (t : ℝ) :
    ((∏ j : Fin m, cosKernel K (lam j * t - θ j) : ℝ) : ℂ)
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (2 * K + 1)),
          (∏ j : Fin m, ((Nat.choose (2 * K) (v j) : ℂ) / 4 ^ K) *
              Complex.exp ((-(((v j : ℝ) - K) * θ j) : ℝ) * Complex.I))
            * expChar (∑ j : Fin m, ((v j : ℝ) - K) * lam j) t := by
  classical
  have hstep : ∀ j : Fin m,
      ((cosKernel K (lam j * t - θ j) : ℝ) : ℂ)
        = ∑ r ∈ Finset.range (2 * K + 1),
            (((Nat.choose (2 * K) r : ℂ) / 4 ^ K)
                * Complex.exp ((-(((r : ℝ) - K) * θ j) : ℝ) * Complex.I))
              * expChar (((r : ℝ) - K) * lam j) t := by
    intro j
    rw [ofReal_cosKernel_eq_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hfac : expChar ((r : ℝ) - K) (lam j * t - θ j)
        = Complex.exp ((-(((r : ℝ) - K) * θ j) : ℝ) * Complex.I)
          * expChar (((r : ℝ) - K) * lam j) t := by
      simp only [expChar, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfac]
    ring
  rw [Complex.ofReal_prod, Finset.prod_congr rfl (fun j _ => hstep j), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.prod_mul_distrib, prod_expChar]

/-- **The mean of the kernel product is its constant coefficient.**  Rational independence makes the
zero frequency occur only at the central multi-index. -/
theorem bohrMean_prod_cosKernel {m : ℕ} {lam : Fin m → ℝ} (hind : LinearIndependent ℚ lam)
    (θ : Fin m → ℝ) (K : ℕ) :
    bohrMean (fun t => ((∏ j : Fin m, cosKernel K (lam j * t - θ j) : ℝ) : ℂ))
      = ((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m := by
  classical
  set Box : Finset (Fin m → ℕ) :=
    Fintype.piFinset (fun _ : Fin m => Finset.range (2 * K + 1)) with hBox
  set C : (Fin m → ℕ) → ℂ := fun v =>
    ∏ j : Fin m, ((Nat.choose (2 * K) (v j) : ℂ) / 4 ^ K) *
      Complex.exp ((-(((v j : ℝ) - K) * θ j) : ℝ) * Complex.I) with hC
  set mu : (Fin m → ℕ) → ℝ := fun v => ∑ j : Fin m, ((v j : ℝ) - K) * lam j with hmu
  have hfun : (fun t : ℝ => ((∏ j : Fin m, cosKernel K (lam j * t - θ j) : ℝ) : ℂ))
      = fun t => ∑ v ∈ Box, C v * expChar (mu v) t :=
    funext fun t => ofReal_prod_cosKernel_eq_sum lam θ K t
  have hcentral : (fun _ : Fin m => K) ∈ Box := by
    rw [hBox, Fintype.mem_piFinset]
    intro j
    exact Finset.mem_range.mpr (by omega)
  have hmuzero : mu (fun _ : Fin m => K) = 0 := by
    rw [hmu]
    simp
  have hCcentral : C (fun _ : Fin m => K) = ((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m := by
    simp [hC, div_pow]
  have hindep : ∀ v : Fin m → ℕ, v ∈ Box → mu v = 0 → v = fun _ : Fin m => K := by
    intro v _ hv
    funext j
    have hq : ∑ i : Fin m, ((v i : ℚ) - (K : ℚ)) • lam i = 0 := by
      have hcast : ∀ i : Fin m, ((v i : ℚ) - (K : ℚ)) • lam i = ((v i : ℝ) - K) * lam i := by
        intro i
        rw [Rat.smul_def]
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun i _ => hcast i)]
      rw [hmu] at hv
      exact hv
    have hzero := (Fintype.linearIndependent_iff.mp hind) (fun i => (v i : ℚ) - (K : ℚ)) hq j
    have hvj : (v j : ℚ) = (K : ℚ) := sub_eq_zero.mp hzero
    exact_mod_cast hvj
  rw [hfun, bohrMean_sum_expChar Box C mu]
  rw [Finset.sum_eq_single_of_mem (fun _ : Fin m => K) hcentral]
  · rw [if_pos hmuzero, hCcentral]
  · intro v hv hne
    rw [if_neg]
    intro hv0
    exact hne (hindep v hv hv0)

/-- The central binomial coefficient dominates `4^K/(2K+1)`. -/
theorem four_pow_le_succ_mul_centralBinom (K : ℕ) :
    4 ^ K ≤ (2 * K + 1) * Nat.choose (2 * K) K := by
  have hsum : ∑ r ∈ Finset.range (2 * K + 1), Nat.choose (2 * K) r = 2 ^ (2 * K) :=
    Nat.sum_range_choose (2 * K)
  have hle : ∑ r ∈ Finset.range (2 * K + 1), Nat.choose (2 * K) r
      ≤ ∑ _r ∈ Finset.range (2 * K + 1), Nat.choose (2 * K) K := by
    refine Finset.sum_le_sum fun r _ => ?_
    have h := Nat.choose_le_middle r (2 * K)
    rwa [Nat.mul_div_cancel_left K (by norm_num : 0 < 2)] at h
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
  rw [show (4 : ℕ) ^ K = 2 ^ (2 * K) by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
    mul_comm], ← hsum]
  exact hle

/-! ### Kronecker's approximation theorem -/

/-- The distance between two unit characters in terms of the cosine of the phase gap. -/
theorem norm_expChar_sub_sq (a b : ℝ) :
    ‖Complex.exp ((a : ℝ) * Complex.I) - Complex.exp ((b : ℝ) * Complex.I)‖ ^ 2
      = 2 - 2 * Real.cos (a - b) := by
  have hfac : Complex.exp ((a : ℝ) * Complex.I) - Complex.exp ((b : ℝ) * Complex.I)
      = Complex.exp ((b : ℝ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℝ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [Complex.exp_mul_I]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  have hpyth := Real.sin_sq_add_cos_sq (a - b)
  ring_nf
  nlinarith [hpyth]

/-- **Kronecker's approximation theorem.**  A rationally independent frequency family makes the
line `t ↦ (e^{iλ_j t})_j` come arbitrarily close to every point of the torus. -/
theorem kronecker_approx {m : ℕ} {lam : Fin m → ℝ} (hind : LinearIndependent ℚ lam)
    (θ : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ∀ j : Fin m,
      ‖expChar (lam j) t - Complex.exp ((θ j : ℝ) * Complex.I)‖ < ε := by
  classical
  by_contra hcon
  push Not at hcon
  set q : ℝ := max 0 (1 - ε ^ 2 / 4) with hqdef
  have hq0 : 0 ≤ q := le_max_left _ _
  have hq1 : q < 1 := by
    refine max_lt one_pos ?_
    nlinarith
  -- the pointwise bound along the line
  have hpoint : ∀ (K : ℕ) (t : ℝ),
      ∏ j : Fin m, cosKernel K (lam j * t - θ j) ≤ q ^ K := by
    intro K t
    obtain ⟨j₀, hj₀⟩ := hcon t
    have hcos : (1 + Real.cos (lam j₀ * t - θ j₀)) / 2 ≤ q := by
      have hsq := norm_expChar_sub_sq (lam j₀ * t) (θ j₀)
      have hge : ε ^ 2 ≤ ‖expChar (lam j₀) t - Complex.exp ((θ j₀ : ℝ) * Complex.I)‖ ^ 2 := by
        have hnn : (0 : ℝ) ≤ ‖expChar (lam j₀) t - Complex.exp ((θ j₀ : ℝ) * Complex.I)‖ :=
          norm_nonneg _
        nlinarith [hj₀]
      have hexpeq : expChar (lam j₀) t = Complex.exp (((lam j₀ * t : ℝ) : ℝ) * Complex.I) := rfl
      rw [hexpeq, hsq] at hge
      have : Real.cos (lam j₀ * t - θ j₀) ≤ 1 - ε ^ 2 / 2 := by linarith
      have hle : (1 + Real.cos (lam j₀ * t - θ j₀)) / 2 ≤ 1 - ε ^ 2 / 4 := by linarith
      exact hle.trans (le_max_right _ _)
    have hbad : cosKernel K (lam j₀ * t - θ j₀) ≤ q ^ K := cosKernel_le_pow hcos
    calc ∏ j : Fin m, cosKernel K (lam j * t - θ j)
        ≤ ∏ j : Fin m, (if j = j₀ then q ^ K else 1) := by
          refine Finset.prod_le_prod (fun j _ => cosKernel_nonneg K _) (fun j _ => ?_)
          by_cases hj : j = j₀
          · subst hj; simpa using hbad
          · simpa [hj] using cosKernel_le_one K (lam j * t - θ j)
      _ = q ^ K := by simp
  -- the mean of the kernel product is dominated by the pointwise bound
  have hmeanbound : ∀ K : ℕ, ‖((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m‖ ≤ q ^ K := by
    intro K
    set g : ℝ → ℂ := fun t => ((∏ j : Fin m, cosKernel K (lam j * t - θ j) : ℝ) : ℂ) with hg
    have hgsum : g = fun t => ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (2 * K + 1)),
        (∏ j : Fin m, ((Nat.choose (2 * K) (v j) : ℂ) / 4 ^ K) *
            Complex.exp ((-(((v j : ℝ) - K) * θ j) : ℝ) * Complex.I))
          * expChar (∑ j : Fin m, ((v j : ℝ) - K) * lam j) t :=
      funext fun t => ofReal_prod_cosKernel_eq_sum lam θ K t
    have hgc : Continuous g := by
      rw [hgsum]
      exact continuous_finsetSum _ fun v _ => continuous_const.mul (continuous_expChar _)
    have hga : HTGeometry.IsBohrAlmostPeriodic g := by
      rw [hgsum]
      exact isBohrAlmostPeriodic_sum _ (fun v _ => continuous_const.mul (continuous_expChar _))
        (fun v _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
    have hnorm : Tendsto (fun T => ‖windowAverage g T‖) atTop (nhds ‖bohrMean g‖) :=
      (continuous_norm.tendsto _).comp (tendsto_windowAverage_bohrMean hgc hga)
    have hbd : ‖bohrMean g‖ ≤ q ^ K := by
      refine le_of_tendsto hnorm ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖g x‖ ≤ q ^ K := by
        intro x _
        rw [hg]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Finset.prod_nonneg fun j _ => cosKernel_nonneg K _)]
        exact hpoint K x
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      simp only [windowAverage, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hT.le)]
      calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, g t‖ ≤ T⁻¹ * (q ^ K * |T - 0|) :=
            mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
        _ = q ^ K := by
            rw [sub_zero, abs_of_nonneg hT.le]
            field_simp
    have hbd' := hbd
    rw [hg] at hbd'
    rw [← bohrMean_prod_cosKernel hind θ K]
    exact hbd'
  -- the central binomial lower bound
  have hlower : ∀ K : ℕ, (1 : ℝ) / (2 * (K : ℝ) + 1) ≤ (Nat.choose (2 * K) K : ℝ) / 4 ^ K := by
    intro K
    have hR : (4 : ℝ) ^ K ≤ (2 * (K : ℝ) + 1) * (Nat.choose (2 * K) K : ℝ) := by
      exact_mod_cast four_pow_le_succ_mul_centralBinom K
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hfinal : ∀ K : ℕ, (1 : ℝ) ≤ (2 * (K : ℝ) + 1) ^ m * q ^ K := by
    intro K
    have h1 := hmeanbound K
    have hnormeq : ‖((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m‖
        = ((Nat.choose (2 * K) K : ℝ) / 4 ^ K) ^ m := by
      rw [norm_pow]
      congr 1
      rw [norm_div]
      norm_num
    rw [hnormeq] at h1
    have h2 : ((1 : ℝ) / (2 * (K : ℝ) + 1)) ^ m ≤ ((Nat.choose (2 * K) K : ℝ) / 4 ^ K) ^ m :=
      pow_le_pow_left₀ (by positivity) (hlower K) m
    have h3 : ((1 : ℝ) / (2 * (K : ℝ) + 1)) ^ m ≤ q ^ K := le_trans h2 h1
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)] at h3
    linarith
  -- exponential decay beats the polynomial bound
  have hdecay : Tendsto (fun K : ℕ => (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K)) atTop (nhds 0) := by
    have habs : |q| < 1 := by rwa [abs_of_nonneg hq0]
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one m habs
    simpa using h.const_mul ((3 : ℝ) ^ m)
  have hev := Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1) hdecay
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  set K : ℕ := max K0 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hsmall : (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) < 1 := hK0 K (le_max_left _ _)
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hcmp : (2 * (K : ℝ) + 1) ^ m * q ^ K ≤ (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) := by
    have hbase : 2 * (K : ℝ) + 1 ≤ 3 * (K : ℝ) := by linarith
    have hp : (2 * (K : ℝ) + 1) ^ m ≤ (3 * (K : ℝ)) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    calc (2 * (K : ℝ) + 1) ^ m * q ^ K ≤ (3 * (K : ℝ)) ^ m * q ^ K :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) := by rw [mul_pow]; ring
  linarith [hfinal K]

end

end GaloisForLFunctions
