import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.DeBruijnShiftContraction

/-!
# Partial fractions and local zero counts for even functions of order one

Let `f` be entire and even, with `f(0) ≠ 0` and the order-one envelope
`‖f z‖ ≤ exp(C(1+‖z‖)log(2+‖z‖))`, and write `a_q` for its zeros counted with multiplicity.

* `logDeriv_eq_tsum_of_even`: off the zeros,
  `f'/f(z) = Σ_q −z/(a_q(a_q − z)) = Σ_q (1/(z − a_q) + 1/a_q)`, from the Hadamard product
  `f = f(0)·∏ E₁(z/a_q)`.
* `two_logDeriv_eq_pair_tsum_of_even`: reflection `a ↦ −a` symmetrises it to
  `2 f'/f(z) = Σ_q (1/(z − a_q) + 1/(z + a_q))`.
* `card_le_of_even_strip`: if every zero has `|Im a| ≤ ½`, then at `z₀ = x₀ − iY` with
  `1 ≤ Y ≤ 2`, every term has nonnegative imaginary part. A zero with `|Re a − x₀| ≤ 1` contributes
  at least `2/29`. So the zeros within unit horizontal distance of `x₀` number at most
  `29 ‖f'/f(z₀)‖`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

variable {f : ℂ → ℂ}

theorem summable_neg_div_zeroCopyPoint {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) (z : ℂ) :
    Summable (fun q : ZeroCopy f => -z / (zeroCopyPoint f q * (zeroCopyPoint f q - z))) := by
  set a := zeroCopyPoint f
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  set S : ℝ := 2 * ‖z‖ + 1
  have hS : 0 < S := by positivity
  have hbase : Summable (fun q : ZeroCopy f => 1 / ‖a q‖ ^ (2 : ℕ)) :=
    OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hev : ∀ᶠ q in cofinite, S ≤ ‖a q‖ := by
    have htend := hbase.tendsto_cofinite_zero
    have hlt : ∀ᶠ q in cofinite, 1 / ‖a q‖ ^ (2 : ℕ) < 1 / S ^ (2 : ℕ) :=
      htend.eventually_lt_const (by positivity)
    filter_upwards [hlt] with q hq
    have haq : 0 < ‖a q‖ := norm_pos_iff.mpr (hane q)
    have hsq : S ^ (2 : ℕ) < ‖a q‖ ^ (2 : ℕ) :=
      lt_of_one_div_lt_one_div (pow_pos haq 2) hq
    exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq)
  refine (hbase.mul_left (2 * ‖z‖)).of_norm_bounded_eventually ?_
  filter_upwards [hev] with q hq
  have haz : ‖z‖ ≤ ‖a q‖ / 2 := by linarith
  have hdiff : ‖a q‖ / 2 ≤ ‖a q - z‖ := by
    have hrev := norm_sub_norm_le (a q) z
    linarith
  have ha0 : 0 < ‖a q‖ := norm_pos_iff.mpr (hane q)
  have hd0 : 0 < ‖a q - z‖ := lt_of_lt_of_le (half_pos ha0) hdiff
  rw [norm_div, norm_neg, norm_mul]
  have hden : ‖a q‖ ^ (2 : ℕ) / 2 ≤ ‖a q‖ * ‖a q - z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hdiff (norm_nonneg (a q))]
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    rw [div_le_iff₀ (mul_pos ha0 hd0)]
    field_simp
    nlinarith

/-- **Partial fraction of an even function of order one.** -/
theorem logDeriv_eq_tsum_of_even {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : f z ≠ 0) :
    logDeriv f z = ∑' q : ZeroCopy f, -z / (zeroCopyPoint f q * (zeroCopyPoint f q - z)) := by
  set a := zeroCopyPoint f with hadef
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  have hford := DeBruijn.analyticOrderAt_ne_top_of_ne_zero hf hf0
  have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
  have hsum2 := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hza : ∀ q, z ≠ a q := fun q h => hz (h ▸ DeBruijn.apply_zeroCopyPoint hf q)
  have hfacne : ∀ q, weierstrassE1 (z / a q) ≠ 0 := by
    intro q
    rw [weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have hdiv : z / a q = 1 := (sub_eq_zero.mp hzero).symm
      apply hza q
      calc z = z / a q * a q := (div_mul_cancel₀ z (hane q)).symm
        _ = 1 * a q := by rw [hdiv]
        _ = a q := one_mul _
    · exact Complex.exp_ne_zero _
  have hsum : Summable (fun q : ZeroCopy f => logDeriv (fun w : ℂ => weierstrassE1 (w / a q)) z) :=
    (summable_neg_div_zeroCopyPoint hC hf hf0 hbound z).congr fun q =>
      (logDeriv_weierstrassE1_div (hane q) (hza q)).symm
  have hH : OrderOneHadamard.hadamardProduct f z ≠ 0 := by
    intro h0
    apply hz
    rw [hfac z, h0, mul_zero]
  have hlog := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) hfacne (by
      intro q
      simp only [weierstrassE1]
      fun_prop) hsum
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn a hane hsum2).multipliableLocallyUniformlyOn
    hH
  have hfeq : f = fun w => f 0 * OrderOneHadamard.hadamardProduct f w := funext hfac
  calc logDeriv f z = logDeriv (OrderOneHadamard.hadamardProduct f) z := by
        rw [show logDeriv f z = logDeriv (fun w => f 0 * OrderOneHadamard.hadamardProduct f w) z
          from congrArg (fun g => logDeriv g z) hfeq, logDeriv_const_mul z _ hf0]
    _ = ∑' q : ZeroCopy f, logDeriv (fun w : ℂ => weierstrassE1 (w / a q)) z := by
        simpa only [OrderOneHadamard.hadamardProduct, canonicalProductE1Indexed] using! hlog
    _ = _ := tsum_congr fun q => logDeriv_weierstrassE1_div (hane q) (hza q)

/-- **Symmetrised partial fraction.** -/
theorem two_logDeriv_eq_pair_tsum_of_even {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : f z ≠ 0) :
    Summable (fun q : ZeroCopy f => (z - zeroCopyPoint f q)⁻¹ + (z + zeroCopyPoint f q)⁻¹) ∧
    2 * logDeriv f z =
      ∑' q : ZeroCopy f, ((z - zeroCopyPoint f q)⁻¹ + (z + zeroCopyPoint f q)⁻¹) := by
  set a := zeroCopyPoint f with hadef
  set σ := OrderOneHadamard.zeroCopyReflect hf heven
  have hσa : ∀ q, a (σ q) = -a q := OrderOneHadamard.zeroCopyPoint_reflect hf heven
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  have hza : ∀ q, z ≠ a q := fun q h => hz (h ▸ DeBruijn.apply_zeroCopyPoint hf q)
  set φ : ZeroCopy f → ℂ := fun q => -z / (a q * (a q - z)) with hφ
  have hφs : Summable φ := summable_neg_div_zeroCopyPoint hC hf hf0 hbound z
  have hφσ : Summable (fun q => φ (σ q)) := σ.summable_iff.mpr hφs
  have hpt : ∀ q, φ q + φ (σ q) = (z - a q)⁻¹ + (z + a q)⁻¹ := by
    intro q
    simp only [hφ, hσa]
    have h1 : a q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hza q))
    have h2 : z + a q ≠ 0 := by
      intro h
      apply hza (σ q)
      rw [hσa]
      linear_combination h
    have h3 : z - a q ≠ 0 := sub_ne_zero.mpr (hza q)
    have h4 : -a q - z ≠ 0 := by
      intro h; apply h2; linear_combination -h
    field_simp [hane q]
    ring
  have hsumpair : Summable (fun q => (z - a q)⁻¹ + (z + a q)⁻¹) :=
    (hφs.add hφσ).congr hpt
  refine ⟨hsumpair, ?_⟩
  rw [logDeriv_eq_tsum_of_even hC hf hf0 heven hbound hz, two_mul]
  calc ∑' q, φ q + ∑' q, φ q = ∑' q, φ q + ∑' q, φ (σ q) := by rw [σ.tsum_eq φ]
    _ = ∑' q, (φ q + φ (σ q)) := (hφs.tsum_add hφσ).symm
    _ = _ := tsum_congr hpt

/-- **Local zero count.** If every zero of `f` has `|Im a| ≤ ½`, then for `1 ≤ Y ≤ 2` the zeros
within unit horizontal distance of `x₀` number at most `29 ‖f'/f(x₀ − iY)‖`. -/
theorem card_le_of_even_strip {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hstrip0 : ∀ w, f w = 0 → |w.im| ≤ 1 / 2) {x₀ Y : ℝ} (hY1 : 1 ≤ Y)
    (hY2 : Y ≤ 2) (F : Finset (ZeroCopy f)) (hF : ∀ q ∈ F, |(zeroCopyPoint f q).re - x₀| ≤ 1) :
    (F.card : ℝ) ≤ 29 * ‖logDeriv f ((x₀ : ℂ) - (Y : ℂ) * I)‖ := by
  set z₀ : ℂ := (x₀ : ℂ) - (Y : ℂ) * I with hz₀
  set a := zeroCopyPoint f with hadef
  have hz₀re : z₀.re = x₀ := by simp [hz₀]
  have hz₀im : z₀.im = -Y := by simp [hz₀]
  have hz : f z₀ ≠ 0 := by
    intro h0
    have h1 := hstrip0 z₀ h0
    rw [hz₀im, abs_neg, abs_of_pos (by linarith)] at h1
    linarith
  have hstrip : ∀ q, |(a q).im| ≤ 1 / 2 := fun q => hstrip0 _ (DeBruijn.apply_zeroCopyPoint hf q)
  obtain ⟨hsum, hpair⟩ := two_logDeriv_eq_pair_tsum_of_even hC hf hf0 heven hbound hz
  set ψ : ZeroCopy f → ℂ := fun q => (z₀ - a q)⁻¹ + (z₀ + a q)⁻¹ with hψ
  -- every term has nonnegative imaginary part
  have hψim : ∀ q, (ψ q).im = -(-Y - (a q).im) / Complex.normSq (z₀ - a q) +
      -(-Y + (a q).im) / Complex.normSq (z₀ + a q) := by
    intro q
    show ((z₀ - a q)⁻¹ + (z₀ + a q)⁻¹).im = _
    rw [Complex.add_im, Complex.inv_im, Complex.inv_im, Complex.sub_im, Complex.add_im, hz₀im]
  have hnonneg : ∀ q, 0 ≤ (ψ q).im := by
    intro q
    have hs := hstrip q
    rw [abs_le] at hs
    rw [hψim]
    have t1 : 0 ≤ -(-Y - (a q).im) / Complex.normSq (z₀ - a q) :=
      div_nonneg (by linarith) (Complex.normSq_nonneg _)
    have t2 : 0 ≤ -(-Y + (a q).im) / Complex.normSq (z₀ + a q) :=
      div_nonneg (by linarith) (Complex.normSq_nonneg _)
    linarith
  -- near zeros contribute at least `2/29`
  have hnear : ∀ q ∈ F, (2 : ℝ) / 29 ≤ (ψ q).im := by
    intro q hq
    have hs := hstrip q
    rw [abs_le] at hs
    have hr := hF q hq
    rw [abs_le] at hr
    have hn1 : Complex.normSq (z₀ - a q) = (x₀ - (a q).re) ^ 2 + (-Y - (a q).im) ^ 2 := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hz₀re, hz₀im]; ring
    rw [hψim]
    have hpos1 : 0 < Complex.normSq (z₀ - a q) := by
      rw [hn1]; nlinarith [sq_nonneg (x₀ - (a q).re)]
    have hle1 : Complex.normSq (z₀ - a q) ≤ 29 / 4 := by
      rw [hn1]; nlinarith
    have t1 : (2 : ℝ) / 29 ≤ -(-Y - (a q).im) / Complex.normSq (z₀ - a q) := by
      rw [le_div_iff₀ hpos1]; nlinarith
    have t2 : 0 ≤ -(-Y + (a q).im) / Complex.normSq (z₀ + a q) :=
      div_nonneg (by linarith) (Complex.normSq_nonneg _)
    linarith
  have hsumim : Summable (fun q => (ψ q).im) := (Complex.imCLM.summable hsum)
  have hlow : ∑ q ∈ F, (ψ q).im ≤ ∑' q, (ψ q).im :=
    hsumim.sum_le_tsum F (fun q _ => hnonneg q)
  have him : (∑' q, ψ q).im = ∑' q, (ψ q).im := Complex.im_tsum hsum
  have hcard : (F.card : ℝ) * (2 / 29) ≤ ∑ q ∈ F, (ψ q).im := by
    have := Finset.sum_le_sum hnear
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have h2 : (2 * logDeriv f z₀).im ≤ ‖2 * logDeriv f z₀‖ := Complex.im_le_norm _
  rw [norm_mul, Complex.norm_two] at h2
  rw [hpair, him] at h2
  have : (F.card : ℝ) * (2 / 29) ≤ 2 * ‖logDeriv f z₀‖ := by linarith
  linarith

end

end RHTower
