import GaloisForLFunctions.HTGeometry.GammaFactorialHarmonicResidue

/-!
# The moving harmonic residue beyond the reciprocal Gamma boundary

The leading Gamma factorial microscope has reciprocal first jet, so its Riccati defect vanishes at
leading order.  This module resolves the next scale.  It proves, for every nonzero microscope point
`x`,

`(gₙ'(x) - gₙ(x)²) / (sₙ Hₙ) → -2 / x`,

where `gₙ(x) = Gamma(-n + sₙ x)` and `sₙ = (-1)^(n+1) / n!`.

The proof separates two exact sources.  The finite backward Gamma product contributes the harmonic
sum, while the analytic tangent factor is negligible at harmonic scale.  A shifted-resolvent bound
then shows that the scaled digamma correction tends to one.  Combining the reciprocal-Gamma and
digamma corrections gives a nonzero direction transverse to the complete first-jet Riccati kernel.
No numerical approximation or full-project build is involved.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

open scoped BigOperators

theorem harmonic_cast_real_le_natSucc (n : ℕ) :
    (harmonic n : ℝ) ≤ n + 1 := by
  have hlog : Real.log (n : ℝ) ≤ n := Real.log_le_self (Nat.cast_nonneg n)
  have hH := harmonic_le_one_add_log n
  linarith

theorem tendsto_gammaHarmonicMicroscopeScale_zero :
    Tendsto gammaHarmonicMicroscopeScale atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor := (tendsto_factorialScale_pow_mul_natSuccPow_zero 1 1 (by omega)).norm
  simp only [pow_one, norm_zero] at hmajor
  apply squeeze_zero' (Filter.Eventually.of_forall fun n =>
    norm_nonneg (gammaHarmonicMicroscopeScale n)) _ hmajor
  filter_upwards with n
  rw [gammaHarmonicMicroscopeScale, norm_mul,
    norm_reciprocalGammaFactorialScale]
  have hH := harmonic_cast_real_le_natSucc n
  have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
    rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact_mod_cast (show (0 : ℚ) ≤ harmonic n by
      rw [harmonic]
      positivity)
  rw [hnormH]
  rw [norm_mul, norm_reciprocalGammaFactorialScale, Complex.norm_natCast]
  push_cast at hH ⊢
  gcongr

theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + u i)) - 1 - ∑ i ∈ s, u i‖ ≤
      (∑ i ∈ s, ‖u i‖) * (Real.exp (∑ i ∈ s, ‖u i‖) - 1) := by
  have hordered :
      (∏ i ∈ s, (1 + u i)) =
        1 + ∑ i ∈ s, u i * ∏ j ∈ s with j < i, (1 + u j) := by
    rw [Finset.prod_add_ordered s (fun _ => 1) u]
    simp
  rw [hordered]
  have heq :
      (1 + ∑ i ∈ s, u i * ∏ j ∈ s with j < i, (1 + u j)) - 1 - ∑ i ∈ s, u i =
        ∑ i ∈ s, u i * ((∏ j ∈ s with j < i, (1 + u j)) - 1) := by
    rw [show (1 + ∑ i ∈ s, u i * ∏ j ∈ s with j < i, (1 + u j)) - 1 =
      ∑ i ∈ s, u i * ∏ j ∈ s with j < i, (1 + u j) by ring]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    ‖∑ i ∈ s, u i * ((∏ j ∈ s with j < i, (1 + u j)) - 1)‖
        ≤ ∑ i ∈ s, ‖u i * ((∏ j ∈ s with j < i, (1 + u j)) - 1)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖u i‖ * (Real.exp (∑ j ∈ s, ‖u j‖) - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      gcongr
      calc
        ‖(∏ j ∈ s with j < i, (1 + u j)) - 1‖
            ≤ Real.exp (∑ j ∈ s with j < i, ‖u j‖) - 1 := by
              simpa using Finset.norm_prod_one_add_sub_one_le
                (s.filter fun j => j < i) u
        _ ≤ Real.exp (∑ j ∈ s, ‖u j‖) - 1 := by
          gcongr
          exact Finset.filter_subset _ _
    _ = (∑ i ∈ s, ‖u i‖) * (Real.exp (∑ i ∈ s, ‖u i‖) - 1) := by
      rw [Finset.sum_mul]

def reciprocalGammaProductTerm (n : ℕ) (x : ℂ) (j : ℕ) : ℂ :=
  -(reciprocalGammaFactorialScale n * x / ((j + 1 : ℕ) : ℂ))

theorem sum_reciprocalGammaProductTerm (n : ℕ) (x : ℂ) :
    ∑ j ∈ Finset.range n, reciprocalGammaProductTerm n x j =
      -(gammaHarmonicMicroscopeScale n * x) := by
  rw [gammaHarmonicMicroscopeScale, HilbertSchmidt.harmonic_cast_complex]
  calc
    ∑ j ∈ Finset.range n, reciprocalGammaProductTerm n x j =
        ∑ j ∈ Finset.range n,
          -(reciprocalGammaFactorialScale n * ((j : ℂ) + 1)⁻¹ * x) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [reciprocalGammaProductTerm]
            push_cast
            ring
    _ = -(∑ j ∈ Finset.range n,
          reciprocalGammaFactorialScale n * ((j : ℂ) + 1)⁻¹ * x) := by
            rw [Finset.sum_neg_distrib]
    _ = -((∑ j ∈ Finset.range n,
          reciprocalGammaFactorialScale n * ((j : ℂ) + 1)⁻¹) * x) := by
            rw [Finset.sum_mul]
    _ = -((reciprocalGammaFactorialScale n *
          ∑ j ∈ Finset.range n, ((j : ℂ) + 1)⁻¹) * x) := by
            rw [Finset.mul_sum]

theorem sum_norm_reciprocalGammaProductTerm (n : ℕ) (x : ℂ) :
    ∑ j ∈ Finset.range n, ‖reciprocalGammaProductTerm n x j‖ =
      ‖gammaHarmonicMicroscopeScale n‖ * ‖x‖ := by
  rw [gammaHarmonicMicroscopeScale, norm_mul,
    norm_reciprocalGammaFactorialScale]
  have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
    rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact_mod_cast (show (0 : ℚ) ≤ harmonic n by
      rw [harmonic]
      positivity)
  rw [hnormH]
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  simp only [reciprocalGammaProductTerm, norm_neg, norm_div, norm_mul,
    Complex.norm_natCast]
  calc
    ∑ j ∈ Finset.range n,
        ‖reciprocalGammaFactorialScale n‖ * ‖x‖ / (j + 1 : ℕ) =
      ∑ j ∈ Finset.range n,
        (1 / (n.factorial : ℝ) * ((j + 1 : ℕ) : ℝ)⁻¹) * ‖x‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_reciprocalGammaFactorialScale]
          field_simp
    _ = (∑ j ∈ Finset.range n,
        1 / (n.factorial : ℝ) * ((j + 1 : ℕ) : ℝ)⁻¹) * ‖x‖ := by
          rw [Finset.sum_mul]
    _ = (1 / (n.factorial : ℝ) * ∑ j ∈ Finset.range n,
        ((j + 1 : ℕ) : ℝ)⁻¹) * ‖x‖ := by
          rw [Finset.mul_sum]

theorem reciprocalGammaNormalizedProduct_eq_prod_terms (n : ℕ) (x : ℂ) :
    reciprocalGammaNormalizedProduct n x =
      ∏ j ∈ Finset.range n, (1 + reciprocalGammaProductTerm n x j) := by
  rw [reciprocalGammaNormalizedProduct]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [reciprocalGammaProductTerm]
  ring

theorem gammaHarmonicMicroscopeScale_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    gammaHarmonicMicroscopeScale n ≠ 0 := by
  apply mul_ne_zero
  · exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)
  · exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'

theorem tendsto_reciprocalGammaNormalizedProduct_first_harmonic
    (x : ℂ) :
    Tendsto (fun n =>
      (reciprocalGammaNormalizedProduct n x - 1) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 (-x)) := by
  let E : ℕ → ℂ := fun n =>
    reciprocalGammaNormalizedProduct n x - 1 -
      ∑ j ∈ Finset.range n, reciprocalGammaProductTerm n x j
  have hq : Tendsto (fun n => ‖gammaHarmonicMicroscopeScale n‖ * ‖x‖)
      atTop (𝓝 0) :=
    by simpa [mul_comm] using
      tendsto_gammaHarmonicMicroscopeScale_zero.norm.const_mul ‖x‖
  have hmajor : Tendsto (fun n =>
      ‖x‖ * (Real.exp (‖gammaHarmonicMicroscopeScale n‖ * ‖x‖) - 1))
      atTop (𝓝 0) := by
    have hexp := (Real.continuous_exp.continuousAt.tendsto.comp hq).sub_const 1
    simpa using hexp.const_mul ‖x‖
  have hE : Tendsto (fun n => E n / gammaHarmonicMicroscopeScale n)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => norm_nonneg (E n / gammaHarmonicMicroscopeScale n))
      _ hmajor
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [norm_div]
    have hden := gammaHarmonicMicroscopeScale_ne_zero hn
    have hbound := norm_prod_one_add_sub_one_sub_sum_le
      (Finset.range n) (reciprocalGammaProductTerm n x)
    rw [← reciprocalGammaNormalizedProduct_eq_prod_terms] at hbound
    rw [sum_norm_reciprocalGammaProductTerm] at hbound
    calc
      ‖E n‖ / ‖gammaHarmonicMicroscopeScale n‖
          ≤ (‖gammaHarmonicMicroscopeScale n‖ * ‖x‖ *
              (Real.exp (‖gammaHarmonicMicroscopeScale n‖ * ‖x‖) - 1)) /
                ‖gammaHarmonicMicroscopeScale n‖ := by gcongr
      _ = ‖x‖ * (Real.exp (‖gammaHarmonicMicroscopeScale n‖ * ‖x‖) - 1) := by
        field_simp [norm_ne_zero_iff.mpr hden]
  have heq : ∀ᶠ n : ℕ in atTop,
      (reciprocalGammaNormalizedProduct n x - 1) /
          gammaHarmonicMicroscopeScale n =
        -x + E n / gammaHarmonicMicroscopeScale n := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hden := gammaHarmonicMicroscopeScale_ne_zero hn
    dsimp only [E]
    rw [sum_reciprocalGammaProductTerm]
    field_simp [hden]
    ring
  have hlim := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => -x) atTop (𝓝 (-x))).add hE).congr'
    (heq.mono fun _ h => h.symm)
  simpa using hlim

theorem differentiableAt_reciprocalGammaTangent_zero :
    DifferentiableAt ℂ reciprocalGammaTangent 0 := by
  have hdiff : Differentiable ℂ reciprocalGammaEntire := by
    simpa [reciprocalGammaEntire] using! Complex.differentiable_one_div_Gamma
  have han : AnalyticAt ℂ reciprocalGammaEntire 0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) 0 (Set.mem_univ 0)
  rcases han with ⟨p, hp⟩
  exact hp.has_fpower_series_dslope_fslope.differentiableAt

theorem tendsto_reciprocalGammaTangent_sub_one_div_harmonicScale
    (x : ℂ) :
    Tendsto (fun n =>
      (reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 0) := by
  have hsx : Tendsto (fun n => reciprocalGammaFactorialScale n * x) atTop (𝓝 0) :=
    by simpa using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hds : Tendsto (fun n => dslope reciprocalGammaTangent 0
      (reciprocalGammaFactorialScale n * x)) atTop
      (𝓝 (dslope reciprocalGammaTangent 0 0)) :=
    (continuousAt_dslope_same.mpr differentiableAt_reciprocalGammaTangent_zero).tendsto.comp hsx
  have hprod := (hds.mul tendsto_inv_harmonic_cast_complex_zero).const_mul x
  have heq : ∀ᶠ n : ℕ in atTop,
      (reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1) /
          gammaHarmonicMicroscopeScale n =
        x * (dslope reciprocalGammaTangent 0
          (reciprocalGammaFactorialScale n * x) * (harmonic n : ℂ)⁻¹) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hs : reciprocalGammaFactorialScale n ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    have hdslope := sub_smul_dslope reciprocalGammaTangent 0
      (reciprocalGammaFactorialScale n * x)
    simp only [sub_zero, smul_eq_mul, reciprocalGammaTangent_zero] at hdslope
    rw [gammaHarmonicMicroscopeScale]
    field_simp [hs, hH]
    rw [hdslope]
  simpa using hprod.congr' (heq.mono fun _ h => h.symm)

theorem tendsto_reciprocalGammaFactorialBlowUp_first_harmonic (x : ℂ) :
    Tendsto (fun n : ℕ =>
      (reciprocalGammaEntire
          (-(n : ℂ) + reciprocalGammaFactorialScale n * x) + x) /
        gammaHarmonicMicroscopeScale n)
      atTop (𝓝 (x ^ 2)) := by
  have hAq := tendsto_reciprocalGammaNormalizedProduct_first_harmonic x
  have hTq := tendsto_reciprocalGammaTangent_sub_one_div_harmonicScale x
  have hA_sub : Tendsto (fun n : ℕ => reciprocalGammaNormalizedProduct n x - 1)
      atTop (𝓝 0) := by
    have h := hAq.mul tendsto_gammaHarmonicMicroscopeScale_zero
    have heq : ∀ᶠ n : ℕ in atTop,
        (reciprocalGammaNormalizedProduct n x - 1) /
            gammaHarmonicMicroscopeScale n * gammaHarmonicMicroscopeScale n =
          reciprocalGammaNormalizedProduct n x - 1 := by
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      field_simp [gammaHarmonicMicroscopeScale_ne_zero hn]
    simpa using h.congr' heq
  have hA : Tendsto (fun n : ℕ => reciprocalGammaNormalizedProduct n x)
      atTop (𝓝 1) := by
    have h := hA_sub.add_const 1
    simpa using h
  have hT_sub : Tendsto (fun n : ℕ =>
      reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1)
      atTop (𝓝 0) := by
    have h := hTq.mul tendsto_gammaHarmonicMicroscopeScale_zero
    have heq : ∀ᶠ n : ℕ in atTop,
        (reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1) /
            gammaHarmonicMicroscopeScale n * gammaHarmonicMicroscopeScale n =
          reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1 := by
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      field_simp [gammaHarmonicMicroscopeScale_ne_zero hn]
    simpa using h.congr' heq
  have hT : Tendsto (fun n : ℕ =>
      reciprocalGammaTangent (reciprocalGammaFactorialScale n * x))
      atTop (𝓝 1) := by
    have h := hT_sub.add_const 1
    simpa using h
  have hcore := (hAq.mul hT).add hTq
  have hscaled := hcore.const_mul (-x)
  have heq : ∀ᶠ n : ℕ in atTop,
      (reciprocalGammaEntire
          (-(n : ℂ) + reciprocalGammaFactorialScale n * x) + x) /
          gammaHarmonicMicroscopeScale n =
        -x * (((reciprocalGammaNormalizedProduct n x - 1) /
            gammaHarmonicMicroscopeScale n) *
              reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) +
            (reciprocalGammaTangent (reciprocalGammaFactorialScale n * x) - 1) /
              gammaHarmonicMicroscopeScale n) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [reciprocalGammaFactorialBlowUp_exact]
    field_simp [gammaHarmonicMicroscopeScale_ne_zero hn]
    ring
  convert hscaled.congr' (heq.mono fun _ h => h.symm) using 1
  ring_nf

theorem ne_intCast_of_ne_zero_of_norm_lt_one {z : ℂ}
    (hz : z ≠ 0) (hzNorm : ‖z‖ < 1) (k : ℤ) :
    z ≠ (k : ℂ) := by
  intro heq
  have hkNorm : ‖(k : ℂ)‖ < 1 := by simpa [heq] using hzNorm
  rw [Complex.norm_intCast] at hkNorm
  have hkBounds : (-1 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1 := abs_lt.mp hkNorm
  have hkBoundsInt : (-1 : ℤ) < k ∧ k < 1 := by exact_mod_cast hkBounds
  have hk : k = 0 := by omega
  subst k
  exact hz (by simpa using heq)

theorem digamma_neg_nat_add_of_ne_int (z : ℂ)
    (hz : ∀ k : ℤ, z ≠ (k : ℂ)) (n : ℕ) :
    Complex.digamma (-(n : ℂ) + z) =
      Complex.digamma z +
        ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℂ) - z)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      let w : ℂ := -((n + 1 : ℕ) : ℂ) + z
      have hw : ∀ k : ℕ, w ≠ -(k : ℂ) := by
        intro k hwk
        apply hz ((n : ℤ) + 1 - (k : ℤ))
        dsimp [w] at hwk
        norm_num [Int.cast_sub, Int.cast_add]
        push_cast at hwk ⊢
        linear_combination hwk
      have hrec := Complex.digamma_apply_add_one w hw
      have hwadd : w + 1 = -(n : ℂ) + z := by
        dsimp [w]
        push_cast
        ring
      have hwinv : w⁻¹ = -((((n + 1 : ℕ) : ℂ) - z)⁻¹) := by
        have hwneg : w = -((((n + 1 : ℕ) : ℂ) - z)) := by
          dsimp [w]
          ring
        rw [hwneg, inv_neg]
      change Complex.digamma w = _
      calc
        Complex.digamma w = Complex.digamma (w + 1) - w⁻¹ := by
          exact eq_sub_of_add_eq hrec.symm
        _ = Complex.digamma (-(n : ℂ) + z) +
            ((((n + 1 : ℕ) : ℂ) - z)⁻¹) := by
          rw [hwadd, hwinv]
          ring
        _ = _ := by
          rw [ih, Finset.sum_range_succ]
          ring

def shiftedHarmonicSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℂ) - z)⁻¹

theorem norm_shiftedHarmonicTerm_sub_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (j : ℕ) :
    ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹ - (((j + 1 : ℕ) : ℂ))⁻¹‖ ≤
      2 * ‖z‖ / ((j + 1 : ℕ) : ℝ) := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hnormk : ‖((j + 1 : ℕ) : ℂ)‖ = k := by
    rw [Complex.norm_natCast]
  have hD : 1 / 2 ≤ ‖((j + 1 : ℕ) : ℂ) - z‖ := by
    have hrev := norm_sub_norm_le ((j + 1 : ℕ) : ℂ) z
    rw [hnormk] at hrev
    linarith
  have hDpos : 0 < ‖((j + 1 : ℕ) : ℂ) - z‖ :=
    lt_of_lt_of_le (by norm_num) hD
  have hk0 : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero j
  have hkz0 : (((j + 1 : ℕ) : ℂ) - z) ≠ 0 := norm_pos_iff.mp hDpos
  rw [show (((j + 1 : ℕ) : ℂ) - z)⁻¹ - (((j + 1 : ℕ) : ℂ))⁻¹ =
      z / (((j + 1 : ℕ) : ℂ) * (((j + 1 : ℕ) : ℂ) - z)) by
    field_simp [hk0, hkz0]
    ring]
  rw [norm_div, norm_mul, hnormk]
  rw [div_le_iff₀' (mul_pos hkpos hDpos)]
  field_simp [hkpos.ne']
  rw [show ((j + 1 : ℕ) : ℝ) = k by rfl]
  have hfactor : 1 ≤ 2 * ‖((j + 1 : ℕ) : ℂ) - z‖ := by linarith
  have hnon : 0 ≤ ‖z‖ * k := mul_nonneg (norm_nonneg z) hkpos.le
  nlinarith [mul_le_mul_of_nonneg_left hfactor hnon]

theorem norm_shiftedHarmonicSum_sub_harmonic_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedHarmonicSum n z - (harmonic n : ℂ)‖ ≤
      2 * ‖z‖ * (harmonic n : ℝ) := by
  rw [shiftedHarmonicSum, HilbertSchmidt.harmonic_cast_complex]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.range n,
        ((((j + 1 : ℕ) : ℂ) - z)⁻¹ - ((j : ℂ) + 1)⁻¹)‖ ≤
        ∑ j ∈ Finset.range n,
          ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹ - ((j : ℂ) + 1)⁻¹‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n,
        2 * ‖z‖ / ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_shiftedHarmonicTerm_sub_le hz j
    _ = 2 * ‖z‖ * (harmonic n : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

theorem tendsto_shiftedHarmonicSum_div_harmonic (x : ℂ) :
    Tendsto (fun n : ℕ =>
      shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) /
        (harmonic n : ℂ)) atTop (𝓝 1) := by
  have hsx : Tendsto (fun n : ℕ => reciprocalGammaFactorialScale n * x)
      atTop (𝓝 0) := by
    simpa using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hmajor : Tendsto (fun n : ℕ =>
      2 * ‖reciprocalGammaFactorialScale n * x‖) atTop (𝓝 0) := by
    simpa using hsx.norm.const_mul 2
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖reciprocalGammaFactorialScale n * x‖ ≤ 1 / 2 :=
    (hsx.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have herror : Tendsto (fun n : ℕ =>
      (shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) -
        (harmonic n : ℂ)) / (harmonic n : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      _ hmajor
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsn hn
    have hHreal : 0 < (harmonic n : ℝ) := by
      exact_mod_cast harmonic_pos (by omega : n ≠ 0)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast hHreal.ne'
    have hbound := norm_shiftedHarmonicSum_sub_harmonic_le hsn n
    rw [norm_div]
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHreal]
    rw [hnormH]
    calc
      ‖shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) -
          (harmonic n : ℂ)‖ / (harmonic n : ℝ) ≤
          (2 * ‖reciprocalGammaFactorialScale n * x‖ * (harmonic n : ℝ)) /
            (harmonic n : ℝ) := by gcongr
      _ = 2 * ‖reciprocalGammaFactorialScale n * x‖ := by
        field_simp [hHreal.ne']
  have hlim := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).add herror
  have heq : ∀ᶠ n : ℕ in atTop,
      shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) /
          (harmonic n : ℂ) =
        1 + (shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) -
          (harmonic n : ℂ)) / (harmonic n : ℂ) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    field_simp [hH]
    ring
  simpa using hlim.congr' (heq.mono fun _ h => h.symm)

def gammaFactorialScaledDigamma (n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n *
    Complex.digamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

theorem tendsto_gammaFactorialScaledDigamma_first_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledDigamma n x + x⁻¹) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 1) := by
  have hsx : Tendsto (fun n : ℕ => reciprocalGammaFactorialScale n * x)
      atTop (𝓝 0) := by
    simpa using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hinput : Tendsto (fun n : ℕ =>
      1 + reciprocalGammaFactorialScale n * x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hsx :
      Tendsto (fun n : ℕ => 1 + reciprocalGammaFactorialScale n * x)
        atTop (𝓝 (1 + 0)))
  have hOff1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpsi : Tendsto (fun n : ℕ =>
      Complex.digamma (1 + reciprocalGammaFactorialScale n * x))
      atTop (𝓝 (Complex.digamma 1)) :=
    (continuousAt_digamma 1 hOff1).tendsto.comp hinput
  have hlocal : Tendsto (fun n : ℕ =>
      Complex.digamma (1 + reciprocalGammaFactorialScale n * x) /
        (harmonic n : ℂ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      hpsi.mul tendsto_inv_harmonic_cast_complex_zero
  have hsum := tendsto_shiftedHarmonicSum_div_harmonic x
  have hlim := hlocal.add hsum
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖reciprocalGammaFactorialScale n * x‖ < 1 :=
    hsx.norm.eventually_lt_const (by norm_num)
  have heq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledDigamma n x + x⁻¹) /
          gammaHarmonicMicroscopeScale n =
        Complex.digamma (1 + reciprocalGammaFactorialScale n * x) /
            (harmonic n : ℂ) +
          shiftedHarmonicSum n (reciprocalGammaFactorialScale n * x) /
            (harmonic n : ℂ) := by
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsn hn
    let s : ℂ := reciprocalGammaFactorialScale n
    let z : ℂ := s * x
    have hs : s ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hz : z ≠ 0 := mul_ne_zero hs hx
    have hzNorm : ‖z‖ < 1 := by simpa [z, s] using hsn
    have hzInt : ∀ k : ℤ, z ≠ (k : ℂ) :=
      ne_intCast_of_ne_zero_of_norm_lt_one hz hzNorm
    have hzOff : ∀ k : ℕ, z ≠ -(k : ℂ) := by
      intro k
      simpa using hzInt (-(k : ℤ))
    have hback := digamma_neg_nat_add_of_ne_int z hzInt n
    have hstep := Complex.digamma_apply_add_one z hzOff
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    change (s * Complex.digamma (-(n : ℂ) + z) + x⁻¹) /
        (s * (harmonic n : ℂ)) = _
    rw [hback]
    change _ = Complex.digamma (1 + z) / (harmonic n : ℂ) + _
    rw [show Complex.digamma z = Complex.digamma (1 + z) - z⁻¹ by
      rw [add_comm]
      exact eq_sub_of_add_eq hstep.symm]
    rw [shiftedHarmonicSum]
    field_simp [hs, hx, hz, hH]
    dsimp [z, s]
    ring_nf
  simpa using hlim.congr' (heq.mono fun _ h => h.symm)

theorem gammaFactorialFirstJetDefect_eq_scaledDigamma
    (n : ℕ) (x : ℂ)
    (hpole : ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ)) :
    gammaFactorialFirstJetDefect n x =
      (gammaFactorialScaledDigamma n x * reciprocalGammaFactorialZoom n x - 1) /
        reciprocalGammaFactorialZoom n x ^ 2 := by
  let w : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hpole
  have hderiv : deriv Complex.Gamma w =
      Complex.digamma w * Complex.Gamma w := by
    rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hGamma]
  rw [gammaFactorialFirstJetDefect, iteratedDeriv_factorialBlowUpZoom]
  simp only [pow_one]
  simp only [iteratedDeriv_one, factorialBlowUpZoom]
  change reciprocalGammaFactorialScale n * deriv Complex.Gamma w -
      Complex.Gamma w ^ 2 = _
  rw [hderiv]
  change _ =
    (reciprocalGammaFactorialScale n * Complex.digamma w *
        (Complex.Gamma w)⁻¹ - 1) / ((Complex.Gamma w)⁻¹) ^ 2
  field_simp [hGamma]

/-- **Moving harmonic transverse residue.**  At every nonzero microscope point, the Riccati defect
of the exact Gamma zoom, divided by the harmonic factorial scale, converges to the nonzero
reciprocal direction `-2/x`. -/
theorem tendsto_gammaFactorialFirstJetDefect_div_harmonicScale
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialFirstJetDefect n x / gammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2 / x)) := by
  have hh : Tendsto (fun n : ℕ =>
      reciprocalGammaEntire
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      atTop (𝓝 (-x)) :=
    tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ x)
  have hhcor := tendsto_reciprocalGammaFactorialBlowUp_first_harmonic x
  have hqcor := tendsto_gammaFactorialScaledDigamma_first_harmonic hx
  have hnumRaw := (hqcor.mul hh).sub (hhcor.const_mul x⁻¹)
  have hscale_ne : ∀ᶠ n : ℕ in atTop,
      gammaHarmonicMicroscopeScale n ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact gammaHarmonicMicroscopeScale_ne_zero hn
  have hnumEq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledDigamma n x *
          reciprocalGammaFactorialZoom n x - 1) /
            gammaHarmonicMicroscopeScale n =
        ((gammaFactorialScaledDigamma n x + x⁻¹) /
            gammaHarmonicMicroscopeScale n) * reciprocalGammaFactorialZoom n x -
          x⁻¹ * ((reciprocalGammaFactorialZoom n x + x) /
            gammaHarmonicMicroscopeScale n) := by
    filter_upwards [hscale_ne] with n hn
    field_simp [hn, hx]
    ring
  have hnum : Tendsto (fun n : ℕ =>
      (gammaFactorialScaledDigamma n x * reciprocalGammaFactorialZoom n x - 1) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 (-2 * x)) := by
    convert hnumRaw.congr' (hnumEq.mono fun _ h => h.symm) using 1
    field_simp [hx]
    ring_nf
  have hden := hh.pow 2
  have hquot := hnum.div hden (pow_ne_zero 2 (neg_ne_zero.mpr hx))
  have hsx : Tendsto (fun n : ℕ => reciprocalGammaFactorialScale n * x)
      atTop (𝓝 0) := by
    simpa using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖reciprocalGammaFactorialScale n * x‖ < 1 :=
    hsx.norm.eventually_lt_const (by norm_num)
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ) := by
    filter_upwards [hsmall] with n hn k
    let z : ℂ := reciprocalGammaFactorialScale n * x
    have hs : reciprocalGammaFactorialScale n ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hz : z ≠ 0 := mul_ne_zero hs hx
    have hzInt : ∀ m : ℤ, z ≠ (m : ℂ) :=
      ne_intCast_of_ne_zero_of_norm_lt_one hz (by simpa [z] using hn)
    intro hpole
    apply hzInt ((n : ℤ) - (k : ℤ))
    dsimp [z]
    push_cast
    linear_combination hpole
  have heq : ∀ᶠ n : ℕ in atTop,
      gammaFactorialFirstJetDefect n x / gammaHarmonicMicroscopeScale n =
        ((gammaFactorialScaledDigamma n x * reciprocalGammaFactorialZoom n x - 1) /
          gammaHarmonicMicroscopeScale n) / reciprocalGammaFactorialZoom n x ^ 2 := by
    filter_upwards [hregular, hscale_ne] with n hn hscale
    have hGamma := Complex.Gamma_ne_zero (hn : ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ))
    have hhne : reciprocalGammaFactorialZoom n x ≠ 0 := by
      change (Complex.Gamma
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x))⁻¹ ≠ 0
      exact inv_ne_zero hGamma
    rw [gammaFactorialFirstJetDefect_eq_scaledDigamma n x hn]
    field_simp [hscale, hhne]
  convert hquot.congr' (heq.mono fun _ h => h.symm) using 1
  field_simp [hx]

end

end GaloisForLFunctions
