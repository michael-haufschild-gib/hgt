import GaloisForLFunctions.RHTower.XiZeroOrdinateHarmonicSums

/-!
# Mean square of a finite zero sum over a dyadic range

For a finite set `F` of zeros and coefficients `c_ρ`,

`∫_X^{2X} |Σ_{ρ ∈ F} c_ρ x^ρ|² x^{-3} dx = Re Σ_{ρ,ρ'} c_ρ c̄_{ρ'} ∫_X^{2X} x^{ρ+ρ̄'-3} dx`,

and `|∫_X^{2X} x^{s-1} dx| ≤ 4 X^{Re s}/(1 + |Im s|)` for `Re s ≤ 0`
(`norm_integral_cpow_sub_one_le`):
the trivial bound `X^{Re s}` near the diagonal and the exact primitive `((2X)^s - X^s)/s` away from
it.  With `|c_ρ c_ρ'| X^{β+β'-2} ≤ (|c_ρ|²X^{2β-2} + |c_ρ'|²X^{2β'-2})/2` this gives

`∫_X^{2X} |Σ c_ρ x^ρ|² x^{-3} dx ≤ 4 W Σ_ρ |c_ρ|² X^{2β-2}`

whenever `Σ_{ρ' ∈ F} 1/(1 + |γ - γ'|) ≤ W` for every `ρ ∈ F`
(`integral_norm_sq_zeroSum_div_cube_le`).
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- `|∫_X^{2X} x^{s-1} dx| ≤ 4 X^{Re s}/(1 + |Im s|)` for `X > 0` and `Re s < 0`. -/
theorem norm_integral_cpow_sub_one_le {X : ℝ} (hX : 0 < X) {s : ℂ} (hs : s.re < 0) :
    ‖∫ x in X..2 * X, (x : ℂ) ^ (s - 1)‖ ≤ 4 * X ^ s.re / (1 + |s.im|) := by
  have hX2 : X ≤ 2 * X := by linarith
  have hXs : 0 < X ^ s.re := Real.rpow_pos_of_pos hX _
  -- the trivial bound
  have htriv : ‖∫ x in X..2 * X, (x : ℂ) ^ (s - 1)‖ ≤ X ^ s.re := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := X) (b := 2 * X)
      (C := X ^ (s.re - 1)) (f := fun x : ℝ => (x : ℂ) ^ (s - 1)) (fun x hx => by
        rw [Set.uIoc_of_le hX2] at hx
        have hx0 : 0 < x := lt_trans hX hx.1
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        simp only [Complex.sub_re, Complex.one_re]
        exact Real.rpow_le_rpow_of_nonpos hX hx.1.le (by linarith))
    refine le_trans h (le_of_eq ?_)
    rw [show 2 * X - X = X by ring, abs_of_pos hX, ← Real.rpow_add_one hX.ne']
    ring_nf
  -- the exact primitive
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have h0 : (0 : ℝ) ∉ Set.uIcc X (2 * X) := by
    rw [Set.uIcc_of_le hX2]
    intro h
    linarith [h.1]
  have hprim : ∫ x in X..2 * X, (x : ℂ) ^ (s - 1) = (((2 * X : ℝ) : ℂ) ^ s - (X : ℂ) ^ s) / s := by
    rw [integral_cpow (Or.inr ⟨fun h => hs0 (by linear_combination h), h0⟩)]
    simp
  rcases le_or_gt |s.im| 1 with h1 | h1
  · refine le_trans htriv ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have hims : 0 < |s.im| := by linarith
    have hnum : ‖((2 * X : ℝ) : ℂ) ^ s - (X : ℂ) ^ s‖ ≤ 2 * X ^ s.re := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.norm_cpow_eq_rpow_re_of_pos hX]
      have : (2 * X) ^ s.re ≤ X ^ s.re := Real.rpow_le_rpow_of_nonpos hX hX2 hs.le
      linarith
    rw [hprim, norm_div]
    calc ‖((2 * X : ℝ) : ℂ) ^ s - (X : ℂ) ^ s‖ / ‖s‖ ≤ 2 * X ^ s.re / ‖s‖ := by
          gcongr
      _ ≤ 2 * X ^ s.re / |s.im| := by
          gcongr
          exact Complex.abs_im_le_norm s
      _ ≤ 4 * X ^ s.re / (1 + |s.im|) := by
          rw [div_le_div_iff₀ hims (by positivity)]
          nlinarith

/-- `‖z‖² x^{-3}` of a finite zero sum as the real part of a double sum of powers. -/
theorem norm_sq_zeroSum_div_cube_eq {x : ℝ} (hx : 0 < x) (F : Finset XiZeroCopy)
    (c : XiZeroCopy → ℂ) :
    ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3
      = (∑ q ∈ F, ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q')
          * (x : ℂ) ^ ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 3)).re := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hconj : ∀ w : ℂ, (starRingEnd ℂ) ((x : ℂ) ^ w) = (x : ℂ) ^ ((starRingEnd ℂ) w) := by
    intro w
    have h := Complex.conj_cpow (x : ℂ) ((starRingEnd ℂ) w) (by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_pos.ne)
    rw [Complex.conj_ofReal, Complex.conj_conj] at h
    exact h.symm
  have hpow : ∀ q q' : XiZeroCopy, (x : ℂ) ^ ((q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 3)
      = (x : ℂ) ^ (q.1 : ℂ) * (x : ℂ) ^ ((starRingEnd ℂ) (q'.1 : ℂ)) / ((x ^ 3 : ℝ) : ℂ) := by
    intro q q'
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_add _ _ hx0,
      show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast
    ring
  have hnorm : ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
      = ((∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ))
          * (starRingEnd ℂ) (∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ))).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hnorm, ← Complex.div_ofReal_re, map_sum, Finset.sum_mul_sum, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [map_mul, hconj, hpow]
  ring

/-- `2uvk ≤ (u² + v²)k`, summed over a symmetric nonnegative kernel. -/
theorem sum_sum_mul_mul_le_of_symm (F : Finset XiZeroCopy) (u : XiZeroCopy → ℝ)
    (k : XiZeroCopy → XiZeroCopy → ℝ) (hk : ∀ q q', 0 ≤ k q q') (hks : ∀ q q', k q q' = k q' q) :
    ∑ q ∈ F, ∑ q' ∈ F, u q * u q' * k q q' ≤ ∑ q ∈ F, u q ^ 2 * ∑ q' ∈ F, k q q' := by
  have h1 : ∀ q q', u q * u q' * k q q' ≤ (u q ^ 2 * k q q' + u q' ^ 2 * k q q') / 2 := by
    intro q q'
    have := mul_le_mul_of_nonneg_right (two_mul_le_add_sq (u q) (u q')) (hk q q')
    linarith
  have h2 : ∑ q ∈ F, ∑ q' ∈ F, u q' ^ 2 * k q q' = ∑ q ∈ F, ∑ q' ∈ F, u q ^ 2 * k q q' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    rw [hks]
  calc ∑ q ∈ F, ∑ q' ∈ F, u q * u q' * k q q'
      ≤ ∑ q ∈ F, ∑ q' ∈ F, (u q ^ 2 * k q q' + u q' ^ 2 * k q q') / 2 :=
        Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun q' _ => h1 q q'
    _ = (∑ q ∈ F, ∑ q' ∈ F, u q ^ 2 * k q q' + ∑ q ∈ F, ∑ q' ∈ F, u q' ^ 2 * k q q') / 2 := by
        simp only [Finset.sum_div, ← Finset.sum_add_distrib]
    _ = ∑ q ∈ F, u q ^ 2 * ∑ q' ∈ F, k q q' := by
        rw [h2]
        simp only [Finset.mul_sum]
        ring

/-- **Mean square of a finite zero sum.**  If `Σ_{ρ' ∈ F} 1/(1 + |γ - γ'|) ≤ W` for every
`ρ ∈ F`, then `∫_X^{2X} |Σ_{ρ ∈ F} c_ρ x^ρ|² x^{-3} dx ≤ 4 W Σ_{ρ ∈ F} |c_ρ|² X^{2β-2}`. -/
theorem integral_norm_sq_zeroSum_div_cube_le {X W : ℝ} (hX : 0 < X) (F : Finset XiZeroCopy)
    (c : XiZeroCopy → ℂ)
    (hW : ∀ q ∈ F, ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤ W) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3
      ≤ 4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2) := by
  have hX2 : X ≤ 2 * X := by linarith
  set e : XiZeroCopy → XiZeroCopy → ℂ := fun q q' => (q.1 : ℂ) + (starRingEnd ℂ) (q'.1 : ℂ) - 3
    with he
  have hcont : ∀ w : ℂ, ContinuousOn (fun x : ℝ => (x : ℂ) ^ w) (Set.uIcc X (2 * X)) := by
    intro w
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    rw [Set.uIcc_of_le hX2] at hx
    exact Complex.continuousAt_ofReal_cpow_const x w (Or.inr (by linarith [hx.1]))
  have hint : ∀ q q' : XiZeroCopy, IntervalIntegrable
      (fun x : ℝ => c q * (starRingEnd ℂ) (c q') * (x : ℂ) ^ e q q')
      MeasureTheory.volume X (2 * X) :=
    fun q q' => (continuousOn_const.mul (hcont (e q q'))).intervalIntegrable
  have hrow : ∀ q : XiZeroCopy, ContinuousOn
      (fun x : ℝ => ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q') * (x : ℂ) ^ e q q')
      (Set.uIcc X (2 * X)) :=
    fun q => continuousOn_finsetSum _ fun q' _ => continuousOn_const.mul (hcont _)
  -- the integrand as a real part
  have hcongr : Set.EqOn (fun x : ℝ => ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)
      (fun x : ℝ => Complex.reCLM (∑ q ∈ F, ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q')
        * (x : ℂ) ^ e q q')) (Set.uIcc X (2 * X)) := by
    intro x hx
    rw [Set.uIcc_of_le hX2] at hx
    simp only [Complex.reCLM_apply, he]
    exact norm_sq_zeroSum_div_cube_eq (lt_of_lt_of_le hX hx.1) F c
  rw [intervalIntegral.integral_congr hcongr]
  have hsumcont : ContinuousOn (fun x : ℝ => ∑ q ∈ F, ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q')
      * (x : ℂ) ^ e q q') (Set.uIcc X (2 * X)) :=
    continuousOn_finsetSum _ fun q _ => hrow q
  rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hsumcont.intervalIntegrable,
    Complex.reCLM_apply]
  have hout : ∫ x in X..2 * X, ∑ q ∈ F, ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q') * (x : ℂ) ^ e q q'
      = ∑ q ∈ F, ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q') * ∫ x in X..2 * X, (x : ℂ) ^ e q q' := by
    have h := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := X) (b := 2 * X)
      (s := F) (f := fun q (x : ℝ) => ∑ q' ∈ F, c q * (starRingEnd ℂ) (c q') * (x : ℂ) ^ e q q')
      (fun q _ => (hrow q).intervalIntegrable)
    rw [h]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h' := intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume) (a := X) (b := 2 * X)
      (s := F) (f := fun q' (x : ℝ) => c q * (starRingEnd ℂ) (c q') * (x : ℂ) ^ e q q')
      (fun q' _ => hint q q')
    rw [h']
    exact Finset.sum_congr rfl fun q' _ => intervalIntegral.integral_const_mul _ _
  rw [hout]
  -- the Gram bound
  set u : XiZeroCopy → ℝ := fun q => ‖c q‖ * X ^ ((q.1 : ℂ).re - 1) with hu
  set k : XiZeroCopy → XiZeroCopy → ℝ := fun q q' => 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
    with hk
  have hk0 : ∀ q q', 0 ≤ k q q' := fun q q' => by rw [hk]; positivity
  have hks : ∀ q q', k q q' = k q' q := fun q q' => by rw [hk]; dsimp only; rw [abs_sub_comm]
  have hterm : ∀ q q' : XiZeroCopy,
      ‖c q * (starRingEnd ℂ) (c q') * ∫ x in X..2 * X, (x : ℂ) ^ e q q'‖
        ≤ 4 * (u q * u q' * k q q') := by
    intro q q'
    have hre : (e q q' + 1).re < 0 := by
      rw [he]
      simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.one_re]
      norm_num
      linarith [xiZeroCopy_re_lt_one q, xiZeroCopy_re_lt_one q']
    have hI := norm_integral_cpow_sub_one_le hX hre
    rw [show e q q' + 1 - 1 = e q q' by ring] at hI
    have hre' : (e q q' + 1).re = ((q.1 : ℂ).re - 1) + ((q'.1 : ℂ).re - 1) := by
      rw [he]
      simp only [Complex.add_re, Complex.sub_re, Complex.conj_re, Complex.one_re]
      norm_num
      ring
    have him' : (e q q' + 1).im = (q.1 : ℂ).im - (q'.1 : ℂ).im := by
      rw [he]
      simp only [Complex.add_im, Complex.sub_im, Complex.conj_im, Complex.one_im]
      norm_num
      ring
    rw [hre', him', Real.rpow_add hX] at hI
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖c q‖ * ‖c q'‖ * ‖∫ x in X..2 * X, (x : ℂ) ^ e q q'‖
        ≤ ‖c q‖ * ‖c q'‖ * (4 * (X ^ ((q.1 : ℂ).re - 1) * X ^ ((q'.1 : ℂ).re - 1))
            / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)) := by gcongr
      _ = 4 * (u q * u q' * k q q') := by
          rw [hu, hk]
          dsimp only
          ring
  refine le_trans (Complex.re_le_norm _) ?_
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun q _ => norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun q' _ => hterm q q') ?_
  simp_rw [← Finset.mul_sum]
  have hgram := sum_sum_mul_mul_le_of_symm F u k hk0 hks
  have hW' : ∑ q ∈ F, u q ^ 2 * ∑ q' ∈ F, k q q' ≤ ∑ q ∈ F, u q ^ 2 * W :=
    Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hW q hq) (sq_nonneg _)
  have hu2 : ∀ q : XiZeroCopy, u q ^ 2 = ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2) := by
    intro q
    rw [hu]
    dsimp only
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    push_cast
    ring
  calc 4 * ∑ q ∈ F, ∑ q' ∈ F, u q * u q' * k q q' ≤ 4 * ∑ q ∈ F, u q ^ 2 * W := by
        linarith
    _ = 4 * W * ∑ q ∈ F, ‖c q‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hu2]
        ring

end

end RHTower
