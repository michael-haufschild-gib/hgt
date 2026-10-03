import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervals
import GaloisForLFunctions.RHTower.CramerPrimeGapRH

/-!
# Under RH, primes in almost all intervals `(x, x + h]` with `h/log⁴x → ∞`

The almost-all argument of `PrimeAlmostAllShortIntervals` runs with an arbitrary window length
`h ∈ [200(Σ+1), X]`: the exceptional set of `x ∈ [X, 2X]` with `ψ(x + h) - ψ(x) < h/4` has measure
at most `8192 W(X) X Σ_ρ zeroShortWeight(X², 192X²/h²)` (`volume_psi_short_deficit_leH`).  Under the
Riemann hypothesis the zero weight is `X^{-1} min(1, Y/(¼+γ²))`; splitting at `S = 14X/h` gives
`Σ_ρ … ≤ 850(A + 1 + log(S+6))/h`, so with `W(X) ≪ log²X` the exceptional measure is
`O(X log³X/h)`.  Hence `ψ(x+h) - ψ(x) ≥ h/4` for almost all `x` once `h/log³X → ∞`, and a prime
lies in `(x, x+h]` for almost all `x` once `h/log⁴X → ∞` (the prime-power leakage is
`O(√h log²X)`).
-/

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory RHTower.Sieve

/-- The near zero sum with window `h`: `D_h(x) = Σ_{|γ| ≤ X⁴} d_ρ x^ρ`, `δ = h/(2X)`, `η = δ/8`. -/
def almostAllLowSumH (h X x : ℝ) : ℂ :=
  ∑ q ∈ almostAllLowZeros X,
    multWindowCoeff (h / (2 * X)) (h / (2 * X) / 8) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)

/-- **The pointwise bound for window `h`.** -/
theorem psi_short_ge_sub_norm_lowSumH {h X x : ℝ} (hX : 2 ≤ X)
    (hh : 200 * (xiSpectralThreeHalvesMass + 1) ≤ h) (hhX' : h ≤ X) (hx : x ∈ Set.Icc X (2 * X)) :
    5 / 16 * h - ‖almostAllLowSumH h X x‖ ≤ Chebyshev.psi (x + h) - Chebyshev.psi x := by
  set δ := h / (2 * X) with hδdef
  set η := δ / 8 with hηdef
  set Ms := xiSpectralThreeHalvesMass with hMs
  have hMs0 : 0 ≤ Ms := xiSpectralThreeHalvesMass_nonneg
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hx2 : 2 ≤ x := le_trans hX hx.1
  have hh200 : 200 ≤ h := by nlinarith
  have hhX : h ≤ X := hhX'
  have hδ : δ = h / (2 * X) := rfl
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; linarith
  have hδX : δ * X = h / 2 := by rw [hδ]; field_simp
  have hηX : η * X = h / 16 := by rw [hηdef]; linarith
  have hδx : δ * x ≤ h := by nlinarith [hx.2]
  have hmono : Chebyshev.psi (x + δ * x) ≤ Chebyshev.psi (x + h) :=
    Chebyshev.psi_mono (by linarith)
  have hlow := psi_mul_window_ge hx2 hη0 h2η hδ1
  -- the zero sum: near part plus far part
  set f : XiZeroCopy → ℂ := fun q => (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (summable_norm_inv_mul_one_sub.mul_left (12 * x / η))
      fun q => ?_
    have hd := norm_multWindowCoeff_le_div hη0 h2η hδ1 (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_self_of_one_le (by linarith) (xiZeroCopy_re_lt_one q).le
    rw [norm_inv_mul_one_sub_eq, hf]
    dsimp only
    rw [norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖multWindowCoeff δ η (q.1 : ℂ)‖
        ≤ x * (12 / (η * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) := by gcongr
      _ = 12 * x / η * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by
          field_simp
  have hsplit := hfs.sum_add_tsum_compl (s := almostAllLowZeros X)
  have hlowsum : ∑ q ∈ almostAllLowZeros X, f q = almostAllLowSumH h X x := by
    rw [almostAllLowSumH]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hf]
    exact mul_comm _ _
  have htail := norm_tsum_compl_mulWindow_le (x := x) (T := X ^ 4) (by linarith)
    (one_le_pow₀ hX1) hη0 h2η hδ1
  have hsq : Real.sqrt (X ^ 4) = X ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq] at htail
  change _ ≤ 36 * x / (η * X ^ 2) * Ms at htail
  set tail := ∑' q : ↑(((finite_xiOrdinateWindow (X ^ 4) 0).toFinset : Finset XiZeroCopy)
      : Set XiZeroCopy)ᶜ, (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeff δ η ((q : XiZeroCopy).1 : ℂ) with htaildef
  have hre : -‖almostAllLowSumH h X x‖ - ‖tail‖ ≤ (∑' q : XiZeroCopy, f q).re := by
    rw [← hsplit, Complex.add_re, ← hlowsum]
    have h1 := Complex.abs_re_le_norm (∑ q ∈ almostAllLowZeros X, f q)
    have h2 := Complex.abs_re_le_norm tail
    have h3 := neg_abs_le (∑ q ∈ almostAllLowZeros X, f q).re
    have h4 := neg_abs_le tail.re
    have : (∑' q : ↑((almostAllLowZeros X : Set XiZeroCopy)ᶜ), f q) = tail := rfl
    rw [this]
    linarith
  -- the far part is small
  have htail' : ‖tail‖ ≤ 1152 * Ms / h := by
    refine le_trans htail ?_
    have hxX : x ≤ 2 * X := hx.2
    have e1 : 36 * x / (η * X ^ 2) * Ms ≤ 36 * (2 * X) / (η * X ^ 2) * Ms := by gcongr
    have e2 : 36 * (2 * X) / (η * X ^ 2) * Ms = 1152 * Ms / h := by
      have : η * X ^ 2 = h / 16 * X := by rw [← hηX]; ring
      rw [this]
      field_simp
      ring
    linarith
  -- the trivial-zero term is small
  have htriv : 4 / (η * x ^ 2) ≤ 64 / (h * X) := by
    have hxx : X ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
    have : η * X ^ 2 = h / 16 * X := by rw [← hηX]; ring
    calc 4 / (η * x ^ 2) ≤ 4 / (η * X ^ 2) := by gcongr
      _ = 64 / (h * X) := by rw [this]; field_simp; ring
  have hmain : (δ - 2 * η) * x ≥ 3 / 8 * h := by
    have : δ - 2 * η = 3 / 4 * δ := by rw [hηdef]; ring
    rw [this]
    nlinarith [hx.1]
  have hsmall : 64 / (h * X) + 1152 * Ms / h ≤ h / 16 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by norm_num)]
    have h2 : 200 * (Ms + 1) * 200 ≤ h * h := by nlinarith
    have h3 : 512 + 18432 * Ms ≤ h * h := by linarith
    have h4 : 1024 + 18432 * X * Ms ≤ h * h * X := by
      have hm := mul_le_mul_of_nonneg_right h3 hX0.le
      calc 1024 + 18432 * X * Ms ≤ 512 * X + 18432 * X * Ms := by linarith
        _ = (512 + 18432 * Ms) * X := by ring
        _ ≤ h * h * X := hm
    have hpos : 0 ≤ h := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hpos
    calc (64 * h + h * X * (1152 * Ms)) * 16 = h * (1024 + 18432 * X * Ms) := by ring
      _ ≤ h * (h * h * X) := h5
      _ = h * (h * X * h) := by ring
  linarith


/-- **Chebyshev's inequality for window `h`.** -/
theorem volume_psi_short_deficit_leH {h X : ℝ} (hX : 2 ≤ X)
    (hh : 200 * (xiSpectralThreeHalvesMass + 1) ≤ h) (hhX' : h ≤ X) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + h) - Chebyshev.psi x < h / 4}).toReal
      ≤ 8192 * almostAllHarmonicWeight X * X
        * ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2)
            (q.1 : ℂ) := by
  set δ := h / (2 * X) with hδdef
  set η := δ / 8 with hηdef
  set F := almostAllLowZeros X with hF
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hMs0 := xiSpectralThreeHalvesMass_nonneg
  have hh200 : 200 ≤ h := by nlinarith
  have hhX : h ≤ X := hhX'
  have hδ : δ = h / (2 * X) := rfl
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; linarith
  set g : ℝ → ℝ := fun x => ‖almostAllLowSumH h X x‖ ^ 2 / x ^ 3 with hg
  set c : ℝ := (h / 16) ^ 2 / (2 * X) ^ 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- the exceptional set lies in a superlevel set of `g`
  have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X)
      ∧ Chebyshev.psi (x + h) - Chebyshev.psi x < h / 4}
      ⊆ {x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X) := by
    rintro x ⟨hx, hlt⟩
    refine ⟨?_, hx⟩
    have hpt := psi_short_ge_sub_norm_lowSumH hX hh hhX' hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hn : h / 16 ≤ ‖almostAllLowSumH h X x‖ := by linarith
    have hn2 : (h / 16) ^ 2 ≤ ‖almostAllLowSumH h X x‖ ^ 2 := by
      have : 0 ≤ h / 16 := by positivity
      nlinarith
    have hx3 : x ^ 3 ≤ (2 * X) ^ 3 := by
      have := hx.2
      gcongr
    show c ≤ ‖almostAllLowSumH h X x‖ ^ 2 / x ^ 3
    rw [hc]
    calc (h / 16) ^ 2 / (2 * X) ^ 3 ≤ (h / 16) ^ 2 / x ^ 3 := by gcongr
      _ ≤ ‖almostAllLowSumH h X x‖ ^ 2 / x ^ 3 := by gcongr
  -- Markov
  have hcontD : ContinuousOn (fun x : ℝ => almostAllLowSumH h X x) (Set.Icc X (2 * X)) := by
    refine continuousOn_finsetSum _ fun q _ => continuousOn_const.mul ?_
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx.1]))
  have hcontg : ContinuousOn g (Set.Icc X (2 * X)) := by
    refine (hcontD.norm.pow 2).div (continuousOn_pow 3) fun x hx => ?_
    have : 0 < x := by linarith [hx.1]
    positivity
  have hgint : Integrable g (volume.restrict (Set.Icc X (2 * X))) :=
    hcontg.integrableOn_Icc
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : 0 < x := by linarith [hx.1]
    simp only [Pi.zero_apply, hg]
    positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hg0 hgint c
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Icc] at hmarkov
  have hint_eq : ∫ x, g x ∂(volume.restrict (Set.Icc X (2 * X))) = ∫ x in X..2 * X, g x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [hint_eq] at hmarkov
  -- the mean square
  have hW : ∀ q ∈ F, ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
      ≤ almostAllHarmonicWeight X := by
    intro q hq
    have hmem : ∀ q' ∈ F, |(q'.1 : ℂ).im| ≤ X ^ 4 := by
      intro q' hq'
      rw [hF, almostAllLowZeros, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff,
        sub_zero] at hq'
      exact hq'
    have hq4 := hmem q hq
    have hR : ∀ q' ∈ F, |(q'.1 : ℂ).im - (q.1 : ℂ).im| ≤ 2 * X ^ 4 := by
      intro q' hq'
      have := hmem q' hq'
      have := abs_sub (q'.1 : ℂ).im (q.1 : ℂ).im
      linarith
    have hharm := sum_inv_one_add_abs_im_sub_le F (t := (q.1 : ℂ).im) (by positivity) hR
    have hcomm : ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
        = ∑ q' ∈ F, 1 / (1 + |(q'.1 : ℂ).im - (q.1 : ℂ).im|) := by
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [abs_sub_comm]
    rw [hcomm]
    refine le_trans hharm ?_
    rw [almostAllHarmonicWeight]
    have hl : Real.log (|(q.1 : ℂ).im| + 2 * X ^ 4 + 4) ≤ Real.log (3 * X ^ 4 + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hl0 : 0 ≤ 1 + Real.log (2 * X ^ 4 + 1) := by
      have : 0 ≤ Real.log (2 * X ^ 4 + 1) :=
        Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
      linarith
    gcongr
  have hms := integral_norm_sq_zeroSum_div_cube_le hX0 F
    (fun q => multWindowCoeff δ η (q.1 : ℂ)) hW
  -- each coefficient against the zero weight
  have hY : 192 * X ^ 2 / h ^ 2 = 48 / δ ^ 2 := by
    rw [hδ]; field_simp; ring
  have hcoef : ∀ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 4 * δ ^ 2 * zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2) (q.1 : ℂ) := by
    intro q _
    have hρ0 := xiZeroCopy_re_pos q
    have hρ1 := xiZeroCopy_re_lt_one q
    have hd1 := norm_multWindowCoeff_le_two_mul hη0 h2η hρ0 hρ1
    have hd2 := norm_multWindowCoeff_le_div hη0 h2η hδ1 hρ0 hρ1
    have hρne := xiZeroCopy_ne_zero q
    have hρ1ne : 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero q
    set P := ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ with hP
    have hP0 : 0 < P := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
    set d := ‖multWindowCoeff δ η (q.1 : ℂ)‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hd2' : d ≤ 96 / (δ * P) := by
      refine le_trans hd2 (le_of_eq ?_)
      rw [hηdef]
      field_simp
      ring
    have hXp : X ^ (2 * (q.1 : ℂ).re - 2) = (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by
      rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rw [zeroShortWeight, hY, hXp]
    have hXp0 : 0 ≤ (X ^ 2) ^ ((q.1 : ℂ).re - 1) := Real.rpow_nonneg (by positivity) _
    have hmin : d ^ 2 ≤ 4 * δ ^ 2 * min 1 (48 / δ ^ 2 / P) := by
      rcases le_total 1 (48 / δ ^ 2 / P) with hle | hle
      · rw [min_eq_left hle]
        nlinarith
      · rw [min_eq_right hle]
        have : d ^ 2 ≤ 2 * δ * (96 / (δ * P)) := by
          rw [sq]
          exact mul_le_mul hd1 hd2' hd0 (by positivity)
        refine le_trans this (le_of_eq ?_)
        field_simp
        ring
    calc d ^ 2 * (X ^ 2) ^ ((q.1 : ℂ).re - 1)
        ≤ 4 * δ ^ 2 * min 1 (48 / δ ^ 2 / P) * (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by gcongr
      _ = 4 * δ ^ 2 * ((X ^ 2) ^ ((q.1 : ℂ).re - 1) * min 1 (48 / δ ^ 2 / P)) := by ring
  have hzsum : ∑ q ∈ F, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2) (q.1 : ℂ)
      ≤ ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2)
          (q.1 : ℂ) := by
    refine Summable.sum_le_tsum F (fun q _ => zeroShortWeight_nonneg (by positivity)
      (by positivity) _) (summable_zeroShortWeight (one_le_pow₀ hX1) (by positivity))
  set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2)
    (q.1 : ℂ) with hZ
  have hW0 : 0 ≤ almostAllHarmonicWeight X := by
    rw [almostAllHarmonicWeight]
    have h1 : 0 ≤ Real.log (3 * X ^ 4 + 4) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
    have h2 : 0 ≤ Real.log (2 * X ^ 4 + 1) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
    positivity
  have hsumcoef : ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 4 * δ ^ 2 * Z := by
    calc ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
        ≤ ∑ q ∈ F, 4 * δ ^ 2 * zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2)
            (q.1 : ℂ) := Finset.sum_le_sum hcoef
      _ = 4 * δ ^ 2 * ∑ q ∈ F, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2)
            (q.1 : ℂ) := by rw [Finset.mul_sum]
      _ ≤ 4 * δ ^ 2 * Z := by gcongr
  have hgeq : (fun x : ℝ => ‖∑ q ∈ F, multWindowCoeff δ η (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
      / x ^ 3) = g := rfl
  rw [hgeq] at hms
  -- assemble
  have hvol : (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + h) - Chebyshev.psi x < h / 4}).toReal
      ≤ (volume ({x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X))).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hfinal : c * (volume ({x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X))).toReal
      ≤ 16 * almostAllHarmonicWeight X * δ ^ 2 * Z := by
    refine le_trans hmarkov (le_trans hms ?_)
    have := mul_le_mul_of_nonneg_left hsumcoef (by positivity : 0 ≤ 4 * almostAllHarmonicWeight X)
    linarith
  have hcδ : 16 * almostAllHarmonicWeight X * δ ^ 2 * Z / c
      = 8192 * almostAllHarmonicWeight X * X * Z := by
    rw [hc, hδ]
    field_simp
    ring
  rw [← hcδ, le_div_iff₀ hc0]
  nlinarith


/-! ## The zero weight under RH -/

/-- **The zero sum of the almost-all window under RH.**  `Σ_ρ zeroShortWeight(X², 192X²/h²) ≤
850(A + 4 + log X)/h` for `1 ≤ h ≤ X`. -/
theorem tsum_zeroShortWeight_almostAll_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {X h : ℝ} (hX : 2 ≤ X) (hh1 : 1 ≤ h) (hhX : h ≤ X) :
    ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h ^ 2) (q.1 : ℂ)
      ≤ 850 * (xiLineTwoLogDerivConstant + 4 + Real.log X) / h := by
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  have hX0 : 0 < X := by linarith
  have hh0 : 0 < h := by linarith
  set S : ℝ := 14 * X / h with hSdef
  have hXh : 1 ≤ X / h := by rw [le_div_iff₀ hh0]; linarith
  have hS14 : 14 ≤ S := by rw [hSdef, mul_div_assoc]; linarith
  have hS4 : 4 ≤ S := by linarith
  have hz := tsum_zeroShortWeight_le_of_riemannHypothesis hRH (x := X ^ 2)
    (Y := 192 * X ^ 2 / h ^ 2) (S := S) (by nlinarith) (by positivity) hS4
  rw [← hA] at hz
  have hpow : (X ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / X := by
    rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le]
    norm_num
    exact Real.rpow_neg_one X
  rw [hpow] at hz
  have hSX : S + 6 ≤ 20 * X := by
    rw [hSdef, div_add' _ _ _ hh0.ne', div_le_iff₀ hh0]
    nlinarith
  have hlog : Real.log (S + 6) ≤ Real.log X + 3 := by
    have h1 : Real.log (S + 6) ≤ Real.log (20 * X) := Real.log_le_log (by linarith) hSX
    rw [Real.log_mul (by norm_num) hX0.ne'] at h1
    have h20 : Real.log 20 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hlog4 : Real.log (S + 4) ≤ Real.log X + 3 := by
    have := Real.log_le_log (by linarith : 0 < S + 4) (by linarith : S + 4 ≤ S + 6)
    linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hT : lagTailBound S ≤ 40 * (A + 4 + Real.log X) / S := by
    unfold lagTailBound
    rw [← hA]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hl6 : 0 ≤ Real.log (S + 6) := Real.log_nonneg (by linarith)
  have hP : 0 ≤ A + 4 + Real.log X := by linarith
  refine hz.trans ?_
  have h1 : 20 * (S + 1) * (A + Real.log (S + 6)) ≤ 20 * (15 * X / h) * (A + 4 + Real.log X) := by
    have hS1 : S + 1 ≤ 15 * X / h := by
      rw [hSdef, div_add_one hh0.ne', div_le_div_iff_of_pos_right hh0]; linarith
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have h2 : 192 * X ^ 2 / h ^ 2 * lagTailBound S
      ≤ 192 * X ^ 2 / h ^ 2 * (40 * (A + 4 + Real.log X) / S) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have e2 : 192 * X ^ 2 / h ^ 2 * (40 * (A + 4 + Real.log X) / S)
      = 3840 / 7 * (X / h) * (A + 4 + Real.log X) := by
    rw [hSdef]; field_simp; ring
  have e1 : 20 * (15 * X / h) * (A + 4 + Real.log X) = 300 * (X / h) * (A + 4 + Real.log X) := by
    ring
  have hsum : 20 * (S + 1) * (A + Real.log (S + 6)) + 192 * X ^ 2 / h ^ 2 * lagTailBound S
      ≤ 850 * (X / h) * (A + 4 + Real.log X) := by
    have : 0 ≤ (X / h) * (A + 4 + Real.log X) := by positivity
    nlinarith
  calc 1 / X * (20 * (S + 1) * (A + Real.log (S + 6)) + 192 * X ^ 2 / h ^ 2 * lagTailBound S)
      ≤ 1 / X * (850 * (X / h) * (A + 4 + Real.log X)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 850 * (A + 4 + Real.log X) / h := by field_simp

/-- **Under RH, primes are dense in almost all intervals of length `h` with `h/log³X → ∞`.** -/
theorem tendsto_volume_psi_short_deficit_of_riemannHypothesis (hRH : RiemannHypothesis)
    {h : ℝ → ℝ} (hh : Tendsto (fun X => h X / Real.log X ^ 3) atTop atTop)
    (hhX : ∀ᶠ X in atTop, h X ≤ X) :
    Tendsto (fun X : ℝ => (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + h X) - Chebyshev.psi x < h X / 4}).toReal / X) atTop (𝓝 0) := by
  set A := xiLineTwoLogDerivConstant with hA
  have hA0 : 0 ≤ A := xiLineTwoLogDerivConstant_nonneg
  set K := |xiLineTwoLogDerivConstant| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  -- the majorant `C (log X + 1)² (log X + A + 4)/h X → 0`
  set C : ℝ := 8192 * (64 * (K + 2)) * 4 * 850 with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  have hratio : Tendsto (fun X : ℝ => (Real.log X + 1) ^ 2 * (Real.log X + A + 4) / h X) atTop
      (𝓝 0) := by
    have hinv : Tendsto (fun X => Real.log X ^ 3 / h X) atTop (𝓝 0) := by
      have := hh.inv_tendsto_atTop
      refine this.congr' ?_
      filter_upwards [hh.eventually_gt_atTop 0] with X hX
      simp only [Pi.inv_apply, inv_div]
    have hpoly : Tendsto (fun X : ℝ => (Real.log X + 1) ^ 2 * (Real.log X + A + 4)
        / Real.log X ^ 3) atTop (𝓝 1) := by
      have hl : Tendsto (fun X : ℝ => (Real.log X)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
      have hlim : Tendsto (fun X : ℝ => (1 + (Real.log X)⁻¹) ^ 2 * (1 + (A + 4) * (Real.log X)⁻¹))
          atTop (𝓝 ((1 + 0) ^ 2 * (1 + (A + 4) * 0))) :=
        ((tendsto_const_nhds.add hl).pow 2).mul (tendsto_const_nhds.add (hl.const_mul _))
      simp only [add_zero, one_pow, mul_zero, mul_one] at hlim
      refine hlim.congr' ?_
      filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with X hX
      field_simp
      ring
    have := hpoly.mul hinv
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with X hX
    have : Real.log X ^ 3 ≠ 0 := pow_ne_zero 3 hX.ne'
    field_simp
  have hlim := hratio.const_mul C
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · have hbig : ∀ᶠ X : ℝ in atTop, 200 * (xiSpectralThreeHalvesMass + 1) ≤ h X := by
      have hlog3 : Tendsto (fun X : ℝ => Real.log X ^ 3) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
      have hprod := hh.atTop_mul_atTop₀ hlog3
      refine (hprod.eventually_ge_atTop (200 * (xiSpectralThreeHalvesMass + 1))).mono ?_
      intro X hX
      by_cases h0 : Real.log X ^ 3 = 0
      · simp [h0] at hX
        have := xiSpectralThreeHalvesMass_nonneg
        linarith
      · rwa [div_mul_cancel₀ _ h0] at hX
    filter_upwards [hbig, hhX, eventually_ge_atTop (3 : ℝ)] with X hXh hXX hX3
    have hX0 : 0 < X := by linarith
    have hMs := xiSpectralThreeHalvesMass_nonneg
    have hh1 : 1 ≤ h X := by linarith
    have hh0 : 0 < h X := by linarith
    have hv := volume_psi_short_deficit_leH (by linarith : (2 : ℝ) ≤ X) hXh hXX
    have hW := almostAllHarmonicWeight_le (by linarith : (1 : ℝ) ≤ X)
    rw [← hK] at hW
    have hZ := tsum_zeroShortWeight_almostAll_le_of_riemannHypothesis hRH
      (by linarith : (2 : ℝ) ≤ X) hh1 hXX
    rw [← hA] at hZ
    set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * X ^ 2 / h X ^ 2) (q.1 : ℂ)
      with hZdef
    have hZ0 : 0 ≤ Z := tsum_nonneg fun q => zeroShortWeight_nonneg (by positivity)
      (by positivity) _
    have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
    have hlog2 : Real.log (X ^ 2) + 2 = 2 * (Real.log X + 1) := by
      rw [Real.log_pow]; push_cast; ring
    have hW0 : 0 ≤ almostAllHarmonicWeight X := by
      rw [almostAllHarmonicWeight]
      have h1 : 0 ≤ Real.log (3 * X ^ 4 + 4) := Real.log_nonneg (by nlinarith)
      have h2 : 0 ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by nlinarith)
      positivity
    rw [div_le_iff₀ hX0]
    calc _ ≤ 8192 * almostAllHarmonicWeight X * X * Z := hv
      _ ≤ 8192 * (64 * (K + 2) * (Real.log (X ^ 2) + 2) ^ 2) * X
            * (850 * (A + 4 + Real.log X) / h X) := by gcongr
      _ = C * ((Real.log X + 1) ^ 2 * (Real.log X + A + 4) / h X) * X := by
          rw [hlog2, hC]; ring


/-- **Under RH, almost all intervals `(x, x + h]` contain a prime once `h/log⁴X → ∞`.** -/
theorem tendsto_volume_no_prime_short_of_riemannHypothesis (hRH : RiemannHypothesis)
    {h : ℝ → ℝ} (hh : Tendsto (fun X => h X / Real.log X ^ 4) atTop atTop)
    (hhX : ∀ᶠ X in atTop, h X ≤ X) :
    Tendsto (fun X : ℝ => (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + h X}).toReal / X) atTop (𝓝 0) := by
  have hh3 : Tendsto (fun X => h X / Real.log X ^ 3) atTop atTop := by
    have hprod := hh.atTop_mul_atTop₀ Real.tendsto_log_atTop
    refine hprod.congr' ?_
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with X hX
    have : Real.log X ^ 4 = Real.log X ^ 3 * Real.log X := by ring
    rw [this]; field_simp
  have hmain := tendsto_volume_psi_short_deficit_of_riemannHypothesis hRH hh3 hhX
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := (64 / Real.log 2) ^ 2 * 16 with hB
  have hbig : ∀ᶠ X : ℝ in atTop, B * Real.log X ^ 4 ≤ h X := by
    filter_upwards [hh.eventually_ge_atTop B, Real.tendsto_log_atTop.eventually_gt_atTop 0]
      with X hX hlX
    have : 0 < Real.log X ^ 4 := by positivity
    rwa [le_div_iff₀ this] at hX
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · filter_upwards [hbig, hhX, Real.tendsto_log_atTop.eventually_ge_atTop 2,
      eventually_ge_atTop (3 : ℝ)] with X hXb hXX hlX hX3
    have hX0 : 0 < X := by linarith
    refine div_le_div_of_nonneg_right ?_ hX0.le
    have hB0 : 0 < B := by rw [hB]; positivity
    have hl4 : 16 ≤ Real.log X ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlX 4
      norm_num at this; linarith
    have hB1 : 1 ≤ B := by
      rw [hB]
      have h64 : 1 ≤ 64 / Real.log 2 := by
        rw [le_div_iff₀ hl2]; have := Real.log_two_lt_d9; linarith
      nlinarith
    have hh1 : 1 ≤ h X := by nlinarith
    have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + h X}
        ⊆ {x : ℝ | x ∈ Set.Icc X (2 * X)
          ∧ Chebyshev.psi (x + h X) - Chebyshev.psi x < h X / 4} := by
      rintro x ⟨hx, hnp⟩
      refine ⟨hx, lt_of_not_ge fun hge => hnp ?_⟩
      have hx2 : 2 ≤ x := by linarith [hx.1]
      have hleak := Sieve.chebyshevPsi_window_le_theta_window_add_local_primePower
        (a := x) (b := x + h X) hx2 (by linarith) (by linarith)
      rw [show x + h X - x = h X by ring] at hleak
      have hb : Real.log (x + h X) ≤ 2 * Real.log X := by
        calc Real.log (x + h X) ≤ Real.log (3 * X) :=
              Real.log_le_log (by linarith) (by linarith [hx.2])
          _ = Real.log 3 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
          _ ≤ 2 * Real.log X := by
              have : Real.log 3 ≤ 2 := by
                rw [Real.log_le_iff_le_exp (by norm_num)]
                have h3 : (3 : ℝ) ≤ Real.exp 2 := by
                  have := Real.add_one_le_exp (2 : ℝ); linarith
                exact h3
              linarith
      have hb0 : 0 ≤ Real.log (x + h X) := Real.log_nonneg (by linarith)
      have hsq1 : 1 ≤ Real.sqrt (h X) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hsqh : Real.sqrt (h X) * Real.sqrt (h X) = h X := Real.mul_self_sqrt (by linarith)
      -- `√h ≥ (64/log 2)·4 log²X`
      have hsqbig : 64 / Real.log 2 * (4 * Real.log X ^ 2) ≤ Real.sqrt (h X) := by
        rw [Real.le_sqrt (by positivity) (by linarith)]
        have : (64 / Real.log 2 * (4 * Real.log X ^ 2)) ^ 2 = B * Real.log X ^ 4 := by
          rw [hB]; ring
        rw [this]; exact hXb
      have hlk : Real.log (x + h X) / Real.log 2 * (Real.sqrt (h X) + 1) * Real.log (x + h X)
          ≤ h X / 32 := by
        have e1 : Real.log (x + h X) / Real.log 2 * (Real.sqrt (h X) + 1) * Real.log (x + h X)
            ≤ (2 * Real.log X) * (2 * Real.log X) * (2 * Real.sqrt (h X)) / Real.log 2 := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2]
          have h1 : Real.log (x + h X) * Real.log (x + h X) ≤ (2 * Real.log X) * (2 * Real.log X) :=
            mul_le_mul hb hb hb0 (by linarith)
          calc Real.log (x + h X) * (Real.sqrt (h X) + 1) * Real.log (x + h X)
              = Real.log (x + h X) * Real.log (x + h X) * (Real.sqrt (h X) + 1) := by ring
            _ ≤ (2 * Real.log X) * (2 * Real.log X) * (2 * Real.sqrt (h X)) :=
                mul_le_mul h1 (by linarith) (by linarith) (by positivity)
        refine e1.trans ?_
        rw [div_le_iff₀ hl2]
        have e2 : 2 * Real.log X * (2 * Real.log X) * (2 * Real.sqrt (h X))
            = 8 * Real.log X ^ 2 * Real.sqrt (h X) := by ring
        rw [e2]
        have hmul := mul_le_mul_of_nonneg_left hsqbig (Real.sqrt_nonneg (h X))
        have e3 : Real.sqrt (h X) * (64 / Real.log 2 * (4 * Real.log X ^ 2))
            = 256 / Real.log 2 * (Real.log X ^ 2 * Real.sqrt (h X)) := by ring
        rw [e3, hsqh] at hmul
        have hl2' : Real.log 2 ≤ 1 := by
          have := Real.log_two_lt_d9; linarith
        have hpos : 0 ≤ Real.log X ^ 2 * Real.sqrt (h X) := by positivity
        have h4 : 256 / Real.log 2 * (Real.log X ^ 2 * Real.sqrt (h X)) * Real.log 2
            = 256 * (Real.log X ^ 2 * Real.sqrt (h X)) := by field_simp
        nlinarith
      have hθw : 0 < Chebyshev.theta (x + h X) - Chebyshev.theta x := by linarith
      exact exists_prime_of_theta_window_pos (by linarith) (by linarith) hθw
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => hx.1) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

end

end RHTower
