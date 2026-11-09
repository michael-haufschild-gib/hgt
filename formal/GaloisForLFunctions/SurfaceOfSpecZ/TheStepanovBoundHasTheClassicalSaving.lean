import GaloisForLFunctions.SurfaceOfSpecZ.ConfigurationsNeedAnAttainedTopAtTwoFrobenii
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionSharp

/-!
# The Stepanov bound has the classical saving

The trivial Stepanov exponent `½` holds with `o(·)` (`ThePrimeNumberTheoremInEveryWindow`); with the
classical zero-free region it holds with the de la Vallée Poussin saving, unconditionally:

  `|2 Re S(u)| ≤ C e^{u/2 − √u/10}`   (`exists_norm_lagStructure_le`),

so the smoothed prime count in the window of `n` is its archimedean-plus-pole prediction up to
`O(√n e^{−√(log n)/10})` (`exists_abs_primeWindow_sub_archPoleWindow_le`).

A zero `ρ = β + it` contributes at most `m (1 + |t|)^{−8} e^{(β − ½)u}` (the spline transform decays
like `(1 + |t|)^{−4}`). Above height `4` the zero-free region `β ≤ 1 − 1/(58 log |t|)`
(`RHTower.riemannZeta_ne_zero_of_one_sub_lt_re`) and `(1 + |t|)^{−6} ≤ e^{−6 log |t|}` give
`e^{u/2 − (6L + u/(58L))} ≤ e^{u/2 − √u/10}`, `L = log |t|` (`sqrt_div_ten_le`). The finitely many
zeros below height `4` have `β ≤ 1 − δ` (`exists_low_margin`). The remaining factor `(1 + |t|)^{−2}` is
summable by temperedness. Any exponent `σ < ½` is a zero-free strip (`TheWidthLawAtEveryGapSet`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **The zero-free region** for the zeros of `ζ` above height `4`. -/
theorem re_le_of_mem_zetaZeroConfig {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (h4 : 4 ≤ |ρ.im|) :
    ρ.re ≤ 1 - 1 / 58 / Real.log |ρ.im| := by
  by_contra hlt
  push Not at hlt
  have hxi :=
    (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      hρ).1
  have hζ := (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
  have h := _root_.RHTower.riemannZeta_ne_zero_of_one_sub_lt_re h4 hlt
  rw [Complex.re_add_im] at h
  exact h hζ

/-- **The low zeros.** The finitely many zeros below height `4` lie left of `1 − δ`. -/
theorem exists_low_margin : ∃ δ : ℝ, 0 < δ ∧
    ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < 4 → ρ.re ≤ 1 - δ := by
  have hfin := zetaZeroConfig.finite_window (-4) 4
  set S := zetaZeroConfig.carrier ∩ {ρ : ℂ | -4 < ρ.im ∧ ρ.im ≤ 4} with hS
  have hmem : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < 4 → ρ ∈ S := fun ρ hρ h =>
    ⟨hρ, by have := abs_lt.mp h; exact ⟨this.1, this.2.le⟩⟩
  by_cases hne : S.Nonempty
  · obtain ⟨ρ₁, hρ₁, hmax⟩ := Set.exists_max_image S Complex.re hfin hne
    have h1 : ρ₁.re < 1 :=
      (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
        hρ₁.1).2.2
    refine ⟨1 - ρ₁.re, by linarith, fun ρ hρ him => ?_⟩
    have := hmax ρ (hmem ρ hρ him)
    linarith
  · exact ⟨1, one_pos, fun ρ hρ him => absurd ⟨ρ, hmem ρ hρ him⟩ hne⟩

/-- **The optimization** `6L + u/(58L) ≥ √u/10`. -/
theorem sqrt_div_ten_le {u L : ℝ} (hu : 0 ≤ u) (hL : 0 < L) :
    Real.sqrt u / 10 ≤ 6 * L + u / (58 * L) := by
  have hs := Real.sqrt_nonneg u
  have hsq := Real.mul_self_sqrt hu
  rcases le_or_gt (Real.sqrt u) (60 * L) with h | h
  · have : 0 ≤ u / (58 * L) := by positivity
    linarith
  · have hsp : 0 < Real.sqrt u := by linarith
    have : Real.sqrt u / 10 ≤ u / (58 * L) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith

/-- `δu ≥ √u/10 − 1/(100δ)`. -/
theorem sqrt_div_ten_le_mul {u δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ) :
    Real.sqrt u / 10 - 1 / (100 * δ) ≤ δ * u := by
  have hs := Real.sqrt_nonneg u
  have hsq := Real.mul_self_sqrt hu
  rcases le_or_gt (1 / (10 * δ)) (Real.sqrt u) with h | h
  · have h1 : 1 / 10 ≤ δ * Real.sqrt u := by
      rw [div_le_iff₀ (by positivity)] at h; nlinarith
    have : 0 ≤ 1 / (100 * δ) := by positivity
    nlinarith
  · have h1 : Real.sqrt u / 10 < 1 / (100 * δ) := by
      have e : 1 / (100 * δ) = 1 / (10 * δ) / 10 := by field_simp; ring
      rw [e]
      exact div_lt_div_of_pos_right h (by norm_num)
    have : 0 ≤ δ * u := by positivity
    linarith

/-- **The weight of one zero.** `(1 + |t|)^{−6} e^{(β − ½)u} ≤ e^{1/(100δ)} e^{u/2 − √u/10}`. -/
theorem pow_mul_exp_le {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < 4 → ρ.re ≤ 1 - δ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {u : ℝ} (hu : 0 ≤ u) :
    1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u) ≤
      Real.exp (1 / (100 * δ)) * Real.exp (u / 2 - Real.sqrt u / 10) := by
  have hK1 : 1 ≤ Real.exp (1 / (100 * δ)) := Real.one_le_exp (by positivity)
  rcases lt_or_ge |ρ.im| 4 with h4 | h4
  · have hβ := hlow ρ hρ h4
    have h1 : 1 / (1 + |ρ.im|) ^ 6 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith [abs_nonneg ρ.im])
    have h2 : Real.exp ((ρ.re - 1 / 2) * u) ≤
        Real.exp (1 / (100 * δ)) * Real.exp (u / 2 - Real.sqrt u / 10) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have := sqrt_div_ten_le_mul hu hδ
      nlinarith
    calc 1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u)
        ≤ 1 * Real.exp ((ρ.re - 1 / 2) * u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact h2
  · have hβ := re_le_of_mem_zetaZeroConfig hρ h4
    set L := Real.log |ρ.im| with hL
    have hL0 : 0 < L := Real.log_pos (by linarith)
    have ht : (0 : ℝ) < |ρ.im| := by linarith
    have h1 : 1 / (1 + |ρ.im|) ^ 6 ≤ Real.exp (-(6 * L)) := by
      have : Real.exp (-(6 * L)) = 1 / |ρ.im| ^ 6 := by
        rw [Real.exp_neg, show 6 * L = ((6 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul, hL,
          Real.exp_log ht, one_div]
      rw [this]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ht.le (by linarith) 6)
    have h2 : (ρ.re - 1 / 2) * u ≤ u / 2 - u / (58 * L) := by
      have : ρ.re - 1 / 2 ≤ 1 / 2 - 1 / (58 * L) := by
        have e : 1 / 58 / L = 1 / (58 * L) := by rw [div_div]
        rw [← e]; linarith
      have := mul_le_mul_of_nonneg_right this hu
      have e2 : (1 / 2 - 1 / (58 * L)) * u = u / 2 - u / (58 * L) := by ring
      linarith
    have h3 := sqrt_div_ten_le hu hL0
    calc 1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u)
        ≤ Real.exp (-(6 * L)) * Real.exp (u / 2 - u / (58 * L)) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (u / 2 - (6 * L + u / (58 * L))) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (u / 2 - Real.sqrt u / 10) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hK1

theorem gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by simp [gammaOf, Complex.div_I]

theorem gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by simp [gammaOf, Complex.div_I]

/-- **The classical saving.** Unconditionally, `‖S(u)‖ ≤ C e^{u/2 − √u/10}` for `u ≥ 0`. -/
theorem exists_norm_lagStructure_le : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖ ≤ C * Real.exp (u / 2 - Real.sqrt u / 10) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_low_margin
  set K := Real.exp (1 / (100 * δ))
  set A : ℝ := 2 ^ (3 + 1) * Real.exp ((3 + 1) / 2)
  have hT := temperedConfig_zetaZeroConfig
  unfold TemperedConfig at hT
  set Sw := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine ⟨2 * A ^ 2 * K * Sw, fun u hu => ?_⟩
  set E := Real.exp (u / 2 - Real.sqrt u / 10)
  set f : zetaZeroConfig.carrier → ℂ := fun ρ => (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ) * cexp (I * gammaOf ρ * u)
  have hb := (contDiff_boxSpline (r := 1) one_pos 2).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hterm : ∀ ρ : zetaZeroConfig.carrier, ‖f ρ‖ ≤
      2 * A ^ 2 * K * E * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hρ := ρ.2
    have hstrip :=
      (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
        hρ).2
    set w := gammaOf (ρ : ℂ)
    set t := (ρ : ℂ).im
    have hwre : w.re = t := gammaOf_re _
    have hwim : w.im = 1 / 2 - (ρ : ℂ).re := gammaOf_im _
    have hwim2 : |w.im| ≤ 1 / 2 := by rw [hwim, abs_le]; constructor <;> linarith
    have hty : |t| ≤ ‖w‖ := by rw [← hwre]; exact Complex.abs_re_le_norm w
    have hB1 := norm_paperFT_boxSpline_le' 3 hwim2 (abs_nonneg t) hty
    have hcim : |(conj w).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hwim2
    have hcn : |t| ≤ ‖conj w‖ := by rw [Complex.norm_conj]; exact hty
    have hB2 := norm_paperFT_boxSpline_le' 3 hcim (abs_nonneg t) hcn
    have hF : ‖paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) w‖ ≤ A ^ 2 / (1 + |t|) ^ 8 := by
      rw [EF.paperFT_weilTest hb hb hbc hbc, norm_mul, Complex.norm_conj]
      calc ‖paperFT (boxSpline 1 3) w‖ * ‖paperFT (boxSpline 1 3) (conj w)‖
          ≤ (A / (1 + |t|) ^ (3 + 1)) * (A / (1 + |t|) ^ (3 + 1)) :=
            mul_le_mul hB1 hB2 (norm_nonneg _) (by positivity)
        _ = A ^ 2 / (1 + |t|) ^ 8 := by field_simp; ring
    have hE : ‖cexp (I * w * u)‖ = Real.exp (((ρ : ℂ).re - 1 / 2) * u) := by
      rw [Complex.norm_exp]
      congr 1
      have : I * w * u = ((ρ : ℂ) - 1 / 2) * u := by
        simp only [w, gammaOf]; field_simp
      rw [this]; simp
    have hW := pow_mul_exp_le hδ hlow hρ hu
    have hnorm : 1 + Complex.normSq w ≤ 2 * (1 + |t|) ^ 2 := by
      rw [Complex.normSq_apply, hwre, hwim]
      have h1 : ((1 / 2 - (ρ : ℂ).re) * (1 / 2 - (ρ : ℂ).re)) ≤ 1 := by nlinarith
      nlinarith [abs_nonneg t, sq_abs t]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hpos : 0 < 1 + Complex.normSq w := by have := Complex.normSq_nonneg w; linarith
    simp only [f]
    rw [norm_mul, norm_mul, Complex.norm_natCast, hE]
    -- `m · A²/(1+|t|)⁸ · e^{(β−½)u} ≤ 2A²K E · m/(1 + |w|²)`
    have key : A ^ 2 / (1 + |t|) ^ 8 * Real.exp (((ρ : ℂ).re - 1 / 2) * u) ≤
        2 * A ^ 2 * K * E * (1 / (1 + Complex.normSq w)) := by
      have h6 : A ^ 2 / (1 + |t|) ^ 8 * Real.exp (((ρ : ℂ).re - 1 / 2) * u) =
          A ^ 2 * (1 / (1 + |t|) ^ 2) *
            (1 / (1 + |t|) ^ 6 * Real.exp (((ρ : ℂ).re - 1 / 2) * u)) := by
        field_simp
      have h7 : 1 / (1 + |t|) ^ 2 ≤ 2 * (1 / (1 + Complex.normSq w)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
        linarith
      rw [h6]
      calc A ^ 2 * (1 / (1 + |t|) ^ 2) *
            (1 / (1 + |t|) ^ 6 * Real.exp (((ρ : ℂ).re - 1 / 2) * u))
          ≤ A ^ 2 * (2 * (1 / (1 + Complex.normSq w))) * (K * E) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h7 (by positivity)) hW (by positivity)
              (by positivity)
        _ = _ := by ring
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) w‖ *
          Real.exp (((ρ : ℂ).re - 1 / 2) * u)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (A ^ 2 / (1 + |t|) ^ 8) *
            Real.exp (((ρ : ℂ).re - 1 / 2) * u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hm) (Real.exp_pos _).le
      _ = (zetaZeroConfig.mult ρ : ℝ) * (A ^ 2 / (1 + |t|) ^ 8 *
            Real.exp (((ρ : ℂ).re - 1 / 2) * u)) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (2 * A ^ 2 * K * E * (1 / (1 + Complex.normSq w))) :=
          mul_le_mul_of_nonneg_left key hm
      _ = _ := by ring
  have hsum : Summable fun ρ : zetaZeroConfig.carrier => ‖f ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hT.mul_left _)
  calc ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖ = ‖∑' ρ, f ρ‖ := rfl
    _ ≤ ∑' ρ, ‖f ρ‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, 2 * A ^ 2 * K * E *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
        Summable.tsum_le_tsum hterm hsum (hT.mul_left _)
    _ = 2 * A ^ 2 * K * Sw * E := by rw [tsum_mul_left]; ring

/-- **The prime number theorem in every window, with the classical error.** -/
theorem exists_abs_primeWindow_sub_archPoleWindow_le : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |primeWindow n - archPoleWindow n| ≤
      C * Real.sqrt n * Real.exp (-(Real.sqrt (Real.log n) / 10)) := by
  obtain ⟨C, hC⟩ := exists_norm_lagStructure_le
  refine ⟨C, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := hC _ hlog
  have he : Real.exp (Real.log n / 2 - Real.sqrt (Real.log n) / 10) =
      Real.sqrt n * Real.exp (-(Real.sqrt (Real.log n) / 10)) := by
    have e1 : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; ring_nf
    rw [sub_eq_add_neg, Real.exp_add, e1]
  have hid : primeWindow n - archPoleWindow n =
      -(lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re := by
    rw [← orbitCorr_eq_re_lagStructure_spline, orbitCorr_log_eq_archPoleWindow_sub_primeWindow]
    ring
  rw [hid, abs_neg]
  calc |(lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re|
      ≤ ‖lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.exp (Real.log n / 2 - Real.sqrt (Real.log n) / 10) := h
    _ = _ := by rw [he]; ring

end GaloisForLFunctions.SurfaceOfSpecZ
