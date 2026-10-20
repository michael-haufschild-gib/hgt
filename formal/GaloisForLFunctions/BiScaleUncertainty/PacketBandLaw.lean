import GaloisForLFunctions.BiScaleUncertainty.PacketSignGapLaw

/-!
# The band of one packet: the square-root barrier as a single-probe energy law

The band of the field is the energy `∫_0^L Ẽ²` of the normalized Chebyshev error; it is linear in
`L` iff RH. Here the same law holds for the energy of a single compact packet.

**Packet band law** (`packet_band_iff`). For a real compact `C²` source `f` and `σ ≥ 0`:
`∫_T^L P_f² = O((1 + L) e^{2σL})` iff `f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`.

* `riemannHypothesis_iff_packet_band_of_universal`: for a universal probe `U`, RH holds iff the
  band of the single packet `P_U` is linear, `∫_T^L P_U² = O(1 + L)`; its slope is then `E(U)`.
* `xiZeroHalfPlaneBound_iff_packet_band_of_universal`: the zero width `β` is half the exponential
  rate of the band of `P_U`.

**Mechanism.** A band bound controls the energy of the zero series `G` on every unit window beyond
the support, since `G = A − P` with `A` bounded. Smoothing by a bump `k` gives the zero series with
coefficients `c_ρ k̂(γ_ρ)` (`integral_mul_zeroSeries_add`), and the inequality
`2|k||G| ≤ e^{στ}k² + e^{−στ}|G|²` turns window energy into the pointwise bound
`O((1 + τ) e^{στ})`. The residue law of the zero resolvent kills `c_ρ k̂(γ_ρ)` at every deeper zero,
and a bump with `k̂(γ_ρ) ≠ 0` isolates `c_ρ`. Continuity of the packet (`continuous_stationaryPacket`,
by local finiteness of the grid and of the polar support) makes the band integrals honest.
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Continuity of the stationary packet -/

/-- **The stationary packet of a compact continuous source is continuous**: near every shift only
finitely many grid points and a bounded polar range meet the source. -/
theorem continuous_stationaryPacket {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (stationaryPacket f) := by
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hz : ∀ v : ℝ, w ≤ |v| → f v = 0 := fun v hv => hwf v (by rwa [Real.norm_eq_abs])
  rw [continuous_iff_continuousAt]
  intro τ₀
  set X := τ₀ + 1 + w
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  have hnbhd : Ioo (τ₀ - 1) (τ₀ + 1) ∈ 𝓝 τ₀ := Ioo_mem_nhds (by linarith) (by linarith)
  -- the grid sum is a finite sum near `τ₀`
  have hloc : ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1),
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * f (Real.log n - τ)) =
        ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          f (Real.log n - τ) := by
    intro τ hτ
    refine tsum_eq_sum fun n hn => ?_
    simp only [Finset.mem_range, not_lt] at hn
    have hn0 : (0 : ℝ) < n := by
      have : (0 : ℝ) < N := lt_of_le_of_lt (Real.exp_pos X).le hN
      exact this.trans_le (by exact_mod_cast hn)
    have hlog : X < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hn0]
      exact hN.trans_le (by exact_mod_cast hn)
    rw [hz _ (by rw [abs_of_pos (by linarith [hτ.2])]; linarith [hτ.2]), mul_zero]
  -- the polar integral is an interval integral near `τ₀`
  set M := max X 0
  have hpol : ∀ τ ∈ Ioo (τ₀ - 1) (τ₀ + 1),
      (∫ x in Ioi (0 : ℝ), 2 * Real.cosh (x / 2) * f (x - τ)) =
        ∫ x in (0 : ℝ)..M, 2 * Real.cosh (x / 2) * f (x - τ) := by
    intro τ hτ
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ M from le_max_right _ _)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
      (f := fun x => 2 * Real.cosh (x / 2) * f (x - τ)) measurableSet_Ioi
      (Ioc_subset_Ioi_self : Ioc (0 : ℝ) M ⊆ Ioi 0) fun x hx => ?_
    have hxM : M < x := by
      by_contra h
      exact hx.2 ⟨hx.1, not_lt.mp h⟩
    have hx' : w ≤ |x - τ| := by
      rw [abs_of_pos (by linarith [le_max_left X 0, hτ.2])]
      linarith [le_max_left X 0, hτ.2]
    rw [hz _ hx', mul_zero]
  have hcont : ContinuousAt (fun τ => (∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * f (Real.log n - τ)) -
        ∫ x in (0 : ℝ)..M, 2 * Real.cosh (x / 2) * f (x - τ)) τ₀ := by
    refine ((continuous_finsetSum _ fun n _ => by fun_prop).sub ?_).continuousAt
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun τ x => 2 * Real.cosh (x / 2) * f (x - τ)) (by fun_prop) continuous_const
  refine hcont.congr (Filter.eventuallyEq_of_mem hnbhd fun τ hτ => ?_)
  simp only [stationaryPacket]
  rw [hloc τ hτ, hpol τ hτ]

/-! ## Smoothing a zero series -/

/-- Smoothing the zero series by `k` multiplies its coefficients by `k̂(γ_ρ)`. -/
theorem integral_mul_zeroSeries_add {Z : Zeta23.ZeroConfig} {c : Z.carrier → ℂ}
    (hc : Summable fun ρ => ‖c ρ‖) {k : ℝ → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (τ : ℝ) :
    ∫ s, (k s : ℂ) * zeroSeries c (τ + s) =
      zeroSeries (fun ρ => c ρ * Zeta23.paperFT (fun u => (k u : ℂ)) (Zeta23.gammaOf ρ)) τ := by
  haveI : Countable Z.carrier := (countable_carrier Z).to_subtype
  obtain ⟨R, hR, hRk⟩ := hkc.exists_pos_le_norm
  have hkz : ∀ s : ℝ, R ≤ |s| → k s = 0 := fun s hs => hRk s (by rwa [Real.norm_eq_abs])
  set F : Z.carrier → ℝ → ℂ := fun ρ s => (k s : ℂ) * (c ρ * cexp (zeroShift ρ * (τ + s)))
  have hFn : ∀ ρ s, ‖F ρ s‖ ≤ ‖c ρ‖ * Real.exp ((|τ| + R) / 2) * |k s| := fun ρ s => by
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hs : R ≤ |s|
    · rw [hkz s hs, abs_zero]; simp
    · have h1 := norm_exp_zeroShift_mul_le ρ (τ + s)
      have h2 : Real.exp (|τ + s| / 2) ≤ Real.exp ((|τ| + R) / 2) :=
        Real.exp_le_exp.mpr (by have := abs_add_le τ s; linarith [not_le.mp hs])
      have : ‖cexp (zeroShift ρ * ↑(τ + s))‖ ≤ Real.exp ((|τ| + R) / 2) := by
        push_cast at h1 ⊢; exact h1.trans h2
      push_cast at this
      calc |k s| * (‖c ρ‖ * ‖cexp (zeroShift ρ * (↑τ + ↑s))‖)
          ≤ |k s| * (‖c ρ‖ * Real.exp ((|τ| + R) / 2)) := by gcongr
        _ = _ := by ring
  have hkint : Integrable fun s => |k s| := (hk.integrable_of_hasCompactSupport hkc).abs
  have hint : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (hkint.const_mul (‖c ρ‖ * Real.exp ((|τ| + R) / 2))).mono'
      ((Complex.continuous_ofReal.comp hk).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun s => (hFn ρ s).trans (le_of_eq (by ring)))
  have hsum : Summable fun ρ => ∫ s, ‖F ρ s‖ := by
    refine ((hc.mul_right (Real.exp ((|τ| + R) / 2))).mul_right (∫ s, |k s|)).of_nonneg_of_le
      (fun ρ => integral_nonneg fun _ => norm_nonneg _) fun ρ => ?_
    rw [← integral_const_mul]
    exact integral_mono (hint ρ).norm (hkint.const_mul _) fun s => (hFn ρ s).trans (le_of_eq (by ring))
  have hpt : ∀ s, (k s : ℂ) * zeroSeries c (τ + s) = ∑' ρ, F ρ s := fun s => by
    rw [zeroSeries, ← tsum_mul_left]
    push_cast
    rfl
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum, zeroSeries]
  refine tsum_congr fun ρ => ?_
  have hsplit : ∀ s, F ρ s = c ρ * cexp (zeroShift ρ * τ) * ((k s : ℂ) * cexp (I * Zeta23.gammaOf ρ * s)) :=
    fun s => by
      simp only [F]
      rw [← I_mul_gammaOf, mul_add, Complex.exp_add]
      ring
  simp_rw [hsplit]
  rw [integral_const_mul]
  unfold Zeta23.paperFT
  ring

/-! ## The band law -/

/-- **Band bound kills deep coefficients.** If `∫_T^L P_f² ≤ K(1 + L)e^{2σL}` for all `L ≥ T`, then
`f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem paperFT_eq_zero_of_packet_band {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {σ K T : ℝ} (hσ : 0 ≤ σ)
    (hband : ∀ L : ℝ, T ≤ L →
      ∫ τ in T..L, stationaryPacket f τ ^ 2 ≤ K * (1 + L) * Real.exp (2 * σ * L))
    (ρ : 𝒵) (hρ : σ < (ρ : ℂ).re - 1 / 2) :
    Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hc := summable_norm_packetCoeff hf hfc
  set A := packetArchTail f
  set G := zeroSeries (packetCoeff f)
  set CA := 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r *
    (Zeta23.EF.gammaBracket r : ℂ)‖
  have hA : ∀ τ, ‖A τ‖ ≤ CA := norm_packetArchTail_le f
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hA 0)
  have hPc : Continuous (stationaryPacket f) := continuous_stationaryPacket hf.continuous hfc
  -- a bump that sees `ρ`
  obtain ⟨k, hk, hkc, hkρ⟩ := exists_bump_paperFT_ne_zero (Zeta23.gammaOf ρ)
  obtain ⟨R, hR, hRk⟩ := hkc.exists_pos_le_norm
  have hkz : ∀ s : ℝ, R ≤ |s| → k s = 0 := fun s hs => hRk s (by rwa [Real.norm_eq_abs])
  set k₂ := ∫ s in (-R)..R, k s ^ 2
  have hk₂ : 0 ≤ k₂ := intervalIntegral.integral_nonneg (by linarith) fun s _ => sq_nonneg _
  -- the smoothed coefficients
  set k₀ : ℝ → ℂ := fun u => (k u : ℂ)
  have hk₀ : Continuous k₀ := Complex.continuous_ofReal.comp hk.continuous
  have hk₀c : HasCompactSupport k₀ := hkc.comp_left Complex.ofReal_zero
  set Ck := ∫ u, ‖k₀ u‖ * Real.exp (1 / 2 * |u|)
  have hkFT : ∀ ρ' : 𝒵, ‖Zeta23.paperFT k₀ (Zeta23.gammaOf ρ')‖ ≤ Ck := fun ρ' => by
    refine RHTower.EvenSector.norm_paperFT_le_of_compact hk₀ hk₀c ?_
    have h1 := abs_re_zeroShift_le ρ'
    rw [← I_mul_gammaOf] at h1
    simpa using h1
  set c' : 𝒵 → ℂ := fun ρ' => packetCoeff f ρ' * Zeta23.paperFT k₀ (Zeta23.gammaOf ρ')
  have hc' : Summable fun ρ' => ‖c' ρ'‖ :=
    (hc.mul_right Ck).of_nonneg_of_le (fun _ => norm_nonneg _) fun ρ' => by
      simp only [c', norm_mul]
      exact mul_le_mul_of_nonneg_left (hkFT ρ') (norm_nonneg _)
  -- rates
  set σ' := (σ + ((ρ : ℂ).re - 1 / 2)) / 2
  have hσσ' : σ < σ' := by simp only [σ']; linarith
  have hσ'ρ : σ' < (zeroShift ρ).re := by simp only [σ', zeroShift]; simp; linarith
  set δ := σ' - σ
  have hδ : 0 < δ := by simp only [δ]; linarith
  set K₃ := k₂ / 2 + |K| * Real.exp (2 * σ * R) * (1 + R + 1 / δ) + 2 * R * CA ^ 2 with hK₃
  set b := max T w + R + 1
  have hb : 0 < b := by have := le_max_right T w; linarith
  -- the pointwise bound on the smoothed zero series
  have hbound : ∀ τ : ℝ, b < τ → ‖zeroSeries c' τ‖ ≤ K₃ * Real.exp (σ' * τ) := by
    intro τ hτ
    have hτT : T ≤ τ - R := by have := le_max_left T w; linarith
    have hτw : w + 1 ≤ τ - R := by have := le_max_right T w; linarith
    have hτ0 : 0 ≤ τ := by linarith
    -- smoothing identity on the window `[−R, R]`
    have hsm := integral_mul_zeroSeries_add hc hk.continuous hkc τ
    have hwin : ∫ s, (k s : ℂ) * G (τ + s) = ∫ s in (-R)..R, (k s : ℂ) * G (τ + s) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
      have : R ≤ |s| := by
        by_contra h
        push Not at h
        exact hs ⟨by linarith [neg_abs_le s, (abs_lt.mp h).1], (abs_lt.mp h).2.le⟩
      rw [hkz s this]; simp
    have hGc : Continuous G := continuous_zeroSeries hc
    have hPG : ∀ s ∈ Icc (-R) R, ‖G (τ + s)‖ ^ 2 ≤ 2 * CA ^ 2 + 2 * stationaryPacket f (τ + s) ^ 2 := by
      intro s hs
      have hP := stationaryPacket_eq hf hfc hw.le hwz (show w < τ + s by linarith [hs.1])
      have hGe : G (τ + s) = A (τ + s) - (stationaryPacket f (τ + s) : ℂ) := by rw [hP]; ring
      have h1 : ‖G (τ + s)‖ ≤ CA + |stationaryPacket f (τ + s)| := by
        rw [hGe]
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith [hA (τ + s)]
      have h3 : ‖G (τ + s)‖ ^ 2 ≤ (CA + |stationaryPacket f (τ + s)|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h4 : (CA + |stationaryPacket f (τ + s)|) ^ 2 ≤
          2 * CA ^ 2 + 2 * |stationaryPacket f (τ + s)| ^ 2 := by
        nlinarith [sq_nonneg (CA - |stationaryPacket f (τ + s)|)]
      rw [sq_abs] at h4
      linarith
    have hamgm : ∀ s, ‖(k s : ℂ) * G (τ + s)‖ ≤
        (Real.exp (σ * τ) * k s ^ 2 + Real.exp (-(σ * τ)) * ‖G (τ + s)‖ ^ 2) / 2 := fun s => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have he : Real.exp (σ * τ) * Real.exp (-(σ * τ)) = 1 := by
        rw [← Real.exp_add]; simp
      have h1 := Real.exp_pos (σ * τ)
      have h2 := Real.exp_pos (-(σ * τ))
      have key : 0 ≤ Real.exp (-(σ * τ)) * (Real.exp (σ * τ) * |k s| - ‖G (τ + s)‖) ^ 2 :=
        mul_nonneg h2.le (sq_nonneg _)
      have hexp : Real.exp (-(σ * τ)) * (Real.exp (σ * τ) * |k s| - ‖G (τ + s)‖) ^ 2 =
          (Real.exp (σ * τ) * Real.exp (-(σ * τ))) * Real.exp (σ * τ) * |k s| ^ 2 -
            2 * (Real.exp (σ * τ) * Real.exp (-(σ * τ))) * (|k s| * ‖G (τ + s)‖) +
              Real.exp (-(σ * τ)) * ‖G (τ + s)‖ ^ 2 := by ring
      rw [hexp, he, sq_abs] at key
      linarith
    -- window energy of `G` from the band
    have hP2c : Continuous fun x => stationaryPacket f x ^ 2 := hPc.pow 2
    have hPband : ∫ s in (-R)..R, stationaryPacket f (τ + s) ^ 2 ≤
        K * (1 + (τ + R)) * Real.exp (2 * σ * (τ + R)) := by
      have hsh := intervalIntegral.integral_comp_add_left (fun x => stationaryPacket f x ^ 2) τ
        (a := -R) (b := R)
      rw [hsh]
      have hmono := intervalIntegral.integral_mono_interval (c := T) (d := τ + R)
        (a := τ + -R) (b := τ + R) (μ := volume) (by linarith) (by linarith) le_rfl
        (Eventually.of_forall fun x => sq_nonneg (stationaryPacket f x))
        (hP2c.intervalIntegrable _ _)
      exact hmono.trans (hband (τ + R) (by linarith))
    have hGwin : ∫ s in (-R)..R, ‖G (τ + s)‖ ^ 2 ≤
        4 * R * CA ^ 2 + 2 * (K * (1 + (τ + R)) * Real.exp (2 * σ * (τ + R))) := by
      have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -R ≤ R)
        (f := fun s => ‖G (τ + s)‖ ^ 2)
        (g := fun s => 2 * CA ^ 2 + 2 * stationaryPacket f (τ + s) ^ 2)
        ((by fun_prop : Continuous fun s => ‖G (τ + s)‖ ^ 2).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s =>
          2 * CA ^ 2 + 2 * stationaryPacket f (τ + s) ^ 2).intervalIntegrable _ _) hPG
      rw [intervalIntegral.integral_add (f := fun _ => 2 * CA ^ 2)
        (g := fun s => 2 * stationaryPacket f (τ + s) ^ 2) intervalIntegrable_const
        ((by fun_prop : Continuous fun s => 2 * stationaryPacket f (τ + s) ^ 2).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at hmono
      have : (R - -R) * (2 * CA ^ 2) = 4 * R * CA ^ 2 := by ring
      linarith
    have hnorm : ‖zeroSeries c' τ‖ ≤ Real.exp (σ * τ) * k₂ / 2 +
        Real.exp (-(σ * τ)) * (4 * R * CA ^ 2 + 2 * (K * (1 + (τ + R)) *
          Real.exp (2 * σ * (τ + R)))) / 2 := by
      rw [← hsm, hwin]
      refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans ?_
      refine (intervalIntegral.integral_mono_on (by linarith)
        (((Complex.continuous_ofReal.comp hk.continuous).mul
          (hGc.comp (continuous_const.add continuous_id))).norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => (Real.exp (σ * τ) * k s ^ 2 +
          Real.exp (-(σ * τ)) * ‖G (τ + s)‖ ^ 2) / 2).intervalIntegrable _ _)
        fun s _ => hamgm s).trans ?_
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (f := fun s => Real.exp (σ * τ) * k s ^ 2)
        (g := fun s => Real.exp (-(σ * τ)) * ‖G (τ + s)‖ ^ 2)
        ((continuous_const.mul (hk.continuous.pow 2)).intervalIntegrable _ _)
        ((by fun_prop : Continuous fun s => Real.exp (-(σ * τ)) * ‖G (τ + s)‖ ^ 2).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have he := (Real.exp_pos (-(σ * τ))).le
      have := mul_le_mul_of_nonneg_left hGwin he
      linarith
    -- collect the exponentials
    have hexp1 : Real.exp (-(σ * τ)) * Real.exp (2 * σ * (τ + R)) =
        Real.exp (σ * τ) * Real.exp (2 * σ * R) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hexp2 : Real.exp (-(σ * τ)) ≤ Real.exp (σ * τ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpoly : 1 + (τ + R) ≤ (1 + R + 1 / δ) * Real.exp (δ * τ) := by
      have h1 : δ * τ + 1 ≤ Real.exp (δ * τ) := Real.add_one_le_exp _
      have h2 : 1 ≤ Real.exp (δ * τ) := Real.one_le_exp (by positivity)
      have h3 : τ ≤ Real.exp (δ * τ) / δ := by
        rw [le_div_iff₀ hδ]; nlinarith
      calc 1 + (τ + R) ≤ (1 + R) * Real.exp (δ * τ) + Real.exp (δ * τ) / δ := by nlinarith
        _ = (1 + R + 1 / δ) * Real.exp (δ * τ) := by field_simp
    have hσ'split : Real.exp (σ' * τ) = Real.exp (σ * τ) * Real.exp (δ * τ) := by
      rw [← Real.exp_add]; congr 1; simp only [δ]; ring
    have hE1 : 1 ≤ Real.exp (δ * τ) := Real.one_le_exp (by positivity)
    have hes := Real.exp_pos (σ * τ)
    have hK : K ≤ |K| := le_abs_self K
    calc ‖zeroSeries c' τ‖ ≤ Real.exp (σ * τ) * k₂ / 2 +
          Real.exp (-(σ * τ)) * (4 * R * CA ^ 2 + 2 * (K * (1 + (τ + R)) *
            Real.exp (2 * σ * (τ + R)))) / 2 := hnorm
      _ = Real.exp (σ * τ) * k₂ / 2 + Real.exp (-(σ * τ)) * (2 * R * CA ^ 2) +
          K * (1 + (τ + R)) * (Real.exp (-(σ * τ)) * Real.exp (2 * σ * (τ + R))) := by ring
      _ ≤ Real.exp (σ * τ) * k₂ / 2 + Real.exp (σ * τ) * (2 * R * CA ^ 2) +
          |K| * ((1 + R + 1 / δ) * Real.exp (δ * τ)) *
            (Real.exp (σ * τ) * Real.exp (2 * σ * R)) := by
          rw [hexp1]
          have hRC : 0 ≤ 2 * R * CA ^ 2 := by positivity
          have h1 : Real.exp (-(σ * τ)) * (2 * R * CA ^ 2) ≤ Real.exp (σ * τ) * (2 * R * CA ^ 2) :=
            mul_le_mul_of_nonneg_right hexp2 hRC
          have h2 : K * (1 + (τ + R)) ≤ |K| * ((1 + R + 1 / δ) * Real.exp (δ * τ)) := by
            have h0 : 0 ≤ 1 + (τ + R) := by linarith
            calc K * (1 + (τ + R)) ≤ |K| * (1 + (τ + R)) := mul_le_mul_of_nonneg_right hK h0
              _ ≤ _ := mul_le_mul_of_nonneg_left hpoly (abs_nonneg K)
          have h3 := mul_le_mul_of_nonneg_right h2 (by positivity :
            (0 : ℝ) ≤ Real.exp (σ * τ) * Real.exp (2 * σ * R))
          linarith
      _ ≤ K₃ * Real.exp (σ' * τ) := by
          rw [hσ'split, hK₃]
          have hk2 : Real.exp (σ * τ) * k₂ / 2 ≤ k₂ / 2 * (Real.exp (σ * τ) * Real.exp (δ * τ)) := by
            have h := mul_le_mul_of_nonneg_left hE1 (by positivity : 0 ≤ k₂ / 2 * Real.exp (σ * τ))
            linarith
          have hRC : Real.exp (σ * τ) * (2 * R * CA ^ 2) ≤
              2 * R * CA ^ 2 * (Real.exp (σ * τ) * Real.exp (δ * τ)) := by
            have h := mul_le_mul_of_nonneg_left hE1
              (by positivity : 0 ≤ 2 * R * CA ^ 2 * Real.exp (σ * τ))
            linarith
          have hKt : |K| * ((1 + R + 1 / δ) * Real.exp (δ * τ)) *
              (Real.exp (σ * τ) * Real.exp (2 * σ * R)) =
                |K| * Real.exp (2 * σ * R) * (1 + R + 1 / δ) *
                  (Real.exp (σ * τ) * Real.exp (δ * τ)) := by ring
          rw [hKt, add_mul, add_mul]
          linarith
  -- the residue law kills the smoothed coefficient
  have hzero := coeff_eq_zero_of_growth hc' hb hbound hσ'ρ
  simp only [c'] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact (packetCoeff_eq_zero_iff f ρ).mp h
  · exact absurd h hkρ

/-- **Packet band law.** For a real compact `C²` source and `σ ≥ 0`, the band of the packet is
`O((1 + L) e^{2σL})` iff `f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem packet_band_iff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ T K : ℝ, ∀ L : ℝ, T ≤ L →
        ∫ τ in T..L, stationaryPacket f τ ^ 2 ≤ K * (1 + L) * Real.exp (2 * σ * L)) ↔
      ∀ ρ : 𝒵, σ < (ρ : ℂ).re - 1 / 2 →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  constructor
  · rintro ⟨T, K, hband⟩ ρ hρ
    exact paperFT_eq_zero_of_packet_band hf hfc hσ hband ρ hρ
  · intro hblind
    obtain ⟨T, K, hK⟩ := (packet_growth_iff hf hfc hσ).mpr hblind
    have hPc := continuous_stationaryPacket hf.continuous hfc
    refine ⟨max T 0, K ^ 2, fun L hL => ?_⟩
    have hT0 : 0 ≤ max T 0 := le_max_right _ _
    have hL0 : 0 ≤ L := hT0.trans hL
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hL
      (f := fun τ => stationaryPacket f τ ^ 2) (g := fun _ => K ^ 2 * Real.exp (2 * σ * L))
      ((hPc.pow 2).intervalIntegrable _ _) intervalIntegrable_const fun τ hτ => by
        have h1 := hK τ ((le_max_left T 0).trans hτ.1)
        have h2 : stationaryPacket f τ ^ 2 ≤ (K * Real.exp (σ * τ)) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have h3 : (K * Real.exp (σ * τ)) ^ 2 ≤ K ^ 2 * Real.exp (2 * σ * L) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg K)
          push_cast
          nlinarith [hτ.2]
        exact h2.trans h3
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    refine hmono.trans ?_
    have hLT : L - max T 0 ≤ 1 + L := by linarith
    have hE := Real.exp_pos (2 * σ * L)
    nlinarith [sq_nonneg K, mul_le_mul_of_nonneg_right hLT
      (mul_nonneg (sq_nonneg K) hE.le)]

/-- **One packet's band decides RH.** For a universal probe `U`, RH holds iff the band of the
single packet `P_U` is linear. -/
theorem riemannHypothesis_iff_packet_band_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ L : ℝ, T ≤ L →
      ∫ τ in T..L, stationaryPacket U τ ^ 2 ≤ K * (1 + L) := by
  have h := packet_band_iff hU hUc le_rfl
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one, sub_pos] at h
  rw [h]
  constructor
  · intro hRH ρ hρ
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  · intro hblind
    by_contra hRH
    obtain ⟨ρ, hρ⟩ := exists_mem_re_gt_of_not_riemannHypothesis hRH
    exact hsees ρ (hblind ρ hρ)

/-- **The zero width is half the band rate of one packet.** For a universal probe `U` and
`β ≥ 0`, every zero has `Re ρ ≤ 1/2 + β` iff `∫_T^L P_U² = O((1 + L) e^{2βL})`. -/
theorem xiZeroHalfPlaneBound_iff_packet_band_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∃ T K : ℝ, ∀ L : ℝ, T ≤ L →
      ∫ τ in T..L, stationaryPacket U τ ^ 2 ≤ K * (1 + L) * Real.exp (2 * β * L) := by
  rw [xiZeroHalfPlaneBound_iff_forall_mem hβ, packet_band_iff hU hUc hβ]
  constructor
  · intro h ρ hρ
    have := h ρ
    linarith
  · intro h ρ
    by_contra hlt
    push Not at hlt
    exact hsees ρ (h ρ (by linarith))

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
