import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.BiScaleUncertainty.TranslatedPairingEnvelopeLaw
import GaloisForLFunctions.BiScaleUncertainty.SimpleZeroPacketCriterion

/-!
# Effective finite-prime translated pairings and the multiplicity defect

This module resolves two open questions in the packet and multiplicity theory of
`BiScaleUncertainty`:

1. **Effective finite-prime truncation and every-shift envelope of translated pairings**
   (`autocorr_eq_zero_of_two_mul_lt_abs`, `stationaryPacket_eq_finite_prime_polar`,
   `stationaryPacket_eq_pairing_of_cutoff_ge`, `zeroSeries_autocorr_eq_criticalSeries_of_blind`,
   `stationaryPacket_autocorr_eq_archTail_sub_criticalSeries`,
   `abs_stationaryPacket_autocorr_le_of_blind`, `abs_translatedPairing_le_levy_of_oneSided`,
   `stationaryPacket_autocorr_eq_local_gauge`):
   For a real `C²_c` source `f` vanishing outside `[−w, w]`, its autocorrelation `h_f = autocorr f`
   vanishes outside `[−2w, 2w]`. For every shift `τ > 2w`:
   * the translated pairing `P_{h_f}(τ) = ⟨h_f(· − τ), ν⟩` is an exact finite prime sum over
     `1 ≤ n ≤ ⌊e^{τ + 2w}⌋` minus the finite window polar integral on `[τ − 2w, τ + 2w]`, and
     coincides with the finite-cutoff pairing `SignedPrimePolar.pairing N (fun x => h_f (x − τ))`
     as soon as `cutoff N > τ + 2w`;
   * whenever `h_f` is blind right of the critical line (in particular whenever `P_f` or `P_{h_f}`
     is bounded on one side, or under RH), reflection symmetry `ĥ_f(γ_ρ) = conj ĥ_f(γ_{1−ρ̄})`
     kills every off-critical zero coefficient on *both* sides of the line, so the off-critical
     zero series of `h_f` vanishes identically on all of `ℝ` and the envelope bound holds at
     **every** shift `τ > 2w` without any unknown threshold `T`:
     `|⟨h_f(· − τ), ν⟩| ≤ W(f) + ‖A_{h_f}(τ)‖ ≤ W(f) + (1 / 2π) ∫ |f̂(r)|² |Ω(r)| dr`;
   * unconditionally (without any one-sided hypothesis), `⟨h_f(· − τ), ν⟩` is given by the local
     Chebyshev gauge integral on `[τ − 2w, τ + 2w]`.

2. **The critical multiplicity defect, explicit `splineProbe` spectral lower bounds, and
   certified finite-prime simplicity testing**
   (`multiplicityDefect`, `multiplicityDefect_eq_tsum`, `two_mul_le_multiplicityDefect`,
   `four_mul_norm_sq_le_multiplicityDefect_of_mult_ne_one`, `le_norm_paperFT_unif`,
   `le_norm_paperFT_upow`, `le_norm_paperFT_splineProbe_ofReal`,
   `splineProbe_multiplicityDefect_lower_bound_of_criticalZero`,
   `forall_critical_simple_up_to_height_of_multiplicityDefect_lt`,
   `finitePrimeMultiplicityDefect`, `tendsto_finitePrimeMultiplicityDefect_of_packet_bddAbove`,
   `riemannHypothesis_and_simple_iff_finitePrimeMultiplicityDefect_of_universal`):
   The multiplicity defect `Δ_mult(f) = E(f) − W(f) = Σ_{Re ρ = 1/2} m_ρ(m_ρ − 1)|f̂(γ_ρ)|² ≥ 0`
   satisfies the conjugate-pair lower bound `2 m_{ρ₀}(m_{ρ₀} − 1)|f̂(γ_{ρ₀})|² ≤ Δ_mult(f)` at
   every critical zero `ρ₀`, hence `4|f̂(γ_{ρ₀})|² ≤ Δ_mult(f)` at any non-simple critical zero.
   For `splineProbe`, the real-line transform satisfies the explicit two-sided sandwich
   `(sinh 1)⁴ / (1 + r²)² ≤ ‖Û(r)‖ ≤ (cosh 1)⁴ / (1 + r²)²`, so any non-simple critical zero of
   ordinate `|γ₀| ≤ Γ` forces `Δ_mult(splineProbe) ≥ 4 (sinh 1)⁸ / (1 + Γ²)⁴`. In terms of finite
   primes, `Δ_mult(g)` is the `N → ∞` limit of the purely finite-prime observable
   `finitePrimeMultiplicityDefect g w N`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators Convolution CompactlySupported ComplexConjugate
open RHTower.WeilDeletion (unif upow integrable_unif integrable_upow hasCompactSupport_upow
  paperFT_unif paperFT_upow norm_paperFT_unif_le norm_paperFT_upow_le)

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## §1. Support localization of autocorrelations and finite-prime truncation of packets -/

/-- If `f` vanishes outside `[−w, w]`, then its autocorrelation `autocorr f` vanishes outside
`[−2w, 2w]`. -/
theorem autocorr_eq_zero_of_two_mul_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : 2 * w < |v|) :
    autocorr f v = 0 := by
  unfold autocorr
  have hzero : (fun u : ℝ => f u * f (u + v)) = fun _ => 0 := by
    funext u
    by_cases hu : w < |u|
    · rw [hw u hu, zero_mul]
    · push Not at hu
      have htri : |v| ≤ |u + v| + |u| := by
        calc |v| = |(u + v) - u| := by ring_nf
          _ ≤ |u + v| + |u| := abs_sub (u + v) u
      have huv : w < |u + v| := by linarith
      rw [hw (u + v) huv, mul_zero]
  rw [hzero, integral_zero]

/-- If `f` vanishes outside `[−w, w]`, then `gaugeDerivative (autocorr f)` vanishes outside
`[−2w, 2w]`. -/
theorem gaugeDerivative_autocorr_eq_zero_of_two_mul_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : 2 * w < |v|) :
    gaugeDerivative (autocorr f) v = 0 :=
  gaugeDerivative_eq_zero_of_lt_abs (fun _ h => autocorr_eq_zero_of_two_mul_lt_abs hw h) hv

/-- **Exact finite-prime truncation of the packet prime sum.** If `H` vanishes outside `[−R, R]`
(`R ≥ 0`), then for every shift `τ ∈ ℝ` the prime series in `stationaryPacket H τ` equals the
finite sum over `1 ≤ n ≤ ⌊e^{τ + R}⌋`. -/
theorem tsum_vonMangoldt_mul_eq_sum_Icc_of_support {H : ℝ → ℝ} {R : ℝ}
    (hH : ∀ v : ℝ, R < |v| → H v = 0) (τ : ℝ) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * H (Real.log n - τ)) =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (τ + R)⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * H (Real.log n - τ) := by
  refine tsum_eq_sum fun n hn => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn0 | hn_gt
  · have : n = 0 := by omega
    subst this
    simp
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hexp : Real.exp (τ + R) < (n : ℝ) := (Nat.floor_lt' hpos.ne').mp hn_gt
      have hlog : τ + R < Real.log (n : ℝ) :=
        (Real.lt_log_iff_exp_lt (by exact_mod_cast hpos)).mpr hexp
      have hR : R < |Real.log (n : ℝ) - τ| := lt_abs.mpr (Or.inl (by linarith))
      rw [hH _ hR, mul_zero]

/-- **Exact finite-window truncation of the packet polar integral.** If `H` vanishes outside
`[−R, R]` and `R < τ`, then the half-line polar integral in `stationaryPacket H τ` equals the
finite window integral on `[τ − R, τ + R]`. -/
theorem integral_Ioi_polar_eq_setIntegral_Icc_of_support {H : ℝ → ℝ} {R : ℝ}
    (hH : ∀ v : ℝ, R < |v| → H v = 0) {τ : ℝ} (hτ : R < τ) :
    (∫ x in Ioi (0 : ℝ), 2 * Real.cosh (x / 2) * H (x - τ)) =
      ∫ x in Icc (τ - R) (τ + R), 2 * Real.cosh (x / 2) * H (x - τ) := by
  have hsub : Icc (τ - R) (τ + R) ⊆ Ioi (0 : ℝ) := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub fun x hx => ?_
  have hx2 := hx.2
  simp only [mem_Icc, not_and_or, not_le] at hx2
  have hR : R < |x - τ| := by
    rcases hx2 with hlt | hgt
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl (by linarith))
  rw [hH _ hR, mul_zero]

/-- **Exact finite-prime and finite-window formula for `stationaryPacket`.** For any `H` vanishing
outside `[−R, R]` and any shift `τ > R`,
`P_H(τ) = Σ_{1 ≤ n ≤ ⌊e^{τ+R}⌋} Λ(n) n^{-1/2} H(log n − τ) − ∫_{τ−R}^{τ+R} 2 cosh(x/2) H(x − τ) dx`. -/
theorem stationaryPacket_eq_finite_prime_polar {H : ℝ → ℝ} {R : ℝ}
    (hH : ∀ v : ℝ, R < |v| → H v = 0) {τ : ℝ} (hτ : R < τ) :
    stationaryPacket H τ =
      (∑ n ∈ Finset.Icc 1 ⌊Real.exp (τ + R)⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * H (Real.log n - τ)) -
        ∫ x in Icc (τ - R) (τ + R), 2 * Real.cosh (x / 2) * H (x - τ) := by
  unfold stationaryPacket
  rw [tsum_vonMangoldt_mul_eq_sum_Icc_of_support hH τ,
    integral_Ioi_polar_eq_setIntegral_Icc_of_support hH hτ]

/-- **Exact agreement of `stationaryPacket` and the finite-cutoff `SignedPrimePolar.pairing`.**
If `H` vanishes outside `[−R, R]` and `τ + R < cutoff N`, then `stationaryPacket H τ` (the
untruncated translated pairing `fullPairing (fun x => H (x − τ))`) equals the finite-cutoff
pairing `SignedPrimePolar.pairing N (fun x => H (x − τ))`. -/
theorem stationaryPacket_eq_pairing_of_cutoff_gt {H : ℝ → ℝ} {R : ℝ}
    (hH : ∀ v : ℝ, R < |v| → H v = 0) {τ : ℝ} {N : ℕ} (hN : τ + R < cutoff N) :
    stationaryPacket H τ = SignedPrimePolar.pairing N (fun x => H (x - τ)) := by
  rw [stationaryPacket_eq_fullPairing]
  refine SignedPrimePolar.fullPairing_eq_pairing_of_tail (fun x => H (x - τ)) N fun x hx => ?_
  exact hH (x - τ) (lt_abs.mpr (Or.inl (by linarith)))

/-- For every `τ ∈ ℝ`, `splinePrimeSum τ` is the finite sum over `1 ≤ n ≤ ⌊e^{τ + 4}⌋`. -/
theorem splinePrimeSum_eq_sum_Icc (τ : ℝ) :
    splinePrimeSum τ =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (τ + 4)⌋₊,
        ArithmeticFunction.vonMangoldt n * Real.sqrt n * cubicSpline (Real.log n - τ) := by
  unfold splinePrimeSum
  refine tsum_eq_sum fun n hn => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn0 | hn_gt
  · have : n = 0 := by omega
    subst this
    simp
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hexp : Real.exp (τ + 4) < (n : ℝ) := (Nat.floor_lt' hpos.ne').mp hn_gt
      have hlog : τ + 4 < Real.log (n : ℝ) :=
        (Real.lt_log_iff_exp_lt (by exact_mod_cast hpos)).mpr hexp
      have h4 : 4 < |Real.log (n : ℝ) - τ| := lt_abs.mpr (Or.inl (by linarith))
      rw [cubicSpline_eq_zero h4, mul_zero]

/-- For every `τ > 4`, `splinePolarMass τ` is the finite window integral on `[τ − 4, τ + 4]`. -/
theorem splinePolarMass_eq_setIntegral_Icc {τ : ℝ} (hτ : 4 < τ) :
    splinePolarMass τ =
      ∫ x in Icc (τ - 4) (τ + 4), 2 * Real.cosh (x / 2) * Real.exp x * cubicSpline (x - τ) := by
  unfold splinePolarMass
  have hsub : Icc (τ - 4) (τ + 4) ⊆ Ioi (0 : ℝ) := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub fun x hx => ?_
  have hx2 := hx.2
  simp only [mem_Icc, not_and_or, not_le] at hx2
  have h4 : 4 < |x - τ| := by
    rcases hx2 with hlt | hgt
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl (by linarith))
  rw [cubicSpline_eq_zero h4, mul_zero]

/-! ## §2. Two-sided off-critical blindness of autocorrelations and every-shift envelope bounds -/

/-- **Two-sided off-critical blindness of an autocorrelation.** Because
`ĥ_f(z) = f̂(z) conj f̂(conj z)` and `conj γ_ρ = γ_{1−ρ̄}`, an autocorrelation `h_f` that is blind
to zeros right of the critical line (`Re ρ > 1/2`) is also blind to zeros left of the critical
line (`Re ρ < 1/2`), hence vanishes at **every** off-critical zero `ρ ∉ criticalZeros`. -/
theorem paperFT_autocorr_eq_zero_of_notMem_criticalZeros {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0)
    {ρ : 𝒵} (hρ : ρ ∉ criticalZeros) :
    Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  have hne : (ρ : ℂ).re ≠ 1 / 2 := hρ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : Zeta23.reflect ρ ∈ 𝒵 := Zeta23.zetaZeroConfig.reflect_mem ρ ρ.2
    have hre : 1 / 2 < (Zeta23.reflect ρ).re := by
      simp only [Zeta23.reflect, sub_re, one_re, conj_re]; linarith
    have h0 := hblind ⟨_, hmem⟩ hre
    rw [paperFT_autocorr hf hfc, conj_gammaOf, reflect_reflect] at h0
    rw [paperFT_autocorr hf hfc, conj_gammaOf]
    rcases mul_eq_zero.mp h0 with h | h
    · rw [h, map_zero, mul_zero]
    · rw [map_eq_zero] at h
      rw [h, zero_mul]
  · exact hblind ρ hgt

/-- Every off-critical zero coefficient `packetCoeff (autocorr f) ρ` vanishes when `autocorr f` is
blind right of the line. -/
theorem packetCoeff_autocorr_eq_zero_of_notMem_criticalZeros {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0)
    {ρ : 𝒵} (hρ : ρ ∉ criticalZeros) :
    packetCoeff (autocorr f) ρ = 0 :=
  (packetCoeff_eq_zero_iff (autocorr f) ρ).mpr
    (paperFT_autocorr_eq_zero_of_notMem_criticalZeros hf hfc hblind hρ)

/-- **Exact critical-only zero series for a blind autocorrelation.** When `autocorr f` is blind
right of the line, its full zero series equals its critical almost-periodic series identically at
**every** shift `τ ∈ ℝ` (with zero off-critical tail). -/
theorem zeroSeries_autocorr_eq_criticalSeries_of_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0)
    (τ : ℝ) :
    zeroSeries (packetCoeff (autocorr f)) τ = criticalSeries (autocorr f) τ := by
  set h := autocorr f
  have hh := contDiff_autocorr hf hfc
  have hhc := hasCompactSupport_autocorr hfc
  have hc := summable_norm_packetCoeff hh hhc
  have hS : Summable fun ρ : 𝒵 => packetCoeff h ρ * cexp (zeroShift ρ * τ) :=
    Summable.of_norm_bounded (hc.mul_right (Real.exp (|τ| / 2))) fun ρ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_exp_zeroShift_mul_le ρ τ) (norm_nonneg _)
  rw [zeroSeries, ← Summable.tsum_add_tsum_compl (s := criticalZeros) (hS.subtype _)
    (hS.subtype _)]
  have hcompl : (∑' ρ : ↥(criticalZerosᶜ : Set 𝒵),
      packetCoeff h ρ * cexp (zeroShift (ρ : 𝒵) * τ)) = 0 := by
    refine (tsum_congr fun ρ => ?_).trans tsum_zero
    rw [packetCoeff_autocorr_eq_zero_of_notMem_criticalZeros hf.continuous hfc hblind ρ.2,
      zero_mul]
  rw [hcompl, add_zero, criticalSeries]
  refine tsum_congr fun ρ => ?_
  rw [zeroShift_of_mem_critical ρ.2]
  push_cast
  ring_nf

/-- **Exact every-shift explicit formula for the translated pairing of a blind autocorrelation.**
If `f ∈ C²_c(ℝ)` vanishes outside `[−w, w]` (`w ≥ 0`) and `autocorr f` is blind right of the line,
then for **every shift `τ > 2w`** right above the support radius `2w` of `autocorr f`,
`(P_{h_f}(τ) : ℂ) = packetArchTail h_f τ − criticalSeries h_f τ`. -/
theorem stationaryPacket_autocorr_eq_archTail_sub_criticalSeries {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0)
    {τ : ℝ} (hτ : 2 * w < τ) :
    (stationaryPacket (autocorr f) τ : ℂ) =
      packetArchTail (autocorr f) τ - criticalSeries (autocorr f) τ := by
  have hh := contDiff_autocorr hf hfc
  have hhc := hasCompactSupport_autocorr hfc
  rw [stationaryPacket_eq hh hhc (by linarith : 0 ≤ 2 * w)
    (fun _ hv => autocorr_eq_zero_of_two_mul_lt_abs hw hv) hτ,
    zeroSeries_autocorr_eq_criticalSeries_of_blind hf hfc hblind τ]

/-- On the real axis, `ĥ_f(r) = ‖f̂(r)‖²`. -/
theorem paperFT_autocorr_ofReal {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (r : ℝ) :
    Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (r : ℂ) =
      ((‖Zeta23.paperFT (fun u => (f u : ℂ)) (r : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [paperFT_autocorr hf hfc (r : ℂ), Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- For every critical zero `ρ ∈ criticalZeros`, `‖packetCoeff (autocorr f) ρ‖ = m_ρ ‖f̂(γ_ρ)‖²`,
so `∑' ρ : criticalZeros, ‖packetCoeff (autocorr f) ρ‖ = criticalWeilEnergy f`. -/
theorem tsum_norm_packetCoeff_autocorr_critical_eq {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (∑' ρ : criticalZeros, ‖packetCoeff (autocorr f) ρ‖) = criticalWeilEnergy f := by
  unfold criticalWeilEnergy
  refine tsum_congr fun ρ => ?_
  simp only [packetCoeff, gammaOf_of_mem_critical ρ.2, paperFT_autocorr_ofReal hf hfc]
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- For every `τ ∈ ℝ`, `‖criticalSeries (autocorr f) τ‖ ≤ criticalWeilEnergy f`. -/
theorem norm_criticalSeries_autocorr_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    ‖criticalSeries (autocorr f) τ‖ ≤ criticalWeilEnergy f := by
  rw [← tsum_norm_packetCoeff_autocorr_critical_eq hf.continuous hfc]
  exact norm_criticalSeries_le (contDiff_autocorr hf hfc) (hasCompactSupport_autocorr hfc) τ

/-- For every `τ ∈ ℝ`,
`‖packetArchTail (autocorr f) τ‖ ≤ (1 / 2π) ∫ r, ‖f̂(r)‖² |Ω(r)|`. -/
theorem norm_packetArchTail_autocorr_le {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    ‖packetArchTail (autocorr f) τ‖ ≤
      1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r‖ ^ 2 * |Zeta23.EF.gammaBracket r| := by
  refine (norm_packetArchTail_le (autocorr f) τ).trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [norm_mul, paperFT_autocorr_ofReal hf hfc r, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs]

/-- **Effective every-shift envelope bound for a blind autocorrelation.** If `f ∈ C²_c(ℝ)` vanishes
outside `[−w, w]` and `autocorr f` is blind right of the line, then for **every shift `τ > 2w`**
(with no unknown threshold `T`),
`|P_{h_f}(τ)| ≤ criticalWeilEnergy f + ‖packetArchTail (autocorr f) τ‖`
`≤ criticalWeilEnergy f + (1 / 2π) ∫ r, ‖f̂(r)‖² |Ω(r)|`. -/
theorem abs_stationaryPacket_autocorr_le_of_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0)
    {τ : ℝ} (hτ : 2 * w < τ) :
    |stationaryPacket (autocorr f) τ| ≤
        criticalWeilEnergy f + ‖packetArchTail (autocorr f) τ‖ ∧
      |stationaryPacket (autocorr f) τ| ≤
        criticalWeilEnergy f +
          1 / (2 * Real.pi) *
            ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r‖ ^ 2 *
              |Zeta23.EF.gammaBracket r| := by
  have h1 : |stationaryPacket (autocorr f) τ| ≤
      criticalWeilEnergy f + ‖packetArchTail (autocorr f) τ‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real,
      stationaryPacket_autocorr_eq_archTail_sub_criticalSeries hf hfc hw0 hw hblind hτ]
    calc ‖packetArchTail (autocorr f) τ - criticalSeries (autocorr f) τ‖
        ≤ ‖packetArchTail (autocorr f) τ‖ + ‖criticalSeries (autocorr f) τ‖ := norm_sub_le _ _
      _ ≤ ‖packetArchTail (autocorr f) τ‖ + criticalWeilEnergy f :=
          add_le_add le_rfl (norm_criticalSeries_autocorr_le hf hfc τ)
      _ = criticalWeilEnergy f + ‖packetArchTail (autocorr f) τ‖ := add_comm _ _
  exact ⟨h1, h1.trans (add_le_add le_rfl (norm_packetArchTail_autocorr_le hf.continuous hfc τ))⟩

/-- **Effective every-shift envelope bound in bi-scale coordinates.** For a real Weil test `g`
vanishing outside `[−w, w]` whose packet is eventually bounded above (in particular under RH), for
**every shift `τ > 2w`**,
`|⟨h_g(· − τ), ν⟩| ≤ Ω(0) h_g(0) + 𝒥(g) − 2⟨h_g, ν⟩ + (1 / 2π) ∫ r, ‖ĝ(r)‖² |Ω(r)|`. -/
theorem abs_translatedPairing_le_levy_of_packet_bddAbove (g : RealWeilTestFn) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K)
    {τ : ℝ} (hτ : 2 * w < τ) :
    |SignedPrimePolar.fullPairing (fun x => autocorr g.source (x - τ))| ≤
      Zeta23.EF.gammaBracket 0 * autocorr g.source 0 + biScaleLevyEnergy g.source -
        2 * SignedPrimePolar.pairing g.supportScale (autocorr g.source) +
        1 / (2 * Real.pi) *
          ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (g.source u : ℂ)) r‖ ^ 2 *
            |Zeta23.EF.gammaBracket r| := by
  rw [← stationaryPacket_eq_fullPairing, levyWeilEnergy_eq_criticalWeilEnergy g hw0 hw hup]
  have hup_iff := packet_upper_iff g.contDiff_source g.hasCompactSupport_source le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr g.source u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => by
      rw [paperFT_autocorr g.contDiff_source.continuous g.hasCompactSupport_source,
        hup_iff.mp hup ρ (by linarith), zero_mul]
  exact (abs_stationaryPacket_autocorr_le_of_blind g.contDiff_source g.hasCompactSupport_source
    hw0 hw hblind hτ).2

/-- For `splineProbe`, the archimedean tail of its autocorrelation `autocorr splineProbe` is
uniformly bounded by `(cosh 1)⁴ * splineArchBound` at every shift `τ ∈ ℝ`. -/
theorem norm_packetArchTail_autocorr_splineProbe_le (τ : ℝ) :
    ‖packetArchTail (autocorr splineProbe) τ‖ ≤ Real.cosh 1 ^ 4 * splineArchBound := by
  have hpt : ∀ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ ^ 2 *
      |Zeta23.EF.gammaBracket r| ≤
      Real.cosh 1 ^ 4 *
        ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)‖ := by
    intro r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (abs_nonneg _))
    calc ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖
        ≤ Real.cosh 1 ^ 4 / (1 + r ^ 2) ^ 2 := norm_paperFT_splineProbe_ofReal_le r
      _ ≤ Real.cosh 1 ^ 4 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos (by nlinarith [sq_nonneg r])
      _ = Real.cosh 1 ^ 4 := div_one _
  have hint1 : Integrable fun r : ℝ =>
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)‖ :=
    (integrable_paperFT_mul_gammaBracket contDiff_splineProbe
      fun _ hv => splineProbe_eq_zero hv).norm
  have hint0 : Integrable fun r : ℝ =>
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ ^ 2 * |Zeta23.EF.gammaBracket r| := by
    have h := (integrable_paperFT_mul_gammaBracket
      (contDiff_autocorr contDiff_splineProbe hasCompactSupport_splineProbe)
      fun _ hv => autocorr_eq_zero_of_two_mul_lt_abs (fun _ h => splineProbe_eq_zero h) hv).norm
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [norm_mul, paperFT_autocorr_ofReal contDiff_splineProbe.continuous
      hasCompactSupport_splineProbe r, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs]
  calc ‖packetArchTail (autocorr splineProbe) τ‖
      ≤ 1 / (2 * Real.pi) *
          ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ ^ 2 *
            |Zeta23.EF.gammaBracket r| :=
        norm_packetArchTail_autocorr_le contDiff_splineProbe.continuous
          hasCompactSupport_splineProbe τ
    _ ≤ 1 / (2 * Real.pi) *
          ∫ r : ℝ, Real.cosh 1 ^ 4 *
            ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
              (Zeta23.EF.gammaBracket r : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (integral_mono hint0 (hint1.const_mul _) hpt) (by positivity)
    _ = Real.cosh 1 ^ 4 *
          (1 / (2 * Real.pi) *
            ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
              (Zeta23.EF.gammaBracket r : ℂ)‖) := by
        rw [integral_const_mul, mul_left_comm]
    _ ≤ Real.cosh 1 ^ 4 * splineArchBound := by
        -- reuse the integral bound from `SplineProbeFiniteShiftBounds`
        set c₀ := _root_.RHTower.digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi
        have hpt2 : ∀ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
            (Zeta23.EF.gammaBracket r : ℂ)‖ ≤
            Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ := by
          intro r
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hU := norm_paperFT_splineProbe_ofReal_le r
          have hγ := _root_.RHTower.WeilSpectral.abs_gammaBracket_le_sqrt r
          have hsqrt : Real.sqrt (1 + |r|) ≤ 1 + |r| :=
            Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [abs_nonneg r]⟩
          have habs : 1 + |r| ≤ 3 / 2 * (1 + r ^ 2) := by
            nlinarith [sq_abs r, sq_nonneg (|r| - 1)]
          have hγ' : |Zeta23.EF.gammaBracket r| ≤ (|c₀| + 3) * (1 + r ^ 2) := by
            have hc₀ : c₀ ≤ |c₀| * (1 + r ^ 2) :=
              (le_abs_self c₀).trans
                (le_mul_of_one_le_right (abs_nonneg c₀) (by nlinarith [sq_nonneg r]))
            linarith
          calc ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ * |Zeta23.EF.gammaBracket r|
              ≤ (Real.cosh 1 ^ 4 / (1 + r ^ 2) ^ 2) * ((|c₀| + 3) * (1 + r ^ 2)) :=
                mul_le_mul hU hγ' (abs_nonneg _) (by positivity)
            _ = Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ := by field_simp
        have hint_le : (∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
            (Zeta23.EF.gammaBracket r : ℂ)‖) ≤
            Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi := by
          calc (∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
                (Zeta23.EF.gammaBracket r : ℂ)‖)
              ≤ ∫ r : ℝ, Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ :=
                integral_mono hint1 (integrable_inv_one_add_sq.const_mul _) hpt2
            _ = Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi := by
                rw [integral_const_mul, integral_univ_inv_one_add_sq]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
              (Zeta23.EF.gammaBracket r : ℂ)‖
            ≤ 1 / (2 * Real.pi) * (Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi) :=
              mul_le_mul_of_nonneg_left hint_le (by positivity)
          _ = splineArchBound := by
              dsimp only [splineArchBound, c₀]
              have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
              field_simp

/-- **Effective every-shift envelope bound for `autocorr splineProbe` under RH.** For every shift
`τ > 8` right above the support radius `8` of `autocorr splineProbe`,
`|⟨h_U(· − τ), ν⟩| ≤ criticalWeilEnergy splineProbe + (cosh 1)⁴ * splineArchBound`. -/
theorem abs_stationaryPacket_autocorr_splineProbe_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {τ : ℝ} (hτ : 8 < τ) :
    |stationaryPacket (autocorr splineProbe) τ| ≤
      criticalWeilEnergy splineProbe + Real.cosh 1 ^ 4 * splineArchBound := by
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr splineProbe u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => by
      rw [re_eq_half_of_mem hRH ρ] at hρ
      exact absurd hρ (lt_irrefl _)
  have h1 := (abs_stationaryPacket_autocorr_le_of_blind contDiff_splineProbe
    hasCompactSupport_splineProbe (by norm_num : (0 : ℝ) ≤ 4)
    (fun _ hv => splineProbe_eq_zero hv) hblind (by linarith : 2 * (4 : ℝ) < τ)).1
  exact h1.trans (add_le_add le_rfl (norm_packetArchTail_autocorr_splineProbe_le τ))

/-- **Unconditional local Chebyshev gauge representation of a translated pairing.** For every
`f ∈ C²_c(ℝ)` vanishing outside `[−w, w]` (`w ≥ 0`) and every shift `τ > 2w`,
`⟨h_f(· − τ), ν⟩ = P_{h_f}(τ)` depends only on `Ẽ(t)` in the local window `[τ − 2w, τ + 2w]`. -/
theorem stationaryPacket_autocorr_eq_local_gauge {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : 2 * w < τ) :
    stationaryPacket (autocorr f) τ =
      -(∫ t in Icc (τ - 2 * w) (τ + 2 * w), Real.exp (-t / 2) * autocorr f (-τ + t)) -
        ∫ t in Icc (τ - 2 * w) (τ + 2 * w),
          normalizedLogError t * gaugeDerivative (autocorr f) (-τ + t) := by
  let H : C_c(ℝ, ℝ) :=
    ⟨⟨autocorr f, (contDiff_autocorr hf hfc).continuous⟩, hasCompactSupport_autocorr hfc⟩
  have hH1 : ContDiff ℝ 1 (H : ℝ → ℝ) := (contDiff_autocorr hf hfc).of_le (by norm_num)
  obtain ⟨N, hN1, -⟩ := exists_cutoff_between (a := τ + 2 * w) (by linarith)
  have hgauge : stationaryPacket (autocorr f) τ =
      forwardResidual (autocorr f) N (-τ) - chebyshevGaugeConvolution (autocorr f) N (-τ) :=
    stationaryPacket_eq_gauge H hH1 (by linarith : 0 ≤ 2 * w)
      (fun _ hv => autocorr_eq_zero_of_two_mul_lt_abs hw hv) hN1
  rw [hgauge]
  have hsub : Icc (τ - 2 * w) (τ + 2 * w) ⊆ Icc 0 (cutoff N) :=
    Icc_subset_Icc (by linarith) hN1.le
  have hres : forwardResidual (autocorr f) N (-τ) =
      -∫ t in Icc (τ - 2 * w) (τ + 2 * w), Real.exp (-t / 2) * autocorr f (-τ + t) := by
    unfold forwardResidual
    rw [autocorr_eq_zero_of_two_mul_lt_abs hw (lt_abs.mpr (Or.inr (by linarith))), zero_sub]
    congr 1
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => ?_
    have ht2 := ht.2
    simp only [mem_Icc, not_and_or, not_le] at ht2
    have h2w : 2 * w < |-τ + t| := by
      rcases ht2 with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    rw [autocorr_eq_zero_of_two_mul_lt_abs hw h2w, mul_zero]
  have hconv : chebyshevGaugeConvolution (autocorr f) N (-τ) =
      ∫ t in Icc (τ - 2 * w) (τ + 2 * w),
        normalizedLogError t * gaugeDerivative (autocorr f) (-τ + t) := by
    unfold chebyshevGaugeConvolution
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => ?_
    have ht2 := ht.2
    simp only [mem_Icc, not_and_or, not_le] at ht2
    have h2w : 2 * w < |-τ + t| := by
      rcases ht2 with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    rw [gaugeDerivative_autocorr_eq_zero_of_two_mul_lt_abs hw h2w, mul_zero]
  rw [hres, hconv]

/-! ## §3. The critical multiplicity defect and quantitative conjugate-pair lower bounds -/

/-- **The critical multiplicity defect** `Δ_mult(f) = E(f) − W(f)` of a source `f`. -/
def multiplicityDefect (f : ℝ → ℝ) : ℝ :=
  criticalPacketEnergy f - criticalWeilEnergy f

/-- Series representation: `Δ_mult(f) = Σ_{Re ρ = 1/2} m_ρ (m_ρ − 1) ‖f̂(γ_ρ)‖²`. -/
theorem multiplicityDefect_eq_tsum {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    multiplicityDefect f =
      ∑' ρ : criticalZeros,
        (Zeta23.zetaZeroConfig.mult ρ : ℝ) * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) - 1) *
          ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 := by
  set x : criticalZeros → ℝ := fun ρ =>
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ)‖ ^ 2
  set m : criticalZeros → ℝ := fun ρ => (Zeta23.zetaZeroConfig.mult ρ : ℝ)
  have hm1 : ∀ ρ, 1 ≤ m ρ := fun ρ => by
    simp only [m]; exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
  have hx0 : ∀ ρ, 0 ≤ x ρ := fun ρ => by positivity
  have hE : Summable fun ρ => m ρ ^ 2 * x ρ := summable_criticalPacketEnergy hf hfc
  have hW : Summable fun ρ => m ρ * x ρ :=
    hE.of_nonneg_of_le (fun ρ => mul_nonneg (by linarith [hm1 ρ]) (hx0 ρ)) fun ρ =>
      mul_le_mul_of_nonneg_right (by nlinarith [hm1 ρ]) (hx0 ρ)
  unfold multiplicityDefect criticalPacketEnergy criticalWeilEnergy
  rw [← hE.tsum_sub hW]
  refine tsum_congr fun ρ => ?_
  ring

theorem summable_multiplicityDefect {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Summable fun ρ : criticalZeros =>
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) - 1) *
        ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 := by
  have hE := summable_criticalPacketEnergy hf hfc
  refine hE.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
  · have hm1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := by
      exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  · have hm1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := by
      exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith

/-- `0 ≤ multiplicityDefect f` for every `f ∈ C²_c(ℝ)`. -/
theorem multiplicityDefect_nonneg {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ multiplicityDefect f :=
  sub_nonneg.mpr (criticalWeilEnergy_le_criticalPacketEnergy hf hfc).1

/-- `multiplicityDefect f = 0` iff every critical zero seen by `f` is simple. -/
theorem multiplicityDefect_eq_zero_iff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    multiplicityDefect f = 0 ↔
      ∀ ρ : criticalZeros,
        Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : 𝒵) : ℂ).im : ℂ) ≠ 0 →
          Zeta23.zetaZeroConfig.mult ρ = 1 := by
  rw [multiplicityDefect, sub_eq_zero, eq_comm]
  exact (criticalWeilEnergy_le_criticalPacketEnergy hf hfc).2

/-- For a universal probe `U`, `multiplicityDefect U = 0` iff every critical zero is simple. -/
theorem multiplicityDefect_eq_zero_iff_of_universal {U : ℝ → ℝ} (hU : ContDiff ℝ 2 U)
    (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    multiplicityDefect U = 0 ↔
      ∀ ρ : criticalZeros, Zeta23.zetaZeroConfig.mult ((ρ : 𝒵) : ℂ) = 1 := by
  rw [multiplicityDefect, sub_eq_zero, eq_comm]
  exact criticalWeilEnergy_eq_iff_simple_of_universal hU hUc hsees

/-- For any real source `f : ℝ → ℝ` and any real frequency `r ∈ ℝ`,
`f̂(−r) = conj f̂(r)`. -/
theorem paperFT_neg_ofReal_eq_conj (f : ℝ → ℝ) (r : ℝ) :
    Zeta23.paperFT (fun u => (f u : ℂ)) ((-r : ℝ) : ℂ) =
      conj (Zeta23.paperFT (fun u => (f u : ℂ)) (r : ℂ)) := by
  unfold Zeta23.paperFT
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_I]

/-- For any real source `f : ℝ → ℝ` and any real frequency `r ∈ ℝ`,
`‖f̂(−r)‖ = ‖f̂(r)‖`. -/
theorem norm_paperFT_neg_ofReal (f : ℝ → ℝ) (r : ℝ) :
    ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((-r : ℝ) : ℂ)‖ =
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (r : ℂ)‖ := by
  rw [paperFT_neg_ofReal_eq_conj, Complex.norm_conj]

/-- **Conjugate-pair lower bound on the multiplicity defect.** For every real `C²_c` source `f`
and every critical zero `ρ₀`, the conjugate pair `{ρ₀, conjCritical ρ₀}` contributes twice the
single-zero defect:
`2 m_{ρ₀}(m_{ρ₀} − 1) ‖f̂(γ_{ρ₀})‖² ≤ multiplicityDefect f`. -/
theorem two_mul_le_multiplicityDefect {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (ρ₀ : criticalZeros) :
    2 * ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
      ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) - 1) *
        ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ ^ 2) ≤
      multiplicityDefect f := by
  classical
  set d : criticalZeros → ℝ := fun ρ =>
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) * ((Zeta23.zetaZeroConfig.mult ρ : ℝ) - 1) *
      ‖Zeta23.paperFT (fun u => (f u : ℂ)) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2
  have hd0 : ∀ ρ, 0 ≤ d ρ := fun ρ => by
    have hm1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := by
      exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ : 𝒵).2
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  set ρ₁ := conjCritical ρ₀
  have hγ₀ : ((ρ₀ : 𝒵) : ℂ).im ≠ 0 := im_ne_zero_of_mem_critical ρ₀
  have hγ₁ : ((ρ₁ : 𝒵) : ℂ).im = -((ρ₀ : 𝒵) : ℂ).im := by simp [ρ₁, conjCritical]
  have hne : ρ₀ ≠ ρ₁ := fun h => hγ₀ (by
    have := congrArg (fun ρ : criticalZeros => ((ρ : 𝒵) : ℂ).im) h
    simp only [hγ₁] at this
    linarith)
  have hmult : Zeta23.zetaZeroConfig.mult ((ρ₁ : 𝒵) : ℂ) =
      Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) :=
    _root_.RHTower.mult_conj_zetaZeroConfig (ρ₀ : 𝒵).2
  have hd1 : d ρ₁ = d ρ₀ := by
    simp only [d, hmult, hγ₁, norm_paperFT_neg_ofReal]
  rw [multiplicityDefect_eq_tsum hf hfc]
  calc 2 * d ρ₀ = d ρ₀ + d ρ₁ := by rw [hd1]; ring
    _ = ∑ ρ ∈ ({ρ₀, ρ₁} : Finset criticalZeros), d ρ := (Finset.sum_pair hne).symm
    _ ≤ ∑' ρ, d ρ :=
        (summable_multiplicityDefect hf hfc).sum_le_tsum {ρ₀, ρ₁} fun ρ _ => hd0 ρ

/-- **Quantitative simplicity gap.** If `ρ₀ ∈ criticalZeros` is a non-simple critical zero
(`mult ρ₀ ≠ 1`), then `4 ‖f̂(γ_{ρ₀})‖² ≤ multiplicityDefect f`. -/
theorem four_mul_norm_sq_le_multiplicityDefect_of_mult_ne_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {ρ₀ : criticalZeros}
    (hmult : Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) ≠ 1) :
    4 * ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ ^ 2 ≤
      multiplicityDefect f := by
  have hm1 : 1 ≤ Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) :=
    Zeta23.zetaZeroConfig.one_le_mult _ (ρ₀ : 𝒵).2
  have hm2 : 2 ≤ Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) := by omega
  have hm2' : (2 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) := by exact_mod_cast hm2
  have hprod : (2 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
      ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) - 1) := by nlinarith
  have h0 := two_mul_le_multiplicityDefect hf hfc ρ₀
  have hle : 4 * ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ ^ 2 ≤
      2 * ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
        ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) - 1) *
          ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖ ^ 2) := by
    nlinarith [sq_nonneg ‖Zeta23.paperFT (fun u => (f u : ℂ)) ((((ρ₀ : 𝒵) : ℂ).im : ℝ) : ℂ)‖]
  exact hle.trans h0

/-! ## §4. Explicit Fourier lower bounds for `unif`, `upow`, and `splineProbe` -/

/-- **Fourier lower bound for the uniform density.** For `w > 0` and `z ≠ 0`,
`|sinh(w · Im z)| / (w ‖z‖) ≤ ‖Û_w(z)‖`. -/
theorem le_norm_paperFT_unif {w : ℝ} (hw : 0 < w) {z : ℂ} (hz : z ≠ 0) :
    |Real.sinh (w * z.im)| / (w * ‖z‖) ≤ ‖Zeta23.paperFT (fun x => (unif w x : ℂ)) z‖ := by
  rw [paperFT_unif hw hz, norm_div]
  have hden : ‖(2 : ℂ) * I * z * w‖ = 2 * w * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw]
    simp; ring
  rw [hden]
  have hnum : 2 * |Real.sinh (w * z.im)| ≤
      ‖Complex.exp (I * z * w) - Complex.exp (-(I * z * w))‖ := by
    have hrev := abs_norm_sub_norm_le (Complex.exp (I * z * w)) (Complex.exp (-(I * z * w)))
    have hn1 : ‖Complex.exp (I * z * w)‖ = Real.exp (-(w * z.im)) := by
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring
    have hn2 : ‖Complex.exp (-(I * z * w))‖ = Real.exp (w * z.im) := by
      rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]; ring
    rw [hn1, hn2] at hrev
    have hsinh : Real.exp (-(w * z.im)) - Real.exp (w * z.im) = -2 * Real.sinh (w * z.im) := by
      rw [Real.sinh_eq]; ring
    rw [hsinh, abs_mul, abs_neg, abs_of_pos two_pos] at hrev
    exact hrev
  have hpos : 0 < 2 * w * ‖z‖ := by
    have := norm_pos_iff.mpr hz
    positivity
  calc |Real.sinh (w * z.im)| / (w * ‖z‖)
      = 2 * |Real.sinh (w * z.im)| / (2 * w * ‖z‖) := by field_simp
    _ ≤ ‖Complex.exp (I * z * w) - Complex.exp (-(I * z * w))‖ / (2 * w * ‖z‖) :=
        div_le_div_of_nonneg_right hnum hpos.le

/-- **Fourier lower bound for `(n+1)`-fold uniform convolution powers.** For `w > 0` and `z ≠ 0`,
`(|sinh(w · Im z)| / (w ‖z‖))^{n+1} ≤ ‖(upow w n)^(z)‖`. -/
theorem le_norm_paperFT_upow {w : ℝ} (hw : 0 < w) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (|Real.sinh (w * z.im)| / (w * ‖z‖)) ^ (n + 1) ≤
      ‖Zeta23.paperFT (fun x => (upow w n x : ℂ)) z‖ := by
  rw [paperFT_upow, norm_pow]
  exact pow_le_pow_left₀ (by positivity) (le_norm_paperFT_unif hw hz) _

/-- **Explicit lower bound on `Û(r)` on the real line.** For every `r ∈ ℝ`,
`(sinh 1)⁴ / (1 + r²)² ≤ ‖Û(r)‖` (matching the upper bound `(cosh 1)⁴ / (1 + r²)²` of
`norm_paperFT_splineProbe_ofReal_le`). -/
theorem le_norm_paperFT_splineProbe_ofReal (r : ℝ) :
    Real.sinh 1 ^ 4 / (1 + r ^ 2) ^ 2 ≤
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ := by
  unfold splineProbe
  rw [paperFT_tiltedSource, cubicSpline]
  have hne : (r : ℂ) - I * 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have h := le_norm_paperFT_upow one_pos 3 hne
  have him : ((r : ℂ) - I * 1).im = -1 := by simp
  have hsinh : |Real.sinh (1 * ((r : ℂ) - I * 1).im)| = Real.sinh 1 := by
    rw [him, one_mul, Real.sinh_neg, abs_neg, abs_of_pos (Real.sinh_pos_iff.mpr one_pos)]
  have hnorm_sq : (1 * ‖(r : ℂ) - I * 1‖) ^ 4 = (1 + r ^ 2) ^ 2 := by
    rw [one_mul, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, I_re, I_im, mul_one, sub_zero, sub_im, ofReal_im, zero_sub]
    ring
  rw [hsinh, div_pow, hnorm_sq] at h
  exact h

/-- **Explicit quantitative lower bound on `multiplicityDefect splineProbe` at a critical zero.**
For every critical zero `ρ₀ = 1/2 + iγ₀ ∈ criticalZeros`,
`2 m_{ρ₀}(m_{ρ₀} − 1) (sinh 1)⁸ / (1 + γ₀²)⁴ ≤ multiplicityDefect splineProbe`. -/
theorem splineProbe_multiplicityDefect_lower_bound_of_criticalZero (ρ₀ : criticalZeros) :
    2 * ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) *
      ((Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) - 1) *
        (Real.sinh 1 ^ 8 / (1 + ((ρ₀ : 𝒵) : ℂ).im ^ 2) ^ 4)) ≤
      multiplicityDefect splineProbe := by
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  have hm1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) : ℝ) := by
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult _ (ρ₀ : 𝒵).2
  have hU := le_norm_paperFT_splineProbe_ofReal γ₀
  have hUsq : Real.sinh 1 ^ 8 / (1 + γ₀ ^ 2) ^ 4 ≤
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (γ₀ : ℂ)‖ ^ 2 := by
    have h0 : 0 ≤ Real.sinh 1 ^ 4 / (1 + γ₀ ^ 2) ^ 2 := by
      have : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
      positivity
    calc Real.sinh 1 ^ 8 / (1 + γ₀ ^ 2) ^ 4
        = (Real.sinh 1 ^ 4 / (1 + γ₀ ^ 2) ^ 2) ^ 2 := by
          rw [div_pow, ← pow_mul, ← pow_mul]
      _ ≤ ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (γ₀ : ℂ)‖ ^ 2 :=
          pow_le_pow_left₀ h0 hU 2
  refine (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hUsq (mul_nonneg (by linarith) (by linarith)))
    zero_le_two).trans ?_
  exact two_mul_le_multiplicityDefect contDiff_splineProbe hasCompactSupport_splineProbe ρ₀

/-- **Quantitative simplicity gap for `splineProbe`.** Any non-simple critical zero
`ρ₀ ∈ criticalZeros` (`mult ρ₀ ≠ 1`) forces
`4 (sinh 1)⁸ / (1 + γ₀²)⁴ ≤ multiplicityDefect splineProbe`. -/
theorem splineProbe_multiplicityDefect_gap_of_mult_ne_one {ρ₀ : criticalZeros}
    (hmult : Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) ≠ 1) :
    4 * (Real.sinh 1 ^ 8 / (1 + ((ρ₀ : 𝒵) : ℂ).im ^ 2) ^ 4) ≤
      multiplicityDefect splineProbe := by
  set γ₀ := ((ρ₀ : 𝒵) : ℂ).im
  have hU := le_norm_paperFT_splineProbe_ofReal γ₀
  have hUsq : Real.sinh 1 ^ 8 / (1 + γ₀ ^ 2) ^ 4 ≤
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (γ₀ : ℂ)‖ ^ 2 := by
    have h0 : 0 ≤ Real.sinh 1 ^ 4 / (1 + γ₀ ^ 2) ^ 2 := by
      have : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
      positivity
    calc Real.sinh 1 ^ 8 / (1 + γ₀ ^ 2) ^ 4
        = (Real.sinh 1 ^ 4 / (1 + γ₀ ^ 2) ^ 2) ^ 2 := by
          rw [div_pow, ← pow_mul, ← pow_mul]
      _ ≤ ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (γ₀ : ℂ)‖ ^ 2 :=
          pow_le_pow_left₀ h0 hU 2
  exact (mul_le_mul_of_nonneg_left hUsq (by norm_num)).trans
    (four_mul_norm_sq_le_multiplicityDefect_of_mult_ne_one contDiff_splineProbe
      hasCompactSupport_splineProbe hmult)

/-- **Certified height-bounded simplicity criterion for `splineProbe`.** For any height `Γ`,
if `multiplicityDefect splineProbe < 4 (sinh 1)⁸ / (1 + Γ²)⁴`, then every critical zero `ρ` with
`|(ρ : ℂ).im| ≤ Γ` is simple (`mult ρ = 1`). -/
theorem forall_critical_simple_up_to_height_of_multiplicityDefect_lt {Γ : ℝ}
    (hgap : multiplicityDefect splineProbe < 4 * (Real.sinh 1 ^ 8 / (1 + Γ ^ 2) ^ 4))
    (ρ₀ : criticalZeros) (hρ₀ : |((ρ₀ : 𝒵) : ℂ).im| ≤ Γ) :
    Zeta23.zetaZeroConfig.mult ((ρ₀ : 𝒵) : ℂ) = 1 := by
  by_contra hne
  have h1 := splineProbe_multiplicityDefect_gap_of_mult_ne_one hne
  have hsq : ((ρ₀ : 𝒵) : ℂ).im ^ 2 ≤ Γ ^ 2 := by
    rw [← sq_abs (((ρ₀ : 𝒵) : ℂ).im)]
    exact pow_le_pow_left₀ (abs_nonneg _) hρ₀ 2
  have hpow : (1 + ((ρ₀ : 𝒵) : ℂ).im ^ 2) ^ 4 ≤ (1 + Γ ^ 2) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hsinh : 0 ≤ Real.sinh 1 ^ 8 := by
    have : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
    positivity
  have hdiv : 4 * (Real.sinh 1 ^ 8 / (1 + Γ ^ 2) ^ 4) ≤
      4 * (Real.sinh 1 ^ 8 / (1 + ((ρ₀ : 𝒵) : ℂ).im ^ 2) ^ 4) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hsinh (by positivity) hpow) (by norm_num)
  linarith

/-! ## §5. Finite-prime / finite-cutoff multiplicity defect observable -/

/-- The `C_c(ℝ, ℝ)`-bundled source of a `RealWeilTestFn`. -/
def realWeilToCc (g : RealWeilTestFn) : C_c(ℝ, ℝ) :=
  ⟨⟨g.source, g.contDiff_source.continuous⟩, g.hasCompactSupport_source⟩

@[simp]
theorem realWeilToCc_apply (g : RealWeilTestFn) (u : ℝ) :
    realWeilToCc g u = g.source u := rfl

/-- **Finite-prime multiplicity defect observable at cutoff `N`.**
On the stationary bulk `[−cutoff N + w, −w]`, `signedSource (realWeilToCc g) N` uses only the
finite prime–polar measure `ν_N` (`n ≤ N + 2`), while the Weil side uses only the finite-cutoff
pairing `SignedPrimePolar.pairing g.supportScale (autocorr g.source)`. -/
def finitePrimeMultiplicityDefect (g : RealWeilTestFn) (w : ℝ) (N : ℕ) : ℝ :=
  (∫ u in (-cutoff N + w)..(-w), signedSource (realWeilToCc g) N u ^ 2) / cutoff N -
    (Zeta23.EF.gammaBracket 0 * autocorr g.source 0 + biScaleLevyEnergy g.source -
      2 * SignedPrimePolar.pairing g.supportScale (autocorr g.source))

/-- For any `C²_c` source `F` vanishing outside `[−w, w]` whose packet is eventually bounded
above, the normalized finite-prime stationary bulk energy
`(1 / cutoff N) ∫_{−cutoff N + w}^{−w} (signedSource F N u)² du` converges as `N → ∞` to
`criticalPacketEnergy F`. -/
theorem tendsto_bulk_signedSource_energy_div_cutoff_of_packet_bddAbove (F : C_c(ℝ, ℝ))
    (hF : ContDiff ℝ 2 (F : ℝ → ℝ)) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → F v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket F τ ≤ K) :
    Tendsto (fun N : ℕ => (∫ u in (-cutoff N + w)..(-w), signedSource F N u ^ 2) / cutoff N)
      atTop (𝓝 (criticalPacketEnergy F)) := by
  have hup_iff := packet_upper_iff hF F.hasCompactSupport le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one] at hup_iff
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (F u : ℂ)) (Zeta23.gammaOf ρ) = 0 :=
    fun ρ hρ => hup_iff.mp hup ρ (by linarith)
  have hP := (tendsto_mean_sq_stationaryPacket_of_blind hF F.hasCompactSupport hw0 hw hblind).comp
    ((tendsto_atTop_add_const_right atTop (-w) tendsto_id).comp tendsto_cutoff_atTop)
  have hratio : Tendsto (fun N : ℕ => (cutoff N - w) / cutoff N) atTop (𝓝 1) := by
    have h := (tendsto_div_add_const w).comp
      ((tendsto_atTop_add_const_right atTop (-w) tendsto_id).comp tendsto_cutoff_atTop)
    refine h.congr fun N => ?_
    simp [sub_eq_add_neg]
  have hmul := hP.mul hratio
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [tendsto_cutoff_atTop.eventually (eventually_ge_atTop (2 * w)),
    tendsto_cutoff_atTop.eventually (eventually_gt_atTop w)] with N hLw hNw
  simp only [Function.comp_apply, id, ← sub_eq_add_neg]
  rw [integral_signedSource_sq_bulk_eq_stationaryPacket F hw0 hw hLw]
  have hne : cutoff N - w ≠ 0 := by linarith
  field_simp

/-- **Convergence of the finite-prime multiplicity defect observable.** For any real Weil test `g`
vanishing outside `[−w, w]` whose packet is eventually bounded above (in particular under RH),
`finitePrimeMultiplicityDefect g w N → multiplicityDefect g.source` as `N → ∞`. -/
theorem tendsto_finitePrimeMultiplicityDefect_of_packet_bddAbove (g : RealWeilTestFn) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → g.source v = 0)
    (hup : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) :
    Tendsto (finitePrimeMultiplicityDefect g w) atTop (𝓝 (multiplicityDefect g.source)) := by
  unfold finitePrimeMultiplicityDefect multiplicityDefect
  rw [← levyWeilEnergy_eq_criticalWeilEnergy g hw0 hw hup]
  exact (tendsto_bulk_signedSource_energy_div_cutoff_of_packet_bddAbove (realWeilToCc g)
    g.contDiff_source hw0 hw hup).sub tendsto_const_nhds

/-- **Certified finite-prime criterion for RH and simplicity of all zeros.** For a real Weil test
`g` vanishing outside `[−w, w]` whose source is a universal probe: RH holds and every nontrivial
zero of `ζ` is simple if and only if the packet `P_g` is eventually bounded above and the
finite-prime multiplicity defect `finitePrimeMultiplicityDefect g w N` converges to `0` as
`N → ∞`. -/
theorem riemannHypothesis_and_simple_iff_finitePrimeMultiplicityDefect_of_universal
    (g : RealWeilTestFn) (hsees : SeesAllZeros g.source) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → g.source v = 0) :
    (RiemannHypothesis ∧ ∀ ρ : 𝒵, Zeta23.zetaZeroConfig.mult (ρ : ℂ) = 1) ↔
      (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket g.source τ ≤ K) ∧
        Tendsto (finitePrimeMultiplicityDefect g w) atTop (𝓝 0) := by
  constructor
  · rintro ⟨hRH, hsimple⟩
    have hup := (riemannHypothesis_iff_packet_bddAbove_of_universal g.contDiff_source
      g.hasCompactSupport_source hsees).mp hRH
    have hlim := tendsto_finitePrimeMultiplicityDefect_of_packet_bddAbove g hw0 hw hup
    have hzero : multiplicityDefect g.source = 0 :=
      (multiplicityDefect_eq_zero_iff_of_universal g.contDiff_source g.hasCompactSupport_source
        hsees).mpr fun ρ => hsimple ρ
    rw [hzero] at hlim
    exact ⟨hup, hlim⟩
  · rintro ⟨hup, hlim0⟩
    have hRH := (riemannHypothesis_iff_packet_bddAbove_of_universal g.contDiff_source
      g.hasCompactSupport_source hsees).mpr hup
    have hlim := tendsto_finitePrimeMultiplicityDefect_of_packet_bddAbove g hw0 hw hup
    have hzero : multiplicityDefect g.source = 0 := tendsto_nhds_unique hlim hlim0
    refine ⟨hRH, fun ρ => ?_⟩
    exact (multiplicityDefect_eq_zero_iff_of_universal g.contDiff_source
      g.hasCompactSupport_source hsees).mp hzero ⟨ρ, re_eq_half_of_mem hRH ρ⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
