import GaloisForLFunctions.ArithmeticCorrespondencePositivity.AnAbelSlopeAtTheGenusIsRHWithSimpleZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheZeroPartHasNoMassAtInfiniteHeight
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw

/-!
# The Abel slope of the prime error is the archimedean genus

The Abel slope `2c ∫ e^{−2cu} g(u)² du` of the prime-error profile
`g(u) = e^{−u/2}(ψ(⌊e^u⌋) − ⌊e^u⌋)` (P50) converges to the archimedean genus
`2 + γ − log 4π = Σ_ρ 1/(ρ(1 − ρ))` exactly when RH holds and every zero is simple
(`riemannHypothesis_and_simple_iff_tendsto_abelSlope`). The `𝔽_q` analogue is P42: the prime-error
slope of a pure curve is `Σ_β mult(β)²`, equal to `2g` exactly for a simple spectrum.

* **RH gives a budget** (`primeError_budget_of_riemannHypothesis`): the corpus mean-square band
  `∫_0^L Ẽ² ≤ C(1 + L)` for `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)` transfers to `g`, which differs from
  `Ẽ` by at most `e^{−u/2}`.
* **No mass at infinite height** (`eventually_abelSlope_le`). Under RH with simple zeros the line
  symbol is the zero part plus the archimedean remainder (`ThePrimeErrorSymbolSplitsAtTheZeros`);
  the zero part carries Abel mass at most `Σ_q 1/|ρ_q|²` (`TheZeroPartHasNoMassAtInfiniteHeight`)
  and the remainder is uniformly square integrable, so `limsup ≤ 2 + γ − log 4π`.
* **Abel capacity** (`eventually_lt_abelSlope`): the window atoms of finitely many critical zeros
  give `liminf ≥ 2 + γ − log 4π`.

The converse is P50. So the archimedean genus `2λ₁` is the energy budget of `ℤ` read on the prime
error exactly in the pure simple case, and under RH alone the Abel escape of `ψ` has no mass at
infinite height.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)
open _root_.RHTower (XiZeroCopy zeroOrdinate)

/-! ### RH gives a prime-error budget -/

theorem primeErrorRow_eq_psi (n : ℕ) : primeErrorRow n = Chebyshev.psi n - n := by
  have hψ : Chebyshev.psi n = ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast,
      ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n), ArithmeticFunction.map_zero, zero_add]
    exact Finset.sum_congr (by ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega)
      fun _ _ => rfl
  rw [primeErrorRow, prefixSum, Finset.sum_sub_distrib, hψ]
  simp

/-- `g(u) = Ẽ(u) + e^{−u/2}(e^u − ⌊e^u⌋)`. -/
theorem logProfile_primeErrorRow_eq (u : ℝ) :
    logProfile primeErrorRow u = BiScaleUncertainty.ChebyshevGauge.normalizedLogError u +
      Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) := by
  have hψ : Chebyshev.psi (⌊Real.exp u⌋₊ : ℝ) = Chebyshev.psi (Real.exp u) := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [logProfile, primeErrorRow_eq_psi, hψ, BiScaleUncertainty.ChebyshevGauge.normalizedLogError,
    BiScaleUncertainty.SignedPrimePolar.logError, neg_div]
  ring

/-- **RH gives a prime-error budget.** -/
theorem primeError_budget_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ S B : ℝ, 0 ≤ S ∧ 0 ≤ B ∧ ∀ L : ℝ, 0 ≤ L →
      ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B := by
  obtain ⟨C, hC0, hC⟩ :=
    BiScaleUncertainty.ChebyshevGauge.exists_meanSquare_band_of_riemannHypothesis hRH
  refine ⟨2 * C + 2, 2 * C, by positivity, by positivity, fun L hL => ?_⟩
  set E := BiScaleUncertainty.ChebyshevGauge.normalizedLogError with hE
  have hpt : ∀ u, 0 ≤ u → logProfile primeErrorRow u ^ 2 ≤ 2 * E u ^ 2 + 2 := by
    intro u hu
    have h0 : 0 ≤ Real.exp u - ⌊Real.exp u⌋₊ := sub_nonneg.mpr (Nat.floor_le (Real.exp_pos u).le)
    have h1 : Real.exp u - ⌊Real.exp u⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (Real.exp u)]
    have h2 : Real.exp (-(u / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hb0 : 0 ≤ Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) :=
      mul_nonneg (Real.exp_pos _).le h0
    have hb1 : Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) ≤ 1 := by
      calc Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) ≤ 1 * 1 :=
            mul_le_mul h2 h1 h0 zero_le_one
        _ = 1 := one_mul 1
    rw [logProfile_primeErrorRow_eq]
    set b := Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊)
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    calc (E u + b) ^ 2 ≤ 2 * E u ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (E u - b)]
      _ ≤ 2 * E u ^ 2 + 2 := by linarith
  have hg : IntegrableOn (fun u => logProfile primeErrorRow u ^ 2) (Ioc 0 L) :=
    (integrableOn_logProfile_sq zero_le_one abs_primeErrorRow_le L).congr_set_ae
      Ioo_ae_eq_Ioc.symm
  have hEint : IntegrableOn (fun u => E u ^ 2) (Icc 0 L) := by
    have hgI : IntegrableOn (fun u => logProfile primeErrorRow u ^ 2) (Icc 0 L) :=
      (integrableOn_logProfile_sq zero_le_one abs_primeErrorRow_le L).congr_set_ae
        Ioo_ae_eq_Icc.symm
    have hdom : IntegrableOn (fun u => 2 * logProfile primeErrorRow u ^ 2 + 8) (Icc 0 L) :=
      (hgI.const_mul 2).add (integrableOn_const (C := (8 : ℝ)) (by simp))
    refine Integrable.mono' hdom
      ((BiScaleUncertainty.ChebyshevGauge.measurable_normalizedLogError.pow_const 2).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hg' := logProfile_primeErrorRow_eq u
    have h0 : 0 ≤ Real.exp u - ⌊Real.exp u⌋₊ := sub_nonneg.mpr (Nat.floor_le (Real.exp_pos u).le)
    have h1 : Real.exp u - ⌊Real.exp u⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one (Real.exp u)]
    have h2 : Real.exp (-(u / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    have hb0 : 0 ≤ Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) :=
      mul_nonneg (Real.exp_pos _).le h0
    have hb1 : Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) ≤ 1 := by
      calc Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊) ≤ 1 * 1 :=
            mul_le_mul h2 h1 h0 zero_le_one
        _ = 1 := one_mul 1
    set b := Real.exp (-(u / 2)) * (Real.exp u - ⌊Real.exp u⌋₊)
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have hEu : E u = logProfile primeErrorRow u - b := by rw [hg']; ring
    rw [hEu]
    nlinarith [sq_nonneg (logProfile primeErrorRow u + b)]
  have hI2 : IntegrableOn (fun u => 2 * E u ^ 2 + 2) (Ioc 0 L) :=
    ((hEint.mono_set Ioc_subset_Icc_self).const_mul 2).add (integrableOn_const (C := (2 : ℝ))
      (by simp))
  rw [intervalIntegral.integral_of_le hL]
  calc ∫ u in Ioc 0 L, logProfile primeErrorRow u ^ 2
      ≤ ∫ u in Ioc 0 L, (2 * E u ^ 2 + 2) :=
        setIntegral_mono_on hg hI2 measurableSet_Ioc fun u hu => hpt u hu.1.le
    _ = 2 * (∫ u in Ioc 0 L, E u ^ 2) + 2 * L := by
        rw [integral_add ((hEint.mono_set Ioc_subset_Icc_self).const_mul 2)
          (integrableOn_const (C := (2 : ℝ)) (by simp)), integral_const_mul, setIntegral_const,
          Real.volume_real_Ioc_of_le hL, smul_eq_mul, sub_zero, mul_comm L]
    _ ≤ 2 * (∫ u in Icc 0 L, E u ^ 2) + 2 * L := by
        have := setIntegral_mono_set hEint (Eventually.of_forall fun u => sq_nonneg (E u))
          Ioc_subset_Icc_self.eventuallyLE
        linarith
    _ ≤ 2 * (C * (1 + L)) + 2 * L := by linarith [hC L hL]
    _ = (2 * C + 2) * L + 2 * C := by ring

/-! ### Simple zeros -/

/-- Under RH with simple zeros, distinct copies have distinct ordinates. -/
theorem zeroOrdinate_injective (hRH : RiemannHypothesis)
    (hsimple : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
      (analyticOrderAt riemannZeta ρ).toNat = 1) :
    ∀ q q' : XiZeroCopy, zeroOrdinate q = zeroOrdinate q' → q = q' := by
  rintro ⟨ρ, i⟩ ⟨ρ', i'⟩ h
  obtain ⟨hz, hre⟩ := riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH ρ
  obtain ⟨-, hre'⟩ := riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH ρ'
  have hρ : ρ = ρ' := Subtype.ext (Complex.ext (by rw [hre, hre']) h)
  subst hρ
  have hm : Int.toNat ((MeromorphicOn.divisor _root_.RHTower.xi Set.univ) (ρ : ℂ)) = 1 := by
    have := xiSupportMultiplicity_eq_toNat_analyticOrderAt_riemannZeta ρ
    rw [hsimple _ hz hre] at this
    exact this
  have hi := i.isLt
  have hi' := i'.isLt
  have : i = i' := Fin.ext (by omega)
  rw [this]

theorem norm_zeroWeight_sq (q : XiZeroCopy) : ‖zeroWeight q‖ ^ 2 = 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
  rw [zeroWeight, norm_neg, norm_div, norm_one, div_pow, one_pow]

/-- Under RH the Abel mass of the copies is the archimedean genus. -/
theorem tsum_norm_zeroWeight_sq (hRH : RiemannHypothesis) :
    ∑' q : XiZeroCopy, ‖zeroWeight q‖ ^ 2 = _root_.RHTower.poleSharpConstant := by
  rw [poleSharpConstant_eq_tsum_of_riemannHypothesis hRH]
  exact tsum_congr norm_zeroWeight_sq

/-! ### The Abel slope under RH -/

/-- Under RH with a budget, on `Re s = ½ + c`, `0 < c < ¼`, the line symbol is the zero part plus
the archimedean remainder. -/
theorem lineSymbol_primeError_eq_split (hRH : RiemannHypothesis) {S B : ℝ} (hS0 : 0 ≤ S)
    (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B)
    {c : ℝ} (hc : 0 < c) (hc4 : c < 1 / 4) (y : ℝ) :
    lineSymbol (logProfile primeErrorRow) c y =
      zeroPart (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) +
        archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hC : 0 ≤ S / c + B := add_nonneg (div_nonneg hS0 hc.le) hB0
  have hE := fun T => pronic_energy_le_of_linear hS0 hB0 hlin (v := primeErrorRow) hc T
  have hsre : 1 / 2 < (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp; linarith
  have hs1 : ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [lineSymbol_logProfile_eq primeErrorRow_zero hC hc.le hE (by linarith) y,
    complexMellinPairing_primeErrorRow_eq hC hc.le hE (by simp; linarith) hs1
      (riemannZeta_ne_zero_of_riemannHypothesis hRH hsre)]
  exact primeErrorSymbol_eq_zeroPart_add hRH hsre hs1

/-- Under a budget, `2c A(c) = (c/π) ∫ ‖G(c + iy)‖² dy`. -/
theorem primeErrorAbelSlope_eq {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B)
    {c : ℝ} (hc : 0 < c) :
    primeErrorAbelSlope c = c / Real.pi * ∫ y, ‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2 ∧
      Integrable (fun y => ‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2) := by
  have hdata := integrable_and_memLp_dampedProfile_logProfile (c := c) primeErrorRow_zero
    (add_nonneg (div_nonneg hS0 hc.le) hB0) hc.le
    (fun T => pronic_energy_le_of_linear hS0 hB0 hlin hc T) (by linarith)
  refine ⟨?_, _root_.RHTower.integrable_norm_sq_laplaceBoundary hdata.1.ofReal hdata.2.ofReal⟩
  rw [integral_norm_sq_lineSymbol hdata.1 hdata.2, primeErrorAbelSlope]
  field_simp

/-- **No mass at infinite height.** Under RH with simple zeros, eventually
`2c A(c) < a` for every `a > 2 + γ − log 4π`. -/
theorem eventually_abelSlope_lt (hRH : RiemannHypothesis)
    (hsimple : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
      (analyticOrderAt riemannZeta ρ).toNat = 1) {a : ℝ}
    (ha : _root_.RHTower.poleSharpConstant < a) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ), primeErrorAbelSlope c < a := by
  obtain ⟨S, B, hS0, hB0, hlin⟩ := primeError_budget_of_riemannHypothesis hRH
  have hinj := zeroOrdinate_injective hRH hsimple
  have hP := tsum_norm_zeroWeight_sq hRH
  set P := _root_.RHTower.poleSharpConstant with hPdef
  have hP0 : 0 ≤ P := hP ▸ tsum_nonneg fun _ => by positivity
  have hη : 0 < a - P := by linarith
  set ε := min 1 ((a - P) / (4 * (P + 2))) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε * (P + 2) ≤ (a - P) / 4 := by
    have h := min_le_right 1 ((a - P) / (4 * (P + 2)))
    rw [← hεdef, le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨K₂, hK₂⟩ := exists_integral_norm_sq_archRemainder_le
  have hZ := eventually_lintegral_zeroPart_le hRH hinj hε
  rw [hP] at hZ
  have hsmall : ∀ᶠ c in 𝓝[>] (0 : ℝ), (1 + 1 / ε) * (c * |K₂|) / Real.pi < (a - P) / 2 := by
    have h : Tendsto (fun c : ℝ => (1 + 1 / ε) * (c * |K₂|) / Real.pi) (𝓝 0)
        (𝓝 ((1 + 1 / ε) * (0 * |K₂|) / Real.pi)) :=
      ((by fun_prop : Continuous fun c : ℝ => (1 + 1 / ε) * (c * |K₂|) / Real.pi)).tendsto 0
    simp only [zero_mul, mul_zero, zero_div] at h
    exact (h.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hZ, hsmall, self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with c hcZ hcs hc hc4
  have hc0 : (0 : ℝ) < c := hc
  obtain ⟨hslope, hGint⟩ := primeErrorAbelSlope_eq hS0 hB0 hlin hc0
  obtain ⟨hRint, hRle⟩ := hK₂ c hc0 hc4.2.le
  have hK₂0 : 0 ≤ K₂ := (integral_nonneg fun _ => by positivity).trans hRle
  have hsplit := fun y => lineSymbol_primeError_eq_split hRH hS0 hB0 hlin hc0 hc4.2 y
  set zP : ℝ → ℝ := fun y => ‖zeroPart (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 with hzP
  set rR : ℝ → ℝ := fun y => ‖archRemainder (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 with hrR
  have hlint : ∫⁻ y : ℝ, ENNReal.ofReal (‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2) ≤
      ENNReal.ofReal ((1 + ε) * (Real.pi * (P + ε) / c) + (1 + 1 / ε) * K₂) := by
    calc ∫⁻ y : ℝ, ENNReal.ofReal (‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2)
        ≤ ∫⁻ y : ℝ, (ENNReal.ofReal ((1 + ε) * zP y) + ENNReal.ofReal ((1 + 1 / ε) * rR y)) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), hsplit y]
          exact ENNReal.ofReal_le_ofReal (norm_add_sq_le_of_pos hε)
      _ = (∫⁻ y : ℝ, ENNReal.ofReal ((1 + ε) * zP y)) +
            ∫⁻ y : ℝ, ENNReal.ofReal ((1 + 1 / ε) * rR y) :=
          lintegral_add_right' _ ((hRint.const_mul _).aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal (1 + ε) * (∫⁻ y : ℝ, ENNReal.ofReal (zP y)) +
            ENNReal.ofReal (1 + 1 / ε) * ∫⁻ y : ℝ, ENNReal.ofReal (rR y) := by
          simp_rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + ε by positivity),
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + 1 / ε by positivity)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (Real.pi * (P + ε) / c) +
            ENNReal.ofReal (1 + 1 / ε) * ENNReal.ofReal K₂ := by
          refine add_le_add (by gcongr) (mul_le_mul_right ?_ _)
          rw [← ofReal_integral_eq_lintegral_ofReal hRint
            (Eventually.of_forall fun _ => by positivity)]
          exact ENNReal.ofReal_le_ofReal hRle
      _ = ENNReal.ofReal ((1 + ε) * (Real.pi * (P + ε) / c) + (1 + 1 / ε) * K₂) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hGle : ∫ y, ‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2 ≤
      (1 + ε) * (Real.pi * (P + ε) / c) + (1 + 1 / ε) * K₂ := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
      hGint.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlint
  have hpi := Real.pi_pos
  have hbound : primeErrorAbelSlope c ≤ (1 + ε) * (P + ε) + (1 + 1 / ε) * (c * K₂) / Real.pi := by
    rw [hslope]
    calc c / Real.pi * ∫ y, ‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2
        ≤ c / Real.pi * ((1 + ε) * (Real.pi * (P + ε) / c) + (1 + 1 / ε) * K₂) :=
          mul_le_mul_of_nonneg_left hGle (by positivity)
      _ = (1 + ε) * (P + ε) + (1 + 1 / ε) * (c * K₂) / Real.pi := by
          field_simp
  rw [abs_of_nonneg hK₂0] at hcs
  have h1 : (1 + ε) * (P + ε) ≤ P + (a - P) / 4 := by nlinarith
  linarith

/-- **Abel capacity at the genus.** Under RH with simple zeros, eventually `a < 2c A(c)` for
every `a < 2 + γ − log 4π`. -/
theorem eventually_lt_abelSlope (hRH : RiemannHypothesis)
    (hsimple : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
      (analyticOrderAt riemannZeta ρ).toNat = 1) {a : ℝ}
    (ha : a < _root_.RHTower.poleSharpConstant) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ), a < primeErrorAbelSlope c := by
  obtain ⟨S, B, hS0, hB0, hlin⟩ := primeError_budget_of_riemannHypothesis hRH
  have hinj := zeroOrdinate_injective hRH hsimple
  obtain ⟨F, hF⟩ : ∃ F : Finset XiZeroCopy, a < ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have := Real.tsum_le_of_sum_le (fun _ => by positivity) h
    rw [← poleSharpConstant_eq_tsum_of_riemannHypothesis hRH] at this
    linarith
  set Z := F.image (fun q : XiZeroCopy => (q.1 : ℂ)) with hZdef
  have hinjF : Set.InjOn (fun q : XiZeroCopy => (q.1 : ℂ)) F := fun q _ q' _ h =>
    hinj q q' (by simp only at h; simp only [zeroOrdinate, h])
  have hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 := by
    intro ρ hρ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hρ
    exact riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH q.1
  have hsumZ : ∑ ρ ∈ Z, ‖-(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2 =
      ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2 := by
    rw [hZdef, Finset.sum_image hinjF]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨hz, hre⟩ := riemannZeta_eq_zero_and_re_of_xiDivisorSupport hRH q.1
    rw [hsimple _ hz hre, neg_div, norm_neg, norm_div, Nat.cast_one, norm_one, div_pow, one_pow]
  have hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im := fun ρ hρ ρ' hρ' hne h =>
    hne (Complex.ext (by rw [(hZ ρ hρ).2, (hZ ρ' hρ').2]) h)
  have hpi := Real.pi_pos
  have hcap := eventually_le_mul_integral_lineSymbol_of_poles primeErrorRow_zero hS0 hB0 hlin Z
    hsep _ (fun ρ hρ => exists_primeError_window_pole_bound hS0 hB0 hlin (hZ ρ hρ).1 (hZ ρ hρ).2)
    (M := Real.pi * (a + ∑ q ∈ F, 1 / ‖(q.1 : ℂ)‖ ^ 2) / 2) (by rw [hsumZ]; nlinarith)
  filter_upwards [hcap, self_mem_nhdsWithin] with c hc1 hc
  obtain ⟨hslope, -⟩ := primeErrorAbelSlope_eq hS0 hB0 hlin (show (0 : ℝ) < c from hc)
  have : c * ∫ y, ‖lineSymbol (logProfile primeErrorRow) c y‖ ^ 2 =
      Real.pi * primeErrorAbelSlope c := by
    rw [hslope]; field_simp
  rw [this] at hc1
  nlinarith

/-- **The Abel slope at the genus under RH with simple zeros.** -/
theorem tendsto_abelSlope_of_riemannHypothesis_of_simple (hRH : RiemannHypothesis)
    (hsimple : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
      (analyticOrderAt riemannZeta ρ).toNat = 1) :
    (∀ c, 0 < c →
      Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2) ∧
    Tendsto primeErrorAbelSlope (𝓝[>] 0) (𝓝 _root_.RHTower.poleSharpConstant) := by
  obtain ⟨S, B, hS0, hB0, hlin⟩ := primeError_budget_of_riemannHypothesis hRH
  refine ⟨fun c hc => ?_, tendsto_order.2 ⟨fun a ha => eventually_lt_abelSlope hRH hsimple ha,
    fun a ha => eventually_abelSlope_lt hRH hsimple ha⟩⟩
  have hdata := integrable_and_memLp_dampedProfile_logProfile (c := c) primeErrorRow_zero
    (add_nonneg (div_nonneg hS0 hc.le) hB0) hc.le
    (fun T => pronic_energy_le_of_linear hS0 hB0 hlin hc T) (by linarith)
  refine ((memLp_two_iff_integrable_sq_norm hdata.2.1).mp hdata.2).congr
    (Eventually.of_forall fun u => ?_)
  simp only [dampedProfile, Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The Abel–Cramér law.** The Abel slope of the prime error converges to the archimedean genus
`2 + γ − log 4π` exactly when RH holds and every critical zero is simple. -/
theorem riemannHypothesis_and_simple_iff_tendsto_abelSlope :
    (RiemannHypothesis ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
        (analyticOrderAt riemannZeta ρ).toNat = 1) ↔
      ((∀ c, 0 < c →
          Integrable fun u => Real.exp (-(2 * c * u)) * logProfile primeErrorRow u ^ 2) ∧
        Tendsto primeErrorAbelSlope (𝓝[>] 0) (𝓝 _root_.RHTower.poleSharpConstant)) :=
  ⟨fun h => tendsto_abelSlope_of_riemannHypothesis_of_simple h.1 h.2,
    fun h => riemannHypothesis_and_simple_of_tendsto_abelSlope h.1 h.2⟩

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
