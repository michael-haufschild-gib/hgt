import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceIsAPhasedSumOverHeckePoints
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRotatedThetaProductReadsTheRotatedCorrelation
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedThetaProductReadsThePhasedSquare

/-!
# The Hecke-at-four trace reads the cubic twist at two

The constant term of the Hecke-at-four trace `Tr F` of the projected theta function `θ_s` is
(`integral_sourceFourTrace`)

`∫_P Tr F(z + jv) dz = 8 |P| (Σ_h b(2v, h) b(v/2, −4h) + Σ_h χ(h) b(v/2, h) b(v/2, −h))`,

where `χ(h) ∈ {0, 1, ω, ω²}` is the cube root of unity congruent to `h` modulo `2` (`0` for even `h`): the
shifted square `Σ T(h)T(−4h)` and the **2-adic cubic twist** `Σ χ(h) T(h)²` of the theta square. The growth
`8 c² v^{4/3}` comes from the first sum only: the twisted sum has `χ(0) = 0`.

Mechanism. On the period parallelogram the doubling `z = 2u` preserves integrals of `3O`-periodic functions
(`integral_periodDomain_two_mul`: `P` is tiled by the four halves `(P + 3n)/2`, `n ∈ {0, 1, ω, 1 + ω}`). In the
variable `u` every Hecke point is a cusp character series, and Parseval reads the products. The half-period phases
are the additive character of `𝔽₄`: `e(ξ_h · 3x/2) = (−1)^{b}` for `hx = a + bω` (`tracePhase_half`), and the
cubic character weights `u` of the twisted products assemble the Gauss sum of `𝔽₄`,
`Σ_u u ψ(h u²) = 2χ(h)` (`gaussFour`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

/-! ### Doubling on the period parallelogram -/

theorem mem_periodDomain_iff (z : ℂ) :
    z ∈ periodDomain ↔ ∀ i, cubicPeriodCoordinates z i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [periodDomain, ZSpan.mem_fundamentalDomain]
  rfl

theorem periodCoordinates_three_eval (m k : ℤ) :
    cubicPeriodCoordinates (3 * ringComplex (Coordinates.eval m k)) = ![(m : ℝ), (k : ℝ)] := by
  have h : cubicPeriodCoordinates.symm ![(m : ℝ), (k : ℝ)] = 3 * ringComplex (Coordinates.eval m k) := by
    rw [ringComplex_eval]
    rfl
  rw [← h, LinearEquiv.apply_symm_apply]

theorem int_mem_zero_one {c : ℝ} (hc : c ∈ Set.Ico (0 : ℝ) 1) (m : ℤ) :
    (1 / 2 : ℝ) * (c + m) ∈ Set.Ico (0 : ℝ) 1 ↔ m = 0 ∨ m = 1 := by
  obtain ⟨hc0, hc1⟩ := hc
  constructor
  · rintro ⟨h0, h1⟩
    have hm0 : (-1 : ℝ) < m := by linarith
    have hm1 : (m : ℝ) < 2 := by linarith
    have : -1 < m := by exact_mod_cast hm0
    have : m < 2 := by exact_mod_cast hm1
    omega
  · rintro (rfl | rfl) <;> constructor <;> push_cast <;> linarith

/-- `(z + 3n)/2 ∈ P` for `z ∈ P` exactly when `n ∈ {0, 1, ω, 1 + ω}`. -/
theorem half_mem_periodDomain {z : ℂ} (hz : z ∈ periodDomain) (m k : ℤ) :
    (1 / 2 : ℝ) • (z + 3 * ringComplex (Coordinates.eval m k)) ∈ periodDomain ↔
      (m = 0 ∨ m = 1) ∧ (k = 0 ∨ k = 1) := by
  rw [mem_periodDomain_iff] at hz ⊢
  rw [map_smul, map_add, periodCoordinates_three_eval]
  have e0 : ((1 / 2 : ℝ) • (cubicPeriodCoordinates z + ![(m : ℝ), (k : ℝ)])) 0 =
      (1 / 2 : ℝ) * (cubicPeriodCoordinates z 0 + m) := by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.cons_val_zero]
  have e1 : ((1 / 2 : ℝ) • (cubicPeriodCoordinates z + ![(m : ℝ), (k : ℝ)])) 1 =
      (1 / 2 : ℝ) * (cubicPeriodCoordinates z 1 + k) := by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · intro h
    refine ⟨(int_mem_zero_one (hz 0) m).mp ?_, (int_mem_zero_one (hz 1) k).mp ?_⟩
    · rw [← e0]; exact h 0
    · rw [← e1]; exact h 1
  · rintro ⟨hm, hk⟩ i
    fin_cases i
    · rw [Fin.zero_eta, e0]; exact (int_mem_zero_one (hz 0) m).mpr hm
    · rw [Fin.mk_one, e1]; exact (int_mem_zero_one (hz 1) k).mpr hk

/-- **Doubling preserves period integrals.** For continuous `3O`-periodic `f`, `∫_P f(2u) du = ∫_P f(z) dz`. -/
theorem integral_periodDomain_two_mul (f : ℂ → ℂ) (hf : Continuous f)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z) :
    ∫ u in periodDomain, f (2 * u) = ∫ z in periodDomain, f z := by
  set Q : Set ℂ := {z | (1 / 2 : ℝ) • z ∈ periodDomain} with hQdef
  have hQm : MeasurableSet Q :=
    periodDomain_measurable.preimage (measurable_const_smul (1 / 2 : ℝ))
  set R := ∑ i : Fin 2, ‖periodBasis i‖
  have hQb : Q ⊆ Metric.closedBall 0 (2 * R) := by
    intro z hz
    have h := norm_mem_periodDomain _ hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  set φ : ℂ → ℂ := Q.indicator f with hφdef
  have hφi : Integrable φ :=
    ((hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 (2 * R))).mono_set hQb).integrable_indicator hQm
  have h1 : ∫ u in periodDomain, f (2 * u) = ∫ u, φ ((2 : ℝ) • u) := by
    rw [← integral_indicator periodDomain_measurable]
    congr 1
    funext u
    have hu : ((2 : ℝ) • u ∈ Q) ↔ u ∈ periodDomain := by
      simp only [hQdef, Set.mem_setOf_eq, smul_smul]
      norm_num
    by_cases hp : u ∈ periodDomain
    · rw [Set.indicator_of_mem hp, hφdef, Set.indicator_of_mem (hu.mpr hp), Complex.real_smul]
      push_cast
      ring_nf
    · rw [Set.indicator_of_notMem hp, hφdef, Set.indicator_of_notMem (fun h => hp (hu.mp h))]
  have h2 : ∫ u, φ ((2 : ℝ) • u) = (1 / 4 : ℝ) • ∫ z, φ z := by
    rw [Measure.integral_comp_smul, Complex.finrank_real_complex]
    norm_num
  have h3 := integral_eq_period_integrals φ hφi
  set S : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (1, 1)}
  have hreindex : ∑' n : O, ∫ z in periodDomain, φ (z + 3 * ringComplex n) =
      ∑' p : ℤ × ℤ, ∫ z in periodDomain, φ (z + 3 * ringComplex (Coordinates.eval p.1 p.2)) :=
    (Coordinates.coordinateEquiv.symm.tsum_eq
      (fun n : O => ∫ z in periodDomain, φ (z + 3 * ringComplex n))).symm
  have hterm : ∀ p : ℤ × ℤ, ∫ z in periodDomain, φ (z + 3 * ringComplex (Coordinates.eval p.1 p.2)) =
      if p ∈ S then ∫ z in periodDomain, f z else 0 := by
    intro p
    split_ifs with hp
    · refine setIntegral_congr_fun periodDomain_measurable fun z hz => ?_
      have hmem : z + 3 * ringComplex (Coordinates.eval p.1 p.2) ∈ Q := by
        refine (half_mem_periodDomain hz p.1 p.2).mpr ?_
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hp
        omega
      rw [hφdef, Set.indicator_of_mem hmem, hper]
    · rw [← integral_zero]
      refine setIntegral_congr_fun periodDomain_measurable fun z hz => ?_
      have hmem : z + 3 * ringComplex (Coordinates.eval p.1 p.2) ∉ Q := by
        intro h
        have h' := (half_mem_periodDomain hz p.1 p.2).mp h
        apply hp
        simp only [S, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
        omega
      rw [hφdef, Set.indicator_of_notMem hmem]
  rw [h1, h2, h3, hreindex, tsum_eq_sum (s := S) (fun p hp => by rw [hterm, if_neg hp]),
    Finset.sum_congr rfl (fun p hp => by rw [hterm, if_pos hp]), Finset.sum_const]
  have hcard : S.card = 4 := by decide
  rw [hcard, Complex.real_smul]
  push_cast
  ring

/-! ### The additive character of `𝔽₄` and its Gauss sum -/

theorem conj_ringComplex_omega : conj (ringComplex omega) = -1 - ringComplex omega := by
  have hre := complex_omega_coordinates.1
  apply Complex.ext <;> norm_num [hre]

theorem ringComplex_traceLambda_eq : ringComplex traceLambda = 1 + 2 * ringComplex omega := by
  simp [traceLambda, map_add, map_mul, map_ofNat]

/-- **The half-period phase is the trace character of `𝔽₄`.** For `x = a + bω`,
`e(x / (2(1 + 2ω))) = (−1)^b`. -/
theorem tracePhase_half (x : O) :
    tracePhase (ringComplex x / (2 * ringComplex traceLambda)) = if (red x).2 = 0 then 1 else -1 := by
  obtain ⟨a, b, rfl⟩ := Coordinates.exists_coordinates x
  have hred : red ((a : O) + (b : O) * omega) = ((a : ZMod 2), (b : ZMod 2)) := red_eval a b
  rw [hred]
  have hs : ringComplex traceLambda ≠ 0 := ringComplex_ne_zero traceLambda_ne_zero
  rw [ringComplex_traceLambda_eq] at hs ⊢
  have hx : ringComplex ((a : O) + (b : O) * omega) = (a : ℂ) + (b : ℂ) * ringComplex omega := by
    simp [map_add, map_mul, map_intCast]
  have key : ((a : ℂ) + b * ringComplex omega) / (2 * (1 + 2 * ringComplex omega)) +
      conj (((a : ℂ) + b * ringComplex omega) / (2 * (1 + 2 * ringComplex omega))) = (b : ℂ) / 2 := by
    rw [map_div₀, map_mul, map_add, map_add, map_mul, map_mul, conj_ringComplex_omega, map_intCast, map_intCast,
      map_one, map_ofNat]
    have hs' : (1 + 2 * (-1 - ringComplex omega)) = -(1 + 2 * ringComplex omega) := by ring
    calc _ = (b : ℂ) * (1 + 2 * ringComplex omega) / (2 * (1 + 2 * ringComplex omega)) := by
          rw [hs', mul_neg, div_neg, ← sub_eq_add_neg, div_sub_div_same]
          congr 1
          ring
      _ = (b : ℂ) / 2 := mul_div_mul_right (b : ℂ) 2 hs
  change Complex.exp (2 * Real.pi * Complex.I *
    (ringComplex ((a : O) + (b : O) * omega) / (2 * (1 + 2 * ringComplex omega)) +
      conj (ringComplex ((a : O) + (b : O) * omega) / (2 * (1 + 2 * ringComplex omega))))) = _
  rw [hx, key, show 2 * (Real.pi : ℂ) * Complex.I * ((b : ℂ) / 2) = (b : ℂ) * (Real.pi * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd b with hb | hb
  · rw [hb.neg_one_zpow, if_pos ((ZMod.intCast_eq_zero_iff_even).mpr hb)]
  · rw [hb.neg_one_zpow, if_neg]
    rw [ZMod.intCast_eq_zero_iff_even]
    exact Int.not_even_iff_odd.mpr hb

/-- The trace character `ψ(p) = (−1)^{Tr p}` of `𝔽₄`. -/
def traceCharF (p : F4) : ℂ := if p.2 = 0 then 1 else -1

/-- The cube root of unity congruent to `p ∈ 𝔽₄` (`0` at `p = 0`). -/
def cubeRootF (p : F4) : ℂ :=
  if p = (1, 0) then 1 else if p = (0, 1) then ringComplex omega else
    if p = (1, 1) then ringComplex omega ^ 2 else 0

theorem omega_complex_rel : ringComplex omega ^ 2 + ringComplex omega + 1 = 0 := by
  have h : omega ^ 2 + omega + 1 = 0 := by linear_combination omega_sq_add
  have h' := congrArg ringComplex h
  simpa [map_add, map_pow] using h'

/-- **The Gauss sum of `𝔽₄`.** `Σ_{u ∈ 𝔽₄^×} u ψ(p u²) = 2 χ(p)`. -/
theorem gaussFour (p : F4) :
    ∑ k : Fin 3, ringComplex (uO k) * traceCharF (f4mul p (f4mul (uF k) (uF k))) = 2 * cubeRootF p := by
  have hω := omega_complex_rel
  obtain ⟨p1, p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;>
    simp (config := { decide := true }) [Fin.sum_univ_three, uO, uF, f4mul, traceCharF, cubeRootF, map_pow] <;>
    first | linear_combination hω | linear_combination -hω

/-! ### Hecke points of the projected theta function -/

theorem transThree_coe (t : O) : (transThree t : SL(2, O)) = integralTranslation (3 * t) := rfl

theorem transThree_smul_upperPoint (z : ℂ) (s : O) (v : ℝ) (hv : 0 < v) :
    complexMatrix (transThree s) • upperPoint z v hv = upperPoint (z + 3 * ringComplex s) v hv := by
  change integralComplexMatrix (integralTranslation (3 * s)) • upperPoint z v hv = _
  rw [integralTranslation_action, map_mul, map_ofNat]

theorem heckeHigh_source_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    heckeHigh sourceTheta (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (2 * z) := by
  rw [heckeHigh, fourDilation_upperPoint, sourceTheta, cubicSourceResidualFunction_fourier_expansion]

theorem heckeLow_source_upperPoint (s : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    heckeLow sourceTheta s (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (v / 2)) ((z + 3 * ringComplex s) / 2) := by
  rw [heckeLow, transThree_smul_upperPoint z s v hv, fourContraction_upperPoint, sourceTheta,
    cubicSourceResidualFunction_fourier_expansion]

/-- The half-shifted amplitudes `b(v/2, h) e(ξ_h · 3s/2)`. -/
def shiftedAmplitude (s : O) (v : ℝ) (h : O) : ℂ :=
  rationalSourceModeAmplitude (v / 2) h * tracePhase (cuspFrequency h * (3 * ringComplex s / 2))

theorem shiftedAmplitude_summable (s : O) (v : ℝ) (hv : 0 < v) :
    Summable (fun h => ‖shiftedAmplitude s v h‖) :=
  (rationalSourceModeAmplitude_summable (v / 2) (by positivity)).congr fun h => by
    rw [shiftedAmplitude, norm_mul, tracePhase_norm, mul_one]

theorem heckeLow_source_two_mul (s : O) (u : ℂ) (v : ℝ) (hv : 0 < v) :
    heckeLow sourceTheta s (upperPoint (2 * u) v hv) = cuspCharacterSeries (shiftedAmplitude s v) u := by
  rw [heckeLow_source_upperPoint, show (2 * u + 3 * ringComplex s) / 2 = u + 3 * ringComplex s / 2 by ring,
    cuspCharacterSeries_translate]
  rfl

theorem cuspFrequency_half_eq (h t : O) :
    cuspFrequency h * (3 * ringComplex t / 2) = ringComplex (h * t) / (2 * ringComplex traceLambda) := by
  have hs : ringComplex traceLambda ≠ 0 := ringComplex_ne_zero traceLambda_ne_zero
  unfold cuspFrequency
  rw [map_mul]
  field_simp

/-- The shifted square does not see the half-period phase. -/
theorem shiftedAmplitude_neg_four (s : O) (v : ℝ) (h : O) :
    shiftedAmplitude s v (-(4 * h)) = rationalSourceModeAmplitude (v / 2) (-(4 * h)) := by
  have hs : ringComplex traceLambda ≠ 0 := ringComplex_ne_zero traceLambda_ne_zero
  have he : cuspFrequency (-(4 * h)) * (3 * ringComplex s / 2) = cuspFrequency (-(2 * h * s)) * (3 * ringComplex 1) := by
    unfold cuspFrequency
    simp only [map_neg, map_mul, map_ofNat, map_one]
    field_simp
    ring
  rw [shiftedAmplitude, he, cuspFrequency_period, mul_one]

/-- The twisted products see the trace character at `h u²`. -/
theorem shiftedAmplitude_mul_neg (k : Fin 3) (t : O) (v : ℝ) (h : O) :
    shiftedAmplitude (-(uO k ^ 2) + t) v h * shiftedAmplitude t v (-h) =
      rationalSourceModeAmplitude (v / 2) h * rationalSourceModeAmplitude (v / 2) (-h) *
        traceCharF (f4mul (red h) (f4mul (uF k) (uF k))) := by
  have hphase : tracePhase (cuspFrequency h * (3 * ringComplex (-(uO k ^ 2) + t) / 2)) *
      tracePhase (cuspFrequency (-h) * (3 * ringComplex t / 2)) =
        tracePhase (cuspFrequency h * (3 * ringComplex (-(uO k ^ 2)) / 2)) := by
    rw [← AddChar.map_add_eq_mul, cuspFrequency_neg]
    congr 1
    rw [map_add]
    ring
  rw [shiftedAmplitude, shiftedAmplitude, mul_mul_mul_comm, hphase, cuspFrequency_half_eq, tracePhase_half,
    red_mul, red_neg, pow_two, red_mul, red_uO, traceCharF]

/-! ### The constant term -/

theorem sourceFourTrace_period (v : ℝ) (hv : 0 < v) (n : O) (z : ℂ) :
    sourceFourTrace (upperPoint (z + 3 * ringComplex n) v hv) = sourceFourTrace (upperPoint z v hv) := by
  rw [← transThree_smul_upperPoint, sourceFourTrace_automorphy, complexCharacter_transThree, one_pow, one_mul]

/-- The trace at `(z, v)` in terms of the cusp character series of `θ_s`. -/
theorem sourceFourTrace_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceFourTrace (upperPoint z v hv) =
      ∑ x : Fin 4, cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (2 * z) *
          cuspCharacterSeries (rationalSourceModeAmplitude (v / 2)) ((z + 3 * ringComplex (tO x)) / 2) +
        ∑ x : Fin 4, cuspCharacterSeries (rationalSourceModeAmplitude (v / 2))
            ((z + 3 * ringComplex (-1 + tO x)) / 2) * cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (2 * z) +
          ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) *
            (cuspCharacterSeries (rationalSourceModeAmplitude (v / 2)) ((z + 3 * ringComplex (-(uO k ^ 2) + tO x)) / 2) *
              cuspCharacterSeries (rationalSourceModeAmplitude (v / 2)) ((z + 3 * ringComplex (tO x)) / 2)) := by
  rw [sourceFourTrace, heckeFourTrace_eq_hecke sourceTheta sourceTheta_automorphy]
  simp only [heckeHigh_source_upperPoint, heckeLow_source_upperPoint]

theorem sourceFourTrace_continuous (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => sourceFourTrace (upperPoint z v hv)) := by
  have hA := cuspCharacterSeries_continuous _ (rationalSourceModeAmplitude_summable (2 * v) (by positivity))
  have hB := cuspCharacterSeries_continuous _ (rationalSourceModeAmplitude_summable (v / 2) (by positivity))
  simp_rw [sourceFourTrace_upperPoint]
  fun_prop

/-- The trace at `(2u, v)`: every Hecke point is a cusp character series in `u`. -/
theorem sourceFourTrace_two_mul (u : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceFourTrace (upperPoint (2 * u) v hv) =
      ∑ x : Fin 4, cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (4 * u) *
          cuspCharacterSeries (shiftedAmplitude (tO x) v) u +
        ∑ x : Fin 4, cuspCharacterSeries (shiftedAmplitude (-1 + tO x) v) u *
          cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (4 * u) +
          ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) *
            (cuspCharacterSeries (shiftedAmplitude (-(uO k ^ 2) + tO x) v) u *
              cuspCharacterSeries (shiftedAmplitude (tO x) v) u) := by
  rw [sourceFourTrace, heckeFourTrace_eq_hecke sourceTheta sourceTheta_automorphy]
  simp only [heckeHigh_source_upperPoint, heckeLow_source_two_mul, show (2 : ℂ) * (2 * u) = 4 * u by ring]

theorem summable_mul_neg_mul (a : O → ℂ) (ha : Summable (fun h => ‖a h‖)) (c : O → ℂ) (hc : ∀ h, ‖c h‖ ≤ 1) :
    Summable (fun h => a h * a (-h) * c h) := by
  refine Summable.of_norm_bounded (g := fun h => ‖a h‖ * ∑' k, ‖a k‖) (ha.mul_right _) fun h => ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖a (-h)‖ ≤ ∑' k, ‖a k‖ := ha.le_tsum (-h) (fun k _ => norm_nonneg _)
  calc ‖a h‖ * ‖a (-h)‖ * ‖c h‖ ≤ ‖a h‖ * ‖a (-h)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hc h) (by positivity)
    _ ≤ ‖a h‖ * ∑' k, ‖a k‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem norm_traceCharF_le (p : F4) : ‖traceCharF p‖ ≤ 1 := by
  unfold traceCharF
  split_ifs <;> simp

/-- **The constant term of the Hecke-at-four trace.** The shifted square and the 2-adic cubic twist of the
theta square:
`∫_P Tr F(z + jv) dz = 8|P| (Σ_h b(2v, h) b(v/2, −4h) + Σ_h χ(h) b(v/2, h) b(v/2, −h))`. -/
theorem integral_sourceFourTrace (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceFourTrace (upperPoint z v hv) =
      8 * periodArea * (∑' h : O, rationalSourceModeAmplitude (2 * v) h * rationalSourceModeAmplitude (v / 2) (-(4 * h)) +
        ∑' h : O, cubeRootF (red h) *
          (rationalSourceModeAmplitude (v / 2) h * rationalSourceModeAmplitude (v / 2) (-h))) := by
  set A := rationalSourceModeAmplitude (2 * v)
  set B := rationalSourceModeAmplitude (v / 2)
  have hA : Summable (fun h => ‖A h‖) := rationalSourceModeAmplitude_summable _ (by positivity)
  have hB : Summable (fun h => ‖B h‖) := rationalSourceModeAmplitude_summable _ (by positivity)
  have hS : ∀ s : O, Summable (fun h => ‖shiftedAmplitude s v h‖) := fun s => shiftedAmplitude_summable s v hv
  have hcA : Continuous (fun u : ℂ => cuspCharacterSeries A (4 * u)) :=
    (cuspCharacterSeries_continuous _ hA).comp (continuous_const.mul continuous_id)
  have hcS : ∀ s : O, Continuous (cuspCharacterSeries (shiftedAmplitude s v)) := fun s =>
    cuspCharacterSeries_continuous _ (hS s)
  rw [← integral_periodDomain_two_mul _ (sourceFourTrace_continuous v hv) (sourceFourTrace_period v hv)]
  simp_rw [sourceFourTrace_two_mul]
  have i1 : ∀ x : Fin 4, Integrable (fun u => cuspCharacterSeries A (4 * u) *
      cuspCharacterSeries (shiftedAmplitude (tO x) v) u) (volume.restrict periodDomain) := fun x =>
    integrableOn_periodDomain_of_continuous _ (hcA.mul (hcS _))
  have i2 : ∀ x : Fin 4, Integrable (fun u => cuspCharacterSeries (shiftedAmplitude (-1 + tO x) v) u *
      cuspCharacterSeries A (4 * u)) (volume.restrict periodDomain) := fun x =>
    integrableOn_periodDomain_of_continuous _ ((hcS _).mul hcA)
  have i3 : ∀ (k : Fin 3) (x : Fin 4), Integrable (fun u => ringComplex (uO k) *
      (cuspCharacterSeries (shiftedAmplitude (-(uO k ^ 2) + tO x) v) u *
        cuspCharacterSeries (shiftedAmplitude (tO x) v) u)) (volume.restrict periodDomain) := fun k x =>
    integrableOn_periodDomain_of_continuous _ (continuous_const.mul ((hcS _).mul (hcS _)))
  have I1 : Integrable (fun u => ∑ x : Fin 4, cuspCharacterSeries A (4 * u) *
      cuspCharacterSeries (shiftedAmplitude (tO x) v) u) (volume.restrict periodDomain) :=
    integrable_finsetSum _ fun x _ => i1 x
  have I2 : Integrable (fun u => ∑ x : Fin 4, cuspCharacterSeries (shiftedAmplitude (-1 + tO x) v) u *
      cuspCharacterSeries A (4 * u)) (volume.restrict periodDomain) :=
    integrable_finsetSum _ fun x _ => i2 x
  have I3 : Integrable (fun u => ∑ k : Fin 3, ∑ x : Fin 4, ringComplex (uO k) *
      (cuspCharacterSeries (shiftedAmplitude (-(uO k ^ 2) + tO x) v) u *
        cuspCharacterSeries (shiftedAmplitude (tO x) v) u)) (volume.restrict periodDomain) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun x _ => i3 k x
  have I12 : Integrable (fun u => (∑ x : Fin 4, cuspCharacterSeries A (4 * u) *
      cuspCharacterSeries (shiftedAmplitude (tO x) v) u) + ∑ x : Fin 4,
        cuspCharacterSeries (shiftedAmplitude (-1 + tO x) v) u * cuspCharacterSeries A (4 * u))
      (volume.restrict periodDomain) := I1.add I2
  rw [integral_add I12 I3, integral_add I1 I2, integral_finsetSum _ fun x _ => i1 x,
    integral_finsetSum _ fun x _ => i2 x, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun x _ => i3 k x]
  simp_rw [integral_finsetSum _ fun x _ => i3 _ x, integral_const_mul]
  have e1 : ∀ s : O, ∫ u in periodDomain, cuspCharacterSeries A (4 * u) * cuspCharacterSeries (shiftedAmplitude s v) u =
      periodArea * ∑' h : O, A h * B (-(4 * h)) := by
    intro s
    rw [integral_cuspCharacterSeries_four_mul _ _ hA (hS s)]
    simp_rw [shiftedAmplitude_neg_four]
    rfl
  have e2 : ∀ s : O, ∫ u in periodDomain, cuspCharacterSeries (shiftedAmplitude s v) u * cuspCharacterSeries A (4 * u) =
      periodArea * ∑' h : O, A h * B (-(4 * h)) := by
    intro s
    simp_rw [mul_comm (cuspCharacterSeries (shiftedAmplitude s v) _)]
    exact e1 s
  have e3 : ∀ (k : Fin 3) (t : O), ∫ u in periodDomain, cuspCharacterSeries (shiftedAmplitude (-(uO k ^ 2) + t) v) u *
      cuspCharacterSeries (shiftedAmplitude t v) u =
        periodArea * ∑' h : O, B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k))) := by
    intro k t
    rw [integral_cuspCharacterSeries_mul _ _ (hS _) (hS _)]
    simp_rw [shiftedAmplitude_mul_neg]
    rfl
  simp_rw [e1, e2, e3]
  have hsum : ∀ k : Fin 3, Summable (fun h => B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k)))) :=
    fun k => summable_mul_neg_mul B hB _ fun h => norm_traceCharF_le _
  have hT : ∑ k : Fin 3, ringComplex (uO k) * ∑' h : O, B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k))) =
      ∑' h : O, 2 * (cubeRootF (red h) * (B h * B (-h))) := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left _)]
    refine tsum_congr fun h => ?_
    have hg := gaussFour (red h)
    calc ∑ k : Fin 3, ringComplex (uO k) * (B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k))))
        = B h * B (-h) * ∑ k : Fin 3, ringComplex (uO k) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [hg]; ring
  have hfin : ∑ k : Fin 3, ∑ _x : Fin 4, ringComplex (uO k) *
      (periodArea * ∑' h : O, B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k)))) =
        4 * periodArea * ∑ k : Fin 3, ringComplex (uO k) *
          ∑' h : O, B h * B (-h) * traceCharF (f4mul (red h) (f4mul (uF k) (uF k))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hfin, hT, tsum_mul_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
