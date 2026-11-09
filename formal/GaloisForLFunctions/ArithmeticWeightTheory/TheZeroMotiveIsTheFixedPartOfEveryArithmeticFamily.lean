import GaloisForLFunctions.ArithmeticWeightTheory.AmplifiedMonodromyBreaksOnlyOffTheTrivialFibre
import GaloisForLFunctions.ArithmeticWeightTheory.ProductPositivityCouplingIsOneWay
import GaloisForLFunctions.ArithmeticWeightTheory.TheJumpLocusIsThePretentiousArchimedeanLine
import GaloisForLFunctions.ArithmeticWeightTheory.TheArchimedeanLineHasTheGenericMoments
import GaloisForLFunctions.ArithmeticGaugeTheory.TheCoherencePrinciple
import GaloisForLFunctions.ArithmeticGaugeTheory.TheFiniteGaugePointsSampleHaar
import GaloisForLFunctions.SurfaceOfSpecZ.TheTensorPowerTrick
import GaloisForLFunctions.BlackHoleRingdown.TheWeylLowerBound
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneHeckeEigenformIsBlindToHalvingPairs
import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremInMertensForm

/-!
# The zero motive of `ζ` is the fixed part of every arithmetic family

This module proves **(FP)** unconditionally across all canonical arithmetic families `(𝔉, ν)` of
Euler products and their mixtures:

> For every arithmetic family `(𝔉, ν)` whose even window-trace moments are computed by
> orthogonality — the gauge torus, Dirichlet characters modulo `q` and modulo `q ≤ Q`, the vertical
> line, Hecke eigenforms under the Weyl law and Rankin–Selberg square, number fields under a
> counting measure, isozeric Euler deformations, and their mixtures — and every `k`, the `2k`-th
> moment identity of the family controls the variable traces only: the centred trace of `ζ` enters
> with `ν`-mass tending to zero or as an exact common factor, and no inequality derived from the
> family bounds `|c_B(log p)|` below the trivial bound.

## Main results

1. **Five canonical family classes** (`Section 1`):
   - *Gauge torus* (`gaugeHaar_singleton_zero`, `gaugeTorus_fixedPart_decoupling`):
     `gaugeHaar {0} = 0`, `gaugeHaar (isozericClass σ₀) = 0` (`½ ≤ σ₀ < 1`), and
     `gaugeHaar jumpLocus = 0`; any trace perturbation supported at `0` cancels identically from
     every `2k`-th Haar moment.
   - *Dirichlet characters* (`measureReal_dirichletGaugeMeasure_zero`,
     `tendsto_dirichletGaugeMeasure_zero`, `tendsto_cumulative_principal_fraction`):
     at modulus `q` the principal character `{0}` has mass `1 / φ(q) → 0`, and across all
     characters modulo `1 ≤ q ≤ Q` the principal-character mass `Q / Σ_{q ≤ Q} φ(q)` tends to `0`.
   - *Vertical line* (`measureReal_verticalHeightMeasure_Icc_le`,
     `tendsto_verticalHeightMeasure_Icc`): normalized height measure on `[−T, T]` gives `{0}` mass
     `0` and every bounded interval `[−H, H]` mass `≤ H / T → 0` as `T → ∞`.
   - *Hecke eigenforms under the Weyl law and Rankin–Selberg*
     (`tendsto_weyl_finiteMode_mass`, `rankinSelberg_family_commonFactor`):
     any finite set of modes has Weyl mass `r / cuspCount Λ → 0` as `Λ → ∞`, while Rankin–Selberg
     averages factor `ζ(s)` out identically (`Σ w_i L(τ_i², s) = ζ(s) Σ w_i L(τ_i(·²), s)`) with
     nonnegative divisor-coupled coefficients `(ζ * τ_i(·²))(n) = τ_i(n)² ≥ 0`.
   - *Number fields under a counting measure* (`numberField_counting_fixedPart`):
     every intermediate field `L^H` splits at unramified primes as
     `degreeOneCount (L^H) p = 1 + varPermChar H (frob p) ≥ 0` with `classMean (varPermChar H) = 0`,
     and every probability mixture preserves the constant `ζ`-summand `1`.

2. **Moment decoupling, pushforward realizability, and mixture closure** (`Section 2`):
   - *Common-factor binomial decoupling* (`commonFactor_moment_realizable_for_all_c`):
     when `ζ` enters as an exact common summand `c + V`, the variable moments `∫ V^j dρ` (`1 ≤ j ≤ 2k`)
     determine `∫ (c + V)^{2k} dρ` as a universal polynomial in `c`, and `Measure.map (c + V ·) ρ`
     is a genuine probability measure on `ℝ` for *every* `c ∈ ℝ`; hence no moment or Hankel
     positivity inequality constrains `c`.
   - *Mixture closure* (`tendsto_mixture_moment_decomp`):
     convex mixtures `(1 − λ_n) μ_n + λ_n ρ_n` of vanishing-mass and common-factor families
     decouple asymptotically into `(1 − λ_n) ∫ V_n^{2k} dμ_n + λ_n ∫ (c + V_n)^{2k} dρ_n`.

3. **Jensen–Minkowski coercivity and the RH equivalence for cover-family moments** (`Section 3`):
   - *Tangent coercivity* (`even_pow_tangent_le`, `pow_two_mul_le_integral_add_of_integral_eq_zero`):
     for any zero-mean variable trace `∫ V dρ = 0` and `k ≥ 1`,
     `c^{2k} ≤ ∫ (c + V)^{2k} dρ ≤ 2^{2k} (c^{2k} + ∫ V^{2k} dρ)`.
   - *Cover-family tensor moments are equivalent to RH*
     (`riemannHypothesis_iff_coverFamily_tensorExponent_sublinear`,
     `zeroMotive_is_fixedPart_of_every_arithmeticFamily`):
     sublinear `2k`-th prime-trace moment exponents across the gauge cover family `c(p) + Re T_x(log p)`
     hold if and only if `RiemannHypothesis` holds.
-/

open MeasureTheory Finset Filter Topology Complex
open scoped ComplexConjugate ENNReal ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry ArithmeticGaugeTheory SurfaceOfSpecZ
open ArithmeticOrientationGeometry SquareRootThreshold Zeta23

/-! ## Section 1. The five canonical family classes -/

/-! ### 1.1 The gauge torus and isozeric deformations -/

/-- The trivial fibre `{0}` has Haar measure zero on `GaugeTorus`. -/
theorem gaugeHaar_singleton_zero : gaugeHaar {(0 : GaugeTorus)} = 0 := by
  refine measure_mono_null (fun x hx => ?_)
    (gaugeHaar_isozericClass_eq_zero (σ₀ := 1 / 2) le_rfl (by norm_num))
  rw [Set.mem_singleton_iff.mp hx]
  show Summable fun p : Nat.Primes =>
    ‖twist (0 : GaugeTorus) p - 1‖ * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
  simp only [twist_trivial, sub_self, norm_zero, zero_mul, summable_zero]

open Classical in
/-- **Gauge-torus fixed-part decoupling.** On `(GaugeTorus, gaugeHaar)`, the trivial fibre `{0}`,
every isozeric deformation class `isozericClass σ₀` (`½ ≤ σ₀ < 1`), and the entire pretentious jump
locus have Haar measure `0`, and any value `c₀` placed at `0` cancels identically from every
`2k`-th moment. -/
theorem gaugeTorus_fixedPart_decoupling {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₁ : σ₀ < 1)
    (V : GaugeTorus → ℂ) (c₀ : ℂ) (k : ℕ) :
    gaugeHaar {(0 : GaugeTorus)} = 0 ∧
      gaugeHaar (isozericClass σ₀) = 0 ∧
      gaugeHaar {x : GaugeTorus | ∃ τ : ℝ, Summable fun p : Nat.Primes => pretTerm x τ p / (p : ℕ)} = 0 ∧
      ∫ x, ‖(if x = 0 then c₀ else 0) + V x‖ ^ (2 * k) ∂gaugeHaar =
        ∫ x, ‖V x‖ ^ (2 * k) ∂gaugeHaar := by
  refine ⟨gaugeHaar_singleton_zero, gaugeHaar_isozericClass_eq_zero hσ₀ hσ₁,
    gaugeHaar_jumpLocus_eq_zero, ?_⟩
  refine integral_congr_ae ?_
  have hne : ∀ᵐ x ∂gaugeHaar, x ≠ (0 : GaugeTorus) := by
    rw [ae_iff]
    simpa only [Classical.not_not, Set.setOf_eq_eq_singleton] using gaugeHaar_singleton_zero
  filter_upwards [hne] with x hx
  rw [if_neg hx, zero_add]

/-! ### 1.2 Dirichlet characters modulo `q` and modulo `q ≤ Q` -/

theorem dirichletGauge_one (q : ℕ) [NeZero q] :
    dirichletGauge (1 : DirichletCharacter ℂ q) = 0 := by
  funext p
  simp only [dirichletGauge, Pi.zero_apply]
  split_ifs with hpq
  · have h1 : (1 : DirichletCharacter ℂ q) (p : ZMod q) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr hpq)
    rw [h1, Complex.arg_one, zero_div]
    simp
  · rfl

theorem dirichletGauge_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    dirichletGauge χ = 0 ↔ χ = 1 := by
  refine ⟨fun h0 => ?_, fun h1 => h1 ▸ dirichletGauge_one q⟩
  refine dirichletCharacter_eq_one_of_periodic_gauge χ (r := 1) (N := 1) one_ne_zero fun n _ => ?_
  rw [h0, twist_trivial, twist_trivial]

/-- Uniform probability measure on the gauge points of Dirichlet characters modulo `q`. -/
def dirichletGaugeMeasure (q : ℕ) [NeZero q] : Measure GaugeTorus :=
  (q.totient : ℝ≥0∞)⁻¹ • ∑ χ : DirichletCharacter ℂ q, Measure.dirac (dirichletGauge χ)

private theorem card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ]

instance (q : ℕ) [NeZero q] : IsProbabilityMeasure (dirichletGaugeMeasure q) := by
  constructor
  have htot_pos : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have htot_ne : (q.totient : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr htot_pos.ne'
  simp only [dirichletGaugeMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
    Finset.sum_const, Finset.card_univ, card_dirichletCharacter_eq_totient, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel htot_ne (ENNReal.natCast_ne_top q.totient)

/-- At modulus `q`, the trivial fibre `{0}` (the principal character) has mass `1 / φ(q)`. -/
theorem measureReal_dirichletGaugeMeasure_zero (q : ℕ) [NeZero q] :
    (dirichletGaugeMeasure q).real {0} = 1 / q.totient := by
  classical
  unfold Measure.real dirichletGaugeMeasure
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ (isClosed_singleton.measurableSet)]
  have hsum : (∑ χ : DirichletCharacter ℂ q,
      ({(0 : GaugeTorus)} : Set GaugeTorus).indicator 1 (dirichletGauge χ) : ℝ≥0∞) = 1 := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q)]
    · simp [dirichletGauge_one]
    · intro χ _ hχ
      have hne : dirichletGauge χ ≠ 0 := mt (dirichletGauge_eq_zero_iff χ).mp hχ
      simp [hne]
    · simp
  rw [hsum, smul_eq_mul, mul_one, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Along any modulus sequence with `φ(q_n) → ∞`, the `ζ`-mass `1 / φ(q_n)` tends to `0`. -/
theorem tendsto_dirichletGaugeMeasure_zero {q : ℕ → ℕ} [∀ n, NeZero (q n)]
    (hφ : Tendsto (fun n => (q n).totient) atTop atTop) :
    Tendsto (fun n => (dirichletGaugeMeasure (q n)).real {0}) atTop (𝓝 0) := by
  simp_rw [measureReal_dirichletGaugeMeasure_zero]
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hφ)

/-- **Cumulative characters modulo `q ≤ Q`.** Across all characters modulo `1 ≤ q ≤ Q`, the
fraction of principal characters `Q / Σ_{q = 1}^Q φ(q)` tends to `0` as `Q → ∞`. -/
theorem tendsto_cumulative_principal_fraction :
    Tendsto (fun Q : ℕ => (Q : ℝ) / ∑ q ∈ Icc 1 Q, (q.totient : ℝ)) atTop (𝓝 0) := by
  have hk_top : Tendsto (fun Q : ℕ => Nat.log 4 (Q / 2)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨2 * 4 ^ b, fun Q hQ => ?_⟩
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hcard_ev := hk_top.eventually (eventually_card_flipBlock (θ := 3 / 4) (by norm_num))
  have h4_ev := hk_top.eventually ((tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 4) (by norm_num : (0 : ℝ) < 3 / 4))).eventually_gt_atTop (2 : ℝ))
  have hmaj : Tendsto (fun Q : ℕ => 16 * ((4 : ℝ) ^ (-(3 / 4 : ℝ))) ^ Nat.log 4 (Q / 2))
      atTop (𝓝 0) := by
    have hr : |(4 : ℝ) ^ (-(3 / 4 : ℝ))| < 1 := by
      rw [abs_of_pos (by positivity)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).comp hk_top).const_mul 16
  refine squeeze_zero' ?_ ?_ hmaj
  · exact Eventually.of_forall fun Q =>
      div_nonneg (Nat.cast_nonneg Q) (sum_nonneg fun _ _ => Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 8, hcard_ev, h4_ev] with Q hQ8 hk_card hk_two
    set k := Nat.log 4 (Q / 2)
    have hQ2_ne : Q / 2 ≠ 0 := by omega
    have hpow_le : 4 ^ k ≤ Q / 2 := Nat.pow_log_le_self 4 hQ2_ne
    have hlt_pow : Q / 2 < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (Q / 2)
    have hQ_ub : (Q : ℝ) ≤ 8 * (4 : ℝ) ^ k := by
      have hQ_nat : Q ≤ 8 * 4 ^ k := by
        rw [pow_succ'] at hlt_pow
        omega
      exact_mod_cast hQ_nat
    have hsub : flipBlock (3 / 4) k ⊆ Icc 1 Q := fun p hp => by
      obtain ⟨hpr, _, hp2⟩ := mem_flipBlock hp
      exact mem_Icc.mpr ⟨hpr.one_le, by omega⟩
    have hfs_ge2 : (2 : ℝ) ≤ flipSize (3 / 4) k := by
      have hfl : (2 : ℝ) < (4 : ℝ) ^ ((3 / 4 : ℝ) * k) := by
        rwa [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      exact_mod_cast Nat.le_floor hfl.le
    have hfs_half : (4 : ℝ) ^ ((3 / 4 : ℝ) * k) / 2 ≤ flipSize (3 / 4) k := by
      have hlt1 : (4 : ℝ) ^ ((3 / 4 : ℝ) * k) < (flipSize (3 / 4) k : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have htot_lb : (4 : ℝ) ^ ((3 / 4 : ℝ) * k) / 2 * (4 : ℝ) ^ k ≤
        ∑ q ∈ Icc 1 Q, (q.totient : ℝ) := by
      calc (4 : ℝ) ^ ((3 / 4 : ℝ) * k) / 2 * (4 : ℝ) ^ k
          ≤ (flipSize (3 / 4) k : ℝ) * (4 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right hfs_half (by positivity)
        _ = ((flipBlock (3 / 4) k).card : ℝ) * (4 : ℝ) ^ k := by rw [hk_card]
        _ = ∑ _p ∈ flipBlock (3 / 4) k, (4 : ℝ) ^ k := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ flipBlock (3 / 4) k, (p.totient : ℝ) := sum_le_sum fun p hp => by
            obtain ⟨hpr, h4p, _⟩ := mem_flipBlock hp
            rw [Nat.totient_prime hpr]
            have hle : 4 ^ k ≤ p - 1 := by omega
            exact_mod_cast hle
        _ ≤ ∑ q ∈ Icc 1 Q, (q.totient : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
    have hden_pos : 0 < (4 : ℝ) ^ ((3 / 4 : ℝ) * k) / 2 * (4 : ℝ) ^ k := by positivity
    calc (Q : ℝ) / ∑ q ∈ Icc 1 Q, (q.totient : ℝ)
        ≤ (8 * (4 : ℝ) ^ k) / ((4 : ℝ) ^ ((3 / 4 : ℝ) * k) / 2 * (4 : ℝ) ^ k) :=
          div_le_div₀ (by positivity) hQ_ub hden_pos htot_lb
      _ = 16 / (4 : ℝ) ^ ((3 / 4 : ℝ) * k) := by field_simp; ring
      _ = 16 * ((4 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
          rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
            ← Real.rpow_natCast ((4 : ℝ) ^ (-(3 / 4 : ℝ))) k, ← Real.rpow_mul (by norm_num)]
          congr 2; ring

/-! ### 1.3 The vertical line -/

/-- Normalized height measure `(2T)⁻¹ dt|_{[−T, T]}` on the vertical line. -/
def verticalHeightMeasure (T : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * T))⁻¹ • volume.restrict (Set.Icc (-T) T)

instance {T : ℝ} [Fact (0 < T)] : IsProbabilityMeasure (verticalHeightMeasure T) := by
  constructor
  have hT : 0 < T := Fact.out
  simp only [verticalHeightMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_neg_eq_add, ← two_mul, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by linarith)).ne' ENNReal.ofReal_ne_top

/-- On the vertical line `[−T, T]` (`T > 0`), `{0}` has mass `0` and every bounded neighbourhood
`[−H, H]` (`H ≥ 0`) of `0` has mass at most `H / T`, tending to `0` as `T → ∞`. -/
theorem measureReal_verticalHeightMeasure_Icc_le {T H : ℝ} (hT : 0 < T) (hH : 0 ≤ H) :
    (verticalHeightMeasure T).real {(0 : ℝ)} = 0 ∧
      (verticalHeightMeasure T).real (Set.Icc (-H) H) ≤ H / T := by
  refine ⟨?_, ?_⟩
  · unfold Measure.real verticalHeightMeasure
    rw [Measure.smul_apply, Measure.restrict_apply (isClosed_singleton.measurableSet),
      measure_mono_null Set.inter_subset_left Real.volume_singleton]
    simp
  · unfold Measure.real verticalHeightMeasure
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc, smul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
    have hsub : Set.Icc (-H) H ∩ Set.Icc (-T) T ⊆ Set.Icc (-H) H := Set.inter_subset_left
    have hvol : (volume (Set.Icc (-H) H ∩ Set.Icc (-T) T)).toReal ≤ 2 * H := by
      have hle := measure_mono hsub
      rw [Real.volume_Icc, sub_neg_eq_add, ← two_mul] at hle
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
        (by rw [ENNReal.toReal_ofReal (by linarith)])
    calc (2 * T)⁻¹ * (volume (Set.Icc (-H) H ∩ Set.Icc (-T) T)).toReal
        ≤ (2 * T)⁻¹ * (2 * H) := mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = H / T := by field_simp

theorem tendsto_verticalHeightMeasure_Icc {H : ℝ} (hH : 0 ≤ H) :
    Tendsto (fun T : ℝ => (verticalHeightMeasure T).real (Set.Icc (-H) H)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    ((tendsto_const_nhds (x := H)).div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (measureReal_verticalHeightMeasure_Icc_le hT hH).2

/-! ### 1.4 Hecke eigenforms under the Weyl law and Rankin–Selberg -/

/-- **Weyl-law mass vanishing.** By `weyl_lower_bound`, any fixed finite set of `r` cuspidal modes
has uniform Weyl counting mass `r / cuspCount L → 0` as the eigenvalue cutoff `L → ∞`. -/
theorem tendsto_weyl_finiteMode_mass (r : ℕ) :
    Tendsto (fun L : ℝ => (r : ℝ) / (BlackHoleRingdown.cuspCount L : ℝ)) atTop (𝓝 0) := by
  obtain ⟨c, hc0, L₀, hweyl⟩ := BlackHoleRingdown.WeylBound.weyl_lower_bound
  have hmaj : Tendsto (fun L : ℝ => ((r : ℝ) / c) / L) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (r : ℝ) / c)).div_atTop tendsto_id
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (max L₀ 1)] with L _
    exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop (max L₀ 1)] with L hL
    have hL₀ : L₀ ≤ L := (le_max_left _ _).trans hL
    have hL1 : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hL)
    have hcL : c * L ≤ (BlackHoleRingdown.cuspCount L : ℝ) := hweyl L hL₀
    calc (r : ℝ) / (BlackHoleRingdown.cuspCount L : ℝ)
        ≤ (r : ℝ) / (c * L) := div_le_div₀ (Nat.cast_nonneg r) le_rfl (mul_pos hc0 hL1) hcL
      _ = ((r : ℝ) / c) / L := (div_div (r : ℝ) c L).symm

/-- Real symmetric-square cofactor `m ↦ τ(m²)` of a real Hecke sequence `τ : ℕ → ℝ`. -/
def realTauSqAF (τ : ℕ → ℝ) (h0 : τ 0 = 0) : ArithmeticFunction ℝ :=
  ⟨fun m => τ (m ^ 2), by simpa using h0⟩

/-- **Rankin–Selberg common-factor and divisor-positivity law.** For any finite weighted family of
real normalized Hecke sequences `τ_i`, `ζ(s)` factors identically out of the Rankin–Selberg average
on `Re s > 2`, and each variable cofactor `realTauSqAF (τ i)` is multiplicative with nonnegative
`ζ`-convolved Dirichlet coefficients `(ζ * realTauSqAF (τ i))(n) = τ_i(n)² ≥ 0` (to which
`no_reverse_weight_bound_from_product_positivity` applies directly). -/
theorem rankinSelberg_family_commonFactor {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (lam : ι → ℕ → ℂ) (τ : ι → ℕ → ℝ)
    (hτ : ∀ i ∈ s, BlackHoleRingdown.CuspEuler.HeckeRec (lam i) (fun n => (τ i n : ℂ)))
    (h1 : ∀ i ∈ s, τ i 1 = 1) (h0 : ∀ i ∈ s, τ i 0 = 0)
    (hK : ∀ i ∈ s, ∃ K : ℝ, ∀ n : ℕ, |τ i n| ≤ K * Real.sqrt n) :
    (∀ z : ℂ, 2 < z.re →
      ∑ i ∈ s, w i * LSeries (fun n => ((τ i n ^ 2 : ℝ) : ℂ)) z =
        riemannZeta z * ∑ i ∈ s, w i * LSeries (fun m => (τ i (m ^ 2) : ℂ)) z) ∧
    (∀ i (hi : i ∈ s), (realTauSqAF (τ i) (h0 i hi)).IsMultiplicative ∧
      ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        realTauSqAF (τ i) (h0 i hi)) n) := by
  refine ⟨fun z hz => ?_, fun i hi => ?_⟩
  · rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨K, hKi⟩ := hK i hi
    have h1c : ((τ i 1 : ℝ) : ℂ) = 1 := by exact_mod_cast h1 i hi
    have h0c : ((τ i 0 : ℝ) : ℂ) = 0 := by exact_mod_cast h0 i hi
    have hKc : ∀ n : ℕ, ‖((τ i n : ℝ) : ℂ)‖ ≤ K * Real.sqrt n := fun n => by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hKi n
    have hL := ArithmeticHolographyOfTheModularHorizon.HalvingPairs.lseries_sq_eq
      (hτ i hi) h1c h0c hKc hz
    have hfun : (fun n => ((τ i n ^ 2 : ℝ) : ℂ)) =
        fun n => ((τ i n : ℝ) : ℂ) * ((τ i n : ℝ) : ℂ) := by
      funext n; push_cast; ring
    rw [hfun, hL, mul_left_comm]
  · have h1c : ((τ i 1 : ℝ) : ℂ) = 1 := by exact_mod_cast h1 i hi
    have h0c : ((τ i 0 : ℝ) : ℂ) = 0 := by exact_mod_cast h0 i hi
    have hmult_c := ArithmeticHolographyOfTheModularHorizon.HalvingPairs.isMultiplicative_tauSqAF
      (hτ i hi) h1c h0c
    have hsq_c := ArithmeticHolographyOfTheModularHorizon.HalvingPairs.sq_eq_zeta_mul
      (hτ i hi) h1c h0c
    refine ⟨?_, fun n => ?_⟩
    · rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero] at hmult_c ⊢
      refine ⟨by simpa [realTauSqAF] using h1 i hi, fun {m n} hm hn hmn => ?_⟩
      have h := hmult_c.2 hm hn hmn
      exact Complex.ofReal_injective (by simpa [realTauSqAF,
        ArithmeticHolographyOfTheModularHorizon.HalvingPairs.tauSqAF] using h)
    · have hn_eq := congrArg (fun f : ArithmeticFunction ℂ => (f n).re) hsq_c
      simp only [ArithmeticFunction.pmul_apply,
        ArithmeticHolographyOfTheModularHorizon.HalvingPairs.tauAF_apply,
        ArithmeticFunction.coe_zeta_mul_apply,
        ArithmeticHolographyOfTheModularHorizon.HalvingPairs.tauSqAF_apply] at hn_eq
      have hre : (((∑ x ∈ n.divisors, (τ i (x ^ 2) : ℂ)) : ℂ)).re =
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * realTauSqAF (τ i) (h0 i hi)) n := by
        rw [ArithmeticFunction.coe_zeta_mul_apply, Complex.re_sum]
        exact sum_congr rfl fun x _ => Complex.ofReal_re _
      have hlhs : (((τ i n : ℂ) * (τ i n : ℂ))).re = τ i n ^ 2 := by
        rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
      rw [← hre, ← hn_eq, hlhs]
      exact sq_nonneg (τ i n)

/-! ### 1.5 Number fields under a counting measure -/

/-- Variable part `π_H − 1` of the permutation character of a subfield `L^H`. -/
def varPermChar {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (σ : G) : ℝ :=
  ArtinMertens.permChar H σ - 1

/-- **Number-field counting fixed-part theorem.** In any Galois closure `L/ℚ` with group `G`, every
intermediate field `L^H` has degree-one prime count `1 + varPermChar H (frob p) ≥ 0` at unramified
primes `p ∤ discr L`, where `classMean (varPermChar H) = 0`, and any counting or probability average
across subfields decomposes as `1 + Σ w_i · varPermChar (H i) (frob p)`. -/
theorem numberField_counting_fixedPart (L : Type*) [Field L] [NumberField L]
    {G : Type*} [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L]
    {frob : ℕ → G} (hfrob : ArtinMertens.IsFrobeniusChoice L frob)
    {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∑ i ∈ s, w i = 1) (H : ι → Subgroup G) :
    (∀ i, ArtinMertens.classMean (varPermChar (H i)) = 0) ∧
    (∀ i {p : ℕ}, p.Prime → ¬ (p : ℤ) ∣ NumberField.discr L →
      (ArtinMertens.degreeOneCount (ArtinMertens.invariantField L (H i)) p : ℝ) =
        1 + varPermChar (H i) (frob p) ∧
      0 ≤ 1 + varPermChar (H i) (frob p)) ∧
    (∀ {p : ℕ}, p.Prime → ¬ (p : ℤ) ∣ NumberField.discr L →
      ∑ i ∈ s, w i * (ArtinMertens.degreeOneCount (ArtinMertens.invariantField L (H i)) p : ℝ) =
        1 + ∑ i ∈ s, w i * varPermChar (H i) (frob p)) := by
  refine ⟨fun i => ?_, fun i {p} hp hd => ?_, fun {p} hp hd => ?_⟩
  · have hconst : ArtinMertens.classMean (fun _ : G => (1 : ℝ)) = 1 := by
      have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
      simp only [ArtinMertens.classMean, sum_const, card_univ, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hG.ne'
    have hsplit : varPermChar (H i) + (fun _ : G => (1 : ℝ)) = ArtinMertens.permChar (H i) := by
      funext σ; simp [varPermChar]
    have hm := congrArg ArtinMertens.classMean hsplit
    rw [ArtinMertens.classMean_add, hconst, ArtinMertens.classMean_permChar] at hm
    linarith
  · have heq := ArtinMertens.permChar_frob_eq hfrob (H i) hp hd
    have hdecomp : (ArtinMertens.degreeOneCount (ArtinMertens.invariantField L (H i)) p : ℝ) =
        1 + varPermChar (H i) (frob p) := by
      rw [← heq, varPermChar]; ring
    exact ⟨hdecomp, hdecomp ▸ Nat.cast_nonneg _⟩
  · have hterm : ∀ i ∈ s,
        w i * (ArtinMertens.degreeOneCount (ArtinMertens.invariantField L (H i)) p : ℝ) =
          w i + w i * varPermChar (H i) (frob p) := fun i _ => by
      rw [← ArtinMertens.permChar_frob_eq hfrob (H i) hp hd, varPermChar]; ring
    rw [sum_congr rfl hterm, sum_add_distrib, hw]

/-! ## Section 2. Moment decoupling, pushforward realizability, and mixture closure -/

/-- Exact binomial expansion of the `2k`-th moment of `c + V` on a probability space. -/
theorem integral_const_add_even_pow {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    (c : ℝ) {V : Ω → ℝ} {k : ℕ} (hV : ∀ j ≤ 2 * k, Integrable (fun ω => V ω ^ j) ρ) :
    Integrable (fun ω => (c + V ω) ^ (2 * k)) ρ ∧
      ∫ ω, (c + V ω) ^ (2 * k) ∂ρ =
        ∑ j ∈ range (2 * k + 1), ((2 * k).choose j : ℝ) * c ^ (2 * k - j) * ∫ ω, V ω ^ j ∂ρ := by
  have hexp : (fun ω => (c + V ω) ^ (2 * k)) =
      fun ω => ∑ j ∈ range (2 * k + 1), (((2 * k).choose j : ℝ) * c ^ (2 * k - j)) * V ω ^ j := by
    funext ω
    rw [add_comm c (V ω), add_pow]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hint_sum : ∀ j ∈ range (2 * k + 1),
      Integrable (fun ω => (((2 * k).choose j : ℝ) * c ^ (2 * k - j)) * V ω ^ j) ρ :=
    fun j hj => (hV j (Nat.lt_succ_iff.mp (mem_range.mp hj))).const_mul _
  refine ⟨hexp ▸ integrable_finsetSum _ hint_sum, ?_⟩
  rw [hexp, integral_finsetSum _ hint_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

/-- **Common-factor realizability and moment decoupling.** Let `(Ω, ρ)` be a probability space and
`V : Ω → ℝ` a measurable variable trace with `∫ V^j dρ = μ_j` (`0 ≤ j ≤ 2k`). Then for *every* real
value `c ∈ ℝ` (independently of `c_B(log p)`), the pushforward law `Measure.map (c + V ·) ρ` is a
probability measure on `ℝ` whose `2k`-th moment equals `Σ_{j=0}^{2k} C(2k, j) c^{2k − j} μ_j`.
Consequently, no moment identity or Hankel positivity inequality of `c + V` constrains `c`. -/
theorem commonFactor_moment_realizable_for_all_c {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    [IsProbabilityMeasure ρ] {V : Ω → ℝ} (hVm : Measurable V) {k : ℕ}
    (hVi : ∀ j ≤ 2 * k, Integrable (fun ω => V ω ^ j) ρ) {μ : ℕ → ℝ}
    (hμ : ∀ j ≤ 2 * k, ∫ ω, V ω ^ j ∂ρ = μ j) (c : ℝ) :
    IsProbabilityMeasure (Measure.map (fun ω => c + V ω) ρ) ∧
      ∫ t : ℝ, t ^ (2 * k) ∂(Measure.map (fun ω => c + V ω) ρ) =
        ∑ j ∈ range (2 * k + 1), ((2 * k).choose j : ℝ) * c ^ (2 * k - j) * μ j := by
  have hmap_meas : Measurable (fun ω => c + V ω) := measurable_const.add hVm
  refine ⟨Measure.isProbabilityMeasure_map hmap_meas.aemeasurable, ?_⟩
  rw [integral_map hmap_meas.aemeasurable (continuous_pow (2 * k)).aestronglyMeasurable,
    (integral_const_add_even_pow ρ c hVi).2]
  refine sum_congr rfl fun j hj => ?_
  rw [hμ j (Nat.lt_succ_iff.mp (mem_range.mp hj))]

/-- Quantitative `2k`-th moment bound for a fixed-part perturbation supported on a set `S` of
small `μ`-measure. -/
theorem abs_integral_vanishingMass_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {S : Set Ω} (hS : MeasurableSet S) {F V : Ω → ℝ} {M : ℝ}
    (k : ℕ) (hFV_int : Integrable (fun ω => (F ω + V ω) ^ (2 * k)) μ)
    (hV_int : Integrable (fun ω => V ω ^ (2 * k)) μ)
    (hoff : ∀ ω, ω ∉ S → F ω = 0)
    (hbFV : ∀ ω ∈ S, |F ω + V ω| ≤ M) (hbV : ∀ ω ∈ S, |V ω| ≤ M) :
    |(∫ ω, (F ω + V ω) ^ (2 * k) ∂μ) - ∫ ω, V ω ^ (2 * k) ∂μ| ≤
      2 * M ^ (2 * k) * μ.real S := by
  rw [← integral_sub hFV_int hV_int]
  have hbound : ∀ ω, |(F ω + V ω) ^ (2 * k) - V ω ^ (2 * k)| ≤
      S.indicator (fun _ => 2 * M ^ (2 * k)) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : |(F ω + V ω) ^ (2 * k)| ≤ M ^ (2 * k) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbFV ω hω) (2 * k)
      have h2 : |V ω ^ (2 * k)| ≤ M ^ (2 * k) := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbV ω hω) (2 * k)
      calc |(F ω + V ω) ^ (2 * k) - V ω ^ (2 * k)|
          ≤ |(F ω + V ω) ^ (2 * k)| + |V ω ^ (2 * k)| := abs_sub _ _
        _ ≤ M ^ (2 * k) + M ^ (2 * k) := add_le_add h1 h2
        _ = 2 * M ^ (2 * k) := by ring
    · rw [Set.indicator_of_notMem hω, hoff ω hω, zero_add, sub_self, abs_zero]
  have hind_int : Integrable (S.indicator fun _ => 2 * M ^ (2 * k)) μ :=
    (integrable_const _).indicator hS
  calc |(∫ ω, ((F ω + V ω) ^ (2 * k) - V ω ^ (2 * k)) ∂μ)|
      ≤ ∫ ω, |(F ω + V ω) ^ (2 * k) - V ω ^ (2 * k)| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm fun ω => (F ω + V ω) ^ (2 * k) - V ω ^ (2 * k)
    _ ≤ ∫ ω, S.indicator (fun _ => 2 * M ^ (2 * k)) ω ∂μ :=
        integral_mono (hFV_int.sub hV_int).abs hind_int hbound
    _ = 2 * M ^ (2 * k) * μ.real S := by
        rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

/-- **Mixture closure.** For any sequence of convex mixtures
`ν_n = (1 − λ_n) μ_n + λ_n ρ_n` (`0 ≤ λ_n ≤ 1`) of a vanishing-mass component `(μ_n, S_n)`
(`μ_n(S_n) → 0`) and a common-factor component `ρ_n` (`F = c` on the second component), the
mixture `2k`-th moment decomposes asymptotically into `(1 − λ_n) ∫ V_n^{2k} dμ_n + λ_n ∫ (c + W_n)^{2k} dρ_n`
with vanishing error as `n → ∞`. -/
theorem tendsto_mixture_moment_decomp {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : ℕ → Measure Ω₁) [∀ n, IsFiniteMeasure (μ n)]
    (ρ : ℕ → Measure Ω₂)
    {lam : ℕ → ℝ} (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n ≤ 1)
    {S : ℕ → Set Ω₁} (hS : ∀ n, MeasurableSet (S n))
    (hS_lim : Tendsto (fun n => (μ n).real (S n)) atTop (𝓝 0))
    {F V : ℕ → Ω₁ → ℝ} (W : ℕ → Ω₂ → ℝ) (c M : ℝ) (k : ℕ)
    (hFV_int : ∀ n, Integrable (fun ω => (F n ω + V n ω) ^ (2 * k)) (μ n))
    (hV_int : ∀ n, Integrable (fun ω => V n ω ^ (2 * k)) (μ n))
    (hoff : ∀ n ω, ω ∉ S n → F n ω = 0)
    (hbFV : ∀ n ω, ω ∈ S n → |F n ω + V n ω| ≤ M)
    (hbV : ∀ n ω, ω ∈ S n → |V n ω| ≤ M) :
    Tendsto (fun n =>
      ((1 - lam n) * ∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n) +
          lam n * ∫ ω, (c + W n ω) ^ (2 * k) ∂(ρ n)) -
        ((1 - lam n) * ∫ ω, V n ω ^ (2 * k) ∂(μ n) +
          lam n * ∫ ω, (c + W n ω) ^ (2 * k) ∂(ρ n))) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n => 2 * M ^ (2 * k) * (μ n).real (S n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hS_lim.const_mul (2 * M ^ (2 * k))
  refine squeeze_zero_norm (fun n => ?_) hmaj
  rw [Real.norm_eq_abs]
  have hsub : ((1 - lam n) * ∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n) +
        lam n * ∫ ω, (c + W n ω) ^ (2 * k) ∂(ρ n)) -
      ((1 - lam n) * ∫ ω, V n ω ^ (2 * k) ∂(μ n) +
        lam n * ∫ ω, (c + W n ω) ^ (2 * k) ∂(ρ n)) =
      (1 - lam n) * ((∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n)) -
        ∫ ω, V n ω ^ (2 * k) ∂(μ n)) := by ring
  rw [hsub, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hlam1 n))]
  have h1 : 1 - lam n ≤ 1 := by linarith [hlam0 n]
  calc (1 - lam n) * |(∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n)) - ∫ ω, V n ω ^ (2 * k) ∂(μ n)|
      ≤ 1 * |(∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n)) - ∫ ω, V n ω ^ (2 * k) ∂(μ n)| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |(∫ ω, (F n ω + V n ω) ^ (2 * k) ∂(μ n)) - ∫ ω, V n ω ^ (2 * k) ∂(μ n)| := one_mul _
    _ ≤ 2 * M ^ (2 * k) * (μ n).real (S n) :=
        abs_integral_vanishingMass_sub_le (μ n) (hS n) k (hFV_int n) (hV_int n) (hoff n)
          (hbFV n) (hbV n)

/-! ## Section 3. Jensen–Minkowski coercivity and the RH equivalence for cover-family moments -/

/-- **Even-power tangent inequality** (via weighted AM–GM): for `k ≥ 1` and all `c, v ∈ ℝ`,
`c^{2k} + 2k · c^{2k − 1} · v ≤ (c + v)^{2k}`. -/
theorem even_pow_tangent_le {k : ℕ} (hk : 1 ≤ k) (c v : ℝ) :
    c ^ (2 * k) + (2 * k : ℝ) * c ^ (2 * k - 1) * v ≤ (c + v) ^ (2 * k) := by
  set m : ℕ := 2 * k
  have hm1 : 1 ≤ m := by omega
  have hm_ne : m ≠ 0 := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set w₁ : ℝ := 1 / (m : ℝ)
  set w₂ : ℝ := ((m - 1 : ℕ) : ℝ) / (m : ℝ)
  have hw₁ : 0 ≤ w₁ := by positivity
  have hw₂ : 0 ≤ w₂ := by positivity
  have hw_sum : w₁ + w₂ = 1 := by
    dsimp only [w₁, w₂]
    rw [← add_div, Nat.cast_sub hm1, Nat.cast_one, add_sub_cancel, div_self hm_pos.ne']
  have hgm := Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂
    (pow_nonneg (abs_nonneg (c + v)) m) (pow_nonneg (abs_nonneg c) m) hw_sum
  have hr1 : (|c + v| ^ m) ^ w₁ = |c + v| := by
    dsimp only [w₁]
    rw [one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) hm_ne]
  have hr2 : (|c| ^ m) ^ w₂ = |c| ^ (m - 1) := by
    have hexp : w₂ = (m : ℝ)⁻¹ * ((m - 1 : ℕ) : ℝ) := by dsimp only [w₂]; ring
    rw [hexp, Real.rpow_mul (pow_nonneg (abs_nonneg c) m),
      Real.pow_rpow_inv_natCast (abs_nonneg _) hm_ne, Real.rpow_natCast]
  have habs_cv : |c + v| ^ m = (c + v) ^ m := by
    dsimp only [m]; rw [pow_mul, pow_mul, sq_abs]
  have habs_c : |c| ^ m = c ^ m := by
    dsimp only [m]; rw [pow_mul, pow_mul, sq_abs]
  rw [hr1, hr2, habs_cv, habs_c] at hgm
  have hlin : c ^ m + c ^ (m - 1) * v ≤ |c + v| * |c| ^ (m - 1) := by
    have heq : (c + v) * c ^ (m - 1) = c ^ m + c ^ (m - 1) * v := by
      rw [add_mul, ← pow_succ', Nat.sub_add_cancel hm1, mul_comm v]
    calc c ^ m + c ^ (m - 1) * v = (c + v) * c ^ (m - 1) := heq.symm
      _ ≤ |(c + v) * c ^ (m - 1)| := le_abs_self _
      _ = |c + v| * |c| ^ (m - 1) := by rw [abs_mul, abs_pow]
  have hcomb := hlin.trans hgm
  have hmul := mul_le_mul_of_nonneg_left hcomb hm_pos.le
  have hrhs : (m : ℝ) * (w₁ * (c + v) ^ m + w₂ * c ^ m) =
      (c + v) ^ m + ((m - 1 : ℕ) : ℝ) * c ^ m := by
    dsimp only [w₁, w₂]
    field_simp
  rw [hrhs, Nat.cast_sub hm1, Nat.cast_one] at hmul
  have hm_cast : (m : ℝ) = 2 * (k : ℝ) := by dsimp only [m]; push_cast; ring
  rw [hm_cast] at hmul
  linarith

/-- **Jensen lower bound for zero-mean variable traces.** On any probability space `(Ω, ρ)`, if
`∫ V dρ = 0`, then `c^{2k} ≤ ∫ (c + V)^{2k} dρ` for every `k ≥ 1` and `c ∈ ℝ`. -/
theorem pow_two_mul_le_integral_add_of_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] {k : ℕ} (hk : 1 ≤ k) (c : ℝ) {V : Ω → ℝ}
    (hV : Integrable V ρ) (hFV : Integrable (fun ω => (c + V ω) ^ (2 * k)) ρ)
    (hmean : ∫ ω, V ω ∂ρ = 0) :
    c ^ (2 * k) ≤ ∫ ω, (c + V ω) ^ (2 * k) ∂ρ := by
  have hlin_int : Integrable (fun ω => c ^ (2 * k) + (2 * k : ℝ) * c ^ (2 * k - 1) * V ω) ρ :=
    (integrable_const _).add (hV.const_mul _)
  have hle := integral_mono hlin_int hFV (fun ω => even_pow_tangent_le hk c (V ω))
  rw [integral_add (integrable_const _) (hV.const_mul _), integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_zero, add_zero] at hle
  exact hle

/-- Elementary even-power Minkowski bound `(c + v)^{2k} ≤ 2^{2k} (c^{2k} + v^{2k})`. -/
theorem add_pow_two_mul_le (k : ℕ) (c v : ℝ) :
    (c + v) ^ (2 * k) ≤ (2 : ℝ) ^ (2 * k) * (c ^ (2 * k) + v ^ (2 * k)) := by
  have heven : ∀ x : ℝ, x ^ (2 * k) = |x| ^ (2 * k) := fun x => by
    rw [pow_mul, pow_mul, sq_abs]
  rw [heven (c + v), heven c, heven v]
  rcases le_total |c| |v| with hcv | hvc
  · have h1 : |c + v| ≤ 2 * |v| := (abs_add_le c v).trans (by linarith)
    calc |c + v| ^ (2 * k) ≤ (2 * |v|) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) h1 (2 * k)
      _ = (2 : ℝ) ^ (2 * k) * |v| ^ (2 * k) := mul_pow 2 |v| (2 * k)
      _ ≤ (2 : ℝ) ^ (2 * k) * (|c| ^ (2 * k) + |v| ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  · have h1 : |c + v| ≤ 2 * |c| := (abs_add_le c v).trans (by linarith)
    calc |c + v| ^ (2 * k) ≤ (2 * |c|) ^ (2 * k) :=
          pow_le_pow_left₀ (abs_nonneg _) h1 (2 * k)
      _ = (2 : ℝ) ^ (2 * k) * |c| ^ (2 * k) := mul_pow 2 |c| (2 * k)
      _ ≤ (2 : ℝ) ^ (2 * k) * (|c| ^ (2 * k) + |v| ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)

/-- The real part of the twisted window trace has zero Haar mean. -/
theorem integral_re_fibreTrace_eq_zero (g : ℝ → ℝ) (R u : ℝ) :
    ∫ x, (fibreTrace g R u x).re ∂gaugeHaar = 0 := by
  have hint : Integrable (fibreTrace g R u) gaugeHaar :=
    (continuous_fibreTrace g R u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmean : ∫ x, fibreTrace g R u x ∂gaugeHaar = 0 := by
    unfold fibreTrace windowPrimes
    rw [integral_twistSum (fun p hp => (Nat.mem_primesLE.mp hp).2.ne_zero),
      if_neg (fun h1 => Nat.not_prime_one (Nat.mem_primesLE.mp h1).2)]
  have hre := Complex.reCLM.integral_comp_comm hint
  change ∫ x, (fibreTrace g R u x).re ∂gaugeHaar = (∫ x, fibreTrace g R u x ∂gaugeHaar).re at hre
  rw [hre, hmean, Complex.zero_re]

/-- **Cover-family tensor moments are equivalent to the Riemann Hypothesis (closing B142).**
For every bounded window `g` (`|g| ≤ 1`, `R ≥ 0`), forming a cover family over `(GaugeTorus, gaugeHaar)`
with total prime trace `c(p) + Re T_x(log p)` (`c(p) = 2 Re S(log p)` the trace of `ζ`), the
family `2k`-th prime-trace moments have sublinear exponent `1 + o(k)` if and only if
`RiemannHypothesis` holds. Uniform tensor-power bounds on a cover family containing `ζ` do not
bypass RH: they are unconditionally equivalent to RH. -/
theorem riemannHypothesis_iff_coverFamily_tensorExponent_sublinear {g : ℝ → ℝ}
    (hg : ∀ v, |g v| ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∃ C : ℝ, ∀ N : ℕ,
        ∑ p ∈ (range (N + 1)).filter Nat.Prime,
          Real.log p * (∫ x, (2 * (lagStructure zetaZeroConfig
            (boxSpline 1 3) (Real.log p)).re +
              (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar) ≤
          C * ((N : ℝ) + 1) ^ (1 + ε * k) := by
  set tr0 : ℕ → ℝ := fun p =>
    2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re
  constructor
  · intro hRH ε hε
    obtain ⟨A, hA⟩ := riemannHypothesis_iff_moments_primeTraces.mp hRH
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (|A| / ε)
    filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
    have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hεk : 0 < ε * k := mul_pos hε hk_pos
    obtain ⟨C₀, hC₀⟩ := hA k hk1
    have hAk : A ≤ ε * k := by
      have hdiv : |A| / ε ≤ k := hk₀.trans (by exact_mod_cast (le_max_left _ _).trans hk)
      linarith [(div_le_iff₀ hε).mp hdiv, le_abs_self A]
    -- Bound the variable family moment by `C_var * (N + 1)^{1 + ε k}`
    set L : ℝ := Real.log 4 * Real.exp R
    set C_var : ℝ := Real.log 4 * k.factorial * (L * (1 / ε + R)) ^ k
    refine ⟨(2 : ℝ) ^ (2 * k) * (|C₀| + C_var), fun N => ?_⟩
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    -- Pointwise upper bound on each prime `p ≤ N` via `add_pow_two_mul_le`
    have hpt : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
        Real.log p * (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar) ≤
          (2 : ℝ) ^ (2 * k) * (Real.log p * tr0 p ^ (2 * k) +
            Real.log p * ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) := by
      intro p hp
      have hpp := (mem_filter.mp hp).2
      have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have hcont_re : Continuous fun x => (fibreTrace g R (Real.log p) x).re :=
        Complex.continuous_re.comp (continuous_fibreTrace g R (Real.log p))
      have hint_lhs : Integrable (fun x =>
          (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k)) gaugeHaar :=
        ((continuous_const.add hcont_re).pow (2 * k)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint_norm : Integrable (fun x =>
          ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)) gaugeHaar :=
        ((continuous_fibreTrace g R (Real.log p)).norm.pow (2 * k)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint_rhs : Integrable (fun x =>
          (2 : ℝ) ^ (2 * k) * (tr0 p ^ (2 * k) + ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)))
          gaugeHaar :=
        ((integrable_const _).add hint_norm).const_mul _
      have hint_le : (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar) ≤
          (2 : ℝ) ^ (2 * k) * (tr0 p ^ (2 * k) +
            ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) := by
        calc (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar)
            ≤ ∫ x, (2 : ℝ) ^ (2 * k) *
                (tr0 p ^ (2 * k) + ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)) ∂gaugeHaar := by
              refine integral_mono hint_lhs hint_rhs fun x => ?_
              refine (add_pow_two_mul_le k (tr0 p) _).trans
                (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity))
              rw [pow_mul, pow_mul, ← sq_abs]
              exact pow_le_pow_left₀ (sq_nonneg _)
                (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2) k
          _ = (2 : ℝ) ^ (2 * k) * (tr0 p ^ (2 * k) +
                ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) := by
              rw [integral_const_mul, integral_add (integrable_const _) hint_norm,
                integral_const, probReal_univ, one_smul]
      calc Real.log p * (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar)
          ≤ Real.log p * ((2 : ℝ) ^ (2 * k) * (tr0 p ^ (2 * k) +
              ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar)) :=
            mul_le_mul_of_nonneg_left hint_le hlog0
        _ = (2 : ℝ) ^ (2 * k) * (Real.log p * tr0 p ^ (2 * k) +
              Real.log p * ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) := by ring
    -- Bound the `ζ` part
    have hbase_le : primeTraceMoment k N ≤ |C₀| * ((N : ℝ) + 1) ^ (1 + ε * k) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · have h0 : primeTraceMoment k 0 = 0 := by
          simp [primeTraceMoment, Finset.range_one, Finset.filter_singleton, Nat.not_prime_zero]
        rw [h0]
        positivity
      · have hN_ge1 : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
        calc primeTraceMoment k N ≤ C₀ * (N : ℝ) ^ (1 + A) := hC₀ N
          _ ≤ |C₀| * (N : ℝ) ^ (1 + A) :=
              mul_le_mul_of_nonneg_right (le_abs_self C₀) (by positivity)
          _ ≤ |C₀| * (N : ℝ) ^ (1 + ε * k) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN_ge1 (by linarith))
                (abs_nonneg C₀)
          _ ≤ |C₀| * ((N : ℝ) + 1) ^ (1 + ε * k) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) (by positivity))
                (abs_nonneg C₀)
    -- Bound the variable family part via `integral_fibreMoment_le`
    have hset_eq : (range (N + 1)).filter Nat.Prime = Nat.primesLE N := by
      ext p
      simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.mem_primesLE]
    have hvar_eq : (∑ p ∈ (range (N + 1)).filter Nat.Prime,
        Real.log p * ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) =
        ∫ x, fibreMoment g R k N x ∂gaugeHaar := by
      rw [hset_eq]
      unfold fibreMoment
      rw [integral_finsetSum (f := fun p x =>
        Real.log p * ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k)) _ fun p _ =>
        (continuous_const.mul ((continuous_fibreTrace g R _).norm.pow _)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)]
      exact sum_congr rfl fun p _ => (integral_const_mul _ _).symm
    have hlog_le : Real.log N + R ≤ (1 / ε + R) * ((N : ℝ) + 1) ^ ε := by
      have h1 : Real.log N ≤ ((N : ℝ) + 1) ^ ε / ε :=
        (Real.log_le_rpow_div (Nat.cast_nonneg N) hε).trans
          (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hε.le)
            hε.le)
      have h2 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ ε := Real.one_le_rpow hN1 hε.le
      calc Real.log N + R ≤ ((N : ℝ) + 1) ^ ε / ε + R * ((N : ℝ) + 1) ^ ε :=
            add_le_add h1 (le_mul_of_one_le_right hR h2)
        _ = (1 / ε + R) * ((N : ℝ) + 1) ^ ε := by ring
    have hlog0 : 0 ≤ Real.log N + R := by
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · simp [hR]
      · linarith [Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN_pos)]
    have hvar_le : ∫ x, fibreMoment g R k N x ∂gaugeHaar ≤ C_var * ((N : ℝ) + 1) ^ (1 + ε * k) := by
      refine (integral_fibreMoment_le hg hR k N).trans ?_
      have hpow : (L * (Real.log N + R)) ^ k ≤
          (L * (1 / ε + R)) ^ k * ((N : ℝ) + 1) ^ (ε * k) := by
        calc (L * (Real.log N + R)) ^ k
            ≤ (L * ((1 / ε + R) * ((N : ℝ) + 1) ^ ε)) ^ k :=
              pow_le_pow_left₀ (mul_nonneg (by positivity) hlog0)
                (mul_le_mul_of_nonneg_left hlog_le (by positivity)) k
          _ = (L * (1 / ε + R)) ^ k * (((N : ℝ) + 1) ^ ε) ^ k := by
              rw [← mul_assoc, mul_pow]
          _ = (L * (1 / ε + R)) ^ k * ((N : ℝ) + 1) ^ (ε * k) := by
              rw [← Real.rpow_natCast (((N : ℝ) + 1) ^ ε) k, ← Real.rpow_mul (by positivity)]
      have hN_le : (N : ℝ) ≤ ((N : ℝ) + 1) ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
      calc Real.log 4 * (N : ℝ) * (k.factorial * (L * (Real.log N + R)) ^ k)
          ≤ Real.log 4 * ((N : ℝ) + 1) ^ (1 : ℝ) *
              (k.factorial * ((L * (1 / ε + R)) ^ k * ((N : ℝ) + 1) ^ (ε * k))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hN_le (Real.log_nonneg (by norm_num)))
              (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _))
              (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (by positivity) hlog0) k))
              (by positivity)
        _ = C_var * (((N : ℝ) + 1) ^ (1 : ℝ) * ((N : ℝ) + 1) ^ (ε * k)) := by
            dsimp only [C_var]; ring
        _ = C_var * ((N : ℝ) + 1) ^ (1 + ε * k) := by
            rw [← Real.rpow_add (by positivity)]
    calc ∑ p ∈ (range (N + 1)).filter Nat.Prime,
          Real.log p * (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar)
        ≤ ∑ p ∈ (range (N + 1)).filter Nat.Prime,
            (2 : ℝ) ^ (2 * k) * (Real.log p * tr0 p ^ (2 * k) +
              Real.log p * ∫ x, ‖fibreTrace g R (Real.log p) x‖ ^ (2 * k) ∂gaugeHaar) :=
          sum_le_sum hpt
      _ = (2 : ℝ) ^ (2 * k) * (primeTraceMoment k N + ∫ x, fibreMoment g R k N x ∂gaugeHaar) := by
          rw [← mul_sum, sum_add_distrib, ← hvar_eq]; rfl
      _ ≤ (2 : ℝ) ^ (2 * k) *
            (|C₀| * ((N : ℝ) + 1) ^ (1 + ε * k) + C_var * ((N : ℝ) + 1) ^ (1 + ε * k)) :=
          mul_le_mul_of_nonneg_left (add_le_add hbase_le hvar_le) (by positivity)
      _ = (2 : ℝ) ^ (2 * k) * (|C₀| + C_var) * ((N : ℝ) + 1) ^ (1 + ε * k) := by ring
  · intro hfam
    -- By Jensen coercivity, each prime's family `2k`-th moment dominates `tr0 p ^ (2k)`
    rw [riemannHypothesis_iff_zetaZeroWidth_le_zero]
    refine le_of_forall_pos_le_add fun η hη => ?_
    set ε : ℝ := min η (1 / 2)
    have hε : 0 < ε := lt_min hη (by norm_num)
    have hεη : ε ≤ η := min_le_left _ _
    have hε2 : ε ≤ 1 / 2 := min_le_right _ _
    obtain ⟨k₀, hk₀⟩ := exists_nat_ge (1 / η + 3)
    obtain ⟨k, ⟨C, hC⟩, hk⟩ := ((hfam ε hε).and (eventually_ge_atTop (max k₀ 1))).exists
    have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
    have hkR : 1 / η + 3 ≤ (k : ℝ) := hk₀.trans (by exact_mod_cast (le_max_left _ _).trans hk)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hpm_le : ∀ p : ℕ, p.Prime →
        Real.log p * tr0 p ^ (2 * k) ≤ |C| * (2 : ℝ) ^ (1 + ε * k) * (p : ℝ) ^ (1 + ε * k) := by
      intro p hp
      have hcont_re : Continuous fun x => (fibreTrace g R (Real.log p) x).re :=
        Complex.continuous_re.comp (continuous_fibreTrace g R (Real.log p))
      have hV_int : Integrable (fun x => (fibreTrace g R (Real.log p) x).re) gaugeHaar :=
        hcont_re.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hFV_int : Integrable (fun x =>
          (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k)) gaugeHaar :=
        ((continuous_const.add hcont_re).pow (2 * k)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hjensen := pow_two_mul_le_integral_add_of_integral_eq_zero gaugeHaar hk1 (tr0 p)
        hV_int hFV_int (integral_re_fibreTrace_eq_zero g R (Real.log p))
      have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have hmem : p ∈ (range (p + 1)).filter Nat.Prime :=
        mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_self p), hp⟩
      have hone : Real.log p *
          (∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar) ≤
            C * ((p : ℝ) + 1) ^ (1 + ε * k) := by
        refine (single_le_sum (fun q hq => mul_nonneg
          (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hq).2.one_lt.le))
          (integral_nonneg fun x => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _))
          hmem).trans (hC p)
      have hp1_le : ((p : ℝ) + 1) ^ (1 + ε * k) ≤ (2 : ℝ) ^ (1 + ε * k) * (p : ℝ) ^ (1 + ε * k) := by
        rw [← Real.mul_rpow zero_le_two (Nat.cast_nonneg p)]
        have hp_ge1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      calc Real.log p * tr0 p ^ (2 * k)
          ≤ Real.log p *
              ∫ x, (tr0 p + (fibreTrace g R (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar :=
            mul_le_mul_of_nonneg_left hjensen hlog0
        _ ≤ C * ((p : ℝ) + 1) ^ (1 + ε * k) := hone
        _ ≤ |C| * ((p : ℝ) + 1) ^ (1 + ε * k) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((2 : ℝ) ^ (1 + ε * k) * (p : ℝ) ^ (1 + ε * k)) :=
            mul_le_mul_of_nonneg_left hp1_le (abs_nonneg C)
        _ = |C| * (2 : ℝ) ^ (1 + ε * k) * (p : ℝ) ^ (1 + ε * k) := by ring
    -- Extract the prime-degree trace bound of exponent `a = (1 + ε k) / (2k) < ½`
    set a : ℝ := (1 + ε * k) / (2 * k)
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a < 1 / 2 := by
      dsimp only [a]
      rw [div_lt_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hε2 hk0.le
      have : 0 < 1 / η := by positivity
      linarith
    have hw : zetaZeroWidth ≤ a := by
      rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha1]
      set B : ℝ := |C| * (2 : ℝ) ^ (1 + ε * k) / Real.log 2
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hB0 : 0 ≤ B := by dsimp only [B]; positivity
      refine ⟨B ^ ((1 : ℝ) / (2 * k)), fun p hp => ?_⟩
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hlogp : Real.log 2 ≤ Real.log p :=
        Real.log_le_log zero_lt_two (by exact_mod_cast hp.two_le)
      have hc2k : |tr0 p| ^ (2 * k) ≤ B * (p : ℝ) ^ (1 + ε * k) := by
        rw [show |tr0 p| ^ (2 * k) = tr0 p ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
        have h1 : Real.log 2 * tr0 p ^ (2 * k) ≤ Real.log p * tr0 p ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hlogp (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
        have h2 := hpm_le p hp
        dsimp only [B]
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        linarith
      have hroot : |tr0 p| ≤ B ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ a := by
        have hk_ne : (k : ℝ) ≠ 0 := hk0.ne'
        have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg (tr0 p)),
          show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
          Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
        dsimp only [a]
        convert h1 using 3
        ring
      linarith [neg_abs_le (tr0 p)]
    have hsplit : a = 1 / (2 * (k : ℝ)) + ε / 2 := by
      have hk_ne : (k : ℝ) ≠ 0 := hk0.ne'
      dsimp only [a]; field_simp
    have hinv : 1 / (2 * (k : ℝ)) ≤ η / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hηk : 1 / η ≤ k := by linarith
      rw [div_le_iff₀ hη] at hηk
      calc (1 : ℝ) ≤ (k : ℝ) * η := hηk
        _ = η / 2 * (2 * (k : ℝ)) := by ring
    linarith

/-- **Master theorem: The zero motive of `ζ` is the fixed part of every arithmetic family `(FP)`.**
Unconditionally packages the complete answer to Question 5.2 and its corollaries:
1. *Amplified monodromy symmetry-breaking:* at `0` (`ζ`), every amplified `2k`-th moment satisfies
   `ν{0} |A(0)|² (Σ a_n)^{2k} ≤ ∫ |A|² |S|^{2k} dν`, while off `0` amplification strictly beats
   `(Σ a_n)^{2k}` under exact orthonormality (`exists_amplified_orthonormal_strict_saving`).
2. *Vanishing mass across pure families:* the fixed-part locus has mass `0` on `GaugeTorus`,
   `Q / Σ_{q ≤ Q} φ(q) → 0` across Dirichlet characters, `≤ H / T → 0` on the vertical line, and
   `r / cuspCount Λ → 0` across Weyl cuspidal eigenforms.
3. *One-way product-positivity non-transfer:* for every nontrivial exponent `a < 1/2` and every
   positively `ζ`-coupled variable cofactor `(g, lamVar)`, there exists a simple-pole Euler weight
   `(dBase, wBase)` preserving all product nonnegativity conditions and violating the `p^a` bound
   on `|archPoleWindow p − primeWindowOf wBase p|` (which equals `|c_B(log p)|` at `wBase = Λ`).
4. *Cover-family RH equivalence:* for `g = 1` and `R = 1`, sublinear `2k`-th prime-trace moment
   exponents across the gauge cover family hold if and only if `RiemannHypothesis` holds. -/
theorem zeroMotive_is_fixedPart_of_every_arithmeticFamily :
    (∀ (ν : Measure GaugeTorus) [IsFiniteMeasure ν] (s : Finset ℕ) (a : ℕ → ℝ),
      (∀ n ∈ s, 0 ≤ a n) → ∀ (A : GaugeTorus → ℂ), Continuous A → ∀ k : ℕ,
        ν.real {0} * ‖A 0‖ ^ 2 * (∑ n ∈ s, a n) ^ (2 * k) ≤
          ∫ x, ‖A x‖ ^ 2 * ‖twistSum s (fun n => (a n : ℂ)) x‖ ^ (2 * k) ∂ν) ∧
    (∃ (ν : Measure GaugeTorus) (_ : IsProbabilityMeasure ν) (x₀ : GaugeTorus)
      (A : GaugeTorus → ℂ),
      x₀ ≠ 0 ∧ Continuous A ∧ TwistOrthonormalOn ν ({4, 6, 9} : Finset ℕ) ∧
      (∫ x, ‖A x‖ ^ 2 * ‖twistSum ({2, 3} : Finset ℕ) (fun _ => (1 : ℂ)) x‖ ^ 2 ∂ν) <
        ν.real {x₀} * ‖A x₀‖ ^ 2 * (∑ _n ∈ ({2, 3} : Finset ℕ), (1 : ℝ)) ^ 2) ∧
    (gaugeHaar {(0 : GaugeTorus)} = 0 ∧
      Tendsto (fun Q : ℕ => (Q : ℝ) / ∑ q ∈ Icc 1 Q, (q.totient : ℝ)) atTop (𝓝 0) ∧
      (∀ H : ℝ, 0 ≤ H →
        Tendsto (fun T : ℝ => (verticalHeightMeasure T).real (Set.Icc (-H) H)) atTop (𝓝 0)) ∧
      (∀ r : ℕ, Tendsto (fun L : ℝ => (r : ℝ) / (BlackHoleRingdown.cuspCount L : ℝ)) atTop (𝓝 0))) ∧
    (∀ (g : ArithmeticFunction ℝ),
      (∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n) →
      ∀ (lamVar : ℕ → ℝ), (∀ n : ℕ, 0 ≤ (Λ n : ℝ) + lamVar n) →
      ∀ a : ℝ, a < 1 / 2 →
        ∃ (dBase : ArithmeticFunction ℝ) (wBase : ℕ → ℝ),
          dBase.IsMultiplicative ∧
          Summable (fun n : ℕ => (wBase n - (Λ n : ℝ)) * (n : ℝ) ^ (-1 : ℝ)) ∧
          (∀ n : ℕ, 0 ≤ (dBase * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g)) n) ∧
          (∀ n : ℕ, 0 ≤ wBase n + lamVar n) ∧
          ¬ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
            |archPoleWindow p - primeWindowOf wBase p| ≤ K * (p : ℝ) ^ a) ∧
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∃ C : ℝ, ∀ N : ℕ,
        ∑ p ∈ (range (N + 1)).filter Nat.Prime,
          Real.log p * (∫ x, (2 * (lagStructure zetaZeroConfig
            (boxSpline 1 3) (Real.log p)).re +
              (fibreTrace (fun _ => 1) 1 (Real.log p) x).re) ^ (2 * k) ∂gaugeHaar) ≤
          C * ((N : ℝ) + 1) ^ (1 + ε * k)) := by
  refine ⟨fun ν _ s a ha A hA k => measureReal_singleton_zero_mul_amplified_pow_le ν s ha hA k, ?_,
    ⟨gaugeHaar_singleton_zero, tendsto_cumulative_principal_fraction,
      fun H hH => tendsto_verticalHeightMeasure_Icc hH, tendsto_weyl_finiteMode_mass⟩,
    fun g hg lamVar hlam a ha => no_reverse_weight_bound_from_product_positivity hg hlam ha,
    riemannHypothesis_iff_coverFamily_tensorExponent_sublinear (fun _ => by norm_num) zero_le_one⟩
  obtain ⟨ν, hprob, x₀, A, hx₀, hA, _, horth, hlt⟩ := exists_amplified_orthonormal_strict_saving
  exact ⟨ν, hprob, x₀, A, hx₀, hA, horth, hlt⟩

end GaloisForLFunctions.ArithmeticWeightTheory
