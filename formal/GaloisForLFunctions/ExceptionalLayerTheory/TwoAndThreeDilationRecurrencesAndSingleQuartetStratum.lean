import GaloisForLFunctions.ZeroConfigurationGeometry.TwoClockDilationAliasingAndThreePrimePinning
import GaloisForLFunctions.ZeroConfigurationGeometry.PrimeErrorFiniteOscillationRigidityAndSignChanges
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExceptionalLayerTheory.SingleQuartetLindelofCosineAndQuotientLaguerrePolya
import GaloisForLFunctions.ExceptionalLayerTheory.TheSingleQuartetWaveInAdjacentPrimeCounts
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.UnconditionalSubSquareRootSinglePairFirewall

/-!
# Two- and Three-Clock Prime-Error Dilation Recurrences and the Single-Quartet Stratum

For `E(x) = ψ(x) − x`, `1/2 < β < 1`, `γ > 0`, and multiplicative clock `a > 1`, consider the
forward single-frequency second-order dilation residual

`R_a(β, γ; x) = E(a² x) − 2 a^β cos(γ log a) E(a x) + a^{2β} E(x)`.

This module gives the complete unconditional characterization of simultaneous `O(√x log² x)`
bounds for `R_a` on two prime clocks `{2, 3}` and on three prime clocks `{2, 3, 5}`, together with
all zero-configuration, spectral-index, Lindelöf, adjacent-cofactor, and model-realization
corollaries:

1. **Exact pointwise classification for two clocks `{2, 3}` and three clocks `{2, 3, 5}`**
   (`singleQuartet_obeys_all_dilation_recurrences`,
   `twoThreeAliasedQuartets_obey_two_and_three_not_five`,
   `twoClock_bounded_and_limsup_iff`, `twoClock_nonCrossResonant_iff_singleQuartet`,
   `threeClock_bounded_and_limsup_iff`):
   - For `1/2 < β < 1` and `γ > 0`, `HasPositivePowerLimsup primeError β` holds jointly with
     `O(√x log² x)` bounds on both `R_2(β, γ)` and `R_3(β, γ)` if and only if either
     `HasSingleOffLineQuartet (β + iγ)` holds, or `γ` admits its unique `(2, 3)` cross-resonant
     partner `ω > 67` (`IsCrossResonantPair 2 3 γ ω`) and `ζ` satisfies either
     `HasSingleOffLineQuartet (β + iω)` or the two-quartet cross-aliased configuration
     `HasTwoThreeAliasedQuartets β γ ω`.
   - Under `HasTwoThreeAliasedQuartets β γ ω`, both `R_2(β, γ)` and `R_3(β, γ)` are
     `O(√x log² x)` while `|R_5(β, γ; x)| / (√x log² x)` is unbounded.
   - Adjoining clock `5` removes all cross-sign aliasing: for every `1/2 < β < 1` and `γ > 0`,
     joint `O(√x log² x)` bounds on `R_2, R_3, R_5` together with `HasPositivePowerLimsup` hold
     if and only if `HasSingleOffLineQuartet (β + iγ)`.

2. **Exact global equivalence and minimal off-line stratum laws**
   (`twoClockPrimeRecurrenceLaw_iff`, `threeClockPrimeRecurrenceLaw_iff`,
   `corollaries_of_twoClockPrimeRecurrenceLaw`):
   - Globally across all `1/2 < β < 1` and `γ > 0`, `TwoClockPrimeRecurrenceLaw` holds if and only
     if `ζ` has neither a single off-line quartet (`∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`) nor a
     `(2, 3)` cross-aliased double quartet (`∀ β γ ω, ¬ HasTwoThreeAliasedQuartets β γ ω`).
   - `ThreeClockPrimeRecurrenceLaw` is unconditionally equivalent to
     `∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`, hence to `RiemannHypothesis ∨ 4 ≤ #(rightZeros)`,
     `realPacketNegIndex ≠ 2`, three-rung confined Weil–Gram index growth under `¬ RH`, and
     universal exclusion of single-wave adjacent Vaughan cofactor errors.

3. **Unconditional Lindelöf / finite-stratum dichotomy and model firewall**
   (`twoClockPrimeRecurrenceLaw_of_not_finiteOffLine`,
   `twoClockPrimeRecurrenceLaw_of_not_lindelof`,
   `twoClockPrimeRecurrenceLaw_or_lindelof_finite_stratum`,
   `model_firewall_for_two_and_three_clocks`):
   Any failure of `FiniteOffLine`, `ZerosApproachLine`, or `LindelofCriticalLine` unconditionally
   forces `TwoClockPrimeRecurrenceLaw`. Thus either `TwoClockPrimeRecurrenceLaw` holds
   unconditionally, or `¬ RiemannHypothesis` coexists with all three forms of the Lindelöf
   conjecture, `FiniteOffLine`, and `realPacketNegIndex ∈ {2, 4}`. Conversely, planted aliased
   waves, `{0, 1, 2}`-prime Beurling edits with `c < 1/2`, over-regular Beurling zeta, and
   positive Euler twins realize single-quartet or cross-aliased waves whenever either `Λ ≥ 0` or
   the `Γ_ℝ` functional equation is relaxed.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### 1. Cross-aliased two-quartet stratum and global recurrence laws -/

/-- `ζ` has an isolated `(2, 3)` cross-aliased pair of off-line quartets on `Re s = β > 1/2`:
`0 < γ`, `IsCrossResonantPair 2 3 γ ω`, both `β + iγ` and `β + iω` are strip zeros of `ζ`, and the
off-line strip zeros of `ζ` are precisely `Q(β + iγ) ∪ Q(β + iω)`. -/
def HasTwoThreeAliasedQuartets (β γ ω : ℝ) : Prop :=
  1 / 2 < β ∧ 0 < γ ∧ IsCrossResonantPair 2 3 γ ω ∧
    ((β : ℂ) + I * γ) ∈ zetaZeroConfig.carrier ∧
    ((β : ℂ) + I * ω) ∈ zetaZeroConfig.carrier ∧
    {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} =
      zeroQuartetSet ((β : ℂ) + I * γ) ∪ zeroQuartetSet ((β : ℂ) + I * ω)

/-- Global two-clock `{2, 3}` prime-error dilation recurrence law across `1/2 < β < 1`, `γ > 0`. -/
def TwoClockPrimeRecurrenceLaw : Prop :=
  ∀ β γ : ℝ, 1 / 2 < β → β < 1 → 0 < γ →
    HasPositivePowerLimsup primeError β →
      IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∨
        IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ)

/-- Global three-clock `{2, 3, 5}` prime-error dilation recurrence law across `1/2 < β < 1`, `γ > 0`. -/
def ThreeClockPrimeRecurrenceLaw : Prop :=
  ∀ β γ : ℝ, 1 / 2 < β → β < 1 → 0 < γ →
    HasPositivePowerLimsup primeError β →
      IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∨
        IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∨
        IsSqrtLogSqUnbounded (primeDilationResidual 5 β γ)

/-! ### 2. Master finite-layer annihilation and positive `x^β` limsup lemmas -/

private theorem dilationRecurrenceOp_finset_sum {ι : Type*} (s : Finset ι) (a β γ : ℝ)
    (f : ι → ℝ → ℝ) (x : ℝ) :
    dilationRecurrenceOp a β γ (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, dilationRecurrenceOp a β γ (f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [dilationRecurrenceOp]
  | insert i s hi ih =>
    have hfun : (fun y => ∑ j ∈ insert i s, f j y) =
        fun y => f i y + ∑ j ∈ s, f j y := by
      funext y; exact Finset.sum_insert hi
    rw [hfun, dilationRecurrenceOp_add, ih, Finset.sum_insert hi]

private theorem xiZeroCopy_mem_carrier' (q : XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
    (xi_eq_zero_of_mem_divisor_support q.1)
  exact ⟨hζ, h0, h1⟩

private theorem mem_carrier_of_xi_eq_zero {z : ℂ} (hxi : xi z = 0) :
    z ∈ zetaZeroConfig.carrier := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  exact hq ▸ xiZeroCopy_mem_carrier' q

private theorem xi_eq_zero_of_mem_carrier {z : ℂ} (hz : z ∈ zetaZeroConfig.carrier) :
    xi z = 0 := by
  obtain ⟨hζ, h0, h1⟩ := hz
  have hne1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ

private theorem finite_xiZeroCopy_fiber' (z : ℂ) :
    Set.Finite {q : XiZeroCopy | (q.1 : ℂ) = z} := by
  by_cases hz : z ∈ (MeromorphicOn.divisor xi Set.univ).support
  · let ρ_s : XiDivisorSupport := ⟨z, hz⟩
    refine ((Set.finite_univ :
      Set.Finite (Set.univ : Set (Fin (((MeromorphicOn.divisor xi Set.univ) z).toNat)))).image
      (fun k => (⟨ρ_s, k⟩ : XiZeroCopy))).subset fun q hq => ?_
    have hρ : q.1 = ρ_s := Subtype.ext hq
    cases q with | mk ρ k =>
    dsimp only at hρ
    subst hρ
    exact ⟨k, Set.mem_univ k, rfl⟩
  · have hemp : {q : XiZeroCopy | (q.1 : ℂ) = z} = ∅ :=
      Set.eq_empty_of_forall_notMem fun q hq => hz (hq ▸ q.1.2)
    rw [hemp]
    exact Set.finite_empty

private theorem finite_xiZeroCopy_zeroQuartetSet (ρ₀ : ℂ) :
    Set.Finite {q : XiZeroCopy | (q.1 : ℂ) ∈ zeroQuartetSet ρ₀} := by
  refine (((finite_xiZeroCopy_fiber' ρ₀).union (finite_xiZeroCopy_fiber' (conj ρ₀))).union
    ((finite_xiZeroCopy_fiber' (1 - ρ₀)).union (finite_xiZeroCopy_fiber' (1 - conj ρ₀)))).subset
    fun q hmem => ?_
  simp only [zeroQuartetSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h2)
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

/-- **Master finite-layer recurrence bound.** If `ξ` has only finitely many off-line zero copies
and every right-of-line copy `q` (`1/2 < Re q`) satisfies `Re q = β` and
`cos(Im q · log a) = cos(γ log a)` (`a ≥ 1`), then `|R_a(β, γ; x)| / (√x log² x)` is bounded at
large `x`. -/
theorem not_isSqrtLogSqUnbounded_of_finite_and_cos_eq {a β γ : ℝ} (ha : 1 ≤ a)
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite)
    (hpin : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re →
      (q.1 : ℂ).re = β ∧ Real.cos ((q.1 : ℂ).im * Real.log a) = Real.cos (γ * Real.log a)) :
    ¬ IsSqrtLogSqUnbounded (primeDilationResidual a β γ) := by
  classical
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨K, hK0, hvk⟩ := RHTower.exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite hfin
  set S : Finset XiZeroCopy := hfin.toFinset
  set S_pos : Finset XiZeroCopy := S.filter fun q => 1 / 2 < (q.1 : ℂ).re
  set S_neg : Finset XiZeroCopy := S.filter fun q => ¬ 1 / 2 < (q.1 : ℂ).re
  let mode : XiZeroCopy → ℝ → ℝ := fun q y =>
    (((q.1 : ℂ)⁻¹) * (y : ℂ) ^ ((β : ℂ) + I * ((q.1 : ℂ).im : ℂ))).re
  let W_pos : ℝ → ℝ := fun y => ∑ q ∈ S_pos, mode q y
  let η : ℝ → ℝ := fun y => primeError y + W_pos y
  set K_neg : ℝ := ∑ q ∈ S_neg, ‖(q.1 : ℂ)‖⁻¹
  have hK_neg0 : 0 ≤ K_neg := Finset.sum_nonneg fun q _ => inv_nonneg.mpr (norm_nonneg _)
  have hη_bound : ∀ x : ℝ, 16 ≤ x →
      |η x| ≤ (K + K_neg) * Real.sqrt x * Real.log x ^ 2 := by
    intro x hx
    have hx_pos : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hlog2 : 1 ≤ Real.log x ^ 2 := by
      have h2 := RHTower.two_le_log_of_sixteen_le hx
      nlinarith
    have hsplit_wave : (RHTower.offLineWave S x).re =
        W_pos x + ∑ q ∈ S_neg, ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re := by
      unfold RHTower.offLineWave
      rw [Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not S (fun q => 1 / 2 < (q.1 : ℂ).re)]
      congr 1
      refine Finset.sum_congr rfl fun q hq => ?_
      have hre_q : (q.1 : ℂ).re = β := (hpin q (Finset.mem_filter.mp hq).2).1
      have hq_eq : (q.1 : ℂ) = (β : ℂ) + I * ((q.1 : ℂ).im : ℂ) := by
        apply Complex.ext <;> simp [hre_q]
      dsimp [mode]
      rw [← hq_eq, div_eq_mul_inv, mul_comm]
    have hη_eq : η x = (Chebyshev.psi x - x + (RHTower.offLineWave S x).re) -
        ∑ q ∈ S_neg, ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re := by
      dsimp [η, primeError]; rw [hsplit_wave]; ring
    have hneg_le : |∑ q ∈ S_neg, ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤
        K_neg * Real.sqrt x * Real.log x ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ q ∈ S_neg, |((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
          ≤ ∑ q ∈ S_neg, ‖(q.1 : ℂ)‖⁻¹ * Real.sqrt x * Real.log x ^ 2 := by
            refine Finset.sum_le_sum fun q hq => ?_
            have hle_half : (q.1 : ℂ).re ≤ 1 / 2 := not_lt.mp (Finset.mem_filter.mp hq).2
            have hq_pos : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
            have hcpow : |((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤
                ‖(q.1 : ℂ)‖⁻¹ * Real.sqrt x := by
              refine (Complex.abs_re_le_norm _).trans ?_
              rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, Real.sqrt_eq_rpow,
                div_eq_inv_mul]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hx1 hle_half) (inv_nonneg.mpr hq_pos.le)
            calc |((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
                ≤ (‖(q.1 : ℂ)‖⁻¹ * Real.sqrt x) * 1 := by linarith
              _ ≤ (‖(q.1 : ℂ)‖⁻¹ * Real.sqrt x) * Real.log x ^ 2 :=
                  mul_le_mul_of_nonneg_left hlog2 (by positivity)
              _ = ‖(q.1 : ℂ)‖⁻¹ * Real.sqrt x * Real.log x ^ 2 := by ring
        _ = K_neg * Real.sqrt x * Real.log x ^ 2 := by
            dsimp [K_neg]; rw [Finset.sum_mul, Finset.sum_mul]
    rw [hη_eq]
    calc |(Chebyshev.psi x - x + (RHTower.offLineWave S x).re) -
            ∑ q ∈ S_neg, ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re|
        ≤ |Chebyshev.psi x - x + (RHTower.offLineWave S x).re| +
            |∑ q ∈ S_neg, ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| := abs_sub _ _
      _ ≤ K * Real.sqrt x * Real.log x ^ 2 + K_neg * Real.sqrt x * Real.log x ^ 2 :=
          add_le_add (hvk x hx) hneg_le
      _ = (K + K_neg) * Real.sqrt x * Real.log x ^ 2 := by ring
  obtain ⟨C₁, X₁, _, hC₁⟩ :=
    abs_dilationRecurrenceOp_le_of_sqrt_log_sq (β := β) (γ := γ) ha (add_nonneg hK0 hK_neg0) hη_bound
  rw [isSqrtLogSqUnbounded_iff_not_eventually_le]
  push Not
  refine ⟨C₁, max X₁ 16, fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx16 : 16 ≤ x := (le_max_right _ _).trans hx
  have hx_pos : 0 < x := by linarith
  have hpe_eq : primeError = fun y => η y - W_pos y := by
    funext y; dsimp [η]; ring
  have hW_zero : dilationRecurrenceOp a β γ W_pos x = 0 := by
    dsimp [W_pos]
    rw [dilationRecurrenceOp_finset_sum]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hcos_q := (hpin q (Finset.mem_filter.mp hq).2).2
    exact dilationRecurrenceOp_re_cpow_eq_zero ha0 hx_pos hcos_q ((q.1 : ℂ)⁻¹)
  rw [primeDilationResidual, hpe_eq, dilationRecurrenceOp_sub, hW_zero, sub_zero]
  exact hC₁ x hx1

/-- **Master finite-layer `x^β` limsup law.** If `ξ` has only finitely many off-line zero copies,
`ζ` has a strip zero with real part `β > 1/2`, and no zero copy has real part exceeding `β`, then
`HasPositivePowerLimsup primeError β` holds (via bounded-logarithmic-gap sign changes). -/
theorem hasPositivePowerLimsup_of_finite_and_top_zero {β : ℝ} (hβ : 1 / 2 < β)
    (hfin : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier) (hre₀ : ρ₀.re = β)
    (hall : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → (q.1 : ℂ).re ≤ β) :
    HasPositivePowerLimsup primeError β := by
  have hΘ_ge : β ≤ zetaZeroAbscissa := by
    have h := re_le_zetaZeroAbscissa hρ₀.1
    rwa [hre₀] at h
  have hΘ_le : zetaZeroAbscissa ≤ β := by
    refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hβ.le fun q => ?_
    rcases le_or_gt (q.1 : ℂ).re (1 / 2) with hle | hgt
    · exact hle.trans hβ.le
    · exact hall q hgt
  have hΘ_eq : zetaZeroAbscissa = β := le_antisymm hΘ_le hΘ_ge
  have hfin_off : RHTower.BacklundConverse.FiniteOffLine := by
    refine hfin.subset fun q hq_im => ?_
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint, Complex.mul_im]
    intro hre
    apply hq_im
    rw [him, hre, sub_self]
  have hzal : RHTower.BacklundConverse.ZerosApproachLine :=
    RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine hfin_off
  have hΘ_inf : zetaAsymptoticAbscissa = 1 / 2 :=
    zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half.mp hzal
  have hnot_aal : ¬ RHTower.AsymptoticAbscissaLaw := by
    rw [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa, hΘ_inf, hΘ_eq]
    linarith
  obtain ⟨_, hΘ₂_lt, hexp⟩ := exists_primeErrorFiniteOscillation_of_lt_gap hnot_aal
  set η : ℝ := (zetaZeroAbscissa - zetaSecondAbscissa) / 2
  have hη_pos : 0 < η := by dsimp [η]; linarith
  have hη_lt : η < zetaZeroAbscissa - zetaSecondAbscissa := by dsimp [η]; linarith
  obtain ⟨S, c, hne, C, x₀, hC⟩ := hexp η hη_pos hη_lt
  have hpfo : PrimeErrorIsFiniteOscillation :=
    ⟨zetaZeroAbscissa, η, by linarith, hη_pos, S, c, hne, C, x₀, hC⟩
  obtain ⟨L, δ, U₀, _, hδ, hwin⟩ :=
    exists_bounded_log_gap_sign_changes_of_primeErrorIsFiniteOscillation hpfo
  refine ⟨δ, hδ, fun X₀ => ?_⟩
  set u₀ : ℝ := max U₀ (Real.log (max X₀ 1))
  obtain ⟨⟨u₁, hu₁_mem, hu₁_gt⟩, _⟩ := hwin u₀ (le_max_left _ _)
  set x : ℝ := Real.exp u₁
  have hx_pos : 0 < x := Real.exp_pos u₁
  have hx_ge : X₀ ≤ x := by
    calc X₀ ≤ max X₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max X₀ 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp u₀ := Real.exp_le_exp.mpr (le_max_right _ _)
      _ ≤ Real.exp u₁ := Real.exp_le_exp.mpr hu₁_mem.1
  refine ⟨x, hx_ge, ?_⟩
  have hpow : Real.exp (zetaZeroAbscissa * u₁) = x ^ β := by
    rw [hΘ_eq]; dsimp [x]; rw [← Real.exp_mul]; ring_nf
  rw [← hpow]
  exact hu₁_gt.le.trans (le_abs_self _)

/-! ### 3. Forward behavior of `HasSingleOffLineQuartet` and `HasTwoThreeAliasedQuartets` -/

private theorem zeroQuartetSet_coord' {ρ₀ ρ : ℂ} (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    |ρ.im| = |ρ₀.im| ∧ (ρ.re = ρ₀.re ∨ ρ.re = 1 - ρ₀.re) := by
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · exact ⟨rfl, Or.inl rfl⟩
  · exact ⟨by simp, Or.inl (Complex.conj_re ρ₀)⟩
  · exact ⟨by simp, Or.inr (by simp)⟩
  · exact ⟨by simp, Or.inr (by simp)⟩

/-- **Single-quartet forward theorem.** Under `HasSingleOffLineQuartet (β + iγ)` (`γ > 0`), we have
`1/2 < β < 1`, `67 < γ`, `HasPositivePowerLimsup primeError β`, and `|R_a(β, γ; x)| / (√x log² x)`
is bounded at large `x` for **every** scale `a ≥ 1` (in particular `a = 2, 3, 5`). -/
theorem singleQuartet_obeys_all_dilation_recurrences {β γ : ℝ} (hγ : 0 < γ)
    (hq : HasSingleOffLineQuartet ((β : ℂ) + I * γ)) :
    1 / 2 < β ∧ β < 1 ∧ 67 < γ ∧
      HasPositivePowerLimsup primeError β ∧
      ∀ a : ℝ, 1 ≤ a → ¬ IsSqrtLogSqUnbounded (primeDilationResidual a β γ) := by
  set ρ₀ : ℂ := (β : ℂ) + I * γ
  have hre₀ : ρ₀.re = β := by simp [ρ₀]
  have him₀ : ρ₀.im = γ := by simp [ρ₀]
  have hβ_lo : 1 / 2 < β := by simpa [hre₀] using hq.1
  have hβ_hi : β < 1 := by simpa [hre₀] using hq.re_lt_one
  have h67 : 67 < γ := by
    have h := sixtySeven_lt_abs_im_of_offLine_zeta_zero hq.2.1.1 hq.2.1.2.1 hq.2.1.2.2
      (by linarith [hq.1])
    rwa [him₀, abs_of_pos hγ] at h
  have hpin_re : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → (q.1 : ℂ).re = β ∧ |(q.1 : ℂ).im| = γ := by
    intro q hgt
    have hmem : (q.1 : ℂ) ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]
      exact ⟨xiZeroCopy_mem_carrier' q, by linarith⟩
    obtain ⟨habs, hre_or⟩ := zeroQuartetSet_coord' hmem
    rw [him₀, abs_of_pos hγ] at habs
    rw [hre₀] at hre_or
    rcases hre_or with h1 | h2
    · exact ⟨h1, habs⟩
    · exfalso; linarith
  have hlim : HasPositivePowerLimsup primeError β :=
    hasPositivePowerLimsup_of_finite_and_top_zero hβ_lo hq.finiteOffLine_copies hq.2.1 hre₀
      (fun q hgt => (hpin_re q hgt).1.le)
  refine ⟨hβ_lo, hβ_hi, h67, hlim, fun a ha => ?_⟩
  refine not_isSqrtLogSqUnbounded_of_finite_and_cos_eq ha hq.finiteOffLine_copies fun q hgt => ?_
  obtain ⟨hre_q, habs_q⟩ := hpin_re q hgt
  refine ⟨hre_q, ?_⟩
  rw [← habs_q]
  rcases abs_choice (q.1 : ℂ).im with h | h <;> rw [h]
  simp [neg_mul, Real.cos_neg]

theorem HasTwoThreeAliasedQuartets.finiteOffLine_copies {β γ ω : ℝ}
    (h : HasTwoThreeAliasedQuartets β γ ω) :
    {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
  refine ((finite_xiZeroCopy_zeroQuartetSet ((β : ℂ) + I * γ)).union
    (finite_xiZeroCopy_zeroQuartetSet ((β : ℂ) + I * ω))).subset fun q hne => ?_
  have hmem : (q.1 : ℂ) ∈ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} :=
    ⟨xiZeroCopy_mem_carrier' q, hne⟩
  rwa [h.2.2.2.2.2] at hmem

theorem HasTwoThreeAliasedQuartets.finiteOffLine {β γ ω : ℝ}
    (h : HasTwoThreeAliasedQuartets β γ ω) :
    RHTower.BacklundConverse.FiniteOffLine := by
  refine h.finiteOffLine_copies.subset fun q hq_im => ?_
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  intro hre
  apply hq_im
  rw [him, hre, sub_self]

/-- **Lindelöf theorem for `(2, 3)` cross-aliased double quartets.** Every configuration
`HasTwoThreeAliasedQuartets β γ ω` satisfies `ZerosApproachLine` and all three standard forms of
the Lindelöf conjecture while violating `RiemannHypothesis`. -/
theorem lindelof_all_forms_of_twoThreeAliasedQuartets {β γ ω : ℝ}
    (h : HasTwoThreeAliasedQuartets β γ ω) :
    ¬ RiemannHypothesis ∧
      RHTower.BacklundConverse.ZerosApproachLine ∧
      RHTower.LindelofSparse.LindelofCriticalLine ∧
      RHTower.LindelofSparse.LindelofHalfPlane ∧
      RHTower.BacklundConverse.LindelofOpen := by
  obtain ⟨hβ, _, _, hmem_γ, _, _⟩ := h
  have hnrh : ¬ RiemannHypothesis := by
    intro hrh
    obtain ⟨hζ, h0, h1⟩ := hmem_γ
    have hhalf : ((β : ℂ) + I * γ).re = 1 / 2 := by
      refine hrh _ hζ ?_ (fun heq => by rw [heq, Complex.one_re] at h1; exact lt_irrefl 1 h1)
      rintro ⟨n, hn⟩
      rw [hn] at h0; simp at h0
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simp at hhalf
    linarith
  have hzal := RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine h.finiteOffLine
  have hcl := RHTower.BacklundConverse.lindelofCriticalLine_of_zerosApproachLine hzal
  exact ⟨hnrh, hzal, hcl, RHTower.LindelofSparse.lindelofHalfPlane_of_criticalLine hcl,
    RHTower.BacklundConverse.lindelofCriticalLine_iff_lindelofOpen.mp hcl⟩

/-- **Cross-aliased two-quartet forward theorem and clock-`5` separation.**
Under `HasTwoThreeAliasedQuartets β γ ω`:
1. `1/2 < β < 1`, `67 < γ`, `67 < ω`, `ω ≠ γ`;
2. `(rightZeros zetaZeroConfig).encard = 4` and `realPacketNegIndex = 4`;
3. `HasPositivePowerLimsup primeError β` holds;
4. Both `R_2(β, γ)` and `R_3(β, γ)` are `O(√x log² x)` at large `x`, whereas
   `|R_5(β, γ; x)| / (√x log² x)` is **unbounded**. -/
theorem twoThreeAliasedQuartets_obey_two_and_three_not_five {β γ ω : ℝ}
    (h : HasTwoThreeAliasedQuartets β γ ω) :
    1 / 2 < β ∧ β < 1 ∧ 67 < γ ∧ 67 < ω ∧ ω ≠ γ ∧
      (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard = 4 ∧
      realPacketNegIndex = 4 ∧
      HasPositivePowerLimsup primeError β ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∧
      IsSqrtLogSqUnbounded (primeDilationResidual 5 β γ) := by
  obtain ⟨hβ, hγ, hres, hmem_γ, hmem_ω, hoff_eq⟩ := h
  set ρ₁ : ℂ := (β : ℂ) + I * γ
  set ρ₂ : ℂ := (β : ℂ) + I * ω
  have hβ1 : β < 1 := by simpa [ρ₁] using hmem_γ.2.2
  have h67_γ : 67 < γ := by
    have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero hmem_γ.1 hmem_γ.2.1 hmem_γ.2.2
      (by simp [ρ₁]; linarith)
    simpa [ρ₁, abs_of_pos hγ] using h67
  have h67_ω : 67 < ω := by
    have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero hmem_ω.1 hmem_ω.2.1 hmem_ω.2.2
      (by simp [ρ₂]; linarith)
    simpa [ρ₂, abs_of_pos hres.1] using h67
  have hpin_q : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re →
      (q.1 : ℂ).re = β ∧ (|(q.1 : ℂ).im| = γ ∨ |(q.1 : ℂ).im| = ω) := by
    intro q hgt
    have hmem : (q.1 : ℂ) ∈ zeroQuartetSet ρ₁ ∪ zeroQuartetSet ρ₂ := by
      rw [← hoff_eq]
      exact ⟨xiZeroCopy_mem_carrier' q, by linarith⟩
    rcases hmem with hm1 | hm2
    · obtain ⟨habs, hre_or⟩ := zeroQuartetSet_coord' hm1
      simp only [ρ₁, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.mul_im, one_mul, zero_add, abs_of_pos hγ] at habs hre_or
      rcases hre_or with h1 | h2
      · exact ⟨h1, Or.inl habs⟩
      · exfalso; linarith
    · obtain ⟨habs, hre_or⟩ := zeroQuartetSet_coord' hm2
      simp only [ρ₂, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
        Complex.mul_im, one_mul, zero_add, abs_of_pos hres.1] at habs hre_or
      rcases hre_or with h1 | h2
      · exact ⟨h1, Or.inr habs⟩
      · exfalso; linarith
  have hfin_copies : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite :=
    HasTwoThreeAliasedQuartets.finiteOffLine_copies ⟨hβ, hγ, hres, hmem_γ, hmem_ω, hoff_eq⟩
  have hlim : HasPositivePowerLimsup primeError β :=
    hasPositivePowerLimsup_of_finite_and_top_zero hβ hfin_copies hmem_γ (by simp [ρ₁])
      (fun q hgt => (hpin_q q hgt).1.le)
  have hb2 : ¬ IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) := by
    refine not_isSqrtLogSqUnbounded_of_finite_and_cos_eq (by norm_num) hfin_copies fun q hgt => ?_
    obtain ⟨hre_q, habs_or⟩ := hpin_q q hgt
    refine ⟨hre_q, ?_⟩
    have hcos_abs : Real.cos (|(q.1 : ℂ).im| * Real.log 2) = Real.cos ((q.1 : ℂ).im * Real.log 2) := by
      rcases abs_choice (q.1 : ℂ).im with hc | hc <;> rw [hc]
      simp [neg_mul, Real.cos_neg]
    rw [← hcos_abs]
    rcases habs_or with h1 | h2
    · rw [h1]
    · rw [h2]; simpa using hres.2.2.1
  have hb3 : ¬ IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) := by
    refine not_isSqrtLogSqUnbounded_of_finite_and_cos_eq (by norm_num) hfin_copies fun q hgt => ?_
    obtain ⟨hre_q, habs_or⟩ := hpin_q q hgt
    refine ⟨hre_q, ?_⟩
    have hcos_abs : Real.cos (|(q.1 : ℂ).im| * Real.log 3) = Real.cos ((q.1 : ℂ).im * Real.log 3) := by
      rcases abs_choice (q.1 : ℂ).im with hc | hc <;> rw [hc]
      simp [neg_mul, Real.cos_neg]
    rw [← hcos_abs]
    rcases habs_or with h1 | h2
    · rw [h1]
    · rw [h2]; simpa using hres.2.2.2
  have hu5 : IsSqrtLogSqUnbounded (primeDilationResidual 5 β γ) := by
    by_contra hb5
    have hρ₂_ne1 : ρ₂ ≠ 1 := fun heq => by
      have := congrArg Complex.re heq; simp [ρ₂] at this; linarith
    have hp5 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 5)
      hb5 (by simp [ρ₂]; exact hβ) hρ₂_ne1 hmem_ω.1
    have hc5 : Real.cos (ω * Real.log 5) = Real.cos (γ * Real.log 5) := by
      simpa [ρ₂] using hp5.2
    have habs := (abs_eq_of_threePrime_cos_eq Nat.prime_two Nat.prime_three Nat.prime_five
      (by decide) (by decide) (by decide) hγ.le).mp ⟨hres.2.2.1, hres.2.2.2, hc5⟩
    rw [abs_of_pos hres.1] at habs
    exact hres.2.1 habs
  -- Exact cardinality `(rightZeros zetaZeroConfig).encard = 4`
  have hright_eq : ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig =
      ({ρ₁, conj ρ₁, ρ₂, conj ρ₂} : Set ℂ) := by
    ext z
    change (z ∈ zetaZeroConfig.carrier ∧ 1 / 2 < z.re) ↔
      z = ρ₁ ∨ z = conj ρ₁ ∨ z = ρ₂ ∨ z = conj ρ₂
    constructor
    · rintro ⟨hz_mem, hz_gt⟩
      have hoff : z ∈ zeroQuartetSet ρ₁ ∪ zeroQuartetSet ρ₂ := by
        rw [← hoff_eq]; exact ⟨hz_mem, by linarith⟩
      rcases hoff with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exfalso; simp [ρ₁] at hz_gt; linarith
      · exfalso; simp [ρ₁] at hz_gt; linarith
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exfalso; simp [ρ₂] at hz_gt; linarith
      · exfalso; simp [ρ₂] at hz_gt; linarith
    · have hxi₁ := xi_eq_zero_of_mem_carrier hmem_γ
      have hxi₂ := xi_eq_zero_of_mem_carrier hmem_ω
      have hc₁ : conj ρ₁ ∈ zetaZeroConfig.carrier :=
        mem_carrier_of_xi_eq_zero (by rw [xi_conj, hxi₁, map_zero])
      have hc₂ : conj ρ₂ ∈ zetaZeroConfig.carrier :=
        mem_carrier_of_xi_eq_zero (by rw [xi_conj, hxi₂, map_zero])
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨hmem_γ, by simp [ρ₁]; exact hβ⟩
      · exact ⟨hc₁, by simp [ρ₁]; exact hβ⟩
      · exact ⟨hmem_ω, by simp [ρ₂]; exact hβ⟩
      · exact ⟨hc₂, by simp [ρ₂]; exact hβ⟩
  have hencard : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard = 4 := by
    have hn12 : ρ₁ ≠ conj ρ₁ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₁] at this; linarith
    have hn13 : ρ₁ ≠ ρ₂ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₁, ρ₂] at this; exact hres.2.1 this.symm
    have hn14 : ρ₁ ≠ conj ρ₂ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₁, ρ₂] at this; linarith [hres.1]
    have hn23 : conj ρ₁ ≠ ρ₂ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₁, ρ₂] at this; linarith [hres.1]
    have hn24 : conj ρ₁ ≠ conj ρ₂ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₁, ρ₂] at this; exact hres.2.1 (by linarith)
    have hn34 : ρ₂ ≠ conj ρ₂ := fun heq => by
      have := congrArg Complex.im heq; simp [ρ₂] at this; linarith [hres.1]
    rw [hright_eq, Set.encard_insert_of_notMem (by simp [hn12, hn13, hn14]),
      Set.encard_insert_of_notMem (by simp [hn23, hn24]),
      Set.encard_pair hn34]
    norm_num
  have hidx : realPacketNegIndex = 4 := by
    rw [realPacketNegIndex_eq_rightZeros, hencard]
  exact ⟨hβ, hβ1, h67_γ, h67_ω, hres.2.1, hencard, hidx, hlim, hb2, hb3, hu5⟩

/-! ### 4. Complete pointwise characterizations on `{2, 3}` and `{2, 3, 5}` -/

private theorem mem_zeroQuartetSet_of_re_and_abs_im {β μ : ℝ} {z : ℂ}
    (hre : z.re = β) (him : |z.im| = μ) :
    z ∈ zeroQuartetSet ((β : ℂ) + I * μ) := by
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases eq_or_eq_neg_of_abs_eq him with hp | hn
  · left
    apply Complex.ext <;> simp [hre, hp]
  · right; left
    apply Complex.ext <;> simp [hre, hn]

private theorem mem_carrier_pos_of_mem_carrier_abs_im {β μ : ℝ} {z : ℂ}
    (hz : z ∈ zetaZeroConfig.carrier) (hre : z.re = β) (him : |z.im| = μ) :
    ((β : ℂ) + I * μ) ∈ zetaZeroConfig.carrier := by
  rcases eq_or_eq_neg_of_abs_eq him with hp | hn
  · have hzeq : z = (β : ℂ) + I * μ := by apply Complex.ext <;> simp [hre, hp]
    rwa [← hzeq]
  · have hzeq : conj z = (β : ℂ) + I * μ := by apply Complex.ext <;> simp [hre, hn]
    rw [← hzeq]
    exact mem_carrier_of_xi_eq_zero (by rw [xi_conj, xi_eq_zero_of_mem_carrier hz, map_zero])

/-- **Complete pointwise `(2, 3)` dilation recurrence characterization.**
For any `1/2 < β < 1` and `γ > 0`, `HasPositivePowerLimsup primeError β` holds with both
`R_2(β, γ)` and `R_3(β, γ)` bounded against `√x log² x` if and only if either:
1. `HasSingleOffLineQuartet (β + iγ)` holds; or
2. `γ` admits a `(2, 3)` cross-resonant partner `ω > 67` (`IsCrossResonantPair 2 3 γ ω`) such that
   `HasSingleOffLineQuartet (β + iω)` or `HasTwoThreeAliasedQuartets β γ ω` holds. -/
theorem twoClock_bounded_and_limsup_iff {β γ : ℝ} (hβ : 1 / 2 < β) (_hβ1 : β < 1) (hγ : 0 < γ) :
    (HasPositivePowerLimsup primeError β ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ)) ↔
    (HasSingleOffLineQuartet ((β : ℂ) + I * γ) ∨
      ∃ ω : ℝ, 67 < ω ∧ IsCrossResonantPair 2 3 γ ω ∧
        (HasSingleOffLineQuartet ((β : ℂ) + I * ω) ∨ HasTwoThreeAliasedQuartets β γ ω)) := by
  constructor
  · rintro ⟨hlim, hb2, hb3⟩
    -- Step 1: At least one right-of-line strip zero exists.
    have hex_right : ∃ z ∈ zetaZeroConfig.carrier, 1 / 2 < z.re := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := fun q =>
        hnone (q.1 : ℂ) (xiZeroCopy_mem_carrier' q)
      exact not_hasPositivePowerLimsup_of_zeroReSup_lt
        ((RHTower.zeroReSup_le_of_forall_re_le hall).trans_lt hβ) hlim
    -- Step 2: Every right-of-line strip zero `z` has `z.re = β`, `67 < |z.im|`, and
    -- either `|z.im| = γ` or `IsCrossResonantPair 2 3 γ |z.im|`.
    have hpin : ∀ z ∈ zetaZeroConfig.carrier, 1 / 2 < z.re →
        z.re = β ∧ 67 < |z.im| ∧ (|z.im| = γ ∨ IsCrossResonantPair 2 3 γ |z.im|) := by
      intro z hz hgt
      have hne1 : z ≠ 1 := fun heq => by
        rw [heq, Complex.one_re] at hz; exact lt_irrefl 1 hz.2.2
      have hp2 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 2)
        hb2 hgt hne1 hz.1
      have hp3 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 3)
        hb3 hgt hne1 hz.1
      have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero hz.1 hz.2.1 hz.2.2 (by linarith)
      have him_ne : z.im ≠ 0 := by intro h0; rw [h0, abs_zero] at h67; linarith
      exact ⟨hp2.1, h67,
        abs_eq_or_isCrossResonantPair_of_twoPrime_cos_eq (p := 2) (q := 3) him_ne hp2.2 hp3.2⟩
    -- Helper: if `(β : ℂ) + I * μ ∈ carrier` (`μ > 0`), then all 4 quartet points lie in `{re ≠ 1/2}`.
    have hquartet_sub : ∀ μ : ℝ, ((β : ℂ) + I * μ) ∈ zetaZeroConfig.carrier →
        zeroQuartetSet ((β : ℂ) + I * μ) ⊆ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} := by
      intro μ hmem z hz_q
      have hxi := xi_eq_zero_of_mem_carrier hmem
      have hc := mem_carrier_of_xi_eq_zero (by rw [xi_conj, hxi, map_zero])
      have hr := mem_carrier_of_xi_eq_zero (by rw [xi_one_sub]; exact hxi)
      have hrc := mem_carrier_of_xi_eq_zero (by rw [xi_one_sub, xi_conj, hxi, map_zero])
      simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hz_q
      rcases hz_q with rfl | rfl | rfl | rfl
      · exact ⟨hmem, by simp; linarith⟩
      · exact ⟨hc, by simp; linarith⟩
      · exact ⟨hr, by simp; linarith⟩
      · exact ⟨hrc, by simp; linarith⟩
    -- Split on whether any right-of-line zero has `|z.im| ≠ γ`.
    by_cases hex_other : ∃ z ∈ zetaZeroConfig.carrier, 1 / 2 < z.re ∧ |z.im| ≠ γ
    · right
      obtain ⟨z_ω, hz_ω, hgt_ω, hne_γ⟩ := hex_other
      obtain ⟨hre_ω, h67_ω, hor_ω⟩ := hpin z_ω hz_ω hgt_ω
      have hres : IsCrossResonantPair 2 3 γ |z_ω.im| := hor_ω.resolve_left hne_γ
      set ω : ℝ := |z_ω.im|
      have hmem_ω : ((β : ℂ) + I * ω) ∈ zetaZeroConfig.carrier :=
        mem_carrier_pos_of_mem_carrier_abs_im hz_ω hre_ω rfl
      -- Every right-of-line zero has `|z.im| = γ` or `|z.im| = ω` by uniqueness!
      have hall_γ_or_ω : ∀ z ∈ zetaZeroConfig.carrier, 1 / 2 < z.re →
          z.re = β ∧ (|z.im| = γ ∨ |z.im| = ω) := by
        intro z hz hgt
        obtain ⟨hre_z, _, hor_z⟩ := hpin z hz hgt
        refine ⟨hre_z, ?_⟩
        rcases hor_z with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (isCrossResonantPair_unique Nat.prime_two Nat.prime_three
            (by decide) hγ h2 hres)
      refine ⟨ω, h67_ω, hres, ?_⟩
      by_cases hmem_γ : ((β : ℂ) + I * γ) ∈ zetaZeroConfig.carrier
      · right
        refine ⟨hβ, hγ, hres, hmem_γ, hmem_ω, Set.Subset.antisymm ?_
          (Set.union_subset (hquartet_sub γ hmem_γ) (hquartet_sub ω hmem_ω))⟩
        rintro ρ ⟨hρ_mem, hρ_ne⟩
        rcases lt_or_gt_of_ne hρ_ne with hlt | hgt
        · have hrefl : 1 - ρ ∈ zetaZeroConfig.carrier :=
            mem_carrier_of_xi_eq_zero (by rw [xi_one_sub]; exact xi_eq_zero_of_mem_carrier hρ_mem)
          obtain ⟨hre_r, him_r⟩ := hall_γ_or_ω (1 - ρ) hrefl (by simp; linarith)
          rcases him_r with h1 | h2
          · left
            have hm := mem_zeroQuartetSet_of_re_and_abs_im hre_r h1
            simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
            rcases hm with hm | hm | hm | hm
            · right; right; left; linear_combination -hm
            · right; right; right; linear_combination -hm
            · left; linear_combination -hm
            · right; left; linear_combination -hm
          · right
            have hm := mem_zeroQuartetSet_of_re_and_abs_im hre_r h2
            simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
            rcases hm with hm | hm | hm | hm
            · right; right; left; linear_combination -hm
            · right; right; right; linear_combination -hm
            · left; linear_combination -hm
            · right; left; linear_combination -hm
        · obtain ⟨hre_r, him_r⟩ := hall_γ_or_ω ρ hρ_mem hgt
          rcases him_r with h1 | h2
          · exact Or.inl (mem_zeroQuartetSet_of_re_and_abs_im hre_r h1)
          · exact Or.inr (mem_zeroQuartetSet_of_re_and_abs_im hre_r h2)
      · left
        refine ⟨by simp; exact hβ, hmem_ω, Set.Subset.antisymm ?_ (hquartet_sub ω hmem_ω)⟩
        rintro ρ ⟨hρ_mem, hρ_ne⟩
        rcases lt_or_gt_of_ne hρ_ne with hlt | hgt
        · have hrefl : 1 - ρ ∈ zetaZeroConfig.carrier :=
            mem_carrier_of_xi_eq_zero (by rw [xi_one_sub]; exact xi_eq_zero_of_mem_carrier hρ_mem)
          obtain ⟨hre_r, him_r⟩ := hall_γ_or_ω (1 - ρ) hrefl (by simp; linarith)
          rcases him_r with h1 | h2
          · exfalso
            exact hmem_γ (mem_carrier_pos_of_mem_carrier_abs_im hrefl hre_r h1)
          · have hm := mem_zeroQuartetSet_of_re_and_abs_im hre_r h2
            simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
            rcases hm with hm | hm | hm | hm
            · right; right; left; linear_combination -hm
            · right; right; right; linear_combination -hm
            · left; linear_combination -hm
            · right; left; linear_combination -hm
        · obtain ⟨hre_r, him_r⟩ := hall_γ_or_ω ρ hρ_mem hgt
          rcases him_r with h1 | h2
          · exfalso
            exact hmem_γ (mem_carrier_pos_of_mem_carrier_abs_im hρ_mem hre_r h1)
          · exact mem_zeroQuartetSet_of_re_and_abs_im hre_r h2
    · left
      push Not at hex_other
      obtain ⟨z₀, hz₀, hgt₀⟩ := hex_right
      have hre₀ : z₀.re = β := (hpin z₀ hz₀ hgt₀).1
      have him₀ : |z₀.im| = γ := hex_other z₀ hz₀ hgt₀
      have hmem_γ : ((β : ℂ) + I * γ) ∈ zetaZeroConfig.carrier :=
        mem_carrier_pos_of_mem_carrier_abs_im hz₀ hre₀ him₀
      refine ⟨by simp; exact hβ, hmem_γ, Set.Subset.antisymm ?_ (hquartet_sub γ hmem_γ)⟩
      rintro ρ ⟨hρ_mem, hρ_ne⟩
      rcases lt_or_gt_of_ne hρ_ne with hlt | hgt
      · have hrefl : 1 - ρ ∈ zetaZeroConfig.carrier :=
          mem_carrier_of_xi_eq_zero (by rw [xi_one_sub]; exact xi_eq_zero_of_mem_carrier hρ_mem)
        have hgt_r : 1 / 2 < (1 - ρ).re := by simp; linarith
        have hm := mem_zeroQuartetSet_of_re_and_abs_im (hpin (1 - ρ) hrefl hgt_r).1
          (hex_other (1 - ρ) hrefl hgt_r)
        simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
        rcases hm with hm | hm | hm | hm
        · right; right; left; linear_combination -hm
        · right; right; right; linear_combination -hm
        · left; linear_combination -hm
        · right; left; linear_combination -hm
      · exact mem_zeroQuartetSet_of_re_and_abs_im (hpin ρ hρ_mem hgt).1 (hex_other ρ hρ_mem hgt)
  · rintro (hq | ⟨ω, _, hres, hq_ω | htwo⟩)
    · obtain ⟨_, _, _, hlim, hall⟩ := singleQuartet_obeys_all_dilation_recurrences hγ hq
      exact ⟨hlim, hall 2 (by norm_num), hall 3 (by norm_num)⟩
    · obtain ⟨_, _, _, hlim, hall⟩ := singleQuartet_obeys_all_dilation_recurrences hres.1 hq_ω
      have heq2 : primeDilationResidual 2 β γ = primeDilationResidual 2 β ω := by
        funext x
        unfold primeDilationResidual
        rw [dilationRecurrenceOp_congr_cos (by simpa using hres.2.2.1.symm)]
      have heq3 : primeDilationResidual 3 β γ = primeDilationResidual 3 β ω := by
        funext x
        unfold primeDilationResidual
        rw [dilationRecurrenceOp_congr_cos (by simpa using hres.2.2.2.symm)]
      rw [heq2, heq3]
      exact ⟨hlim, hall 2 (by norm_num), hall 3 (by norm_num)⟩
    · obtain ⟨_, _, _, _, _, _, _, hlim, hb2, hb3, _⟩ :=
        twoThreeAliasedQuartets_obey_two_and_three_not_five htwo
      exact ⟨hlim, hb2, hb3⟩

/-- **Non-cross-resonant pointwise `(2, 3)` equivalence.** Whenever `γ > 0` has no `(2, 3)`
cross-resonant partner above height `67` (in particular for every non-cross-resonant `γ > 0`),
boundedness of `R_2(β, γ)` and `R_3(β, γ)` with `HasPositivePowerLimsup primeError β` is
unconditionally equivalent to `HasSingleOffLineQuartet (β + iγ)`. -/
theorem twoClock_nonCrossResonant_iff_singleQuartet {β γ : ℝ}
    (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hno_alias : ∀ ω : ℝ, IsCrossResonantPair 2 3 γ ω → ω ≤ 67) :
    (HasPositivePowerLimsup primeError β ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ)) ↔
    HasSingleOffLineQuartet ((β : ℂ) + I * γ) := by
  rw [twoClock_bounded_and_limsup_iff hβ hβ1 hγ]
  refine ⟨?_, Or.inl⟩
  rintro (hq | ⟨ω, h67, hres, _⟩)
  · exact hq
  · exact absurd (hno_alias ω hres) (not_le.mpr h67)

/-- **Complete pointwise `{2, 3, 5}` de-aliased characterization.**
For **every** `1/2 < β < 1` and **every** `γ > 0` (without any cross-resonance side condition),
`HasPositivePowerLimsup primeError β` holds with `R_2(β, γ)`, `R_3(β, γ)`, and `R_5(β, γ)` all
bounded against `√x log² x` if and only if `HasSingleOffLineQuartet (β + iγ)`. -/
theorem threeClock_bounded_and_limsup_iff {β γ : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hγ : 0 < γ) :
    (HasPositivePowerLimsup primeError β ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (primeDilationResidual 5 β γ)) ↔
    HasSingleOffLineQuartet ((β : ℂ) + I * γ) := by
  constructor
  · rintro ⟨hlim, hb2, hb3, hb5⟩
    rcases (twoClock_bounded_and_limsup_iff hβ hβ1 hγ).mp ⟨hlim, hb2, hb3⟩ with
      hq | ⟨ω, _, hres, hq_ω | htwo⟩
    · exact hq
    · exfalso
      have hne1 : ((β : ℂ) + I * ω) ≠ 1 := fun heq => by
        have := congrArg Complex.re heq; simp at this; linarith
      have hp5 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 5)
        hb5 hq_ω.1 hne1 hq_ω.2.1.1
      have hc5 : Real.cos (ω * Real.log 5) = Real.cos (γ * Real.log 5) := by simpa using hp5.2
      have habs := (abs_eq_of_threePrime_cos_eq Nat.prime_two Nat.prime_three Nat.prime_five
        (by decide) (by decide) (by decide) hγ.le).mp ⟨hres.2.2.1, hres.2.2.2, hc5⟩
      rw [abs_of_pos hres.1] at habs
      exact hres.2.1 habs
    · exfalso
      exact hb5 (twoThreeAliasedQuartets_obey_two_and_three_not_five htwo).2.2.2.2.2.2.2.2.2.2
  · intro hq
    obtain ⟨_, _, _, hlim, hall⟩ := singleQuartet_obeys_all_dilation_recurrences hγ hq
    exact ⟨hlim, hall 2 (by norm_num), hall 3 (by norm_num), hall 5 (by norm_num)⟩

/-! ### 5. Global characterizations, Lindelöf dichotomy, and cross-route corollaries -/

private theorem hasSingleOffLineQuartet_abs_im {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    0 < |ρ₀.im| ∧ HasSingleOffLineQuartet ((ρ₀.re : ℂ) + I * |ρ₀.im|) := by
  have him_pos : 0 < |ρ₀.im| := abs_pos.mpr hq.im_ne_zero
  refine ⟨him_pos, ?_⟩
  set ρ₊ : ℂ := (ρ₀.re : ℂ) + I * |ρ₀.im|
  have hρ₊_eq : ρ₊ = ρ₀ ∨ ρ₊ = conj ρ₀ := by
    rcases abs_choice ρ₀.im with hp | hn
    · left; apply Complex.ext <;> simp [ρ₊, hp]
    · right; apply Complex.ext <;> simp [ρ₊, hn]
  rcases hρ₊_eq with h1 | h2
  · rwa [h1]
  · rw [h2]
    have hmem_c : conj ρ₀ ∈ zetaZeroConfig.carrier :=
      mem_carrier_of_xi_eq_zero (by rw [xi_conj, hq.xi_eq_zero, map_zero])
    refine ⟨by simp; exact hq.1, hmem_c, ?_⟩
    rw [hq.2.2]
    ext z
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff, Complex.conj_conj]
    tauto

/-- **Exact global characterization of the two-clock `{2, 3}` recurrence law.**
`TwoClockPrimeRecurrenceLaw` holds across all `1/2 < β < 1` and `γ > 0` if and only if `ζ` has
neither a single off-line quartet nor a `(2, 3)` cross-aliased pair of off-line quartets. -/
theorem twoClockPrimeRecurrenceLaw_iff :
    TwoClockPrimeRecurrenceLaw ↔
      (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
        (∀ β γ ω : ℝ, ¬ HasTwoThreeAliasedQuartets β γ ω) := by
  constructor
  · intro hlaw
    refine ⟨fun ρ₀ hq => ?_, fun β γ ω htwo => ?_⟩
    · obtain ⟨him_pos, hq_pos⟩ := hasSingleOffLineQuartet_abs_im hq
      obtain ⟨hβ, hβ1, _, hlim, hall⟩ :=
        singleQuartet_obeys_all_dilation_recurrences him_pos hq_pos
      rcases hlaw ρ₀.re |ρ₀.im| hβ hβ1 him_pos hlim with hu2 | hu3
      · exact hall 2 (by norm_num) hu2
      · exact hall 3 (by norm_num) hu3
    · obtain ⟨hβ, hβ1, _, _, _, _, _, hlim, hb2, hb3, _⟩ :=
        twoThreeAliasedQuartets_obey_two_and_three_not_five htwo
      rcases hlaw β γ hβ hβ1 htwo.2.1 hlim with hu2 | hu3
      · exact hb2 hu2
      · exact hb3 hu3
  · rintro ⟨hno_one, hno_two⟩ β γ hβ hβ1 hγ hlim
    by_contra hnot
    push Not at hnot
    obtain ⟨hb2, hb3⟩ := hnot
    rcases (twoClock_bounded_and_limsup_iff hβ hβ1 hγ).mp ⟨hlim, hb2, hb3⟩ with
      hq | ⟨ω, _, _, hq_ω | htwo⟩
    · exact hno_one _ hq
    · exact hno_one _ hq_ω
    · exact hno_two β γ ω htwo

/-- **Exact global characterization of the three-clock `{2, 3, 5}` recurrence law.**
`ThreeClockPrimeRecurrenceLaw` is unconditionally equivalent to excluding a single off-line
quartet everywhere in `ℂ`, hence to `RiemannHypothesis ∨ 4 ≤ (rightZeros zetaZeroConfig).encard`. -/
theorem threeClockPrimeRecurrenceLaw_iff :
    ThreeClockPrimeRecurrenceLaw ↔ ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  constructor
  · intro hlaw ρ₀ hq
    obtain ⟨him_pos, hq_pos⟩ := hasSingleOffLineQuartet_abs_im hq
    obtain ⟨hβ, hβ1, _, hlim, hall⟩ :=
      singleQuartet_obeys_all_dilation_recurrences him_pos hq_pos
    rcases hlaw ρ₀.re |ρ₀.im| hβ hβ1 him_pos hlim with hu2 | hu3 | hu5
    · exact hall 2 (by norm_num) hu2
    · exact hall 3 (by norm_num) hu3
    · exact hall 5 (by norm_num) hu5
  · intro hno_one β γ hβ hβ1 hγ hlim
    by_contra hnot
    push Not at hnot
    obtain ⟨hb2, hb3, hb5⟩ := hnot
    exact hno_one _ ((threeClock_bounded_and_limsup_iff hβ hβ1 hγ).mp ⟨hlim, hb2, hb3, hb5⟩)

theorem threeClockPrimeRecurrenceLaw_of_twoClock (h : TwoClockPrimeRecurrenceLaw) :
    ThreeClockPrimeRecurrenceLaw :=
  threeClockPrimeRecurrenceLaw_iff.mpr (twoClockPrimeRecurrenceLaw_iff.mp h).1

/-- Any failure of `FiniteOffLine` unconditionally forces `TwoClockPrimeRecurrenceLaw`. -/
theorem twoClockPrimeRecurrenceLaw_of_not_finiteOffLine
    (hinf : ¬ RHTower.BacklundConverse.FiniteOffLine) :
    TwoClockPrimeRecurrenceLaw :=
  twoClockPrimeRecurrenceLaw_iff.mpr
    ⟨fun _ hq => hinf hq.finiteOffLine, fun _ _ _ htwo => hinf htwo.finiteOffLine⟩

/-- Any failure of `ZerosApproachLine` unconditionally forces `TwoClockPrimeRecurrenceLaw`. -/
theorem twoClockPrimeRecurrenceLaw_of_not_zerosApproachLine
    (hnzal : ¬ RHTower.BacklundConverse.ZerosApproachLine) :
    TwoClockPrimeRecurrenceLaw :=
  twoClockPrimeRecurrenceLaw_of_not_finiteOffLine fun hfin =>
    hnzal (RHTower.BacklundConverse.zerosApproachLine_of_finiteOffLine hfin)

/-- Any failure of the Lindelöf conjecture unconditionally forces `TwoClockPrimeRecurrenceLaw`. -/
theorem twoClockPrimeRecurrenceLaw_of_not_lindelof
    (hnl : ¬ RHTower.LindelofSparse.LindelofCriticalLine) :
    TwoClockPrimeRecurrenceLaw :=
  twoClockPrimeRecurrenceLaw_iff.mpr
    ⟨not_hasSingleOffLineQuartet_of_not_lindelof hnl,
      fun _ _ _ htwo => hnl (lindelof_all_forms_of_twoThreeAliasedQuartets htwo).2.2.1⟩

/-- `RiemannHypothesis` unconditionally implies `TwoClockPrimeRecurrenceLaw`. -/
theorem twoClockPrimeRecurrenceLaw_of_riemannHypothesis (hrh : RiemannHypothesis) :
    TwoClockPrimeRecurrenceLaw :=
  twoClockPrimeRecurrenceLaw_iff.mpr
    ⟨fun _ hq => hq.not_riemannHypothesis hrh,
      fun _ _ _ htwo => (lindelof_all_forms_of_twoThreeAliasedQuartets htwo).1 hrh⟩

/-- **Unconditional global dichotomy on `ζ`.**
Either `TwoClockPrimeRecurrenceLaw` holds unconditionally across all `1/2 < β < 1` and `γ > 0`,
**or** `¬ RiemannHypothesis` coexists with `FiniteOffLine`, `ZerosApproachLine`, all three forms
of the Lindelöf conjecture (`LindelofCriticalLine`, `LindelofHalfPlane`, `LindelofOpen`), and
`realPacketNegIndex ∈ {2, 4}` (`(rightZeros zetaZeroConfig).encard ∈ {2, 4}`). -/
theorem twoClockPrimeRecurrenceLaw_or_lindelof_finite_stratum :
    TwoClockPrimeRecurrenceLaw ∨
      (¬ RiemannHypothesis ∧
        RHTower.BacklundConverse.FiniteOffLine ∧
        RHTower.BacklundConverse.ZerosApproachLine ∧
        RHTower.LindelofSparse.LindelofCriticalLine ∧
        RHTower.LindelofSparse.LindelofHalfPlane ∧
        RHTower.BacklundConverse.LindelofOpen ∧
        ((ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard = 2 ∨
          (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard = 4) ∧
        (realPacketNegIndex = 2 ∨ realPacketNegIndex = 4)) := by
  by_cases hlaw : TwoClockPrimeRecurrenceLaw
  · exact Or.inl hlaw
  · right
    have hnot := (twoClockPrimeRecurrenceLaw_iff.not_left).mp hlaw
    push Not at hnot
    by_cases hex1 : ∃ ρ₀ : ℂ, HasSingleOffLineQuartet ρ₀
    · obtain ⟨ρ₀, hq⟩ := hex1
      obtain ⟨hcl, hhp, hopen⟩ := lindelof_all_forms_of_singleQuartet hq
      have henc2 : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard = 2 :=
        (exists_singleOffLineQuartet_ecs_tfae.out 0 1).mp ⟨ρ₀, hq⟩
      have hidx2 : realPacketNegIndex = 2 :=
        (exists_singleOffLineQuartet_ecs_tfae.out 0 3).mp ⟨ρ₀, hq⟩
      exact ⟨hq.not_riemannHypothesis, hq.finiteOffLine, zerosApproachLine_of_singleQuartet hq,
        hcl, hhp, hopen, Or.inl henc2, Or.inl hidx2⟩
    · have hex2 := hnot (not_exists.mp hex1)
      obtain ⟨β, γ, ω, htwo⟩ := hex2
      obtain ⟨hnrh, hzal, hcl, hhp, hopen⟩ := lindelof_all_forms_of_twoThreeAliasedQuartets htwo
      obtain ⟨_, _, _, _, _, henc4, hidx4, _⟩ :=
        twoThreeAliasedQuartets_obey_two_and_three_not_five htwo
      exact ⟨hnrh, htwo.finiteOffLine, hzal, hcl, hhp, hopen, Or.inr henc4, Or.inr hidx4⟩

/-- **Cross-route corollaries of `ThreeClockPrimeRecurrenceLaw` (and `TwoClockPrimeRecurrenceLaw`).**
Whenever `ThreeClockPrimeRecurrenceLaw` holds (in particular whenever `TwoClockPrimeRecurrenceLaw`
holds):
1. `ζ` has no single off-line quartet `Q(ρ₀)` of **any** divisor multiplicity `m ≥ 1`;
2. Either `RiemannHypothesis` holds, or at least **four** distinct zeros lie right of `Re s = 1/2`
   (`(rightZeros zetaZeroConfig).encard ≥ 4`);
3. `realPacketNegIndex ≠ 2`;
4. Under `¬ RiemannHypothesis`, there exist a confinement ratio `R > 0`, a finite shift set `S`,
   and half-line test states `H : S → ℝ → ℝ` with `3 ≤ hermNegIndex (confinedGram R H)`
   (eliminating the two-rung confined critical-state ladder);
5. Cofinally many odd primes `2t + 1` witness the nonexistence of any single-wave error bound
   `O(√x log² x)` in consecutive Vaughan cofactor counts `adjacentCountAt t`. -/
theorem corollaries_of_threeClockPrimeRecurrenceLaw (h : ThreeClockPrimeRecurrenceLaw) :
    (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
    (RiemannHypothesis ∨
      (4 : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard) ∧
    realPacketNegIndex ≠ 2 ∧
    (¬ RiemannHypothesis →
      ∃ (R : ℝ), 0 < R ∧ ∃ (S : Finset ℝ) (H : S → ℝ → ℝ),
        (∀ s, IsHalfLineTest (H s)) ∧ 3 ≤ hermNegIndex (confinedGram R H)) ∧
    (∀ B : ℕ, ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → ¬ ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
          K * Real.sqrt x * Real.log x ^ 2) := by
  have hno_one : ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ :=
    threeClockPrimeRecurrenceLaw_iff.mp h
  have hrh_or_4 : RiemannHypothesis ∨
      (4 : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard :=
    no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp hno_one
  have hidx_ne2 : realPacketNegIndex ≠ 2 := fun hidx2 => by
    obtain ⟨ρ₀, hq⟩ := (exists_singleOffLineQuartet_ecs_tfae.out 3 0).mp hidx2
    exact hno_one ρ₀ hq
  have hgram3 : ¬ RiemannHypothesis →
      ∃ (R : ℝ), 0 < R ∧ ∃ (S : Finset ℝ) (H : S → ℝ → ℝ),
        (∀ s, IsHalfLineTest (H s)) ∧ 3 ≤ hermNegIndex (confinedGram R H) := by
    intro hnrh
    by_contra hnot3
    push Not at hnot3
    have hle2 : ∀ (R : ℝ), 0 < R → ∀ (S : Finset ℝ) (H : S → ℝ → ℝ),
        (∀ s, IsHalfLineTest (H s)) → hermNegIndex (confinedGram R H) ≤ 2 := by
      intro R hR S H hH
      have hlt := hnot3 R hR S H hH
      omega
    obtain ⟨ρ₀, hq⟩ := (exists_singleOffLineQuartet_ecs_tfae.out 4 0).mp ⟨hnrh, hle2⟩
    exact hno_one ρ₀ hq
  have hadj : ∀ B : ℕ, ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → ¬ ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
          K * Real.sqrt x * Real.log x ^ 2 := by
    intro B
    obtain ⟨t, ht, hp, hchar⟩ := cofinal_adjacentCounts_characterize_singleQuartet B
    exact ⟨t, ht, hp, fun ρ hlo hhi hζ hwave => hno_one ρ ((hchar ρ hlo hhi hζ).mpr hwave)⟩
  exact ⟨hno_one, hrh_or_4, hidx_ne2, hgram3, hadj⟩

theorem corollaries_of_twoClockPrimeRecurrenceLaw (h : TwoClockPrimeRecurrenceLaw) :
    (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
    (∀ β γ ω : ℝ, ¬ HasTwoThreeAliasedQuartets β γ ω) ∧
    (RiemannHypothesis ∨
      (4 : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard) ∧
    realPacketNegIndex ≠ 2 ∧
    (¬ RiemannHypothesis →
      ∃ (R : ℝ), 0 < R ∧ ∃ (S : Finset ℝ) (H : S → ℝ → ℝ),
        (∀ s, IsHalfLineTest (H s)) ∧ 3 ≤ hermNegIndex (confinedGram R H)) ∧
    (∀ B : ℕ, ∃ t > B, (2 * t + 1).Prime ∧ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
      riemannZeta ρ = 0 → ¬ ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |adjacentCountAt t x - 2 * (quartetCopyMult ρ : ℝ) * ((x : ℂ) ^ ρ / ρ).re| ≤
          K * Real.sqrt x * Real.log x ^ 2) := by
  obtain ⟨hno_one, hno_two⟩ := twoClockPrimeRecurrenceLaw_iff.mp h
  obtain ⟨_, hrh_or_4, hidx_ne2, hgram3, hadj⟩ :=
    corollaries_of_threeClockPrimeRecurrenceLaw (threeClockPrimeRecurrenceLaw_of_twoClock h)
  exact ⟨hno_one, hno_two, hrh_or_4, hidx_ne2, hgram3, hadj⟩

/-- **Unconditional model-realization firewall for two and three dilation clocks.**
1. Dense `(2, 3)` cross-resonant pairs `(γ, ω*)` (`ω* > 67`) exist on every open interval in
   `(0, ∞)` and yield planted two-frequency waves `f` satisfying `HasPositivePowerLimsup f β` and
   exact annihilation under both `dilationRecurrenceOp 2 β γ` and `dilationRecurrenceOp 3 β γ` while
   driving `dilationRecurrenceOp 5 β γ f` unbounded against `√x log² x`.
2. For every `β ∈ (1/2, 27001 / 48000)` and `γ > 0`, either `ζ(β + iγ) = 0` (`¬ RH`), or a
   `{0, 1, 2}`-prime Beurling edit `sEdit α β γ k₀` realizes `{β ± iγ}` with integer norm-count
   exponent `c < 1/2` and holomorphic continuation below `Re s = 1/2`.
3. Over-regular Beurling zeta (`Λ ≥ 0`, no functional equation) and positive degree-one Euler twins
   (functional equation, fake Euler product) realize off-line quartet critical states. -/
theorem model_firewall_for_two_and_three_clocks {a b β : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hlo : 1 / 2 < β) (hhi : β < 27001 / 48000) :
    (∃ γ ω : ℝ, a < γ ∧ γ < b ∧ 67 < ω ∧ IsCrossResonantPair 2 3 γ ω ∧
      let f : ℝ → ℝ := fun x =>
        ((1 : ℂ) * (x : ℂ) ^ ((β : ℂ) + I * γ)).re +
          ((1 : ℂ) * (x : ℂ) ^ ((β : ℂ) + I * ω)).re
      HasPositivePowerLimsup f β ∧
        (∀ x : ℝ, 0 < x → dilationRecurrenceOp 2 β γ f x = 0) ∧
        (∀ x : ℝ, 0 < x → dilationRecurrenceOp 3 β γ f x = 0) ∧
        IsSqrtLogSqUnbounded (dilationRecurrenceOp 5 β γ f)) ∧
    (∀ γ : ℝ, (riemannZeta (WorldsOfTheZeroConfiguration.TwoSidedEdits.zeroPt β γ) = 0 ∧
        ¬ RiemannHypothesis) ∨
      ∃ (α : ℝ) (k₀ : ℕ) (c σ₁ : ℝ),
        c < 1 / 2 ∧ σ₁ < 1 / 2 ∧
        SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt
          (WorldsOfTheZeroConfiguration.TwoSidedEdits.editSystem
            (WorldsOfTheZeroConfiguration.SignedEdit.sEdit α β γ k₀)) c ∧
        DifferentiableOn ℂ
          (WorldsOfTheZeroConfiguration.SignedEdit.editG α β γ k₀) {s : ℂ | σ₁ < s.re}) ∧
    (RHTower.BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1 ((3 / 5 : ℝ) + I) = 0) := by
  refine ⟨?_, fun γ => ?_, (singleQuartet_realized_in_models hlo).2.2.1⟩
  · obtain ⟨γ, ω, hγa, hγb, hω67, hres⟩ := dense_exists_isCrossResonantPair ha hab 67
    have hγ_pos : 0 < γ := lt_of_le_of_lt ha hγa
    exact ⟨γ, ω, hγa, hγb, hω67, hres,
      plantedAliasedDoubleWave_separates_two_and_three_clocks hlo hγ_pos hres⟩
  · rcases WorldsOfTheZeroConfiguration.unconditional_subSqrt_singlePair_dichotomy (γ := γ) hlo hhi
      with hζ | ⟨α, k₀, c, σ₁, hc, hσ₁, hfake, _, hdiff, _⟩
    · exact Or.inl hζ
    · exact Or.inr ⟨α, k₀, c, σ₁, hc, hσ₁, hfake, hdiff⟩

#print axioms singleQuartet_obeys_all_dilation_recurrences
#print axioms twoThreeAliasedQuartets_obey_two_and_three_not_five
#print axioms twoClock_bounded_and_limsup_iff
#print axioms twoClock_nonCrossResonant_iff_singleQuartet
#print axioms threeClock_bounded_and_limsup_iff
#print axioms twoClockPrimeRecurrenceLaw_iff
#print axioms threeClockPrimeRecurrenceLaw_iff
#print axioms twoClockPrimeRecurrenceLaw_or_lindelof_finite_stratum
#print axioms corollaries_of_twoClockPrimeRecurrenceLaw
#print axioms model_firewall_for_two_and_three_clocks

end GaloisForLFunctions.ExceptionalLayerTheory
