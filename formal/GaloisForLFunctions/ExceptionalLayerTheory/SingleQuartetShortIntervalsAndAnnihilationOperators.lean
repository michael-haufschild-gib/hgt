import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExceptionalLayerTheory.SingleQuartetLindelofCosineAndQuotientLaguerrePolya
import GaloisForLFunctions.ExceptionalLayerTheory.TwoAndThreeDilationRecurrencesAndSingleQuartetStratum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Short-Interval Prime Laws, Half-Period Annihilation, and Unified Multiplicity Bifurcation

This module establishes five unconditional analytic and arithmetic laws governing the single-quartet
stratum `HasSingleOffLineQuartet ρ₀` and the finite off-line world `BacklundConverse.FiniteOffLine`:

1. **Unified `OutsideQuartetOnLine ρ₀` bifurcation and single-wave law**
   (`OutsideQuartetOnLine`, `hasSingleOffLineQuartet_iff_outsideQuartetOnLine`,
   `outsideQuartetOnLine_dichotomy`, `riemannHypothesis_iff_outsideQuartetOnLine_and_mult_zero`,
   `outsideQuartetOnLine_chebyshevPsi_and_theta_wave`):
   Requiring all strip zeros outside `zeroQuartetSet ρ₀` (`1/2 < Re ρ₀ < 1`) to lie on `Re s = 1/2`
   unifies `RiemannHypothesis` (`quartetCopyMult ρ₀ = 0`) and `HasSingleOffLineQuartet ρ₀`
   (`quartetCopyMult ρ₀ ≥ 1`) into a single integer-multiplicity family with uniform explicit error
   `ψ(x) - x = -2 m Re(x^{ρ₀}/ρ₀) + O(√x log² x)` and `θ(x) - x = -2 m Re(x^{ρ₀}/ρ₀) + O(√x log² x)`.

2. **Two-point half-period annihilation operator and secular polynomial-wave cancellation**
   (`quartetHalfPeriodScale`, `halfPeriodAnnihilator`, `halfPeriodAnnihilator_re_cpow_eq_zero`,
   `iterate_halfPeriodAnnihilator_re_cpow_log_pow_eq_zero`,
   `outsideQuartetOnLine_halfPeriod_chebyshev_cancellation`):
   At the half-period multiplier `λ₀ = exp(π / |Im ρ₀|) ∈ (1, 2)`, the two-point operator
   `(𝓓_{ρ₀} F)(x) = F(λ₀ x) + λ₀^{Re ρ₀} F(x)` satisfies `λ₀^{ρ₀} = -λ₀^{Re ρ₀}`, annihilates
   `x ↦ Re(c x^{ρ₀})`, annihilates `x ↦ Re(c x^{ρ₀} (log x)^k)` for all `k < m` upon `m`-fold
   iteration `𝓓_{ρ₀}^[m]`, and cancels the `x^{Re ρ₀}` wave in `ψ(x) - x` and `θ(x) - x` down to
   `O(√x log² x)` using only `{x, λ₀ x}`.

3. **Cramér-scale short-interval prime theorem under `FiniteOffLine` and World-II contrapositive**
   (`norm_cpow_increment_le`, `norm_cpow_increment_sub_linear_le`,
   `finiteOffLine_short_interval_psi_and_theta`, `finiteOffLine_exists_prime_in_cramer_interval`,
   `singleQuartet_exists_prime_in_cramer_interval`, `infinite_offLine_of_cramer_prime_gap_failure`):
   Every smooth off-line mode `x^ρ / ρ` (`Re ρ < 1`) changes across `[x, x + h]` by at most
   `h x^{Re ρ - 1} = o(h)`. Hence under `BacklundConverse.FiniteOffLine` (covering both
   `RiemannHypothesis` and `HasSingleOffLineQuartet ρ₀`), there exists `C > 0` such that every
   sufficiently large interval `(x, x + C √x log² x]` contains a prime; contrapositively, any
   failure of Cramér-scale prime gaps forces infinitely many off-line zeros of `ζ`.

4. **Pointwise (`3/2 - Re ρ₀`) and `L²` (`2 - 2 Re ρ₀`) short-interval crossover thresholds**
   (`singleQuartet_short_interval_subcritical_rh_bound`,
   `singleQuartet_short_interval_supercritical_both_signs`,
   `singleQuartet_wave_short_interval_L2_crossover`):
   Under `HasSingleOffLineQuartet ρ₀`, `ψ(x + x^α) - ψ(x) - x^α` and `θ(x + x^α) - θ(x) - x^α` obey
   the RH bound `O(√x log² x)` for all `0 < α ≤ 3/2 - Re ρ₀`, take both signs `± c X^{α + Re ρ₀ - 1}`
   on every large dyadic interval `[X, 2X]` for `3/2 - Re ρ₀ < α < 1`, while the `L²` energy of the
   quartet wave increment across `[X, 2X]` scales as `asymp h² X^{2 Re ρ₀ - 1}`, crossing the
   critical-line variance scale `X h log² X` already at the strictly smaller exponent
   `α = 2 - 2 Re ρ₀ < 3/2 - Re ρ₀ < 1`.

5. **Shifted `ξ`-sum half-plane nonvanishing and vertical-line zero uniqueness**
   (`xi_add_shift_ne_zero_of_singleQuartet`,
   `riemannZeta_re_eq_zero_iff_abs_im_eq_of_singleQuartet`):
   Under `HasSingleOffLineQuartet ρ₀`, `ξ(s) + ξ(s - 2h) ≠ 0` holds whenever `h ≥ Re ρ₀ - 1/2` and
   `Re s ≠ 1/2 + h`, and on the vertical line `Re s = Re ρ₀` the zeros of `ζ` are precisely
   `Re ρ₀ ± i Im ρ₀`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Finset MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ## 1. Unified `OutsideQuartetOnLine` bifurcation and single-wave Chebyshev law -/

/-- Every strip zero of `ζ` outside `zeroQuartetSet ρ₀` lies on the critical line `Re s = 1/2`. -/
def OutsideQuartetOnLine (ρ₀ : ℂ) : Prop :=
  ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ ∉ zeroQuartetSet ρ₀ → ρ.re = 1 / 2

private theorem xiZeroCopy_mem_carrier_local (q : RHTower.XiZeroCopy) :
    (q.1 : ℂ) ∈ Zeta23.zetaZeroConfig.carrier := by
  have h0 := RHTower.xiZeroCopy_re_pos q
  have h1 := RHTower.xiZeroCopy_re_lt_one q
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
    (RHTower.xi_eq_zero_of_mem_divisor_support q.1)
  exact ⟨hζ, h0, h1⟩

private theorem mem_carrier_iff_quartetCopyMult_pos {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ ∈ Zeta23.zetaZeroConfig.carrier ↔ 0 < quartetCopyMult ρ := by
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  constructor
  · rintro ⟨hζ, -, -⟩
    have hxi : RHTower.xi ρ = 0 := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ
    obtain ⟨q, hq_eq⟩ := RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
    have hpos := RHTower.xi_divisor_pos_on_support q.1
    unfold quartetCopyMult
    rw [← hq_eq]
    omega
  · intro hpos
    have hdiv_pos : 0 < (MeromorphicOn.divisor RHTower.xi Set.univ) ρ := by
      unfold quartetCopyMult at hpos
      omega
    have hmem_supp : ρ ∈ (MeromorphicOn.divisor RHTower.xi Set.univ).support :=
      Function.mem_support.mpr (ne_of_gt hdiv_pos)
    have hxi : RHTower.xi ρ = 0 :=
      RHTower.xi_eq_zero_of_mem_divisor_support ⟨ρ, hmem_supp⟩
    exact ⟨(RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp hxi, h0, h1⟩

private theorem quartetCopyMult_eq_of_mem_zeroQuartetSet {ρ₀ ρ : ℂ}
    (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    quartetCopyMult ρ = quartetCopyMult ρ₀ := by
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
  rcases hρ with rfl | rfl | rfl | rfl
  · rfl
  · exact quartetCopyMult_conj ρ₀
  · exact quartetCopyMult_one_sub ρ₀
  · exact quartetCopyMult_one_sub_conj ρ₀

/-- `RiemannHypothesis` implies `OutsideQuartetOnLine ρ₀` for every `ρ₀ ∈ ℂ`. -/
theorem outsideQuartetOnLine_of_riemannHypothesis (hRH : RiemannHypothesis) (ρ₀ : ℂ) :
    OutsideQuartetOnLine ρ₀ :=
  fun ρ hρ _ =>
    (GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH) ρ hρ

/-- Exact equivalence between `HasSingleOffLineQuartet ρ₀` and `OutsideQuartetOnLine ρ₀` at a
right-of-line strip zero `ρ₀`. -/
theorem hasSingleOffLineQuartet_iff_outsideQuartetOnLine (ρ₀ : ℂ) :
    HasSingleOffLineQuartet ρ₀ ↔
      1 / 2 < ρ₀.re ∧ ρ₀ ∈ Zeta23.zetaZeroConfig.carrier ∧ OutsideQuartetOnLine ρ₀ := by
  constructor
  · rintro ⟨hre, hmem, heq⟩
    refine ⟨hre, hmem, fun ρ hρ hnot => ?_⟩
    by_contra hne
    exact hnot (heq ▸ ⟨hρ, hne⟩)
  · rintro ⟨hre, hmem, hout⟩
    refine ⟨hre, hmem, Set.Subset.antisymm ?_ ?_⟩
    · rintro ρ ⟨hρ, hne⟩
      by_contra hnot
      exact hne (hout ρ hρ hnot)
    · intro ρ hρ_q
      have hne1_0 : ρ₀ ≠ 1 := fun h => by
        have := hmem.2.2; rw [h, Complex.one_re] at this; exact lt_irrefl 1 this
      have hxi0 : RHTower.xi ρ₀ = 0 :=
        (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hmem.2.1 hne1_0).mpr hmem.1
      have hmem_of_xi : ∀ {z : ℂ}, RHTower.xi z = 0 → z ∈ Zeta23.zetaZeroConfig.carrier := by
        intro z hxi
        obtain ⟨q, hq_eq⟩ := RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
        rw [← hq_eq]
        exact xiZeroCopy_mem_carrier_local q
      simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ_q
      rcases hρ_q with rfl | rfl | rfl | rfl
      · exact ⟨hmem, ne_of_gt hre⟩
      · refine ⟨hmem_of_xi (by rw [RHTower.xi_conj, hxi0, map_zero]), ?_⟩
        rw [Complex.conj_re]; exact ne_of_gt hre
      · refine ⟨hmem_of_xi (by rw [RHTower.xi_one_sub]; exact hxi0), ?_⟩
        rw [Complex.sub_re, Complex.one_re]; linarith
      · refine ⟨hmem_of_xi (by rw [RHTower.xi_one_sub, RHTower.xi_conj, hxi0, map_zero]), ?_⟩
        rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith

/-- **Exact multiplicity dichotomy under `OutsideQuartetOnLine ρ₀`.**
For `1/2 < Re ρ₀ < 1`, `OutsideQuartetOnLine ρ₀` splits cleanly into `RiemannHypothesis`
(`quartetCopyMult ρ₀ = 0`) and `HasSingleOffLineQuartet ρ₀` (`1 ≤ quartetCopyMult ρ₀`). -/
theorem outsideQuartetOnLine_dichotomy {ρ₀ : ℂ} (hre : 1 / 2 < ρ₀.re) (hlt1 : ρ₀.re < 1)
    (hout : OutsideQuartetOnLine ρ₀) :
    (RiemannHypothesis ∧ quartetCopyMult ρ₀ = 0) ∨
      (HasSingleOffLineQuartet ρ₀ ∧ 1 ≤ quartetCopyMult ρ₀) := by
  have h0 : 0 < ρ₀.re := by linarith
  by_cases hm : quartetCopyMult ρ₀ = 0
  · left
    refine ⟨?_, hm⟩
    rw [GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine]
    intro ρ hcar
    have hpos : 0 < quartetCopyMult ρ :=
      (mem_carrier_iff_quartetCopyMult_pos hcar.2.1 hcar.2.2).mp hcar
    have hnot : ρ ∉ zeroQuartetSet ρ₀ := by
      intro hmem
      rw [quartetCopyMult_eq_of_mem_zeroQuartetSet hmem, hm] at hpos
      exact lt_irrefl 0 hpos
    exact hout ρ hcar hnot
  · right
    have hpos : 0 < quartetCopyMult ρ₀ := Nat.pos_of_ne_zero hm
    have hcar : ρ₀ ∈ Zeta23.zetaZeroConfig.carrier :=
      (mem_carrier_iff_quartetCopyMult_pos h0 hlt1).mpr hpos
    exact ⟨(hasSingleOffLineQuartet_iff_outsideQuartetOnLine ρ₀).mpr ⟨hre, hcar, hout⟩, hpos⟩

/-- **Multiplicity-zero characterization of `RiemannHypothesis`.**
At any off-line strip point `ρ₀` (`1/2 < Re ρ₀ < 1`), `RiemannHypothesis` holds if and only if
`OutsideQuartetOnLine ρ₀` holds with `quartetCopyMult ρ₀ = 0`. -/
theorem riemannHypothesis_iff_outsideQuartetOnLine_and_mult_zero {ρ₀ : ℂ}
    (hre : 1 / 2 < ρ₀.re) (hlt1 : ρ₀.re < 1) :
    RiemannHypothesis ↔ OutsideQuartetOnLine ρ₀ ∧ quartetCopyMult ρ₀ = 0 := by
  constructor
  · intro hRH
    refine ⟨outsideQuartetOnLine_of_riemannHypothesis hRH ρ₀, ?_⟩
    by_contra hm
    have hcar : ρ₀ ∈ Zeta23.zetaZeroConfig.carrier :=
      (mem_carrier_iff_quartetCopyMult_pos (by linarith) hlt1).mpr (Nat.pos_of_ne_zero hm)
    have hhalf :=
      (GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH)
        ρ₀ hcar
    linarith
  · rintro ⟨hout, hm⟩
    rcases outsideQuartetOnLine_dichotomy hre hlt1 hout with ⟨hRH, -⟩ | ⟨-, hpos⟩
    · exact hRH
    · omega

private theorem abs_psi_sub_theta_le_sqrt_log_sq {y : ℝ} (hy : 16 ≤ y) :
    |Chebyshev.psi y - Chebyshev.theta y| ≤ 2 * Real.sqrt y * Real.log y ^ 2 := by
  have hdiff := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ y)
  have hnn : 0 ≤ Chebyshev.psi y - Chebyshev.theta y :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi y)
  have hlog2 : 2 ≤ Real.log y := RHTower.two_le_log_of_sixteen_le hy
  rw [abs_of_nonneg hnn]
  calc Chebyshev.psi y - Chebyshev.theta y
      ≤ 2 * Real.sqrt y * Real.log y := hdiff
    _ ≤ 2 * Real.sqrt y * Real.log y ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)

/-- **Unified single-wave Chebyshev law under `OutsideQuartetOnLine ρ₀`.**
Uniformly across `m = quartetCopyMult ρ₀ = 0` (`RiemannHypothesis`) and `m ≥ 1`
(`HasSingleOffLineQuartet ρ₀`), both `ψ(x) - x` and `θ(x) - x` equal `-2 m Re(x^{ρ₀}/ρ₀)` up to
`O(√x log² x)` for all `x ≥ 16`. -/
theorem outsideQuartetOnLine_chebyshevPsi_and_theta_wave {ρ₀ : ℂ}
    (hre : 1 / 2 < ρ₀.re) (hlt1 : ρ₀.re < 1) (hout : OutsideQuartetOnLine ρ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤
        K * Real.sqrt x * Real.log x ^ 2 ∧
      |Chebyshev.theta x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤
        (K + 2) * Real.sqrt x * Real.log x ^ 2 := by
  rcases outsideQuartetOnLine_dichotomy hre hlt1 hout with ⟨hRH, hm0⟩ | ⟨hq, -⟩
  · set K₀ : ℝ := 200 * (RHTower.xiLineTwoLogDerivConstant + 2)
    have hK₀ : 0 ≤ K₀ := by
      have := RHTower.xiLineTwoLogDerivConstant_nonneg
      dsimp [K₀]; positivity
    refine ⟨K₀, hK₀, fun x hx => ?_⟩
    have hempty : ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → q ∈ (∅ : Finset RHTower.XiZeroCopy) := by
      intro q hne
      have hhalf :=
        (GaloisForLFunctions.SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH)
          (q.1 : ℂ) (xiZeroCopy_mem_carrier_local q)
      exact absurd hhalf hne
    have hpsi := RHTower.abs_chebyshevPsi_sub_add_offLineWave_le (S := ∅) hempty hx
    simp only [RHTower.offLineWave, Finset.sum_empty, Complex.zero_re, add_zero,
      Finset.card_empty, Nat.cast_zero, mul_zero] at hpsi
    simp only [hm0, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine ⟨hpsi, ?_⟩
    have hsplit : Chebyshev.theta x - x =
        (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [hsplit]
    calc |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)|
        ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ ≤ K₀ * Real.sqrt x * Real.log x ^ 2 + 2 * Real.sqrt x * Real.log x ^ 2 :=
          add_le_add hpsi (abs_psi_sub_theta_le_sqrt_log_sq hx)
      _ = (K₀ + 2) * Real.sqrt x * Real.log x ^ 2 := by ring
  · obtain ⟨K₁, hK₁⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1 hq.2.1).mp hq
    refine ⟨|K₁|, abs_nonneg K₁, fun x hx => ?_⟩
    have hpsi : |Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤
        |K₁| * Real.sqrt x * Real.log x ^ 2 :=
      (hK₁ x hx).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K₁) (Real.sqrt_nonneg x)) (sq_nonneg _))
    refine ⟨hpsi, ?_⟩
    have hsplit : Chebyshev.theta x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re =
        (Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re) -
          (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [hsplit]
    calc _ ≤ |Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re| +
              |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ ≤ |K₁| * Real.sqrt x * Real.log x ^ 2 + 2 * Real.sqrt x * Real.log x ^ 2 :=
          add_le_add hpsi (abs_psi_sub_theta_le_sqrt_log_sq hx)
      _ = (|K₁| + 2) * Real.sqrt x * Real.log x ^ 2 := by ring

/-! ## 2. Two-point half-period annihilation operator and secular polynomial-wave cancellation -/

/-- Multiplicative half-period `λ₀(ρ₀) = exp(π / |Im ρ₀|)` reversing the phase of `x^{ρ₀}`. -/
def quartetHalfPeriodScale (ρ₀ : ℂ) : ℝ :=
  Real.exp (Real.pi / |ρ₀.im|)

/-- Two-point linear half-period operator `(𝓓_{ρ₀} F)(x) = F(λ₀ x) + λ₀^{Re ρ₀} F(x)`. -/
def halfPeriodAnnihilator (ρ₀ : ℂ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  F (quartetHalfPeriodScale ρ₀ * x) + quartetHalfPeriodScale ρ₀ ^ ρ₀.re * F x

theorem quartetHalfPeriodScale_pos (ρ₀ : ℂ) : 0 < quartetHalfPeriodScale ρ₀ :=
  Real.exp_pos _

theorem quartetHalfPeriodScale_gt_one {ρ₀ : ℂ} (him : ρ₀.im ≠ 0) :
    1 < quartetHalfPeriodScale ρ₀ :=
  Real.one_lt_exp_iff.mpr (div_pos Real.pi_pos (abs_pos.mpr him))

/-- Under `HasSingleOffLineQuartet ρ₀`, `|Im ρ₀| > 67` forces `quartetHalfPeriodScale ρ₀ ∈ (1, 2)`. -/
theorem quartetHalfPeriodScale_lt_two_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    1 < quartetHalfPeriodScale ρ₀ ∧ quartetHalfPeriodScale ρ₀ < 2 := by
  have h67 : 67 < |ρ₀.im| :=
    sixtySeven_lt_abs_im_of_offLine_zeta_zero hq.2.1.1 hq.2.1.2.1 hq.2.1.2.2 (by linarith [hq.1])
  refine ⟨quartetHalfPeriodScale_gt_one hq.im_ne_zero, ?_⟩
  rw [quartetHalfPeriodScale, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine Real.exp_lt_exp.mpr ?_
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hdiv : Real.pi / |ρ₀.im| < 4 / 67 := by
    calc Real.pi / |ρ₀.im| < 4 / |ρ₀.im| := div_lt_div_of_pos_right hpi (by linarith)
      _ < 4 / 67 := div_lt_div_of_pos_left (by norm_num) (by norm_num) h67
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  linarith

/-- **Half-period phase reversal:** `(exp(π / |Im ρ₀|))^{ρ₀} = -(exp(π / |Im ρ₀|))^{Re ρ₀}`. -/
theorem quartetHalfPeriodScale_cpow {ρ₀ : ℂ} (him : ρ₀.im ≠ 0) :
    (quartetHalfPeriodScale ρ₀ : ℂ) ^ ρ₀ = -((quartetHalfPeriodScale ρ₀ ^ ρ₀.re : ℝ) : ℂ) := by
  set lam0 := quartetHalfPeriodScale ρ₀
  have hlam_pos : 0 < lam0 := quartetHalfPeriodScale_pos ρ₀
  have hlam_ne : (lam0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam_pos.ne'
  have hlog : Real.log lam0 = Real.pi / |ρ₀.im| := Real.log_exp _
  rw [Complex.cpow_def_of_ne_zero hlam_ne, ← Complex.ofReal_log hlam_pos.le]
  have hexp_split : ((Real.log lam0 : ℝ) : ℂ) * ρ₀ =
      ((Real.log lam0 * ρ₀.re : ℝ) : ℂ) + ((Real.log lam0 * ρ₀.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hexp_split, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hlam_pos]
  have him_phase : Complex.exp (((Real.log lam0 * ρ₀.im : ℝ) : ℂ) * I) = -1 := by
    rw [hlog]
    rcases lt_or_gt_of_ne him with hneg | hpos
    · rw [abs_of_neg hneg, show Real.pi / -ρ₀.im * ρ₀.im = -Real.pi by field_simp [him]]
      rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    · rw [abs_of_pos hpos, div_mul_cancel₀ _ him, Complex.exp_pi_mul_I]
  rw [him_phase, mul_neg, mul_one]

theorem halfPeriodAnnihilator_add (ρ₀ : ℂ) (F G : ℝ → ℝ) (x : ℝ) :
    halfPeriodAnnihilator ρ₀ (fun y => F y + G y) x =
      halfPeriodAnnihilator ρ₀ F x + halfPeriodAnnihilator ρ₀ G x := by
  unfold halfPeriodAnnihilator; ring

theorem halfPeriodAnnihilator_sub (ρ₀ : ℂ) (F G : ℝ → ℝ) (x : ℝ) :
    halfPeriodAnnihilator ρ₀ (fun y => F y - G y) x =
      halfPeriodAnnihilator ρ₀ F x - halfPeriodAnnihilator ρ₀ G x := by
  unfold halfPeriodAnnihilator; ring

theorem halfPeriodAnnihilator_const_mul (ρ₀ : ℂ) (a : ℝ) (F : ℝ → ℝ) (x : ℝ) :
    halfPeriodAnnihilator ρ₀ (fun y => a * F y) x = a * halfPeriodAnnihilator ρ₀ F x := by
  unfold halfPeriodAnnihilator; ring

private theorem iterate_halfPeriodAnnihilator_congr_pos (ρ₀ : ℂ) :
    ∀ (m : ℕ) {F G : ℝ → ℝ}, (∀ y : ℝ, 0 < y → F y = G y) →
      ∀ {x : ℝ}, 0 < x → ((halfPeriodAnnihilator ρ₀)^[m] F) x = ((halfPeriodAnnihilator ρ₀)^[m] G) x
  | 0, _, _, hFG, _, hx => hFG _ hx
  | m + 1, F, G, hFG, x, hx => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      refine iterate_halfPeriodAnnihilator_congr_pos ρ₀ m (fun y hy => ?_) hx
      unfold halfPeriodAnnihilator
      rw [hFG _ (mul_pos (quartetHalfPeriodScale_pos ρ₀) hy), hFG y hy]

private theorem iterate_halfPeriodAnnihilator_finset_sum (ρ₀ : ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) :
    ∀ (m : ℕ) (x : ℝ),
      ((halfPeriodAnnihilator ρ₀)^[m] (fun y => ∑ i ∈ s, f i y)) x =
        ∑ i ∈ s, ((halfPeriodAnnihilator ρ₀)^[m] (f i)) x := by
  classical
  intro m
  induction m generalizing f with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [Function.iterate_succ_apply]
    have hstep : halfPeriodAnnihilator ρ₀ (fun y => ∑ i ∈ s, f i y) =
        fun y => ∑ i ∈ s, halfPeriodAnnihilator ρ₀ (f i) y := by
      funext y
      unfold halfPeriodAnnihilator
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [hstep, ih]
    exact Finset.sum_congr rfl fun i _ =>
      (congrFun (Function.iterate_succ_apply (halfPeriodAnnihilator ρ₀) m (f i)) x).symm

/-- **Exact two-point annihilation of `Re(c x^{ρ₀})`.** -/
theorem halfPeriodAnnihilator_re_cpow_eq_zero {ρ₀ : ℂ} (him : ρ₀.im ≠ 0) (c : ℂ)
    {x : ℝ} (hx : 0 < x) :
    halfPeriodAnnihilator ρ₀ (fun y => (c * (y : ℂ) ^ ρ₀).re) x = 0 := by
  set lam0 := quartetHalfPeriodScale ρ₀
  have hlam_pos : 0 < lam0 := quartetHalfPeriodScale_pos ρ₀
  have hmul : ((lam0 * x : ℝ) : ℂ) ^ ρ₀ = (lam0 : ℂ) ^ ρ₀ * (x : ℂ) ^ ρ₀ := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hlam_pos.le hx.le]
  unfold halfPeriodAnnihilator
  change (c * ((lam0 * x : ℝ) : ℂ) ^ ρ₀).re + lam0 ^ ρ₀.re * (c * (x : ℂ) ^ ρ₀).re = 0
  rw [hmul, quartetHalfPeriodScale_cpow him]
  have h1 : c * (-((lam0 ^ ρ₀.re : ℝ) : ℂ) * (x : ℂ) ^ ρ₀) =
      -((lam0 ^ ρ₀.re : ℝ) : ℂ) * (c * (x : ℂ) ^ ρ₀) := by ring
  rw [h1, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  ring

/-- **Higher-multiplicity secular polynomial-wave cancellation.**
For any `m ∈ ℕ`, `k < m`, `c ∈ ℂ`, and `x > 0`, the `m`-fold iterate `(halfPeriodAnnihilator ρ₀)^[m]`
annihilates `y ↦ Re(c y^{ρ₀} (log y)^k)` identically. -/
theorem iterate_halfPeriodAnnihilator_re_cpow_log_pow_eq_zero {ρ₀ : ℂ} (him : ρ₀.im ≠ 0) :
    ∀ (m : ℕ) {k : ℕ}, k < m → ∀ (c : ℂ) {x : ℝ}, 0 < x →
      ((halfPeriodAnnihilator ρ₀)^[m]
        (fun y => (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k).re)) x = 0 := by
  intro m
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk c x hx
    set lam0 := quartetHalfPeriodScale ρ₀
    have hlam_pos : 0 < lam0 := quartetHalfPeriodScale_pos ρ₀
    rw [Function.iterate_succ_apply]
    let g : ℝ → ℝ := fun y =>
      ∑ j ∈ Finset.range k,
        ((-(lam0 ^ ρ₀.re : ℂ) * c * (Nat.choose k j : ℂ) *
          (Real.log lam0 : ℂ) ^ (k - j)) * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ j).re
    have hstep_pos : ∀ y : ℝ, 0 < y →
        halfPeriodAnnihilator ρ₀ (fun u => (c * (u : ℂ) ^ ρ₀ * (Real.log u : ℂ) ^ k).re) y = g y := by
      intro y hy
      unfold halfPeriodAnnihilator
      have hmul : ((lam0 * y : ℝ) : ℂ) ^ ρ₀ = (lam0 : ℂ) ^ ρ₀ * (y : ℂ) ^ ρ₀ := by
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hlam_pos.le hy.le]
      have hlog_mul : Real.log (lam0 * y) = Real.log y + Real.log lam0 := by
        rw [Real.log_mul hlam_pos.ne' hy.ne', add_comm]
      have hbinom : ((Real.log (lam0 * y) : ℝ) : ℂ) ^ k - (Real.log y : ℂ) ^ k =
          ∑ j ∈ Finset.range k,
            (Real.log y : ℂ) ^ j * (Real.log lam0 : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) := by
        rw [hlog_mul, Complex.ofReal_add, add_pow, Finset.sum_range_succ,
          Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
      have hcomb : c * ((lam0 * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (lam0 * y) : ℝ) : ℂ) ^ k +
          ((lam0 ^ ρ₀.re : ℝ) : ℂ) * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k) =
          -(lam0 ^ ρ₀.re : ℂ) * c * (y : ℂ) ^ ρ₀ *
            (((Real.log (lam0 * y) : ℝ) : ℂ) ^ k - (Real.log y : ℂ) ^ k) := by
        rw [hmul, quartetHalfPeriodScale_cpow him]
        push_cast; ring
      have hre_lhs : (c * ((lam0 * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (lam0 * y) : ℝ) : ℂ) ^ k).re +
          lam0 ^ ρ₀.re * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k).re =
          (c * ((lam0 * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (lam0 * y) : ℝ) : ℂ) ^ k +
            ((lam0 ^ ρ₀.re : ℝ) : ℂ) * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k)).re := by
        rw [Complex.add_re, Complex.re_ofReal_mul]
      change (c * ((lam0 * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (lam0 * y) : ℝ) : ℂ) ^ k).re +
        lam0 ^ ρ₀.re * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k).re = g y
      rw [hre_lhs, hcomb, hbinom, Finset.mul_sum, Complex.re_sum]
      dsimp [g]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; ring
    rw [iterate_halfPeriodAnnihilator_congr_pos ρ₀ m hstep_pos hx]
    dsimp [g]
    rw [iterate_halfPeriodAnnihilator_finset_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_lt : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.lt_succ_iff.mp hk)
    exact ih hj_lt _ hx

/-- **Two-point half-period Chebyshev cancellation under `OutsideQuartetOnLine ρ₀`.**
Under `OutsideQuartetOnLine ρ₀` (`1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`) — and hence under
`HasSingleOffLineQuartet ρ₀` — applying `halfPeriodAnnihilator ρ₀` cancels the `x^{Re ρ₀}` prime
wave identically using only `{x, λ₀ x}`, leaving `O(√x log² x)` for both `ψ(x) - x` and `θ(x) - x`. -/
theorem outsideQuartetOnLine_halfPeriod_chebyshev_cancellation {ρ₀ : ℂ}
    (hre : 1 / 2 < ρ₀.re) (hlt1 : ρ₀.re < 1) (him : ρ₀.im ≠ 0)
    (hout : OutsideQuartetOnLine ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 16 ≤ x →
      |halfPeriodAnnihilator ρ₀ (fun y => Chebyshev.psi y - y) x| ≤
        C * Real.sqrt x * Real.log x ^ 2 ∧
      |halfPeriodAnnihilator ρ₀ (fun y => Chebyshev.theta y - y) x| ≤
        C * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hwave⟩ := outsideQuartetOnLine_chebyshevPsi_and_theta_wave hre hlt1 hout
  set lam0 := quartetHalfPeriodScale ρ₀
  have hlam1 : 1 < lam0 := quartetHalfPeriodScale_gt_one him
  have hlam_pos : 0 < lam0 := by linarith
  set M : ℝ := Real.sqrt lam0 * (1 + Real.log lam0) ^ 2 + lam0 ^ ρ₀.re
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(K + 2) * M, mul_nonneg (by linarith) hM0, fun x hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hlamx16 : 16 ≤ lam0 * x := by nlinarith
  have hlog2 : 2 ≤ Real.log x := RHTower.two_le_log_of_sixteen_le hx
  have hlog_lamx : Real.log (lam0 * x) ^ 2 ≤ (1 + Real.log lam0) ^ 2 * Real.log x ^ 2 := by
    rw [Real.log_mul hlam_pos.ne' hx_pos.ne']
    have hloglam_nn : 0 ≤ Real.log lam0 := Real.log_nonneg hlam1.le
    have hle : Real.log lam0 + Real.log x ≤ (1 + Real.log lam0) * Real.log x := by nlinarith
    have hnn1 : 0 ≤ Real.log lam0 + Real.log x := by linarith
    nlinarith [mul_self_le_mul_self hnn1 hle, mul_pow (1 + Real.log lam0) (Real.log x) 2]
  have hscale_err : Real.sqrt (lam0 * x) * Real.log (lam0 * x) ^ 2 ≤
      Real.sqrt lam0 * (1 + Real.log lam0) ^ 2 * (Real.sqrt x * Real.log x ^ 2) := by
    rw [Real.sqrt_mul hlam_pos.le]
    calc Real.sqrt lam0 * Real.sqrt x * Real.log (lam0 * x) ^ 2
        ≤ Real.sqrt lam0 * Real.sqrt x * ((1 + Real.log lam0) ^ 2 * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlog_lamx (by positivity)
      _ = Real.sqrt lam0 * (1 + Real.log lam0) ^ 2 * (Real.sqrt x * Real.log x ^ 2) := by ring
  let W : ℝ → ℝ := fun y => -(2 * (quartetCopyMult ρ₀ : ℝ) * (ρ₀⁻¹ * (y : ℂ) ^ ρ₀).re)
  have hW_zero : halfPeriodAnnihilator ρ₀ W x = 0 := by
    have h0 := halfPeriodAnnihilator_re_cpow_eq_zero him (ρ₀⁻¹) hx_pos
    have h1 := halfPeriodAnnihilator_const_mul ρ₀ (-(2 * (quartetCopyMult ρ₀ : ℝ)))
      (fun y => (ρ₀⁻¹ * (y : ℂ) ^ ρ₀).re) x
    change halfPeriodAnnihilator ρ₀
      (fun y => -(2 * (quartetCopyMult ρ₀ : ℝ)) * (ρ₀⁻¹ * (y : ℂ) ^ ρ₀).re) x = 0
    rw [h1, h0, mul_zero]
  have herr_bound : ∀ {E : ℝ → ℝ},
      (∀ y : ℝ, 16 ≤ y → |E y - W y| ≤ (K + 2) * Real.sqrt y * Real.log y ^ 2) →
      |halfPeriodAnnihilator ρ₀ E x| ≤ (K + 2) * M * Real.sqrt x * Real.log x ^ 2 := by
    intro E hE
    have hdecomp : E = fun y => (E y - W y) + W y := by funext y; ring
    rw [hdecomp, halfPeriodAnnihilator_add, hW_zero, add_zero]
    unfold halfPeriodAnnihilator
    have h1 := hE (lam0 * x) hlamx16
    have h2 := hE x hx
    calc |(E (lam0 * x) - W (lam0 * x)) + lam0 ^ ρ₀.re * (E x - W x)|
        ≤ |E (lam0 * x) - W (lam0 * x)| + |lam0 ^ ρ₀.re * (E x - W x)| := abs_add_le _ _
      _ = |E (lam0 * x) - W (lam0 * x)| + lam0 ^ ρ₀.re * |E x - W x| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hlam_pos _)]
      _ ≤ (K + 2) * (Real.sqrt (lam0 * x) * Real.log (lam0 * x) ^ 2) +
            lam0 ^ ρ₀.re * ((K + 2) * (Real.sqrt x * Real.log x ^ 2)) := by
          refine add_le_add (by linarith) ?_
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (K + 2) * (Real.sqrt lam0 * (1 + Real.log lam0) ^ 2 * (Real.sqrt x * Real.log x ^ 2)) +
            lam0 ^ ρ₀.re * ((K + 2) * (Real.sqrt x * Real.log x ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hscale_err (by linarith)) le_rfl
      _ = (K + 2) * M * Real.sqrt x * Real.log x ^ 2 := by dsimp [M]; ring
  have hW_eq : ∀ y : ℝ, -W y = 2 * (quartetCopyMult ρ₀ : ℝ) * ((y : ℂ) ^ ρ₀ / ρ₀).re := by
    intro y; dsimp [W]; rw [div_eq_inv_mul]; ring
  constructor
  · refine herr_bound fun y hy => ?_
    rw [sub_eq_add_neg, hW_eq]
    exact (hwave y hy).1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg y)) (sq_nonneg _))
  · refine herr_bound fun y hy => ?_
    rw [sub_eq_add_neg, hW_eq]
    exact (hwave y hy).2

/-! ## 3. Cramér-scale short-interval prime theorem under `FiniteOffLine` and World-II forcing -/

/-- **First-order short-interval complex-power increment bound.**
For `ρ ≠ 0` with `Re ρ ≤ 1`, `x > 0`, and `h ≥ 0`, `‖((x + h)^ρ - x^ρ) / ρ‖ ≤ h x^{Re ρ - 1}`. -/
theorem norm_cpow_increment_le {ρ : ℂ} (hρ : ρ ≠ 0) (hre : ρ.re ≤ 1)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ‖ ≤ h * x ^ (ρ.re - 1) := by
  let s : Set ℝ := Set.Icc x (x + h)
  have hs_conv : Convex ℝ s := convex_Icc x (x + h)
  have hxs : x ∈ s := ⟨le_rfl, by linarith⟩
  have hys : x + h ∈ s := ⟨by linarith, le_rfl⟩
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ / ρ)
      ((t : ℂ) ^ (ρ - 1)) s t := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
    exact (((hasDerivAt_ofReal_cpow_const ht_pos.ne' hρ).div_const ρ).congr_deriv
      (mul_div_cancel_left₀ _ hρ)).hasDerivWithinAt
  have hbound : ∀ t ∈ s, ‖(t : ℂ) ^ (ρ - 1)‖ ≤ x ^ (ρ.re - 1) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  have hmvt := hs_conv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hxs hys
  rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh, mul_comm] at hmvt
  exact hmvt

/-- **Second-order short-interval Taylor approximation of `x^ρ / ρ`.**
For `ρ ≠ 0` with `Re ρ ≤ 2`, `x > 0`, and `h ≥ 0`,
`‖(x + h)^ρ / ρ - x^ρ / ρ - h x^{ρ - 1}‖ ≤ ‖ρ - 1‖ h² x^{Re ρ - 2}`. -/
theorem norm_cpow_increment_sub_linear_le {ρ : ℂ} (hρ : ρ ≠ 0) (hre : ρ.re ≤ 2)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ - (h : ℂ) * (x : ℂ) ^ (ρ - 1)‖ ≤
      ‖ρ - 1‖ * h ^ 2 * x ^ (ρ.re - 2) := by
  by_cases hr1 : ρ = 1
  · subst hr1
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    simp only [sub_self, Complex.cpow_zero, Complex.cpow_one, div_one, norm_zero, zero_mul]
    have h0 : ((x + h : ℝ) : ℂ) - (x : ℂ) - (h : ℂ) * 1 = 0 := by push_cast; ring
    rw [h0, norm_zero]
  · let s : Set ℝ := Set.Icc x (x + h)
    let g : ℝ → ℂ := fun y => (y : ℂ) ^ ρ / ρ - ((y : ℂ) - (x : ℂ)) * (x : ℂ) ^ (ρ - 1)
    let g' : ℝ → ℂ := fun y => (y : ℂ) ^ (ρ - 1) - (x : ℂ) ^ (ρ - 1)
    have hs_conv : Convex ℝ s := convex_Icc x (x + h)
    have hxs : x ∈ s := ⟨le_rfl, by linarith⟩
    have hys : x + h ∈ s := ⟨by linarith, le_rfl⟩
    have hg_deriv : ∀ t ∈ s, HasDerivWithinAt g (g' t) s t := by
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx ht.1
      have hd1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ ρ / ρ) ((t : ℂ) ^ (ρ - 1)) t :=
        ((hasDerivAt_ofReal_cpow_const ht_pos.ne' hρ).div_const ρ).congr_deriv
          (mul_div_cancel_left₀ _ hρ)
      have hd2 : HasDerivAt (fun y : ℝ => ((y : ℂ) - (x : ℂ)) * (x : ℂ) ^ (ρ - 1))
          ((x : ℂ) ^ (ρ - 1)) t := by
        have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) - (x : ℂ)) 1 t :=
          (Complex.ofRealCLM.hasDerivAt).sub_const (x : ℂ)
        simpa [one_mul] using hlin.mul_const ((x : ℂ) ^ (ρ - 1))
      exact (hd1.sub hd2).hasDerivWithinAt
    have hg'_bound : ∀ t ∈ s, ‖g' t‖ ≤ ‖ρ - 1‖ * h * x ^ (ρ.re - 2) := by
      intro t ht
      let s_t : Set ℝ := Set.Icc x t
      have hs_t : Convex ℝ s_t := convex_Icc x t
      have hd_sub : ∀ u ∈ s_t, HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (ρ - 1))
          ((ρ - 1) * (u : ℂ) ^ (ρ - 2)) s_t u := by
        intro u hu
        have hu_pos : 0 < u := lt_of_lt_of_le hx hu.1
        have hd := hasDerivAt_ofReal_cpow_const hu_pos.ne' (sub_ne_zero.mpr hr1)
        rw [show ρ - 1 - 1 = ρ - 2 by ring] at hd
        exact hd.hasDerivWithinAt
      have hb_sub : ∀ u ∈ s_t, ‖(ρ - 1) * (u : ℂ) ^ (ρ - 2)‖ ≤ ‖ρ - 1‖ * x ^ (ρ.re - 2) := by
        intro u hu
        have hu_pos : 0 < u := lt_of_lt_of_le hx hu.1
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu_pos,
          show (ρ - 2).re = ρ.re - 2 by simp]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hx hu.1 (by linarith)) (norm_nonneg _)
      have hmvt_t := hs_t.norm_image_sub_le_of_norm_hasDerivWithin_le hd_sub hb_sub
        ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
      have hth : t - x ≤ h := by linarith [ht.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - x)] at hmvt_t
      calc ‖g' t‖ ≤ (‖ρ - 1‖ * x ^ (ρ.re - 2)) * (t - x) := hmvt_t
        _ ≤ (‖ρ - 1‖ * x ^ (ρ.re - 2)) * h :=
            mul_le_mul_of_nonneg_left hth (by positivity)
        _ = ‖ρ - 1‖ * h * x ^ (ρ.re - 2) := by ring
    have hmvt := hs_conv.norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv hg'_bound hxs hys
    have hdiff_eq : g (x + h) - g x =
        ((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ - (h : ℂ) * (x : ℂ) ^ (ρ - 1) := by
      dsimp [g]
      push_cast
      ring
    rw [hdiff_eq, add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh] at hmvt
    calc ‖((x + h : ℝ) : ℂ) ^ ρ / ρ - (x : ℂ) ^ ρ / ρ - (h : ℂ) * (x : ℂ) ^ (ρ - 1)‖
        ≤ ‖ρ - 1‖ * h * x ^ (ρ.re - 2) * h := hmvt
      _ = ‖ρ - 1‖ * h ^ 2 * x ^ (ρ.re - 2) := by ring

private theorem exists_prime_Ioc_of_theta_sub_pos {x y : ℝ} (hx : 0 ≤ x)
    (hpos : 0 < Chebyshev.theta y - Chebyshev.theta x) :
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_contra hnone
  push Not at hnone
  have hy0 : 0 ≤ y := by
    by_contra hlt
    rw [Chebyshev.theta_eq_zero_of_lt_two (by linarith)] at hpos
    linarith [Chebyshev.theta_nonneg x]
  have hsub : (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp_ioc, hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp0, hpy⟩ := Finset.mem_Ioc.mp hp_ioc
    have hpy_real : (p : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp hpy
    have hpx_real : (p : ℝ) ≤ x := by
      by_contra hgt
      exact absurd hpy_real (not_le.mpr (hnone p hprime (not_le.mp hgt)))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp0, (Nat.le_floor_iff hx).mpr hpx_real⟩, hprime⟩
  have hle : Chebyshev.theta y ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  linarith

/-- **Uniform short-interval `ψ` and `θ` asymptotics under `BacklundConverse.FiniteOffLine`.**
Whenever `ξ` has only finitely many off-line zeros, there exist `K ≥ 0` and `betaStar ∈ [1/2, 1)` such
that for all `x ≥ 16` and `0 ≤ h ≤ x`, both `|ψ(x + h) - ψ(x) - h|` and `|θ(x + h) - θ(x) - h|`
are bounded by `K √x log² x + K h x^{betaStar - 1}`. -/
theorem finiteOffLine_short_interval_psi_and_theta
    (hfin : RHTower.BacklundConverse.FiniteOffLine) :
    ∃ (K betaStar : ℝ), 0 ≤ K ∧ 1 / 2 ≤ betaStar ∧ betaStar < 1 ∧
      ∀ {x h : ℝ}, 16 ≤ x → 0 ≤ h → h ≤ x →
        |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤
          K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (betaStar - 1) ∧
        |Chebyshev.theta (x + h) - Chebyshev.theta x - h| ≤
          K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (betaStar - 1) := by
  classical
  have hfin_re : {q : RHTower.XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
    refine hfin.subset fun q hne => ?_
    have him : (RHTower.xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [RHTower.xiSpectralPoint, Complex.mul_im]
    intro h0; exact hne (by linarith)
  obtain ⟨K₀, hK₀, hvk⟩ := RHTower.exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite hfin_re
  set S : Finset RHTower.XiZeroCopy := hfin_re.toFinset
  let betaStar : ℝ := (1 / 2 : ℝ) ⊔ (if hS : S.Nonempty then S.sup' hS (fun q => (q.1 : ℂ).re) else 1 / 2)
  have hβ_ge : 1 / 2 ≤ betaStar := le_sup_left
  have hβ_lt1 : betaStar < 1 := by
    dsimp [betaStar]
    refine sup_lt_iff.mpr ⟨by norm_num, ?_⟩
    split_ifs with hS
    · exact (Finset.sup'_lt_iff hS).mpr fun q _ => RHTower.xiZeroCopy_re_lt_one q
    · norm_num
  have hq_le_β : ∀ q ∈ S, (q.1 : ℂ).re ≤ betaStar := by
    intro q hq
    refine le_trans ?_ (le_sup_right : _ ≤ betaStar)
    rw [dif_pos ⟨q, hq⟩]
    exact Finset.le_sup' (fun q : RHTower.XiZeroCopy => (q.1 : ℂ).re) hq
  set K : ℝ := 9 * (K₀ + 2) + (S.card : ℝ)
  refine ⟨K, betaStar, by dsimp [K]; positivity, hβ_ge, hβ_lt1, fun {x h} hx hh hhx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxh16 : 16 ≤ x + h := by linarith
  have hscale_xh : Real.sqrt (x + h) * Real.log (x + h) ^ 2 ≤
      8 * (Real.sqrt x * Real.log x ^ 2) := by
    have hxh_le : x + h ≤ 2 * x := by linarith
    have hsqrt_le : Real.sqrt (x + h) ≤ 2 * Real.sqrt x := by
      calc Real.sqrt (x + h) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hxh_le
        _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
        _ ≤ 2 * Real.sqrt x := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg x)
            rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
            exact Real.sqrt_le_sqrt (by norm_num)
    have hlog_sq : Real.log (x + h) ^ 2 ≤ 4 * Real.log x ^ 2 := by
      have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
      have hlog_xh : Real.log (x + h) ≤ 2 * Real.log x := by
        calc Real.log (x + h) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) hxh_le
          _ = Real.log 2 + Real.log x := Real.log_mul two_ne_zero hx_pos.ne'
          _ ≤ 2 * Real.log x := by linarith
      have hnn : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
      nlinarith
    calc Real.sqrt (x + h) * Real.log (x + h) ^ 2
        ≤ (2 * Real.sqrt x) * (4 * Real.log x ^ 2) :=
          mul_le_mul hsqrt_le hlog_sq (sq_nonneg _) (by positivity)
      _ = 8 * (Real.sqrt x * Real.log x ^ 2) := by ring
  have hwave_inc : |(RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re| ≤
      (S.card : ℝ) * h * x ^ (betaStar - 1) := by
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    unfold RHTower.offLineWave
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le S _).trans ?_
    calc ∑ q ∈ S, ‖((x + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) - (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖
        ≤ ∑ _q ∈ S, h * x ^ (betaStar - 1) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_ne : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
          have hq_lt1 := (RHTower.xiZeroCopy_re_lt_one q).le
          refine (norm_cpow_increment_le hq_ne hq_lt1 hx_pos hh).trans ?_
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hq_le_β q hq])) hh
      _ = (S.card : ℝ) * h * x ^ (betaStar - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  set η : ℝ → ℝ := fun y => Chebyshev.psi y - y + (RHTower.offLineWave S y).re
  have hpsi_split : Chebyshev.psi (x + h) - Chebyshev.psi x - h =
      η (x + h) - η x - ((RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re) := by
    dsimp [η]; ring
  have hη_xh : |η (x + h)| ≤ 8 * K₀ * (Real.sqrt x * Real.log x ^ 2) := by
    calc |η (x + h)| ≤ K₀ * (Real.sqrt (x + h) * Real.log (x + h) ^ 2) := by linarith [hvk (x + h) hxh16]
      _ ≤ K₀ * (8 * (Real.sqrt x * Real.log x ^ 2)) := mul_le_mul_of_nonneg_left hscale_xh hK₀
      _ = 8 * K₀ * (Real.sqrt x * Real.log x ^ 2) := by ring
  have hη_x : |η x| ≤ K₀ * (Real.sqrt x * Real.log x ^ 2) := by linarith [hvk x hx]
  have hpsi_bound : |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤
      9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (betaStar - 1) := by
    rw [hpsi_split]
    calc |η (x + h) - η x - ((RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re)|
        ≤ |η (x + h) - η x| + |(RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re| :=
          abs_sub _ _
      _ ≤ (|η (x + h)| + |η x|) + (S.card : ℝ) * h * x ^ (betaStar - 1) :=
          add_le_add (abs_sub _ _) hwave_inc
      _ ≤ 9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (betaStar - 1) := by
          linarith
  have hK_ge1 : 9 * K₀ ≤ K := by dsimp [K]; positivity
  have hK_ge2 : (S.card : ℝ) ≤ K := by dsimp [K]; positivity
  constructor
  · calc |Chebyshev.psi (x + h) - Chebyshev.psi x - h|
        ≤ 9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (betaStar - 1) := hpsi_bound
      _ ≤ K * (Real.sqrt x * Real.log x ^ 2) + K * (h * x ^ (betaStar - 1)) :=
          add_le_add (mul_le_mul_of_nonneg_right hK_ge1 (by positivity))
            (mul_le_mul_of_nonneg_right hK_ge2 (by positivity))
      _ = K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (betaStar - 1) := by ring
  · have hθ_split : Chebyshev.theta (x + h) - Chebyshev.theta x - h =
        (Chebyshev.psi (x + h) - Chebyshev.psi x - h) -
          (Chebyshev.psi (x + h) - Chebyshev.theta (x + h)) +
          (Chebyshev.psi x - Chebyshev.theta x) := by ring
    have hdiff_xh : |Chebyshev.psi (x + h) - Chebyshev.theta (x + h)| ≤
        16 * (Real.sqrt x * Real.log x ^ 2) := by
      calc |Chebyshev.psi (x + h) - Chebyshev.theta (x + h)|
          ≤ 2 * (Real.sqrt (x + h) * Real.log (x + h) ^ 2) := by
            linarith [abs_psi_sub_theta_le_sqrt_log_sq hxh16]
        _ ≤ 2 * (8 * (Real.sqrt x * Real.log x ^ 2)) :=
            mul_le_mul_of_nonneg_left hscale_xh (by norm_num)
        _ = 16 * (Real.sqrt x * Real.log x ^ 2) := by ring
    have hdiff_x : |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * (Real.sqrt x * Real.log x ^ 2) := by
      linarith [abs_psi_sub_theta_le_sqrt_log_sq hx]
    rw [hθ_split]
    calc |(Chebyshev.psi (x + h) - Chebyshev.psi x - h) -
            (Chebyshev.psi (x + h) - Chebyshev.theta (x + h)) +
            (Chebyshev.psi x - Chebyshev.theta x)|
        ≤ |Chebyshev.psi (x + h) - Chebyshev.psi x - h| +
            |Chebyshev.psi (x + h) - Chebyshev.theta (x + h)| +
            |Chebyshev.psi x - Chebyshev.theta x| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ (9 * K₀ + 18) * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (betaStar - 1) := by
          linarith
      _ ≤ K * (Real.sqrt x * Real.log x ^ 2) + K * (h * x ^ (betaStar - 1)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity))
            (mul_le_mul_of_nonneg_right hK_ge2 (by positivity))
      _ = K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (betaStar - 1) := by ring

private theorem log_sq_le_sixtyFour_rpow_quarter {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 64 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h1 : Real.log (x ^ (1 / 8 : ℝ)) ≤ x ^ (1 / 8 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
  rw [Real.log_rpow hx0] at h1
  have hlog_le : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by linarith
  calc Real.log x ^ 2 ≤ (8 * x ^ (1 / 8 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg hx) hlog_le 2
    _ = 64 * (x ^ (1 / 8 : ℝ)) ^ 2 := by ring
    _ = 64 * x ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num

/-- **Cramér-scale short-interval prime theorem under `BacklundConverse.FiniteOffLine`.**
Even when `ζ` has finitely many off-line zeros producing global `Ω_±(x^Θ)` oscillations (`Θ > 1/2`),
there exists `C > 0` such that for all sufficiently large `x`, `(x, x + C √x log² x]` contains a
prime and carries `θ`-mass at least `√x log² x`. -/
theorem finiteOffLine_exists_prime_in_cramer_interval
    (hfin : RHTower.BacklundConverse.FiniteOffLine) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      Real.sqrt x * Real.log x ^ 2 ≤
        Chebyshev.theta (x + C * Real.sqrt x * Real.log x ^ 2) - Chebyshev.theta x ∧
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, betaStar, hK0, _, hβ1, hwin⟩ := finiteOffLine_short_interval_psi_and_theta hfin
  set C : ℝ := 2 * (K + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdecay1 : ∀ᶠ x : ℝ in atTop, K * x ^ (betaStar - 1) ≤ 1 / 2 := by
    have htend : Tendsto (fun x : ℝ => K * x ^ (-(1 - betaStar))) atTop (𝓝 (K * 0)) :=
      tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - betaStar))
    rw [mul_zero] at htend
    filter_upwards [htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx
    rw [show betaStar - 1 = -(1 - betaStar) by ring]
    exact hx.le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdecay1, eventually_ge_atTop (max 16 ((64 * C) ^ 4))] with x hKx hx_top
  have hx16 : 16 ≤ x := (le_max_left _ _).trans hx_top
  have hxC4 : (64 * C) ^ 4 ≤ x := (le_max_right _ _).trans hx_top
  have hx0 : 0 < x := by linarith
  set h : ℝ := C * Real.sqrt x * Real.log x ^ 2
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh_le_x : h ≤ x := by
    have h64_le : 64 * C ≤ x ^ (1 / 4 : ℝ) := by
      have hr := Real.rpow_le_rpow (by positivity) hxC4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show (4 : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at hr
    have hlog_sq := log_sq_le_sixtyFour_rpow_quarter (by linarith : 1 ≤ x)
    dsimp [h]
    calc C * Real.sqrt x * Real.log x ^ 2
        ≤ C * Real.sqrt x * (64 * x ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog_sq (by positivity)
      _ = (64 * C) * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) := by
          rw [Real.sqrt_eq_rpow]; ring
      _ ≤ x ^ (1 / 4 : ℝ) * (x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right h64_le (by positivity)
      _ = x := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
          norm_num
  have hθ := (hwin hx16 hh0 hh_le_x).2
  have hlow := (abs_le.mp hθ).1
  -- `θ(x + h) - θ(x) ≥ h - K √x log² x - K h x^{betaStar - 1} ≥ (C/2 - K) √x log² x = √x log² x`.
  have hKh : K * h * x ^ (betaStar - 1) ≤ (1 / 2) * h := by
    calc K * h * x ^ (betaStar - 1) = (K * x ^ (betaStar - 1)) * h := by ring
      _ ≤ (1 / 2) * h := mul_le_mul_of_nonneg_right hKx hh0
  have hmass_pos : 0 < Real.sqrt x * Real.log x ^ 2 := by
    have hlog2 := RHTower.two_le_log_of_sixteen_le hx16
    positivity
  have hθ_ge : Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.theta (x + h) - Chebyshev.theta x := by
    have hC_half : (1 / 2) * h - K * Real.sqrt x * Real.log x ^ 2 =
        Real.sqrt x * Real.log x ^ 2 := by
      dsimp [h, C]; ring
    linarith
  exact ⟨hθ_ge, exists_prime_Ioc_of_theta_sub_pos hx0.le (hmass_pos.trans_le hθ_ge)⟩

/-- **Cramér-scale short-interval prime theorem under `HasSingleOffLineQuartet ρ₀`.**
Every lone off-line quartet preserves the RH prime-gap law `p_{n+1} - p_n = O(√p_n log² p_n)`. -/
theorem singleQuartet_exists_prime_in_cramer_interval {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      Real.sqrt x * Real.log x ^ 2 ≤
        Chebyshev.theta (x + C * Real.sqrt x * Real.log x ^ 2) - Chebyshev.theta x ∧
      ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x ^ 2 :=
  finiteOffLine_exists_prime_in_cramer_interval hq.finiteOffLine

/-- **World-II contrapositive:** if Cramér-scale short intervals `(x, x + C √x log² x]` fail to
contain primes for every `C > 0`, then `ζ` has **infinitely many** off-line zeros (and in particular
`∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`). -/
theorem infinite_offLine_of_cramer_prime_gap_failure
    (hfail : ∀ C : ℝ, 0 < C → ∃ᶠ x : ℝ in atTop,
      ∀ p : ℕ, p.Prime → ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ x + C * Real.sqrt x * Real.log x ^ 2)) :
    {q : RHTower.XiZeroCopy | (RHTower.xiSpectralPoint q).im ≠ 0}.Infinite ∧
      ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  have hnfin : ¬ RHTower.BacklundConverse.FiniteOffLine := by
    intro hfin
    obtain ⟨C, hC, hev⟩ := finiteOffLine_exists_prime_in_cramer_interval hfin
    exact ((hfail C hC).and_eventually hev).exists.elim fun x ⟨hno, _, p, hp, hpx⟩ =>
      hno p hp hpx
  exact ⟨hnfin, fun _ hq => hnfin hq.finiteOffLine⟩

/-! ## 4. Exact pointwise (`3/2 - Re ρ₀`) and `L²` (`2 - 2 Re ρ₀`) short-interval crossovers -/

/-- Dominant single-quartet explicit-formula wave `W_{ρ₀}(x) = -2 m Re(x^{ρ₀} / ρ₀)`. -/
def singleQuartetMainWave (ρ₀ : ℂ) (x : ℝ) : ℝ :=
  -(2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re)

private theorem cpow_sub_one_re {ρ₀ : ℂ} {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ (ρ₀ - 1)).re = x ^ (ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x) := by
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx_ne, ← Complex.ofReal_log hx.le]
  have hexp : ((Real.log x : ℝ) : ℂ) * (ρ₀ - 1) =
      ((Real.log x * (ρ₀.re - 1) : ℝ) : ℂ) + ((ρ₀.im * Real.log x : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [mul_comm]
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hx,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

private theorem singleQuartetMainWave_increment_approx (ρ₀ : ℂ) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) (hre : ρ₀.re ≤ 2) (hρ : ρ₀ ≠ 0) :
    |(singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) -
        (-(2 * (quartetCopyMult ρ₀ : ℝ) * h * x ^ (ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x)))| ≤
      2 * (quartetCopyMult ρ₀ : ℝ) * ‖ρ₀ - 1‖ * h ^ 2 * x ^ (ρ₀.re - 2) := by
  have hm_nn : 0 ≤ 2 * (quartetCopyMult ρ₀ : ℝ) := by positivity
  have hlin_re : (((h : ℂ) * (x : ℂ) ^ (ρ₀ - 1))).re =
      h * x ^ (ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x) := by
    rw [Complex.re_ofReal_mul, cpow_sub_one_re hx, mul_assoc]
  have hid : (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) -
      (-(2 * (quartetCopyMult ρ₀ : ℝ) * h * x ^ (ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x))) =
      -(2 * (quartetCopyMult ρ₀ : ℝ) *
        (((x + h : ℝ) : ℂ) ^ ρ₀ / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ - (h : ℂ) * (x : ℂ) ^ (ρ₀ - 1)).re) := by
    unfold singleQuartetMainWave
    rw [Complex.sub_re, Complex.sub_re, hlin_re]
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hm_nn]
  have hre_le := (Complex.abs_re_le_norm _).trans (norm_cpow_increment_sub_linear_le hρ hre hx hh)
  calc 2 * (quartetCopyMult ρ₀ : ℝ) *
          |(((x + h : ℝ) : ℂ) ^ ρ₀ / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀ - (h : ℂ) * (x : ℂ) ^ (ρ₀ - 1)).re|
      ≤ 2 * (quartetCopyMult ρ₀ : ℝ) * (‖ρ₀ - 1‖ * h ^ 2 * x ^ (ρ₀.re - 2)) :=
        mul_le_mul_of_nonneg_left hre_le hm_nn
    _ = 2 * (quartetCopyMult ρ₀ : ℝ) * ‖ρ₀ - 1‖ * h ^ 2 * x ^ (ρ₀.re - 2) := by ring

/-- **Subcritical pointwise RH bound (`0 < α ≤ 3/2 - Re ρ₀`).**
Under `HasSingleOffLineQuartet ρ₀`, for every short-interval exponent `0 < α ≤ 3/2 - Re ρ₀`, both
`ψ(x + x^α) - ψ(x) - x^α` and `θ(x + x^α) - θ(x) - x^α` satisfy the RH bound `O(√x log² x)`. -/
theorem singleQuartet_short_interval_subcritical_rh_bound {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {α : ℝ} (_hα0 : 0 < α) (hα : α ≤ 3 / 2 - ρ₀.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 16 ≤ x →
      |Chebyshev.psi (x + x ^ α) - Chebyshev.psi x - x ^ α| ≤
        C * Real.sqrt x * Real.log x ^ 2 ∧
      |Chebyshev.theta (x + x ^ α) - Chebyshev.theta x - x ^ α| ≤
        C * Real.sqrt x * Real.log x ^ 2 := by
  have hα_lt1 : α < 1 := by linarith [hq.1]
  obtain ⟨K, hK0, hwave⟩ := outsideQuartetOnLine_chebyshevPsi_and_theta_wave hq.1 hq.re_lt_one
    ((hasSingleOffLineQuartet_iff_outsideQuartetOnLine ρ₀).mp hq).2.2
  have hρ_ne : ρ₀ ≠ 0 := fun h0 => hq.im_ne_zero (by rw [h0]; simp)
  set C : ℝ := 9 * (K + 2) + 2 * (quartetCopyMult ρ₀ : ℝ)
  refine ⟨C, by dsimp [C]; positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hh0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le α
  have hh_le_x : x ^ α ≤ x := by
    calc x ^ α ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hα_lt1.le
      _ = x := Real.rpow_one x
  have hxh16 : 16 ≤ x + x ^ α := by linarith
  have hscale_xh : Real.sqrt (x + x ^ α) * Real.log (x + x ^ α) ^ 2 ≤
      8 * (Real.sqrt x * Real.log x ^ 2) := by
    have hsqrt : Real.sqrt (x + x ^ α) ≤ 2 * Real.sqrt x := by
      calc Real.sqrt (x + x ^ α) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt 2 * Real.sqrt x := Real.sqrt_mul (by norm_num) x
        _ ≤ 2 * Real.sqrt x := mul_le_mul_of_nonneg_right
            (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]; exact Real.sqrt_le_sqrt (by norm_num))
            (Real.sqrt_nonneg x)
    have hlog_sq : Real.log (x + x ^ α) ^ 2 ≤ 4 * Real.log x ^ 2 := by
      have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
      have hlog_xh : Real.log (x + x ^ α) ≤ 2 * Real.log x := by
        calc Real.log (x + x ^ α) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + Real.log x := Real.log_mul two_ne_zero hx0.ne'
          _ ≤ 2 * Real.log x := by linarith
      have hnn : 0 ≤ Real.log (x + x ^ α) := Real.log_nonneg (by linarith)
      nlinarith
    calc Real.sqrt (x + x ^ α) * Real.log (x + x ^ α) ^ 2
        ≤ (2 * Real.sqrt x) * (4 * Real.log x ^ 2) :=
          mul_le_mul hsqrt hlog_sq (sq_nonneg _) (by positivity)
      _ = 8 * (Real.sqrt x * Real.log x ^ 2) := by ring
  have hW_inc : |singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x| ≤
      2 * (quartetCopyMult ρ₀ : ℝ) * (Real.sqrt x * Real.log x ^ 2) := by
    have hsub : singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x =
        -(2 * (quartetCopyMult ρ₀ : ℝ) *
          (((x + x ^ α : ℝ) : ℂ) ^ ρ₀ / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀).re) := by
      unfold singleQuartetMainWave; rw [Complex.sub_re]; ring
    rw [hsub, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    have hinc := (Complex.abs_re_le_norm _).trans
      (norm_cpow_increment_le hρ_ne hq.re_lt_one.le hx0 hh0)
    have hrpow_le : x ^ α * x ^ (ρ₀.re - 1) ≤ Real.sqrt x * Real.log x ^ 2 := by
      rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
      have h1 : x ^ (α + (ρ₀.re - 1)) ≤ x ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hlog1 : 1 ≤ Real.log x ^ 2 := by
        have := RHTower.two_le_log_of_sixteen_le hx; nlinarith
      calc x ^ (α + (ρ₀.re - 1)) ≤ x ^ (1 / 2 : ℝ) * 1 := by linarith
        _ ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ 2 := mul_le_mul_of_nonneg_left hlog1 (by positivity)
    exact mul_le_mul_of_nonneg_left (hinc.trans hrpow_le) (by positivity)
  have hbound_gen : ∀ {F : ℝ → ℝ},
      (∀ y : ℝ, 16 ≤ y → |F y - y - singleQuartetMainWave ρ₀ y| ≤ (K + 2) * Real.sqrt y * Real.log y ^ 2) →
      |F (x + x ^ α) - F x - x ^ α| ≤ C * Real.sqrt x * Real.log x ^ 2 := by
    intro F hF
    set η : ℝ → ℝ := fun y => F y - y - singleQuartetMainWave ρ₀ y
    have hsplit : F (x + x ^ α) - F x - x ^ α =
        η (x + x ^ α) - η x + (singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x) := by
      dsimp [η]; ring
    have hη_xh : |η (x + x ^ α)| ≤ 8 * (K + 2) * (Real.sqrt x * Real.log x ^ 2) := by
      calc |η (x + x ^ α)| ≤ (K + 2) * (Real.sqrt (x + x ^ α) * Real.log (x + x ^ α) ^ 2) := by
            linarith [hF (x + x ^ α) hxh16]
        _ ≤ (K + 2) * (8 * (Real.sqrt x * Real.log x ^ 2)) :=
            mul_le_mul_of_nonneg_left hscale_xh (by linarith)
        _ = 8 * (K + 2) * (Real.sqrt x * Real.log x ^ 2) := by ring
    have hη_x : |η x| ≤ (K + 2) * (Real.sqrt x * Real.log x ^ 2) := by linarith [hF x hx]
    rw [hsplit]
    calc |η (x + x ^ α) - η x + (singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x)|
        ≤ (|η (x + x ^ α)| + |η x|) +
            |singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ C * (Real.sqrt x * Real.log x ^ 2) := by dsimp [C]; linarith
      _ = C * Real.sqrt x * Real.log x ^ 2 := by ring
  constructor
  · refine hbound_gen fun y hy => ?_
    unfold singleQuartetMainWave; rw [sub_neg_eq_add]
    exact (hwave y hy).1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg y)) (sq_nonneg _))
  · refine hbound_gen fun y hy => ?_
    unfold singleQuartetMainWave; rw [sub_neg_eq_add]
    exact (hwave y hy).2

/-- On `[X, 3X/2]` (`X > 0`, `|γ| > 67`), `γ log x` sweeps more than `2π`, so there exist points in
`[X, 3X/2]` realizing `cos(γ log x) = -1` and `cos(γ log x) = +1`. -/
private theorem exists_cos_extrema_in_three_halves {γ X : ℝ} (hγ : 67 < |γ|) (hX : 0 < X) :
    (∃ xPos ∈ Set.Icc X (3 * X / 2), Real.cos (γ * Real.log xPos) = -1) ∧
      (∃ xNeg ∈ Set.Icc X (3 * X / 2), Real.cos (γ * Real.log xNeg) = 1) := by
  have hlog32' : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
    have hinv : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2) := by
      rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hspan : 2 * Real.pi < |γ| * Real.log (3 / 2) := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have h1 : (67 / 3 : ℝ) < |γ| * (1 / 3) := by linarith
    have h2 : |γ| * (1 / 3) ≤ |γ| * Real.log (3 / 2) :=
      mul_le_mul_of_nonneg_left hlog32' (abs_nonneg γ)
    linarith
  -- Find `k : ℤ` with `|γ| log X ≤ (2k + 1) π ≤ |γ| log(3X/2)` and `m : ℤ` with `|γ| log X ≤ 2m π ≤ |γ| log(3X/2)`.
  set A : ℝ := |γ| * Real.log X
  set B : ℝ := |γ| * Real.log (3 * X / 2)
  have hBA : B - A = |γ| * Real.log (3 / 2) := by
    dsimp [A, B]
    rw [show 3 * X / 2 = (3 / 2) * X by ring, Real.log_mul (by norm_num) hX.ne']
    ring
  have hpi_pos : 0 < 2 * Real.pi := by positivity
  have hex_shift : ∀ θ : ℝ, ∃ x ∈ Set.Icc X (3 * X / 2), |γ| * Real.log x ∈
      Set.range (fun k : ℤ => θ + (k : ℝ) * (2 * Real.pi)) := by
    intro θ
    set k : ℤ := ⌈(A - θ) / (2 * Real.pi)⌉
    have hk_ge : (A - θ) / (2 * Real.pi) ≤ (k : ℝ) := Int.le_ceil _
    have hk_lt : (k : ℝ) < (A - θ) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
    set t : ℝ := θ + (k : ℝ) * (2 * Real.pi)
    have htA : A ≤ t := by
      have := (div_le_iff₀ hpi_pos).mp hk_ge
      dsimp [t]; linarith
    have htB : t ≤ B := by
      have := (lt_div_iff₀ hpi_pos).mp (by linarith : (k : ℝ) - 1 < (A - θ) / (2 * Real.pi))
      dsimp [t]; linarith [hspan, hBA]
    have hγ_pos : 0 < |γ| := by linarith
    set x : ℝ := Real.exp (t / |γ|)
    have hx_lo : X ≤ x := by
      rw [← Real.exp_log hX]
      exact Real.exp_le_exp.mpr ((le_div_iff₀ hγ_pos).mpr (by dsimp [A] at htA; linarith))
    have hx_hi : x ≤ 3 * X / 2 := by
      rw [← Real.exp_log (by positivity : 0 < 3 * X / 2)]
      exact Real.exp_le_exp.mpr ((div_le_iff₀ hγ_pos).mpr (by dsimp [B] at htB; linarith))
    refine ⟨x, ⟨hx_lo, hx_hi⟩, k, ?_⟩
    dsimp [x, t]
    rw [Real.log_exp, mul_div_cancel₀ _ hγ_pos.ne']
  have hcos_abs : ∀ y : ℝ, Real.cos (γ * y) = Real.cos (|γ| * y) := by
    intro y
    rcases abs_choice γ with h | h <;> rw [h]
    simp [neg_mul, Real.cos_neg]
  constructor
  · obtain ⟨xPos, hxPos, k, hk⟩ := hex_shift Real.pi
    refine ⟨xPos, hxPos, ?_⟩
    rw [hcos_abs, ← hk, Real.cos_add_int_mul_two_pi, Real.cos_pi]
  · obtain ⟨xNeg, hxNeg, k, hk⟩ := hex_shift 0
    refine ⟨xNeg, hxNeg, ?_⟩
    rw [hcos_abs, ← hk, zero_add, Real.cos_int_mul_two_pi]

/-- **Supercritical pointwise dyadic sign-change law (`3/2 - Re ρ₀ < α < 1`).**
Above the threshold `3/2 - Re ρ₀ ∈ (1/2, 1)`, on every sufficiently large dyadic interval `[X, 2X]`,
both `ψ(x + x^α) - ψ(x) - x^α` and `θ(x + x^α) - θ(x) - x^α` attain both signs with magnitude at
least `quartetCopyMult ρ₀ · X^{α + Re ρ₀ - 1}` (which strictly dominates `√X log² X`). -/
theorem singleQuartet_short_interval_supercritical_both_signs {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {α : ℝ}
    (hα_lo : 3 / 2 - ρ₀.re < α) (hα_hi : α < 1) :
    1 / 2 < 3 / 2 - ρ₀.re ∧ 3 / 2 - ρ₀.re < 1 ∧
      ∀ᶠ X : ℝ in atTop,
        (∃ xPos ∈ Set.Icc X (2 * X),
          (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) ≤
            Chebyshev.psi (xPos + xPos ^ α) - Chebyshev.psi xPos - xPos ^ α ∧
          (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) ≤
            Chebyshev.theta (xPos + xPos ^ α) - Chebyshev.theta xPos - xPos ^ α) ∧
        (∃ xNeg ∈ Set.Icc X (2 * X),
          Chebyshev.psi (xNeg + xNeg ^ α) - Chebyshev.psi xNeg - xNeg ^ α ≤
            -((quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1)) ∧
          Chebyshev.theta (xNeg + xNeg ^ α) - Chebyshev.theta xNeg - xNeg ^ α ≤
            -((quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1))) := by
  refine ⟨by linarith [hq.re_lt_one], by linarith [hq.1], ?_⟩
  have h67 : 67 < |ρ₀.im| :=
    sixtySeven_lt_abs_im_of_offLine_zeta_zero hq.2.1.1 hq.2.1.2.1 hq.2.1.2.2 (by linarith [hq.1])
  have hρ_ne : ρ₀ ≠ 0 := fun h0 => hq.im_ne_zero (by rw [h0]; simp)
  have hm_pos : (1 : ℝ) ≤ (quartetCopyMult ρ₀ : ℝ) := by exact_mod_cast hq.quartetCopyMult_pos
  obtain ⟨K, hK0, hwave⟩ := outsideQuartetOnLine_chebyshevPsi_and_theta_wave hq.1 hq.re_lt_one
    ((hasSingleOffLineQuartet_iff_outsideQuartetOnLine ρ₀).mp hq).2.2
  -- Gap exponents `δ₁ = (α + Re ρ₀ - 1) - 1/2 > 0` and `δ₂ = 1 - α > 0`.
  set δ₁ : ℝ := α + ρ₀.re - 3 / 2
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; linarith
  have hδ₂ : 0 < 1 - α := by linarith
  -- Use `log y ≤ (4/δ₁) y^{δ₁/4}` to bound `√x log² x / X^{α + Re ρ₀ - 1} → 0` cleanly.
  have herr1 : ∀ᶠ X : ℝ in atTop,
      18 * (K + 2) * (Real.sqrt X * Real.log (2 * X) ^ 2) ≤
        (1 / 2) * (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) := by
    have htend : Tendsto (fun X : ℝ =>
        18 * (K + 2) * (4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * X ^ (-(δ₁ / 2))) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by positivity : 0 < δ₁ / 2))
    filter_upwards [htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_ge_atTop (16 : ℝ)] with X hX_small hX16
    have hX0 : 0 < X := by linarith
    have h2X0 : 0 < 2 * X := by positivity
    have hlog_bound : Real.log (2 * X) ≤ (4 / δ₁) * (2 * X) ^ (δ₁ / 4) := by
      have hsub := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h2X0 (δ₁ / 4))
      rw [Real.log_rpow h2X0] at hsub
      have hdiv := (le_div_iff₀ (by positivity : 0 < δ₁ / 4)).mpr (by linarith : (δ₁ / 4) * Real.log (2 * X) ≤ (2 * X) ^ (δ₁ / 4))
      linarith [show (2 * X) ^ (δ₁ / 4) / (δ₁ / 4) = (4 / δ₁) * (2 * X) ^ (δ₁ / 4) by ring]
    have hlog_sq : Real.log (2 * X) ^ 2 ≤ (4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * X ^ (δ₁ / 2) := by
      calc Real.log (2 * X) ^ 2 ≤ ((4 / δ₁) * (2 * X) ^ (δ₁ / 4)) ^ 2 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_bound 2
        _ = (4 / δ₁) ^ 2 * ((2 * X) ^ (δ₁ / 4)) ^ 2 := by ring
        _ = (4 / δ₁) ^ 2 * (2 * X) ^ (δ₁ / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul h2X0.le]; congr 2; ring
        _ = (4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * X ^ (δ₁ / 2) := by
            rw [Real.mul_rpow (by norm_num) hX0.le]; ring
    have hexp_id : X ^ (1 / 2 : ℝ) * X ^ (δ₁ / 2) = X ^ (-(δ₁ / 2)) * X ^ (α + ρ₀.re - 1) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      congr 1; dsimp [δ₁]; ring
    calc 18 * (K + 2) * (Real.sqrt X * Real.log (2 * X) ^ 2)
        ≤ 18 * (K + 2) * (X ^ (1 / 2 : ℝ) * ((4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * X ^ (δ₁ / 2))) := by
          rw [Real.sqrt_eq_rpow]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog_sq (by positivity)) (by positivity)
      _ = (18 * (K + 2) * (4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * X ^ (-(δ₁ / 2))) * X ^ (α + ρ₀.re - 1) := by
          linear_combination 18 * (K + 2) * (4 / δ₁) ^ 2 * 2 ^ (δ₁ / 2) * hexp_id
      _ ≤ (1 / 2) * 1 * X ^ (α + ρ₀.re - 1) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hX_small.le (by positivity)
      _ ≤ (1 / 2) * (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have herr2 : ∀ᶠ X : ℝ in atTop,
      8 * ‖ρ₀ - 1‖ * X ^ (-(1 - α)) ≤ 1 / 2 := by
    have htend : Tendsto (fun X : ℝ => 8 * ‖ρ₀ - 1‖ * X ^ (-(1 - α))) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_rpow_neg_atTop hδ₂)
    exact (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  filter_upwards [herr1, herr2, eventually_ge_atTop (16 : ℝ)] with X he1 he2 hX16
  have hX0 : 0 < X := by linarith
  obtain ⟨⟨xPos, hxPos, hcosPos⟩, ⟨xNeg, hxNeg, hcosNeg⟩⟩ := exists_cos_extrema_in_three_halves h67 hX0
  have hpoint_err : ∀ {x : ℝ}, x ∈ Set.Icc X (3 * X / 2) →
      ∀ {F : ℝ → ℝ},
        (∀ y : ℝ, 16 ≤ y → |F y - y - singleQuartetMainWave ρ₀ y| ≤
          (K + 2) * Real.sqrt y * Real.log y ^ 2) →
      |(F (x + x ^ α) - F x - x ^ α) -
          (-(2 * (quartetCopyMult ρ₀ : ℝ) * x ^ (α + ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x)))| ≤
        (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) ∧
      X ^ (α + ρ₀.re - 1) ≤ x ^ (α + ρ₀.re - 1) ∧ x ∈ Set.Icc X (2 * X) := by
    intro x hxI F hF
    have hx16 : 16 ≤ x := hX16.trans hxI.1
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hx_le_2X : x ≤ 2 * X := by linarith [hxI.2]
    have hh0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le α
    have hh_le_x : x ^ α ≤ x :=
      (Real.rpow_le_rpow_of_exponent_le hx1 hα_hi.le).trans_eq (Real.rpow_one x)
    have hxh16 : 16 ≤ x + x ^ α := by linarith
    have hxh_le_4X : x + x ^ α ≤ 4 * X := by linarith
    have hlog_4X : Real.log (4 * X) ≤ 2 * Real.log (2 * X) := by
      have hsq : 4 * X ≤ (2 * X) ^ 2 := by nlinarith
      calc Real.log (4 * X) ≤ Real.log ((2 * X) ^ 2) := Real.log_le_log (by positivity) hsq
        _ = 2 * Real.log (2 * X) := by rw [Real.log_pow]; push_cast; rfl
    have hη_sum : |(F (x + x ^ α) - (x + x ^ α) - singleQuartetMainWave ρ₀ (x + x ^ α)) -
        (F x - x - singleQuartetMainWave ρ₀ x)| ≤
        18 * (K + 2) * (Real.sqrt X * Real.log (2 * X) ^ 2) := by
      have h1 := hF (x + x ^ α) hxh16
      have h2 := hF x hx16
      have hs1 : Real.sqrt (x + x ^ α) ≤ 2 * Real.sqrt X := by
        calc Real.sqrt (x + x ^ α) ≤ Real.sqrt (4 * X) := Real.sqrt_le_sqrt hxh_le_4X
          _ = 2 * Real.sqrt X := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
      have hl1 : Real.log (x + x ^ α) ^ 2 ≤ 4 * Real.log (2 * X) ^ 2 := by
        have hle := (Real.log_le_log (by positivity) hxh_le_4X).trans hlog_4X
        have hnn : 0 ≤ Real.log (x + x ^ α) := Real.log_nonneg (by linarith)
        nlinarith
      have hs2 : Real.sqrt x ≤ 2 * Real.sqrt X := by
        calc Real.sqrt x ≤ Real.sqrt (4 * X) := Real.sqrt_le_sqrt (by linarith)
          _ = 2 * Real.sqrt X := by rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
      have hl2 : Real.log x ^ 2 ≤ Real.log (2 * X) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log hx0 hx_le_2X) 2
      have hb1 : Real.sqrt (x + x ^ α) * Real.log (x + x ^ α) ^ 2 ≤
          8 * (Real.sqrt X * Real.log (2 * X) ^ 2) := by
        calc Real.sqrt (x + x ^ α) * Real.log (x + x ^ α) ^ 2
            ≤ (2 * Real.sqrt X) * (4 * Real.log (2 * X) ^ 2) :=
              mul_le_mul hs1 hl1 (sq_nonneg _) (by positivity)
          _ = 8 * (Real.sqrt X * Real.log (2 * X) ^ 2) := by ring
      have hb2 : Real.sqrt x * Real.log x ^ 2 ≤
          2 * (Real.sqrt X * Real.log (2 * X) ^ 2) := by
        calc Real.sqrt x * Real.log x ^ 2
            ≤ (2 * Real.sqrt X) * Real.log (2 * X) ^ 2 :=
              mul_le_mul hs2 hl2 (sq_nonneg _) (by positivity)
          _ = 2 * (Real.sqrt X * Real.log (2 * X) ^ 2) := by ring
      calc _ ≤ |F (x + x ^ α) - (x + x ^ α) - singleQuartetMainWave ρ₀ (x + x ^ α)| +
                |F x - x - singleQuartetMainWave ρ₀ x| := abs_sub _ _
        _ ≤ (K + 2) * (8 * (Real.sqrt X * Real.log (2 * X) ^ 2)) +
              (K + 2) * (2 * (Real.sqrt X * Real.log (2 * X) ^ 2)) :=
            add_le_add ((h1.trans_eq (mul_assoc _ _ _)).trans (mul_le_mul_of_nonneg_left hb1 (by linarith)))
              ((h2.trans_eq (mul_assoc _ _ _)).trans (mul_le_mul_of_nonneg_left hb2 (by linarith)))
        _ ≤ 18 * (K + 2) * (Real.sqrt X * Real.log (2 * X) ^ 2) := by
            nlinarith [Real.sqrt_nonneg X, sq_nonneg (Real.log (2 * X))]
    have hW_rem : |(singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x) -
        (-(2 * (quartetCopyMult ρ₀ : ℝ) * x ^ (α + ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x)))| ≤
        (1 / 2) * (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) := by
      have htaylor := singleQuartetMainWave_increment_approx ρ₀ hx0 hh0 (by linarith [hq.re_lt_one]) hρ_ne
      have hxpow : x ^ α * x ^ (ρ₀.re - 1) = x ^ (α + ρ₀.re - 1) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      have h1 : (x ^ α) ^ 2 ≤ 4 * X ^ (2 * α) := by
        have h2a_nn : 0 ≤ 2 * α := by linarith [hq.re_lt_one]
        have hle2 : 2 ^ (2 * α) ≤ (4 : ℝ) := by
          calc (2 : ℝ) ^ (2 * α) ≤ 2 ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 4 := by norm_num
        calc (x ^ α) ^ 2 = x ^ (2 * α) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; ring
          _ ≤ (2 * X) ^ (2 * α) := Real.rpow_le_rpow hx0.le hx_le_2X h2a_nn
          _ = 2 ^ (2 * α) * X ^ (2 * α) := Real.mul_rpow (by norm_num) hX0.le
          _ ≤ 4 * X ^ (2 * α) := mul_le_mul_of_nonneg_right hle2 (by positivity)
      have h2 : x ^ (ρ₀.re - 2) ≤ X ^ (ρ₀.re - 2) :=
        Real.rpow_le_rpow_of_nonpos hX0 hxI.1 (by linarith [hq.re_lt_one])
      have hexp_split : X ^ (2 * α) * X ^ (ρ₀.re - 2) =
          X ^ (-(1 - α)) * X ^ (α + ρ₀.re - 1) := by
        rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; ring
      have hmul_x : 2 * (quartetCopyMult ρ₀ : ℝ) * (x ^ α) * x ^ (ρ₀.re - 1) =
          2 * (quartetCopyMult ρ₀ : ℝ) * x ^ (α + ρ₀.re - 1) := by
        rw [mul_assoc (2 * _), hxpow]
      rw [hmul_x] at htaylor
      calc _ ≤ 2 * (quartetCopyMult ρ₀ : ℝ) * ‖ρ₀ - 1‖ * ((x ^ α) ^ 2 * x ^ (ρ₀.re - 2)) := by
              linarith [htaylor]
        _ ≤ 2 * (quartetCopyMult ρ₀ : ℝ) * ‖ρ₀ - 1‖ * (4 * X ^ (2 * α) * X ^ (ρ₀.re - 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)
        _ = (quartetCopyMult ρ₀ : ℝ) * (8 * ‖ρ₀ - 1‖ * X ^ (-(1 - α))) * X ^ (α + ρ₀.re - 1) := by
            linear_combination 8 * (quartetCopyMult ρ₀ : ℝ) * ‖ρ₀ - 1‖ * hexp_split
        _ ≤ (quartetCopyMult ρ₀ : ℝ) * (1 / 2) * X ^ (α + ρ₀.re - 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 (by positivity)) (by positivity)
        _ = (1 / 2) * (quartetCopyMult ρ₀ : ℝ) * X ^ (α + ρ₀.re - 1) := by ring
    have hsplit_tot : (F (x + x ^ α) - F x - x ^ α) -
        (-(2 * (quartetCopyMult ρ₀ : ℝ) * x ^ (α + ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x))) =
        ((F (x + x ^ α) - (x + x ^ α) - singleQuartetMainWave ρ₀ (x + x ^ α)) -
          (F x - x - singleQuartetMainWave ρ₀ x)) +
        ((singleQuartetMainWave ρ₀ (x + x ^ α) - singleQuartetMainWave ρ₀ x) -
          (-(2 * (quartetCopyMult ρ₀ : ℝ) * x ^ (α + ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x)))) := by
      ring
    refine ⟨?_, Real.rpow_le_rpow hX0.le hxI.1 (by linarith), ⟨hxI.1, hx_le_2X⟩⟩
    rw [hsplit_tot]
    exact (abs_add_le _ _).trans (by linarith [hη_sum, hW_rem, he1])
  have hF_psi : ∀ y : ℝ, 16 ≤ y →
      |Chebyshev.psi y - y - singleQuartetMainWave ρ₀ y| ≤ (K + 2) * Real.sqrt y * Real.log y ^ 2 := by
    intro y hy
    unfold singleQuartetMainWave; rw [sub_neg_eq_add]
    exact (hwave y hy).1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg y)) (sq_nonneg _))
  have hF_theta : ∀ y : ℝ, 16 ≤ y →
      |Chebyshev.theta y - y - singleQuartetMainWave ρ₀ y| ≤ (K + 2) * Real.sqrt y * Real.log y ^ 2 := by
    intro y hy
    unfold singleQuartetMainWave; rw [sub_neg_eq_add]
    exact (hwave y hy).2
  constructor
  · obtain ⟨hp_err, hpow_ge, hxPos_mem⟩ := hpoint_err hxPos hF_psi
    obtain ⟨ht_err, -, -⟩ := hpoint_err hxPos hF_theta
    rw [hcosPos, mul_neg_one, neg_neg] at hp_err ht_err
    exact ⟨xPos, hxPos_mem, by linarith [(abs_le.mp hp_err).1, mul_le_mul_of_nonneg_left hpow_ge (show (0 : ℝ) ≤ 2 * quartetCopyMult ρ₀ by positivity)],
      by linarith [(abs_le.mp ht_err).1, mul_le_mul_of_nonneg_left hpow_ge (show (0 : ℝ) ≤ 2 * quartetCopyMult ρ₀ by positivity)]⟩
  · obtain ⟨hp_err, hpow_ge, hxNeg_mem⟩ := hpoint_err hxNeg hF_psi
    obtain ⟨ht_err, -, -⟩ := hpoint_err hxNeg hF_theta
    rw [hcosNeg, mul_one] at hp_err ht_err
    exact ⟨xNeg, hxNeg_mem, by linarith [(abs_le.mp hp_err).2, mul_le_mul_of_nonneg_left hpow_ge (show (0 : ℝ) ≤ 2 * quartetCopyMult ρ₀ by positivity)],
      by linarith [(abs_le.mp ht_err).2, mul_le_mul_of_nonneg_left hpow_ge (show (0 : ℝ) ≤ 2 * quartetCopyMult ρ₀ by positivity)]⟩

/-- **`L²` dyadic wave-increment scaling and the `2 - 2 Re ρ₀` variance crossover.**
Under `HasSingleOffLineQuartet ρ₀`, `0 < 2 - 2 Re ρ₀ < 3/2 - Re ρ₀ < 1`, and there exist constants
`c₁, C₂ > 0` and step ratio `η₀ > 0` such that for all `X ≥ 16` and `0 ≤ h ≤ η₀ X`,
`c₁ h² X^{2 Re ρ₀ - 1} ≤ ∫_{X}^{2X} (W_{ρ₀}(x + h) - W_{ρ₀}(x))² dx ≤ C₂ h² X^{2 Re ρ₀ - 1}`. -/
theorem singleQuartet_wave_short_interval_L2_crossover {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    0 < 2 - 2 * ρ₀.re ∧ 2 - 2 * ρ₀.re < 3 / 2 - ρ₀.re ∧ 3 / 2 - ρ₀.re < 1 ∧
      ∃ (c₁ C₂ η₀ : ℝ), 0 < c₁ ∧ 0 < C₂ ∧ 0 < η₀ ∧
        ∀ {X h : ℝ}, 16 ≤ X → 0 ≤ h → h ≤ η₀ * X →
          c₁ * h ^ 2 * X ^ (2 * ρ₀.re - 1) ≤
            ∫ x in X..(2 * X), (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 ∧
          (∫ x in X..(2 * X), (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) ≤
            C₂ * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by
  refine ⟨by linarith [hq.re_lt_one], by linarith [hq.1], by linarith [hq.1], ?_⟩
  have h67 : 67 < |ρ₀.im| :=
    sixtySeven_lt_abs_im_of_offLine_zeta_zero hq.2.1.1 hq.2.1.2.1 hq.2.1.2.2 (by linarith [hq.1])
  have hρ_ne : ρ₀ ≠ 0 := fun h0 => hq.im_ne_zero (by rw [h0]; simp)
  have hm_pos : 0 < (quartetCopyMult ρ₀ : ℝ) := by exact_mod_cast hq.quartetCopyMult_pos
  set m : ℝ := (quartetCopyMult ρ₀ : ℝ)
  set δ : ℝ := min (1 / 4) (1 / (4 * |ρ₀.im|))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  set η₀ : ℝ := 1 / (8 * (1 + ‖ρ₀ - 1‖))
  have hη₀_pos : 0 < η₀ := by dsimp [η₀]; positivity
  set c₁ : ℝ := δ * (m / 4) ^ 2
  set C₂ : ℝ := 4 * m ^ 2
  refine ⟨c₁, C₂, η₀, by dsimp [c₁]; positivity, by dsimp [C₂]; positivity, hη₀_pos,
    fun {X h} hX16 hh0 hh_le => ?_⟩
  have hX0 : 0 < X := by linarith
  -- Continuity of `(W(x+h) - W(x))²` on `[X, 2X]`.
  have hcont_W : ContinuousOn (fun x : ℝ =>
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) (Set.Icc X (2 * X)) := by
    have hcont_cpow : ∀ c : ℝ, 0 ≤ c → ContinuousOn (fun x : ℝ => singleQuartetMainWave ρ₀ (x + c))
        (Set.Icc X (2 * X)) := by
      intro c hc
      unfold singleQuartetMainWave
      refine ContinuousOn.neg (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_))
      refine ContinuousOn.div_const ?_ ρ₀
      refine ContinuousOn.cpow_const ?_ fun x hx => Or.inl (by rw [Complex.ofReal_re]; linarith [hx.1])
      exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_id.add continuousOn_const)
    have h1 := hcont_cpow h hh0
    have h2 : ContinuousOn (singleQuartetMainWave ρ₀) (Set.Icc X (2 * X)) := by
      simpa using hcont_cpow 0 le_rfl
    exact (h1.sub h2).pow 2
  -- Pointwise upper bound `(W(x+h) - W(x))² ≤ 4 m² h² X^{2 Re ρ₀ - 2}` on `[X, 2X]`.
  have hup_pt : ∀ x ∈ Set.Icc X (2 * X),
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 ≤
        4 * m ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hX0 hx.1
    have hinc : |singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x| ≤
        2 * m * h * X ^ (ρ₀.re - 1) := by
      have hsub : singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x =
          -(2 * m * (((x + h : ℝ) : ℂ) ^ ρ₀ / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀).re) := by
        unfold singleQuartetMainWave; rw [Complex.sub_re]; dsimp [m]; ring
      rw [hsub, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
      have h1 := (Complex.abs_re_le_norm _).trans (norm_cpow_increment_le hρ_ne hq.re_lt_one.le hx0 hh0)
      have h2 : x ^ (ρ₀.re - 1) ≤ X ^ (ρ₀.re - 1) :=
        Real.rpow_le_rpow_of_nonpos hX0 hx.1 (by linarith [hq.re_lt_one])
      calc 2 * m * |(((x + h : ℝ) : ℂ) ^ ρ₀ / ρ₀ - (x : ℂ) ^ ρ₀ / ρ₀).re|
          ≤ 2 * m * (h * X ^ (ρ₀.re - 1)) :=
            mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hh0)) (by positivity)
        _ = 2 * m * h * X ^ (ρ₀.re - 1) := by ring
    have hsq := sq_le_sq.mpr (hinc.trans_eq (abs_of_nonneg (by positivity)).symm)
    calc (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2
        ≤ (2 * m * h * X ^ (ρ₀.re - 1)) ^ 2 := hsq
      _ = 4 * m ^ 2 * h ^ 2 * (X ^ (ρ₀.re - 1)) ^ 2 := by ring
      _ = 4 * m ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2) := by
          rw [← Real.rpow_natCast (X ^ (ρ₀.re - 1)) 2, ← Real.rpow_mul hX0.le]
          congr 2; push_cast; ring
  -- Upper bound on `[X, 2X]`.
  have hint_full : IntervalIntegrable
      (fun x : ℝ => (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2)
      volume X (2 * X) :=
    hcont_W.intervalIntegrable_of_Icc (by linarith)
  have hupper : (∫ x in X..(2 * X),
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) ≤
      C₂ * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by
    have hmono := intervalIntegral.integral_mono_on (by linarith : X ≤ 2 * X)
      hint_full intervalIntegrable_const hup_pt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hexp_X : (2 * X - X) * (4 * m ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2)) =
        C₂ * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by
      have hmulX : X * X ^ (2 * ρ₀.re - 2) = X ^ (2 * ρ₀.re - 1) := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0]; congr 1; ring
      dsimp [C₂]
      calc (2 * X - X) * (4 * m ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2))
          = 4 * m ^ 2 * h ^ 2 * (X * X ^ (2 * ρ₀.re - 2)) := by ring
        _ = 4 * m ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by rw [hmulX]
    linarith
  -- Lower bound on the anti-nodal subinterval `[xPos, xPos + δ X] ⊆ [X, 2X]`.
  obtain ⟨⟨xPos, hxPos, hcosPos⟩, -⟩ := exists_cos_extrema_in_three_halves h67 hX0
  have hδ_le_q : δ ≤ 1 / 4 := min_le_left _ _
  have hδ_le_im : δ ≤ 1 / (4 * |ρ₀.im|) := min_le_right _ _
  set b : ℝ := xPos + δ * X
  have hxPos_ge : X ≤ xPos := hxPos.1
  have hb_ge : xPos ≤ b := by dsimp [b]; nlinarith
  have hb_le : b ≤ 2 * X := by dsimp [b]; linarith [hxPos.2]
  -- On `[xPos, b]`, `cos(Im ρ₀ · log x) ≤ -1/2` because `|Im ρ₀ · (log x - log xPos)| ≤ 1/4`.
  have hlow_pt : ∀ x ∈ Set.Icc xPos b,
      (m / 4) ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2) ≤
        (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 := by
    intro x hx_sub
    have hx0 : 0 < x := lt_of_lt_of_le hX0 (hxPos_ge.trans hx_sub.1)
    have hxPos0 : 0 < xPos := lt_of_lt_of_le hX0 hxPos_ge
    have hlog_diff : |ρ₀.im * Real.log x - ρ₀.im * Real.log xPos| ≤ 1 / 4 := by
      rw [← mul_sub, abs_mul, ← Real.log_div hx0.ne' hxPos0.ne']
      have hdiv_ge1 : 1 ≤ x / xPos := (one_le_div hxPos0).mpr hx_sub.1
      have hlog_nn : 0 ≤ Real.log (x / xPos) := Real.log_nonneg hdiv_ge1
      rw [abs_of_nonneg hlog_nn]
      have hlog_le : Real.log (x / xPos) ≤ δ := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hxPos0)
        have h2 : x / xPos - 1 ≤ δ := by
          rw [div_sub_one hxPos0.ne']
          exact (div_le_iff₀ hxPos0).mpr (by dsimp [b] at hx_sub; nlinarith)
        linarith
      calc |ρ₀.im| * Real.log (x / xPos) ≤ |ρ₀.im| * δ :=
            mul_le_mul_of_nonneg_left hlog_le (abs_nonneg _)
        _ ≤ |ρ₀.im| * (1 / (4 * |ρ₀.im|)) :=
            mul_le_mul_of_nonneg_left hδ_le_im (abs_nonneg _)
        _ = 1 / 4 := by field_simp [hq.im_ne_zero]
    -- Using `|cos u - cos v| ≤ |u - v|` (`Real.abs_cos_sub_cos_le`): `cos(γ log x) ≤ -1 + 1/4 = -3/4`.
    have hcos_le : Real.cos (ρ₀.im * Real.log x) ≤ -(3 / 4) := by
      have hlip := Real.abs_cos_sub_cos_le (ρ₀.im * Real.log x) (ρ₀.im * Real.log xPos)
      rw [hcosPos, sub_neg_eq_add] at hlip
      linarith [(abs_le.mp (hlip.trans hlog_diff)).2]
    have htaylor := singleQuartetMainWave_increment_approx ρ₀ hx0 hh0 (by linarith [hq.re_lt_one]) hρ_ne
    -- Main linear term at `x ∈ [xPos, b] ⊆ [X, 2X]`:
    -- `-2 m h x^{Re ρ₀ - 1} cos(...) ≥ (3/2) m h x^{Re ρ₀ - 1}`, while Taylor error is `≤ (1/4) m h x^{Re ρ₀ - 1}`!
    have hrem_le : 2 * m * ‖ρ₀ - 1‖ * h ^ 2 * x ^ (ρ₀.re - 2) ≤
        (1 / 4) * m * h * x ^ (ρ₀.re - 1) := by
      have hh_x : ‖ρ₀ - 1‖ * h ≤ x / 8 := by
        have h1 : (1 + ‖ρ₀ - 1‖) * h ≤ X / 8 := by
          have := mul_le_mul_of_nonneg_left hh_le (by positivity : 0 ≤ 1 + ‖ρ₀ - 1‖)
          dsimp [η₀] at this
          linarith [show (1 + ‖ρ₀ - 1‖) * (1 / (8 * (1 + ‖ρ₀ - 1‖)) * X) = X / 8 by
            field_simp [show (1 : ℝ) + ‖ρ₀ - 1‖ ≠ 0 by positivity]]
        nlinarith [norm_nonneg (ρ₀ - 1), hx_sub.1]
      have hx_split : x ^ (ρ₀.re - 2) * x = x ^ (ρ₀.re - 1) := by
        conv_lhs => rhs; rw [← Real.rpow_one x]
        rw [← Real.rpow_add hx0]; congr 1; ring
      calc 2 * m * ‖ρ₀ - 1‖ * h ^ 2 * x ^ (ρ₀.re - 2)
          = 2 * m * h * (‖ρ₀ - 1‖ * h) * x ^ (ρ₀.re - 2) := by ring
        _ ≤ 2 * m * h * (x / 8) * x ^ (ρ₀.re - 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hh_x (by positivity)) (by positivity)
        _ = (1 / 4) * m * h * (x ^ (ρ₀.re - 2) * x) := by ring
        _ = (1 / 4) * m * h * x ^ (ρ₀.re - 1) := by rw [hx_split]
    have hmain_ge : (3 / 2) * m * h * x ^ (ρ₀.re - 1) ≤
        -(2 * m * h * x ^ (ρ₀.re - 1) * Real.cos (ρ₀.im * Real.log x)) := by
      have hnn_fac : 0 ≤ 2 * m * h * x ^ (ρ₀.re - 1) := by positivity
      nlinarith
    -- Also `x ≤ 2 X` and `ρ₀.re - 1 > -1/2`, so `x^{ρ₀.re - 1} ≥ (2X)^{ρ₀.re - 1} ≥ (1/2) X^{ρ₀.re - 1}`.
    have hx_pow_low : (1 / 2) * X ^ (ρ₀.re - 1) ≤ x ^ (ρ₀.re - 1) := by
      have h2_low : (1 / 2 : ℝ) ≤ 2 ^ (ρ₀.re - 1) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hq.1])
      calc (1 / 2) * X ^ (ρ₀.re - 1)
          ≤ 2 ^ (ρ₀.re - 1) * X ^ (ρ₀.re - 1) :=
            mul_le_mul_of_nonneg_right h2_low (by positivity)
        _ = (2 * X) ^ (ρ₀.re - 1) := (Real.mul_rpow (by norm_num) hX0.le).symm
        _ ≤ x ^ (ρ₀.re - 1) :=
            Real.rpow_le_rpow_of_nonpos hx0 (hx_sub.2.trans hb_le) (by linarith [hq.re_lt_one])
    have hW_ge : (m / 4) * h * X ^ (ρ₀.re - 1) ≤
        singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x := by
      have h1 := (abs_le.mp htaylor).1
      have h2 : (5 / 4) * m * h * x ^ (ρ₀.re - 1) ≤
          singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x := by
        dsimp [m] at hmain_ge hrem_le ⊢
        linarith
      have h3 : (m / 4) * h * X ^ (ρ₀.re - 1) ≤ (5 / 4) * m * h * x ^ (ρ₀.re - 1) := by
        have := mul_le_mul_of_nonneg_left hx_pow_low (show 0 ≤ (5 / 4) * m * h by positivity)
        linarith [show 0 ≤ m * h * X ^ (ρ₀.re - 1) by positivity]
      linarith
    have hsq := pow_le_pow_left₀ (by positivity) hW_ge 2
    calc (m / 4) ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2)
        = ((m / 4) * h * X ^ (ρ₀.re - 1)) ^ 2 := by
            rw [mul_pow, mul_pow, ← Real.rpow_natCast (X ^ (ρ₀.re - 1)) 2, ← Real.rpow_mul hX0.le]
            congr 2; push_cast; ring
      _ ≤ (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 := hsq
  -- Integrate over `[xPos, b] ⊆ [X, 2X]` using nonnegativity of the integrand outside `[xPos, b]`.
  have hint_1 : IntervalIntegrable
      (fun x : ℝ => (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2)
      volume X xPos :=
    (hcont_W.mono (Set.Icc_subset_Icc le_rfl (hb_ge.trans hb_le))).intervalIntegrable_of_Icc hxPos_ge
  have hint_2 : IntervalIntegrable
      (fun x : ℝ => (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2)
      volume xPos b :=
    (hcont_W.mono (Set.Icc_subset_Icc hxPos_ge hb_le)).intervalIntegrable_of_Icc hb_ge
  have hint_3 : IntervalIntegrable
      (fun x : ℝ => (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2)
      volume b (2 * X) :=
    (hcont_W.mono (Set.Icc_subset_Icc (hxPos_ge.trans hb_ge) le_rfl)).intervalIntegrable_of_Icc hb_le
  have hsplit_int : (∫ x in X..(2 * X),
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) =
      (∫ x in X..xPos, (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) +
      (∫ x in xPos..b, (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) +
      (∫ x in b..(2 * X), (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hint_1 hint_2,
      intervalIntegral.integral_add_adjacent_intervals (hint_1.trans hint_2) hint_3]
  have hnn_1 : 0 ≤ ∫ x in X..xPos,
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 :=
    intervalIntegral.integral_nonneg hxPos_ge fun _ _ => sq_nonneg _
  have hnn_3 : 0 ≤ ∫ x in b..(2 * X),
      (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 :=
    intervalIntegral.integral_nonneg hb_le fun _ _ => sq_nonneg _
  have hmid_ge : c₁ * h ^ 2 * X ^ (2 * ρ₀.re - 1) ≤
      ∫ x in xPos..b, (singleQuartetMainWave ρ₀ (x + h) - singleQuartetMainWave ρ₀ x) ^ 2 := by
    have hmono := intervalIntegral.integral_mono_on hb_ge intervalIntegrable_const hint_2 hlow_pt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hlen : b - xPos = δ * X := by dsimp [b]; ring
    have hmulX : X * X ^ (2 * ρ₀.re - 2) = X ^ (2 * ρ₀.re - 1) := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]; congr 1; ring
    have hid : (b - xPos) * ((m / 4) ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2)) =
        c₁ * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by
      rw [hlen]; dsimp [c₁]
      calc δ * X * ((m / 4) ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 2))
          = δ * (m / 4) ^ 2 * h ^ 2 * (X * X ^ (2 * ρ₀.re - 2)) := by ring
        _ = δ * (m / 4) ^ 2 * h ^ 2 * X ^ (2 * ρ₀.re - 1) := by rw [hmulX]
    linarith
  exact ⟨by linarith [hsplit_int], hupper⟩

/-! ## 5. Shifted `ξ`-sum half-plane nonvanishing and vertical-line zero uniqueness -/

/-- **Shifted `ξ`-sum nonvanishing in the `s`-plane under `HasSingleOffLineQuartet ρ₀`.**
For every shift `h ≥ Re ρ₀ - 1/2` and every `s ∈ ℂ` off the shifted symmetry line
(`Re s ≠ 1/2 + h`), `ξ(s) + ξ(s - 2h) ≠ 0`. -/
theorem xi_add_shift_ne_zero_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {h : ℝ} (hh : ρ₀.re - 1 / 2 ≤ h)
    {s : ℂ} (hs : s.re ≠ 1 / 2 + h) :
    RHTower.xi s + RHTower.xi (s - 2 * (h : ℂ)) ≠ 0 := by
  intro hsum
  set z : ℂ := (s - ((1 / 2 : ℂ) + (h : ℂ))) * (-I)
  have hz_im : z.im ≠ 0 := by
    have him : z.im = -(s.re - (1 / 2 + h)) := by
      dsimp [z]
      simp [Complex.mul_im]
    rw [him]
    intro h0; exact hs (by linarith)
  have hs1 : (1 / 2 : ℂ) + (z - (h : ℂ) * I) * I = s := by
    dsimp [z]
    apply Complex.ext <;> simp <;> ring
  have hs2 : (1 / 2 : ℂ) + (z + (h : ℂ) * I) * I = s - 2 * (h : ℂ) := by
    dsimp [z]
    apply Complex.ext <;> simp <;> ring
  have hcos0 : RHTower.cosProducer h z = 0 := by
    unfold RHTower.cosProducer RHTower.XiC
    rw [hs2, hs1, add_comm, hsum, zero_div]
  rcases eq_or_lt_of_le hh with rfl | hgt
  · exact hz_im ((cosProducer_apex_pinning_of_singleQuartet hq).2.2.1 z hcos0)
  · exact hz_im (cosProducer_real_and_simple_of_singleQuartet_gt hq hgt hcos0).1

/-- **Vertical-line zero uniqueness under `HasSingleOffLineQuartet ρ₀`.**
Along the vertical line `Re s = Re ρ₀`, `ζ(Re ρ₀ + i t) = 0` holds if and only if `|t| = |Im ρ₀|`. -/
theorem riemannZeta_re_eq_zero_iff_abs_im_eq_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (t : ℝ) :
    riemannZeta ((ρ₀.re : ℂ) + (t : ℂ) * I) = 0 ↔ |t| = |ρ₀.im| := by
  set s : ℂ := (ρ₀.re : ℂ) + (t : ℂ) * I
  have hs_re : s.re = ρ₀.re := by simp [s]
  have hs_im : s.im = t := by simp [s]
  constructor
  · intro hζ
    have hcar : s ∈ Zeta23.zetaZeroConfig.carrier :=
      ⟨hζ, by rw [hs_re]; linarith [hq.1], by rw [hs_re]; exact hq.re_lt_one⟩
    have hmem : s ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]
      exact ⟨hcar, by rw [hs_re]; exact ne_of_gt hq.1⟩
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with heq | heq | heq | heq
    · rw [← hs_im, heq]
    · rw [← hs_im, heq, Complex.conj_im, abs_neg]
    · exfalso; have := congrArg Complex.re heq; simp [hs_re] at this; linarith [hq.1]
    · exfalso; have := congrArg Complex.re heq; simp [hs_re] at this; linarith [hq.1]
  · intro habs
    rcases abs_eq_abs.mp habs with rfl | rfl
    · have hs_eq : s = ρ₀ := by apply Complex.ext <;> simp [s]
      rw [hs_eq]
      exact hq.2.1.1
    · have hs_eq : s = conj ρ₀ := by apply Complex.ext <;> simp [s]
      rw [hs_eq, riemannZeta_conj, hq.2.1.1, map_zero]

end GaloisForLFunctions.ExceptionalLayerTheory

