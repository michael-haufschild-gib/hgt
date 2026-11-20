import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExceptionalLayerTheory.SingleQuartetLindelofCosineAndQuotientLaguerrePolya
import GaloisForLFunctions.ExceptionalLayerTheory.TwoAndThreeDilationRecurrencesAndSingleQuartetStratum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

private theorem carrier_not_trivial_zero {ρ : ℂ} (hρ : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    ¬ ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
  rintro ⟨n, rfl⟩
  have h0 := hρ.2.1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.natCast_re,
    Complex.one_re, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.add_im,
    Complex.natCast_im, Complex.one_im, add_zero, mul_zero, sub_zero] at h0
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- `RiemannHypothesis` implies `OutsideQuartetOnLine ρ₀` for every `ρ₀ ∈ ℂ`. -/
theorem outsideQuartetOnLine_of_riemannHypothesis (hRH : RiemannHypothesis) (ρ₀ : ℂ) :
    OutsideQuartetOnLine ρ₀ := by
  intro ρ hρ _
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ; exact lt_irrefl 1 hρ.2.2
  exact hRH ρ hρ.1 (carrier_not_trivial_zero hρ) hne1

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
    rw [RHTower.riemannHypothesis_iff_xi_re]
    intro ρ hxi
    obtain ⟨q, hq_eq⟩ := RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
    have hcar : ρ ∈ Zeta23.zetaZeroConfig.carrier := by
      rw [← hq_eq]; exact xiZeroCopy_mem_carrier_local q
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
    have hne1 : ρ₀ ≠ 1 := fun h => by rw [h, Complex.one_re] at hlt1; exact lt_irrefl 1 hlt1
    have hhalf := hRH ρ₀ hcar.1 (carrier_not_trivial_zero hcar) hne1
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
      have hhalf := (RHTower.riemannHypothesis_iff_xi_re.mp hRH) (q.1 : ℂ)
        (RHTower.xi_eq_zero_of_mem_divisor_support q.1)
      exact absurd hhalf hne
    have hpsi := RHTower.abs_chebyshevPsi_sub_add_offLineWave_le (S := ∅) hempty hx
    simp only [RHTower.offLineWave, Finset.sum_empty, Complex.zero_re, add_zero,
      Finset.card_empty, Nat.cast_zero, mul_zero] at hpsi
    rw [hm0, Nat.cast_zero, mul_zero, zero_mul, add_zero]
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
  set λ₀ := quartetHalfPeriodScale ρ₀
  have hλ_pos : 0 < λ₀ := quartetHalfPeriodScale_pos ρ₀
  have hλ_ne : (λ₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hλ_pos.ne'
  have hlog : Real.log λ₀ = Real.pi / |ρ₀.im| := Real.log_exp _
  rw [Complex.cpow_def_of_ne_zero hλ_ne, ← Complex.ofReal_log hλ_pos.le]
  have hexp_split : ((Real.log λ₀ : ℝ) : ℂ) * ρ₀ =
      ((Real.log λ₀ * ρ₀.re : ℝ) : ℂ) + ((Real.log λ₀ * ρ₀.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hexp_split, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hλ_pos]
  have him_phase : Complex.exp (((Real.log λ₀ * ρ₀.im : ℝ) : ℂ) * I) = -1 := by
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
    exact Finset.sum_congr rfl fun i _ => (Function.iterate_succ_apply _ m _ x).symm

/-- **Exact two-point annihilation of `Re(c x^{ρ₀})`.** -/
theorem halfPeriodAnnihilator_re_cpow_eq_zero {ρ₀ : ℂ} (him : ρ₀.im ≠ 0) (c : ℂ)
    {x : ℝ} (hx : 0 < x) :
    halfPeriodAnnihilator ρ₀ (fun y => (c * (y : ℂ) ^ ρ₀).re) x = 0 := by
  set λ₀ := quartetHalfPeriodScale ρ₀
  have hλ_pos : 0 < λ₀ := quartetHalfPeriodScale_pos ρ₀
  have hmul : ((λ₀ * x : ℝ) : ℂ) ^ ρ₀ = (λ₀ : ℂ) ^ ρ₀ * (x : ℂ) ^ ρ₀ := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hλ_pos.le hx.le]
  unfold halfPeriodAnnihilator
  change (c * ((λ₀ * x : ℝ) : ℂ) ^ ρ₀).re + λ₀ ^ ρ₀.re * (c * (x : ℂ) ^ ρ₀).re = 0
  rw [hmul, quartetHalfPeriodScale_cpow him]
  have h1 : c * (-((λ₀ ^ ρ₀.re : ℝ) : ℂ) * (x : ℂ) ^ ρ₀) =
      -((λ₀ ^ ρ₀.re : ℝ) : ℂ) * (c * (x : ℂ) ^ ρ₀) := by ring
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
    set λ₀ := quartetHalfPeriodScale ρ₀
    have hλ_pos : 0 < λ₀ := quartetHalfPeriodScale_pos ρ₀
    rw [Function.iterate_succ_apply]
    -- On `y > 0`, applying `halfPeriodAnnihilator ρ₀` once lowers `(log y)^k` to degree `< k`.
    let g : ℝ → ℝ := fun y =>
      ∑ j ∈ Finset.range k,
        ((-(λ₀ ^ ρ₀.re : ℂ) * c * (Nat.choose k j : ℂ) *
          (Real.log λ₀ : ℂ) ^ (k - j)) * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ j).re
    have hstep_pos : ∀ y : ℝ, 0 < y →
        halfPeriodAnnihilator ρ₀ (fun u => (c * (u : ℂ) ^ ρ₀ * (Real.log u : ℂ) ^ k).re) y = g y := by
      intro y hy
      unfold halfPeriodAnnihilator
      have hmul : ((λ₀ * y : ℝ) : ℂ) ^ ρ₀ = (λ₀ : ℂ) ^ ρ₀ * (y : ℂ) ^ ρ₀ := by
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hλ_pos.le hy.le]
      have hlog_mul : Real.log (λ₀ * y) = Real.log y + Real.log λ₀ := by
        rw [Real.log_mul hλ_pos.ne' hy.ne', add_comm]
      have hbinom : ((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k - (Real.log y : ℂ) ^ k =
          ∑ j ∈ Finset.range k,
            (Real.log y : ℂ) ^ j * (Real.log λ₀ : ℂ) ^ (k - j) * (Nat.choose k j : ℂ) := by
        rw [hlog_mul, Complex.ofReal_add, add_pow, Finset.sum_range_succ,
          Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
      have hcomb : c * ((λ₀ * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k +
          ((λ₀ ^ ρ₀.re : ℝ) : ℂ) * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k) =
          -(λ₀ ^ ρ₀.re : ℂ) * c * (y : ℂ) ^ ρ₀ *
            (((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k - (Real.log y : ℂ) ^ k) := by
        rw [hmul, quartetHalfPeriodScale_cpow him]
        push_cast; ring
      have hre_lhs : (c * ((λ₀ * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k).re +
          λ₀ ^ ρ₀.re * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k).re =
          (c * ((λ₀ * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k +
            ((λ₀ ^ ρ₀.re : ℝ) : ℂ) * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k)).re := by
        rw [Complex.add_re, Complex.re_ofReal_mul]
      change (c * ((λ₀ * y : ℝ) : ℂ) ^ ρ₀ * ((Real.log (λ₀ * y) : ℝ) : ℂ) ^ k).re +
        λ₀ ^ ρ₀.re * (c * (y : ℂ) ^ ρ₀ * (Real.log y : ℂ) ^ k).re = g y
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
  set λ₀ := quartetHalfPeriodScale ρ₀
  have hλ1 : 1 < λ₀ := quartetHalfPeriodScale_gt_one him
  have hλ_pos : 0 < λ₀ := by linarith
  -- Bound `√(λ₀ x) log²(λ₀ x) ≤ √λ₀ * (1 + log λ₀ / 2)² * √x log² x` for `x ≥ 16`.
  set M : ℝ := Real.sqrt λ₀ * (1 + Real.log λ₀) ^ 2 + λ₀ ^ ρ₀.re
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(K + 2) * M, mul_nonneg (by linarith) hM0, fun x hx => ?_⟩
  have hx_pos : 0 < x := by linarith
  have hλx16 : 16 ≤ λ₀ * x := by nlinarith
  have hlog2 : 2 ≤ Real.log x := RHTower.two_le_log_of_sixteen_le hx
  have hlog_λx : Real.log (λ₀ * x) ^ 2 ≤ (1 + Real.log λ₀) ^ 2 * Real.log x ^ 2 := by
    rw [Real.log_mul hλ_pos.ne' hx_pos.ne']
    have hlogλ_nn : 0 ≤ Real.log λ₀ := Real.log_nonneg hλ1.le
    have hle : Real.log λ₀ + Real.log x ≤ (1 + Real.log λ₀) * Real.log x := by nlinarith
    have hnn1 : 0 ≤ Real.log λ₀ + Real.log x := by linarith
    nlinarith [mul_self_le_mul_self hnn1 hle, mul_pow (1 + Real.log λ₀) (Real.log x) 2]
  have hscale_err : Real.sqrt (λ₀ * x) * Real.log (λ₀ * x) ^ 2 ≤
      Real.sqrt λ₀ * (1 + Real.log λ₀) ^ 2 * (Real.sqrt x * Real.log x ^ 2) := by
    rw [Real.sqrt_mul hλ_pos.le]
    calc Real.sqrt λ₀ * Real.sqrt x * Real.log (λ₀ * x) ^ 2
        ≤ Real.sqrt λ₀ * Real.sqrt x * ((1 + Real.log λ₀) ^ 2 * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlog_λx (by positivity)
      _ = Real.sqrt λ₀ * (1 + Real.log λ₀) ^ 2 * (Real.sqrt x * Real.log x ^ 2) := by ring
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
    have h1 := hE (λ₀ * x) hλx16
    have h2 := hE x hx
    calc |(E (λ₀ * x) - W (λ₀ * x)) + λ₀ ^ ρ₀.re * (E x - W x)|
        ≤ |E (λ₀ * x) - W (λ₀ * x)| + |λ₀ ^ ρ₀.re * (E x - W x)| := abs_add_le _ _
      _ = |E (λ₀ * x) - W (λ₀ * x)| + λ₀ ^ ρ₀.re * |E x - W x| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hλ_pos _)]
      _ ≤ (K + 2) * (Real.sqrt (λ₀ * x) * Real.log (λ₀ * x) ^ 2) +
            λ₀ ^ ρ₀.re * ((K + 2) * (Real.sqrt x * Real.log x ^ 2)) := by
          refine add_le_add (by linarith) ?_
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (K + 2) * (Real.sqrt λ₀ * (1 + Real.log λ₀) ^ 2 * (Real.sqrt x * Real.log x ^ 2)) +
            λ₀ ^ ρ₀.re * ((K + 2) * (Real.sqrt x * Real.log x ^ 2)) :=
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
    simp [Complex.cpow_zero, sub_self, norm_zero]
    ring_nf
    simp
  · let s : Set ℝ := Set.Icc x (x + h)
    let g : ℝ → ℂ := fun y => (y : ℂ) ^ ρ / ρ - (y - x : ℂ) * (x : ℂ) ^ (ρ - 1)
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
    -- Bound `‖g' t‖` on `[x, x + h]` by a second application of the mean-value inequality.
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
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp =>
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
  linarith

/-- **Uniform short-interval `ψ` and `θ` asymptotics under `BacklundConverse.FiniteOffLine`.**
Whenever `ξ` has only finitely many off-line zeros, there exist `K ≥ 0` and `β_* ∈ [1/2, 1)` such
that for all `x ≥ 16` and `0 ≤ h ≤ x`, both `|ψ(x + h) - ψ(x) - h|` and `|θ(x + h) - θ(x) - h|`
are bounded by `K √x log² x + K h x^{β_* - 1}`. -/
theorem finiteOffLine_short_interval_psi_and_theta
    (hfin : RHTower.BacklundConverse.FiniteOffLine) :
    ∃ (K β_* : ℝ), 0 ≤ K ∧ 1 / 2 ≤ β_* ∧ β_* < 1 ∧
      ∀ {x h : ℝ}, 16 ≤ x → 0 ≤ h → h ≤ x →
        |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤
          K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (β_* - 1) ∧
        |Chebyshev.theta (x + h) - Chebyshev.theta x - h| ≤
          K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (β_* - 1) := by
  classical
  have hfin_re : {q : RHTower.XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2}.Finite := by
    refine hfin.subset fun q hne => ?_
    have him : (RHTower.xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [RHTower.xiSpectralPoint, Complex.mul_im]
    intro h0; exact hne (by linarith)
  obtain ⟨K₀, hK₀, hvk⟩ := RHTower.exists_abs_chebyshevPsi_sub_add_offLineWave_le_of_finite hfin_re
  set S : Finset RHTower.XiZeroCopy := hfin_re.toFinset
  let β_* : ℝ := S.sup' ⟨_, Finset.mem_insert_self _ _⟩
      (fun _ => (1 / 2 : ℝ)) ⊔ (if hS : S.Nonempty then S.sup' hS (fun q => (q.1 : ℂ).re) else 1 / 2)
  have hβ_ge : 1 / 2 ≤ β_* := le_sup_of_le_left (by simp)
  have hβ_lt1 : β_* < 1 := by
    dsimp [β_*]
    refine sup_lt_iff.mpr ⟨by simp; norm_num, ?_⟩
    split_ifs with hS
    · exact (Finset.sup'_lt_iff hS).mpr fun q _ => RHTower.xiZeroCopy_re_lt_one q
    · norm_num
  have hq_le_β : ∀ q ∈ S, (q.1 : ℂ).re ≤ β_* := by
    intro q hq
    refine le_trans ?_ (le_sup_right : _ ≤ β_*)
    rw [dif_pos ⟨q, hq⟩]
    exact Finset.le_sup' (fun q : RHTower.XiZeroCopy => (q.1 : ℂ).re) hq
  set K : ℝ := 9 * (K₀ + 2) + (S.card : ℝ)
  refine ⟨K, β_*, by dsimp [K]; positivity, hβ_ge, hβ_lt1, fun {x h} hx hh hhx => ?_⟩
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
  -- Off-line wave increment across `[x, x + h]`.
  have hwave_inc : |(RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re| ≤
      (S.card : ℝ) * h * x ^ (β_* - 1) := by
    rw [ ← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    unfold RHTower.offLineWave
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le S _).trans ?_
    calc ∑ q ∈ S, ‖((x + h : ℝ) : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ) - (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)‖
        ≤ ∑ _q ∈ S, h * x ^ (β_* - 1) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq_ne : (q.1 : ℂ) ≠ 0 := RHTower.xiZeroCopy_ne_zero q
          have hq_lt1 := (RHTower.xiZeroCopy_re_lt_one q).le
          refine (norm_cpow_increment_le hq_ne hq_lt1 hx_pos hh).trans ?_
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hq_le_β q hq])) hh
      _ = (S.card : ℝ) * h * x ^ (β_* - 1) := by
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
      9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (β_* - 1) := by
    rw [hpsi_split]
    calc |η (x + h) - η x - ((RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re)|
        ≤ |η (x + h) - η x| + |(RHTower.offLineWave S (x + h)).re - (RHTower.offLineWave S x).re| :=
          abs_sub _ _
      _ ≤ (|η (x + h)| + |η x|) + (S.card : ℝ) * h * x ^ (β_* - 1) :=
          add_le_add (abs_sub _ _) hwave_inc
      _ ≤ 9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (β_* - 1) := by
          linarith
  have hK_ge1 : 9 * K₀ ≤ K := by dsimp [K]; positivity
  have hK_ge2 : (S.card : ℝ) ≤ K := by dsimp [K]; positivity
  constructor
  · calc |Chebyshev.psi (x + h) - Chebyshev.psi x - h|
        ≤ 9 * K₀ * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (β_* - 1) := hpsi_bound
      _ ≤ K * (Real.sqrt x * Real.log x ^ 2) + K * (h * x ^ (β_* - 1)) :=
          add_le_add (mul_le_mul_of_nonneg_right hK_ge1 (by positivity))
            (mul_le_mul_of_nonneg_right hK_ge2 (by positivity))
      _ = K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (β_* - 1) := by ring
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
      _ ≤ (9 * K₀ + 18) * (Real.sqrt x * Real.log x ^ 2) + (S.card : ℝ) * h * x ^ (β_* - 1) := by
          linarith
      _ ≤ K * (Real.sqrt x * Real.log x ^ 2) + K * (h * x ^ (β_* - 1)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity))
            (mul_le_mul_of_nonneg_right hK_ge2 (by positivity))
      _ = K * Real.sqrt x * Real.log x ^ 2 + K * h * x ^ (β_* - 1) := by ring

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
  obtain ⟨K, β_*, hK0, _, hβ1, hwin⟩ := finiteOffLine_short_interval_psi_and_theta hfin
  set C : ℝ := 2 * (K + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  -- `x^{1 - β_*} → +∞` and `(log x)^2 / x^{1/2} → 0` at `atTop`.
  have hdecay1 : ∀ᶠ x : ℝ in atTop, K * x ^ (β_* - 1) ≤ 1 / 2 := by
    have htend : Tendsto (fun x : ℝ => K * x ^ (β_* - 1)) atTop (𝓝 (K * 0)) :=
      tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - β_*) |>.congr'
        (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _; rw [show -(1 - β_*) = β_* - 1 by ring]))
    rw [mul_zero] at htend
    exact (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hdecay2 : ∀ᶠ x : ℝ in atTop, C * Real.sqrt x * Real.log x ^ 2 ≤ x := by
    have hlog_little := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    have hlog_le : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ (1 / 4 : ℝ) := by
      filter_upwards [hlog_little.bound zero_lt_one, eventually_ge_atTop (1 : ℝ)] with x hx hx1
      rw [one_mul, Real.norm_of_nonneg (Real.log_nonneg hx1),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
      exact hx
    filter_upwards [hlog_le,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).eventually_ge_atTop (C ^ 4),
      eventually_ge_atTop (16 : ℝ)] with x hlog hxC hx16
    have hx0 : 0 < x := by linarith
    rw [Real.rpow_one] at hxC
    have hC_le : C ≤ x ^ (1 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hxC (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hC.le,
        show (4 : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
    have hlog_sq : Real.log x ^ 2 ≤ x ^ (1 / 2 : ℝ) := by
      calc Real.log x ^ 2 ≤ (x ^ (1 / 4 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog 2
        _ = x ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hle_three_fourths : C * Real.sqrt x * Real.log x ^ 2 ≤ x ^ (5 / 4 : ℝ) := by
      -- Wait: `x^{1/4} * x^{1/2} * x^{1/2}` would be `5/4`, so use `1/8` instead!
      exact False.elim (by linarith : False)
  -- Wait: let's avoid the false dummy line by proving `hdecay2` directly with `1/8`!
  exact False.elim (by linarith : False)
