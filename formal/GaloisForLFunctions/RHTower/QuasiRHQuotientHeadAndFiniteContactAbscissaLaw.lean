import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusQuotientPowerCutoff
import GaloisForLFunctions.RHTower.MobiusDivisorLowerStripPowerGapBootstrap
import GaloisForLFunctions.RHTower.SuzukiCompletedFormationEnergy
import GaloisForLFunctions.RHTower.SuzukiQuadraticContactUnconditionalDecay

/-!
# Quasi-RH Abscissa Laws: Any-Cutoff Quotient Heads, Finite-Contact Suzuki Residuals, and Formation Energy

This module connects four previously separate sectors of the `RHTower` corpus to establish
unconditional strip and exact exponent laws for the Riemann zero abscissa `zetaZeroAbscissa`:

1. **Global `zetaZeroAbscissa` ↔ `XiZeroHalfPlaneBound` ↔ `XiZeroCopy` Equivalence:**
   Using `ZetaXiZeroCorrespondence` and `ZetaZeroAbscissa`, `zetaZeroAbscissa - 1/2` is
   unconditionally a `XiZeroHalfPlaneBound`, and for `0 ≤ α` we have
   `XiZeroHalfPlaneBound α ↔ zetaZeroAbscissa ≤ 1/2 + α`.

2. **Unconditional Generalized von Koch and One-Sided / Power-Gap Exponent Laws at `zetaZeroAbscissa`:**
   Connecting `CCMGeneralizedVonKoch`, `CCMFUSuzukiMobiusDivisorAbelProducer`,
   `MobiusDivisorOneSidedPowerGapBootstrap`, and `MobiusDivisorLowerStripPowerGapBootstrap`
   yields unconditional `O(M^{zetaZeroAbscissa - 1/2 + ε})` bounds and exact one-sided `sInf`
   exponent formulas for `coherentSelbergSquareRootAbelMoment` and
   `mobiusDivisorSquareRootAbelMoment`.

3. **Self-Contracting Any-Cutoff Quotient-Head Exponent Law (`quasi-rh.md` §8.2–8.3):**
   Combining `mobiusDivisorQuotientPowerHead_error_subpower` with the one-sided strip laws shows
   that for **every** fixed power cutoff `θ > 0` (arbitrarily small, with no baseline `b₀ = 7/8`
   or two-sided norm required), a one-sided bound of exponent `c ≥ 0` on
   `mobiusDivisorQuotientHead M ⌈M^θ⌉₊ / M` self-contracts `(1 - θ)(zetaZeroAbscissa - 1/2)` and
   forces `zetaZeroAbscissa ≤ 1/2 + c`.

4. **Polynomial-Growth Finite-Contact Suzuki Residual and Formation-Energy Laws (`quasi-rh.md` §2.3, §8.1, §8.4):**
   Generalizes `SuzukiTransitionCoreFiniteContactWidthClassification` from boundedness (`r = 0`)
   to arbitrary polynomial growth `P_m(N) ≤ B N^r`, proves the converse unconditional upper bound
   of exponent `2m(zetaZeroAbscissa - 1/2) - (m - 1) + ε`, derives the exact `sInf` exponent law
   and sub-frontier power decay `P_m(N) → 0` for all `m ≥ 1`, and proves the corresponding exact
   exponent laws for `suzukiCompletedFormationEnergy`.
-/

open Complex Real Set Filter Topology Finset
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: Exact Bridge Between `zetaZeroAbscissa`, `XiZeroHalfPlaneBound`, and `XiZeroCopy` -/

/-- Every zero of `xi` lies at or to the left of `zetaZeroAbscissa`. -/
theorem xi_zero_re_le_zetaZeroAbscissa {ρ : ℂ} (hρ : xi ρ = 0) :
    ρ.re ≤ zetaZeroAbscissa :=
  re_le_zetaZeroAbscissa (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ).1

/-- The intrinsic half-plane width `zetaZeroAbscissa - 1/2` is unconditionally a `XiZeroHalfPlaneBound`. -/
theorem xiZeroHalfPlaneBound_zetaZeroAbscissa_sub_half :
    XiZeroHalfPlaneBound (zetaZeroAbscissa - 1 / 2) := by
  intro ρ hρ
  linarith [xi_zero_re_le_zetaZeroAbscissa hρ]

/-- Conversely, any `XiZeroHalfPlaneBound α` with `0 ≤ α` bounds `zetaZeroAbscissa` by `1/2 + α`. -/
theorem zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound {α : ℝ} (hα : 0 ≤ α)
    (hXi : XiZeroHalfPlaneBound α) : zetaZeroAbscissa ≤ 1 / 2 + α := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ρ, hzero, hre1, hre⟩ := exists_zetaZero_mem_openStrip_lt_re hlt
  have hxi : xi ρ = 0 := by
    refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hzero, fun n hn => ?_⟩
    have hre_neg : ρ.re = -(2 * ((n : ℝ) + 1)) := by
      rw [hn]
      simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  linarith [hXi ρ hxi]

/-- Exact equivalence between `XiZeroHalfPlaneBound α` and `zetaZeroAbscissa ≤ 1/2 + α` for `0 ≤ α`. -/
theorem xiZeroHalfPlaneBound_iff_zetaZeroAbscissa_le {α : ℝ} (hα : 0 ≤ α) :
    XiZeroHalfPlaneBound α ↔ zetaZeroAbscissa ≤ 1 / 2 + α := by
  constructor
  · exact zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound hα
  · intro hle ρ hρ
    linarith [xi_zero_re_le_zetaZeroAbscissa hρ]

/-- Any strip bound `|(q.1 : ℂ).re - 1/2| ≤ α` on `XiZeroCopy` (`0 ≤ α`) forces `zetaZeroAbscissa ≤ 1/2 + α`. -/
theorem zetaZeroAbscissa_le_of_forall_xiZeroCopy_abs_re_sub_half_le {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) :
    zetaZeroAbscissa ≤ 1 / 2 + α := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound hα fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  linarith [(abs_le.mp (h q)).2]

/-- Every `q : XiZeroCopy` lies in the strip `|(q.1 : ℂ).re - 1/2| ≤ zetaZeroAbscissa - 1/2`. -/
theorem xiZeroCopy_abs_re_sub_half_le_zetaZeroAbscissa (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ zetaZeroAbscissa - 1 / 2 :=
  abs_re_sub_half_le_of_xiZeroHalfPlaneBound xiZeroHalfPlaneBound_zetaZeroAbscissa_sub_half q

/-- `zetaZeroAbscissa = 1/2` is equivalent to `RiemannHypothesis`. -/
theorem zetaZeroAbscissa_eq_half_iff_riemannHypothesis :
    zetaZeroAbscissa = 1 / 2 ↔ RiemannHypothesis := by
  rw [← xiZeroHalfPlaneBound_zero_iff_rh, xiZeroHalfPlaneBound_iff_zetaZeroAbscissa_le le_rfl,
    add_zero]
  exact ⟨le_of_eq, fun h => le_antisymm h half_le_zetaZeroAbscissa⟩

/-! ## Section 2: Unconditional Generalized von Koch and One-Sided / Power-Gap Exponent Laws for
`coherentSelbergSquareRootAbelMoment` and `mobiusDivisorSquareRootAbelMoment` at `zetaZeroAbscissa` -/

/-- Unconditional Chebyshev error power spectrum at the true zero abscissa `zetaZeroAbscissa`. -/
theorem chebyshevErrorPowerSpectrum_zetaZeroAbscissa_sub_half :
    ChebyshevErrorPowerSpectrum (zetaZeroAbscissa - 1 / 2) :=
  chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound
    (sub_nonneg.mpr half_le_zetaZeroAbscissa) xiZeroHalfPlaneBound_zetaZeroAbscissa_sub_half

/-- Unconditional subpower bound on `psiRemainder` at `zetaZeroAbscissa`. -/
theorem exists_psiRemainder_le_rpow_zetaZeroAbscissa (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |psiRemainder N| ≤ C * (N : ℝ) ^ (zetaZeroAbscissa + ε) := by
  have hα0 : 0 ≤ zetaZeroAbscissa - 1 / 2 := sub_nonneg.mpr half_le_zetaZeroAbscissa
  rcases lt_or_ge (zetaZeroAbscissa - 1 / 2) (1 / 2) with hlt | hge
  · obtain ⟨C, hC0, hC⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
      hα0 hlt xiZeroHalfPlaneBound_zetaZeroAbscissa_sub_half hε
    refine ⟨C, hC0.le, fun N hN => ?_⟩
    rw [psiRemainder, chebyshevPsi_eq_psi, psi_natCast_eq_sum_Icc_one]
    have hexp : 1 / 2 + (zetaZeroAbscissa - 1 / 2) + ε = zetaZeroAbscissa + ε := by ring
    simpa only [hexp] using hC N hN
  · refine ⟨6, by norm_num, fun N hN => ?_⟩
    rw [psiRemainder, chebyshevPsi_eq_psi]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have habs : |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    have hpow : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ (zetaZeroAbscissa + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_one] at hpow
    exact habs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- Unconditional subpower bound on `coherentSelbergSquareRootAbelMoment` at `zetaZeroAbscissa`. -/
theorem exists_coherentSelbergSquareRootAbelMoment_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |coherentSelbergSquareRootAbelMoment M / M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  refine ⟨C, hC0, fun M hM => ?_⟩
  have hM0 : (0 : ℝ) < M := by positivity
  have hM1 : 1 ≤ M := by omega
  have hΘ0 : 0 ≤ zetaZeroAbscissa + ε := by linarith [half_le_zetaZeroAbscissa]
  have hw : ∀ k : ℕ, 0 ≤ Real.sqrt (k + 1 : ℕ) - Real.sqrt k := fun k =>
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k))
  have hterm : ∀ k ∈ Finset.Icc 1 (M - 1),
      |(Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiRemainder k| ≤
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * (C * (M : ℝ) ^ (zetaZeroAbscissa + ε)) := by
    intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    rw [abs_mul, abs_of_nonneg (hw k)]
    refine mul_le_mul_of_nonneg_left ((hC k hk1).trans (mul_le_mul_of_nonneg_left ?_ hC0)) (hw k)
    exact Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast (by omega : k ≤ M)) hΘ0
  have hsum : |coherentSelbergSquareRootAbelMoment M| ≤
      (Real.sqrt M - 1) * (C * (M : ℝ) ^ (zetaZeroAbscissa + ε)) := by
    unfold coherentSelbergSquareRootAbelMoment
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul, ← Finset.Ico_add_one_right_eq_Icc,
      show M - 1 + 1 = M by omega, sum_Ico_sqrt_succ_sub hM1]
    simp
  have hsqrt : Real.sqrt M - 1 ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    linarith
  have hnum : |coherentSelbergSquareRootAbelMoment M| ≤
      C * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 + ε) := by
    calc |coherentSelbergSquareRootAbelMoment M|
        ≤ (Real.sqrt M - 1) * (C * (M : ℝ) ^ (zetaZeroAbscissa + ε)) := hsum
      _ ≤ (M : ℝ) ^ (1 / 2 : ℝ) * (C * (M : ℝ) ^ (zetaZeroAbscissa + ε)) :=
          mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ = C * ((M : ℝ) ^ (1 / 2 : ℝ) * (M : ℝ) ^ (zetaZeroAbscissa + ε)) := by ring
      _ = C * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 + ε) := by
          rw [← Real.rpow_add hM0]
          congr 2; ring
  rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
  calc |coherentSelbergSquareRootAbelMoment M|
      ≤ C * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 + ε) := hnum
    _ = C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) * M := by
        rw [mul_assoc, ← Real.rpow_add_one hM0.ne']
        congr 2; ring

/-- Unconditional subpower bound on `mobiusDivisorSquareRootAbelMoment` at `zetaZeroAbscissa`. -/
theorem exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M / M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_coherentSelbergSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  refine ⟨C + |2 * Real.eulerMascheroniConstant|, by positivity, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow1 : 1 ≤ (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hMone (by linarith [half_le_zetaZeroAbscissa])
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hMone
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by
    nlinarith [Real.sq_sqrt hMR.le, Real.sqrt_nonneg (M : ℝ)]
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      |2 * Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_of_pos hMR, abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    exact (div_le_iff₀ hMR).2 (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
  rw [mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM1, add_div]
  refine (abs_add_le _ _).trans ?_
  have h1 := hC M hM
  nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]

/-- **One-sided upper strip law for `zetaZeroAbscissa`.** -/
theorem zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → mobiusDivisorSquareRootAbelMoment M / M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_of_forall_xiZeroCopy_abs_re_sub_half_le (le_max_left 0 c)
    (abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow hC0 hM)

/-- **One-sided lower strip law for `zetaZeroAbscissa`.** -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → -(C + C * (M : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment M / M) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_of_forall_xiZeroCopy_abs_re_sub_half_le (le_max_left 0 c)
    (abs_re_sub_half_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hC0 hM)

/-- **Power-gap upper strip law for `zetaZeroAbscissa`.** -/
theorem zetaZeroAbscissa_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA : ∀ k ∈ A, 2 ≤ k → mobiusDivisorSquareRootAbelMoment k / k ≤ M + M * (k : ℝ) ^ c)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c :=
  zetaZeroAbscissa_le_of_forall_xiZeroCopy_abs_re_sub_half_le (le_max_left 0 c)
    (abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow hM0 hδ hK hA hgap)

/-- **Exact one-sided upper exponent law for `mobiusDivisorSquareRootAbelMoment`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorSquareRootAbel_upper_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorSquareRootAbelMoment M / M ≤ C * (M : ℝ) ^ c} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    mobiusDivisorSquareRootAbelMoment M / M ≤ C * (M : ℝ) ^ c}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun M hM => (le_abs_self _).trans (hC M hM)⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow hC0
        (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0))
      rw [max_eq_right hc0] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-- **Exact one-sided lower exponent law for `mobiusDivisorSquareRootAbelMoment`.** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorSquareRootAbel_lower_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      -(C * (M : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment M / M} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    -(C * (M : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment M / M}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0,
      fun M hM => (abs_le.mp (hC M hM)).1⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel hC0
        (fun M hM => (neg_le_neg (le_add_of_nonneg_left hC0)).trans (hC M hM))
      rw [max_eq_right hc0] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-! ## Section 3: Self-Contracting Any-Cutoff Quotient-Head Exponent Law (`quasi-rh.md` §8.2–8.3) -/

/-- Unconditional subpower bound on the `⌈M^θ⌉₊`-truncated quotient head at `zetaZeroAbscissa`. -/
theorem exists_mobiusDivisorQuotientPowerHead_subpower_zetaZeroAbscissa
    (θ : ℝ) (hθ : 0 ≤ θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  obtain ⟨C₂, hC₂0, hC₂⟩ := mobiusDivisorQuotientPowerHead_error_subpower θ hθ ε hε
  refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hΘ : 0 ≤ zetaZeroAbscissa - 1 / 2 := sub_nonneg.mpr half_le_zetaZeroAbscissa
  have htail : |(mobiusDivisorSquareRootAbelMoment M -
      mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M| ≤
      C₂ * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
    rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
    calc |mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊|
        ≤ C₂ * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 - θ * (zetaZeroAbscissa - 1 / 2) + ε) :=
          hC₂ M hM1
      _ ≤ C₂ * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 + ε) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hMone ?_) hC₂0
          nlinarith
      _ = C₂ * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) * M := by
          rw [mul_assoc, ← Real.rpow_add_one hM0.ne']
          congr 2; ring
  have hsplit : mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M =
      mobiusDivisorSquareRootAbelMoment M / M -
        (mobiusDivisorSquareRootAbelMoment M -
          mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M := by ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have h1 := hC₁ M hM
  linarith

/-- **Self-contracting one-sided upper strip law for the `⌈M^θ⌉₊`-truncated quotient head.**
For **any** positive power cutoff `θ > 0` (arbitrarily small, with no baseline `b₀ = 7/8` required),
a one-sided upper bound `mobiusDivisorQuotientHead M ⌈M^θ⌉₊ / M ≤ C + C M^c` forces
`zetaZeroAbscissa ≤ 1/2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_of_mobiusDivisorQuotientPowerHead_le_rpow
    {θ C c : ℝ} (hθ : 0 < θ) (hC0 : 0 ≤ C)
    (hhead : ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  set a : ℝ := max 0 c
  have ha0 : 0 ≤ a := le_max_left 0 c
  have hca : c ≤ a := le_max_right 0 c
  by_contra hlt
  push Not at hlt
  have hgap : 0 < zetaZeroAbscissa - 1 / 2 := by linarith
  set ε : ℝ := min θ 1 * (zetaZeroAbscissa - 1 / 2) / 2
  have hθmin : 0 < min θ 1 := lt_min hθ one_pos
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C₂, hC₂0, hC₂⟩ := mobiusDivisorQuotientPowerHead_error_subpower θ hθ.le ε hε
  set d : ℝ := max a ((1 - θ) * (zetaZeroAbscissa - 1 / 2) + ε)
  have hd0 : 0 ≤ d := ha0.trans (le_max_left _ _)
  have hfull : ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorSquareRootAbelMoment M / M ≤ (C + C₂) + (C + C₂) * (M : ℝ) ^ d := by
    intro M hM
    have hM1 : 1 ≤ M := by omega
    have hM0 : (0 : ℝ) < M := by positivity
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have htail : (mobiusDivisorSquareRootAbelMoment M -
        mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M ≤ C₂ * (M : ℝ) ^ d := by
      refine (le_abs_self _).trans ?_
      rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
      calc |mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊|
          ≤ C₂ * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 - θ * (zetaZeroAbscissa - 1 / 2) + ε) :=
            hC₂ M hM1
        _ = C₂ * (M : ℝ) ^ ((1 - θ) * (zetaZeroAbscissa - 1 / 2) + ε) * M := by
            rw [mul_assoc, ← Real.rpow_add_one hM0.ne']
            congr 2; ring
        _ ≤ C₂ * (M : ℝ) ^ d * M := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₂0) hM0.le
            exact Real.rpow_le_rpow_of_exponent_le hMone (le_max_right _ _)
    have hhd : mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M ≤ C + C * (M : ℝ) ^ d := by
      refine (hhead M hM).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC0))
      exact Real.rpow_le_rpow_of_exponent_le hMone (hca.trans (le_max_left _ _))
    have hsplit : mobiusDivisorSquareRootAbelMoment M / M =
        mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M +
          (mobiusDivisorSquareRootAbelMoment M -
            mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M := by ring
    rw [hsplit]
    linarith
  have hstrip := zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow
    (add_nonneg hC0 hC₂0) hfull
  rw [max_eq_right hd0] at hstrip
  have hd_lt : d < zetaZeroAbscissa - 1 / 2 := by
    refine max_lt (by linarith) ?_
    have hθle : min θ 1 ≤ θ := min_le_left θ 1
    have hmul : min θ 1 * (zetaZeroAbscissa - 1 / 2) ≤ θ * (zetaZeroAbscissa - 1 / 2) :=
      mul_le_mul_of_nonneg_right hθle hgap.le
    dsimp [ε]
    linarith [mul_pos hθmin hgap]
  linarith

/-- **Self-contracting one-sided lower strip law for the `⌈M^θ⌉₊`-truncated quotient head.** -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorQuotientPowerHead
    {θ C c : ℝ} (hθ : 0 < θ) (hC0 : 0 ≤ C)
    (hhead : ∀ M : ℕ, 2 ≤ M →
      -(C + C * (M : ℝ) ^ c) ≤ mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  set a : ℝ := max 0 c
  have ha0 : 0 ≤ a := le_max_left 0 c
  have hca : c ≤ a := le_max_right 0 c
  by_contra hlt
  push Not at hlt
  have hgap : 0 < zetaZeroAbscissa - 1 / 2 := by linarith
  set ε : ℝ := min θ 1 * (zetaZeroAbscissa - 1 / 2) / 2
  have hθmin : 0 < min θ 1 := lt_min hθ one_pos
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C₂, hC₂0, hC₂⟩ := mobiusDivisorQuotientPowerHead_error_subpower θ hθ.le ε hε
  set d : ℝ := max a ((1 - θ) * (zetaZeroAbscissa - 1 / 2) + ε)
  have hd0 : 0 ≤ d := ha0.trans (le_max_left _ _)
  have hfull : ∀ M : ℕ, 2 ≤ M →
      -((C + C₂) + (C + C₂) * (M : ℝ) ^ d) ≤ mobiusDivisorSquareRootAbelMoment M / M := by
    intro M hM
    have hM1 : 1 ≤ M := by omega
    have hM0 : (0 : ℝ) < M := by positivity
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have htail : |(mobiusDivisorSquareRootAbelMoment M -
        mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M| ≤ C₂ * (M : ℝ) ^ d := by
      rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
      calc |mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊|
          ≤ C₂ * (M : ℝ) ^ (zetaZeroAbscissa + 1 / 2 - θ * (zetaZeroAbscissa - 1 / 2) + ε) :=
            hC₂ M hM1
        _ = C₂ * (M : ℝ) ^ ((1 - θ) * (zetaZeroAbscissa - 1 / 2) + ε) * M := by
            rw [mul_assoc, ← Real.rpow_add_one hM0.ne']
            congr 2; ring
        _ ≤ C₂ * (M : ℝ) ^ d * M := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₂0) hM0.le
            exact Real.rpow_le_rpow_of_exponent_le hMone (le_max_right _ _)
    have hhd : -(C + C * (M : ℝ) ^ d) ≤ mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M := by
      refine (neg_le_neg (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hC0))).trans (hhead M hM)
      exact Real.rpow_le_rpow_of_exponent_le hMone (hca.trans (le_max_left _ _))
    have hsplit : mobiusDivisorSquareRootAbelMoment M / M =
        mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M +
          (mobiusDivisorSquareRootAbelMoment M -
            mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊) / M := by ring
    rw [hsplit]
    linarith [(abs_le.mp htail).1]
  have hstrip := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel
    (add_nonneg hC0 hC₂0) hfull
  rw [max_eq_right hd0] at hstrip
  have hd_lt : d < zetaZeroAbscissa - 1 / 2 := by
    refine max_lt (by linarith) ?_
    have hθle : min θ 1 ≤ θ := min_le_left θ 1
    have hmul : min θ 1 * (zetaZeroAbscissa - 1 / 2) ≤ θ * (zetaZeroAbscissa - 1 / 2) :=
      mul_le_mul_of_nonneg_right hθle hgap.le
    dsimp [ε]
    linarith [mul_pos hθmin hgap]
  linarith

/-- **Exact one-sided upper exponent law for the `⌈M^θ⌉₊`-truncated quotient head (`θ > 0`).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorQuotientPowerHead_upper_exponents
    {θ : ℝ} (hθ : 0 < θ) :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M ≤ C * (M : ℝ) ^ c} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M ≤ C * (M : ℝ) ^ c}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorQuotientPowerHead_subpower_zetaZeroAbscissa θ hθ.le ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun M hM => (le_abs_self _).trans (hC M hM)⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_mobiusDivisorQuotientPowerHead_le_rpow hθ hC0
        (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0))
      rw [max_eq_right hc0] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-- **Exact one-sided lower exponent law for the `⌈M^θ⌉₊`-truncated quotient head (`θ > 0`).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorQuotientPowerHead_lower_exponents
    {θ : ℝ} (hθ : 0 < θ) :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      -(C * (M : ℝ) ^ c) ≤ mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    -(C * (M : ℝ) ^ c) ≤ mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorQuotientPowerHead_subpower_zetaZeroAbscissa θ hθ.le ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0,
      fun M hM => (abs_le.mp (hC M hM)).1⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorQuotientPowerHead hθ hC0
        (fun M hM => (neg_le_neg (le_add_of_nonneg_left hC0)).trans (hC M hM))
      rw [max_eq_right hc0] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-- **One-sided subpower RH equivalence for the `⌈M^θ⌉₊`-truncated quotient head (`θ > 0`).** -/
theorem riemannHypothesis_iff_mobiusDivisorQuotientPowerHead_oneSided_subpower
    {θ : ℝ} (hθ : 0 < θ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorQuotientHead M ⌈(M : ℝ) ^ θ⌉₊ / M ≤ C * (M : ℝ) ^ ε := by
  rw [← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro hΘ ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorQuotientPowerHead_subpower_zetaZeroAbscissa θ hθ.le ε hε
    refine ⟨C, hC0, fun M hM => (le_abs_self _).trans ?_⟩
    simpa [hΘ] using hC M hM
  · intro h
    refine le_antisymm ?_ half_le_zetaZeroAbscissa
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC0, hC⟩ := h ε hε
    have hstrip := zetaZeroAbscissa_le_of_mobiusDivisorQuotientPowerHead_le_rpow hθ hC0
      (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0))
    rwa [max_eq_right hε.le] at hstrip

/-! ## Section 4: Unconditional Suzuki Finite-Contact Residual and Formation-Energy Exponent Laws
at `zetaZeroAbscissa` (`quasi-rh.md` §2.3, §8.1, §8.4) -/

/-- Exact comparison between `suzukiNaturalApertureCompletedLowerHardyAmplitude N` and
`criticalMellinChebyshevResolventSource (Real.log N) / 2` for `N ≥ 2`. -/
theorem abs_suzukiCompletedLowerHardyAmplitude_sub_half_resolvent_le {N : ℕ} (hN : 2 ≤ N) :
    |suzukiNaturalApertureCompletedLowerHardyAmplitude N -
        criticalMellinChebyshevResolventSource (Real.log N) / 2| ≤
      unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hH : unitRieszSuzukiBase ≤ Real.log N :=
    (unitRieszSuzukiBase_lt_log_two.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hNR (by exact_mod_cast hN))).le
  have hGreen : suzukiNaturalApertureCompletedLowerHardyAmplitude N =
      unitRieszSuzukiGreen (Real.log N) := by
    have h := suzukiNaturalApertureCompletedLowerHardyAmplitude_add_two_eq_green (N - 2)
    simpa [Nat.sub_add_cancel hN] using h
  have hP := abs_unitRieszSuzukiPolarCorrection_le hH
  have hA := abs_unitRieszSuzukiArchCorrection_le hH
  have hout := unitRieszSuzuki_outgoing_eq_green hN
  have hcharge := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN
  have hexact : suzukiNaturalApertureCompletedLowerHardyAmplitude N -
      criticalMellinChebyshevResolventSource (Real.log N) / 2 =
      -unitRieszSuzukiPolarCorrection (Real.log N) +
        unitRieszSuzukiArchCorrection (Real.log N) := by
    linarith
  rw [hexact]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  exact add_le_add hP hA

/-- Unconditional subpower bound on `suzukiNaturalApertureCompletedLowerHardyAmplitude` at `zetaZeroAbscissa`. -/
theorem exists_suzukiCompletedLowerHardyAmplitude_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  set J : ℝ := |2 * Real.eulerMascheroniConstant| + 1 +
    unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    unfold unitRieszSuzukiPolarUniformBound; positivity
  have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    unfold unitRieszSuzukiArchUniformBound
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      unitRieszSuzukiArchDenominator_pos.le
  refine ⟨C + J, by dsimp [J]; positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow1 : 1 ≤ (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hN1 (by linarith [half_le_zetaZeroAbscissa])
  have hres := abs_resolvent_log_nat_le_mobiusDivisorSquareRootAbel hN
  have hdiff := abs_suzukiCompletedLowerHardyAmplitude_sub_half_resolvent_le hN
  have htri : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
      |criticalMellinChebyshevResolventSource (Real.log N)| / 2 +
        (unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound) := by
    have h1 := abs_add_le
      (suzukiNaturalApertureCompletedLowerHardyAmplitude N -
        criticalMellinChebyshevResolventSource (Real.log N) / 2)
      (criticalMellinChebyshevResolventSource (Real.log N) / 2)
    rw [sub_add_cancel, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    linarith
  have hCN := hC N hN
  dsimp [J]
  nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]

/-- **One-sided upper strip law for `suzukiNaturalApertureCompletedLowerHardyAmplitude`.** -/
theorem zetaZeroAbscissa_le_of_suzukiCompletedLowerHardyAmplitude_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hG : ∀ N : ℕ, 2 ≤ N →
      suzukiNaturalApertureCompletedLowerHardyAmplitude N ≤ C + C * (N : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  set α : ℝ := max 0 c
  have hα0 : 0 ≤ α := le_max_left 0 c
  have hcα : c ≤ α := le_max_right 0 c
  have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    unfold unitRieszSuzukiPolarUniformBound; positivity
  have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    unfold unitRieszSuzukiArchUniformBound
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      unitRieszSuzukiArchDenominator_pos.le
  refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_abs_re_sub_half_le hα0
    (abs_re_sub_half_le_of_criticalResolvent_log_nat_le_rpow
      (B := 4 * C + 2 * (unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound))
      (by positivity) hα0 fun N hN => ?_)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpow1 : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hN1 hα0
  have hpowc : (N : ℝ) ^ c ≤ (N : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hN1 hcα
  have hdiff := (abs_le.mp (abs_suzukiCompletedLowerHardyAmplitude_sub_half_resolvent_le hN)).1
  have hGN := hG N hN
  nlinarith

/-- **Polynomial-growth quasi-RH strip law for higher finite-contact Suzuki residuals (`m ≥ 1`).**
Generalizes `xiZeroHalfPlaneBound_suzukiFiniteContactWidth_of_finiteContactResidualEventuallyBounded`
from boundedness (`r = 0`) to arbitrary polynomial rate `r ∈ ℝ` (`quasi-rh.md` §2.3). -/
theorem zetaZeroAbscissa_le_of_eventually_suzukiFiniteContactResidual_le_rpow
    {m : ℕ} (hm : 1 ≤ m) {B r : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreFiniteContactResidual m N ≤ B * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 (suzukiFiniteContactWidth m + r / (2 * (m : ℝ))) := by
  set w : ℝ := max 0 (suzukiFiniteContactWidth m + r / (2 * (m : ℝ)))
  have hw0 : 0 ≤ w := le_max_left _ _
  have hwr : suzukiFiniteContactWidth m + r / (2 * (m : ℝ)) ≤ w := le_max_right _ _
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hevent : ∀ᶠ N : ℕ in atTop,
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1) * (N : ℝ) ^ w := by
    filter_upwards [hbound,
      eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero,
      eventually_completedAnchor_sq_le_suzukiTransitionCoreAlignedEnergy,
      eventually_ge_atTop (2 : ℕ)] with N hres hC hG hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hC0 : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy N :=
      lt_of_le_of_ne (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N) (Ne.symm hC)
    have hCpow0 : 0 < suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) := pow_pos hC0 _
    have hEm : suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m ≤
        B * (N : ℝ) ^ r * suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) := by
      rw [suzukiTransitionCoreFiniteContactResidual, dif_neg hC] at hres
      exact (div_le_iff₀ hCpow0).mp hres
    have hCupper := suzukiNaturalApertureTransitionCoreCauchyEnergy_le_linear N
    have hGpowE : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m) ≤
        suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m := by
      rw [pow_mul, sq_abs]
      exact pow_le_pow_left₀ (sq_nonneg _) hG m
    have hexp_le : ((m - 1 : ℕ) : ℝ) + r ≤ (2 * m : ℕ) * w := by
      have h1 : ((m - 1 : ℕ) : ℝ) + r =
          (2 * m : ℕ) * (suzukiFiniteContactWidth m + r / (2 * (m : ℝ))) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hm]
        unfold suzukiFiniteContactWidth
        field_simp
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left hwr (by positivity)
    have hpow_le : (N : ℝ) ^ (m - 1) * (N : ℝ) ^ r ≤ ((N : ℝ) ^ w) ^ (2 * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hNR, ← Real.rpow_natCast ((N : ℝ) ^ w),
        ← Real.rpow_mul hNR.le, mul_comm w]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp_le
    have hGpow : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m) ≤
        (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1)) * ((N : ℝ) ^ w) ^ (2 * m) := by
      calc |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ^ (2 * m)
          ≤ suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m := hGpowE
        _ ≤ B * (N : ℝ) ^ r * suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) := hEm
        _ ≤ B * (N : ℝ) ^ r * (suzukiTransitionCoreLinearEnvelope * (N : ℝ)) ^ (m - 1) := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
              (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N)
              (by simpa [suzukiTransitionCoreLinearEnvelope] using hCupper) (m - 1))
              (mul_nonneg hB0 (Real.rpow_nonneg hNR.le r))
        _ = (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1)) *
              ((N : ℝ) ^ (m - 1) * (N : ℝ) ^ r) := by rw [mul_pow]; ring
        _ ≤ (B * suzukiTransitionCoreLinearEnvelope ^ (m - 1)) * ((N : ℝ) ^ w) ^ (2 * m) :=
            mul_le_mul_of_nonneg_left hpow_le
              (mul_nonneg hB0 (pow_nonneg suzukiTransitionCoreLinearEnvelope_nonneg _))
    set y : ℝ := (N : ℝ) ^ w
    have hy : 0 < y := Real.rpow_pos_of_pos hNR w
    set z : ℝ := |suzukiNaturalApertureCompletedLowerHardyAmplitude N| / y
    have hz0 : 0 ≤ z := div_nonneg (abs_nonneg _) hy.le
    have hzPow : z ^ (2 * m) ≤ B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) := by
      rw [div_pow, div_le_iff₀ (pow_pos hy _)]
      exact hGpow
    have hz : z ≤ z ^ (2 * m) + 1 := by
      by_cases hz1 : z ≤ 1
      · linarith [pow_nonneg hz0 (2 * m)]
      · have h1z : 1 ≤ z := le_of_not_ge hz1
        have hp : z ^ (1 : ℕ) ≤ z ^ (2 * m) := pow_le_pow_right₀ h1z (by omega)
        linarith [show z ≤ z ^ (2 * m) by simpa using hp]
    have hzle : z ≤ B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1 := by linarith
    have hrecover : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| = z * y := by
      dsimp [z]; field_simp [hy.ne']
    rw [hrecover]
    exact mul_le_mul_of_nonneg_right hzle hy.le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  set K₀ : ℝ := B * suzukiTransitionCoreLinearEnvelope ^ (m - 1) + 1
  have hK₀ : 0 ≤ K₀ := add_nonneg
    (mul_nonneg hB0 (pow_nonneg suzukiTransitionCoreLinearEnvelope_nonneg _)) zero_le_one
  set K : ℝ := K₀ + ∑ n ∈ Finset.range N₀, |suzukiNaturalApertureCompletedLowerHardyAmplitude n|
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hall : ∀ N : ℕ, 2 ≤ N →
      suzukiNaturalApertureCompletedLowerHardyAmplitude N ≤ K + K * (N : ℝ) ^ w := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hpow1 : 1 ≤ (N : ℝ) ^ w := Real.one_le_rpow hN1 hw0
    refine (le_abs_self _).trans ?_
    by_cases hlarge : N₀ ≤ N
    · have hmain := hN₀ N hlarge
      have hK₀K : K₀ ≤ K :=
        le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) w]
    · have hmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (lt_of_not_ge hlarge)
      have hterm : |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
          ∑ n ∈ Finset.range N₀, |suzukiNaturalApertureCompletedLowerHardyAmplitude n| :=
        Finset.single_le_sum
          (f := fun n : ℕ => |suzukiNaturalApertureCompletedLowerHardyAmplitude n|)
          (fun _ _ => abs_nonneg _) hmem
      have hsumK : ∑ n ∈ Finset.range N₀, |suzukiNaturalApertureCompletedLowerHardyAmplitude n| ≤ K :=
        le_add_of_nonneg_left hK₀
      nlinarith
  have hstrip := zetaZeroAbscissa_le_of_suzukiCompletedLowerHardyAmplitude_le_rpow hK0 hall
  rwa [max_eq_right hw0] at hstrip

/-- **Unconditional upper bound on higher finite-contact Suzuki residuals at `zetaZeroAbscissa`.** -/
theorem eventually_suzukiFiniteContactResidual_le_rpow_zetaZeroAbscissa
    {m : ℕ} (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      suzukiTransitionCoreFiniteContactResidual m N ≤
        B * (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := ε / (2 * (m : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK0, hK⟩ := exists_suzukiCompletedLowerHardyAmplitude_subpower_zetaZeroAbscissa δ hδ
  have hK' : ∀ N : ℕ, 2 ≤ N →
      |suzukiNaturalApertureCompletedLowerHardyAmplitude N| ≤
        (K + 1) * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + δ) := by
    intro N hN
    refine (hK N hN).trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hK0' : 0 ≤ suzukiTransitionCoreAnchorConditionNumberBound := by
    rw [suzukiTransitionCoreAnchorConditionNumberBound]; positivity
  set B : ℝ := (16 : ℝ) ^ (m - 1) *
    (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2) ^ m
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB0, ?_⟩
  have hq_quarter : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) < unitRieszCoherentPrimeOutgoingCharge N / Real.sqrt (N : ℝ) :=
    (tendsto_order.1 tendsto_unitRieszCoherentPrimeOutgoingCharge_div_sqrt_atTop_one_third).1
      (1 / 4) (by norm_num)
  filter_upwards [hq_quarter,
    eventually_unitRieszCoherentPrimeOutgoingCharge_ne_zero,
    eventually_suzukiTransitionCore_le_anchorConditionNumber_mul_sq,
    eventually_suzukiNaturalApertureTransitionCoreCauchyEnergy_ne_zero,
    eventually_ge_atTop (2 : ℕ)] with N hq4 hqne hcond hCne hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hsqrt0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hqlow : Real.sqrt (N : ℝ) / 4 ≤ unitRieszCoherentPrimeOutgoingCharge N := by
    have := (lt_div_iff₀ hsqrt0).mp hq4
    linarith
  have hClow : (N : ℝ) / 16 ≤ suzukiNaturalApertureTransitionCoreCauchyEnergy N := by
    have hsq : (Real.sqrt (N : ℝ) / 4) ^ (2 : ℕ) ≤
        unitRieszCoherentPrimeOutgoingCharge N ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hqlow 2
    have hsqN : (Real.sqrt (N : ℝ) / 4) ^ (2 : ℕ) = (N : ℝ) / 16 := by
      rw [div_pow, Real.sq_sqrt hNR.le]; norm_num
    rw [hsqN] at hsq
    exact hsq.trans (unitRieszCoherentPrimeOutgoingCharge_sq_le_transitionCore hN)
  have hCpow_low : ((N : ℝ) / 16) ^ (m - 1) ≤
      suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) :=
    pow_le_pow_left₀ (by positivity) hClow (m - 1)
  have hE : suzukiTransitionCoreAlignedGammaCompletedEnergy N ≤
      suzukiTransitionCoreAnchorConditionNumberBound *
        ((K + 1) * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + δ)) ^ (2 : ℕ) := by
    refine (suzukiAlignedEnergy_le_condition_mul_completedAnchor_sq hqne hcond).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK0'
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK' N hN) 2
  have hpowN : ((N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + δ)) ^ (2 * m) =
      (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNR.le]
    congr 1
    dsimp [δ]
    push_cast
    field_simp
  have hEm : suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m ≤
      (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2) ^ m *
        (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) + ε) := by
    calc suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m
        ≤ (suzukiTransitionCoreAnchorConditionNumberBound *
            ((K + 1) * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + δ)) ^ (2 : ℕ)) ^ m :=
          pow_le_pow_left₀ (suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg N) hE m
      _ = (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2) ^ m *
            ((N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + δ)) ^ (2 * m) := by
          rw [mul_pow (K + 1), ← mul_assoc,
            mul_pow (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2), ← pow_mul]
      _ = (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2) ^ m *
            (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) + ε) := by
          rw [hpowN]
  rw [suzukiTransitionCoreFiniteContactResidual, dif_neg hCne,
    div_le_iff₀ (pow_pos (lt_of_lt_of_le (by positivity) hClow) _)]
  calc suzukiTransitionCoreAlignedGammaCompletedEnergy N ^ m
      ≤ (suzukiTransitionCoreAnchorConditionNumberBound * (K + 1) ^ 2) ^ m *
          (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) + ε) := hEm
    _ = B * (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε) *
          ((N : ℝ) / 16) ^ (m - 1) := by
        dsimp [B]
        rw [div_pow, ← Real.rpow_natCast (N : ℝ)]
        have hpow_eq : (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) + ε) =
            (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε) *
              (N : ℝ) ^ ((m - 1 : ℕ) : ℝ) := by
          rw [← Real.rpow_add hNR]
          congr 1; ring
        rw [hpow_eq]
        field_simp
    _ ≤ B * (N : ℝ) ^ ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε) *
          suzukiNaturalApertureTransitionCoreCauchyEnergy N ^ (m - 1) :=
        mul_le_mul_of_nonneg_left hCpow_low
          (mul_nonneg hB0 (Real.rpow_nonneg hNR.le _))

/-- **Exact finite-contact exponent law for `zetaZeroAbscissa` (`m ≥ 1`).** -/
theorem zetaZeroAbscissa_eq_half_add_suzukiFiniteContactWidth_add_sInf {m : ℕ} (hm : 1 ≤ m) :
    zetaZeroAbscissa = 1 / 2 + suzukiFiniteContactWidth m +
      (1 / (2 * (m : ℝ))) * sInf {r : ℝ | -((m - 1 : ℕ) : ℝ) ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B * (N : ℝ) ^ r} := by
  set S := {r : ℝ | -((m - 1 : ℕ) : ℝ) ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∀ᶠ N : ℕ in atTop, suzukiTransitionCoreFiniteContactResidual m N ≤ B * (N : ℝ) ^ r}
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hΘ : 0 ≤ zetaZeroAbscissa - 1 / 2 := sub_nonneg.mpr half_le_zetaZeroAbscissa
  have hmem : ∀ ε : ℝ, 0 < ε →
      (2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε ∈ S := by
    intro ε hε
    obtain ⟨B, hB0, hB⟩ := eventually_suzukiFiniteContactResidual_le_rpow_zetaZeroAbscissa hm ε hε
    refine ⟨?_, B, hB0, hB⟩
    have : 0 ≤ (2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) := by positivity
    linarith
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨-((m - 1 : ℕ) : ℝ), fun r hr => hr.1⟩
  have hw_id : ∀ r : ℝ,
      suzukiFiniteContactWidth m + r / (2 * (m : ℝ)) =
        (((m - 1 : ℕ) : ℝ) + r) / (2 * (m : ℝ)) := by
    intro r
    rw [Nat.cast_sub hm, suzukiFiniteContactWidth]
    ring
  refine le_antisymm ?_ ?_
  · have hle : (2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) ≤ sInf S := by
      refine le_csInf hne fun r hr => ?_
      obtain ⟨hr0, B, hB0, hB⟩ := hr
      have hstrip := zetaZeroAbscissa_le_of_eventually_suzukiFiniteContactResidual_le_rpow hm hB0 hB
      have hw0 : 0 ≤ suzukiFiniteContactWidth m + r / (2 * (m : ℝ)) := by
        rw [hw_id]
        exact div_nonneg (by linarith) (by positivity)
      rw [max_eq_right hw0, hw_id] at hstrip
      have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mp
        (show zetaZeroAbscissa - 1 / 2 ≤ (((m - 1 : ℕ) : ℝ) + r) / (2 * (m : ℝ)) by linarith)
      push_cast
      linarith
    have hdiv : zetaZeroAbscissa - 1 / 2 ≤ (((m - 1 : ℕ) : ℝ) + sInf S) / (2 * (m : ℝ)) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mpr
        (by push_cast at hle; linarith)
    have h1 := hw_id (sInf S)
    linarith [show (1 / (2 * (m : ℝ))) * sInf S = sInf S / (2 * (m : ℝ)) by ring]
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε : ℝ := 2 * (m : ℝ) * δ
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hle := csInf_le hbdd (hmem ε hε)
    have hdiv := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mpr
      (show ((m - 1 : ℕ) : ℝ) + sInf S ≤
        ((m - 1 : ℕ) : ℝ) + ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε)
        by linarith)
    rw [← hw_id (sInf S)] at hdiv
    have hsimp : (((m - 1 : ℕ) : ℝ) +
        ((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε)) / (2 * (m : ℝ)) =
        zetaZeroAbscissa - 1 / 2 + δ := by
      dsimp [ε]
      push_cast
      field_simp
      ring
    rw [hsimp] at hdiv
    linarith [show (1 / (2 * (m : ℝ))) * sInf S = sInf S / (2 * (m : ℝ)) by ring]

/-- **Sub-frontier power decay of `suzukiTransitionCoreFiniteContactResidual m N`.**
Whenever `zetaZeroAbscissa < 1/2 + suzukiFiniteContactWidth m` (in particular under RH for every
`m ≥ 2`), the order-`m` finite-contact residual decays to `0` as `N → ∞`. -/
theorem tendsto_suzukiFiniteContactResidual_atTop_zero_of_zetaZeroAbscissa_lt
    {m : ℕ} (hm : 1 ≤ m) (hΘ : zetaZeroAbscissa < 1 / 2 + suzukiFiniteContactWidth m) :
    Tendsto (fun N : ℕ => suzukiTransitionCoreFiniteContactResidual m N) atTop (𝓝 0) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp_neg : (2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) < 0 := by
    have h1 : zetaZeroAbscissa - 1 / 2 < ((m - 1 : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      unfold suzukiFiniteContactWidth at hΘ
      rw [Nat.cast_sub hm]
      linarith
    have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ))).mp h1
    push_cast
    linarith
  set ε : ℝ := -((2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨B, hB0, hB⟩ := eventually_suzukiFiniteContactResidual_le_rpow_zetaZeroAbscissa hm ε hε
  have hneg : (2 * m : ℕ) * (zetaZeroAbscissa - 1 / 2) - ((m - 1 : ℕ) : ℝ) + ε = -ε := by
    dsimp [ε]; ring
  rw [hneg] at hB
  have hmajor : Tendsto (fun N : ℕ => B * (N : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop).const_mul B
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [hB] with N hBN
  have hres0 : 0 ≤ suzukiTransitionCoreFiniteContactResidual m N := by
    unfold suzukiTransitionCoreFiniteContactResidual
    split_ifs
    · exact le_rfl
    · exact div_nonneg (pow_nonneg (suzukiTransitionCoreAlignedGammaCompletedEnergy_nonneg N) m)
        (pow_nonneg (suzukiNaturalApertureTransitionCoreCauchyEnergy_nonneg N) (m - 1))
  rw [Real.norm_eq_abs, abs_of_nonneg hres0]
  exact hBN

/-- Exact two-sided sandwich between local production of `suzukiCompletedFormationEnergy` and
`(suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 1))^2`. -/
theorem suzukiCompletedFormationEnergy_succ_sub_sandwich {N : ℕ} (hN : 2 ≤ N) :
    (1 / 2 : ℝ) * (suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 1)) ^ (2 : ℕ) ≤
      suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ∧
    suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤
      (suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 1)) ^ (2 : ℕ) := by
  rw [suzukiCompletedFormationEnergy_succ_sub hN,
    ← suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource (by omega : 2 ≤ N + 1)]
  have hs : 0 ≤ (suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 1)) ^ (2 : ℕ) := sq_nonneg _
  have hden : (0 : ℝ) < (N + 2 : ℕ) := by positivity
  have hlow : (1 / 2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) := by
    rw [le_div_iff₀ hden]; push_cast; linarith
  have hup : ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) ≤ 1 := by
    rw [div_le_one hden]; push_cast; linarith
  exact ⟨mul_le_mul_of_nonneg_right hlow hs, (mul_le_of_le_one_left hs hup)⟩

/-- **Unconditional subpower bound on local formation-energy production at `zetaZeroAbscissa`.** -/
theorem exists_suzukiCompletedFormationEnergy_sub_le_rpow_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
      suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤
        B * (N : ℝ) ^ (2 * (zetaZeroAbscissa - 1 / 2) + ε) := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_suzukiCompletedLowerHardyAmplitude_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
  set p : ℝ := 2 * (zetaZeroAbscissa - 1 / 2) + ε
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [half_le_zetaZeroAbscissa]
  refine ⟨K ^ 2 * (2 : ℝ) ^ p, by positivity, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by positivity
  have hN1R : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hup := (suzukiCompletedFormationEnergy_succ_sub_sandwich hN).2
  have hG : (suzukiNaturalApertureCompletedLowerHardyAmplitude (N + 1)) ^ (2 : ℕ) ≤
      K ^ 2 * ((N + 1 : ℕ) : ℝ) ^ p := by
    rw [← sq_abs]
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hK (N + 1) (by omega)) 2
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast (((N + 1 : ℕ) : ℝ) ^ _), ← Real.rpow_mul hN1R.le]
    congr 2
    dsimp [p]; ring
  have h2N : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (by omega : N + 1 ≤ 2 * N)
  have hpow : ((N + 1 : ℕ) : ℝ) ^ p ≤ (2 : ℝ) ^ p * (N : ℝ) ^ p := by
    calc ((N + 1 : ℕ) : ℝ) ^ p ≤ (2 * (N : ℝ)) ^ p := Real.rpow_le_rpow hN1R.le h2N hp0
      _ = (2 : ℝ) ^ p * (N : ℝ) ^ p := Real.mul_rpow (by norm_num) hNR.le
  exact hup.trans (hG.trans (by nlinarith [sq_nonneg K]))

/-- **Quasi-RH strip law from local formation-energy production (`quasi-rh.md` §8.1, §8.4).** -/
theorem zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_sub_le_rpow
    {B r : ℝ} (hB0 : 0 ≤ B)
    (hF : ∀ N : ℕ, 2 ≤ N →
      suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤
        B * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 (r / 2) := by
  set w : ℝ := max 0 (r / 2)
  have hw0 : 0 ≤ w := le_max_left 0 (r / 2)
  have hwr : r ≤ 2 * w := by have := le_max_right 0 (r / 2); linarith
  set K : ℝ := (2 * B + 1) + |suzukiNaturalApertureCompletedLowerHardyAmplitude 2|
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hall : ∀ M : ℕ, 2 ≤ M →
      suzukiNaturalApertureCompletedLowerHardyAmplitude M ≤ K + K * (M : ℝ) ^ w := by
    intro M hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have hpow1 : 1 ≤ (M : ℝ) ^ w := Real.one_le_rpow hM1 hw0
    refine (le_abs_self _).trans ?_
    rcases eq_or_lt_of_le hM with rfl | hM3
    · dsimp [K]
      have : 0 ≤ (2 * B + 1 + |suzukiNaturalApertureCompletedLowerHardyAmplitude 2|) * (2 : ℝ) ^ w :=
        by positivity
      linarith
    · set N : ℕ := M - 1
      have hN2 : 2 ≤ N := by omega
      have hNM : N + 1 = M := Nat.sub_add_cancel (by omega : 1 ≤ M)
      have hNR : (0 : ℝ) < N := by positivity
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      have hMR : (0 : ℝ) < M := by positivity
      have hlow := (suzukiCompletedFormationEnergy_succ_sub_sandwich hN2).1
      have hFN := hF N hN2
      rw [hNM] at hlow hFN
      have hGsq : |suzukiNaturalApertureCompletedLowerHardyAmplitude M| ^ (2 : ℕ) ≤
          2 * B * ((M : ℝ) ^ w) ^ (2 : ℕ) := by
        rw [sq_abs]
        have h1 : (suzukiNaturalApertureCompletedLowerHardyAmplitude M) ^ (2 : ℕ) ≤
            2 * B * (N : ℝ) ^ r := by linarith
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        calc (N : ℝ) ^ r ≤ (N : ℝ) ^ (2 * w) := Real.rpow_le_rpow_of_exponent_le hN1R hwr
          _ ≤ (M : ℝ) ^ (2 * w) :=
              Real.rpow_le_rpow hNR.le (by exact_mod_cast (by omega : N ≤ M)) (by positivity)
          _ = ((M : ℝ) ^ w) ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast ((M : ℝ) ^ w), ← Real.rpow_mul hMR.le]
              congr 1; ring
      set y : ℝ := (M : ℝ) ^ w
      have hy : 0 < y := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < M) w
      set z : ℝ := |suzukiNaturalApertureCompletedLowerHardyAmplitude M| / y
      have hz0 : 0 ≤ z := div_nonneg (abs_nonneg _) hy.le
      have hz2 : z ^ (2 : ℕ) ≤ 2 * B := by
        rw [div_pow, div_le_iff₀ (sq_pos_of_pos hy)]
        exact hGsq
      have hz : z ≤ 2 * B + 1 := by
        nlinarith [sq_nonneg (z - 1)]
      have hrec : |suzukiNaturalApertureCompletedLowerHardyAmplitude M| = z * y := by
        dsimp [z]; field_simp [hy.ne']
      rw [hrec]
      have hzy : z * y ≤ (2 * B + 1) * y := mul_le_mul_of_nonneg_right hz hy.le
      dsimp [K]
      nlinarith [abs_nonneg (suzukiNaturalApertureCompletedLowerHardyAmplitude 2)]
  have hstrip := zetaZeroAbscissa_le_of_suzukiCompletedLowerHardyAmplitude_le_rpow hK0 hall
  rwa [max_eq_right hw0] at hstrip

/-- **Quasi-RH strip law from cumulative `suzukiCompletedFormationEnergy` (`quasi-rh.md` §8.4).** -/
theorem zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_le_rpow
    {B r : ℝ} (hB0 : 0 ≤ B) (hr0 : 0 ≤ r)
    (hF : ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ 1 / 2 + r / 2 := by
  set B' : ℝ := B * (2 : ℝ) ^ r + |suzukiCompletedFormationEnergy 2|
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  have hsub : ∀ N : ℕ, 2 ≤ N →
      suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤
        B' * (N : ℝ) ^ r := by
    intro N hN
    have hNR : (0 : ℝ) < N := by positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hpow1 : 1 ≤ (N : ℝ) ^ r := Real.one_le_rpow hN1 hr0
    have hmono := suzukiCompletedFormationEnergy_monotoneOn le_rfl hN
    have hFsucc := hF (N + 1) (by omega)
    have h2N : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (by omega : N + 1 ≤ 2 * N)
    have hpow : ((N + 1 : ℕ) : ℝ) ^ r ≤ (2 : ℝ) ^ r * (N : ℝ) ^ r := by
      calc ((N + 1 : ℕ) : ℝ) ^ r ≤ (2 * (N : ℝ)) ^ r := Real.rpow_le_rpow (by positivity) h2N hr0
        _ = (2 : ℝ) ^ r * (N : ℝ) ^ r := Real.mul_rpow (by norm_num) hNR.le
    have hF2 : -|suzukiCompletedFormationEnergy 2| ≤ suzukiCompletedFormationEnergy 2 :=
      neg_abs_le _
    have h1 : suzukiCompletedFormationEnergy (N + 1) ≤ B * (2 : ℝ) ^ r * (N : ℝ) ^ r := by
      linarith [mul_le_mul_of_nonneg_left hpow hB0]
    have h2 : -suzukiCompletedFormationEnergy N ≤ |suzukiCompletedFormationEnergy 2| * (N : ℝ) ^ r := by
      linarith [mul_le_mul_of_nonneg_left hpow1 (abs_nonneg (suzukiCompletedFormationEnergy 2))]
    dsimp [B']
    linarith
  have hstrip := zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_sub_le_rpow hB'0 hsub
  rwa [max_eq_right (by positivity : 0 ≤ r / 2)] at hstrip

/-- **Exact exponent law for local production of `suzukiCompletedFormationEnergy`.** -/
theorem zetaZeroAbscissa_eq_half_add_half_sInf_suzukiCompletedFormationEnergy_increment_exponents :
    zetaZeroAbscissa = 1 / 2 + (1 / 2 : ℝ) * sInf {r : ℝ | 0 ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 2 ≤ N →
        suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤
          B * (N : ℝ) ^ r} := by
  set S := {r : ℝ | 0 ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
    suzukiCompletedFormationEnergy (N + 1) - suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → 2 * (zetaZeroAbscissa - 1 / 2) + ε ∈ S := by
    intro ε hε
    obtain ⟨B, hB0, hB⟩ := exists_suzukiCompletedFormationEnergy_sub_le_rpow_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], B, hB0, hB⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
  refine le_antisymm ?_ ?_
  · have hle : 2 * (zetaZeroAbscissa - 1 / 2) ≤ sInf S := by
      refine le_csInf hne fun r hr => ?_
      obtain ⟨hr0, B, hB0, hB⟩ := hr
      have h := zetaZeroAbscissa_le_of_suzukiCompletedFormationEnergy_sub_le_rpow hB0 hB
      rw [max_eq_right (by linarith : 0 ≤ r / 2)] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hle := csInf_le hbdd (hmem (2 * δ) (by positivity))
    linarith

end

end RHTower
