import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorOneSided
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorAbelSubpower
import GaloisForLFunctions.RHTower.MobiusRieszQuarticSampling
import GaloisForLFunctions.RHTower.WeilLagPowerGapSampling

/-!
# One-Sided Upper Strip Law, Endpoint Monotonicity, and Power-Gap Bootstrap for the Möbius Divisor Abel Moment

`CCMFUSuzukiMobiusDivisorAbelSubpower` previously routed zero-free strip bounds for the Möbius
divisor square-root Abel moment
`mobiusDivisorSquareRootAbelMoment M = Σ_{m=1}^{M-1} (√M − √m) (μ * 1)(m)`
through the **two-sided** Laplace transform of `criticalMellinChebyshevResolventSource`, requiring a
two-sided norm bound `|mobiusDivisorSquareRootAbelMoment M / M| ≤ C M^α`. Meanwhile,
`MobiusRieszQuarticSampling` used second-difference semiconvexity with the trivial Chebyshev bound
`|ψ(k) − k| ≤ A k`, which restricted polynomial sampling of `mobiusDivisorSquareRootAbelMoment` to
fourth powers (`m = 4`, gap `O(M^{3/4})`).

This module removes both limitations:

1. **One-sided upper exponential and power strip laws (`Section 1`):**
   Because `suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le` (`CCMUnitRieszSuzukiGreenPositiveInverse`)
   localizes the Green inversion to the compact interval `[unitRieszSuzukiBase, t]`, a one-sided
   exponential upper bound `unitRieszSuzukiGreen u ≤ B e^{α u}` (`α ≥ 0`) on `[unitRieszSuzukiBase, t]`
   acts as a constant `B e^{α t}` on that interval, yielding a one-sided exponential lower bound on
   `suzukiPsi t` and hence (via `abs_im_xiSpectralPoint_le_of_suzukiPsi_ge'`) the zero-free strip
   `|(q.1 : ℂ).re - 1/2| ≤ α`. Transporting through `criticalMellinChebyshevResolventSource` and
   `resolvent_log_nat_le_mobiusDivisorSquareRootAbel` proves that a **one-sided upper** power bound
   `mobiusDivisorSquareRootAbelMoment M / M ≤ C + C M^c` forces `|Re ρ - 1/2| ≤ max 0 c`
   (`abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow`), strengthening the subpower RH
   equivalence to a one-sided upper bound (`riemannHypothesis_iff_mobiusDivisorSquareRootAbel_oneSided_subpower`).

2. **Exact endpoint monotonicity and unconditional downward drift (`Section 2`):**
   Using `mobiusDivisorSquareRootAbelMoment_succ_sub` and the monotonicity of `ψ(d)`, we prove an
   exact interval sum representation (`mobiusDivisorSquareRootAbel_sub_eq`), an endpoint-only
   monotonicity sandwich (`mobiusDivisorSquareRootAbel_sub_endpoint_sandwich`) whose lower bound
   depends only on `ψ(k) − k` and whose upper bound depends only on `ψ(n) − n`, and an unconditional
   downward drift bound `-(n (√n − √k)) ≤ mobiusDivisorSquareRootAbelMoment n − mobiusDivisorSquareRootAbelMoment k`
   (`mobiusDivisorSquareRootAbel_sub_ge_neg_mul`).

3. **Power-gap transport and two-step supremum fixed-point bootstrap (`Section 3`):**
   Combining the first-difference inequality `(√n − √k) √n ≤ n − k` (`sqrt_sub_sqrt_mul_sqrt_le`)
   with our new one-sided upper strip law and the two-step supremum fixed-point bootstrap
   (`α = zeroReSup - 1/2`: Step 1 uses Chebyshev `β = 1` to obtain `α < 1/2`, Step 2 uses the
   explicit-formula Von Koch bridge at `e = α` to contract `α + δ/2 - δ = α - δ/2 < α`), we prove
   that a one-sided upper bound on any power-gap sampling set (`n − k ≤ K n^{1−δ}`, `δ > 0`) forces
   the full zero-free strip (`abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow`)
   and decides `RiemannHypothesis`, generalizing `MobiusRieszQuarticSampling` from `m = 4` to
   **every** `m ≥ 1` (`riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove`).
-/

open Real Set Filter Topology
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: One-sided upper exponential strip laws for Suzuki Green, critical Mellin resolvent,
and the Möbius divisor square-root Abel moment -/

/-- **One-sided upper exponential strip law for `unitRieszSuzukiGreen`.**
If `unitRieszSuzukiGreen t ≤ B e^{α t}` for `t ≥ unitRieszSuzukiBase` (`B ≥ 0`, `α ≥ 0`), then every
`q : XiZeroCopy` satisfies `|(q.1 : ℂ).re - 1/2| ≤ α`. -/
theorem abs_re_sub_half_le_of_unitRieszSuzukiGreen_le_exp {B α : ℝ} (hB0 : 0 ≤ B) (hα0 : 0 ≤ α)
    (hG : ∀ t : ℝ, unitRieszSuzukiBase ≤ t → unitRieszSuzukiGreen t ≤ B * Real.exp (α * t))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  have him : |(xiSpectralPoint q).im| ≤ α := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_suzukiPsi.continuousOn (s := Icc (0 : ℝ) unitRieszSuzukiBase))
    set A : ℝ := 2 * (B + unitRieszSuzukiGreenBoundaryBound) with hAdef
    have hA0 : 0 ≤ A := by
      rw [hAdef, unitRieszSuzukiGreenBoundaryBound]
      positivity
    set Q : ℝ := (η + 2) ^ 2 / η ^ 2 with hQdef
    have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
    set C₀ : ℝ := (2 * A + |M|) * Q with hC₀
    refine abs_im_xiSpectralPoint_le_of_suzukiPsi_ge' (C₀ := C₀) (ε := α + η) ?_ (by linarith) q
    intro t ht
    have hquad : (1 + t) ^ 2 ≤ Q * Real.exp (η * t) :=
      UnitRieszGreenInverse.quadratic_le_exponential hη ht
    have hexpα : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht)
    have hexpη : 1 ≤ Real.exp (η * t) := Real.one_le_exp (mul_nonneg hη.le ht)
    have hsq1 : 1 ≤ (1 + t) ^ 2 := by nlinarith [sq_nonneg t]
    have hQexp : (1 + t) ^ 2 * Real.exp (α * t) ≤ Q * Real.exp ((α + η) * t) := by
      calc (1 + t) ^ 2 * Real.exp (α * t)
          ≤ (Q * Real.exp (η * t)) * Real.exp (α * t) :=
            mul_le_mul_of_nonneg_right hquad (Real.exp_pos _).le
        _ = Q * Real.exp ((α + η) * t) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    by_cases hbt : unitRieszSuzukiBase ≤ t
    · have hl := suzukiPsi_quadratic_lower_of_unitRieszSuzukiGreen_le hbt
        (B := B * Real.exp (α * t)) (fun u hu => (hG u hu.1).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hα0)) hB0))
      have hd : 0 ≤ t - unitRieszSuzukiBase := sub_nonneg.mpr hbt
      have hdt : t - unitRieszSuzukiBase ≤ t := by linarith [unitRieszSuzukiBase_pos]
      have hp : 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
          (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 ≤ 2 * (1 + t) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hdt) (add_nonneg ht hd)]
      have hBbound : B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound ≤
          (B + unitRieszSuzukiGreenBoundaryBound) * Real.exp (α * t) := by
        have : 0 ≤ unitRieszSuzukiGreenBoundaryBound := by
          unfold unitRieszSuzukiGreenBoundaryBound; positivity
        nlinarith
      have h1 : 2 * (B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound) *
          (1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
            (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2) ≤
          2 * A * ((1 + t) ^ 2 * Real.exp (α * t)) := by
        rw [hAdef]
        have hp0 : 0 ≤ 1 + (3 / 2 : ℝ) * (t - unitRieszSuzukiBase) +
            (1 / 4 : ℝ) * (t - unitRieszSuzukiBase) ^ 2 := by positivity
        have hstep1 : 2 * (B * Real.exp (α * t) + unitRieszSuzukiGreenBoundaryBound) ≤
            A * Real.exp (α * t) := by rw [hAdef]; linarith
        have hstep2 := mul_le_mul hstep1 hp hp0 (mul_nonneg hA0 (Real.exp_pos _).le)
        linarith
      have h2 : 2 * A * ((1 + t) ^ 2 * Real.exp (α * t)) ≤
          C₀ * Real.exp ((α + η) * t) := by
        rw [hC₀]
        calc 2 * A * ((1 + t) ^ 2 * Real.exp (α * t))
            ≤ (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) :=
              mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M]) (by positivity)
          _ ≤ (2 * A + |M|) * (Q * Real.exp ((α + η) * t)) :=
              mul_le_mul_of_nonneg_left hQexp (by positivity)
          _ = (2 * A + |M|) * Q * Real.exp ((α + η) * t) := by ring
      linarith
    · have hm := hM t ⟨ht, le_of_not_ge hbt⟩
      rw [Real.norm_eq_abs] at hm
      have hneg := neg_abs_le (suzukiPsi t)
      have h1 : |M| ≤ (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) := by
        have : 1 ≤ (1 + t) ^ 2 * Real.exp (α * t) := one_le_mul_of_one_le_of_one_le hsq1 hexpα
        nlinarith [abs_nonneg M]
      have h2 : (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t)) ≤
          C₀ * Real.exp ((α + η) * t) := by
        rw [hC₀]
        calc (2 * A + |M|) * ((1 + t) ^ 2 * Real.exp (α * t))
            ≤ (2 * A + |M|) * (Q * Real.exp ((α + η) * t)) :=
              mul_le_mul_of_nonneg_left hQexp (by positivity)
          _ = (2 * A + |M|) * Q * Real.exp ((α + η) * t) := by ring
      linarith [le_abs_self M]
  rwa [xiSpectralPoint_im_eq, abs_sub_comm] at him

/-- **One-sided upper exponential strip law for `criticalMellinChebyshevResolventSource`.** -/
theorem abs_re_sub_half_le_of_criticalResolvent_le_exp {B α : ℝ} (hB0 : 0 ≤ B) (hα0 : 0 ≤ α)
    (hR : ∀ t : ℝ, 0 ≤ t → criticalMellinChebyshevResolventSource t ≤ B * Real.exp (α * t))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  set B' : ℝ := B / 2 + unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  have hpolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    have := abs_unitRieszSuzukiPolarCorrection_le (le_rfl : unitRieszSuzukiBase ≤ unitRieszSuzukiBase)
    exact (abs_nonneg _).trans this
  have harch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    have := abs_unitRieszSuzukiArchCorrection_le (le_rfl : unitRieszSuzukiBase ≤ unitRieszSuzukiBase)
    exact (abs_nonneg _).trans this
  have hB'0 : 0 ≤ B' := by dsimp [B']; positivity
  refine abs_re_sub_half_le_of_unitRieszSuzukiGreen_le_exp hB'0 hα0 (fun t ht => ?_) q
  have ht0 : 0 ≤ t := unitRieszSuzukiBase_pos.le.trans ht
  have heq := criticalMellinChebyshevResolventSource_half_eq_suzukiGreen ht
  have hpolar := (abs_le.mp (abs_unitRieszSuzukiPolarCorrection_le ht)).1
  have harch := (abs_le.mp (abs_unitRieszSuzukiArchCorrection_le ht)).2
  have hexp1 : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht0)
  have hRt := hR t ht0
  dsimp [B']
  nlinarith

/-- **One-sided upper integer-logarithmic strip law for `criticalMellinChebyshevResolventSource`.** -/
theorem abs_re_sub_half_le_of_criticalResolvent_log_nat_le_rpow {B α : ℝ} (hB0 : 0 ≤ B)
    (hα0 : 0 ≤ α)
    (hN : ∀ N : ℕ, 2 ≤ N → criticalMellinChebyshevResolventSource (Real.log N) ≤ B * (N : ℝ) ^ α)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ α := by
  have hC : 0 ≤ Real.log 4 + 5 := by positivity
  refine abs_re_sub_half_le_of_criticalResolvent_le_exp (B := B + 2 * (Real.log 4 + 5))
    (by positivity) hα0 (fun t ht => ?_) q
  have hexp1 : 1 ≤ Real.exp (α * t) := Real.one_le_exp (mul_nonneg hα0 ht)
  by_cases hlog : Real.log 2 ≤ t
  · set X := Real.exp t
    set N : ℕ := ⌊X⌋₊
    have hX2 : (2 : ℝ) ≤ X := by
      rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
      exact Real.exp_le_exp.mpr hlog
    have hXpos : 0 < X := Real.exp_pos t
    have hN2 : 2 ≤ N := Nat.le_floor hX2
    have hNX : (N : ℝ) ≤ X := Nat.floor_le hXpos.le
    have hXN : X ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one X).le
    have hcell := (abs_le.mp (UnitRieszOneSided.abs_resolvent_log_sub_nat_mul_le hN2 hNX hXN)).2
    rw [Real.log_exp] at hcell
    have hr0 : 0 ≤ (N : ℝ) / X := by positivity
    have hr1 : (N : ℝ) / X ≤ 1 := (div_le_one hXpos).2 hNX
    have hpow : (N : ℝ) ^ α ≤ Real.exp (α * t) := by
      calc (N : ℝ) ^ α ≤ X ^ α := Real.rpow_le_rpow (Nat.cast_nonneg N) hNX hα0
        _ = Real.exp (α * t) := by rw [← Real.exp_mul, mul_comm]
    have hsample : ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N) ≤
        B * Real.exp (α * t) := by
      calc ((N : ℝ) / X) * criticalMellinChebyshevResolventSource (Real.log N)
          ≤ ((N : ℝ) / X) * (B * (N : ℝ) ^ α) := mul_le_mul_of_nonneg_left (hN N hN2) hr0
        _ ≤ 1 * (B * Real.exp (α * t)) :=
            mul_le_mul hr1 (mul_le_mul_of_nonneg_left hpow hB0) (by positivity) zero_le_one
        _ = B * Real.exp (α * t) := one_mul _
    nlinarith
  · have hexp : Real.exp t < 2 := by
      calc Real.exp t < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (lt_of_not_ge hlog)
        _ = 2 := Real.exp_log (by norm_num)
    have hsum : (∑ k ∈ Finset.Icc 0 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp t))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkR : (k : ℝ) ≤ Real.exp t :=
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ)).trans
          (Nat.floor_le (Real.exp_pos t).le)
      have hk2 : k < 2 := by exact_mod_cast hkR.trans_lt hexp
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp
    have hsource := UnitRieszRealAperture.resolvent_log_eq_prime_sum (Real.exp_pos t)
    rw [Real.log_exp, hsum, mul_zero, zero_sub] at hsource
    rw [hsource]
    nlinarith [Real.sqrt_nonneg (Real.exp t)]

/-- **One-sided upper power strip law for `mobiusDivisorSquareRootAbelMoment`.**
If `mobiusDivisorSquareRootAbelMoment M / M ≤ C + C M^c` for `M ≥ 2` (`C ≥ 0`), then every
`q : XiZeroCopy` satisfies `|(q.1 : ℂ).re - 1/2| ≤ max 0 c`. -/
theorem abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → mobiusDivisorSquareRootAbelMoment M / M ≤ C + C * (M : ℝ) ^ c)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  set α : ℝ := max 0 c
  have hα0 : 0 ≤ α := le_max_left 0 c
  have hcα : c ≤ α := le_max_right 0 c
  refine abs_re_sub_half_le_of_criticalResolvent_log_nat_le_rpow
    (B := 4 * C + 2 * (|2 * Real.eulerMascheroniConstant| + 1)) (by positivity) hα0
    (fun M hM2 => ?_) q
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hpow1 : 1 ≤ (M : ℝ) ^ α := Real.one_le_rpow hM1 hα0
  have hpowc : (M : ℝ) ^ c ≤ (M : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hM1 hcα
  have hres := resolvent_log_nat_le_mobiusDivisorSquareRootAbel hM2
  have hbound : 2 * (mobiusDivisorSquareRootAbelMoment M / M) ≤ 2 * (C + C * (M : ℝ) ^ c) :=
    mul_le_mul_of_nonneg_left (hM M hM2) (by norm_num)
  refine (hres.trans (add_le_add hbound le_rfl)).trans ?_
  nlinarith [abs_nonneg (2 * Real.eulerMascheroniConstant)]

/-- **One-sided subpower RH equivalence for `mobiusDivisorSquareRootAbelMoment`.**
Strengthens `riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower` from a two-sided norm bound
to a one-sided upper bound. -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_oneSided_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorSquareRootAbelMoment M / M ≤ C * (M : ℝ) ^ ε := by
  constructor
  · intro hRH ε hε
    obtain ⟨C, hC, hbound⟩ :=
      riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower.mp hRH ε hε
    exact ⟨C, hC, fun M hM => (le_abs_self _).trans (hbound M hM)⟩
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC0, hC⟩ := h ε hε
    have hq := abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow hC0
      (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0)) q
    rw [max_eq_right hε.le] at hq
    linarith [(abs_le.mp hq).2]

/-! ## Section 2: Exact endpoint monotonicity and one-sided lower variation of
`mobiusDivisorSquareRootAbelMoment` -/

/-- Exact telescoping of `Σ_{k ≤ d < n} (√(d+1) − √d) = √n − √k`. -/
theorem sum_Ico_sqrt_succ_sub {k n : ℕ} (hkn : k ≤ n) :
    ∑ d ∈ Finset.Ico k n, (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) =
      Real.sqrt n - Real.sqrt k :=
  Finset.sum_Ico_sub (fun d : ℕ => Real.sqrt d) hkn

/-- Exact decomposition of `mobiusDivisorSquareRootAbelMoment n − mobiusDivisorSquareRootAbelMoment k`
over any interval `1 ≤ k ≤ n`. -/
theorem mobiusDivisorSquareRootAbel_sub_eq {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k =
      ∑ d ∈ Finset.Ico k n,
        (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
          (psiRemainder d + 2 * Real.eulerMascheroniConstant) := by
  rw [← Finset.sum_Ico_sub mobiusDivisorSquareRootAbelMoment hkn]
  refine Finset.sum_congr rfl fun d hd => ?_
  exact mobiusDivisorSquareRootAbelMoment_succ_sub (le_trans hk (Finset.mem_Ico.mp hd).1)

/-- **Endpoint-only monotonicity sandwich for `mobiusDivisorSquareRootAbelMoment`.**
For any `1 ≤ k ≤ n`, the increment of `mobiusDivisorSquareRootAbelMoment` across `[k, n]` is
trapped between its left-endpoint and right-endpoint source values, up to the linear index drift
`n − k`. -/
theorem mobiusDivisorSquareRootAbel_sub_endpoint_sandwich {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (psiRemainder k + 2 * Real.eulerMascheroniConstant - ((n : ℝ) - k)) *
        (Real.sqrt n - Real.sqrt k) ≤
      mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k ∧
    mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k ≤
      (psiRemainder n + 2 * Real.eulerMascheroniConstant + ((n : ℝ) - k)) *
        (Real.sqrt n - Real.sqrt k) := by
  rw [mobiusDivisorSquareRootAbel_sub_eq hk hkn]
  have hw : ∀ d : ℕ, 0 ≤ Real.sqrt (d + 1 : ℕ) - Real.sqrt d := fun d =>
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ d))
  have hlow : ∀ d ∈ Finset.Ico k n,
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder k + 2 * Real.eulerMascheroniConstant - ((n : ℝ) - k)) ≤
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder d + 2 * Real.eulerMascheroniConstant) := by
    intro d hd
    obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
    apply mul_le_mul_of_nonneg_left _ (hw d)
    have hfall := psiRemainder_sub_ge hkd
    have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn.le
    linarith
  have hup : ∀ d ∈ Finset.Ico k n,
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder d + 2 * Real.eulerMascheroniConstant) ≤
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder n + 2 * Real.eulerMascheroniConstant + ((n : ℝ) - k)) := by
    intro d hd
    obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
    apply mul_le_mul_of_nonneg_left _ (hw d)
    have hfall := psiRemainder_sub_ge hdn.le
    have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
    linarith
  have h1 := Finset.sum_le_sum hlow
  have h2 := Finset.sum_le_sum hup
  rw [← Finset.sum_mul, sum_Ico_sqrt_succ_sub hkn] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- **Unconditional downward drift bound for `mobiusDivisorSquareRootAbelMoment`.**
Because `ψ(k) ≥ 0` and `γ ≥ 0`, `mobiusDivisorSquareRootAbelMoment` can decrease across `[k, n]`
by at most `n (√n − √k)`. -/
theorem mobiusDivisorSquareRootAbel_sub_ge_neg_mul {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    -((n : ℝ) * (Real.sqrt n - Real.sqrt k)) ≤
      mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k := by
  obtain ⟨hlow, _⟩ := mobiusDivisorSquareRootAbel_sub_endpoint_sandwich hk hkn
  have hψ0 : -(k : ℝ) ≤ psiRemainder k := by
    rw [psiRemainder, chebyshevPsi_eq_psi]
    linarith [psi_nat_nonneg k]
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    have := eulerMascheroniConstant_gt; linarith
  have hsnk : 0 ≤ Real.sqrt n - Real.sqrt k :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast hkn))
  have hfactor : -(n : ℝ) ≤ psiRemainder k + 2 * Real.eulerMascheroniConstant - ((n : ℝ) - k) := by
    linarith
  exact ( by
    have := mul_le_mul_of_nonneg_right hfactor hsnk
    linarith : -((n : ℝ) * (Real.sqrt n - Real.sqrt k)) ≤
      (psiRemainder k + 2 * Real.eulerMascheroniConstant - ((n : ℝ) - k)) *
        (Real.sqrt n - Real.sqrt k)).trans hlow

/-! ## Section 3: Power-gap transport and two-step fixed-point bootstrap for
`mobiusDivisorSquareRootAbelMoment` -/

/-- For `k ≤ n`, `(√n − √k) √n ≤ n − k`. -/
theorem sqrt_sub_sqrt_mul_sqrt_le {k n : ℕ} (hkn : k ≤ n) :
    (Real.sqrt n - Real.sqrt k) * Real.sqrt n ≤ (n : ℝ) - k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hskn : Real.sqrt k ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  have hkk : (k : ℝ) ≤ Real.sqrt k * Real.sqrt n := by
    calc (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hk0).symm
      _ ≤ Real.sqrt k * Real.sqrt n := mul_le_mul_of_nonneg_left hskn (Real.sqrt_nonneg _)
  have hnn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0
  nlinarith

/-- **Pointwise power-gap upper transport for `mobiusDivisorSquareRootAbelMoment`.**
If `1 ≤ k ≤ n`, `n − k ≤ K n^{1−δ}`, and `|ψ(d) − d| ≤ C d^β` for `1 ≤ d`, then
`mobiusDivisorSquareRootAbelMoment n / n ≤ max (mobiusDivisorSquareRootAbelMoment k / k) 0 +
K (C + 2) n^{β − 1/2 − δ}`. -/
theorem mobiusDivisorSquareRootAbel_div_le_of_sample {K δ C β : ℝ} {k n : ℕ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hgapn : (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β) :
    mobiusDivisorSquareRootAbelMoment n / n ≤
      max (mobiusDivisorSquareRootAbelMoment k / k) 0 +
        K * (C + 2) * (n : ℝ) ^ (β - 1 / 2 - δ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn1 : 1 ≤ n := le_trans hk hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsn : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hγ : 2 * Real.eulerMascheroniConstant ≤ 2 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hnb1 : (1 : ℝ) ≤ (n : ℝ) ^ β := Real.one_le_rpow hn1R hβ
  have hw : ∀ d : ℕ, 0 ≤ Real.sqrt (d + 1 : ℕ) - Real.sqrt d := fun d =>
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ d))
  have hterm : ∀ d ∈ Finset.Ico k n,
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) *
        (psiRemainder d + 2 * Real.eulerMascheroniConstant) ≤
      (Real.sqrt (d + 1 : ℕ) - Real.sqrt d) * ((C + 2) * (n : ℝ) ^ β) := by
    intro d hd
    obtain ⟨hkd, hdn⟩ := Finset.mem_Ico.mp hd
    apply mul_le_mul_of_nonneg_left _ (hw d)
    have hd1 : 1 ≤ d := le_trans hk hkd
    have hdψ : psiRemainder d ≤ C * (n : ℝ) ^ β := by
      rw [psiRemainder, chebyshevPsi_eq_psi]
      refine (le_abs_self _).trans ((hψ d hd1).trans (mul_le_mul_of_nonneg_left ?_ hC))
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdn.le) hβ
    nlinarith
  have hdiff : mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k ≤
      (Real.sqrt n - Real.sqrt k) * ((C + 2) * (n : ℝ) ^ β) := by
    rw [mobiusDivisorSquareRootAbel_sub_eq hk hkn]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, sum_Ico_sqrt_succ_sub hkn]
  set y : ℝ := (n : ℝ) ^ (β - 1 / 2 - δ) with hy
  have hkey : (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β = y * ((n : ℝ) * Real.sqrt n) := by
    rw [hy, hsn, ← Real.rpow_add hn0, show (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ ((1 : ℝ) + 1 / 2) by rw [Real.rpow_add hn0, Real.rpow_one],
      ← Real.rpow_add hn0]
    ring_nf
  have herr : (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n ≤
      K * (C + 2) * y := by
    rw [div_le_iff₀ hn0]
    have hmul := mul_le_mul_of_nonneg_right hdiff hsn0.le
    have hsq := sqrt_sub_sqrt_mul_sqrt_le hkn
    have hstep : (Real.sqrt n - Real.sqrt k) * ((C + 2) * (n : ℝ) ^ β) * Real.sqrt n ≤
        (K * (n : ℝ) ^ (1 - δ)) * ((C + 2) * (n : ℝ) ^ β) := by
      calc (Real.sqrt n - Real.sqrt k) * ((C + 2) * (n : ℝ) ^ β) * Real.sqrt n
          = ((Real.sqrt n - Real.sqrt k) * Real.sqrt n) * ((C + 2) * (n : ℝ) ^ β) := by ring
        _ ≤ (K * (n : ℝ) ^ (1 - δ)) * ((C + 2) * (n : ℝ) ^ β) :=
            mul_le_mul_of_nonneg_right (hsq.trans hgapn) (by positivity)
    have hstep2 : (K * (n : ℝ) ^ (1 - δ)) * ((C + 2) * (n : ℝ) ^ β) =
        (K * (C + 2) * y * n) * Real.sqrt n := by
      calc (K * (n : ℝ) ^ (1 - δ)) * ((C + 2) * (n : ℝ) ^ β)
          = K * (C + 2) * ((n : ℝ) ^ (1 - δ) * (n : ℝ) ^ β) := by ring
        _ = K * (C + 2) * (y * ((n : ℝ) * Real.sqrt n)) := by rw [hkey]
        _ = (K * (C + 2) * y * n) * Real.sqrt n := by ring
    exact le_of_mul_le_mul_right (hmul.trans (hstep.trans hstep2.le)) hsn0
  have hbase : mobiusDivisorSquareRootAbelMoment k / n ≤
      max (mobiusDivisorSquareRootAbelMoment k / k) 0 := by
    have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hr0 : 0 ≤ (k : ℝ) / n := by positivity
    have hr1 : (k : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hknR
    calc mobiusDivisorSquareRootAbelMoment k / n
        = ((k : ℝ) / n) * (mobiusDivisorSquareRootAbelMoment k / k) := by field_simp
      _ ≤ ((k : ℝ) / n) * max (mobiusDivisorSquareRootAbelMoment k / k) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hr0
      _ ≤ 1 * max (mobiusDivisorSquareRootAbelMoment k / k) 0 :=
          mul_le_mul_of_nonneg_right hr1 (le_max_right _ _)
      _ = max (mobiusDivisorSquareRootAbelMoment k / k) 0 := one_mul _
  have hsplit : mobiusDivisorSquareRootAbelMoment n / n =
      mobiusDivisorSquareRootAbelMoment k / n +
        (mobiusDivisorSquareRootAbelMoment n - mobiusDivisorSquareRootAbelMoment k) / n := by ring
  rw [hsplit]
  exact add_le_add hbase herr

/-- **One round of power-gap upper transport for `mobiusDivisorSquareRootAbelMoment`.** -/
theorem exists_mobiusDivisorSquareRootAbel_le_rpow_of_powerGaps {A : Set ℕ} {M c K δ C β : ℝ}
    {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hA : ∀ k ∈ A, 2 ≤ k → mobiusDivisorSquareRootAbelMoment k / k ≤ M + M * (k : ℝ) ^ c)
    (hψ : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C * (N : ℝ) ^ β)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ n : ℕ, 2 ≤ n →
      mobiusDivisorSquareRootAbelMoment n / n ≤
        M' + M' * (n : ℝ) ^ max (max c 0) (max (β - 1 / 2 - δ) 0) := by
  set a := max (max c 0) (max (β - 1 / 2 - δ) 0) with hadef
  have ha0 : 0 ≤ a := le_trans (le_max_right _ _) (le_max_right _ _)
  have hca : c ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have hba : β - 1 / 2 - δ ≤ a := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hlim.eventually (eventually_le_nhds
    (show (0 : ℝ) < 1 / 2 by norm_num)))
  set N₁ : ℕ := max N₀ (max N₂ 4)
  set S : ℝ := ∑ j ∈ Finset.range N₁, |mobiusDivisorSquareRootAbelMoment j / j|
  have hS0 : 0 ≤ S := by positivity
  set D : ℝ := 2 * M + K * (C + 2) + S
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD0, fun n hn2 => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hna1 : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hn1 ha0
  rcases le_or_gt N₁ n with hnN₁ | hnN₁
  · have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hnN₁
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN₁
    have hn4 : 4 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hnN₁
    obtain ⟨k, hkA, hkn, hgapn⟩ := hgap n hnN₀
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsplit : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
      rw [show (1 : ℝ) - δ = -δ + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
    have hhalf : K * (n : ℝ) ^ (1 - δ) ≤ n / 2 := by
      have := hN₂ n hnN₂; rw [hsplit, ← mul_assoc]; nlinarith
    have hk2 : 2 ≤ k := by
      have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
      have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      have : (2 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    have hstep := mobiusDivisorSquareRootAbel_div_le_of_sample hC hβ (by omega) hkn hgapn hψ
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hkc : (k : ℝ) ^ c ≤ (n : ℝ) ^ a := by
      calc (k : ℝ) ^ c ≤ (k : ℝ) ^ a := Real.rpow_le_rpow_of_exponent_le hk1 hca
        _ ≤ (n : ℝ) ^ a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) ha0
    have hnb : (n : ℝ) ^ (β - 1 / 2 - δ) ≤ (n : ℝ) ^ a :=
      Real.rpow_le_rpow_of_exponent_le hn1 hba
    have hAk : max (mobiusDivisorSquareRootAbelMoment k / k) 0 ≤ 2 * M * (n : ℝ) ^ a := by
      apply max_le
      · refine (hA k hkA hk2).trans ?_
        nlinarith
      · positivity
    have hKC : K * (C + 2) * (n : ℝ) ^ (β - 1 / 2 - δ) ≤ K * (C + 2) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left hnb (by positivity)
    refine (hstep.trans (add_le_add hAk hKC)).trans ?_
    dsimp [D]
    nlinarith
  · have hmem : n ∈ Finset.range N₁ := Finset.mem_range.mpr hnN₁
    have hleS : |mobiusDivisorSquareRootAbelMoment n / n| ≤ S :=
      Finset.single_le_sum (f := fun j : ℕ => |mobiusDivisorSquareRootAbelMoment j / j|)
        (fun j _ => abs_nonneg _) hmem
    refine ((le_abs_self _).trans hleS).trans ?_
    dsimp [D]
    nlinarith

/-- **Two-step supremum fixed-point bootstrap for `mobiusDivisorSquareRootAbelMoment`.**
If `A ⊆ ℕ` meets every window `[n − K n^{1−δ}, n]` for `n ≥ N₀` (`δ > 0`) and
`mobiusDivisorSquareRootAbelMoment k / k ≤ M + M k^c` on `A` (`M ≥ 0`), then every zero satisfies
`|Re ρ − 1/2| ≤ max 0 c`. -/
theorem abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA : ∀ k ∈ A, 2 ≤ k → mobiusDivisorSquareRootAbelMoment k / k ≤ M + M * (k : ℝ) ^ c)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hα0 : 0 ≤ α := le_trans (abs_nonneg _) (hαall q)
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q' : XiZeroCopy => (xiZeroCopy_re_lt_one q').le)
    rw [hαdef]; linarith
  by_cases hc : 1 / 2 ≤ max 0 c
  · exact (hαall q).trans (by linarith)
  push Not at hc
  -- Step 1 (Chebyshev β = 1): prove α < 1/2
  have hψ1 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ 6 * (N : ℝ) ^ (1 : ℝ) := by
    intro N _
    rw [Real.rpow_one]
    have h1 := psi_nat_le_six_mul N
    have h0 := psi_nat_nonneg N
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [abs_le]; constructor <;> linarith
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_mobiusDivisorSquareRootAbel_le_rpow_of_powerGaps hM0 hδ hK
    (by norm_num) (by norm_num) hA hψ1 hgap
  set a₁ := max (max c 0) (max ((1 : ℝ) - 1 / 2 - δ) 0) with ha₁
  have ha₁0 : 0 ≤ a₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₁ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + a₁ := fun q' => by
    have hq' := abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow hM₁0 hM₁ q'
    rw [max_eq_right ha₁0] at hq'
    linarith [(abs_le.mp hq').2]
  have hsup₁ := zeroReSup_le hg₁
  have hle₁ : α ≤ a₁ := by linarith
  have hαlt : α < 1 / 2 := by
    have hc1 : max c 0 < 1 / 2 := by rwa [max_comm]
    have hc2 : max ((1 : ℝ) - 1 / 2 - δ) 0 < 1 / 2 := max_lt (by linarith) (by norm_num)
    exact lt_of_le_of_lt hle₁ (max_lt hc1 hc2)
  -- Step 2 (Von Koch at e = α < 1/2): prove α ≤ max 0 c
  obtain ⟨C₂, hC₂0, hC₂⟩ := Sieve.exists_chebyshev_error_power_bound_of_xiZeroHalfPlaneBound
    hα0 hαlt hXi (show 0 < δ / 2 by positivity)
  have hψ2 : ∀ N : ℕ, 1 ≤ N → |Chebyshev.psi N - N| ≤ C₂ * (N : ℝ) ^ (1 / 2 + α + δ / 2) := by
    intro N hN
    rw [psi_natCast_eq_sum_Icc_one]
    exact hC₂ N hN
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_mobiusDivisorSquareRootAbel_le_rpow_of_powerGaps hM0 hδ hK
    hC₂0.le (by positivity) hA hψ2 hgap
  set a₂ := max (max c 0) (max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0) with ha₂
  have ha₂0 : 0 ≤ a₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hg₂ : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ 1 / 2 + a₂ := fun q' => by
    have hq' := abs_re_sub_half_le_of_mobiusDivisorSquareRootAbel_le_rpow hM₂0 hM₂ q'
    rw [max_eq_right ha₂0] at hq'
    linarith [(abs_le.mp hq').2]
  have hsup₂ := zeroReSup_le hg₂
  have hle₂ : α ≤ a₂ := by linarith
  have hαc : α ≤ max 0 c := by
    by_contra hlt
    push Not at hlt
    have hc1 : max c 0 < α := by rwa [max_comm]
    have hc2 : max (1 / 2 + α + δ / 2 - 1 / 2 - δ) 0 < α :=
      max_lt (by linarith) (lt_of_le_of_lt (le_max_left 0 c) hlt)
    have hc3 : a₂ < α := max_lt hc1 hc2
    linarith
  exact (hαall q).trans hαc

/-- **Power-gap upper sampling of `mobiusDivisorSquareRootAbelMoment` gives RH.** -/
theorem riemannHypothesis_of_powerGaps_mobiusDivisorSquareRootAbel_le
    {A : Set ℕ} {M K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ))
    (hA : ∀ k ∈ A, 2 ≤ k → mobiusDivisorSquareRootAbelMoment k / k ≤ M) : RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hA' : ∀ k ∈ A, 2 ≤ k →
      mobiusDivisorSquareRootAbelMoment k / k ≤ max M 0 + max M 0 * (k : ℝ) ^ (0 : ℝ) := by
    intro k hkA hk2
    rw [Real.rpow_zero, mul_one]
    exact (hA k hkA hk2).trans (by linarith [le_max_left M 0, le_max_right M 0])
  have h := abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (le_max_right M 0) hδ hK hA' hgap q
  rw [max_self] at h
  linarith [(abs_le.mp h).2]

/-- **RH ⟺ `mobiusDivisorSquareRootAbelMoment` is bounded above on a power-gap sampling set.** -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddAbove_of_powerGaps
    {A : Set ℕ} {K δ : ℝ} {N₀ : ℕ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k →
      mobiusDivisorSquareRootAbelMoment k / k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_powerGaps_mobiusDivisorSquareRootAbel_le hδ hK hgap hM

/-- **Every `m`-th power sequence (`m ≥ 1`) decides RH for `mobiusDivisorSquareRootAbelMoment`.**
Generalizes the `m = 4` theorem of `MobiusRieszQuarticSampling` to arbitrary `m ≥ 1`. -/
theorem riemannHypothesis_iff_mobiusDivisorSquareRootAbel_pow_bddAbove {m : ℕ} (hm : 1 ≤ m) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ j : ℕ, 2 ≤ j ^ m →
      mobiusDivisorSquareRootAbelMoment (j ^ m) / (j ^ m : ℕ) ≤ M := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap : ∀ n : ℕ, 1 ≤ n → ∃ k ∈ Set.range (fun j : ℕ => j ^ m), k ≤ n ∧
      (n : ℝ) - k ≤ (m * 2 ^ (m - 1) : ℝ) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hj, hgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hj, hgap⟩
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbel_bddAbove_of_powerGaps
    (by positivity) (by positivity) hgap]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun j hj => hM _ ⟨j, rfl⟩ hj⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k hk hk2 => ?_⟩
    obtain ⟨j, rfl⟩ := hk
    exact hM j hk2

/-- **Adaptive power-window criterion for `mobiusDivisorSquareRootAbelMoment`.**
RH holds iff for some `δ > 0` and level `M`, every power window `[n − n^{1−δ}, n]` contains a point
`k` where `mobiusDivisorSquareRootAbelMoment k / k ≤ M`. -/
theorem riemannHypothesis_iff_exists_powerWindow_mobiusDivisorSquareRootAbel_le :
    RiemannHypothesis ↔ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - k ≤ (n : ℝ) ^ (1 - δ) ∧
        mobiusDivisorSquareRootAbelMoment k / k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_mobiusDivisorSquareRootAbel_boundedAbove.mp h
    refine ⟨1 / 2, by norm_num, M, 2, fun n hn => ⟨n, hn, le_rfl, ?_, hM n hn⟩⟩
    rw [sub_self]; positivity
  · rintro ⟨δ, hδ, M, N₀, h⟩
    refine riemannHypothesis_of_powerGaps_mobiusDivisorSquareRootAbel_le
      (A := {k | 2 ≤ k ∧ mobiusDivisorSquareRootAbelMoment k / k ≤ M})
      (M := M) (K := 1) (N₀ := N₀) hδ zero_le_one (fun n hn => ?_) (fun k hk _ => hk.2)
    obtain ⟨k, hk2, hkn, hgap, hk⟩ := h n hn
    exact ⟨k, ⟨hk2, hk⟩, hkn, by rw [one_mul]; exact hgap⟩

end
end RHTower
