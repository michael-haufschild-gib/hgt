import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeEnergyAtTheAbscissaPaysTheResidues

/-!
# The Mertens energy pays its critical residues

The Abel escape calculus (`TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol`) applies to every
row. For the Mertens row `M(n) = Σ_{k ≤ n} μ(k)` it yields an unconditional mean-square law with
the residues of `1/ζ` at the critical zeros as constant.

* **Rows** (`integrable_and_memLp_dampedProfile_logProfile`, `lineSymbol_logProfile_eq`). For any
  row with `v(0) = 0` and pronic energy `O((T+1)^κ)`, the damped log profile is `L¹ ∩ L²` for
  `c > κ/2`, with symbol `Φ_v(s)/s`, `s = c + ½ + iy`.
* **The Mertens symbol** (`complexMellinPairing_mertensRow`,
  `riemannZeta_mul_complexMellinPairing_mertensRow`). `Φ_M = L(μ, ·)` on `Re s > 1`; under
  energy `O((T+1)^κ)`, `ζ(s) Φ_M(s) = 1` on `Re s > (1+κ)/2`, `s ≠ 1`.
* **Poles** (`exists_inv_zeta_pole_bound`). At a simple zero `ρ`,
  `1/(sζ(s)) = r_ρ/(s − ρ) + O(1)`, `r_ρ = 1/(ρ ζ′(ρ))`.
* **The capacity of atoms** (`eventually_le_mul_integral_of_atoms`), for any family of line
  symbols with finitely many separated atoms.
* **Residue mass ≤ log-slope** (`sum_residue_le_slope`). For any row with `v(0) = 0`,
  `|v(n)| ≤ K n²` and log-energy `∫_0^L g_v² ≤ S L + B`, simple poles `r_ρ/(e + i(y − Im ρ))` of its
  line symbols at separated critical heights satisfy `Σ_ρ ‖r_ρ‖² ≤ S` (capacity against the
  Abelian bound).
* **The Mertens law** (`not_forall_mertens_energy_le_linear`,
  `not_forall_mertens_pronicEnergy_le_log`). For every finite set `Z` of simple critical zeros and
  every `S < Σ_{ρ ∈ Z} ‖1/(ρ ζ′(ρ))‖²`, neither
  `∫_0^L e^{−u} M(⌊e^u⌋)² du = ∫_1^{e^L} M(⌊x⌋)²/x² dx ≤ S L + B` for all `L`, nor
  `Σ_{n ≤ T} M(n)²/(n(n+1)) ≤ S log(T+1) + B` for all `T`.

So `limsup_{X→∞} (log X)⁻¹ ∫_1^X M(x)²/x² dx ≥ Σ_ρ ‖1/(ρ ζ′(ρ))‖²` over the simple zeros on the
critical line, without any hypothesis: a linear log-energy bound forces `ζ ≠ 0` on `Re s > ½`
(continuation of `Φ_M`), so all critical simple zeros are dominant, and each carries the Abel atom
`π ‖r_ρ‖²` that the Abelian bound charges to the slope.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)
open ArithmeticFunction (moebius)

/-! ### Step profiles of rows -/

/-- The damped log profile of a row is the real step integrand at `s = c + ½`. -/
theorem ofReal_dampedProfile_logProfile (f : ℕ → ℝ) (c u : ℝ) :
    ((dampedProfile (logProfile f) c u : ℝ) : ℂ) =
      stepLaplaceIntegrand f (((c + 1 / 2 : ℝ)) : ℂ) u := by
  rw [dampedProfile, logProfile, stepLaplaceIntegrand, ← mul_assoc, ← Real.exp_add]
  push_cast
  rw [show -((c : ℂ) * (u : ℂ)) + -((u : ℂ) / 2) = -((c : ℂ) + 1 / 2) * (u : ℂ) by ring]

/-- **Energy integrates the damped profile of a row.** Pronic energy `O((T+1)^κ)` puts
`e^{−cu} g_f(u)` in `L¹ ∩ L²` for every `c > κ/2`. -/
theorem integrable_and_memLp_dampedProfile_logProfile {f : ℕ → ℝ} (hA0 : f 0 = 0) {C κ c : ℝ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ) (hc : κ / 2 < c) :
    Integrable (dampedProfile (logProfile f) c) ∧ MemLp (dampedProfile (logProfile f) c) 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hmeas : Measurable (dampedProfile (logProfile f) c) := by
    unfold dampedProfile logProfile
    refine (by fun_prop : Measurable fun u : ℝ => Real.exp (-(c * u))).mul
      ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(u / 2))).mul ?_)
    exact (measurable_from_nat (f := f)).comp Real.measurable_exp.nat_floor
  -- `L¹`
  have hsum1 : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-((c + 1 / 2 : ℝ) : ℂ).re - 1) := by
    simpa using ArithmeticCorrelationGeometry.summable_abs_mul_rpow_of_energy_growth hA0 hC hκ
      (b := c + 1 / 2) (by linarith) hEA
  have hI := integrable_stepLaplaceIntegrand hA0 (s := ((c + 1 / 2 : ℝ) : ℂ)) (by simp; linarith)
    hsum1
  refine ⟨?_, ?_⟩
  · refine hI.norm.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [← ofReal_dampedProfile_logProfile, Complex.norm_real]
  -- `L²`: the square is the step integrand of `A²` at `2c + 1`
  · rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
    have hsq0 : (fun n => f n ^ 2) 0 = 0 := by simp [hA0]
    have hsum2 : Summable fun n : ℕ =>
        |f n ^ 2| * (n : ℝ) ^ (-((2 * c + 1 : ℝ) : ℂ).re - 1) := by
      have h1 := ArithmeticCorrelationGeometry.summable_mul_rpow_neg_of_partialSum_le
        (e := fun n => f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) (fun n => by positivity)
        (by simp [hA0]) hC hκ (γ := 2 * c) (by linarith) hEA
      refine (h1.mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
      simp only [Complex.ofReal_re]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hA0]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_nonneg (sq_nonneg _), show -(2 * c + 1) - 1 = -(2 * c) - 2 by ring,
        Real.rpow_sub hn0, Real.rpow_two]
      have hle : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have : ((n : ℝ) ^ 2)⁻¹ ≤ 2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        calc ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) * ((n : ℝ) + 1)) ≤
            ((n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ) ^ 2) := by gcongr
          _ = 2 := by field_simp
      calc f n ^ 2 * ((n : ℝ) ^ (-(2 * c)) * ((n : ℝ) ^ 2)⁻¹)
          ≤ f n ^ 2 * ((n : ℝ) ^ (-(2 * c)) * (2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹)) := by
            gcongr
        _ = 2 * (f n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1))⁻¹ * (n : ℝ) ^ (-(2 * c))) := by ring
    have hI2 := integrable_stepLaplaceIntegrand hsq0 (s := ((2 * c + 1 : ℝ) : ℂ))
      (by simp; linarith) hsum2
    refine hI2.norm.congr (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [norm_stepLaplaceIntegrand, Complex.ofReal_re, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, sq_abs, dampedProfile, logProfile, mul_pow, mul_pow,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    push_cast
    ring

/-- The line symbol of the log profile of a row with energy `O((T+1)^κ)` is its Mellin pairing
over `s`: `G(c + iy) = Φ_f(s)/s`, `s = c + ½ + iy`, for `c > κ/2`. -/
theorem lineSymbol_logProfile_eq {f : ℕ → ℝ} (hA0 : f 0 = 0) {C κ c : ℝ} (hC : 0 ≤ C)
    (hκ : 0 ≤ κ)
    (hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ) (hc : κ / 2 < c) (y : ℝ) :
    lineSymbol (logProfile f) c y =
      complexMellinPairing f (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        (((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
  set s : ℂ := ((c + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hs
  have hsre : s.re = c + 1 / 2 := by simp [hs]
  have hsum : Summable fun n : ℕ => |f n| * (n : ℝ) ^ (-s.re - 1) := by
    rw [hsre]
    exact ArithmeticCorrelationGeometry.summable_abs_mul_rpow_of_energy_growth hA0 hC hκ
      (by linarith) hEA
  rw [← integral_stepLaplaceIntegrand hA0 (by rw [hsre]; linarith) hsum, lineSymbol,
    _root_.RHTower.laplaceBoundary]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [ofReal_dampedProfile_logProfile, stepLaplaceIntegrand, stepLaplaceIntegrand, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  rw [hs]
  ring


/-! ### The Mertens symbol -/

/-- The Mertens row `M(n) = Σ_{k ≤ n} μ(k)`. -/
def mertensRow (n : ℕ) : ℝ := prefixSum (fun k => (moebius k : ℝ)) n

theorem mertensRow_zero : mertensRow 0 = 0 := prefixSum_zero _

theorem abs_mertensRow_le (n : ℕ) : |mertensRow n| ≤ n := by
  unfold mertensRow prefixSum
  calc |∑ m ∈ Finset.Icc 1 n, (moebius m : ℝ)| ≤ ∑ m ∈ Finset.Icc 1 n, |(moebius m : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun m _ => by
        have := ArithmeticFunction.abs_moebius_le_one (n := m)
        exact_mod_cast this
    _ = n := by simp

theorem abs_mertensRow_le_sq (n : ℕ) : |mertensRow n| ≤ 1 * (n : ℝ) ^ 2 := by
  rw [one_mul]
  refine (abs_mertensRow_le n).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

/-- **The Mertens pairing is `1/ζ` on `Re s > 1`**: `Σ_n M(n)(n^{−s} − (n+1)^{−s}) = L(μ, s)`. -/
theorem complexMellinPairing_mertensRow {s : ℂ} (hs : 1 < s.re) :
    complexMellinPairing mertensRow s = LSeries (fun n => (moebius n : ℂ)) s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsum : Summable fun n : ℕ => |mertensRow n| * (n : ℝ) ^ (-s.re - 1) := by
    refine (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [mertensRow_zero, abs_zero, zero_mul]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc |mertensRow n| * (n : ℝ) ^ (-s.re - 1) ≤ n * (n : ℝ) ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right (abs_mertensRow_le n) (by positivity)
      _ = (n : ℝ) ^ (-s.re) := by
          rw [Real.rpow_sub hn0, Real.rpow_one]; field_simp
  have hval := integral_stepLaplaceIntegrand mertensRow_zero (by linarith) hsum
  have hint := integrable_stepLaplaceIntegrand mertensRow_zero (by linarith) hsum
  -- the horizon integrals converge to the full integral
  have hIci : ∫ u, stepLaplaceIntegrand mertensRow s u =
      ∫ u in Ioi (0 : ℝ), stepLaplaceIntegrand mertensRow s u := by
    rw [← integral_Ici_eq_integral_Ioi]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Ici, not_le] at hu
    exact stepLaplaceIntegrand_of_neg mertensRow_zero s hu
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 0 hint.integrableOn hlog
  rw [← hIci, hval] at hlim1
  -- the horizon integrals are partial Dirichlet sums plus a vanishing boundary
  have hrw : ∀ N : ℕ, ∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1), stepLaplaceIntegrand mertensRow s u =
      (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℝ) : ℂ) * (n : ℂ) ^ (-s) -
        (mertensRow N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) / s := by
    intro N
    simp only [mertensRow]
    rw [← integral_prefix_exp_eq (fun k => (moebius k : ℝ)) hs0 N]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [stepLaplaceIntegrand, mertensRow]
    ring
  simp_rw [hrw] at hlim1
  have hL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((moebius n : ℝ) : ℂ) * (n : ℂ) ^ (-s))
      atTop (𝓝 (LSeries (fun n => (moebius n : ℂ)) s)) := by
    have hS : LSeriesSummable (fun n => (moebius n : ℂ)) s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
    have h := hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun N => ?_
    simp only [Function.comp]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      Finset.sum_range_succ', LSeries.term_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (by omega), add_comm 1 n, Complex.cpow_neg, div_eq_mul_inv]
    push_cast
    ring
  have hB : Tendsto (fun N : ℕ => (mertensRow N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_rpow_neg_atTop (show 0 < s.re - 1 by
      linarith) |>.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos
      (Nat.succ_pos N)]
    simp only [Function.comp, neg_re]
    rw [Nat.cast_succ]
    have h1 : |mertensRow N| ≤ (N : ℝ) + 1 := (abs_mertensRow_le N).trans (by linarith)
    calc |mertensRow N| * ((N : ℝ) + 1) ^ (-s.re) ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((N : ℝ) + 1) ^ (-(s.re - 1)) := by
          rw [show -(s.re - 1) = -s.re + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]
          ring
  have hlim2 := (hL.sub hB).div_const s
  rw [sub_zero] at hlim2
  have := tendsto_nhds_unique hlim1 hlim2
  field_simp at this
  exact this


/-- **Continuation of the Mertens pairing.** If the Mertens energy is `O((T+1)^κ)`, then on
`Re s > (1+κ)/2`, `s ≠ 1`, `ζ(s) Φ_M(s) = 1`: in particular `ζ` has no zero there. -/
theorem riemannZeta_mul_complexMellinPairing_mertensRow {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hE : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ) {s : ℂ} (hs : (1 + κ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * complexMellinPairing mertensRow s = 1 := by
  have hΦ := ArithmeticCorrelationGeometry.differentiableOn_complexMellinPairing_of_energy_growth
    mertensRow_zero hC hκ hE
  set U : Set ℂ := {s : ℂ | (1 + κ) / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt ((1 + κ) / 2)).isPreconnected
  set H : ℂ → ℂ := fun s => _root_.RHTower.zetaResidueUnit s * complexMellinPairing mertensRow s -
    (s - 1) with hH
  have hR : DifferentiableOn ℂ _root_.RHTower.zetaResidueUnit U := fun s _ =>
    (_root_.RHTower.analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt
  have hHd : DifferentiableOn ℂ H U := (hR.mul hΦ).sub (differentiableOn_id.sub_const _)
  set x₀ : ℂ := (((1 + κ) / 2 + 2 : ℝ) : ℂ) with hx₀
  have h2U : x₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hx₀, Complex.ofReal_re]; linarith
  -- `H` vanishes on `Re s > 1`
  have hzero : H =ᶠ[𝓝 x₀] 0 := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        simp only [Set.mem_setOf_eq, hx₀, Complex.ofReal_re]; linarith)
    filter_upwards [hopen] with s hs'
    have hs1' : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
    simp only [hH, Pi.zero_apply]
    rw [ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hs1', complexMellinPairing_mertensRow hs',
      mul_assoc, ← LSeries_one_eq_riemannZeta hs', LSeries_one_mul_Lseries_moebius hs', mul_one,
      sub_self]
  have hEq := (hHd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h2U hzero
  have hval := hEq (show s ∈ U from hs)
  simp only [hH, Pi.zero_apply] at hval
  rw [ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hs1, sub_eq_zero, mul_assoc] at hval
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have := mul_left_cancel₀ hne (hval.trans (mul_one _).symm)
  exact this

/-- **`1/(sζ(s))` has a simple pole at a simple zero.** Near a simple zero `ρ ∉ {0, 1}`,
`1/(sζ(s)) = r/(s − ρ) + O(1)`, `r = 1/(ρ ζ′(ρ))`. -/
theorem exists_inv_zeta_pole_bound {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hd : deriv riemannZeta ρ ≠ 0) (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) :
    ∃ η > 0, ∃ M : ℝ, ∀ s : ℂ, ‖s - ρ‖ < η → s ≠ ρ →
      riemannZeta s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 0 ∧
      ‖1 / (s * riemannZeta s) - 1 / (ρ * deriv riemannZeta ρ) / (s - ρ)‖ ≤ M := by
  have hZd : DifferentiableAt ℂ riemannZeta ρ := differentiableAt_riemannZeta hρ1
  set Z₁ := dslope riemannZeta ρ with hZ₁
  have hZ₁ρ : Z₁ ρ = deriv riemannZeta ρ := by rw [hZ₁, dslope_same]
  have hfac : ∀ s, riemannZeta s = (s - ρ) * Z₁ s := fun s => by
    have := sub_smul_dslope riemannZeta ρ s
    rw [hρ, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hS : {s : ℂ | s ≠ 1} ∈ 𝓝 ρ := isOpen_ne.mem_nhds hρ1
  have hZ₁d : DifferentiableAt ℂ Z₁ ρ :=
    ((Complex.differentiableOn_dslope hS).mpr fun s hs =>
      (differentiableAt_riemannZeta hs).differentiableWithinAt).differentiableAt hS
  set F : ℂ → ℂ := fun s => 1 / s / Z₁ s with hF
  have hFd : DifferentiableAt ℂ F ρ :=
    ((differentiableAt_const _).div differentiableAt_id hρ0).div hZ₁d (by rw [hZ₁ρ]; exact hd)
  have hKc : ContinuousAt (dslope F ρ) ρ := continuousAt_dslope_same.mpr hFd
  have hev : ∀ᶠ s in 𝓝 ρ, dist (dslope F ρ s) (dslope F ρ ρ) < 1 ∧ Z₁ s ≠ 0 ∧ s ≠ 1 ∧ s ≠ 0 :=
    (Metric.tendsto_nhds.mp hKc 1 one_pos).and ((hZ₁d.continuousAt.eventually_ne
      (by rw [hZ₁ρ]; exact hd)).and (Filter.Eventually.and hS (eventually_ne_nhds hρ0)))
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η, hη, ‖dslope F ρ ρ‖ + 1, fun s hs hne => ?_⟩
  obtain ⟨hK1, hZ₁ne, hs1, hs0⟩ := hball (by rwa [dist_eq_norm])
  have hss : s - ρ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨by rw [hfac]; exact mul_ne_zero hss hZ₁ne, hs1, hs0, ?_⟩
  have hval : 1 / (s * riemannZeta s) - 1 / (ρ * deriv riemannZeta ρ) / (s - ρ) =
      dslope F ρ s := by
    rw [dslope_of_ne _ hne, slope_def_field, hF]
    simp only
    rw [hZ₁ρ, hfac s]
    field_simp
  rw [hval]
  have := norm_sub_norm_le (dslope F ρ s) (dslope F ρ ρ)
  rw [dist_eq_norm] at hK1
  linarith



/-! ### The capacity of finitely many atoms -/

/-- **The capacity of atoms.** If the windows of a finite set of separated heights carry, in the
`e`-scaled limit, the atoms `π ‖r_ρ‖²`, then eventually the total scaled mass exceeds every
`M < π Σ_ρ ‖r_ρ‖²`. -/
theorem eventually_le_mul_integral_of_atoms {S : ℝ → ℝ → ℂ} (Z : Finset ℂ) (r : ℂ → ℂ)
    (δ₀ : ℂ → ℝ) (hδ₀ : ∀ ρ ∈ Z, 0 < δ₀ ρ)
    (hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im)
    (hT : ∀ ρ ∈ Z, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ ρ →
      Tendsto (fun e : ℝ => e * ∫ y in (ρ.im - δ)..(ρ.im + δ), ‖S e y‖ ^ 2) (𝓝[>] 0)
        (𝓝 (Real.pi * ‖r ρ‖ ^ 2)))
    (hint : ∀ e : ℝ, 0 < e → Integrable (fun y => ‖S e y‖ ^ 2)) {M : ℝ}
    (hM : M < Real.pi * ∑ ρ ∈ Z, ‖r ρ‖ ^ 2) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), M ≤ e * ∫ y, ‖S e y‖ ^ 2 := by
  have hevδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ (∀ ρ ∈ Z, δ ≤ δ₀ ρ) ∧
      ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * δ < |ρ.im - ρ'.im| := by
    refine eventually_mem_nhdsWithin.and (Filter.Eventually.and ?_ ?_)
    · refine (eventually_all_finset Z).mpr fun ρ hρ => ?_
      exact ((gt_mem_nhds (hδ₀ ρ hρ)).filter_mono nhdsWithin_le_nhds).mono fun δ h => h.le
    · refine (eventually_all_finset Z).mpr fun ρ hρ => (eventually_all_finset Z).mpr fun ρ' hρ' => ?_
      by_cases hne : ρ = ρ'
      · exact Eventually.of_forall fun δ h => absurd hne h
      · have hpos : 0 < |ρ.im - ρ'.im| := abs_pos.mpr (sub_ne_zero.mpr (hsep ρ hρ ρ' hρ' hne))
        exact ((gt_mem_nhds (show (0 : ℝ) < |ρ.im - ρ'.im| / 2 by linarith)).filter_mono
          nhdsWithin_le_nhds).mono fun δ h _ => by linarith
  obtain ⟨δ, hδ0, hδle, hgap⟩ := hevδ.exists
  have hdisj : (Z : Set ℂ).Pairwise
      (Function.onFun Disjoint fun ρ : ℂ => Icc (ρ.im - δ) (ρ.im + δ)) := by
    intro ρ hρ ρ' hρ' hne
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hlt := hgap ρ hρ ρ' hρ' hne
    have hle : |ρ.im - ρ'.im| ≤ 2 * δ :=
      abs_le.mpr ⟨by linarith [hy.1, hy.2, hy'.1, hy'.2], by linarith [hy.1, hy.2, hy'.1, hy'.2]⟩
    linarith
  have hsum : Tendsto (fun e : ℝ => ∑ ρ ∈ Z, e * ∫ y in (ρ.im - δ)..(ρ.im + δ), ‖S e y‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∑ ρ ∈ Z, Real.pi * ‖r ρ‖ ^ 2)) :=
    tendsto_finsetSum Z fun ρ hρ => hT ρ hρ δ hδ0 (hδle ρ hρ)
  rw [← Finset.mul_sum] at hsum
  filter_upwards [hsum.eventually (le_mem_nhds hM), self_mem_nhdsWithin] with e he he0
  have he0' : (0 : ℝ) < e := he0
  refine he.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ he0'.le
  have hunion : (∫ y in ⋃ ρ ∈ Z, Icc (ρ.im - δ) (ρ.im + δ), ‖S e y‖ ^ 2) =
      ∑ ρ ∈ Z, ∫ y in (ρ.im - δ)..(ρ.im + δ), ‖S e y‖ ^ 2 := by
    rw [integral_biUnion_finset Z (fun _ _ => measurableSet_Icc) hdisj
      (fun _ _ => (hint e he0').integrableOn)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [← hunion]
  exact setIntegral_le_integral (hint e he0') (Eventually.of_forall fun y => by positivity)

/-! ### The log-scale energy of a row -/

/-- The pronic energy of a row is the square mass of its log profile up to the horizon. -/
theorem pronic_energy_eq_log_integral (v : ℕ → ℝ) (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile v u ^ 2 := by
  have h := pronicPairing_rowDilate_eq_translationGram v (j := 1) (k := 1) le_rfl le_rfl T
  simpa only [ArithmeticContinuationAndCriticalEnergy.pronicPairing,
    ArithmeticContinuationAndCriticalEnergy.rowDilate, Nat.div_one, Nat.cast_one,
    Real.sqrt_one, mul_one, inv_one, one_mul, Real.log_one, sub_zero, pow_two] using h

theorem measurable_logProfile (v : ℕ → ℝ) : Measurable (logProfile v) :=
  (by fun_prop : Measurable fun u : ℝ => Real.exp (-(u / 2))).mul
    ((measurable_from_nat (f := v)).comp Real.measurable_exp.nat_floor)

/-- A row with `|v(n)| ≤ K n²` has `g_v(u)² ≤ K² e^{3u}`. -/
theorem logProfile_sq_le {v : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hv : ∀ n, |v n| ≤ K * n ^ 2)
    (u : ℝ) : logProfile v u ^ 2 ≤ K ^ 2 * Real.exp (3 * u) := by
  have hfl : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hM : |v ⌊Real.exp u⌋₊| ≤ K * Real.exp u ^ 2 := (hv _).trans (by gcongr)
  rw [logProfile, mul_pow, ← Real.exp_nat_mul, ← sq_abs (v _)]
  calc Real.exp (((2 : ℕ) : ℝ) * -(u / 2)) * |v ⌊Real.exp u⌋₊| ^ 2
      ≤ Real.exp (((2 : ℕ) : ℝ) * -(u / 2)) * (K * Real.exp u ^ 2) ^ 2 := by gcongr
    _ = K ^ 2 * Real.exp (3 * u) := by
        rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
        rw [show K ^ 2 * Real.exp (3 * u) = K ^ 2 * Real.exp (((2 : ℕ) : ℝ) * -(u / 2) +
          ((2 * 2 : ℕ) : ℝ) * u) by congr 2; push_cast; ring, Real.exp_add]
        ring

theorem integrableOn_logProfile_sq {v : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ n, |v n| ≤ K * n ^ 2) (L : ℝ) :
    IntegrableOn (fun u => logProfile v u ^ 2) (Ioo 0 L) := by
  refine Measure.integrableOn_of_bounded (M := K ^ 2 * Real.exp (3 * L)) (by simp)
    ((measurable_logProfile v).pow_const 2).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (logProfile_sq_le hK hv u).trans (by gcongr; exact hu.2.le)

/-- A linear log-energy `∫_0^L g_v² ≤ S L + B` keeps the pronic energy below every power. -/
theorem pronic_energy_le_of_linear {v : ℕ → ℝ} {S B : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + B)
    {κ : ℝ} (hκ : 0 < κ) (T : ℕ) :
    ∑ n ∈ Finset.Icc 1 T, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (S / κ + B) * ((T : ℝ) + 1) ^ κ := by
  have hT1 : (1 : ℝ) ≤ (T : ℝ) + 1 := by linarith [T.cast_nonneg (α := ℝ)]
  have hpow : 1 ≤ ((T : ℝ) + 1) ^ κ := Real.one_le_rpow hT1 hκ.le
  have hlog := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ (T : ℝ) + 1) hκ
  rw [pronic_energy_eq_log_integral]
  calc ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile v u ^ 2
      ≤ S * Real.log ((T : ℝ) + 1) + B := hlin _ (Real.log_nonneg hT1)
    _ ≤ S * (((T : ℝ) + 1) ^ κ / κ) + B * ((T : ℝ) + 1) ^ κ := by
        gcongr
        exact le_mul_of_one_le_right hB hpow
    _ = (S / κ + B) * ((T : ℝ) + 1) ^ κ := by ring

/-- **The Abelian line bound.** A log-energy `∫_0^L g² ≤ S L + B` bounds the mean square of the
line symbol: `e ∫ ‖G(e + iy)‖² dy ≤ π S + 2π e B` for every `e > 0`. -/
theorem mul_integral_norm_sq_lineSymbol_le_of_linear {v : ℕ → ℝ} (hv0 : v 0 = 0) {K : ℝ}
    (hK : 0 ≤ K) (hv : ∀ n, |v n| ≤ K * n ^ 2) {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + B) {e : ℝ}
    (he : 0 < e) :
    e * ∫ y, ‖lineSymbol (logProfile v) e y‖ ^ 2 ≤ Real.pi * S + 2 * Real.pi * e * B := by
  set g := logProfile v with hg
  have hdata : Integrable (dampedProfile g e) ∧ MemLp (dampedProfile g e) 2 :=
    integrable_and_memLp_dampedProfile_logProfile hv0 (add_nonneg (div_nonneg hS0 he.le) hB0)
      he.le (fun T => pronic_energy_le_of_linear hS0 hB0 hlin he T) (by linarith)
  have hH : ∀ L, 0 < L → ∫⁻ u in Ioo 0 L, ENNReal.ofReal (g u ^ 2) ≤
      ENNReal.ofReal (S * L + B) := by
    intro L hL
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_logProfile_sq hK hv L)
      (Eventually.of_forall fun u => sq_nonneg _), ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL.le]
    exact ENNReal.ofReal_le_ofReal (hlin L hL.le)
  have hAbel : abelGram g e 0 0 ≤ S / (2 * e) + B := by
    have hsq : Integrable (fun u => dampedProfile g e u ^ 2) := hdata.2.integrable_sq
    have hA : abelGram g e 0 0 = ∫ u, dampedProfile g e u ^ 2 := by
      rw [abelGram_eq_integral_dampedProfile]
      simp only [add_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero, sq]
    have hneg : ∀ u : ℝ, u < 0 → g u = 0 := fun u hu => by
      rw [hg, logProfile, floor_exp_eq_zero_of_neg hu, hv0, mul_zero]
    have hlint : ENNReal.ofReal (abelGram g e 0 0) =
        ∫⁻ u in Ioi 0, ENNReal.ofReal (Real.exp (-(2 * e * u))) * ENNReal.ofReal (g u ^ 2) := by
      rw [hA, ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun u => sq_nonneg _),
        setLIntegral_congr Ioi_ae_eq_Ici, ← lintegral_indicator measurableSet_Ici]
      refine lintegral_congr fun u => ?_
      by_cases hu : 0 ≤ u
      · rw [indicator_of_mem (mem_Ici.mpr hu), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          dampedProfile, mul_pow, ← Real.exp_nat_mul]
        congr 3
        push_cast
        ring
      · rw [indicator_of_notMem (by simpa using hu), dampedProfile, hneg u (not_le.mp hu)]
        simp
    have hb := lintegral_exp_mul_le_of_horizon (f := fun u => g u ^ 2)
      (Φ := fun L => S * L + B) ((measurable_logProfile v).pow_const 2) (by fun_prop)
      (show 0 < 2 * e by linarith) hH
    have hfin : ENNReal.ofReal (abelGram g e 0 0) ≤ ENNReal.ofReal (S / (2 * e) + B) :=
      hlint ▸ hb.trans (lintegral_Ioi_exp_linear (by linarith) hS0 hB0).le
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfin
  rw [integral_norm_sq_lineSymbol hdata.1 hdata.2]
  calc e * (2 * Real.pi * abelGram g e 0 0) ≤ e * (2 * Real.pi * (S / (2 * e) + B)) := by
        gcongr
    _ = Real.pi * S + 2 * Real.pi * e * B := by field_simp

/-- **Abel capacity under a budget.** If a row has a linear log-energy and its line symbol has
window poles with residues `r ρ` at finitely many separated heights, then
`e ∫ ‖G(e + iy)‖² dy` eventually exceeds every `M < π Σ_ρ ‖r ρ‖²`. -/
theorem eventually_le_mul_integral_lineSymbol_of_poles {v : ℕ → ℝ} (hv0 : v 0 = 0) {S B : ℝ}
    (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + B)
    (Z : Finset ℂ) (hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im) (r : ℂ → ℂ)
    (hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile v) e y - r ρ / ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M)
    {M : ℝ} (hM : M < Real.pi * ∑ ρ ∈ Z, ‖r ρ‖ ^ 2) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), M ≤ e * ∫ y, ‖lineSymbol (logProfile v) e y‖ ^ 2 := by
  set g := logProfile v with hg
  have hC : ∀ κ : ℝ, 0 < κ → 0 ≤ S / κ + B := fun κ hκ => add_nonneg (div_nonneg hS0 hκ.le) hB0
  have hdata : ∀ e : ℝ, 0 < e → Integrable (dampedProfile g e) ∧ MemLp (dampedProfile g e) 2 :=
    fun e he => integrable_and_memLp_dampedProfile_logProfile hv0 (hC e he) he.le
      (fun T => pronic_energy_le_of_linear hS0 hB0 hlin he T) (by linarith)
  choose! δ₀ hδ₀ Mρ hMρ using hpole
  have hT : ∀ ρ ∈ Z, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ ρ →
      Tendsto (fun e : ℝ => e * ∫ y in (ρ.im - δ)..(ρ.im + δ), ‖lineSymbol g e y‖ ^ 2)
        (𝓝[>] 0) (𝓝 (Real.pi * ‖r ρ‖ ^ 2)) := by
    intro ρ hρ δ hδ hδδ
    have h := tendsto_window_atom (S := fun e y => lineSymbol g e y) (y₀ := ρ.im) (δ := δ)
      (M := |Mρ ρ|) (L := 0) (W := 1) (r := r ρ) (w := fun _ => 1)
      hδ (abs_nonneg _) le_rfl
      (fun e he => (continuous_lineSymbol (hdata e he.1).1).continuousOn)
      (fun e he y hy => (hMρ ρ hρ e ⟨he.1, he.2.trans_le hδδ⟩ y
        ⟨by linarith [hy.1], by linarith [hy.2]⟩).trans (le_abs_self _))
      continuous_const (fun y => by simp) (fun y => by simp)
    simpa only [mul_one] using h
  exact eventually_le_mul_integral_of_atoms (S := fun e y => lineSymbol g e y) Z
    r δ₀ hδ₀ hsep hT
    (fun e he => _root_.RHTower.integrable_norm_sq_laplaceBoundary (hdata e he).1.ofReal
      (hdata e he).2.ofReal) hM

/-- **The residue mass is at most the log-slope.** Let a row with `v(0) = 0` and `|v(n)| ≤ K n²`
have linear log-energy `∫_0^L g_v² ≤ S L + B`, and let its symbol on the lines `Re s = e` have,
at finitely many separated heights `Im ρ` of the critical line, simple poles `r_ρ/(e + i(y − Im ρ))`
with bounded remainders. Then `Σ_ρ ‖r_ρ‖² ≤ S`. -/
theorem sum_residue_le_slope {v : ℕ → ℝ} (hv0 : v 0 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ n, |v n| ≤ K * n ^ 2) {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + B)
    (Z : Finset ℂ) (hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im) (r : ℂ → ℂ)
    (hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile v) e y - r ρ / ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M) :
    ∑ ρ ∈ Z, ‖r ρ‖ ^ 2 ≤ S := by
  by_contra hlt
  simp only [not_le] at hlt
  set R := ∑ ρ ∈ Z, ‖r ρ‖ ^ 2 with hR
  have hcap := eventually_le_mul_integral_lineSymbol_of_poles hv0 hS0 hB0 hlin Z hsep r hpole
    (M := Real.pi * (S + R) / 2) (by have := Real.pi_pos; nlinarith)
  have hgap : 0 < Real.pi * (R - S) / 2 := by have := Real.pi_pos; nlinarith
  have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), 2 * Real.pi * e * B < Real.pi * (R - S) / 2 := by
    have hc : Tendsto (fun e : ℝ => 2 * Real.pi * e * B) (𝓝 0) (𝓝 (2 * Real.pi * 0 * B)) :=
      (by fun_prop : Continuous fun e : ℝ => 2 * Real.pi * e * B).tendsto 0
    simp only [mul_zero, zero_mul] at hc
    exact (hc.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hgap)
  obtain ⟨e, he1, he2, he0⟩ := (hcap.and (hsmall.and self_mem_nhdsWithin)).exists
  have he : (0 : ℝ) < e := he0
  have hpi := Real.pi_pos
  have := mul_integral_norm_sq_lineSymbol_le_of_linear hv0 hK hv hS0 hB0 hlin he
  nlinarith

/-- A negative slope is impossible for a nonnegative log-energy. -/
theorem not_forall_logEnergy_le_of_neg (v : ℕ → ℝ) {S B : ℝ} (hS : S < 0) :
    ¬ ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + B := by
  intro hlin
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ S * L + B < 0 :=
    ⟨max 0 ((|B| + 1) / (-S)), le_max_left _ _, by
      have h1 : (|B| + 1) / (-S) ≤ max 0 ((|B| + 1) / (-S)) := le_max_right _ _
      have hSne : -S ≠ 0 := by linarith
      have h2 : -S * ((|B| + 1) / (-S)) = |B| + 1 := mul_div_cancel₀ _ hSne
      nlinarith [le_abs_self B]⟩
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 :=
    intervalIntegral.integral_nonneg hL0 fun u _ => sq_nonneg _
  linarith [hlin L hL0]

/-! ### The critical residues are paid by the energy -/

/-- **The Mertens line symbol.** Under a linear log-energy, on the line `Re s = ½ + e`, `e > 0`,
`ζ(s)` does not vanish and the line symbol of the Mertens profile is `1/(s ζ(s))`. -/
theorem lineSymbol_mertens_eq_of_linear {S B : ℝ} (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B)
    {e : ℝ} (he : 0 < e) (y : ℝ) (hs1 : (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1) :
    riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 ∧
      lineSymbol (logProfile mertensRow) e y = 1 / ((((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
        riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
  have hC : 0 ≤ S / e + B := add_nonneg (div_nonneg hS0 he.le) hB0
  have hE := fun T => pronic_energy_le_of_linear hS0 hB0 hlin (v := mertensRow) he T
  have hprod := riemannZeta_mul_complexMellinPairing_mertensRow hC he.le hE
    (s := ((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) (by simp; linarith) hs1
  refine ⟨left_ne_zero_of_mul_eq_one hprod, ?_⟩
  rw [lineSymbol_logProfile_eq mertensRow_zero hC he.le hE (by linarith) y,
    eq_one_div_of_mul_eq_one_right hprod, div_div, mul_comm]

/-- **The Mertens energy pays its critical residues.** For every finite set `Z` of simple zeros of
`ζ` on the critical line and every `S < Σ_{ρ ∈ Z} ‖1/(ρ ζ′(ρ))‖²`, the log-scale Mertens energy
`∫_0^L e^{−u} M(⌊e^u⌋)² du = ∫_1^{e^L} M(⌊x⌋)²/x² dx` is not bounded by `S L + B` for any `B`. -/
theorem not_forall_mertens_energy_le_linear (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖1 / (ρ * deriv riemannZeta ρ)‖ ^ 2) :
    ¬ ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B := by
  intro hlin
  by_cases hS0 : S < 0
  · exact not_forall_logEnergy_le_of_neg mertensRow hS0 hlin
  simp only [not_lt] at hS0
  set B' := max B 0 with hB'
  have hlin' : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2 ≤ S * L + B' :=
    fun L hL => (hlin L hL).trans (by linarith [le_max_left B 0])
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hsym : ∀ e : ℝ, 0 < e → ∀ y : ℝ,
      ((((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1) →
      lineSymbol (logProfile mertensRow) e y = 1 / ((((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
        riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) := fun e he y hs1 =>
    (lineSymbol_mertens_eq_of_linear hS0 hB0 hlin' he y hs1).2
  have hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile mertensRow) e y - 1 / (ρ * deriv riemannZeta ρ) /
          ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := by
    intro ρ hρ
    obtain ⟨hz, hd, hre⟩ := hZ ρ hρ
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre; norm_num at hre
    have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; norm_num at hre
    obtain ⟨η, hη, M, hp⟩ := exists_inv_zeta_pole_bound hz hd hρ1 hρ0
    refine ⟨η / 2, by positivity, M, fun e he y hy => ?_⟩
    set s : ℂ := ((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hsdef
    have hss : s - ρ = (e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hsdef, hre]
    have hnorm : ‖s - ρ‖ < η := by
      rw [hss]
      calc ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖ ≤ ‖(e : ℂ)‖ + ‖((y - ρ.im : ℝ) : ℂ) * I‖ :=
            norm_add_le _ _
        _ = |e| + |y - ρ.im| := by
            simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ < η := by
            have h1 : |e| < η / 2 := by rw [abs_of_pos he.1]; exact he.2
            have h2 : |y - ρ.im| ≤ η / 2 :=
              abs_sub_le_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
            linarith
    have hne : s ≠ ρ := fun h => by
      have := congrArg Complex.re (show s - ρ = 0 by rw [h, sub_self])
      rw [hss] at this; simp at this; linarith [he.1]
    obtain ⟨-, hs1, -, hb⟩ := hp s hnorm hne
    rw [hsym e he.1 y hs1, ← hss]
    exact hb
  have hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im := fun ρ hρ ρ' hρ' hne h =>
    hne (Complex.ext (by rw [(hZ ρ hρ).2.2, (hZ ρ' hρ').2.2]) h)
  have hle := sum_residue_le_slope mertensRow_zero zero_le_one
    abs_mertensRow_le_sq hS0 hB0 hlin' Z hsep _ hpole
  linarith

/-- **The Mertens law in pronic form.** For every finite set `Z` of simple critical zeros and every
`S < Σ_{ρ ∈ Z} ‖1/(ρ ζ′(ρ))‖²`, the Mertens pronic energy `Σ_{n ≤ T} M(n)²/(n(n+1))` is not bounded
by `S log(T+1) + B` for all `T`. -/
theorem not_forall_mertens_pronicEnergy_le_log (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖1 / (ρ * deriv riemannZeta ρ)‖ ^ 2) :
    ¬ ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      S * Real.log ((T : ℝ) + 1) + B := by
  intro hT
  by_cases hS0 : S < 0
  · -- the energy is nonnegative, so a negative slope fails at large `T`
    obtain ⟨T, hT'⟩ : ∃ T : ℕ, S * Real.log ((T : ℝ) + 1) + B < 0 := by
      have hlog : Tendsto (fun T : ℕ => S * Real.log ((T : ℝ) + 1) + B) atTop atBot :=
        tendsto_atBot_add_const_right _ B ((Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).const_mul_atTop_of_neg
            hS0)
      exact (hlog.eventually (eventually_lt_atBot 0)).exists
    have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 T, mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      Finset.sum_nonneg fun n _ => by positivity
    linarith [hT T]
  simp only [not_lt] at hS0
  refine not_forall_mertens_energy_le_linear Z hZ hS (B := B + S * Real.log 2) fun L hL => ?_
  set T := ⌊Real.exp L⌋₊ with hTdef
  have hLT : L ≤ Real.log ((T : ℝ) + 1) :=
    ((Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)).le
  have hT2 : Real.log ((T : ℝ) + 1) ≤ L + Real.log 2 := by
    rw [← Real.log_exp L, ← Real.log_mul (Real.exp_pos L).ne' two_ne_zero]
    refine Real.log_le_log (by positivity) ?_
    have hfl : (T : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have h1 : 1 ≤ Real.exp L := Real.one_le_exp hL
    linarith
  calc ∫ u in (0 : ℝ)..L, logProfile mertensRow u ^ 2
      ≤ ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile mertensRow u ^ 2 := by
        refine intervalIntegral.integral_mono_interval le_rfl hL hLT
          (Eventually.of_forall fun u => sq_nonneg _) ?_
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (Real.log_nonneg (by
          linarith [T.cast_nonneg (α := ℝ)]))).mpr (integrableOn_logProfile_sq zero_le_one
            abs_mertensRow_le_sq _)
      _ = ∑ n ∈ Finset.Icc 1 T, mertensRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        (pronic_energy_eq_log_integral mertensRow T).symm
      _ ≤ S * Real.log ((T : ℝ) + 1) + B := hT T
      _ ≤ S * (L + Real.log 2) + B := by gcongr
      _ = S * L + (B + S * Real.log 2) := by ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
