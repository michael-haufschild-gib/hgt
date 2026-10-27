import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensEnergyPaysItsCriticalResidues

/-!
# The prime-error energy pays the critical zeros

The log profile of the prime-error row `ψ(n) − n` has symbol `(−ζ′(s)/ζ(s) − ζ(s))/s`, whose
poles at the zeros of `ζ` are simple whatever their multiplicity: at a zero `ρ` of order `m_ρ` the
residue is `−m_ρ/ρ`. The residue-mass law of `TheMertensEnergyPaysItsCriticalResidues` therefore
applies to every critical zero, with no simplicity hypothesis.

* **The prime-error symbol** (`complexMellinPairing_primeErrorRow`,
  `complexMellinPairing_primeErrorRow_eq`). `Φ_ψ = −ζ′/ζ − ζ` on `Re s > 2`, and under energy
  `O((T+1)^κ)` on `Re s > (1+κ)/2` wherever `ζ(s) ≠ 0`, `s ≠ 1` (identity theorem for the cleared
  function `R(s)((s−1)Φ_ψ(s)) + R(s)² + (s−1)R′(s) − R(s)`, `R(s) = (s−1)ζ(s)`).
* **Poles of the logarithmic derivative** (`exists_logDeriv_symbol_pole_bound`). At a zero `ρ` of
  order `m`, `(−ζ′/ζ − ζ)(s)/s = (−m/ρ)/(s − ρ) + O(1)`, from `ζ = (s − ρ)^m h`, `h(ρ) ≠ 0`.
* **The prime-error law** (`not_forall_primeError_energy_le_linear`,
  `not_forall_primeError_pronicEnergy_le_log`). For every finite set `Z` of zeros on the critical
  line and every `S < Σ_{ρ ∈ Z} m_ρ²/‖ρ‖²`, neither `∫_0^L e^{−u}(ψ(⌊e^u⌋) − ⌊e^u⌋)² du ≤ S L + B`
  for all `L` nor `Σ_{n ≤ T} (ψ(n) − n)²/(n(n+1)) ≤ S log(T+1) + B` for all `T`.

So `limsup (log X)⁻¹ ∫_1^X (ψ(⌊x⌋) − ⌊x⌋)²/x² dx ≥ Σ_{Re ρ = ½} m_ρ²/|ρ|²` unconditionally: the
constant of Cramér's mean-square theorem, which under RH is the exact limit, is an unconditional
lower bound for the upper log-density of the prime-error energy.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)
open ArithmeticFunction (vonMangoldt)

/-! ### The prime-error row and its symbol -/

/-- The prime-error row `ψ(n) − n = Σ_{k ≤ n} (Λ(k) − 1)`. -/
def primeErrorRow (n : ℕ) : ℝ := prefixSum (fun k => vonMangoldt k - 1) n

theorem primeErrorRow_zero : primeErrorRow 0 = 0 := prefixSum_zero _

theorem abs_vonMangoldt_sub_one_le {k : ℕ} (hk : 1 ≤ k) : |vonMangoldt k - 1| ≤ k := by
  have h0 : 0 ≤ vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : vonMangoldt k ≤ (k : ℝ) - 1 :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_sub_one_of_pos hk0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [abs_le]; constructor <;> linarith

theorem abs_primeErrorRow_le (n : ℕ) : |primeErrorRow n| ≤ 1 * (n : ℝ) ^ 2 := by
  unfold primeErrorRow prefixSum
  calc |∑ m ∈ Finset.Icc 1 n, (vonMangoldt m - 1)| ≤ ∑ m ∈ Finset.Icc 1 n, |vonMangoldt m - 1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (n : ℝ) := Finset.sum_le_sum fun m hm => by
        have hm' := Finset.mem_Icc.mp hm
        exact (abs_vonMangoldt_sub_one_le hm'.1).trans (by exact_mod_cast hm'.2)
    _ = 1 * (n : ℝ) ^ 2 := by simp; ring

/-- **The prime-error pairing on `Re s > 2`**: `Σ_n (ψ(n) − n)(n^{−s} − (n+1)^{−s}) =
−ζ′(s)/ζ(s) − ζ(s)`. -/
theorem complexMellinPairing_primeErrorRow {s : ℂ} (hs : 2 < s.re) :
    complexMellinPairing primeErrorRow s = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsum : Summable fun n : ℕ => |primeErrorRow n| * (n : ℝ) ^ (-s.re - 1) := by
    refine (Real.summable_nat_rpow.mpr (show 1 - s.re < -1 by linarith)).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [primeErrorRow_zero, abs_zero, zero_mul]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    calc |primeErrorRow n| * (n : ℝ) ^ (-s.re - 1) ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ (-s.re - 1) :=
          mul_le_mul_of_nonneg_right ((abs_primeErrorRow_le n).trans (by rw [one_mul]))
            (by positivity)
      _ = (n : ℝ) ^ (1 - s.re) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hn0]; norm_num; ring_nf
  have hval := integral_stepLaplaceIntegrand primeErrorRow_zero (by linarith) hsum
  have hint := integrable_stepLaplaceIntegrand primeErrorRow_zero (by linarith) hsum
  have hIci : ∫ u, stepLaplaceIntegrand primeErrorRow s u =
      ∫ u in Ioi (0 : ℝ), stepLaplaceIntegrand primeErrorRow s u := by
    rw [← integral_Ici_eq_integral_Ioi]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Ici, not_le] at hu
    exact stepLaplaceIntegrand_of_neg primeErrorRow_zero s hu
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 0 hint.integrableOn hlog
  rw [← hIci, hval] at hlim1
  have hrw : ∀ N : ℕ, ∫ u in (0 : ℝ)..Real.log ((N : ℝ) + 1),
      stepLaplaceIntegrand primeErrorRow s u =
      (∑ n ∈ Finset.Icc 1 N, ((vonMangoldt n - 1 : ℝ) : ℂ) * (n : ℂ) ^ (-s) -
        (primeErrorRow N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) / s := by
    intro N
    simp only [primeErrorRow]
    rw [← integral_prefix_exp_eq (fun k => vonMangoldt k - 1) hs0 N]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [stepLaplaceIntegrand, primeErrorRow]
    ring
  simp_rw [hrw] at hlim1
  have hΛ : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  have h1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs1
  have hL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((vonMangoldt n - 1 : ℝ) : ℂ) * (n : ℂ) ^ (-s))
      atTop (𝓝 (LSeries ((fun n => (vonMangoldt n : ℂ)) - 1) s)) := by
    have hS : LSeriesSummable ((fun n => (vonMangoldt n : ℂ)) - 1) s := hΛ.sub h1
    have h := hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun N => ?_
    simp only [Function.comp]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      Finset.sum_range_succ', LSeries.term_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (by omega), add_comm 1 n, Complex.cpow_neg, div_eq_mul_inv]
    simp only [Pi.sub_apply, Pi.one_apply]
    push_cast
    ring
  have hB : Tendsto (fun N : ℕ => (primeErrorRow N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_rpow_neg_atTop (show 0 < s.re - 2 by
      linarith) |>.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos
      (Nat.succ_pos N)]
    simp only [Function.comp, neg_re]
    rw [Nat.cast_succ]
    have h1' : |primeErrorRow N| ≤ ((N : ℝ) + 1) ^ 2 :=
      ((abs_primeErrorRow_le N).trans (by rw [one_mul])).trans (by gcongr; linarith)
    calc |primeErrorRow N| * ((N : ℝ) + 1) ^ (-s.re) ≤ ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right h1' (by positivity)
      _ = ((N : ℝ) + 1) ^ (-(s.re - 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]; norm_num; ring_nf
  have hlim2 := (hL.sub hB).div_const s
  rw [sub_zero] at hlim2
  have := tendsto_nhds_unique hlim1 hlim2
  rw [div_left_inj' hs0, LSeries_sub hΛ h1,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1,
    LSeries_one_eq_riemannZeta hs1] at this
  exact this


/-- **Continuation of the prime-error pairing.** Under energy `O((T+1)^κ)`, at every `s` with
`Re s > (1+κ)/2`, `s ≠ 1` and `ζ(s) ≠ 0`, `Φ_ψ(s) = −ζ′(s)/ζ(s) − ζ(s)`. -/
theorem complexMellinPairing_primeErrorRow_eq {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hE : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      C * ((T : ℝ) + 1) ^ κ) {s : ℂ} (hs : (1 + κ) / 2 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    complexMellinPairing primeErrorRow s = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have hΦ := ArithmeticCorrelationGeometry.differentiableOn_complexMellinPairing_of_energy_growth
    primeErrorRow_zero hC hκ hE
  set R := _root_.RHTower.zetaResidueUnit with hRdef
  have hRa : ∀ z, AnalyticAt ℂ R z := _root_.RHTower.analyticAt_zetaResidueUnit
  have hderivR : ∀ z : ℂ, z ≠ 1 → deriv R z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
    intro z hz
    have hev : R =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hw
    rw [hev.deriv_eq]
    have := ((hasDerivAt_id z).sub_const 1).mul (differentiableAt_riemannZeta hz).hasDerivAt
    simp only [id, one_mul] at this
    exact this.deriv
  set U : Set ℂ := {s : ℂ | (1 + κ) / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt ((1 + κ) / 2)).isPreconnected
  set H : ℂ → ℂ := fun z => R z * ((z - 1) * complexMellinPairing primeErrorRow z) + R z ^ 2 +
    ((z - 1) * deriv R z - R z) with hH
  have hRd : DifferentiableOn ℂ R U := fun z _ => (hRa z).differentiableAt.differentiableWithinAt
  have hR'd : DifferentiableOn ℂ (deriv R) U := fun z _ =>
    (hRa z).deriv.differentiableAt.differentiableWithinAt
  have hHd : DifferentiableOn ℂ H U :=
    ((hRd.mul ((differentiableOn_id.sub_const _).mul hΦ)).add (hRd.pow 2)).add
      (((differentiableOn_id.sub_const _).mul hR'd).sub hRd)
  set x₀ : ℂ := (((1 + κ) / 2 + 3 : ℝ) : ℂ) with hx₀
  have hx₀U : x₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hx₀, Complex.ofReal_re]; linarith
  have hzero : H =ᶠ[𝓝 x₀] 0 := by
    have hopen : {z : ℂ | 2 < z.re} ∈ 𝓝 x₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
        simp only [Set.mem_setOf_eq, hx₀, Complex.ofReal_re]; linarith)
    filter_upwards [hopen] with z hz
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz
    have hζz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    simp only [hH, Pi.zero_apply]
    rw [hderivR z hz1, hRdef, ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hz1,
      complexMellinPairing_primeErrorRow hz]
    field_simp
    ring
  have hEq := (hHd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx₀U hzero
  have hval := hEq (show s ∈ U from hs)
  simp only [hH, Pi.zero_apply] at hval
  rw [hderivR s hs1, hRdef, ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hs1] at hval
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hkey : riemannZeta s * complexMellinPairing primeErrorRow s =
      -riemannZeta s ^ 2 - deriv riemannZeta s := by
    have h2 : (s - 1) ^ 2 * (riemannZeta s * complexMellinPairing primeErrorRow s +
        riemannZeta s ^ 2 + deriv riemannZeta s) = 0 := by linear_combination hval
    have := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hs1')
    linear_combination this
  field_simp
  linear_combination hkey

/-! ### Poles of the logarithmic derivative -/

/-- `ζ` is analytic away from `1`. -/
theorem analyticAt_riemannZeta_of_ne_one {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ riemannZeta z :=
  DifferentiableOn.analyticAt (s := {w | w ≠ 1})
    (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
    (isOpen_ne.mem_nhds hz)

/-- `ζ` is not locally zero at any point `z ≠ 1`. -/
theorem not_eventually_riemannZeta_eq_zero {z : ℂ} (hz : z ≠ 1) :
    ¬ ∀ᶠ w in 𝓝 z, riemannZeta w = 0 := by
  intro h
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun w hw =>
    analyticAt_riemannZeta_of_ne_one hw
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre
    (show z ∈ ({1}ᶜ : Set ℂ) from hz) h
  have h2 := hEq (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re) h2

/-- **The logarithmic derivative symbol at a zero of order `m`.** Near a zero `ρ ∉ {0, 1}` of
order `m`, `(−ζ′(s)/ζ(s) − ζ(s))/s = (−m/ρ)/(s − ρ) + O(1)`, and `ζ ≠ 0` on the punctured disc. -/
theorem exists_logDeriv_symbol_pole_bound {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1)
    (hρ0 : ρ ≠ 0) :
    ∃ η > 0, ∃ M : ℝ, ∀ s : ℂ, ‖s - ρ‖ < η → s ≠ ρ →
      riemannZeta s ≠ 0 ∧ s ≠ 1 ∧
      ‖(-deriv riemannZeta s / riemannZeta s - riemannZeta s) / s -
        -(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ / (s - ρ)‖ ≤ M := by
  have hA := analyticAt_riemannZeta_of_ne_one hρ1
  obtain ⟨n, h, hhA, hh0, hfac⟩ :=
    hA.exists_eventuallyEq_pow_smul_nonzero_iff.mpr (not_eventually_riemannZeta_eq_zero hρ1)
  have hord : analyticOrderAt riemannZeta ρ = n :=
    hA.analyticOrderAt_eq_natCast.mpr ⟨h, hhA, hh0, hfac⟩
  rw [hord, ENat.toNat_coe]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · have := hfac.self_of_nhds
      simp only [sub_self, pow_zero, one_smul] at this
      exact absurd (this.symm.trans hρ) hh0
    · exact ⟨m, rfl⟩
  -- the derivative of the factorization
  have hderiv : ∀ᶠ z in 𝓝 ρ, deriv riemannZeta z =
      ((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * h z + (z - ρ) ^ (m + 1) * deriv h z := by
    filter_upwards [hfac.eventually_nhds, hhA.eventually_analyticAt] with z hz hzA
    rw [(show riemannZeta =ᶠ[𝓝 z] (fun w => (w - ρ) ^ (m + 1) • h w) from hz).deriv_eq]
    have := ((hasDerivAt_id z).sub_const ρ).pow (m + 1) |>.mul hzA.differentiableAt.hasDerivAt
    simp only [id, Nat.add_sub_cancel, mul_one] at this
    simp only [smul_eq_mul]
    exact this.deriv
  -- the bounded remainder
  set K : ℂ → ℂ := fun z => ((m + 1 : ℕ) : ℂ) / (z * ρ) - deriv h z / h z / z -
    riemannZeta z / z with hK
  have hKc : ContinuousAt K ρ := by
    have hh' : ContinuousAt (deriv h) ρ := (hhA.deriv).continuousAt
    refine ((continuousAt_const.div (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero hρ0 hρ0)).sub ((hh'.div hhA.continuousAt hh0).div continuousAt_id hρ0)).sub
      ((hA.continuousAt).div continuousAt_id hρ0)
  have hev : ∀ᶠ z in 𝓝 ρ, dist (K z) (K ρ) < 1 ∧ h z ≠ 0 ∧ z ≠ 1 ∧ z ≠ 0 ∧
      riemannZeta z = (z - ρ) ^ (m + 1) * h z ∧
      deriv riemannZeta z = ((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * h z + (z - ρ) ^ (m + 1) * deriv h z := by
    filter_upwards [Metric.tendsto_nhds.mp hKc 1 one_pos, hhA.continuousAt.eventually_ne hh0,
      isOpen_ne.mem_nhds hρ1, eventually_ne_nhds hρ0, hfac, hderiv] with z h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, by simpa only [smul_eq_mul] using h5, h6⟩
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨η, hη, ‖K ρ‖ + 1, fun s hs hne => ?_⟩
  obtain ⟨hK1, hhs, hs1, hs0, hζs, hζ's⟩ := hball (by rwa [dist_eq_norm])
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hne
  have hζne : riemannZeta s ≠ 0 := by rw [hζs]; exact mul_ne_zero (pow_ne_zero _ hsρ) hhs
  refine ⟨hζne, hs1, ?_⟩
  have hval : (-deriv riemannZeta s / riemannZeta s - riemannZeta s) / s -
      -(((m + 1 : ℕ) : ℕ) : ℂ) / ρ / (s - ρ) = K s := by
    simp only [hK]
    rw [hζ's]
    nth_rewrite 1 [hζs]
    have hpow : (s - ρ) ^ m ≠ 0 := pow_ne_zero _ hsρ
    field_simp
    ring
  rw [hval]
  have := norm_sub_norm_le (K s) (K ρ)
  rw [dist_eq_norm] at hK1
  linarith


/-! ### The critical zeros are paid by the prime-error energy -/

/-- **The prime-error energy pays the critical zeros.** For every finite set `Z` of zeros of `ζ`
on the critical line and every `S < Σ_{ρ ∈ Z} ‖m_ρ/ρ‖²`, `m_ρ` the order of `ρ`, the log-scale
prime-error energy `∫_0^L e^{−u}(ψ(⌊e^u⌋) − ⌊e^u⌋)² du` is not bounded by `S L + B` for any `B`. -/
theorem not_forall_primeError_energy_le_linear (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2) :
    ¬ ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤ S * L + B := by
  intro hlin
  by_cases hS0 : S < 0
  · exact not_forall_logEnergy_le_of_neg primeErrorRow hS0 hlin
  simp only [not_lt] at hS0
  set B' := max B 0 with hB'
  have hlin' : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2 ≤
      S * L + B' := fun L hL => (hlin L hL).trans (by linarith [le_max_left B 0])
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hC : ∀ κ : ℝ, 0 < κ → 0 ≤ S / κ + B' := fun κ hκ => add_nonneg (div_nonneg hS0 hκ.le) hB0
  have hE := fun κ (hκ : 0 < κ) T =>
    pronic_energy_le_of_linear hS0 hB0 hlin' (v := primeErrorRow) hκ T
  have hsym : ∀ e : ℝ, 0 < e → ∀ y : ℝ,
      ((((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 1) →
      riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 →
      lineSymbol (logProfile primeErrorRow) e y =
        (-deriv riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) -
          riemannZeta (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) /
        (((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro e he y hs1 hζ
    rw [lineSymbol_logProfile_eq primeErrorRow_zero (hC e he) he.le (hE e he) (by linarith) y,
      complexMellinPairing_primeErrorRow_eq (hC e he) he.le (hE e he) (by simp; linarith) hs1 hζ]
  have hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile primeErrorRow) e y -
          -(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ /
            ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := by
    intro ρ hρ
    obtain ⟨hz, hre⟩ := hZ ρ hρ
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre; norm_num at hre
    have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre; norm_num at hre
    obtain ⟨η, hη, M, hp⟩ := exists_logDeriv_symbol_pole_bound hz hρ1 hρ0
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
    obtain ⟨hζ, hs1, hb⟩ := hp s hnorm hne
    rw [hsym e he.1 y hs1 hζ, ← hss]
    exact hb
  have hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im := fun ρ hρ ρ' hρ' hne h =>
    hne (Complex.ext (by rw [(hZ ρ hρ).2, (hZ ρ' hρ').2]) h)
  have hle := sum_residue_le_slope primeErrorRow_zero zero_le_one abs_primeErrorRow_le hS0 hB0
    hlin' Z hsep _ hpole
  simp only [neg_div, norm_neg] at hle
  linarith

/-- **The prime-error law in pronic form.** For every finite set `Z` of critical zeros and every
`S < Σ_{ρ ∈ Z} ‖m_ρ/ρ‖²`, `Σ_{n ≤ T} (ψ(n) − n)²/(n(n+1))` is not bounded by `S log(T+1) + B` for
all `T`. -/
theorem not_forall_primeError_pronicEnergy_le_log (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖(((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℂ) / ρ‖ ^ 2) :
    ¬ ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T, primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      S * Real.log ((T : ℝ) + 1) + B := by
  intro hT
  by_cases hS0 : S < 0
  · obtain ⟨T, hT'⟩ : ∃ T : ℕ, S * Real.log ((T : ℝ) + 1) + B < 0 := by
      have hlog : Tendsto (fun T : ℕ => S * Real.log ((T : ℝ) + 1) + B) atTop atBot :=
        tendsto_atBot_add_const_right _ B ((Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).const_mul_atTop_of_neg
            hS0)
      exact (hlog.eventually (eventually_lt_atBot 0)).exists
    have h0 : 0 ≤ ∑ n ∈ Finset.Icc 1 T, primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      Finset.sum_nonneg fun n _ => by positivity
    linarith [hT T]
  simp only [not_lt] at hS0
  refine not_forall_primeError_energy_le_linear Z hZ hS (B := B + S * Real.log 2) fun L hL => ?_
  set T := ⌊Real.exp L⌋₊ with hTdef
  have hLT : L ≤ Real.log ((T : ℝ) + 1) :=
    ((Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)).le
  have hT2 : Real.log ((T : ℝ) + 1) ≤ L + Real.log 2 := by
    rw [← Real.log_exp L, ← Real.log_mul (Real.exp_pos L).ne' two_ne_zero]
    refine Real.log_le_log (by positivity) ?_
    have hfl : (T : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have h1 : 1 ≤ Real.exp L := Real.one_le_exp hL
    linarith
  calc ∫ u in (0 : ℝ)..L, logProfile primeErrorRow u ^ 2
      ≤ ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile primeErrorRow u ^ 2 := by
        refine intervalIntegral.integral_mono_interval le_rfl hL hLT
          (Eventually.of_forall fun u => sq_nonneg _) ?_
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (Real.log_nonneg (by
          linarith [T.cast_nonneg (α := ℝ)]))).mpr (integrableOn_logProfile_sq zero_le_one
            abs_primeErrorRow_le _)
      _ = ∑ n ∈ Finset.Icc 1 T, primeErrorRow n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        (pronic_energy_eq_log_integral primeErrorRow T).symm
      _ ≤ S * Real.log ((T : ℝ) + 1) + B := hT T
      _ ≤ S * (L + Real.log 2) + B := by gcongr
      _ = S * L + (B + S * Real.log 2) := by ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
