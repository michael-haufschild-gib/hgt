/-
# Böttcher tower — the complex Böttcher coordinate (log-series), brick 2

`log φ_c(z) = log z + ∑ₖ 2⁻⁽ᵏ⁺¹⁾·log(1 + c/(f_c^[k]z)²)`. The series converges on the
escape set: each term is bounded by `(‖c‖/‖z‖²)·(1/2)ᵏ` (via the complex-log estimate
`norm_clog_one_add_le` and the orbit growth), hence summable. This is the ℂ-analog of
`greenApprox_converges`; `Re(log φ_c) = G_c`, and the multivaluedness of the series
(branch of `log`) on disconnected `Ω_c` is where the dyadic monodromy lives.
-/
import GaloisForLFunctions.Bottcher.ComplexLogBound
import GaloisForLFunctions.Bottcher.GreenFunction
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.AbsMax

open Complex InnerProductSpace

namespace Bottcher

/-- The `k`-th term of the complex Böttcher log-series. -/
noncomputable def bottcherLogTerm (c z : ℂ) (k : ℕ) : ℂ :=
  (2 ^ (k + 1) : ℂ)⁻¹ * Complex.log (1 + c / ((quadratic c)^[k] z) ^ 2)

/-- **Term bound** `‖term_k‖ ≤ (‖c‖/‖z‖²)·(1/2)ᵏ` on the escape set. -/
theorem norm_bottcherLogTerm_le {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (k : ℕ) :
    ‖bottcherLogTerm c z k‖ ≤ ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ k := by
  unfold bottcherLogTerm
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz k
  set A := (quadratic c)^[k] z with hA
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hne
  have hA2 : (0 : ℝ) < ‖A‖ ^ 2 := by positivity
  have hw : ‖c / A ^ 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, div_le_iff₀ hA2]; nlinarith [hreg]
  have hlog := norm_clog_one_add_le hw
  have hnorm2 : ‖(2 ^ (k + 1) : ℂ)⁻¹‖ = (2 ^ (k + 1) : ℝ)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_ofNat]
  have hAz : ‖z‖ ≤ ‖A‖ := norm_le_orbit hc hz k
  have hcA : ‖c / A ^ 2‖ = ‖c‖ / ‖A‖ ^ 2 := by rw [norm_div, norm_pow]
  rw [norm_mul, hnorm2]
  calc (2 ^ (k + 1) : ℝ)⁻¹ * ‖Complex.log (1 + c / A ^ 2)‖
      ≤ (2 ^ (k + 1) : ℝ)⁻¹ * (2 * ‖c / A ^ 2‖) := by gcongr
    _ = (2 ^ (k + 1) : ℝ)⁻¹ * (2 * (‖c‖ / ‖A‖ ^ 2)) := by rw [hcA]
    _ ≤ (2 ^ (k + 1) : ℝ)⁻¹ * (2 * (‖c‖ / ‖z‖ ^ 2)) := by
        have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (by linarith) 2
        gcongr
    _ = ‖c‖ / ‖z‖ ^ 2 * (1 / 2) ^ k := by rw [pow_succ, div_pow, one_pow]; field_simp

/-- **The complex Böttcher log-series is summable** on the escape set. -/
theorem bottcherLogTerm_summable {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    Summable (bottcherLogTerm c z) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_bottcherLogTerm_le hc hz k) ?_
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The complex Böttcher coordinate's logarithm, `log φ_c(z) = log z + ∑ₖ termₖ`. -/
noncomputable def bottcherLog (c z : ℂ) : ℂ :=
  Complex.log z + ∑' k, bottcherLogTerm c z k

/-- The complex Böttcher coordinate `φ_c(z) = exp(log φ_c(z))`, with `|φ_c| = exp(G_c)`. -/
noncomputable def bottcherCoord (c z : ℂ) : ℂ := Complex.exp (bottcherLog c z)

/-- `φ_c` is never zero (it is an exponential). -/
theorem bottcherCoord_ne_zero (c z : ℂ) : bottcherCoord c z ≠ 0 := Complex.exp_ne_zero _

/-- The open neighborhood of `∞` (`‖z‖ > max 2 ‖c‖`) where the escape regime holds. -/
def escapeOpen (c : ℂ) : Set ℂ := {z | max 2 ‖c‖ < ‖z‖}

theorem isOpen_escapeOpen (c : ℂ) : IsOpen (escapeOpen c) :=
  isOpen_lt continuous_const continuous_norm

theorem mem_escapeOpen_regime {c z : ℂ} (hz : z ∈ escapeOpen c) : ‖c‖ ≤ ‖z‖ ∧ 2 < ‖z‖ :=
  ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz), lt_of_le_of_lt (le_max_left _ _) hz⟩

/-- **Real part of the term = Green telescoping difference**: `Re(termₖ) = g_{k+1}-g_k`.
This ties the complex coordinate to the proven real Green's function: summing gives
`Re(bottcherLog) = G_c`, i.e. `|φ_c| = exp(G_c)`. -/
theorem bottcherLogTerm_re {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (k : ℕ) :
    (bottcherLogTerm c z k).re = greenApprox c z (k + 1) - greenApprox c z k := by
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz k
  have hAne : (quadratic c)^[k] z ≠ 0 := hne
  have hfkp1 : (quadratic c)^[k + 1] z = ((quadratic c)^[k] z) ^ 2 + c := by
    rw [Function.iterate_succ', Function.comp_apply, quadratic_apply]
  have hfne : (quadratic c)^[k + 1] z ≠ 0 := (escape_regime_stable hc hz (k + 1)).2
  have hfe : (1 : ℂ) + c / ((quadratic c)^[k] z) ^ 2
      = (quadratic c)^[k + 1] z / ((quadratic c)^[k] z) ^ 2 := by
    rw [hfkp1]; field_simp
  unfold bottcherLogTerm greenApprox
  rw [hfe, show ((2 : ℂ) ^ (k + 1))⁻¹ = ((((2 : ℝ) ^ (k + 1))⁻¹ : ℝ) : ℂ) from by push_cast; ring,
      re_ofReal_mul, Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hfne) (norm_ne_zero_iff.mpr (pow_ne_zero 2 hAne)),
      norm_pow, Real.log_pow, pow_succ]
  push_cast
  field_simp

/-- **`Re(log φ_c) = G_c`**: the real part of the complex Böttcher logarithm is exactly
the Green's function. -/
theorem bottcherLog_re {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    (bottcherLog c z).re = greenLimit c z := by
  unfold bottcherLog
  rw [Complex.add_re, Complex.log_re, re_tsum (bottcherLogTerm_summable hc hz),
      tsum_congr (fun k => bottcherLogTerm_re hc hz k), greenLimit_eq_tsum hc hz]
  congr 1
  simp [greenApprox]

/-- **`‖φ_c‖ = exp(G_c)`** from the actual complex coordinate (matching `bottcherModulus`). -/
theorem norm_bottcherCoord {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖bottcherCoord c z‖ = bottcherModulus c z := by
  unfold bottcherCoord bottcherModulus
  rw [Complex.norm_exp, bottcherLog_re hc hz]

/-- `φ_c` maps the escape regime into `{|w| > 1}` (`‖φ_c(z)‖ > 1`). -/
theorem one_lt_norm_bottcherCoord {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    1 < ‖bottcherCoord c z‖ := by
  rw [norm_bottcherCoord hc hz]
  exact Real.one_lt_exp_iff.mpr (greenLimit_pos_escape hc hz)

/-- **Term-shift** `termₖ(f_c z) = 2·term_{k+1}(z)` — the branch-free seed of the
Böttcher functional equation `φ_c(z²+c)=φ_c(z)²` (same log argument, shifted index). -/
theorem bottcherLogTerm_quadratic (c z : ℂ) (k : ℕ) :
    bottcherLogTerm c (quadratic c z) k = 2 * bottcherLogTerm c z (k + 1) := by
  unfold bottcherLogTerm
  rw [← Function.iterate_succ_apply, pow_succ]
  field_simp
  ring

/-- The quadratic map is analytic everywhere. -/
theorem analyticAt_quadratic (c z : ℂ) : AnalyticAt ℂ (quadratic c) z := by
  unfold quadratic
  exact (analyticAt_id.pow 2).add analyticAt_const

/-- Every iterate `(quadratic c)^[k]` is analytic (a polynomial of degree `2ᵏ`). -/
theorem analyticAt_quadratic_iterate (c : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ (quadratic c)^[k] z := by
  induction k with
  | zero => rw [Function.iterate_zero]; exact analyticAt_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (analyticAt_quadratic c _).comp ih

/-- On the escape regime, `1 + c/(f_c^[k]z)²` lies in the slit plane (`Re ≥ 1/2`), so the
principal `Complex.log` is analytic there — a prerequisite for `φ_c`'s analyticity. -/
theorem one_add_mem_slitPlane {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (k : ℕ) :
    1 + c / ((quadratic c)^[k] z) ^ 2 ∈ slitPlane := by
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz k
  have hApos : 0 < ‖(quadratic c)^[k] z‖ := norm_pos_iff.mpr hne
  rw [mem_slitPlane_iff]; left
  have hw : ‖c / ((quadratic c)^[k] z) ^ 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, div_le_iff₀ (pow_pos hApos 2)]; linarith [hreg]
  have hre : -(1 / 2 : ℝ) ≤ (c / ((quadratic c)^[k] z) ^ 2).re := by
    have h := abs_re_le_norm (c / ((quadratic c)^[k] z) ^ 2)
    rw [abs_le] at h; linarith [h.1, hw]
  rw [Complex.add_re, Complex.one_re]; linarith [hre]

/-- **Each term is analytic** on the escape regime (orbit analytic, denominator nonzero,
argument in the slit plane) — a step toward the analyticity of `φ_c`. -/
theorem analyticAt_bottcherLogTerm {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (k : ℕ) :
    AnalyticAt ℂ (fun w => bottcherLogTerm c w k) z := by
  obtain ⟨hreg, hne⟩ := escape_regime_stable hc hz k
  have horbit : AnalyticAt ℂ (fun w => (quadratic c)^[k] w) z :=
    analyticAt_quadratic_iterate c k z
  have hdiv : AnalyticAt ℂ (fun w => c / ((quadratic c)^[k] w) ^ 2) z :=
    analyticAt_const.div (horbit.pow 2) (pow_ne_zero 2 hne)
  have hlog : AnalyticAt ℂ (fun w => Complex.log (1 + c / ((quadratic c)^[k] w) ^ 2)) z :=
    (analyticAt_const.add hdiv).clog (one_add_mem_slitPlane hc hz k)
  exact analyticAt_const.mul hlog

/-- **The Böttcher log-series `∑ₖ termₖ` is analytic** on `escapeOpen` (Weierstrass M-test:
each term analytic, uniformly bounded by a summable geometric series). -/
theorem differentiableOn_bottcherLogSum (c : ℂ) :
    DifferentiableOn ℂ (fun z => ∑' k, bottcherLogTerm c z k) (escapeOpen c) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun k => ‖c‖ / (max 2 ‖c‖) ^ 2 * (1 / 2) ^ k)
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · intro k z hz
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
    exact (analyticAt_bottcherLogTerm hc hz2 k).differentiableAt.differentiableWithinAt
  · exact isOpen_escapeOpen c
  · intro k w hw
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hw
    refine le_trans (norm_bottcherLogTerm_le hc hz2 k) ?_
    have hR : (0 : ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    gcongr
    exact le_of_lt hw

/-- `log φ_c = log z + ∑ₖ termₖ` is analytic on the slit neighborhood `escapeOpen ∩ slitPlane`
(the `log z` summand contributes the branch cut on the negative reals). -/
theorem differentiableOn_bottcherLog (c : ℂ) :
    DifferentiableOn ℂ (bottcherLog c) (escapeOpen c ∩ slitPlane) := by
  unfold bottcherLog
  exact DifferentiableOn.add
    (fun z hz => (Complex.hasDerivAt_log hz.2).differentiableAt.differentiableWithinAt)
    ((differentiableOn_bottcherLogSum c).mono Set.inter_subset_left)

/-- **`φ_c` is analytic** on the slit neighborhood of `∞` (`escapeOpen ∩ slitPlane`).
The multivaluedness across the slit / around the holes of disconnected `K_c` is the
monodromy that carries the dyadic group. -/
theorem analyticOnNhd_bottcherCoord (c : ℂ) :
    AnalyticOnNhd ℂ (bottcherCoord c) (escapeOpen c ∩ slitPlane) := by
  have hd : DifferentiableOn ℂ (bottcherCoord c) (escapeOpen c ∩ slitPlane) := by
    unfold bottcherCoord
    exact (differentiableOn_bottcherLog c).cexp
  exact hd.analyticOnNhd ((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane)

/-- **`d log φ_c` term-by-term**: on `escapeOpen`, the derivative of the Böttcher series
is the sum of the term derivatives. The analytic object the contour/monodromy integrates. -/
theorem hasSum_deriv_bottcherLogSum {c z : ℂ} (hz : z ∈ escapeOpen c) :
    HasSum (fun k => deriv (fun w => bottcherLogTerm c w k) z)
      (deriv (fun w => ∑' k, bottcherLogTerm c w k) z) := by
  apply Complex.hasSum_deriv_of_summable_norm
    (u := fun k => ‖c‖ / (max 2 ‖c‖) ^ 2 * (1 / 2) ^ k)
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · intro k z' hz'
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz'
    exact (analyticAt_bottcherLogTerm hc hz2 k).differentiableAt.differentiableWithinAt
  · exact isOpen_escapeOpen c
  · intro k w hw
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hw
    refine le_trans (norm_bottcherLogTerm_le hc hz2 k) ?_
    have hR : (0 : ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    gcongr
    exact le_of_lt hw
  · exact hz

/-- **Explicit `d log φ_c = z⁻¹ + ∑ₖ deriv(termₖ)`** on the slit neighborhood. The
`z⁻¹` is the pole at `∞`; the series part contributes the Cauchy transform of the
equilibrium measure (Brolin), whose loop integrals are the dyadic monodromy. -/
theorem deriv_bottcherLog {c z : ℂ} (hz : z ∈ escapeOpen c ∩ slitPlane) :
    deriv (bottcherLog c) z = z⁻¹ + deriv (fun w => ∑' k, bottcherLogTerm c w k) z := by
  have hlog : DifferentiableAt ℂ Complex.log z := (Complex.hasDerivAt_log hz.2).differentiableAt
  have hsum : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm c w k) z :=
    (differentiableOn_bottcherLogSum c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hz.1)
  unfold bottcherLog
  rw [deriv_fun_add hlog hsum, (Complex.hasDerivAt_log hz.2).deriv]

/-- **`G_c` is harmonic** on the slit neighborhood of `∞`: `G_c = Re(log φ_c)` and `φ_c`
is analytic, so its real part is harmonic. A defining property of the Green's function —
a step toward Brolin's characterization `G_c = potential of the equilibrium measure`. -/
theorem harmonicAt_greenLimit {c z : ℂ} (hz : z ∈ escapeOpen c ∩ slitPlane) :
    HarmonicAt (greenLimit c) z := by
  have hopen : IsOpen (escapeOpen c ∩ slitPlane) :=
    (isOpen_escapeOpen c).inter Complex.isOpen_slitPlane
  have hanalytic : AnalyticAt ℂ (bottcherLog c) z :=
    (differentiableOn_bottcherLog c).analyticAt (hopen.mem_nhds hz)
  have hharm : HarmonicAt (fun w => (bottcherLog c w).re) z := hanalytic.harmonicAt_re
  have heq : (fun w => (bottcherLog c w).re) =ᶠ[nhds z] greenLimit c := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hw.1
    exact bottcherLog_re hc hz2
  exact (harmonicAt_congr_nhds heq).mp hharm

/-- `G_c` is continuous on the slit neighborhood (harmonic ⟹ `C²` ⟹ continuous). -/
theorem continuousAt_greenLimit {c z : ℂ} (hz : z ∈ escapeOpen c ∩ slitPlane) :
    ContinuousAt (greenLimit c) z :=
  (harmonicAt_greenLimit hz).1.continuousAt

/-- **Böttcher normalization** `‖log φ_c(z) − log z‖ ≤ 2‖c‖/‖z‖²` on the escape set, so
`log φ_c(z) − log z → 0` and `φ_c(z)/z → 1` as `z → ∞` — the defining normalization. -/
theorem norm_bottcherLog_sub_log_le {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖bottcherLog c z - Complex.log z‖ ≤ 2 * ‖c‖ / ‖z‖ ^ 2 := by
  have hgeom : Summable (fun k : ℕ => ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hns : Summable (fun k => ‖bottcherLogTerm c z k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_bottcherLogTerm_le hc hz k) hgeom
  unfold bottcherLog
  rw [add_sub_cancel_left]
  calc ‖∑' k, bottcherLogTerm c z k‖
      ≤ ∑' k, ‖bottcherLogTerm c z k‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' k : ℕ, ‖c‖ / ‖z‖ ^ 2 * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_mono hns hgeom (fun k => norm_bottcherLogTerm_le hc hz k)
    _ = 2 * ‖c‖ / ‖z‖ ^ 2 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

/-- **Sum part of the functional equation** (branch-free):
`∑ₖ termₖ(f_c z) = 2·(∑ₖ termₖ(z) − term₀(z))`. The remaining `log z` vs `log(z²+c)`
part is the branch-dependent piece where the dyadic monodromy lives. -/
theorem bottcherLog_sum_quadratic {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ∑' k, bottcherLogTerm c (quadratic c z) k
      = 2 * (∑' k, bottcherLogTerm c z k - bottcherLogTerm c z 0) := by
  rw [tsum_congr (fun k => bottcherLogTerm_quadratic c z k), tsum_mul_left]
  congr 1
  rw [eq_sub_iff_add_eq, add_comm]
  exact ((bottcherLogTerm_summable hc hz).tsum_eq_zero_add).symm

/-- `‖φ_c(z)‖ = exp(G_c(z))` on the escape set (from `‖exp w‖ = exp(Re w)` and
`Re(log φ_c) = G_c`). The modulus of the complex coordinate is the exponential of the
real Green's function — the bridge between max-modulus (for `φ_c`) and the maximum
principle (for `G_c`). -/
theorem norm_bottcherCoord_eq_exp_green {c z : ℂ} (hz : z ∈ escapeOpen c ∩ slitPlane) :
    ‖bottcherCoord c z‖ = Real.exp (greenLimit c z) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz.1
  rw [bottcherCoord, Complex.norm_exp, bottcherLog_re hc hz2]

/-- **Maximum principle for the dynamical Green's function.** If `G_c` attains a maximum
over a preconnected open `U ⊆ escapeOpen ∩ slitPlane` at an interior point `z₀`, then `G_c`
is constant on `U`. Derived from the maximum-modulus principle for the analytic `φ_c`
(`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`) via `‖φ_c‖ = exp G_c`: an interior max of
`G_c` is an interior max of `‖φ_c‖`, forcing `φ_c` constant, hence `G_c` constant. This is the
uniqueness engine identifying `G_c` with the equilibrium potential (Brolin step A2). -/
theorem greenLimit_eqOn_of_isMaxOn {c : ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hsub : U ⊆ escapeOpen c ∩ slitPlane)
    (hz₀ : z₀ ∈ U) (hmax : IsMaxOn (greenLimit c) U z₀) :
    Set.EqOn (greenLimit c) (Function.const ℂ (greenLimit c z₀)) U := by
  have hdiff : DifferentiableOn ℂ (bottcherCoord c) U :=
    ((analyticOnNhd_bottcherCoord c).mono hsub).differentiableOn
  have hmaxnorm : IsMaxOn (norm ∘ bottcherCoord c) U z₀ := by
    rw [isMaxOn_iff]
    intro z hz
    simp only [Function.comp_apply]
    rw [norm_bottcherCoord_eq_exp_green (hsub hz), norm_bottcherCoord_eq_exp_green (hsub hz₀)]
    exact Real.exp_le_exp.mpr (hmax hz)
  have hconst : Set.EqOn (bottcherCoord c) (Function.const ℂ (bottcherCoord c z₀)) U :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdiff hz₀ hmaxnorm
  intro z hz
  have h1 : ‖bottcherCoord c z‖ = ‖bottcherCoord c z₀‖ := by rw [hconst hz]; rfl
  rw [norm_bottcherCoord_eq_exp_green (hsub hz), norm_bottcherCoord_eq_exp_green (hsub hz₀)] at h1
  exact Real.exp_injective h1

/-- **Functional equation for the complex Böttcher coordinate**: `φ_c(z²+c) = φ_c(z)²`
on the escape set. Pure `exp`-algebra from `bottcherLog_sum_quadratic` — the branch
ambiguity `log(z²) − 2 log z ∈ 2πiℤ` is annihilated by `exp`, so the squaring identity is
*exact*. This is the conjugacy `φ_c ∘ f_c = (·)² ∘ φ_c` of the dynamics to `w ↦ w²`; it is
the engine of the dyadic monodromy: pulling a branch of `φ_c` back through `f_c` halves it,
and the `2ⁿ` preimages of a base loop carry `2ⁿ`-th-root multipliers. -/
theorem bottcherCoord_quadratic {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    bottcherCoord c (quadratic c z) = (bottcherCoord c z) ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
  have hzsq : z ^ 2 ≠ 0 := pow_ne_zero _ hz0
  have hqc : z ^ 2 + c ≠ 0 := by
    intro h
    have h1 : ‖z‖ ^ 2 = ‖c‖ := by
      have h2 : z ^ 2 = -c := by linear_combination h
      rw [← norm_pow, h2, norm_neg]
    nlinarith [hc, hz, norm_nonneg z, norm_nonneg c]
  have hfrac : (1 : ℂ) + c / z ^ 2 = (z ^ 2 + c) / z ^ 2 := by
    rw [add_div, div_self hzsq]
  have hone : (1 : ℂ) + c / z ^ 2 ≠ 0 := by rw [hfrac]; exact div_ne_zero hqc hzsq
  have ht0 : bottcherLogTerm c z 0 = (2 : ℂ)⁻¹ * Complex.log (1 + c / z ^ 2) := by
    unfold bottcherLogTerm; simp
  have hexp2t0 : Complex.exp (2 * bottcherLogTerm c z 0) = 1 + c / z ^ 2 := by
    rw [ht0, show (2 : ℂ) * ((2 : ℂ)⁻¹ * Complex.log (1 + c / z ^ 2))
        = Complex.log (1 + c / z ^ 2) by ring]
    exact Complex.exp_log hone
  set S := ∑' k, bottcherLogTerm c z k with hS
  set T0 := bottcherLogTerm c z 0 with hT0
  have hLHS : bottcherCoord c (quadratic c z)
      = (z ^ 2 + c) * Complex.exp (2 * S) * (Complex.exp (2 * T0))⁻¹ := by
    unfold bottcherCoord bottcherLog
    rw [bottcherLog_sum_quadratic hc hz, quadratic_apply,
        show Complex.log (z ^ 2 + c) + 2 * (S - T0)
        = Complex.log (z ^ 2 + c) + 2 * S + (-(2 * T0)) by ring,
        Complex.exp_add, Complex.exp_add, Complex.exp_log hqc, Complex.exp_neg]
  have hRHS : (bottcherCoord c z) ^ 2 = z ^ 2 * Complex.exp (2 * S) := by
    unfold bottcherCoord bottcherLog
    rw [← Complex.exp_nat_mul,
        show ((2 : ℕ) : ℂ) * (Complex.log z + S) = 2 * Complex.log z + 2 * S by push_cast; ring,
        Complex.exp_add]
    congr 1
    rw [show (2 : ℂ) * Complex.log z = Complex.log z + Complex.log z by ring,
        Complex.exp_add, Complex.exp_log hz0, sq]
  rw [hLHS, hexp2t0, hRHS, hfrac, inv_div, div_eq_mul_inv,
      show (z ^ 2 + c) * Complex.exp (2 * S) * (z ^ 2 * (z ^ 2 + c)⁻¹)
        = z ^ 2 * Complex.exp (2 * S) * ((z ^ 2 + c) * (z ^ 2 + c)⁻¹) by ring,
      mul_inv_cancel₀ hqc, mul_one]

/-- **Orbit stays in the escape regime.** For `z` beyond radius `2` with `‖c‖ ≤ ‖z‖`, every
iterate satisfies `‖z‖ ≤ ‖f_c^[n] z‖` (the orbit only grows). Hence the escape-regime
hypotheses `‖c‖ ≤ ‖·‖`, `2 < ‖·‖` propagate to all iterates. -/
theorem norm_iterate_ge {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖(quadratic c)^[n] z‖ := by
  have hgrow := quadratic_orbit_growth hc hz n
  have hz1 : (1 : ℝ) ≤ ‖z‖ - 1 := by linarith
  have hge1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ hz1
  nlinarith [hgrow, hge1, norm_nonneg z,
    mul_nonneg (norm_nonneg z) (by linarith [hge1] : (0 : ℝ) ≤ (‖z‖ - 1) ^ n - 1)]

/-- **Iterated functional equation**: `φ_c(f_c^[n] z) = φ_c(z)^(2ⁿ)` on the escape set.
The `n`-fold conjugacy of `f_c` to `w ↦ w²` — here the dyadic `2ⁿ` of the monodromy is
born: a branch of `φ_c` pulled back through `f_c^[n]` is a `2ⁿ`-th root of `φ_c`, so the
deck group over the depth-`n` cylinder is cyclic of order `2ⁿ`. -/
theorem bottcherCoord_iterate {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    bottcherCoord c ((quadratic c)^[n] z) = (bottcherCoord c z) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwz : ‖z‖ ≤ ‖(quadratic c)^[n] z‖ := norm_iterate_ge hc hz n
    have hwc : ‖c‖ ≤ ‖(quadratic c)^[n] z‖ := le_trans hc hwz
    have hw2 : 2 < ‖(quadratic c)^[n] z‖ := lt_of_lt_of_le hz hwz
    rw [Function.iterate_succ', Function.comp_apply, bottcherCoord_quadratic hwc hw2, ih,
        ← pow_mul, pow_succ]

/-- **Branch-free factorization** `φ_c(z) = z · exp(∑ₖ termₖ(z))` for `z ≠ 0`. The `log z` in
`bottcherLog` carries a branch cut, but `exp(log z) = z` removes it: `φ_c` itself is single-valued
and analytic across the slit (everywhere `z ≠ 0` where the series is defined), with the `z`-factor
giving the normalization `φ_c ~ z` at `∞`. -/
theorem bottcherCoord_eq_mul_exp {c z : ℂ} (hz : z ≠ 0) :
    bottcherCoord c z = z * Complex.exp (∑' k, bottcherLogTerm c z k) := by
  unfold bottcherCoord bottcherLog
  rw [Complex.exp_add, Complex.exp_log hz]

/-- **`φ_c` is analytic on all of `escapeOpen`** (not merely the slit neighborhood): via the
branch-free factorization `φ_c = z · exp(∑ₖ termₖ)`, with the series differentiable on `escapeOpen`.
This removes the `slitPlane` restriction from `analyticOnNhd_bottcherCoord`, so contours (e.g. a
circle `C(0,R)` crossing the negative reals) lie in the domain of analyticity. -/
theorem differentiableOn_bottcherCoord (c : ℂ) :
    DifferentiableOn ℂ (bottcherCoord c) (escapeOpen c) := by
  have hg : DifferentiableOn ℂ (fun z => z * Complex.exp (∑' k, bottcherLogTerm c z k))
      (escapeOpen c) :=
    differentiableOn_id.mul ((differentiableOn_bottcherLogSum c).cexp)
  refine hg.congr (fun z hz => ?_)
  obtain ⟨_, hz2⟩ := mem_escapeOpen_regime hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz2; linarith
  exact bottcherCoord_eq_mul_exp hz0

end Bottcher
