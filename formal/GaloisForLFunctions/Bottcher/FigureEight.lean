/-
# Böttcher tower — the disconnected-basin figure-eight / component structure (L4)

The disconnected case turns on a fact that the connected case lacks: for `c ∉ M` the escaping critical
point `0` is a *critical point of the Green's function* `G_c`, sitting at a positive level `G_c(0) > 0`.
That critical point is the saddle whose level set `{G_c = G_c(0)}` is a figure-eight; below it the
sub-level basin splits into the two Cantor lobes that the dyadic monodromy winds around. This file builds
that structure from the harmonic `G_c` (`harmonicOnNhd_greenLimit_basin`) and the basin scaling law
`G_c(f_c z) = 2·G_c(z)`, upward toward the winding loop around a single component (the `2πi/2ⁿ` period
of `φ_{c₁}`) that, paired with `pathInt_dlog_lift_closed_eq_zero` (the loop fixes `φ_{c₂}`), assembles
the monodromy automorphism `σ_n` discharging `hDisc`.
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import GaloisForLFunctions.Bottcher.Winding
import GaloisForLFunctions.Bottcher.CoverConstruction

open Complex

namespace Bottcher

/-- **[L4a — the branch point] The escaping critical point `0` is a critical point of `G_c`.**
For disconnected `c` (`0 ∉ K_c`), the Green's function has vanishing gradient at the critical point:
`fderiv ℝ (G_c) 0 = 0`. Reason: `G_c(z) = ½·G_c(f_c z)` near `0` (the basin scaling law), and
`f_c'(0) = 2·0 = 0`, so the chain rule kills the derivative — `fderiv G_c 0 = ½·(fderiv G_c c)∘(f_c'(0))
= 0`. This is the saddle of the harmonic `G_c`: the level set `{G_c = G_c(0)}` passes through `0` as a
figure-eight, and it is exactly *because* `0` escapes (`c ∉ M`) that this critical point sits at a
positive level `G_c(0) > 0`, splitting the sub-level basin into the two Cantor lobes the dyadic
monodromy winds around. The seed of the whole disconnected component structure. Axiom-clean. -/
theorem fderiv_greenLimit_critical {c : ℂ} (hc : Disconnected c) :
    fderiv ℝ (greenLimit c) 0 = 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hc0 : quadratic c 0 ∉ filledJulia c := by
    simpa using not_mem_filledJulia_iterate h0 1
  have hdiffc : DifferentiableAt ℝ (greenLimit c) (quadratic c 0) :=
    (harmonicOnNhd_greenLimit_basin c (quadratic c 0) hc0).1.differentiableAt (by norm_num)
  have hfd : HasFDerivAt (quadratic c) (0 : ℂ →L[ℝ] ℂ) 0 := by
    have hd : HasDerivAt (quadratic c) 0 0 := by
      simpa using (hasStrictDerivAt_quadratic c 0).hasDerivAt
    have h2 := hd.hasFDerivAt.restrictScalars ℝ
    convert h2 using 1
    ext z; simp
  have hcomp : HasFDerivAt (greenLimit c ∘ quadratic c) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have := hdiffc.hasFDerivAt.comp 0 hfd
    rwa [ContinuousLinearMap.comp_zero] at this
  have heq : greenLimit c =ᶠ[nhds (0:ℂ)] (fun z => (2:ℝ)⁻¹ * greenLimit c (quadratic c z)) := by
    filter_upwards [(isClosed_filledJulia c).isOpen_compl.mem_nhds h0] with w hw
    show greenLimit c w = (2:ℝ)⁻¹ * greenLimit c (quadratic c w)
    rw [greenLimit_quadratic_basin hw]; ring
  rw [heq.fderiv_eq]
  have hfinal : HasFDerivAt (fun z => (2:ℝ)⁻¹ * greenLimit c (quadratic c z))
      ((2:ℝ)⁻¹ • (0 : ℂ →L[ℝ] ℝ)) 0 := hcomp.const_mul (2:ℝ)⁻¹
  rw [hfinal.fderiv, smul_zero]

end Bottcher

namespace Bottcher
open Complex

/-- **[Winding value] A depth-`n` lifted loop carries the dyadic period `2πi/2ⁿ`.** If `γ` is a loop in
the escape set whose `n`-fold image `f_c^[n] ∘ γ` traces a contour of total `d log φ_c`-period `2πi`
(the base period, `circleIntegral_dlog_bottcher`), then `γ` itself has period `2πi/2ⁿ`. This is the
exact order-`2ⁿ` monodromy multiplier exponent: continuing `φ_{c₁}` around `γ` multiplies it by
`exp(2πi/2ⁿ) = ζ_{2ⁿ}`. Pure consequence of the `n`-fold period scaling `pathInt_iterate_comp`
(`∮_{f^[n]∘γ} = 2ⁿ ∮_γ`). Together with `pathInt_dlog_lift_closed_eq_zero` (the same loop fixes
`φ_{c₂}`), this is the full monodromy datum `σ_n F = ζF, σ_n G = G` — and the algebraic shadow of
"`φ_{c₁}∘f^[n]` is not a square in `meroField`", the Kummer-irreducibility input. Axiom-clean. -/
theorem winding_value_of_iterate_loop {c : ℂ} (n : ℕ) {γ γ' : ℝ → ℂ}
    (hmem : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi), γ θ ∈ escapeOpen c)
    (hbase : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (bottcherCoord c) ((quadratic c)^[n] (γ θ))
          * (2 ^ n * (∏ k ∈ Finset.range n, (quadratic c)^[k] (γ θ)) * γ' θ))
      = 2 * Real.pi * Complex.I) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (γ θ) * γ' θ)
      = 2 * Real.pi * Complex.I / 2 ^ n := by
  have h := pathInt_iterate_comp (γ' := γ') n hmem
  rw [hbase] at h
  rw [eq_div_iff (show (2:ℂ) ^ n ≠ 0 from pow_ne_zero n two_ne_zero)]
  linear_combination -h

end Bottcher

namespace Bottcher
open Complex InnerProductSpace

/-- **[L4c — the holomorphic saddle model] Near the critical point `0`, `G_c` is the real part of a
holomorphic `F` with `F'(0) = 0`.** For disconnected `c`, `G_c` is harmonic on a ball about `0`
(`harmonicOnNhd_greenLimit_basin`), so it has a holomorphic completion `F` (`Re F = G_c`) on that ball
(Mathlib's harmonic-conjugate `exists_analyticOnNhd_ball_re_eq`). Since `0` is a critical point of `G_c`
(`fderiv_greenLimit_critical`), the Cauchy–Riemann derivative vanishes: `deriv F 0 = 0`. Thus `F(z) -
F(0) = ½F''(0)z² + O(z³)` — the standard non-degenerate saddle whose level set `{Re F = Re F(0)} =
{G_c = G_c(0)}` is the figure-eight, and below which the basin splits into the two Cantor lobes. This is
the local analytic model the disconnected component structure is read off from. Axiom-clean. -/
theorem exists_holomorphic_completion_critical {c : ℂ} (hc : Disconnected c) :
    ∃ (R : ℝ) (F : ℂ → ℂ), 0 < R ∧ AnalyticOnNhd ℂ F (Metric.ball 0 R) ∧
      Set.EqOn (fun z => (F z).re) (greenLimit c) (Metric.ball 0 R) ∧ deriv F 0 = 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨R, hRpos, hsub⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds h0)
  have hharm : HarmonicOnNhd (greenLimit c) (Metric.ball 0 R) :=
    fun x hx => harmonicOnNhd_greenLimit_basin c x (hsub hx)
  obtain ⟨F, hFan, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  refine ⟨R, F, hRpos, hFan, hFre, ?_⟩
  have hball0 : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hRpos
  have hFda : DifferentiableAt ℂ F 0 := (hFan 0 hball0).differentiableAt
  have hReF_eq : (fun z => (F z).re) =ᶠ[nhds (0:ℂ)] greenLimit c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hball0] with w hw using hFre hw
  have hfd_eq : fderiv ℝ (fun z => (F z).re) 0 = 0 := by
    rw [hReF_eq.fderiv_eq]; exact fderiv_greenLimit_critical hc
  have hcomp : HasFDerivAt (fun z => (F z).re)
      (Complex.reCLM.comp ((fderiv ℂ F 0).restrictScalars ℝ)) 0 :=
    Complex.reCLM.hasFDerivAt.comp 0 (hFda.hasFDerivAt.restrictScalars ℝ)
  have hCLM : Complex.reCLM.comp ((fderiv ℂ F 0).restrictScalars ℝ) = 0 :=
    hcomp.fderiv.symm.trans hfd_eq
  have hd1 : (deriv F 0).re = 0 := by
    have h := congrArg (fun L => L (1:ℂ)) hCLM
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      Complex.reCLM_apply] at h
    rw [← fderiv_apply_one_eq_deriv]
    exact h
  have hdI : (deriv F 0).im = 0 := by
    have h := congrArg (fun L => L Complex.I) hCLM
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
      Complex.reCLM_apply] at h
    have h1 : (fderiv ℂ F 0) Complex.I = Complex.I • (fderiv ℂ F 0) 1 := by
      rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    have hI : (fderiv ℂ F 0) Complex.I = Complex.I * deriv F 0 := by
      rw [h1, fderiv_apply_one_eq_deriv, smul_eq_mul]
    rw [show (((fderiv ℂ F 0).restrictScalars ℝ) Complex.I) = (fderiv ℂ F 0) Complex.I from rfl,
      hI, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      neg_eq_zero] at h
    exact h
  exact Complex.ext hd1 hdI

end Bottcher

namespace Bottcher
open Complex

/-- **[L4d — the critical point is aperiodic] For disconnected `c`, the critical orbit never returns to
`0`: `f_c^[k] 0 ≠ 0` for `k ≥ 1`.** If it did, `0` would be a periodic point, its forward orbit finite
hence bounded, putting `0 ∈ K_c` — contradicting `Disconnected c` (`0 ∉ K_c`). Consequence: `c = f_c(0)`
is **not precritical** (no iterate sends it to `0`), so `logDeriv φ_c(c) ≠ 0`, i.e. the holomorphic
saddle model `F` (`exists_holomorphic_completion_critical`) is **non-degenerate** (`F''(0) = F'(c) ≠ 0`):
the level set `{G_c = G_c(0)}` is an honest figure-eight (exactly two arcs), not a higher monkey-saddle.
Axiom-clean. -/
theorem critical_orbit_ne_zero {c : ℂ} (hc : Disconnected c) {k : ℕ} (hk : 1 ≤ k) :
    (quadratic c)^[k] 0 ≠ 0 := by
  intro hper
  apply hc
  show (0 : ℂ) ∈ filledJulia c
  rw [mem_filledJulia_iff]
  have hper' : ∀ n : ℕ, (quadratic c)^[n] 0 = (quadratic c)^[n % k] 0 := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n k, Function.iterate_add_apply]
    rw [show (quadratic c)^[k * (n / k)] 0 = 0 from by
      rw [Function.iterate_mul]; exact Function.iterate_fixed hper (n / k)]
  have hkpos : 0 < k := hk
  have hsub : Set.range (fun n : ℕ => (quadratic c)^[n] 0) ⊆
      ↑((Finset.range k).image (fun i => (quadratic c)^[i] 0)) := by
    rintro x ⟨n, rfl⟩
    show (quadratic c)^[n] 0 ∈ ↑((Finset.range k).image (fun i => (quadratic c)^[i] 0))
    rw [hper' n]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨n % k, Finset.mem_range.mpr (Nat.mod_lt _ hkpos), rfl⟩)
  exact (((Finset.range k).image (fun i => (quadratic c)^[i] 0)).finite_toSet.subset hsub).isBounded

end Bottcher

namespace Bottcher
open Complex

/-- **[L4e — critical points propagate forward off `0`] For `z₀` in the basin with `z₀ ≠ 0`, `G_c` has a
critical point at `z₀` iff it does at `f_c z₀`.** From the basin scaling `G_c = ½·G_c∘f_c` and the chain
rule: `∇G_c(z₀) = ½·∇G_c(f_c z₀)∘(f_c'(z₀))`, and `f_c'(z₀) = 2z₀` is an invertible ℝ-linear map (since
`z₀ ≠ 0`), so the gradient vanishes at `z₀` iff at `f_c z₀`. Iterating: a critical point of `G_c` whose
forward orbit avoids `0` stays critical out to the escape region — where `∇G_c ≠ 0`. So the critical
points are exactly the precritical orbit; with `critical_orbit_ne_zero` this makes the critical value `c`
a regular point, hence the saddle at `0` non-degenerate. Axiom-clean. -/
theorem fderiv_greenLimit_eq_zero_iff_quadratic {c z₀ : ℂ}
    (hz₀ : z₀ ∉ filledJulia c) (hz0 : z₀ ≠ 0) :
    fderiv ℝ (greenLimit c) z₀ = 0 ↔ fderiv ℝ (greenLimit c) (quadratic c z₀) = 0 := by
  have hfz : quadratic c z₀ ∉ filledJulia c := by
    simpa using not_mem_filledJulia_iterate hz₀ 1
  have hdiff : DifferentiableAt ℝ (greenLimit c) (quadratic c z₀) :=
    (harmonicOnNhd_greenLimit_basin c _ hfz).1.differentiableAt (by norm_num)
  have hd : HasDerivAt (quadratic c) (2 * z₀) z₀ := (hasStrictDerivAt_quadratic c z₀).hasDerivAt
  have hfd := hd.hasFDerivAt.restrictScalars ℝ
  have hcomp := (hdiff.hasFDerivAt.comp z₀ hfd).const_mul (2:ℝ)⁻¹
  have heq : greenLimit c =ᶠ[nhds z₀] (fun y => (2:ℝ)⁻¹ * (greenLimit c ∘ quadratic c) y) := by
    filter_upwards [(isClosed_filledJulia c).isOpen_compl.mem_nhds hz₀] with w hw
    show greenLimit c w = (2:ℝ)⁻¹ * (greenLimit c ∘ quadratic c) w
    simp only [Function.comp_apply]
    rw [greenLimit_quadratic_basin hw]; ring
  rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
  set A := fderiv ℝ (greenLimit c) (quadratic c z₀) with hA
  set Lf := (ContinuousLinearMap.toSpanSingleton ℂ (2 * z₀)).restrictScalars ℝ with hLf
  have hLfapp : ∀ x : ℂ, Lf x = x * (2 * z₀) := by
    intro x; rw [hLf]; simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have h2z0 : (2 * z₀) ≠ 0 := mul_ne_zero two_ne_zero hz0
  constructor
  · intro h
    have hcompzero : A.comp Lf = 0 :=
      (smul_eq_zero.mp h).resolve_left (by norm_num : (2:ℝ)⁻¹ ≠ 0)
    ext y
    have hy : Lf (y * (2 * z₀)⁻¹) = y := by
      rw [hLfapp, mul_assoc, inv_mul_cancel₀ h2z0, mul_one]
    have hh := DFunLike.congr_fun hcompzero (y * (2 * z₀)⁻¹)
    rw [ContinuousLinearMap.comp_apply, hy, ContinuousLinearMap.zero_apply] at hh
    exact hh
  · intro h
    rw [h, ContinuousLinearMap.zero_comp, smul_zero]

end Bottcher

namespace Bottcher
open Complex

/-- **[escape base, step 1] `d log φ_c = z⁻¹ + S'(z)` on ALL of `escapeOpen`** (off the slit too),
where `S(z) = ∑ₖ termₖ` is the analytic correction. From `φ_c = z·exp(S)` (`bottcherCoord_eq_mul_exp`),
`logDeriv φ_c = logDeriv(id) + logDeriv(exp∘S) = z⁻¹ + S'`. Slit-free version of
`logDeriv_bottcherCoord_eq`, needed to bound `d log φ_c` near `∞` (Cauchy estimate on `S'`) and conclude
`d log φ_c ≠ 0` far out — the base case of the critical-point propagation
`fderiv_greenLimit_eq_zero_iff_quadratic`. Axiom-clean. -/
theorem logDeriv_bottcherCoord_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    logDeriv (bottcherCoord c) z
      = z⁻¹ + deriv (fun w => ∑' k, bottcherLogTerm c w k) z := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz2; linarith
  have hSdiff : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm c w k) z :=
    (differentiableOn_bottcherLogSum c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hz)
  have hee : bottcherCoord c =ᶠ[nhds z]
      (fun w => w * Complex.exp (∑' k, bottcherLogTerm c w k)) := by
    filter_upwards [compl_singleton_mem_nhds hz0] with w hw
    exact bottcherCoord_eq_mul_exp (by simpa using hw)
  rw [logDeriv_apply, hee.deriv_eq, hee.eq_of_nhds, ← logDeriv_apply]
  have hmul : logDeriv (fun w => w * Complex.exp (∑' k, bottcherLogTerm c w k)) z
      = logDeriv (fun w => w) z
        + logDeriv (fun w => Complex.exp (∑' k, bottcherLogTerm c w k)) z :=
    logDeriv_mul z hz0 (Complex.exp_ne_zero _) differentiableAt_id hSdiff.cexp
  rw [hmul]
  congr 1
  · rw [logDeriv_apply, deriv_id'', one_div]
  · rw [logDeriv_apply, (hSdiff.hasDerivAt.cexp).deriv, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one]

end Bottcher

namespace Bottcher
open Complex

/-- **[escape base, step 2] Cauchy estimate on `S'`: `‖S'(z)‖ ≤ 16‖c‖/‖z‖³` for `‖z‖ > 2·max(2,‖c‖)`.**
On the ball `B(z, R=‖z‖/2)` (⊆ `escapeOpen`), `‖S(w)‖ ≤ 2‖c‖/‖w‖² ≤ 2‖c‖/R²`
(`norm_bottcherLog_sub_log_le`), so the Cauchy derivative estimate
`norm_deriv_le_of_forall_mem_sphere_norm_le` gives `‖S'(z)‖ ≤ (2‖c‖/R²)/R = 16‖c‖/‖z‖³`. With
`logDeriv φ_c = z⁻¹ + S'` this yields `d log φ_c ≠ 0` once `‖z‖² > 16‖c‖`. Axiom-clean. -/
theorem norm_deriv_bottcherLogSum_le {c z : ℂ} (hz : 2 * max 2 ‖c‖ < ‖z‖) :
    ‖deriv (fun w => ∑' k, bottcherLogTerm c w k) z‖ ≤ 16 * ‖c‖ / ‖z‖ ^ 3 := by
  have hmaxpos : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hzpos : 0 < ‖z‖ := by nlinarith
  set R := ‖z‖ / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hmaxlt : max 2 ‖c‖ < R := by rw [hRdef]; linarith
  have hsub : Metric.closedBall z R ⊆ escapeOpen c := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [escapeOpen, Set.mem_setOf_eq]
    have h1 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    linarith
  have hdiff : DiffContOnCl ℂ (fun w => ∑' k, bottcherLogTerm c w k) (Metric.ball z R) :=
    ⟨(differentiableOn_bottcherLogSum c).mono (Metric.ball_subset_closedBall.trans hsub),
     ((differentiableOn_bottcherLogSum c).mono hsub).continuousOn.mono
        Metric.closure_ball_subset_closedBall⟩
  have hC : ∀ w ∈ Metric.sphere z R, ‖(fun w => ∑' k, bottcherLogTerm c w k) w‖
      ≤ 2 * ‖c‖ / R ^ 2 := by
    intro w hw
    show ‖∑' k, bottcherLogTerm c w k‖ ≤ 2 * ‖c‖ / R ^ 2
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hwge : R ≤ ‖w‖ := by
      have h1 := norm_sub_norm_le z w
      rw [norm_sub_rev, hw] at h1
      linarith
    have hwc : ‖c‖ ≤ ‖w‖ := le_trans (le_max_right _ _) (le_of_lt (lt_of_lt_of_le hmaxlt hwge))
    have hw2 : 2 < ‖w‖ := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hmaxlt) hwge
    have hbound := norm_bottcherLog_sub_log_le hwc hw2
    have heq : (∑' k, bottcherLogTerm c w k) = bottcherLog c w - Complex.log w := by
      unfold bottcherLog; ring
    rw [heq]
    refine le_trans hbound ?_
    gcongr
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdiff hC
  refine le_trans hcauchy (le_of_eq ?_)
  rw [hRdef]
  field_simp
  ring

end Bottcher

namespace Bottcher
open Complex

/-- **[escape base, step 3] `d log φ_c ≠ 0` far out.** For `‖z‖ > 2·max(2,‖c‖)` and `‖z‖² > 16‖c‖`:
`logDeriv φ_c z = z⁻¹ + S'(z)` with `‖z⁻¹‖ = 1/‖z‖` strictly bigger than `‖S'(z)‖ ≤ 16‖c‖/‖z‖³`, so the
sum is nonzero — the pole `z⁻¹` dominates the analytic correction at `∞`. Axiom-clean. -/
theorem logDeriv_bottcherCoord_ne_zero_far {c z : ℂ}
    (h1 : 2 * max 2 ‖c‖ < ‖z‖) (h2 : 16 * ‖c‖ < ‖z‖ ^ 2) :
    logDeriv (bottcherCoord c) z ≠ 0 := by
  have hm : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hzpos : 0 < ‖z‖ := by linarith
  have hesc : z ∈ escapeOpen c := by
    rw [escapeOpen, Set.mem_setOf_eq]; linarith
  rw [logDeriv_bottcherCoord_escape hesc]
  intro hzero
  have hSeq : deriv (fun w => ∑' k, bottcherLogTerm c w k) z = -z⁻¹ := by
    linear_combination hzero
  have hSbound := norm_deriv_bottcherLogSum_le h1
  rw [hSeq, norm_neg, norm_inv] at hSbound
  have hkey : ‖z‖ ^ 2 ≤ 16 * ‖c‖ := by
    have hz3 : (0:ℝ) < ‖z‖ ^ 3 := by positivity
    have h := (le_div_iff₀ hz3).mp hSbound
    have heqsimp : ‖z‖⁻¹ * ‖z‖ ^ 3 = ‖z‖ ^ 2 := by
      rw [inv_mul_eq_div, eq_comm, eq_div_iff hzpos.ne']; ring
    rwa [heqsimp] at h
  linarith [hkey, h2]

end Bottcher

namespace Bottcher
open Complex

/-- **[escape base, step 4] `d log φ_c ≠ 0` on ALL of `escapeOpen`.** The orbit `f_c^[N] z` escapes past
any threshold (`exists_orbit_gt`); at a deep enough iterate `d log φ_c ≠ 0`
(`logDeriv_bottcherCoord_ne_zero_far`), and the forward-invariance of the zero set
(`logDeriv_bottcherCoord_iterate_eq_zero_iff`) pulls that back to `z`. So `φ_c` is a local
biholomorphism everywhere on the escape region — the base case from which critical points of `G_c`
propagate (`fderiv_greenLimit_eq_zero_iff_quadratic`). Axiom-clean. -/
theorem logDeriv_bottcherCoord_ne_zero_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    logDeriv (bottcherCoord c) z ≠ 0 := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  have hznf : z ∉ filledJulia c := not_mem_filledJulia hc hz2
  obtain ⟨N, hN⟩ := exists_orbit_gt hznf (2 * max 2 ‖c‖ + 16 * ‖c‖ + 2)
  set w := (quadratic c)^[N] z with hw
  have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hmax : (2:ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
  have h1far : 2 * max 2 ‖c‖ < ‖w‖ := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hge1 : 1 < ‖w‖ := by linarith
  have h16 : 16 * ‖c‖ < ‖w‖ := by linarith
  have h2far : 16 * ‖c‖ < ‖w‖ ^ 2 := by nlinarith [hge1, h16, hwpos]
  intro hzero
  rw [logDeriv_bottcherCoord_iterate_eq_zero_iff hz N] at hzero
  exact logDeriv_bottcherCoord_ne_zero_far h1far h2far hzero

end Bottcher
