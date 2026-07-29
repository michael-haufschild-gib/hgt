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
    apply h2.congr_fderiv
    ext z
    simp
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
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply,
      Complex.reCLM_apply] at h
    rw [← fderiv_apply_one_eq_deriv]
    exact h
  have hdI : (deriv F 0).im = 0 := by
    have h := congrArg (fun L => L Complex.I) hCLM
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply,
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
    rw [ContinuousLinearMap.comp_apply, hy, _root_.zero_apply] at hh
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

namespace Bottcher
open Complex InnerProductSpace

/-- Helper (Cauchy–Riemann): if the ℝ-gradient of `Re∘g` vanishes at `z` and `g` is ℂ-differentiable
there, then the complex derivative `g'(z) = 0`. -/
theorem deriv_eq_zero_of_fderiv_re_eq_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (hfd : fderiv ℝ (fun w => (g w).re) z = 0) :
    deriv g z = 0 := by
  have hcomp : HasFDerivAt (fun w => (g w).re)
      (Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hg.hasFDerivAt.restrictScalars ℝ)
  have hCLM : Complex.reCLM.comp ((fderiv ℂ g z).restrictScalars ℝ) = 0 :=
    hcomp.fderiv.symm.trans hfd
  have hd1 : (deriv g z).re = 0 := by
    have h := congrArg (fun L => L (1:ℂ)) hCLM
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply,
      Complex.reCLM_apply] at h
    rw [← fderiv_apply_one_eq_deriv]; exact h
  have hdI : (deriv g z).im = 0 := by
    have h := congrArg (fun L => L Complex.I) hCLM
    simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply,
      Complex.reCLM_apply] at h
    have h1 : (fderiv ℂ g z) Complex.I = Complex.I • (fderiv ℂ g z) 1 := by
      rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    have hI : (fderiv ℂ g z) Complex.I = Complex.I * deriv g z := by
      rw [h1, fderiv_apply_one_eq_deriv, smul_eq_mul]
    rw [show (((fderiv ℂ g z).restrictScalars ℝ) Complex.I) = (fderiv ℂ g z) Complex.I from rfl,
      hI, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      neg_eq_zero] at h
    exact h
  exact Complex.ext hd1 hdI

/-- **[escape base, step 5] `∇G_c ≠ 0` on `escapeOpen`.** On a ball `B ⊆ escapeOpen` about `z`, `G_c`
has a holomorphic completion `F` (`Re F = G_c`); on `B ∩ slitPlane` both `F` and `bottcherLog` have real
part `G_c`, so `Re(F − bottcherLog) ≡ 0`, forcing `deriv F = logDeriv φ_c` there; identity theorem ⟹
`deriv F = logDeriv φ_c` on all `B`. If `∇G_c(z) = 0` then `deriv F z = 0` (CR), so `logDeriv φ_c z = 0`
— contradicting `logDeriv_bottcherCoord_ne_zero_escape`. So the escape region is regular for `G_c`, the
base case of the critical-point propagation. Axiom-clean. -/
theorem fderiv_greenLimit_ne_zero_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    fderiv ℝ (greenLimit c) z ≠ 0 := by
  obtain ⟨R, hRpos, hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_escapeOpen c).mem_nhds hz)
  have hball0 : z ∈ Metric.ball z R := Metric.mem_ball_self hRpos
  have hUopen : IsOpen (Metric.ball z R ∩ Complex.slitPlane) :=
    Metric.isOpen_ball.inter Complex.isOpen_slitPlane
  have hbasin : Metric.ball z R ⊆ (filledJulia c)ᶜ := by
    intro x hx
    obtain ⟨hc, hx2⟩ := mem_escapeOpen_regime (hsub hx)
    exact not_mem_filledJulia hc hx2
  have hharm : HarmonicOnNhd (greenLimit c) (Metric.ball z R) :=
    fun x hx => harmonicOnNhd_greenLimit_basin c x (hbasin hx)
  obtain ⟨F, hFan, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  have hlogDan : AnalyticOnNhd ℂ (logDeriv (bottcherCoord c)) (Metric.ball z R) := by
    intro x hx
    have hxe : x ∈ escapeOpen c := hsub hx
    have hbc : AnalyticAt ℂ (bottcherCoord c) x :=
      (differentiableOn_bottcherCoord c).analyticAt ((isOpen_escapeOpen c).mem_nhds hxe)
    exact hbc.deriv.div hbc (bottcherCoord_ne_zero c x)
  have hderivFan : AnalyticOnNhd ℂ (deriv F) (Metric.ball z R) := hFan.deriv
  have hagree : Set.EqOn (deriv F) (logDeriv (bottcherCoord c))
      (Metric.ball z R ∩ Complex.slitPlane) := by
    intro w hw
    have hwe : w ∈ escapeOpen c := hsub hw.1
    obtain ⟨hwc, hw2⟩ := mem_escapeOpen_regime hwe
    have hFd : DifferentiableAt ℂ F w := (hFan w hw.1).differentiableAt
    have hBd : DifferentiableAt ℂ (bottcherLog c) w :=
      (differentiableOn_bottcherLog c).differentiableAt
        (((isOpen_escapeOpen c).inter Complex.isOpen_slitPlane).mem_nhds ⟨hwe, hw.2⟩)
    have hreq : fderiv ℝ (fun u => (F u - bottcherLog c u).re) w = 0 := by
      have hev : (fun u => (F u - bottcherLog c u).re) =ᶠ[nhds w] (fun _ => (0:ℝ)) := by
        filter_upwards [hUopen.mem_nhds hw] with u hu
        obtain ⟨huc, hu2⟩ := mem_escapeOpen_regime (hsub hu.1)
        rw [Complex.sub_re, show (F u).re = greenLimit c u from hFre hu.1,
          bottcherLog_re huc hu2, sub_self]
      rw [hev.fderiv_eq]; simp
    have hderivsub := deriv_eq_zero_of_fderiv_re_eq_zero (hFd.sub hBd) hreq
    have hsubz : deriv F w - deriv (bottcherLog c) w = 0 := by
      rw [← deriv_sub hFd hBd]; exact hderivsub
    rw [sub_eq_zero.mp hsubz, ← logDeriv_bottcherCoord_eq ⟨hwe, hw.2⟩]
  obtain ⟨w₀, hw₀ball, hw₀slit⟩ : ∃ w ∈ Metric.ball z R, w ∈ Complex.slitPlane := by
    have hnorm : ‖Complex.I * ((R / 2 : ℝ) : ℂ)‖ = R / 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    rcases eq_or_ne (z.im + R / 2) 0 with h | h
    · refine ⟨z - Complex.I * ((R / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show
          z - Complex.I * ((R / 2 : ℝ) : ℂ) - z = -(Complex.I * ((R / 2 : ℝ) : ℂ)) from by ring,
          norm_neg, hnorm]
        linarith
      · rw [Complex.mem_slitPlane_iff]; right
        simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, one_mul, mul_zero, zero_add]
        intro hcon; linarith
    · refine ⟨z + Complex.I * ((R / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, show
          z + Complex.I * ((R / 2 : ℝ) : ℂ) - z = Complex.I * ((R / 2 : ℝ) : ℂ) from by ring, hnorm]
        linarith
      · rw [Complex.mem_slitPlane_iff]; right
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, one_mul, mul_zero, zero_add]
        exact h
  have heqf : deriv F =ᶠ[nhds w₀] logDeriv (bottcherCoord c) := by
    filter_upwards [hUopen.mem_nhds ⟨hw₀ball, hw₀slit⟩] with u hu using hagree hu
  have hEqOn : Set.EqOn (deriv F) (logDeriv (bottcherCoord c)) (Metric.ball z R) :=
    hderivFan.eqOn_of_preconnected_of_eventuallyEq hlogDan
      (convex_ball z R).isPreconnected hw₀ball heqf
  intro hzero
  have hFre_ev : (fun w => (F w).re) =ᶠ[nhds z] greenLimit c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hball0] with w hw using hFre hw
  have hFda : DifferentiableAt ℂ F z := (hFan z hball0).differentiableAt
  have hderivFz : deriv F z = 0 :=
    deriv_eq_zero_of_fderiv_re_eq_zero hFda (by rw [hFre_ev.fderiv_eq]; exact hzero)
  have hcontra : logDeriv (bottcherCoord c) z = 0 := by rw [← hEqOn hball0]; exact hderivFz
  exact logDeriv_bottcherCoord_ne_zero_escape hz hcontra

end Bottcher

namespace Bottcher
open Complex

/-- **[L4k — the critical value is a regular point] `∇G_c(c) ≠ 0`.** The critical value `c = f_c(0)` is
not a critical point of `G_c`. Its forward orbit `f_c^[n](c) = f_c^[n+1](0)` never hits `0`
(`critical_orbit_ne_zero`) and escapes (`exists_orbit_gt`); were `∇G_c(c) = 0`, the off-`0` propagation
`fderiv_greenLimit_eq_zero_iff_quadratic` would push the critical point all the way out to the escape
region, contradicting `fderiv_greenLimit_ne_zero_escape`. Hence `∇G_c(c) ≠ 0`. Combined with the saddle
model (`exists_holomorphic_completion_critical`, where `F''(0) = F'(c)`), this makes the critical point
`0` a **non-degenerate** saddle: `{G_c = G_c(0)}` is a genuine figure-eight. Axiom-clean. -/
theorem fderiv_greenLimit_ne_zero_critical_value {c : ℂ} (hc : Disconnected c) :
    fderiv ℝ (greenLimit c) (quadratic c 0) ≠ 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hcnf : quadratic c 0 ∉ filledJulia c := by simpa using not_mem_filledJulia_iterate h0 1
  obtain ⟨N, hN⟩ := exists_orbit_gt hcnf (max 2 ‖c‖)
  have hesc : (quadratic c)^[N] (quadratic c 0) ∈ escapeOpen c := by
    rw [escapeOpen, Set.mem_setOf_eq]; exact hN
  intro hzero
  have hforward : ∀ n, fderiv ℝ (greenLimit c) ((quadratic c)^[n] (quadratic c 0)) = 0 := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ k ih =>
      have hjnf : (quadratic c)^[k] (quadratic c 0) ∉ filledJulia c :=
        not_mem_filledJulia_iterate hcnf k
      have hjeq : (quadratic c)^[k] (quadratic c 0) = (quadratic c)^[k + 1] 0 :=
        (Function.iterate_succ_apply (quadratic c) k 0).symm
      have hjne : (quadratic c)^[k] (quadratic c 0) ≠ 0 := by
        rw [hjeq]; exact critical_orbit_ne_zero hc (Nat.succ_le_succ (Nat.zero_le k))
      rw [Function.iterate_succ_apply']
      exact (fderiv_greenLimit_eq_zero_iff_quadratic hjnf hjne).mp ih
  exact fderiv_greenLimit_ne_zero_escape hesc (hforward N)

end Bottcher

namespace Bottcher
open Complex InnerProductSpace

/-- **[L4l — the saddle is non-degenerate] `F''(0) ≠ 0`** for a holomorphic completion `F` of `G_c`
near `0` (`Re F = G_c` on a basin ball). With a conjugate `F_c` of `G_c` near the critical value `c`,
the basin scaling `G_c = ½·G_c∘f_c` gives `Re(F − ½F_c∘f_c) ≡ 0` near `0`, so `deriv F(z) = z·F_c'(z²+c)`
and `F''(0) = F_c'(c) ≠ 0` (since `∇G_c(c) ≠ 0`). The saddle at `0` is order-2: a genuine figure-eight.
Axiom-clean. -/
theorem deriv2_completion_critical_ne_zero {c : ℂ} (hc : Disconnected c) {R : ℝ} (hRpos : 0 < R)
    {F : ℂ → ℂ} (hbasin : Metric.ball 0 R ⊆ (filledJulia c)ᶜ)
    (hFan : AnalyticOnNhd ℂ F (Metric.ball 0 R))
    (hFre : Set.EqOn (fun z => (F z).re) (greenLimit c) (Metric.ball 0 R)) :
    deriv (deriv F) 0 ≠ 0 := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  have hcnf : quadratic c 0 ∉ filledJulia c := by simpa using not_mem_filledJulia_iterate h0 1
  obtain ⟨Rc, hRcpos, hsubc⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds hcnf)
  have hharmc : HarmonicOnNhd (greenLimit c) (Metric.ball (quadratic c 0) Rc) :=
    fun x hx => harmonicOnNhd_greenLimit_basin c x (hsubc hx)
  obtain ⟨Fc, hFcan, hFcre⟩ := hharmc.exists_analyticOnNhd_ball_re_eq
  have hcball : quadratic c 0 ∈ Metric.ball (quadratic c 0) Rc := Metric.mem_ball_self hRcpos
  -- F_c'(c) ≠ 0
  have hFc'c : deriv Fc (quadratic c 0) ≠ 0 := by
    intro hzero
    apply fderiv_greenLimit_ne_zero_critical_value hc
    have hFcre_ev : (fun w => (Fc w).re) =ᶠ[nhds (quadratic c 0)] greenLimit c := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hcball] with w hw using hFcre hw
    rw [← hFcre_ev.fderiv_eq]
    have hFcda : DifferentiableAt ℂ Fc (quadratic c 0) := (hFcan _ hcball).differentiableAt
    have hcomp : HasFDerivAt (fun w => (Fc w).re)
        (Complex.reCLM.comp ((fderiv ℂ Fc (quadratic c 0)).restrictScalars ℝ)) (quadratic c 0) :=
      Complex.reCLM.hasFDerivAt.comp _ (hFcda.hasFDerivAt.restrictScalars ℝ)
    have hfc0 : fderiv ℂ Fc (quadratic c 0) = 0 := by
      apply ContinuousLinearMap.ext_ring
      rw [fderiv_apply_one_eq_deriv, hzero]; rfl
    rw [hcomp.fderiv, hfc0]; simp
  -- small radius
  set r := min R (min Rc 1) with hr
  have hrpos : 0 < r := by rw [hr]; simp [hRpos, hRcpos]
  have hrR : r ≤ R := min_le_left _ _
  have hrle1 : r ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hrRc : r ≤ Rc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hball_sub : Metric.ball (0:ℂ) r ⊆ Metric.ball 0 R := Metric.ball_subset_ball hrR
  have hmaps : ∀ z ∈ Metric.ball (0:ℂ) r, quadratic c z ∈ Metric.ball (quadratic c 0) Rc := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    simp only [sub_zero] at hz
    have hzz : quadratic c z - quadratic c 0 = z ^ 2 := by simp only [quadratic]; ring
    rw [hzz, norm_pow]
    have h1 : ‖z‖ ^ 2 < r ^ 2 := by
      rw [sq, sq]; exact mul_self_lt_mul_self (norm_nonneg z) hz
    nlinarith [h1, hrle1, hrRc, hrpos]
  -- deriv F = z * deriv Fc (quadratic c z) on ball 0 r
  have hderivF : Set.EqOn (deriv F) (fun z => z * deriv Fc (quadratic c z)) (Metric.ball 0 r) := by
    intro w hw
    have hwR : w ∈ Metric.ball 0 R := hball_sub hw
    have hwc : quadratic c w ∈ Metric.ball (quadratic c 0) Rc := hmaps w hw
    have hFw : DifferentiableAt ℂ F w := (hFan w hwR).differentiableAt
    have hqw : DifferentiableAt ℂ (quadratic c) w := (hasStrictDerivAt_quadratic c w).hasDerivAt.differentiableAt
    have hFcfw : DifferentiableAt ℂ (fun u => Fc (quadratic c u)) w :=
      ((hFcan _ hwc).differentiableAt).comp w hqw
    have hreq : fderiv ℝ (fun u => (F u - ((1/2:ℝ):ℂ) * Fc (quadratic c u)).re) w = 0 := by
      have hev : (fun u => (F u - ((1/2:ℝ):ℂ) * Fc (quadratic c u)).re)
          =ᶠ[nhds w] (fun _ => (0:ℝ)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hw] with u hu
        have huR : u ∈ Metric.ball 0 R := hball_sub hu
        have huc : quadratic c u ∈ Metric.ball (quadratic c 0) Rc := hmaps u hu
        have hunf : u ∉ filledJulia c := hbasin huR
        have hF1 : (F u).re = greenLimit c u := hFre huR
        have hFc1 : (Fc (quadratic c u)).re = greenLimit c (quadratic c u) := hFcre huc
        have hgq : greenLimit c (quadratic c u) = 2 * greenLimit c u :=
          greenLimit_quadratic_basin hunf
        show (F u - ((1/2:ℝ):ℂ) * Fc (quadratic c u)).re = 0
        rw [Complex.sub_re, Complex.re_ofReal_mul, hF1, hFc1, hgq]
        ring
      rw [hev.fderiv_eq]; simp
    have hHD : HasDerivAt (fun u => F u - ((1/2:ℝ):ℂ) * Fc (quadratic c u))
        (deriv F w - ((1/2:ℝ):ℂ) * (deriv Fc (quadratic c w) * (2 * w))) w := by
      have hcomp : HasDerivAt (fun u => Fc (quadratic c u))
          (deriv Fc (quadratic c w) * (2 * w)) w :=
        ((hFcan _ hwc).differentiableAt).hasDerivAt.comp w
          (hasStrictDerivAt_quadratic c w).hasDerivAt
      exact hFw.hasDerivAt.sub (hcomp.const_mul ((1/2:ℝ):ℂ))
    have hd0 := deriv_eq_zero_of_fderiv_re_eq_zero hHD.differentiableAt hreq
    rw [hHD.deriv] at hd0
    have heqd : deriv F w = ((1/2:ℝ):ℂ) * (deriv Fc (quadratic c w) * (2 * w)) := by
      linear_combination hd0
    rw [heqd]; push_cast; ring
  -- conclude: F''(0) = F_c'(c)
  have hderivF_ev : deriv F =ᶠ[nhds (0:ℂ)] (fun z => z * deriv Fc (quadratic c z)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) hrpos] with w hw using hderivF hw
  have hgdiff : DifferentiableAt ℂ (fun z => deriv Fc (quadratic c z)) 0 :=
    (((hFcan.deriv) _ hcball).differentiableAt).comp 0
      (hasStrictDerivAt_quadratic c 0).hasDerivAt.differentiableAt
  rw [hderivF_ev.deriv_eq]
  have hHD2 : HasDerivAt (fun z => z * deriv Fc (quadratic c z)) (deriv Fc (quadratic c 0)) 0 := by
    have h := (hasDerivAt_id (0:ℂ)).mul hgdiff.hasDerivAt
    rw [show (fun z => z * deriv Fc (quadratic c z)) =
        id * (fun z => deriv Fc (quadratic c z)) by
      funext z
      rfl]
    apply h.congr_deriv
    simp
  rw [hHD2.deriv]; exact hFc'c

end Bottcher

namespace Bottcher
open Complex

/-- **[normal form, step 1] A nonvanishing analytic function has a local analytic square root.** -/
theorem exists_analyticAt_sq_eq {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧ ∀ᶠ z in nhds z₀, h z ^ 2 = g z := by
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = g z₀ :=
    IsAlgClosed.exists_pow_nat_eq (g z₀) (by norm_num)
  have hsne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; exact hg0 hs.symm
  set q : ℂ → ℂ := fun z => g z / g z₀ with hq
  have hqan : AnalyticAt ℂ q z₀ := hg.div analyticAt_const hg0
  have hq0 : q z₀ = 1 := by rw [hq]; field_simp
  have hmem : ∀ᶠ z in nhds z₀, q z ∈ Metric.ball (1:ℂ) 1 := by
    have hcont : ContinuousAt q z₀ := hqan.continuousAt
    have hball : Metric.ball (1:ℂ) 1 ∈ nhds (q z₀) := by
      rw [hq0]; exact Metric.ball_mem_nhds _ one_pos
    exact hcont.preimage_mem_nhds hball
  have hslit : Metric.ball (1:ℂ) 1 ⊆ Complex.slitPlane := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hb : |w.re - 1| ≤ ‖w - 1‖ := by
      calc |w.re - 1| = |(w - 1).re| := by rw [Complex.sub_re, Complex.one_re]
        _ ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
    have hlt := abs_lt.mp (lt_of_le_of_lt hb hw)
    linarith [hlt.1]
  refine ⟨fun z => s * Complex.exp ((2:ℂ)⁻¹ * Complex.log (q z)), ?_, ?_, ?_⟩
  · have hld : DifferentiableOn ℂ Complex.log Complex.slitPlane :=
      fun x hx => (Complex.hasDerivAt_log hx).differentiableAt.differentiableWithinAt
    have hla : AnalyticAt ℂ Complex.log (q z₀) :=
      (hld.analyticOnNhd Complex.isOpen_slitPlane) (q z₀)
        (hslit (by rw [hq0]; exact Metric.mem_ball_self one_pos))
    have hlogan : AnalyticAt ℂ (fun z => Complex.log (q z)) z₀ := hla.comp hqan
    exact analyticAt_const.mul ((analyticAt_const.mul hlogan).cexp)
  · show s * Complex.exp ((2:ℂ)⁻¹ * Complex.log (q z₀)) ≠ 0
    rw [hq0, Complex.log_one, mul_zero, Complex.exp_zero, mul_one]; exact hsne
  · filter_upwards [hmem] with z hz
    have hqz0 : q z ≠ 0 := by
      intro hz0
      rw [hz0, Metric.mem_ball, dist_eq_norm] at hz
      simp at hz
    have hqval : q z = g z / g z₀ := rfl
    rw [mul_pow, pow_two (Complex.exp ((2:ℂ)⁻¹ * Complex.log (q z))), ← Complex.exp_add,
      show (2:ℂ)⁻¹ * Complex.log (q z) + (2:ℂ)⁻¹ * Complex.log (q z) = Complex.log (q z) by ring,
      Complex.exp_log hqz0, hqval, hs]
    field_simp

/-- **[normal form, step 2] Order-2 factorization.** An analytic `F` with `F'(0)=0`, `F''(0)≠0`
factors near `0` as `F z − F 0 = z² · G z` with `G` analytic, `G 0 = ½F''(0) ≠ 0`. (Taylor to order 3:
the order-0 and order-1 coefficients vanish, the order-2 coefficient is `½F''(0)`.) -/
theorem exists_factor_order_two {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF'0 : deriv F 0 = 0) (hF''0 : deriv (deriv F) 0 ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 ≠ 0 ∧ ∀ᶠ z in nhds 0, F z - F 0 = z ^ 2 * G z := by
  set d : ℂ → ℂ := fun z => F z - F 0 with hd
  have hdan : AnalyticAt ℂ d 0 := hF.sub analyticAt_const
  obtain ⟨F₃, hF₃an, hF₃⟩ := hdan.exists_eventuallyEq_sum_add_pow_mul 3
  have hdd : deriv d = deriv F := by funext z; exact deriv_sub_const (F 0)
  have hid0 : iteratedDeriv 0 d 0 = 0 := by rw [iteratedDeriv_zero]; simp [hd]
  have hid1 : iteratedDeriv 1 d 0 = 0 := by rw [iteratedDeriv_one, hdd]; exact hF'0
  have hid2 : iteratedDeriv 2 d 0 = deriv (deriv F) 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hdd]
  refine ⟨fun z => (deriv (deriv F) 0) / 2 + z * F₃ z, ?_, ?_, ?_⟩
  · exact analyticAt_const.add (analyticAt_id.mul hF₃an)
  · show deriv (deriv F) 0 / 2 + (0:ℂ) * F₃ 0 ≠ 0
    rw [zero_mul, add_zero]; exact div_ne_zero hF''0 two_ne_zero
  · filter_upwards [hF₃] with z hz
    rw [show F z - F 0 = d z from rfl, hz]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hid0, hid1, hid2,
      smul_eq_mul, mul_zero, zero_add, add_zero, Nat.factorial_zero,
      Nat.factorial_one, pow_zero, pow_one]
    push_cast [Nat.factorial]
    ring

/-- **[normal form, step 3] Local `√` normal form.** An analytic `F` with `F'(0)=0`, `F''(0)≠0` has a
local biholomorphic coordinate `h` (`h 0 = 0`, `h'(0) ≠ 0`) with `F z − F 0 = h(z)²` near `0`. So the
critical point is the standard saddle `w ↦ w²`: the figure-eight `{Re(F−F(0)) = 0}` is `h⁻¹{Re w² = 0}`
(two arcs) and the sublevel `{Re(F−F(0)) < 0}` is `h⁻¹{Re w² < 0}` (two lobes). The local model from
which the disconnected basin's two-lobe split is read. Axiom-clean. -/
theorem exists_sq_normal_form {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF'0 : deriv F 0 = 0) (hF''0 : deriv (deriv F) 0 ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 ≠ 0 ∧
      ∀ᶠ z in nhds 0, F z - F 0 = (h z) ^ 2 := by
  obtain ⟨G, hGan, hG0, hGeq⟩ := exists_factor_order_two hF hF'0 hF''0
  obtain ⟨s, hsan, hs0, hseq⟩ := exists_analyticAt_sq_eq hGan hG0
  refine ⟨fun z => z * s z, analyticAt_id.mul hsan, by simp, ?_, ?_⟩
  · have hHD : HasDerivAt (fun z => z * s z) (s 0) 0 := by
      have h := (hasDerivAt_id (0:ℂ)).mul hsan.differentiableAt.hasDerivAt
      rw [show (fun z => z * s z) = id * s by
        funext z
        rfl]
      apply h.congr_deriv
      simp
    rw [hHD.deriv]; exact hs0
  · filter_upwards [hGeq, hseq] with z hz1 hz2
    rw [hz1, ← hz2]; ring

end Bottcher

namespace Bottcher
open Complex

/-- **[component split, step 1] `Re(w²) < 0 ↔ |Re w| < |Im w|`.** The sublevel set of the saddle model
`w ↦ Re(w²)` is the open double cone `{|Re w| < |Im w|}` — two half-cones (`Im w > |Re w|` and
`Im w < −|Re w|`) meeting only at `0`. This is what makes `{Re w² < 0}` disconnected, hence (pulled back
by the normal-form biholomorphism) the two Cantor lobes of the disconnected basin. Axiom-clean. -/
theorem re_sq_neg_iff (w : ℂ) : (w ^ 2).re < 0 ↔ |w.re| < |w.im| := by
  rw [sq, Complex.mul_re]
  constructor
  · intro h
    nlinarith [abs_mul_abs_self w.re, abs_mul_abs_self w.im, abs_nonneg w.re, abs_nonneg w.im, h]
  · intro h
    nlinarith [abs_mul_abs_self w.re, abs_mul_abs_self w.im, abs_nonneg w.re, abs_nonneg w.im, h]

/-- **[component split, step 2] The sublevel set in the normal-form coordinate.** Given the `√` normal
form `F z − c₀ = (h z)²` near `0`, the sublevel set `{Re(F − c₀) < 0}` coincides near `0` with the
preimage of the open double cone `{|Re w| < |Im w|}` under `h`. Since `h` is a local biholomorphism
(`deriv h 0 ≠ 0`) and the double cone has two components, the sublevel set near `0` has two components —
the two lobes. Axiom-clean. -/
theorem sublevel_eq_preimage_doublecone {F h : ℂ → ℂ} {c₀ : ℂ}
    (heq : ∀ᶠ z in nhds (0:ℂ), F z - c₀ = (h z) ^ 2) :
    ∀ᶠ z in nhds (0:ℂ), ((F z - c₀).re < 0 ↔ |(h z).re| < |(h z).im|) := by
  filter_upwards [heq] with z hz
  rw [hz]; exact re_sq_neg_iff (h z)

end Bottcher

namespace Bottcher
open Complex

/-- **[component split, step 4] The two lobes are genuinely populated.** A local biholomorphism `h`
(`h 0 = 0`, `deriv h 0 ≠ 0`) is an open map at `0` (inverse function theorem,
`exists_openPartialHomeomorph_of_hasStrictDerivAt`), so its image covers a neighborhood of `0`. Hence in
any neighborhood `U` of `0` there are points `zp, zm` with `h zp = i·δ`, `h zm = −i·δ` (small `δ > 0`):
one in each half-cone `{|Re w| < |Im w|}` (`Im(h zp}) > 0`, `Im(h zm) < 0`). Together with
`sublevel_eq_preimage_doublecone` these are points in the two distinct lobes of `{Re(F−F(0)) < 0}`. The
final analytic input separating the disconnected basin's two Cantor halves. Axiom-clean. -/
theorem exists_two_lobe_points {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 0) (hh'0 : deriv h 0 ≠ 0)
    {U : Set ℂ} (hU : U ∈ nhds (0:ℂ)) :
    ∃ zp ∈ U, ∃ zm ∈ U, 0 < (h zp).im ∧ |(h zp).re| < |(h zp).im|
      ∧ (h zm).im < 0 ∧ |(h zm).re| < |(h zm).im| := by
  have hsd : HasStrictDerivAt h (deriv h 0) 0 := hh.hasStrictDerivAt
  obtain ⟨φ, h0src, hφeq⟩ := exists_openPartialHomeomorph_of_hasStrictDerivAt hsd hh'0
  have hφ0 : φ 0 = 0 := by rw [hφeq]; exact hh0
  have h0tgt : (0:ℂ) ∈ φ.target := hφ0 ▸ φ.map_source h0src
  have htgt_nhds : φ.target ∈ nhds (0:ℂ) := φ.open_target.mem_nhds h0tgt
  have hsymm0 : φ.symm 0 = 0 := by
    have hli := φ.left_inv h0src; rwa [hφ0] at hli
  have hsymm_cont : ContinuousAt φ.symm 0 := φ.continuousAt_symm h0tgt
  have hboth : φ.target ∩ φ.symm ⁻¹' U ∈ nhds (0:ℂ) :=
    Filter.inter_mem htgt_nhds (hsymm_cont.preimage_mem_nhds (by rw [hsymm0]; exact hU))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hboth
  have hnorm : ∀ a : ℝ, ‖Complex.I * (a : ℂ)‖ = |a| := by
    intro a; rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hmem : ∀ a : ℝ, |a| < δ → (Complex.I * (a : ℂ)) ∈ φ.target ∩ φ.symm ⁻¹' U := by
    intro a ha
    apply hδ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]; exact ha
  have hval : ∀ a : ℝ, |a| < δ → h (φ.symm (Complex.I * (a : ℂ))) = Complex.I * (a : ℂ) := by
    intro a ha
    rw [← hφeq]; exact φ.right_inv (hmem a ha).1
  have hδ2 : |(δ / 2 : ℝ)| < δ := by rw [abs_of_pos (by linarith)]; linarith
  have hδ2' : |(-(δ / 2) : ℝ)| < δ := by rw [abs_of_neg (by linarith), neg_neg]; linarith
  refine ⟨φ.symm (Complex.I * ((δ / 2 : ℝ) : ℂ)), (hmem _ hδ2).2,
    φ.symm (Complex.I * ((-(δ / 2) : ℝ) : ℂ)), (hmem _ hδ2').2, ?_, ?_, ?_, ?_⟩
  · rw [hval _ hδ2]; simp; linarith
  · rw [hval _ hδ2]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, zero_mul, one_mul, mul_zero, sub_zero, zero_add, abs_zero]
    rw [abs_of_pos (by linarith : (0:ℝ) < δ / 2)]; linarith
  · rw [hval _ hδ2']; simp; linarith
  · rw [hval _ hδ2']
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, zero_mul, one_mul, mul_zero, sub_zero, zero_add, abs_zero,
      abs_neg]
    rw [abs_of_pos (by linarith : (0:ℝ) < δ / 2)]; linarith

end Bottcher
