/-
# Reflection across a general analytic modulus-one arc

The interface the smooth-piece rigidity discharge consumes.  For an analytic `g` with
`deriv g z₀ ≠ 0` and `‖g z₀‖ = 1`, a function `f` continuous near `z₀` and holomorphic off the
modulus-one arc `{‖g z‖ = 1}` is holomorphic at `z₀`.

Proof: `g` is a local biholomorphism at `z₀` (holomorphic inverse-function theorem,
`exists_localInverse_of_continuation`).  Rotating by `ρ = (g z₀)⁻¹` places `g z₀` at `1` in the slit
plane, so `ψ = log(ρ·g)` is a partial biholomorphism carrying the arc `{‖g z‖ = 1}` to the straight
line `{(I·ψ z).im = 0}`, and `differentiableOn_of_off_biholom_preimage_line` reflects `f` across it.
In the smooth-piece application `g = wfam k` (a branch of the fibre polynomial, analytic across the
Julia frontier) and `f` is the piecewise Böttcher continuation; the resulting holomorphy at `z₀` is a
`ContinuesAcross` witness contradicting the natural boundary in the one-sided case.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.OpenMapping
import GaloisForLFunctions.Bottcher.SchwarzReflection
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction

open Complex Set Filter Topology

namespace Bottcher

/-- **Reflection across a general analytic modulus-one arc.**  If `g` is analytic at `z₀` with
`deriv g z₀ ≠ 0` and `‖g z₀‖ = 1`, and `f` is continuous near `z₀` and holomorphic wherever
`‖g z‖ ≠ 1` near `z₀`, then `f` is holomorphic at `z₀`. -/
theorem differentiableAt_of_off_modulus_arc
    {f g : ℂ → ℂ} {z₀ : ℂ}
    (hgAt : AnalyticAt ℂ g z₀) (hd0 : deriv g z₀ ≠ 0) (hmod : ‖g z₀‖ = 1)
    (hfcont : ∀ᶠ z in 𝓝 z₀, ContinuousAt f z)
    (hfoff : ∀ᶠ z in 𝓝 z₀, ‖g z‖ ≠ 1 → DifferentiableAt ℂ f z) :
    AnalyticAt ℂ f z₀ := by
  classical
  have hgz0 : g z₀ ≠ 0 := by rw [← norm_ne_zero_iff, hmod]; norm_num
  set ρ : ℂ := (g z₀)⁻¹ with hρ
  have hρ0 : ρ ≠ 0 := inv_ne_zero hgz0
  have hρg0 : ρ * g z₀ = 1 := by rw [hρ]; field_simp
  have hρnorm : ‖ρ‖ = 1 := by rw [hρ, norm_inv, hmod, inv_one]
  -- local inverse of `g`
  obtain ⟨γ, hγAn, hγg, _hgγ⟩ := exists_localInverse_of_continuation hgAt hd0
  have hgCont : ContinuousAt g z₀ := hgAt.continuousAt
  -- gather the neighborhood facts and extract a common ball `V`
  have hev_gAn : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hgAt.eventually_analyticAt
  have hev_slit : ∀ᶠ z in 𝓝 z₀, ρ * g z ∈ Complex.slitPlane := by
    have hc : ContinuousAt (fun z => ρ * g z) z₀ := by fun_prop
    exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds
      (by rw [hρg0]; exact Complex.one_mem_slitPlane))
  have hev_γAn : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ γ (g z) :=
    hgCont.eventually hγAn.eventually_analyticAt
  have hev := hev_gAn.and (hev_slit.and (hγg.and (hev_γAn.and (hfcont.and hfoff))))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set V : Set ℂ := Metric.ball z₀ δ with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball
  have hVc : IsPreconnected V := (convex_ball z₀ δ).isPreconnected
  have hz₀V : z₀ ∈ V := Metric.mem_ball_self hδ
  have hV : ∀ z ∈ V, AnalyticAt ℂ g z ∧ ρ * g z ∈ Complex.slitPlane ∧ γ (g z) = z ∧
      AnalyticAt ℂ γ (g z) ∧ ContinuousAt f z ∧ (‖g z‖ ≠ 1 → DifferentiableAt ℂ f z) :=
    fun z hz => hball (Metric.mem_ball.mp hz)
  -- the biholomorphism data
  set ψ : ℂ → ℂ := fun z => Complex.log (ρ * g z) with hψdef
  set ψinv : ℂ → ℂ := fun w => γ (ρ⁻¹ * Complex.exp w) with hψinvdef
  have hgznorm : ∀ z ∈ V, ρ * g z ≠ 0 := fun z hz => Complex.slitPlane_ne_zero (hV z hz).2.1
  have hψDiff : DifferentiableOn ℂ ψ V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (fun z => ρ * g z) z := by
      have := (hV z hz).1; fun_prop
    exact (Complex.differentiableAt_log (hV z hz).2.1).comp z h1
  have hψAn : AnalyticOnNhd ℂ ψ V := hψDiff.analyticOnNhd hVo
  have hleft : ∀ z ∈ V, ψinv (ψ z) = z := by
    intro z hz
    simp only [hψinvdef, hψdef]
    rw [Complex.exp_log (hgznorm z hz), show ρ⁻¹ * (ρ * g z) = g z from by field_simp]
    exact (hV z hz).2.2.1
  have hVimg : IsOpen (ψ '' V) := by
    rcases hψAn.is_constant_or_isOpen hVc with hconst | hopen
    · rcases V.eq_empty_or_nonempty with hVe | _hVne
      · simp [hVe]
      · exfalso
        obtain ⟨c, hc⟩ := hconst
        obtain ⟨ε, hε, hballV⟩ := Metric.isOpen_iff.mp hVo z₀ hz₀V
        set p : ℂ := z₀ + ((ε / 2 : ℝ) : ℂ) with hp
        have hpmem : p ∈ Metric.ball z₀ ε := by
          have hd2 : p - z₀ = ((ε / 2 : ℝ) : ℂ) := by rw [hp]; ring
          rw [Metric.mem_ball, Complex.dist_eq, hd2, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          linarith
        have hpV : p ∈ V := hballV hpmem
        have e1 : ψinv c = z₀ := by rw [← hc z₀ hz₀V]; exact hleft z₀ hz₀V
        have e2 : ψinv c = p := by rw [← hc p hpV]; exact hleft p hpV
        have hpz : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ := by rw [← hp, ← e2, e1]
        have hz : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination hpz
        rw [Complex.ofReal_eq_zero] at hz; linarith
    · exact hopen V subset_rfl hVo
  have hψinvDiff : DifferentiableOn ℂ ψinv (ψ '' V) := by
    rintro w ⟨z, hz, rfl⟩
    apply DifferentiableAt.differentiableWithinAt
    have hval : ρ⁻¹ * Complex.exp (ψ z) = g z := by
      simp only [hψdef]; rw [Complex.exp_log (hgznorm z hz)]; field_simp
    have hγat : DifferentiableAt ℂ γ (ρ⁻¹ * Complex.exp (ψ z)) := by
      rw [hval]; exact (hV z hz).2.2.2.1.differentiableAt
    have hinner : DifferentiableAt ℂ (fun w => ρ⁻¹ * Complex.exp w) (ψ z) := by fun_prop
    exact hγat.comp (ψ z) hinner
  have hset : V ∩ {z : ℂ | (I * ψ z + 0).im ≠ 0} = V ∩ {z : ℂ | ‖g z‖ ≠ 1} := by
    ext z
    simp only [mem_inter_iff, mem_setOf_eq]
    refine and_congr_right fun hzV => ?_
    have h1 : (I * ψ z + 0).im = Real.log ‖g z‖ := by
      simp only [add_zero, hψdef, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.log_re,
        zero_mul, one_mul, zero_add, norm_mul, hρnorm, one_mul]
    rw [h1]
    have hgz : g z ≠ 0 := fun h => hgznorm z hzV (by rw [h, mul_zero])
    have hpos : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
    rw [not_iff_not, Real.log_eq_zero]
    constructor
    · rintro (h | h | h)
      · exact absurd h hpos.ne'
      · exact h
      · exact absurd h (by linarith)
    · intro h; right; left; exact h
  have hfContV : ContinuousOn f V := fun z hz => (hV z hz).2.2.2.2.1.continuousWithinAt
  have hfDiffV : DifferentiableOn ℂ f (V ∩ {z : ℂ | ‖g z‖ ≠ 1}) := by
    rintro z ⟨hzV, hz1⟩
    exact ((hV z hzV).2.2.2.2.2 hz1).differentiableWithinAt
  rw [← hset] at hfDiffV
  have hfV : DifferentiableOn ℂ f V :=
    differentiableOn_of_off_biholom_preimage_line (c := I) (d := 0) Complex.I_ne_zero
      hVimg hψDiff hψinvDiff hleft hfContV hfDiffV
  exact (hfV.analyticOnNhd hVo) z₀ hz₀V

end Bottcher
