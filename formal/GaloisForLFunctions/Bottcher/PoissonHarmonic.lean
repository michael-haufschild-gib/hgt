/-
# The Poisson integral of continuous boundary data is harmonic (Dirichlet ingredient 2/3)

Second of the three ingredients of the harmonic Schwarz reflection principle needed to discharge the
Kellogg–Warschawski hypothesis `hu` (`BottcherArcExtension.lean`).  For `g` continuous on the circle
`sphere c R`, the Poisson integral `w ↦ circleAverage (poissonKernel c w • g) c R` is harmonic on the
open disc `ball c R`.

The proof avoids differentiation under the integral by reducing to mathlib's **Cauchy transform
analyticity** (`hasFPowerSeriesOn_cauchy_integral`, which needs only circle integrability):
`poissonKernel c w z = Re(herglotzRieszKernel c w z)`, and the partial fraction
`(z-c)⁻¹·herglotz(c,w,z) = -(z-c)⁻¹ + 2(z-w)⁻¹` gives, under `circleAverage_eq_circleIntegral`,
`circleAverage (herglotz(c,w,·)·g_ℂ) c R = -(circleAverage g_ℂ) + 2·(Cauchy transform of g_ℂ)(w)`, an
analytic function of `w`.  Its real part is the Poisson integral (`Re` commutes with `circleAverage`),
so the Poisson integral is `Re` of an analytic function, hence harmonic.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib

open Complex Set Metric MeasureTheory InnerProductSpace

namespace Bottcher

/-- **The Poisson integral of continuous boundary data is harmonic in the disc.** -/
theorem poissonInt_harmonicOnNhd {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℝ}
    (hg : ContinuousOn g (sphere c R)) :
    HarmonicOnNhd (fun w => Real.circleAverage (poissonKernel c w • g) c R) (ball c R) := by
  classical
  set gc : ℂ → ℂ := fun z => (g z : ℂ) with hgc
  have habsR : |R| = R := abs_of_pos hR
  have hgcCont : ContinuousOn gc (sphere c |R|) := by
    rw [habsR]; exact Complex.continuous_ofReal.comp_continuousOn hg
  have hgcCI : CircleIntegrable gc c R := hgcCont.circleIntegrable'
  set Rnn : NNReal := ⟨R, hR.le⟩ with hRnn
  have hRnnR : (Rnn : ℝ) = R := rfl
  set CauchyT : ℂ → ℂ := fun w => (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • gc z with hCT
  have hCTan : AnalyticOnNhd ℂ CauchyT (ball c R) := by
    have h := (hasFPowerSeriesOn_cauchy_integral (f := gc) (c := c) (R := Rnn)
      (by rw [hRnnR]; exact hgcCI) (by rw [hRnn]; exact hR)).analyticOnNhd
    rw [Metric.eball_coe, hRnnR] at h
    exact h
  set F : ℂ → ℂ := fun w => -(Real.circleAverage gc c R) + 2 * CauchyT w with hF
  have hFan : AnalyticOnNhd ℂ F (ball c R) :=
    analyticOnNhd_const.add (analyticOnNhd_const.mul hCTan)
  -- z ≠ c on the sphere
  have hzc : ∀ z ∈ sphere c |R|, z - c ≠ 0 := fun z hz => sub_ne_zero.mpr (fun h => by
    rw [mem_sphere] at hz; rw [h, dist_self, habsR] at hz; exact hR.ne' hz.symm)
  have hkey : ∀ w ∈ ball c R, Real.circleAverage (poissonKernel c w • g) c R = (F w).re := by
    intro w hw
    have hzw : ∀ z ∈ sphere c |R|, z - w ≠ 0 := fun z hz => by
      rw [sub_ne_zero]; intro h; subst h
      rw [mem_sphere, habsR] at hz; rw [mem_ball] at hw
      exact absurd hz (ne_of_lt hw)
    -- integrability facts
    have hHcont : ContinuousOn (fun z => herglotzRieszKernel c w z * gc z) (sphere c |R|) := by
      apply ContinuousOn.mul _ hgcCont
      rw [herglotzRieszKernel_fun_def]
      exact ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun z hz => by rw [show (z-c)-(w-c) = z-w by ring]; exact hzw z hz)
    have hHCI : CircleIntegrable (fun z => herglotzRieszKernel c w z * gc z) c R :=
      hHcont.circleIntegrable'
    have hCIw : CircleIntegrable (fun z => (z - w)⁻¹ • gc z) c R :=
      (ContinuousOn.smul (ContinuousOn.inv₀ (by fun_prop) (fun z hz => hzw z hz)) hgcCont).circleIntegrable'
    have hCIc : CircleIntegrable (fun z => (z - c)⁻¹ • gc z) c R :=
      (ContinuousOn.smul (ContinuousOn.inv₀ (by fun_prop) (fun z hz => hzc z hz)) hgcCont).circleIntegrable'
    -- (A) Re of H = poissonInt
    have hA : (Real.circleAverage (fun z => herglotzRieszKernel c w z * gc z) c R).re
        = Real.circleAverage (poissonKernel c w • g) c R := by
      rw [show (Real.circleAverage (fun z => herglotzRieszKernel c w z * gc z) c R).re
          = Complex.reCLM (Real.circleAverage (fun z => herglotzRieszKernel c w z * gc z) c R) from rfl,
        ← ContinuousLinearMap.circleAverage_comp_comm Complex.reCLM hHCI]
      congr 1
      funext z
      have hpk : poissonKernel c w z = (herglotzRieszKernel c w z).re := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]; rfl
      simp only [Function.comp_apply, Complex.reCLM_apply, Pi.mul_apply,
        smul_eq_mul, hgc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, hpk]
    -- (B) H = F
    have hB : Real.circleAverage (fun z => herglotzRieszKernel c w z * gc z) c R = F w := by
      rw [hF, hCT,
        Real.circleAverage_eq_circleIntegral hR.ne' (f := fun z => herglotzRieszKernel c w z * gc z),
        Real.circleAverage_eq_circleIntegral hR.ne' (f := gc)]
      have hsplit : (∮ z in C(c, R), (z - c)⁻¹ • (herglotzRieszKernel c w z * gc z))
          = (∮ z in C(c, R), ((2 : ℂ) • ((z - w)⁻¹ • gc z) - (z - c)⁻¹ • gc z)) := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        have hz' : z ∈ sphere c |R| := by rw [habsR]; exact hz
        have h1 : z - c ≠ 0 := hzc z hz'
        have h2 : z - w ≠ 0 := hzw z hz'
        have hpf : (z - c)⁻¹ * herglotzRieszKernel c w z = -(z - c)⁻¹ + 2 * (z - w)⁻¹ := by
          rw [herglotzRieszKernel_def, show (z-c)-(w-c) = z-w by ring]; field_simp; ring
        simp only [smul_eq_mul]
        rw [← mul_assoc, hpf]; ring
      have hCI2w : CircleIntegrable (fun z => (2 : ℂ) • ((z - w)⁻¹ • gc z)) c R :=
        (continuousOn_const.smul ((ContinuousOn.inv₀ (by fun_prop)
          (fun z hz => hzw z hz)).smul hgcCont)).circleIntegrable'
      rw [hsplit, circleIntegral.integral_sub hCI2w hCIc, circleIntegral.integral_smul]
      simp only [smul_eq_mul]; ring
    rw [← hA, hB]
  intro w hw
  have hre := (hFan w hw).harmonicAt_re
  have heq : (fun w => Real.circleAverage (poissonKernel c w • g) c R) =ᶠ[nhds w] (fun z => (F z).re) := by
    filter_upwards [isOpen_ball.mem_nhds hw] with y hy using hkey y hy
  exact (harmonicAt_congr_nhds heq).mpr hre

end Bottcher
