import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition
import GaloisForLFunctions.RHTower.SeamVerticalDecay

/-!
# The completed logarithmic-flux germ remembers its base point

At a nonzero point of `xi`, equality of two translated completed-flux germs forces the two base
points to coincide.  The mechanism is global despite the local hypothesis.  Equal logarithmic
derivatives make the corresponding translates of `xi` constant multiples of one another.  The
functional equation squares that quasi-period into an actual period, and the established
aperiodicity of `xi` kills every nonzero shift.

This gives a constraint-side characterization of the critical line.  The two local germs selected
by functional-equation reflection (`1 - ρ`) and Schwarz conjugation (`conj ρ`) agree exactly when
`Re ρ = 1/2`.  No flow, cutoff, carrier, zero enumeration, or positivity hypothesis occurs.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Local equality of the translated completed logarithmic flux makes the corresponding translates
of `xi` globally proportional. -/
theorem xi_shift_eq_const_mul_of_seamFlux_germ_eq
    {a b : ℂ} (ha : xi a ≠ 0) (hb : xi b ≠ 0)
    (hflux : (fun x : ℂ => seamFluxCochain (a + x)) =ᶠ[𝓝 0]
      fun x : ℂ => seamFluxCochain (b + x)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x : ℂ, xi (a + x) = c * xi (b + x) := by
  have hfa_ne : ∀ᶠ x : ℂ in 𝓝 0, xi (a + x) ≠ 0 := by
    have hadd : ContinuousAt (fun x : ℂ => a + x) 0 := continuousAt_const.add continuousAt_id
    have hcont : ContinuousAt (fun x : ℂ => xi (a + x)) 0 :=
      xi_differentiable.continuous.continuousAt.comp hadd
    exact hcont.eventually_ne (by simpa using ha)
  have hfb_ne : ∀ᶠ x : ℂ in 𝓝 0, xi (b + x) ≠ 0 := by
    have hadd : ContinuousAt (fun x : ℂ => b + x) 0 := continuousAt_const.add continuousAt_id
    have hcont : ContinuousAt (fun x : ℂ => xi (b + x)) 0 :=
      xi_differentiable.continuous.continuousAt.comp hadd
    exact hcont.eventually_ne (by simpa using hb)
  have hall : ∀ᶠ x : ℂ in 𝓝 0,
      seamFluxCochain (a + x) = seamFluxCochain (b + x) ∧
        xi (a + x) ≠ 0 ∧ xi (b + x) ≠ 0 := by
    filter_upwards [hflux, hfa_ne, hfb_ne] with x hq hane hbne
    exact ⟨hq, hane, hbne⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hall
  let ratio : ℂ → ℂ := fun x => xi (a + x) / xi (b + x)
  have hratio_diff : DifferentiableOn ℂ ratio (ball 0 r) := by
    intro x hx
    have hne := (hrsub hx).2.2
    have hda : DifferentiableAt ℂ (fun y : ℂ => a + y) x :=
      differentiableAt_const (c := a) |>.add differentiableAt_id
    have hdb : DifferentiableAt ℂ (fun y : ℂ => b + y) x :=
      differentiableAt_const (c := b) |>.add differentiableAt_id
    simpa only [ratio, Function.comp_apply, Pi.div_apply] using
      ((xi_differentiable.differentiableAt.comp x hda).div
        (xi_differentiable.differentiableAt.comp x hdb) hne).differentiableWithinAt
  have hratio_deriv : ∀ x ∈ ball (0 : ℂ) r, deriv ratio x = 0 := by
    intro x hx
    obtain ⟨hfluxx, hax, hbx⟩ := hrsub hx
    have hfa : HasDerivAt (fun y : ℂ => xi (a + y)) (deriv xi (a + x)) x := by
      have hadd : HasDerivAt (fun y : ℂ => a + y) 1 x := by
        convert (hasDerivAt_const (x := x) (c := a)).add (hasDerivAt_id x) using 1
        all_goals ring
      simpa using xi_differentiable.differentiableAt.hasDerivAt.comp x hadd
    have hfb : HasDerivAt (fun y : ℂ => xi (b + y)) (deriv xi (b + x)) x := by
      have hadd : HasDerivAt (fun y : ℂ => b + y) 1 x := by
        convert (hasDerivAt_const (x := x) (c := b)).add (hasDerivAt_id x) using 1
        all_goals ring
      simpa using xi_differentiable.differentiableAt.hasDerivAt.comp x hadd
    have hdiv := hfa.div hfb hbx
    have hdiv' : deriv ratio x =
        (deriv xi (a + x) * xi (b + x) - xi (a + x) * deriv xi (b + x)) /
          xi (b + x) ^ 2 := by
      simpa only [ratio, Pi.div_apply] using hdiv.deriv
    rw [hdiv']
    have hlog : deriv xi (a + x) / xi (a + x) =
        deriv xi (b + x) / xi (b + x) := by
      change -logDeriv xi (a + x) = -logDeriv xi (b + x) at hfluxx
      simpa [logDeriv_apply] using congrArg Neg.neg hfluxx
    field_simp [hax, hbx] at hlog
    rw [hlog, sub_self, zero_div]
  have hratio_const : ∀ x ∈ ball (0 : ℂ) r, ratio x = ratio 0 := by
    intro x hx
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball 0 r).isPreconnected
      hratio_diff (fun y hy => hratio_deriv y hy) hx (mem_ball_self hr)
  let c : ℂ := ratio 0
  have hc : c ≠ 0 := div_ne_zero (by simpa using ha) (by simpa using hb)
  have hlocal : (fun x : ℂ => xi (a + x)) =ᶠ[𝓝 0]
      fun x : ℂ => c * xi (b + x) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with x hx
    have hconst := hratio_const x hx
    change xi (a + x) / xi (b + x) = c at hconst
    exact (div_eq_iff (hrsub hx).2.2).mp hconst
  have hana : AnalyticOnNhd ℂ (fun x : ℂ => xi (a + x)) Set.univ := by
    have hdiff : Differentiable ℂ (fun x : ℂ => xi (a + x)) :=
      xi_differentiable.comp ((differentiable_const a).add differentiable_id)
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hanb : AnalyticOnNhd ℂ (fun x : ℂ => c * xi (b + x)) Set.univ := by
    have hshift : Differentiable ℂ (fun x : ℂ => xi (b + x)) :=
      xi_differentiable.comp ((differentiable_const b).add differentiable_id)
    exact ((differentiable_const c).mul hshift).differentiableOn.analyticOnNhd isOpen_univ
  have heq := hana.eq_of_eventuallyEq hanb hlocal
  exact ⟨c, hc, fun x => congrFun heq x⟩

/-- **Completed-flux germ rigidity.** At nonzero points of `xi`, the local completed logarithmic
flux germ is injective in its base point. -/
theorem seamFlux_germ_injective {a b : ℂ} (ha : xi a ≠ 0) (hb : xi b ≠ 0)
    (hflux : (fun x : ℂ => seamFluxCochain (a + x)) =ᶠ[𝓝 0]
      fun x : ℂ => seamFluxCochain (b + x)) :
    a = b := by
  obtain ⟨c, _hc, hshift⟩ := xi_shift_eq_const_mul_of_seamFlux_germ_eq ha hb hflux
  let h : ℂ := a - b
  have hglobal : ∀ z : ℂ, xi (z + h) = c * xi z := by
    intro z
    calc
      xi (z + h) = xi (a + (z - b)) := by
        congr 1
        dsimp [h]
        ring
      _ = c * xi (b + (z - b)) := hshift (z - b)
      _ = c * xi z := by
        congr 2
        ring
  have hc_sq : c ^ 2 = 1 := by
    have hz := hglobal (1 - (2 : ℂ) - h)
    have hz2 := hglobal 2
    have hxi2 : xi (2 : ℂ) ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
    rw [show (1 - (2 : ℂ) - h) + h = 1 - 2 by ring, xi_one_sub,
      show 1 - (2 : ℂ) - h = 1 - (2 + h) by ring, xi_one_sub, hz2] at hz
    apply mul_left_cancel₀ hxi2
    calc
      xi 2 * c ^ 2 = c * (c * xi 2) := by ring
      _ = xi 2 := hz.symm
      _ = xi 2 * 1 := by ring
  have hperiod : ∀ z : ℂ, xi (z + 2 * h) = xi z := by
    intro z
    calc
      xi (z + 2 * h) = xi ((z + h) + h) := by
        congr 1
        ring
      _ = c * xi (z + h) := hglobal (z + h)
      _ = c * (c * xi z) := by rw [hglobal z]
      _ = c ^ 2 * xi z := by ring
      _ = xi z := by rw [hc_sq, one_mul]
  have hh : h = 0 := by
    by_contra hh0
    exact xi_not_periodic (show 2 * h ≠ 0 by exact mul_ne_zero (by norm_num) hh0) hperiod
  dsimp [h] at hh
  exact sub_eq_zero.mp hh

/-- Equality of the two completed-flux germs selected by FE reflection and Schwarz conjugation. -/
def seamFluxCriticalPhaseAt (ρ : ℂ) : Prop :=
  (fun x : ℂ => seamFluxCochain ((1 - ρ) + x)) =ᶠ[𝓝 0]
    fun x : ℂ => seamFluxCochain ((starRingEnd ℂ) ρ + x)

/-- **Constraint characterization of the critical line.** At a nonzero point of `xi`, the FE-side
and Schwarz-side completed-flux germs agree exactly on `Re ρ = 1/2`. -/
theorem seamFluxCriticalPhaseAt_iff {ρ : ℂ} (hρ : xi ρ ≠ 0) :
    seamFluxCriticalPhaseAt ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro hphase
    have hleft : xi (1 - ρ) ≠ 0 := by rw [xi_one_sub]; exact hρ
    have hright : xi ((starRingEnd ℂ) ρ) ≠ 0 := by
      rw [xi_conj]
      exact (map_ne_zero (starRingEnd ℂ)).2 hρ
    have heq := seamFlux_germ_injective hleft hright hphase
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hre
    have heq : (1 - ρ : ℂ) = (starRingEnd ℂ) ρ := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · simp
    rw [seamFluxCriticalPhaseAt, heq]

end

end RHTower
