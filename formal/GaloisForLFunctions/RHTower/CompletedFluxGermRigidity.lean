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

/-- **Residue-filled germ rigidity at arbitrary points.** Equality of the analytic completed-flux
germs forces equality of their base points, including when one or both bases are zeros of `xi`.
The proof moves to a nearby punctured point, where the peeled factors are nonzero, and invokes the
nonzero-point logarithmic-flux rigidity. -/
theorem completedFluxGermAt_germ_injective {a b : ℂ}
    (hgerm : completedFluxGermAt a =ᶠ[𝓝 0] completedFluxGermAt b) :
    a = b := by
  obtain ⟨Ra, hRa, ha, _haan, ha0, hafact⟩ := xi_peel_ball a
  obtain ⟨Rb, hRb, hb, _hban, hb0, hbfact⟩ := xi_peel_ball b
  obtain ⟨Re, hRe, hResub⟩ := Metric.mem_nhds_iff.mp hgerm
  let r : ℝ := min Re (min Ra Rb)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hRe (lt_min hRa hRb)
  let x0 : ℂ := ((r / 2 : ℝ) : ℂ)
  have hx0 : x0 ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hr.ne' (by norm_num))
  have hx0norm : ‖x0‖ = r / 2 := by
    change ‖((r / 2 : ℝ) : ℂ)‖ = r / 2
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  have hx0Re : x0 ∈ ball (0 : ℂ) Re := by
    rw [mem_ball, dist_eq, sub_zero, hx0norm]
    have hrRe : r ≤ Re := min_le_left _ _
    linarith
  have hxa : a + x0 ∈ ball a Ra := by
    rw [mem_ball, dist_eq, show a + x0 - a = x0 by ring, hx0norm]
    have hrRa : r ≤ Ra := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hxb : b + x0 ∈ ball b Rb := by
    rw [mem_ball, dist_eq, show b + x0 - b = x0 by ring, hx0norm]
    have hrRb : r ≤ Rb := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hane : xi (a + x0) ≠ 0 := by
    rw [hafact (a + x0) hxa]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hx0)) (ha0 (a + x0) hxa)
  have hbne : xi (b + x0) ≠ 0 := by
    rw [hbfact (b + x0) hxb]
    exact mul_ne_zero (pow_ne_zero _ (by simpa using hx0)) (hb0 (b + x0) hxb)
  have hopen : IsOpen (ball (0 : ℂ) Re ∩ ({0} : Set ℂ)ᶜ) :=
    isOpen_ball.inter isOpen_compl_singleton
  have hxopen : x0 ∈ ball (0 : ℂ) Re ∩ ({0} : Set ℂ)ᶜ :=
    ⟨hx0Re, by simpa using hx0⟩
  have hq : (fun y : ℂ => seamFluxCochain (a + y)) =ᶠ[𝓝 x0]
      fun y : ℂ => seamFluxCochain (b + y) := by
    filter_upwards [hopen.mem_nhds hxopen] with y hy
    have hy0 : y ≠ 0 := by simpa using hy.2
    have heq := hResub hy.1
    change completedFluxGermAt a y = completedFluxGermAt b y at heq
    simp only [completedFluxGermAt, if_neg hy0] at heq
    exact mul_left_cancel₀ hy0 heq
  have hto : Tendsto (fun u : ℂ => x0 + u) (𝓝 0) (𝓝 x0) := by
    have hc : ContinuousAt (fun u : ℂ => x0 + u) 0 := continuousAt_const.add continuousAt_id
    simpa using hc.tendsto
  have hq0 : (fun u : ℂ => seamFluxCochain ((a + x0) + u)) =ᶠ[𝓝 0]
      fun u : ℂ => seamFluxCochain ((b + x0) + u) := by
    filter_upwards [hto.eventually hq] with u hu
    simpa [add_assoc] using hu
  have hab := seamFlux_germ_injective hane hbne hq0
  exact add_right_cancel hab

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

/-- Equality of all completed-flux Taylor coefficients is exactly equality of the two analytic
residue-filled germs. -/
theorem completedFluxTaylorCoeff_all_eq_iff_germ_eq (a b : ℂ) :
    (∀ n : ℕ, completedFluxTaylorCoeff a n = completedFluxTaylorCoeff b n) ↔
      completedFluxGermAt a =ᶠ[𝓝 0] completedFluxGermAt b := by
  constructor
  · intro hcoeff
    apply analyticAt_eventuallyEq_of_iteratedDeriv_eq
      (completedFluxGermAt_analyticAt_zero a) (completedFluxGermAt_analyticAt_zero b)
    intro n
    have hc := hcoeff n
    rw [completedFluxTaylorCoeff, completedFluxTaylorCoeff] at hc
    have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    exact mul_right_cancel₀ hfac ((div_eq_div_iff hfac hfac).mp hc)
  · intro hgerm n
    rw [completedFluxTaylorCoeff, completedFluxTaylorCoeff,
      hgerm.iteratedDeriv_eq n]

/-- Equality of the residue-filled completed-flux germs at the FE and Schwarz images.  Unlike
`seamFluxCriticalPhaseAt`, this predicate remains meaningful at zeros of `xi`. -/
def completedFluxCriticalPhaseAt (ρ : ℂ) : Prop :=
  completedFluxGermAt (1 - ρ) =ᶠ[𝓝 0] completedFluxGermAt ((starRingEnd ℂ) ρ)

/-- **All-point critical-line reconstruction.** The residue-filled completed-flux germ belongs to
the FE--Schwarz fixed locus exactly at points of the critical line, including zeros. -/
theorem completedFluxCriticalPhaseAt_iff (ρ : ℂ) :
    completedFluxCriticalPhaseAt ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro hphase
    have heq := completedFluxGermAt_germ_injective hphase
    have hre := congrArg Complex.re heq
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hre
    have heq : (1 - ρ : ℂ) = (starRingEnd ℂ) ρ := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · simp
    rw [completedFluxCriticalPhaseAt, heq]

/-- **All-order coefficient form.** The FE-side and Schwarz-side completed-flux Taylor sequences
agree at every order exactly on the critical line. -/
theorem completedFluxTaylorCoeff_line_pair_all_eq_iff (ρ : ℂ) :
    (∀ n : ℕ, completedFluxTaylorCoeff (1 - ρ) n =
      completedFluxTaylorCoeff ((starRingEnd ℂ) ρ) n) ↔
      ρ.re = 1 / 2 := by
  rw [completedFluxTaylorCoeff_all_eq_iff_germ_eq, ← completedFluxCriticalPhaseAt_iff]
  rfl

/-- **Finite transverse witness.** Every off-critical point is detected by a finite coefficient of
the single completed-flux Taylor sequence: the FE and Schwarz images disagree at some order. -/
theorem exists_completedFluxTaylorCoeff_line_pair_ne_of_re_ne_half {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) :
    ∃ n : ℕ, completedFluxTaylorCoeff (1 - ρ) n ≠
      completedFluxTaylorCoeff ((starRingEnd ℂ) ρ) n := by
  by_contra h
  push Not at h
  exact hρ ((completedFluxTaylorCoeff_line_pair_all_eq_iff ρ).mp h)

end

end RHTower
