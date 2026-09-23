import GaloisForLFunctions.HTGeometry.ClockProbeInhomogeneousChart
import GaloisForLFunctions.HTGeometry.ConformalMetricClockCalculus

/-!
# The exactly determined class on a chart

Every determination result so far recovers a potential that is a function of a leaf label. The
exponential substitution escapes that restriction entirely. For a smooth `w` the field `e^{w}` is
nowhere zero and satisfies

`□ e^{w} = (□w + Γ(w,w)) e^{w}`,

so the potential `-(□w + Γ(w,w))` — a genuinely inhomogeneous function of all the coordinates —
carries a globally nonvanishing probe and is therefore determined outright.

This is exactly the reachable class: a potential admits a globally nonvanishing smooth probe **if
and only if** it has this form. The proof of the converse takes the logarithm of the probe, which is
legitimate because a nowhere-vanishing continuous function on a coordinate space has constant sign.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

open scoped ContDiff

variable {d : ℕ}

/-! ## Linearity of the chart d'Alembertian -/

theorem SmoothMetricChart.dalembert_const_mul (M : SmoothMetricChart d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Fin d → ℝ) :
    M.dalembert (fun y => c * f y) x = c * M.dalembert f x := by
  have hflux : ∀ i : Fin d, M.flux (fun y => c * f y) i = fun y => c * M.flux f i y := by
    intro i
    funext y
    have hs : ∑ j, M.inverseMetric y i j * coordPartial j (fun z => c * f z) y
        = c * ∑ j, M.inverseMetric y i j * coordPartial j f y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordPartial_const_mul (differentiableAt_of_contDiff_infty hf y) c j]
      ring
    simp only [SmoothMetricChart.flux]
    rw [hs]
    ring
  have hsum : ∑ i, coordPartial i (M.flux (fun y => c * f y) i) x
      = c * ∑ i, coordPartial i (M.flux f i) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hflux i, coordPartial_const_mul
      (differentiableAt_of_contDiff_infty (M.contDiff_flux hf i) x) c i]
  simp only [SmoothMetricChart.dalembert]
  rw [hsum]
  ring

/-! ## The exponential probe -/

/-- Exponential probe of a smooth exponent on a chart. -/
noncomputable def chartExpProbe (w : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => Real.exp (w x)

theorem chartExpProbe_ne_zero (w : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    chartExpProbe w x ≠ 0 := Real.exp_ne_zero _

theorem chartExpProbe_pos (w : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 < chartExpProbe w x := Real.exp_pos _

/-- **Exponential chain rule.** -/
theorem dalembert_chartExpProbe (M : SmoothMetricChart d) {w : (Fin d → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) (x : Fin d → ℝ) :
    M.dalembert (chartExpProbe w) x
      = Real.exp (w x) * (M.dalembert w x + M.gradPair w w x) := by
  have h := M.dalembert_expSmul 1 hw x
  simp only [one_mul, one_pow] at h
  exact h

/-- The potential carried by an exponential probe. -/
noncomputable def chartRiccatiPotential (M : SmoothMetricChart d) (w : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ := fun x => -(M.dalembert w x + M.gradPair w w x)

/-- **Every smooth exponent yields a solved potential.** -/
theorem solvesPotentialWave_chartExpProbe (M : SmoothMetricChart d) {w : (Fin d → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) :
    SolvesPotentialWave M.dalembert (chartRiccatiPotential M w) (chartExpProbe w) := by
  intro x
  rw [dalembert_chartExpProbe M hw x, chartRiccatiPotential, chartExpProbe]
  ring

/-- **The class is determined**, by a globally nonvanishing probe. -/
theorem noCommonZero_chartRiccatiPotential (M : SmoothMetricChart d) {w : (Fin d → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) : NoCommonZero M.dalembert (chartRiccatiPotential M w) :=
  noCommonZero_of_nonvanishing_probe (chartExpProbe_ne_zero w)
    (solvesPotentialWave_chartExpProbe M hw)

/-- **Determination.** Any potential with the same solutions is that potential. -/
theorem potential_eq_chartRiccatiPotential (M : SmoothMetricChart d) {w : (Fin d → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) {other : (Fin d → ℝ) → ℝ}
    (hother : ∀ u ∈ solutionSet M.dalembert (chartRiccatiPotential M w),
      SolvesPotentialWave M.dalembert other u) :
    other = chartRiccatiPotential M w :=
  potential_eq_of_noCommonZero (noCommonZero_chartRiccatiPotential M hw) hother

/-! ## The class is exactly the potentials with a nonvanishing probe -/

/-- A nowhere-vanishing continuous function on a coordinate space has constant sign. -/
theorem sign_const_of_ne_zero {u : (Fin d → ℝ) → ℝ} (hc : Continuous u)
    (hu : ∀ x, u x ≠ 0) : (∀ x, 0 < u x) ∨ ∀ x, u x < 0 := by
  have hpre : IsPreconnected (Set.range u) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image u hc.continuousOn
  have hoc := hpre.ordConnected
  have key : ∀ a b : Fin d → ℝ, 0 < u a → 0 < u b := by
    intro a b ha
    by_contra hb
    rw [not_lt] at hb
    have hmem : (0 : ℝ) ∈ Set.range u := hoc.out ⟨b, rfl⟩ ⟨a, rfl⟩ ⟨hb, le_of_lt ha⟩
    obtain ⟨y, hy⟩ := hmem
    exact hu y hy
  rcases lt_or_gt_of_ne (hu 0) with hneg | hpos
  · right
    intro x
    by_contra hx
    rw [not_lt] at hx
    have hxpos : 0 < u x := lt_of_le_of_ne hx (Ne.symm (hu x))
    exact absurd (key x 0 hxpos) (not_lt.mpr (le_of_lt hneg))
  · left
    exact fun x => key 0 x hpos

/-- **A nonvanishing probe is an exponential up to sign, so its potential is Riccati.** -/
theorem exists_chartRiccati_of_nonvanishing_probe (M : SmoothMetricChart d)
    {V u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hu0 : ∀ x, u x ≠ 0)
    (hsolve : SolvesPotentialWave M.dalembert V u) :
    ∃ w : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ w ∧ V = chartRiccatiPotential M w := by
  obtain ⟨c, hcpos, hv⟩ : ∃ c : ℝ, (∀ x, 0 < c * u x) ∧ ContDiff ℝ ∞ fun x => c * u x := by
    rcases sign_const_of_ne_zero hu.continuous hu0 with hp | hn
    · exact ⟨1, fun x => by simpa using hp x, contDiff_const.mul hu⟩
    · refine ⟨-1, fun x => ?_, contDiff_const.mul hu⟩
      have := hn x
      nlinarith [this]
  set v : (Fin d → ℝ) → ℝ := fun x => c * u x with hvdef
  have hvne : ∀ x, v x ≠ 0 := fun x => ne_of_gt (hcpos x)
  have hsolveV : SolvesPotentialWave M.dalembert V v := by
    intro x
    have hc0 : c ≠ 0 := by
      intro h
      have := hcpos 0
      rw [h] at this
      simp at this
    have hd := M.dalembert_const_mul hu c x
    have h2 := hsolve x
    rw [hvdef]
    show M.dalembert (fun y => c * u y) x + V x * (c * u x) = 0
    rw [hd]
    linear_combination c * h2
  refine ⟨fun x => Real.log (v x), hv.log hvne, ?_⟩
  funext x
  have hexp : Real.exp (Real.log (v x)) = v x := Real.exp_log (hcpos x)
  have hprobe : chartExpProbe (fun y => Real.log (v y)) = v := by
    funext y
    rw [chartExpProbe]
    exact Real.exp_log (hcpos y)
  have hchain := dalembert_chartExpProbe M (hv.log hvne) x
  rw [hprobe, hexp] at hchain
  have hs := hsolveV x
  rw [hchain] at hs
  have hvx : v x ≠ 0 := hvne x
  rw [chartRiccatiPotential]
  have : (V x + (M.dalembert (fun y => Real.log (v y)) x
      + M.gradPair (fun y => Real.log (v y)) (fun y => Real.log (v y)) x)) * v x = 0 := by
    nlinarith [hs]
  rcases mul_eq_zero.mp this with h | h
  · linarith [h]
  · exact absurd h hvx

/-- **The exact reachable class.** A potential carries a globally nonvanishing smooth probe exactly
when it is `-(□w + Γ(w,w))` for a smooth exponent. -/
theorem chartRiccati_iff (M : SmoothMetricChart d) (V : (Fin d → ℝ) → ℝ) :
    (∃ u : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ u ∧ (∀ x, u x ≠ 0) ∧
        SolvesPotentialWave M.dalembert V u)
      ↔ ∃ w : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ w ∧ V = chartRiccatiPotential M w := by
  constructor
  · rintro ⟨u, hu, hu0, hsolve⟩
    exact exists_chartRiccati_of_nonvanishing_probe M hu hu0 hsolve
  · rintro ⟨w, hw, rfl⟩
    exact ⟨chartExpProbe w, Real.contDiff_exp.comp hw, chartExpProbe_ne_zero w,
      solvesPotentialWave_chartExpProbe M hw⟩

/-! ## The class contains potentials that are not functions of any leaf label -/

theorem ofSignature_gradPair (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (f h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair f h x
      = ∑ i, (eps i)⁻¹ * coordPartial i f x * coordPartial i h x := by
  simp only [SmoothMetricChart.gradPair, SmoothPseudoMetric.ofSignature_inverseMetric,
    Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (Ne.symm hj)]
    ring
  · intro hn
    exact absurd (Finset.mem_univ i) hn

/-- The squared coordinate, used as an exponent. -/
noncomputable def sqCoord (k : Fin d) : (Fin d → ℝ) → ℝ := fun x => x k * x k

theorem contDiff_sqCoord (k : Fin d) : ContDiff ℝ ∞ (sqCoord k) :=
  (contDiff_apply ℝ ℝ k).mul (contDiff_apply ℝ ℝ k)

theorem coordPartial_sqCoord (k i : Fin d) (x : Fin d → ℝ) :
    coordPartial i (sqCoord k) x = 2 * x k * (if k = i then 1 else 0) := by
  have hd : DifferentiableAt ℝ (fun y : Fin d → ℝ => y k) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).differentiableAt
  show coordPartial i (fun y : Fin d → ℝ => y k * y k) x = 2 * x k * (if k = i then 1 else 0)
  rw [coordPartial_mul hd hd i, coordPartial_coord]
  ring

theorem coordPartial_coordPartial_sqCoord (k i : Fin d) (x : Fin d → ℝ) :
    coordPartial i (coordPartial i (sqCoord k)) x
      = 2 * (if k = i then 1 else 0) * (if k = i then 1 else 0) := by
  have hfun : coordPartial i (sqCoord k)
      = fun y : Fin d → ℝ => (2 * (if k = i then 1 else 0)) * y k := by
    funext y
    rw [coordPartial_sqCoord]
    ring
  have hd : DifferentiableAt ℝ (fun y : Fin d → ℝ => y k) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).differentiableAt
  rw [hfun, coordPartial_const_mul hd _ i, coordPartial_coord]

theorem chartRiccatiPotential_ofSignature_sqCoord (eps : Fin d → ℝ) (heps : ∀ i, eps i ≠ 0)
    (k : Fin d) (x : Fin d → ℝ) :
    chartRiccatiPotential (SmoothPseudoMetric.ofSignature eps heps).chart (sqCoord k) x
      = -((eps k)⁻¹ * 2 + (eps k)⁻¹ * (2 * x k) ^ (2 : ℕ)) := by
  have hdal : (SmoothPseudoMetric.ofSignature eps heps).chart.dalembert (sqCoord k) x
      = (eps k)⁻¹ * 2 := by
    rw [SmoothPseudoMetric.ofSignature_dalembert eps heps (contDiff_sqCoord k) x,
      Finset.sum_eq_single k]
    · rw [coordPartial_coordPartial_sqCoord]
      simp
    · intro i _ hi
      rw [coordPartial_coordPartial_sqCoord, if_neg (Ne.symm hi)]
      ring
    · intro hn
      exact absurd (Finset.mem_univ k) hn
  have hgp : (SmoothPseudoMetric.ofSignature eps heps).chart.gradPair (sqCoord k) (sqCoord k) x
      = (eps k)⁻¹ * (2 * x k) ^ (2 : ℕ) := by
    rw [ofSignature_gradPair, Finset.sum_eq_single k]
    · rw [coordPartial_sqCoord]
      simp
      ring
    · intro i _ hi
      rw [coordPartial_sqCoord, if_neg (Ne.symm hi)]
      ring
    · intro hn
      exact absurd (Finset.mem_univ k) hn
  rw [chartRiccatiPotential, hdal, hgp]

/-- **A determined potential that is not a function of the zeroth coordinate.** Two points of one
level set of `x⁰` carry different values, so no slicing or foliation theorem along `x⁰` reaches
it — yet it is determined by a globally nonvanishing probe. -/
theorem exists_determined_potential_not_leafConstant :
    ∃ (V : (Fin (d + 1 + 1) → ℝ) → ℝ),
      NoCommonZero (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart.dalembert V ∧
        ∃ x y : Fin (d + 1 + 1) → ℝ, x 0 = y 0 ∧ V x ≠ V y := by
  classical
  refine ⟨chartRiccatiPotential (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart (sqCoord 1),
    noCommonZero_chartRiccatiPotential _ (contDiff_sqCoord 1), 0, Pi.single 1 1, by simp, ?_⟩
  have h1 : ((1 : Fin (d + 1 + 1)) : ℕ) = 1 := by simp
  have hval : ∀ x : Fin (d + 1 + 1) → ℝ,
      chartRiccatiPotential (SmoothPseudoMetric.minkowski (d + 1 + 1)).chart (sqCoord 1) x
        = -(2 + (2 * x 1) ^ (2 : ℕ)) := by
    intro x
    rw [SmoothPseudoMetric.minkowski,
      chartRiccatiPotential_ofSignature_sqCoord _ _ 1 x]
    norm_num [h1]
  rw [hval, hval]
  norm_num

end GaloisForLFunctions.HTGeometry
