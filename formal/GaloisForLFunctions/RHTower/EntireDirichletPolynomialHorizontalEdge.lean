import GaloisForLFunctions.RHTower.EntireDirichletPolynomialTrace
import GaloisForLFunctions.RHTower.WeightedSegmentArgumentBound
import GaloisForLFunctions.HTGeometry.DistinctZerosLeDivisor
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle

/-!
# The horizontal edge of a Littlewood rectangle for a Dirichlet polynomial

The weighted argument variation of a finite Dirichlet polynomial `Ψ` across a horizontal segment
`[c,4]` at height `T` is at most `2(4−c)π` times one more than the number of sign changes of
`Re Ψ(σ+iT)`.  Every such sign change is a real zero of the analytic trace, and Jensen's inequality
in the disc of radius `4−c` about `4` bounds those by `log(Mb/m)/log(8/(4−c))`, with `Mb` the
`n⁴`-weighted `ℓ¹` mass of the coefficients and `m` a lower bound for `|Re Ψ(4+iT)|`.

For the Levinson mollifier of length `M = T^θ` both quantities are explicit and the count is
`O(log T)`, exactly as for the detector itself.
-/

open Complex Metric Set MeromorphicOn MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped Interval

noncomputable section

namespace RHTower

theorem hasDerivAt_edPoly_horiz (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T x : ℝ) :
    HasDerivAt (fun y : ℝ => edPoly a s ((y : ℂ) + (T : ℂ) * I))
      (deriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)) x := by
  have hpath : HasDerivAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((T : ℂ) * I)
  have h := ((differentiable_edPoly a hs _).hasDerivAt).comp x hpath
  exact h.congr_deriv (by ring)

theorem continuous_edPoly_horiz (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) :
    Continuous (fun y : ℝ => edPoly a s ((y : ℂ) + (T : ℂ) * I)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hasDerivAt_edPoly_horiz a hs T x).continuousAt

theorem continuous_deriv_edPoly_horiz (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) :
    Continuous (fun y : ℝ => deriv (edPoly a s) ((y : ℂ) + (T : ℂ) * I)) := by
  have hana : AnalyticOnNhd ℂ (deriv (edPoly a s)) Set.univ := fun z _ =>
    ((analyticOnNhd_edPoly a hs) z (Set.mem_univ z)).deriv
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : ContinuousAt ((deriv (edPoly a s)) ∘ (fun v : ℝ => (v : ℂ) + (T : ℂ) * I)) x :=
    ContinuousAt.comp (hana _ (Set.mem_univ _)).continuousAt
      (by fun_prop : ContinuousAt (fun v : ℝ => (v : ℂ) + (T : ℂ) * I) x)
  simpa [Function.comp_def] using hc

/-- **The weighted horizontal edge of a Dirichlet polynomial.** -/
theorem abs_integral_weighted_im_logDeriv_edPoly_le
    (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hreal : ∀ n ∈ s, (starRingEnd ℂ) (a n) = a n) (T : ℝ)
    {c m Mb : ℝ} (hc : -4 < c) (hc4 : c < 4)
    (hne : ∀ x ∈ Set.Icc c (4 : ℝ), edPoly a s ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    |∫ x in c..(4 : ℝ), (x - c) *
        (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ 2 * (4 - c) *
        ((Real.log (Mb / m) / Real.log (8 / (4 - c)) + 1) * Real.pi) := by
  classical
  set r : ℝ := 4 - c with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr8 : r < 8 := by rw [hr]; linarith
  set K : Set ℂ := closedBall (4 : ℂ) |r| with hK
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hana : AnalyticOnNhd ℂ (edPolyTrace a s T) K := analyticOnNhd_edPolyTrace a hs T K
  have htracene : ∃ z : ℂ, edPolyTrace a s T z ≠ 0 := by
    refine ⟨4, ?_⟩
    intro h0
    rw [h0, norm_zero] at hcentre
    linarith
  have hord : ∀ z ∈ K, analyticOrderAt (edPolyTrace a s T) z ≠ ⊤ := fun z _ =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero
      (analyticOnNhd_edPolyTrace a hs T Set.univ) htracene z
  have hfin : {u : ℂ | u ∈ K ∧ edPolyTrace a s T u = 0}.Finite := by
    have hdiv := (MeromorphicOn.divisor (edPolyTrace a s T) K).finiteSupport hKcompact
    refine hdiv.subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hana hu.1 hu.2 (hord u hu.1)
    omega
  have hfinR : {x : ℝ | (x : ℂ) ∈ K ∧ edPolyTrace a s T (x : ℂ) = 0}.Finite := by
    refine Set.Finite.ofFinset (hfin.toFinset.preimage (fun x : ℝ => (x : ℂ))
      (fun p _ q _ h => Complex.ofReal_inj.mp h)) ?_
    intro x
    rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
    rfl
  set Z : Finset ℝ := hfinR.toFinset with hZdef
  set f : ℝ → ℂ := fun x => edPoly a s ((x : ℂ) + (T : ℂ) * I) with hfdef
  set f' : ℝ → ℂ := fun x => deriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I) with hf'def
  have hZmem : ∀ x ∈ Set.Ioo c (4 : ℝ), (f x).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [hK, mem_closedBall, abs_of_pos hr0, Complex.dist_eq]
      have hval : ‖((x : ℂ) - 4)‖ = |x - 4| := by
        rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le, hr]
      constructor <;> linarith [hx.1, hx.2]
    · rw [edPolyTrace_ofReal a hs hreal T x]
      rw [hfdef] at hzero
      simp only at hzero
      rw [hzero]
      norm_num
  have hbound := abs_integral_weighted_im_logDeriv_le_of_finite_re_zeros hc4.le
    (f := f) (f' := f') (fun x => hasDerivAt_edPoly_horiz a hs T x)
    (continuous_edPoly_horiz a hs T) (continuous_deriv_edPoly_horiz a hs T)
    (fun x hx => hne x hx) Z hZmem
  have hcongr : ∀ x ∈ Set.uIcc c (4 : ℝ),
      (x - c) * (f' x / f x).im
        = (x - c) * (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x _
    rw [hf'def, hfdef, logDeriv_apply]
  rw [intervalIntegral.integral_congr hcongr] at hbound
  refine le_trans hbound ?_
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ)
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
    have hsubc : (Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card ≤ Z.card :=
      Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun p q h => Complex.ofReal_inj.mp h)
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ K ∧ edPolyTrace a s T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [hZdef, Set.Finite.mem_toFinset] at hx
      exact hx
    have hle := card_le_divisor_sum hKcompact hana hord _ hS
    rw [himg] at hle
    have hjensen := edPolyTrace_count_le a hs T hr0 hr8 hm hM1 hcentre hmass
    have hcast : ((Z.card : ℤ) : ℝ)
        ≤ ((∑ᶠ u, MeromorphicOn.divisor (edPolyTrace a s T) K u : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hsubc
    push_cast at hcast
    linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hwidth : (0 : ℝ) < 4 - c := by linarith
  have hstep : (((Z.filter (fun z => z ∈ Set.Ioo c (4 : ℝ))).card : ℝ) + 1) * Real.pi
      ≤ (Real.log (Mb / m) / Real.log (8 / (4 - c)) + 1) * Real.pi := by
    rw [← hr]
    exact mul_le_mul_of_nonneg_right (by linarith [hcard]) hπ.le
  nlinarith [hstep, hwidth]

end RHTower

end
