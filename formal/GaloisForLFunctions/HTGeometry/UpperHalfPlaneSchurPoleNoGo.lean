import GaloisForLFunctions.HTGeometry.UpperHalfPlaneSchurInterpolation

/-!
# Pole obstruction to sampled Schur positivity

A positive kernel on a higher open sampling half-plane interpolates to a
bounded holomorphic carrier.  Analytic uniqueness then propagates that bound
down to the boundary of a larger half-plane.  A nonzero numerator over a
vanishing denominator there is impossible.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An accumulation sampling set in the higher half-plane detects an
uncancelled pole on the boundary of the larger analytic half-plane. -/
theorem not_isPSDKernel_accumulationSet_of_uncancelled_pole
    {y₀ y₁ : ℝ} (hy₀ : 0 < y₀) (hy₁ : y₀ < y₁)
    (A : Set ℂ) (hA : A ⊆ {z : ℂ | y₁ < z.im})
    (p : ℂ) (hp : y₁ < p.im)
    (hfreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), z ∈ A)
    (H D : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | y₀ < z.im})
    (hD : AnalyticOnNhd ℂ D {z : ℂ | y₀ < z.im})
    (hDne : ∀ z : ℂ, y₀ < z.im → D z ≠ 0)
    (hHcont : ContinuousAt H ((y₀ : ℂ) * I))
    (hDcont : ContinuousAt D ((y₀ : ℂ) * I))
    (hHzero : H ((y₀ : ℂ) * I) ≠ 0)
    (hDzero : D ((y₀ : ℂ) * I) = 0) :
    ¬ IsPSDKernel (fun z w : A =>
        upperHalfPlaneSchurKernel (fun u => H u / D u) z.1 w.1) := by
  intro hK
  let U : Set ℂ := {z : ℂ | y₀ < z.im}
  let V : Set ℂ := {z : ℂ | y₁ < z.im}
  have hUsub : U ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    change y₀ < z.im at hz
    change 0 < z.im
    linarith
  have hVsub : V ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    change y₁ < z.im at hz
    change 0 < z.im
    linarith
  have hVU : V ⊆ U := by
    intro z hz
    change y₁ < z.im at hz
    change y₀ < z.im
    linarith
  have hAup : A ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact hVsub (hA hz)
  obtain ⟨F, hFana, hFbound, hFval⟩ :=
    exists_upperHalfPlane_schur_interpolant A hAup
      (fun u => H u / D u) hK
  have hQana : AnalyticOnNhd ℂ (fun u => H u / D u) U := by
    exact hH.div hD (fun z hz => hDne z hz)
  have hFanaU : AnalyticOnNhd ℂ F U := hFana.mono hUsub
  have hUpre : IsPreconnected U := (convex_halfSpace_im_gt y₀).isPreconnected
  have hpU : p ∈ U := hVU hp
  have hEqFreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), F z = H z / D z :=
    hfreq.mono (fun z hz => hFval z hz)
  have hEq : EqOn F (fun u => H u / D u) U :=
    hFanaU.eqOn_of_preconnected_of_frequently_eq hQana hUpre hpU hEqFreq
  have hbound (z : ℂ) (hz : z ∈ U) : ‖H z‖ ≤ ‖D z‖ := by
    have hDz : D z ≠ 0 := hDne z hz
    have hzUp : 0 < z.im := hUsub hz
    have hQ : ‖H z / D z‖ ≤ 1 := by
      calc
        ‖H z / D z‖ = ‖F z‖ := congrArg norm (hEq hz).symm
        _ ≤ 1 := hFbound z hzUp
    rw [norm_div] at hQ
    exact (div_le_one (norm_pos_iff.mpr hDz)).mp hQ
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let zseq : ℕ → ℂ := fun n => (((y₀ + t n : ℝ) : ℂ) * I)
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hzseqU (n : ℕ) : zseq n ∈ U := by
    change y₀ < (zseq n).im
    have him : (zseq n).im = y₀ + t n := by simp [zseq, Complex.mul_im]
    rw [him]
    linarith [htpos n]
  have htlim : Tendsto t atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hzlim : Tendsto zseq atTop (nhds ((y₀ : ℂ) * I)) := by
    have hreal : Tendsto (fun n : ℕ => y₀ + t n) atTop (nhds y₀) := by
      simpa using (tendsto_const_nhds.add htlim)
    have hcomplex : Tendsto (fun n : ℕ => ((y₀ + t n : ℝ) : ℂ)) atTop
        (nhds (y₀ : ℂ)) := Complex.continuous_ofReal.tendsto y₀ |>.comp hreal
    exact hcomplex.mul_const I
  have hHlim : Tendsto (fun n => ‖H (zseq n)‖) atTop
      (nhds ‖H ((y₀ : ℂ) * I)‖) :=
    (hHcont.tendsto.comp hzlim).norm
  have hDlim : Tendsto (fun n => ‖D (zseq n)‖) atTop
      (nhds ‖D ((y₀ : ℂ) * I)‖) :=
    (hDcont.tendsto.comp hzlim).norm
  have hle : ‖H ((y₀ : ℂ) * I)‖ ≤ ‖D ((y₀ : ℂ) * I)‖ :=
    le_of_tendsto_of_tendsto' hHlim hDlim (fun n => hbound (zseq n) (hzseqU n))
  rw [hDzero, norm_zero] at hle
  exact hHzero (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- A quotient with an uncancelled boundary-approached pole cannot have a
positive Schur kernel on the higher open half-plane. -/
theorem not_isPSDKernel_upperHalfPlane_of_uncancelled_pole
    {y₀ y₁ : ℝ} (hy₀ : 0 < y₀) (hy₁ : y₀ < y₁)
    (H D : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | y₀ < z.im})
    (hD : AnalyticOnNhd ℂ D {z : ℂ | y₀ < z.im})
    (hDne : ∀ z : ℂ, y₀ < z.im → D z ≠ 0)
    (hHcont : ContinuousAt H ((y₀ : ℂ) * I))
    (hDcont : ContinuousAt D ((y₀ : ℂ) * I))
    (hHzero : H ((y₀ : ℂ) * I) ≠ 0)
    (hDzero : D ((y₀ : ℂ) * I) = 0) :
    ¬ IsPSDKernel (fun z w : {z : ℂ | y₁ < z.im} =>
        upperHalfPlaneSchurKernel (fun u => H u / D u) z.1 w.1) := by
  let V : Set ℂ := {z : ℂ | y₁ < z.im}
  let p : ℂ := ((y₁ + 1 : ℝ) : ℂ) * I
  have hp : y₁ < p.im := by simp [p]
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_im
  have hdense : Dense ({p}ᶜ : Set ℂ) := dense_compl_singleton p
  have hpclose : p ∈ closure (V ∩ ({p}ᶜ : Set ℂ)) :=
    hdense.open_subset_closure_inter hVopen hp
  have hfreq : ∃ᶠ z in nhdsWithin p ({p}ᶜ), z ∈ V :=
    frequently_nhdsWithin_iff.mpr
      ((mem_closure_iff_frequently.mp hpclose).mono (fun z hz => ⟨hz.1, hz.2⟩))
  exact not_isPSDKernel_accumulationSet_of_uncancelled_pole
    hy₀ hy₁ V (by intro z hz; exact hz) p hp hfreq
    H D hH hD hDne hHcont hDcont hHzero hDzero

end

end GaloisForLFunctions.HTGeometry
