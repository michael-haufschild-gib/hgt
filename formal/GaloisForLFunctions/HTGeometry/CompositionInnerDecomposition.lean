import GaloisForLFunctions.HTGeometry.CompositionDecompositionLaw
import GaloisForLFunctions.HTGeometry.ParabolicFatouJetRealization
import GaloisForLFunctions.HTGeometry.EllipticMeroFieldDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EulerQGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum
import GaloisForLFunctions.HTGeometry.FirstOrderCompositionDefect
import GaloisForLFunctions.HTGeometry.RGTowerCoherence

/-!
# Recovering the inner factor of a composition

If the outer factor and the composition are both differentially algebraic, so is the inner factor.
Near a point where both derivatives are nonzero the outer factor has a local analytic inverse; that
inverse is differentially algebraic by `differentiallyAlgebraicOn_of_localInverse`, and the inner
factor is its composite with the composition.

This is the companion of `CompositionDecompositionLaw.differentiallyAlgebraic_of_comp`, which
recovers the *outer* factor from the inner one and the composition.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set Bottcher
open scoped UnivMeroFieldInstances

variable {f g : ℂ → ℂ}

/-- A nonconstant entire function has a point with nonzero derivative. -/
theorem exists_deriv_ne_zero (hf : Differentiable ℂ f)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) : ∃ w : ℂ, deriv f w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hfnc ⟨f 0, fun z => is_const_of_deriv_eq_zero hf hcon z 0⟩

/-- **A regular point of the composition.**  Both derivatives are nonzero off a countable set. -/
theorem exists_regular_point (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    ∃ z₀ : ℂ, deriv g z₀ ≠ 0 ∧ deriv f (g z₀) ≠ 0 := by
  classical
  have hfd : Differentiable ℂ (deriv f) := by
    have han : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
      hf.differentiableOn.analyticOnNhd isOpen_univ
    exact fun z => (han.deriv z (Set.mem_univ z)).differentiableAt
  have hgd : Differentiable ℂ (deriv g) := by
    have han : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
      hg.differentiableOn.analyticOnNhd isOpen_univ
    exact fun z => (han.deriv z (Set.mem_univ z)).differentiableAt
  have hgne : ∃ w : ℂ, deriv g w ≠ 0 := exists_deriv_ne_zero hg hgnc
  have hfne : ∃ w : ℂ, deriv f w ≠ 0 := exists_deriv_ne_zero hf hfnc
  obtain ⟨z₁, hz₁⟩ := exists_ne_zero_comp hfd hg hfne hgnc
  have hc1 : {w : ℂ | deriv g w = 0}.Countable :=
    countable_zeroSet_of_exists_ne_zero hgd hgne
  have hc2 : {z : ℂ | deriv f (g z) = 0}.Countable :=
    countable_zeroSet_of_exists_ne_zero (fun z => (hfd (g z)).comp z (hg z)) ⟨z₁, hz₁⟩
  have hcov : ¬ (Set.univ : Set ℂ) ⊆ {w : ℂ | deriv g w = 0} ∪ {z : ℂ | deriv f (g z) = 0} := by
    intro hsub
    exact Set.not_countable_univ ((hc1.union hc2).mono hsub)
  obtain ⟨z₀, -, hz₀⟩ := Set.not_subset.mp hcov
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hz₀
  exact ⟨z₀, hz₀.1, hz₀.2⟩

/-- **A local analytic inverse with explicit domains.**  At a point where the derivative is nonzero
an entire function restricts to a bijection between a ball and an open set, with an analytic
inverse. -/
theorem exists_localInverse_domains (hf : Differentiable ℂ f) {w₀ : ℂ} (hd : deriv f w₀ ≠ 0) :
    ∃ (γ : ℂ → ℂ) (s : ℝ) (B : Set ℂ), 0 < s ∧ IsOpen B ∧ f w₀ ∈ B ∧
      AnalyticOnNhd ℂ γ B ∧
      Set.MapsTo f (ball w₀ s) B ∧ Set.MapsTo γ B (ball w₀ s) ∧
      (∀ w ∈ ball w₀ s, γ (f w) = w) ∧ (∀ v ∈ B, f (γ v) = v) := by
  classical
  have hfan : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨γ, hγan, hγf, hfγ⟩ :=
    exists_localInverse_analytic (hfan w₀ (Set.mem_univ w₀)) hd
  have hγ0 : γ (f w₀) = w₀ := hγf.self_of_nhds
  -- a ball on which `γ ∘ f = id`
  obtain ⟨s₀, hs₀, hs₀mem⟩ := Metric.eventually_nhds_iff_ball.mp hγf
  -- a ball on which `γ` is analytic and `f ∘ γ = id`
  obtain ⟨δ₀, hδ₀, hδ₀mem⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hfγ.and hγan.eventually_analyticAt)
  -- shrink the source ball so that `f` lands in the target ball
  have hcont : ContinuousAt f w₀ := (hf w₀).continuousAt
  obtain ⟨s₁, hs₁, hs₁mem⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont (Metric.ball_mem_nhds (f w₀) hδ₀))
  have hcont' : ContinuousOn γ (ball (f w₀) δ₀) := by
    intro v hv
    exact ((hδ₀mem v hv).2).continuousAt.continuousWithinAt
  refine ⟨γ, min s₀ s₁, ball (f w₀) δ₀ ∩ γ ⁻¹' ball w₀ (min s₀ s₁),
    lt_min hs₀ hs₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont'.isOpen_inter_preimage Metric.isOpen_ball
      (t := ball w₀ (min s₀ s₁)) Metric.isOpen_ball
  · refine ⟨Metric.mem_ball_self hδ₀, ?_⟩
    simp only [Set.mem_preimage, hγ0]
    exact Metric.mem_ball_self (lt_min hs₀ hs₁)
  · intro v hv
    exact (hδ₀mem v hv.1).2
  · intro w hw
    have hw₁ : w ∈ ball w₀ s₁ := ball_subset_ball (min_le_right _ _) hw
    have hw₀ : w ∈ ball w₀ s₀ := ball_subset_ball (min_le_left _ _) hw
    refine ⟨hs₁mem w hw₁, ?_⟩
    simp only [Set.mem_preimage, hs₀mem w hw₀]
    exact hw
  · intro v hv
    exact hv.2
  · intro w hw
    exact hs₀mem w (ball_subset_ball (min_le_left _ _) hw)
  · intro v hv
    exact (hδ₀mem v hv.1).1

set_option maxHeartbeats 800000 in
/-- **Recovering the inner factor of a composition.**  If a nonconstant entire outer factor and the
composition are both differentially algebraic, so is the nonconstant entire inner factor. -/
theorem differentiallyAlgebraic_inner_of_comp
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    (hfDA : DifferentiallyAlgebraic f)
    (hcDA : DifferentiallyAlgebraic (fun z => f (g z))) :
    DifferentiallyAlgebraic g := by
  classical
  obtain ⟨z₀, hgz, hfz⟩ := exists_regular_point hf hg hfnc hgnc
  obtain ⟨γ, s, B, hs, hBo, hfw₀B, hγan, hfmaps, hγmaps, hγf, hfγ⟩ :=
    exists_localInverse_domains hf hfz
  have hfanUniv : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hcompdiff : Differentiable ℂ (fun z => f (g z)) := fun z => (hf (g z)).comp z (hg z)
  have hcompanUniv : AnalyticOnNhd ℂ (fun z => f (g z)) (Set.univ : Set ℂ) :=
    hcompdiff.differentiableOn.analyticOnNhd isOpen_univ
  -- the inverse is differentially algebraic on `B`
  have hγDA : DifferentiallyAlgebraicOn γ B :=
    differentiallyAlgebraicOn_of_localInverse Metric.isOpen_ball
      ((convex_ball (g z₀) s).isPreconnected) (Metric.nonempty_ball.mpr hs)
      (infinite_ball (g z₀) hs) hγan (fun z _ => hfanUniv z (Set.mem_univ z))
      hfmaps hγmaps hγf hfγ (differentiallyAlgebraicOn_of_differentiallyAlgebraic hfDA)
  -- a ball inside `B`
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hBo _ hfw₀B
  have hγDA' : DifferentiallyAlgebraicOn γ (ball (f (g z₀)) δ) := by
    obtain ⟨n, P, hP0, hPv⟩ := hγDA
    exact ⟨n, P, hP0, fun z hz => hPv z (hδsub hz)⟩
  have hγan' : AnalyticOnNhd ℂ γ (ball (f (g z₀)) δ) := fun v hv => hγan v (hδsub hv)
  -- the composition has a local inverse at `z₀`
  have hcderiv : deriv (fun z => f (g z)) z₀ = deriv f (g z₀) * deriv g z₀ :=
    deriv_comp z₀ (hf (g z₀)) (hg z₀)
  have hcne : deriv (fun z => f (g z)) z₀ ≠ 0 := by
    rw [hcderiv]
    exact mul_ne_zero hfz hgz
  obtain ⟨ρ, hρan, hρc, hcρ⟩ :=
    exists_localInverse_analytic (hcompanUniv z₀ (Set.mem_univ z₀)) hcne
  have hρ0 : ρ (f (g z₀)) = z₀ := hρc.self_of_nhds
  -- a source ball on which `g` lands in `A` and the composition lands in the smaller target ball
  obtain ⟨t₁, ht₁, ht₁mem⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hg z₀).continuousAt (Metric.ball_mem_nhds (g z₀) hs))
  obtain ⟨t₂, ht₂, ht₂mem⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hcompdiff z₀).continuousAt (Metric.ball_mem_nhds (f (g z₀)) hδ))
  set t : ℝ := min t₁ t₂ with ht
  have htpos : 0 < t := lt_min ht₁ ht₂
  have hgW : ∀ z ∈ ball z₀ t, g z ∈ ball (g z₀) s := fun z hz =>
    ht₁mem z (ball_subset_ball (min_le_left _ _) hz)
  have hcW : Set.MapsTo (fun z => f (g z)) (ball z₀ t) (ball (f (g z₀)) δ) := fun z hz =>
    ht₂mem z (ball_subset_ball (min_le_right _ _) hz)
  -- a target ball on which the composition's local inverse lands in the source ball
  obtain ⟨η₁, hη₁, hη₁mem⟩ := Metric.eventually_nhds_iff_ball.mp hcρ
  obtain ⟨η₂, hη₂, hη₂mem⟩ := Metric.eventually_nhds_iff_ball.mp
    (hρan.continuousAt (by rw [hρ0]; exact Metric.ball_mem_nhds z₀ htpos))
  set η : ℝ := min (min η₁ η₂) δ with hη
  have hηpos : 0 < η := lt_min (lt_min hη₁ hη₂) hδ
  -- the substitution is faithful
  have hfaith : SubstitutionFaithful (ball z₀ t) (ball (f (g z₀)) δ) (fun z => f (g z)) := by
    refine substitutionFaithful_of_rightInverse (ρ := ρ) (W := ball (f (g z₀)) η)
      ((convex_ball (f (g z₀)) δ).isPreconnected)
      Metric.isOpen_ball (Metric.nonempty_ball.mpr hηpos)
      (ball_subset_ball (min_le_right _ _)) (fun v hv => ?_) (fun v hv => ?_)
    · exact hη₂mem v (ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _)) hv)
    · exact hη₁mem v (ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hv)
  -- the composite with the inverse is differentially algebraic on the source ball
  have hstep : DifferentiallyAlgebraicOn (fun z => γ (f (g z))) (ball z₀ t) :=
    differentiallyAlgebraicOn_comp Metric.isOpen_ball ((convex_ball z₀ t).isPreconnected)
      (Metric.nonempty_ball.mpr htpos) (infinite_ball z₀ htpos)
      Metric.isOpen_ball ((convex_ball (f (g z₀)) δ).isPreconnected)
      (Metric.nonempty_ball.mpr hδ) (infinite_ball (f (g z₀)) hδ)
      hγan' (fun z _ => hcompanUniv z (Set.mem_univ z)) hcW hfaith hγDA'
      (differentiallyAlgebraicOn_of_differentiallyAlgebraic hcDA)
  -- and it is the inner factor there
  have heq : Set.EqOn (fun z => γ (f (g z))) g (ball z₀ t) := fun z hz => hγf (g z) (hgW z hz)
  exact differentiallyAlgebraic_of_differentiallyAlgebraicOn hg Metric.isOpen_ball
    (Metric.nonempty_ball.mpr htpos)
    (differentiallyAlgebraicOn_of_eqOn Metric.isOpen_ball heq hstep)

/-- **The substitution by a nonconstant entire function is faithful on the plane.** -/
theorem substitutionFaithful_univ (hg : Differentiable ℂ g)
    (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    SubstitutionFaithful (Set.univ : Set ℂ) (Set.univ : Set ℂ) g := by
  have hganUniv : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₀, hz₀⟩ := exists_deriv_ne_zero hg hgnc
  obtain ⟨ρ, -, -, hgρ⟩ :=
    exists_localInverse_analytic (hganUniv z₀ (Set.mem_univ z₀)) hz₀
  obtain ⟨η, hη, hηmem⟩ := Metric.eventually_nhds_iff_ball.mp hgρ
  exact substitutionFaithful_of_rightInverse (ρ := ρ) (W := ball (g z₀) η)
    isPreconnected_univ Metric.isOpen_ball (Metric.nonempty_ball.mpr hη)
    (Set.subset_univ _) (fun v _ => Set.mem_univ _) hηmem

/-- **Composition closure on the plane.**  The composite of two differentially algebraic entire
functions, the inner one nonconstant, is differentially algebraic. -/
theorem differentiallyAlgebraic_comp_entire (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    (hfDA : DifferentiallyAlgebraic f) (hgDA : DifferentiallyAlgebraic g) :
    DifferentiallyAlgebraic (fun z => f (g z)) := by
  have hfanUniv : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hganUniv : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hcompdiff : Differentiable ℂ (fun z => f (g z)) := fun z => (hf (g z)).comp z (hg z)
  have hstep := differentiallyAlgebraicOn_comp isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hfanUniv hganUniv (Set.mapsTo_univ _ _)
    (substitutionFaithful_univ hg hgnc)
    (differentiallyAlgebraicOn_of_differentiallyAlgebraic hfDA)
    (differentiallyAlgebraicOn_of_differentiallyAlgebraic hgDA)
  exact differentiallyAlgebraic_of_differentiallyAlgebraicOn hcompdiff isOpen_univ
    Set.univ_nonempty hstep

/-- **Recovering the outer factor.**  Restatement of
`CompositionDecompositionLaw.differentiallyAlgebraic_of_comp` for entire factors. -/
theorem differentiallyAlgebraic_outer_of_comp (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    (hgDA : DifferentiallyAlgebraic g)
    (hcDA : DifferentiallyAlgebraic (fun z => f (g z))) :
    DifferentiallyAlgebraic f := by
  have hganUniv : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hnc : ∀ c : ℂ, ∃ z, g z ≠ c := by
    intro c
    by_contra hcon
    push Not at hcon
    exact hgnc ⟨c, hcon⟩
  obtain ⟨z₀, hz₀⟩ := exists_deriv_ne_zero hg hgnc
  have hdne : analyticMeroElement (deriv g)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (fun z => ((hganUniv.deriv z (Set.mem_univ z)).differentiableAt))) ≠ 0 := by
    intro hzero
    exact hz₀ ((analyticMeroElement_eq_zero_iff _).mp hzero z₀ (Set.mem_univ z₀))
  exact differentiallyAlgebraic_of_comp hf hg hnc hdne
    (differentiallyAlgebraicOn_of_differentiallyAlgebraic hgDA)
    (differentiallyAlgebraicOn_of_differentiallyAlgebraic hcDA)

/-- **The Boolean composition law, modulo the both-hypertranscendental case.**  For nonconstant
entire `f` and `g`, the composite is differentially algebraic exactly when both factors are, once
the case of two hypertranscendental factors is excluded.  That excluded case is Steinmetz's
reduction theorem. -/
theorem differentiallyAlgebraic_comp_iff_of_gap
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c)
    (hgap : ¬ DifferentiallyAlgebraic f → ¬ DifferentiallyAlgebraic g →
      ¬ DifferentiallyAlgebraic (fun z => f (g z))) :
    DifferentiallyAlgebraic (fun z => f (g z)) ↔
      (DifferentiallyAlgebraic f ∧ DifferentiallyAlgebraic g) := by
  classical
  constructor
  · intro hc
    by_cases hfa : DifferentiallyAlgebraic f
    · exact ⟨hfa, differentiallyAlgebraic_inner_of_comp hf hg hfnc hgnc hfa hc⟩
    · by_cases hga : DifferentiallyAlgebraic g
      · exact ⟨differentiallyAlgebraic_outer_of_comp hf hg hgnc hga hc, hga⟩
      · exact absurd hc (hgap hfa hga)
  · rintro ⟨hfa, hga⟩
    exact differentiallyAlgebraic_comp_entire hf hg hgnc hfa hga

end GaloisForLFunctions.HTGeometry
