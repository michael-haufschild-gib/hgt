import GaloisForLFunctions.HTGeometry.EntireCompositionSteinmetz
import GaloisForLFunctions.HTGeometry.ReciprocalGammaHypertranscendental
import GaloisForLFunctions.HTGeometry.EulerQGammaHypertranscendence

/-!
# Hypertranscendence of entire compositions obeys the Boolean OR law

For nonconstant entire functions differential algebraicity is preserved and reflected by
composition (`EntireCompositionSteinmetz.differentiallyAlgebraic_comp_iff`).  Consequently:

* every finite composition of nonconstant entire functions is differentially algebraic exactly
  when every factor is, i.e. it is hypertranscendental exactly when some factor is;
* every iterate `f^{[n]}`, `n ≥ 1`, of a hypertranscendental nonconstant entire `f` is
  hypertranscendental.

The law fails for local germs: the reciprocal Gamma function and a local inverse of it are both
hypertranscendental germs, while their composite is the identity.  Global entire continuation is
therefore load-bearing.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Metric

noncomputable section

/-- A composite of nonconstant entire functions is nonconstant (open mapping theorem). -/
theorem comp_not_const {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) (hgnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c := by
  rintro ⟨c, hc⟩
  have hgan : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hfan : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  rcases hgan.is_constant_or_isOpen isPreconnected_univ with ⟨w, hw⟩ | hopen
  · exact hgnc ⟨w, fun z => hw z (mem_univ z)⟩
  · -- `f` equals `c` on the open image of `g`
    have himg : IsOpen (g '' univ) := hopen univ subset_rfl isOpen_univ
    have hev : ∀ᶠ w in nhds (g 0), f w = c := by
      filter_upwards [himg.mem_nhds ⟨0, mem_univ 0, rfl⟩] with w hw
      obtain ⟨z, -, rfl⟩ := hw
      exact hc z
    have hall := hfan.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => c) analyticOnNhd_const
      isPreconnected_univ (mem_univ (g 0)) hev
    exact hfnc ⟨c, fun w => hall (mem_univ w)⟩

/-- **Finite compositions.**  A composite `φ₁ ∘ ⋯ ∘ φₖ` of nonconstant entire functions is
differentially algebraic exactly when every factor is. -/
theorem differentiallyAlgebraic_foldr_comp_iff (L : List (ℂ → ℂ))
    (hL : ∀ φ ∈ L, Differentiable ℂ φ ∧ ¬ ∃ c : ℂ, ∀ z : ℂ, φ z = c) :
    (Differentiable ℂ (L.foldr (· ∘ ·) id) ∧ ¬ ∃ c : ℂ, ∀ z : ℂ, L.foldr (· ∘ ·) id z = c) ∧
      (DifferentiallyAlgebraic (L.foldr (· ∘ ·) id) ↔ ∀ φ ∈ L, DifferentiallyAlgebraic φ) := by
  induction L with
  | nil =>
      refine ⟨⟨differentiable_id, fun ⟨c, hc⟩ => ?_⟩, ?_⟩
      · have h0 := hc 0
        have h1 := hc 1
        simp only [List.foldr_nil, id] at h0 h1
        rw [← h1] at h0
        exact zero_ne_one h0
      · simp only [List.foldr_nil, List.not_mem_nil, false_imp_iff, imp_true_iff, iff_true]
        have h := differentiallyAlgebraic_polynomial Polynomial.X
        simp only [Polynomial.eval_X] at h
        exact h
  | cons φ L ih =>
      have hφ := hL φ List.mem_cons_self
      obtain ⟨⟨hLd, hLnc⟩, hLiff⟩ := ih fun ψ hψ => hL ψ (List.mem_cons_of_mem φ hψ)
      have hfold : (φ :: L).foldr (· ∘ ·) id = fun z => φ (L.foldr (· ∘ ·) id z) := rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hfold]
        exact hφ.1.comp hLd
      · rw [hfold]
        exact comp_not_const hφ.1 hLd hφ.2 hLnc
      · rw [hfold, differentiallyAlgebraic_comp_iff hφ.1 hLd hφ.2 hLnc, hLiff]
        simp only [List.mem_cons, forall_eq_or_imp]

/-- **Iterates.**  Every iterate `f^{[n+1]}` of a hypertranscendental nonconstant entire function is
hypertranscendental. -/
theorem not_differentiallyAlgebraic_iterate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) (hHT : ¬ DifferentiallyAlgebraic f) (n : ℕ) :
    ¬ DifferentiallyAlgebraic (f^[n + 1]) := by
  have hfold : ∀ m : ℕ, (List.replicate (m + 1) f).foldr (· ∘ ·) id = f^[m + 1] := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [List.replicate_succ, List.foldr_cons, ih]
        exact (Function.iterate_succ' f (m + 1)).symm
  have hL : ∀ φ ∈ List.replicate (n + 1) f, Differentiable ℂ φ ∧ ¬ ∃ c : ℂ, ∀ z : ℂ, φ z = c :=
    fun φ hφ => by
      rw [List.eq_of_mem_replicate hφ]
      exact ⟨hf, hfnc⟩
  obtain ⟨-, hiff⟩ := differentiallyAlgebraic_foldr_comp_iff _ hL
  rw [hfold n] at hiff
  intro hDA
  exact hHT ((hiff.mp hDA) f (List.mem_replicate.mpr ⟨by omega, rfl⟩))

/-- **The law fails for local germs.**  The reciprocal Gamma function `G` has a local analytic
inverse `γ`; neither germ satisfies an algebraic differential equation on its domain, but
`γ ∘ G` is the identity. -/
theorem exists_hypertranscendental_germ_pair :
    ∃ (G γ : ℂ → ℂ) (U V : Set ℂ), IsOpen U ∧ U.Nonempty ∧ IsOpen V ∧ V.Nonempty ∧
      AnalyticOnNhd ℂ G U ∧ AnalyticOnNhd ℂ γ V ∧ MapsTo G U V ∧ (∀ z ∈ U, γ (G z) = z) ∧
      ¬ DifferentiallyAlgebraicOn G U ∧ ¬ DifferentiallyAlgebraicOn γ V ∧
      DifferentiallyAlgebraicOn (fun z => γ (G z)) U := by
  set G : ℂ → ℂ := fun z => (Complex.Gamma z)⁻¹ with hG
  have hGd : Differentiable ℂ G := Complex.differentiable_one_div_Gamma
  have hGnc : ¬ ∃ c : ℂ, ∀ z : ℂ, G z = c := by
    rintro ⟨c, hc⟩
    apply hypertranscendental_invGamma
    have : G = fun _ => c := funext hc
    rw [← hG, this]
    simpa using differentiallyAlgebraic_polynomial (Polynomial.C c)
  obtain ⟨w₀, hw₀⟩ := exists_deriv_ne_zero hGd hGnc
  obtain ⟨γ, s, B, hs, hBo, hB₀, hγan, hGmaps, hγmaps, hγG, hGγ⟩ :=
    exists_localInverse_domains hGd hw₀
  -- a ball `V` around `G w₀` inside `B`, and `U = ball w₀ s ∩ G⁻¹ V`
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hBo (G w₀) hB₀
  set V : Set ℂ := ball (G w₀) ε with hV
  set U : Set ℂ := ball w₀ s ∩ G ⁻¹' V with hU
  have hVo : IsOpen V := isOpen_ball
  have hVne : V.Nonempty := ⟨G w₀, mem_ball_self hε⟩
  have hUo : IsOpen U := isOpen_ball.inter (hVo.preimage hGd.continuous)
  have hw₀U : w₀ ∈ U := ⟨mem_ball_self hs, mem_ball_self hε⟩
  have hGan : AnalyticOnNhd ℂ G univ := hGd.differentiableOn.analyticOnNhd isOpen_univ
  have hγV : MapsTo γ V U := by
    intro v hv
    refine ⟨hγmaps (hεB hv), ?_⟩
    show G (γ v) ∈ V
    rw [hGγ v (hεB hv)]
    exact hv
  have hGU : MapsTo G U V := fun z hz => hz.2
  have hγGU : ∀ z ∈ U, γ (G z) = z := fun z hz => hγG z hz.1
  have hGγV : ∀ v ∈ V, G (γ v) = v := fun v hv => hGγ v (hεB hv)
  have hGnot : ¬ DifferentiallyAlgebraicOn G U :=
    not_differentiallyAlgebraicOn_invGamma hUo ⟨w₀, hw₀U⟩
  refine ⟨G, γ, U, V, hUo, ⟨w₀, hw₀U⟩, hVo, hVne, fun z _ => hGan z (mem_univ z),
    fun v hv => hγan v (hεB hv), hGU, hγGU, hGnot, fun hγDA => ?_, ?_⟩
  · -- a differentially algebraic inverse would make `G` differentially algebraic on `U`
    exact hGnot (differentiallyAlgebraicOn_of_localInverse hVo (convex_ball _ _).isPreconnected
      hVne (infinite_of_mem_nhds (G w₀) (hVo.mem_nhds (mem_ball_self hε)))
      (fun z _ => hGan z (mem_univ z)) (fun v hv => hγan v (hεB hv)) hγV hGU hGγV hγGU hγDA)
  · -- the composite is the identity
    refine differentiallyAlgebraicOn_of_eqOn hUo (f := fun z => Polynomial.X.eval z)
      (fun z hz => by simp [hγGU z hz]) ?_
    exact differentiallyAlgebraicOn_of_differentiallyAlgebraic
      (differentiallyAlgebraic_polynomial Polynomial.X)

end

end GaloisForLFunctions.HTGeometry
