/-
# Deck-normalized modular-lambda Montel extraction

The raw target `z ↦ λ(cayleyInv z)` has no continuous closed-disk extension.  The useful
normal-family branch is therefore the deck-normalized one: after replacing each lift by an
equivalent deck translate, keep one basepoint in a strict subdisk.  Montel then produces an
interior limit, and the modular target may be composed on a smaller closed ball.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaCuspNormal
import GaloisForLFunctions.Bottcher.DiskLiftBoundary

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped UpperHalfPlane

namespace Bottcher

noncomputable section

/-- A compact subset of the upper half-plane has Cayley coordinates uniformly inside the unit disk. -/
theorem exists_cayley_norm_bound_lt_one_of_isCompact {T : Set ℍ} (hT : IsCompact T) :
    ∃ s : ℝ, s < 1 ∧ ∀ τ ∈ T, ‖cayley (τ : ℂ)‖ ≤ s := by
  have hcayley : Continuous fun τ : ℍ => cayley (τ : ℂ) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hden : (τ : ℂ) + Complex.I ≠ 0 := by
      intro h
      have him : (τ : ℂ).im + 1 = 0 := by
        simpa [Complex.add_im] using congrArg Complex.im h
      linarith [τ.2]
    exact (cayley_differentiableAt hden).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  rcases T.eq_empty_or_nonempty with hempty | hne
  · refine ⟨0, by norm_num, ?_⟩
    intro τ hτ
    rw [hempty] at hτ
    exact hτ.elim
  · obtain ⟨τ₀, hτ₀, hmax⟩ :=
      hT.exists_isMaxOn hne (continuous_norm.comp hcayley).continuousOn
    refine ⟨‖cayley (τ₀ : ℂ)‖, cayley_norm_lt_one τ₀.2, ?_⟩
    intro τ hτ
    exact hmax hτ

/-- If all desired basepoint values have representatives in one compact subset of `ℍ`, then their
Cayley representatives satisfy a single strict disk bound. -/
theorem exists_uniform_cayley_bound_of_compact_preimages {a : ℕ → ℂ} {T : Set ℍ}
    (hT : IsCompact T)
    (hpre : ∀ n, ∃ τ : ℍ, τ ∈ T ∧ modularLambda (τ : ℂ) = a n) :
    ∃ s : ℝ, s < 1 ∧
      ∀ n, ∃ τ : ℍ, modularLambda (τ : ℂ) = a n ∧ ‖cayley (τ : ℂ)‖ ≤ s := by
  obtain ⟨s, hs, hbound⟩ := exists_cayley_norm_bound_lt_one_of_isCompact hT
  refine ⟨s, hs, ?_⟩
  intro n
  obtain ⟨τ, hτT, hτeq⟩ := hpre n
  exact ⟨τ, hτeq, hbound τ hτT⟩

/-- Spherical normality of modular-lambda pushforwards from deck-normalized disk lifts.

The hypotheses are exactly the output wanted from the deck-normalization step: the lifted maps
are holomorphic disk maps and their center values stay in a fixed strict subdisk.  The conclusion
is local, on a smaller closed ball whose radius is produced by the proof. -/
theorem spherical_normal_of_modularDiskTarget_basepoint_strict_lifts
    {Fseq : ℕ → ℂ → EuclideanSpace ℝ (Fin 3)} {gseq : ℕ → ℂ → ℂ}
    {c : ℂ} {R ρ s₀ : ℝ}
    (hρ0 : 0 < ρ) (hρR : ρ < R / 2) (hs₀ : s₀ < 1)
    (hgdiff : ∀ n, DifferentiableOn ℂ (gseq n) (ball c R))
    (hgbd : ∀ n z, z ∈ ball c R → ‖gseq n z‖ ≤ 1)
    (hgbase : ∀ n, ‖gseq n c‖ ≤ s₀)
    (heq : ∀ n, Set.EqOn
      (fun z => stereo (modularLambda (cayleyInv (gseq n z)))) (Fseq n) (ball c R)) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)) (r : ℝ),
      StrictMono φ ∧ 0 < r ∧ closedBall c r ⊆ closedBall c ρ ∧
      ContinuousOn G (closedBall c r) ∧
      TendstoUniformlyOn (fun k z => Fseq (φ k) z) G atTop (closedBall c r) := by
  obtain ⟨φ, gl, hφ, hgconv, -⟩ :=
    montel_subseq hρ0 hρR hgdiff (fun n z hz => hgbd n z hz)
  have hρRball : closedBall c ρ ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hseqcont : ∀ k, ContinuousOn (gseq (φ k)) (closedBall c ρ) := by
    intro k
    exact ((hgdiff (φ k)).continuousOn).mono hρRball
  have hglcont : ContinuousOn gl (closedBall c ρ) :=
    hgconv.continuousOn (Frequently.of_forall hseqcont)
  have hcρ : c ∈ closedBall c ρ := mem_closedBall_self hρ0.le
  have hglbase_le : ‖gl c‖ ≤ s₀ := by
    refine le_of_tendsto ((hgconv.tendsto_at hcρ).norm) ?_
    exact Eventually.of_forall (fun k => hgbase (φ k))
  have hglbase : ‖gl c‖ < 1 := lt_of_le_of_lt hglbase_le hs₀
  obtain ⟨r, s, hr0, hs1, hrsub, hgls⟩ :=
    exists_closedBall_norm_bound_lt_one_of_continuousOn hρ0 hglcont hglbase
  have hconv_mod :
      TendstoUniformlyOn
        (fun k z => stereo (modularLambda (cayleyInv (gseq (φ k) z))))
        (fun z => stereo (modularLambda (cayleyInv (gl z)))) atTop (closedBall c r) :=
    tendstoUniformlyOn_stereo_modularDiskTarget_of_lift_limit_strict
      (K := closedBall c r) hs1 hgls (hgconv.mono hrsub)
  have hGcont : ContinuousOn
      (fun z => stereo (modularLambda (cayleyInv (gl z)))) (closedBall c r) := by
    have hglcont_r : ContinuousOn gl (closedBall c r) := hglcont.mono hrsub
    exact (continuousOn_stereo_modularDiskTarget_closedBall hs1).comp hglcont_r
      (fun z hz => by
        rw [mem_closedBall, dist_zero_right]
        exact hgls z hz)
  have hconv_F : TendstoUniformlyOn (fun k z => Fseq (φ k) z)
      (fun z => stereo (modularLambda (cayleyInv (gl z)))) atTop (closedBall c r) := by
    refine hconv_mod.congr ?_
    filter_upwards with k z hz
    exact heq (φ k) (hρRball (hrsub hz))
  exact ⟨φ, fun z => stereo (modularLambda (cayleyInv (gl z))), r,
    hφ, hr0, hrsub, hGcont, hconv_F⟩

end

end Bottcher
