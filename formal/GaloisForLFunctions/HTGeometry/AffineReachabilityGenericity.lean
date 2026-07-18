import GaloisForLFunctions.HTGeometry.ControlPullbackNowhereDense

/-!
# Genericity from affine reachability

A parameter map into a jet space is rarely linear.  The Herglotz chart `u ↦ exp u` is the standard
example: the jet map is linear in the density, not in the parameter.  The classical remedy is
parametric transversality — differentiate the chart and ask the derivative to be surjective.

That derivative is not needed.  It is enough that the reachable jets from a small parameter ball
contain an *affine* image `F u₀ + L h` of a small ball, for some surjective continuous linear `L`.
For the exponential chart this holds exactly, with no linearization error, by perturbing the
density multiplicatively: replacing `exp u₀` by `exp u₀ * (1 + h)` moves the parameter by
`log (1 + h)` and moves the jets by exactly `L h`.

Under that hypothesis the reachable set contains a neighbourhood of `F u₀`, and a nonzero
polynomial cannot vanish on a neighbourhood, so nondegenerate parameters are dense.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Genericity from affine reachability.**  If from every parameter and every accuracy the
reachable jets contain an affine image of a ball under a surjective continuous linear map, then the
parameters on which a fixed nonzero polynomial does not degenerate are dense.  No differentiability
of the parameter map is used. -/
theorem dense_nondegenerate_of_affine_reachability
    {X σ : Type*} [Fintype σ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → (σ → ℂ)) (P : MvPolynomial σ ℂ) (hP : P ≠ 0)
    (hreach : ∀ u₀ : X, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L : X →L[ℝ] (σ → ℂ), Function.Surjective L ∧
        ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧ F u = F u₀ + L h) :
    Dense {u : X | MvPolynomial.eval (F u) P ≠ 0} := by
  classical
  rw [Metric.dense_iff]
  intro u₀ ε hε
  obtain ⟨δ, hδ, L, hLsurj, hreach'⟩ := hreach u₀ ε hε
  -- The affine image of a ball is an open neighbourhood of `F u₀`.
  have hopen : IsOpen (L '' Metric.ball (0 : X) δ) :=
    L.isOpenMap hLsurj _ Metric.isOpen_ball
  set U : Set (σ → ℂ) :=
    (fun y : σ → ℂ => y - F u₀) ⁻¹' (L '' Metric.ball (0 : X) δ) with hU
  have hUopen : IsOpen U :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hUne : U.Nonempty := by
    refine ⟨F u₀, ?_⟩
    rw [hU, Set.mem_preimage, sub_self]
    exact ⟨0, Metric.mem_ball_self hδ, map_zero L⟩
  -- A nonzero polynomial is nonzero somewhere on every nonempty open set.
  have hdense := mvPolynomial_nonzero_eval_dense P hP
  obtain ⟨y, hyU, hyP⟩ := hdense.inter_open_nonempty U hUopen hUne
  obtain ⟨h, hhball, hhL⟩ := hyU
  have hhnorm : ‖h‖ < δ := by
    simpa [Metric.mem_ball, dist_zero_right] using hhball
  obtain ⟨u, hudist, hFu⟩ := hreach' h hhnorm
  refine ⟨u, ?_, ?_⟩
  · exact Metric.mem_ball.mpr hudist
  · show MvPolynomial.eval (F u) P ≠ 0
    have hy : F u₀ + L h = y := by
      rw [hhL]
      simp
    rw [hFu, hy]
    exact hyP

end

end GaloisForLFunctions.HTGeometry
