import GaloisForLFunctions.RHTower.EulerSquarefreeWickCompletedJetOrientationRigidity

/-!
# Horizontal faithfulness of the completed EWQ jet

The countable EWQ jet is more than a nowhere-zero auxiliary family.  It is projectively faithful
to horizontal position.  Any scalar affine quasiperiod with nonzero real displacement would carry
one actual completed mod-12 zero repeatedly out of the unconditional open critical strip.  Hence
two scalar-projectively equal full jets must have equal real coordinates.

This gives EWQ-V a coefficient-faithful, dimension-preserving horizontal color on the original
divisor fibre: no finite auxiliary tensor dimension or choice of one nonvanishing derivative is
needed.  It does not assert that all Xi-divisor colors are fixed by the orientation involution.
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A scalar affine translate of the primitive completed EWQ carrier cannot have nonzero
horizontal displacement. -/
theorem eulerWickPrimitiveCompletedInteraction_no_horizontal_quasiperiod
    {omega c : ℂ} (homega : omega.re ≠ 0) :
    ¬ ∀ z : ℂ,
      eulerWickQuadraticPrimitiveCompletedInteraction (z + omega) =
        c * eulerWickQuadraticPrimitiveCompletedInteraction z := by
  intro hshift
  obtain ⟨rho, hrho⟩ :=
    _root_.RHTower.exists_completedLFunction_eq_zero quadraticCharacterTwelve_ne_one
  have hrhoJ : eulerWickQuadraticPrimitiveCompletedInteraction rho = 0 := by
    simp [eulerWickQuadraticPrimitiveCompletedInteraction, _root_.RHTower.dirichletXi,
      hrho]
  have hiterate : ∀ n : ℕ,
      eulerWickQuadraticPrimitiveCompletedInteraction (rho + (n : ℂ) * omega) =
        c ^ n * eulerWickQuadraticPrimitiveCompletedInteraction rho := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          eulerWickQuadraticPrimitiveCompletedInteraction
              (rho + ((n + 1 : ℕ) : ℂ) * omega) =
            eulerWickQuadraticPrimitiveCompletedInteraction
              ((rho + (n : ℂ) * omega) + omega) := by
                congr 1
                push_cast
                ring
          _ = c * eulerWickQuadraticPrimitiveCompletedInteraction
              (rho + (n : ℂ) * omega) := hshift _
          _ = c * (c ^ n * eulerWickQuadraticPrimitiveCompletedInteraction rho) := by
            rw [ih]
          _ = c ^ (n + 1) * eulerWickQuadraticPrimitiveCompletedInteraction rho := by
            rw [pow_succ]
            ring
  have hzero : ∀ n : ℕ,
      DirichletCharacter.completedLFunction quadraticCharacterTwelve
        (rho + (n : ℂ) * omega) = 0 := by
    intro n
    have hJzero :
        eulerWickQuadraticPrimitiveCompletedInteraction (rho + (n : ℂ) * omega) = 0 := by
      rw [hiterate, hrhoJ, mul_zero]
    rw [eulerWickQuadraticPrimitiveCompletedInteraction,
      _root_.RHTower.dirichletXi] at hJzero
    exact (mul_eq_zero.mp hJzero).resolve_left
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  rcases lt_or_gt_of_ne homega with hneg | hpos
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (rho.re / (-omega.re))
    have hprod : rho.re + (n : ℝ) * omega.re < 0 := by
      have hden : 0 < -omega.re := by linarith
      have := (div_lt_iff₀ hden).mp hn
      nlinarith
    have hstrip := _root_.RHTower.completedLFunction_zero_mem_openUnitStrip
      quadraticCharacterTwelve_ne_one quadraticCharacterTwelve_isPrimitive (hzero n)
    have hre : (rho + (n : ℂ) * omega).re = rho.re + (n : ℝ) * omega.re := by
      simp
    rw [hre] at hstrip
    linarith
  · obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((1 - rho.re) / omega.re)
    have hprod : 1 < rho.re + (n : ℝ) * omega.re := by
      have := (div_lt_iff₀ hpos).mp hn
      linarith
    have hstrip := _root_.RHTower.completedLFunction_zero_mem_openUnitStrip
      quadraticCharacterTwelve_ne_one quadraticCharacterTwelve_isPrimitive (hzero n)
    have hre : (rho + (n : ℂ) * omega).re = rho.re + (n : ℝ) * omega.re := by
      simp
    rw [hre] at hstrip
    linarith

/-- Scalar projective agreement of two complete EWQ jets. -/
def EulerWickPrimitiveCompletedJetsProjectivelyAgree (s t : ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ n : ℕ,
    iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction s =
      c * iteratedDeriv n eulerWickQuadraticPrimitiveCompletedInteraction t

/-- Full EWQ jet is projectively faithful to horizontal position.  Projective identification of
two complete jets forces equality of their real coordinates. -/
theorem re_eq_of_eulerWickPrimitiveCompletedJetsProjectivelyAgree
    {s t : ℂ} (hjets : EulerWickPrimitiveCompletedJetsProjectivelyAgree s t) :
    s.re = t.re := by
  obtain ⟨c, _hc, hjets⟩ := hjets
  by_contra hre
  apply eulerWickPrimitiveCompletedInteraction_no_horizontal_quasiperiod
    (omega := s - t) (c := c)
  · simp only [Complex.sub_re]
    exact sub_ne_zero.mpr hre
  · have hJanalytic : ∀ z : ℂ,
        AnalyticAt ℂ eulerWickQuadraticPrimitiveCompletedInteraction z := by
      intro z
      exact eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.differentiableOn
        |>.analyticOnNhd isOpen_univ z (Set.mem_univ z)
    let defect : ℂ → ℂ := fun z =>
      eulerWickQuadraticPrimitiveCompletedInteraction (s + z) -
        c * eulerWickQuadraticPrimitiveCompletedInteraction (t + z)
    have hleftAnalytic : ∀ z : ℂ,
        AnalyticAt ℂ (fun w => eulerWickQuadraticPrimitiveCompletedInteraction (s + w)) z := by
      intro z
      fun_prop
    have hrightAnalytic : ∀ z : ℂ,
        AnalyticAt ℂ (fun w => c *
          eulerWickQuadraticPrimitiveCompletedInteraction (t + w)) z := by
      intro z
      fun_prop
    have hflat : ∀ n : ℕ, iteratedDeriv n defect 0 = 0 := by
      intro n
      rw [show iteratedDeriv n defect 0 =
          iteratedDeriv n
              (fun z => eulerWickQuadraticPrimitiveCompletedInteraction (s + z)) 0 -
            iteratedDeriv n
              (fun z => c * eulerWickQuadraticPrimitiveCompletedInteraction (t + z)) 0 by
        exact GaloisForLFunctions.HTGeometry.iteratedDeriv_fun_sub n
          hleftAnalytic hrightAnalytic 0]
      rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add n hJanalytic s 0]
      rw [show iteratedDeriv n
          (fun z => c * eulerWickQuadraticPrimitiveCompletedInteraction (t + z)) 0 =
            c * iteratedDeriv n
              (fun z => eulerWickQuadraticPrimitiveCompletedInteraction (t + z)) 0 by
        exact congrFun (GaloisForLFunctions.iteratedDeriv_const_mul_field c
          (fun z => eulerWickQuadraticPrimitiveCompletedInteraction (t + z)) n) 0]
      rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_add n hJanalytic t 0]
      simp only [add_zero]
      exact sub_eq_zero.mpr (hjets n)
    have hdefectDifferentiable : Differentiable ℂ defect := by
      dsimp [defect]
      exact (eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.comp
        ((differentiable_const s).add differentiable_id)).sub
          ((differentiable_const c).mul
            (eulerWickQuadraticPrimitiveCompletedInteraction_differentiable.comp
              ((differentiable_const t).add differentiable_id)))
    have hdefectAnalytic : AnalyticOnNhd ℂ defect Set.univ :=
      hdefectDifferentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hgerm : defect =ᶠ[nhds 0] 0 :=
      _root_.HTGeometry.eventuallyEq_zero_of_iteratedDeriv_eq_zero
        (hdefectAnalytic 0 (Set.mem_univ 0)) hflat
    have hglobal : Set.EqOn defect 0 Set.univ :=
      hdefectAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ 0) hgerm
    intro z
    have hz := hglobal (Set.mem_univ (z - t))
    have heq :
        eulerWickQuadraticPrimitiveCompletedInteraction (s + (z - t)) =
          c * eulerWickQuadraticPrimitiveCompletedInteraction (t + (z - t)) := by
      simpa [defect, sub_eq_zero] using hz
    convert heq using 1 <;> ring

end

end GaloisForLFunctions.RHTower
