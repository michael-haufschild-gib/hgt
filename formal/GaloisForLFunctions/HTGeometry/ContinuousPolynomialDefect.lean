import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

/-!
# Polynomial defects pulled back along continuous linear observations

A finite polynomial relation in continuous linear observations has a closed zero set.  If one
source escapes the relation, then every affine line from an arbitrary source to that witness has a
nonzero endpoint polynomial; the one-variable root bound supplies escaping points at arbitrarily
small positive times.  Hence the defect has empty interior.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero set of a polynomial in continuous linear observations is closed. -/
theorem isClosed_continuousLinearMap_mvPolynomial_zero
    {X σ : Type*} [TopologicalSpace X] [AddCommMonoid X] [Module ℂ X]
    (L : X →L[ℂ] (σ → ℂ)) (P : MvPolynomial σ ℂ) :
    IsClosed {x : X | MvPolynomial.eval (L x) P = 0} := by
  exact isClosed_singleton.preimage (P.continuous_eval.comp L.continuous)

/-- One nonvanishing witness makes the nonzero locus of a polynomial observation dense. -/
theorem dense_continuousLinearMap_mvPolynomial_ne_zero_of_witness
    {X σ : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [ContinuousAdd X] [ContinuousSMul ℂ X]
    (L : X →L[ℂ] (σ → ℂ)) (P : MvPolynomial σ ℂ)
    (h : X) (hh : MvPolynomial.eval (L h) P ≠ 0) :
    Dense {x : X | MvPolynomial.eval (L x) P ≠ 0} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  rw [mem_closure_iff]
  intro o ho hxo
  let line : ℝ → X := fun t => x + (t : ℂ) • (h - x)
  have hline : Continuous line := by
    exact continuous_const.add
      (Complex.continuous_ofReal.smul continuous_const)
  have hzero : line 0 = x := by simp [line]
  have hopen : IsOpen (line ⁻¹' o) := ho.preimage hline
  have hzeroMem : (0 : ℝ) ∈ line ⁻¹' o := by
    simpa [hzero] using hxo
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzeroMem
  obtain ⟨ε, hε, hεη, hne⟩ :=
    exists_small_real_line_eval_ne_zero P (L x) (L h) hh hη
  have hεball : ε ∈ Metric.ball (0 : ℝ) η := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hε] using hεη
  have hlineMem : line ε ∈ o := hball hεball
  refine ⟨line ε, hlineMem, ?_⟩
  have hobs :
      L (line ε) = fun i ↦ L x i + (ε : ℂ) * (L h i - L x i) := by
    funext i
    simp [line, map_add, map_sub, Pi.smul_apply]
  change MvPolynomial.eval (L (line ε)) P ≠ 0
  rw [hobs]
  exact hne

/-- A polynomial defect with one escaping source has empty interior. -/
theorem interior_continuousLinearMap_mvPolynomial_zero_eq_empty_of_witness
    {X σ : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℂ X]
    [ContinuousAdd X] [ContinuousSMul ℂ X]
    (L : X →L[ℂ] (σ → ℂ)) (P : MvPolynomial σ ℂ)
    (h : X) (hh : MvPolynomial.eval (L h) P ≠ 0) :
    interior {x : X | MvPolynomial.eval (L x) P = 0} = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  have hset : {x : X | MvPolynomial.eval (L x) P = 0}ᶜ =
      {x : X | MvPolynomial.eval (L x) P ≠ 0} := by
    ext x
    simp
  rw [hset]
  exact dense_continuousLinearMap_mvPolynomial_ne_zero_of_witness L P h hh

end

end GaloisForLFunctions.HTGeometry
