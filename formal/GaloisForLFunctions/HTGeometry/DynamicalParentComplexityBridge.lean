import GaloisForLFunctions.HTGeometry.FiniteClockUnitaryReferenceFrameMasterObservabilityUniversalityLaw

/-!
# Dynamical parent complexity bridge

Unitary evolution transports a parent Hamiltonian and its ground state
together.  Approximate preparation of the evolved state therefore forces
near-ground energy for the transported parent.  This is the exact bridge from
autonomous complexity growth to a dynamical NLTS statement.
-/

open scoped ComplexConjugate

namespace HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Real expectation of a bounded operator in a vector state. -/
def quantumExpectationReal (K : E →L[ℂ] E) (ψ : E) : ℝ :=
  RCLike.re (inner ℂ ψ (K ψ))

/-- Parent operator transported by a unitary frame. -/
def transportedParent (V K : E →L[ℂ] E) : E →L[ℂ] E :=
  V * K * V.adjoint

/-- Unitary transport intertwines the parent action on every evolved vector. -/
theorem transportedParent_apply_evolved
    (V K : E →L[ℂ] E) (ψ : E) (hleft : V.adjoint * V = 1) :
    transportedParent V K (V ψ) = V (K ψ) := by
  unfold transportedParent
  simp only [mul_apply_eq_comp]
  have hleftApply := congrArg (fun T : E →L[ℂ] E => T ψ) hleft
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    congrArg V (congrArg K hleftApply)

/-- Every parent eigenpair is transported with exactly the same eigenvalue. -/
theorem transportedParent_eigenvector
    (V K : E →L[ℂ] E) (ψ : E) (eigenvalue : ℂ)
    (hleft : V.adjoint * V = 1) (heigen : K ψ = eigenvalue • ψ) :
    transportedParent V K (V ψ) = eigenvalue • V ψ := by
  rw [transportedParent_apply_evolved V K ψ hleft, heigen, map_smul]

/-- The evolved parent has exactly the original energy on the evolved state. -/
theorem quantumExpectationReal_transportedParent_evolved
    (V K : E →L[ℂ] E) (ψ : E) (hleft : V.adjoint * V = 1) :
    quantumExpectationReal (transportedParent V K) (V ψ) =
      quantumExpectationReal K ψ := by
  unfold quantumExpectationReal transportedParent
  simp only [mul_apply_eq_comp]
  have hleftApply := congrArg (fun T : E →L[ℂ] E => T ψ) hleft
  simp only [mul_apply_eq_comp, one_apply_eq_self] at hleftApply
  rw [hleftApply]
  congr 1
  rw [← V.adjoint_inner_left]
  exact congrArg (fun y : E => inner ℂ y (K ψ)) hleftApply

omit [CompleteSpace E] in
/-- Bounded-operator expectations are `2‖K‖`-Lipschitz on the unit ball. -/
theorem norm_expectation_sub_expectation_le
    (K : E →L[ℂ] E) (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖inner ℂ x (K x) - inner ℂ y (K y)‖ ≤
      2 * ‖K‖ * ‖x - y‖ := by
  have hdecomp :
      inner ℂ x (K x) - inner ℂ y (K y) =
        inner ℂ (x - y) (K x) + inner ℂ y (K (x - y)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hdecomp]
  calc
    ‖inner ℂ (x - y) (K x) + inner ℂ y (K (x - y))‖ ≤
        ‖inner ℂ (x - y) (K x)‖ + ‖inner ℂ y (K (x - y))‖ :=
      norm_add_le _ _
    _ ≤ (‖x - y‖ * ‖K x‖) + (‖y‖ * ‖K (x - y)‖) :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖x - y‖ * (‖K‖ * ‖x‖)) +
        (‖y‖ * (‖K‖ * ‖x - y‖)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (K.le_opNorm x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (K.le_opNorm (x - y)) (norm_nonneg _))
    _ ≤ 2 * ‖K‖ * ‖x - y‖ := by
      have hK : 0 ≤ ‖K‖ := norm_nonneg _
      have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
      calc
        _ = (‖K‖ * ‖x - y‖) * (‖x‖ + ‖y‖) := by ring
        _ ≤ (‖K‖ * ‖x - y‖) * (1 + 1) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hx hy)
            (mul_nonneg hK hxy)
        _ = _ := by ring

omit [CompleteSpace E] in
theorem abs_quantumExpectationReal_sub_le
    (K : E →L[ℂ] E) (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |quantumExpectationReal K x - quantumExpectationReal K y| ≤
      2 * ‖K‖ * ‖x - y‖ := by
  rw [quantumExpectationReal, quantumExpectationReal, ← map_sub]
  exact (RCLike.norm_re_le_norm
    (inner ℂ x (K x) - inner ℂ y (K y))).trans
      (norm_expectation_sub_expectation_le K x y hx hy)

/-- Any normalized state close to the evolved state has correspondingly low
energy for the transported parent. -/
theorem near_evolvedState_implies_near_transportGroundEnergy
    (V K : E →L[ℂ] E) (ψ φ : E)
    (hleft : V.adjoint * V = 1)
    (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) {ε : ℝ}
    (hnear : ‖φ - V ψ‖ ≤ ε) :
    quantumExpectationReal (transportedParent V K) φ ≤
      quantumExpectationReal K ψ +
        2 * ‖transportedParent V K‖ * ε := by
  have hVψ : ‖V ψ‖ ≤ 1 := by
    have hisom : ‖V ψ‖ = ‖ψ‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      change ‖V ψ‖ ^ 2 = ‖ψ‖ ^ 2
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),
        norm_sq_eq_re_inner (𝕜 := ℂ)]
      rw [← V.adjoint_inner_left]
      have hleftApply := congrArg (fun T : E →L[ℂ] E => T ψ) hleft
      simp only [mul_apply_eq_comp, one_apply_eq_self] at hleftApply
      rw [hleftApply]
    rw [hisom]
    exact hψ
  have hbound := abs_quantumExpectationReal_sub_le
    (transportedParent V K) φ (V ψ) hφ hVψ
  have henergy := quantumExpectationReal_transportedParent_evolved V K ψ hleft
  rw [henergy] at hbound
  have hdiff :
      quantumExpectationReal (transportedParent V K) φ -
          quantumExpectationReal K ψ ≤
        2 * ‖transportedParent V K‖ * ‖φ - V ψ‖ :=
    (le_abs_self _).trans hbound
  have hK : 0 ≤ ‖transportedParent V K‖ := norm_nonneg _
  have hscale :
      2 * ‖transportedParent V K‖ * ‖φ - V ψ‖ ≤
        2 * ‖transportedParent V K‖ * ε := by
    exact mul_le_mul_of_nonneg_left hnear (mul_nonneg (by norm_num) hK)
  linarith

/-- A strict energy barrier for the transported parent certifies that a
candidate state is outside the requested approximation radius. -/
theorem transportEnergyBarrier_forbids_near_evolvedState
    (V K : E →L[ℂ] E) (ψ φ : E)
    (hleft : V.adjoint * V = 1)
    (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) {ε : ℝ}
    (hbarrier :
      quantumExpectationReal K ψ +
          2 * ‖transportedParent V K‖ * ε <
        quantumExpectationReal (transportedParent V K) φ) :
    ¬ ‖φ - V ψ‖ ≤ ε := by
  intro hnear
  exact (not_lt_of_ge
    (near_evolvedState_implies_near_transportGroundEnergy
      V K ψ φ hleft hψ hφ hnear)) hbarrier

end

end HTGeometry
