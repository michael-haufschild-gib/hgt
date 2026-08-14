import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator

open Module Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A diagonal identity on a dense form core determines the full represented form and hence
the Friedrichs extension. -/
theorem boundedPerturbedFriedrichsOperator_extends_of_diagonal_formCore
    (J : V →L[ℂ] H) (B : H →L[ℂ] H) (hB : IsSelfAdjoint B)
    (hJinj : Function.Injective J) (hDense : Dense (J.range : Set H))
    (T : H →ₗ.[ℂ] H) (coreLift : T.domain →ₗ[ℂ] V)
    (hsection : ∀ x : T.domain, J (coreLift x) = (x : H))
    (hcoreDense : DenseRange coreLift)
    (hTformal : T.IsFormalAdjoint T)
    (hdiag : ∀ x : T.domain,
      inner ℂ (coreLift x) (coreLift x) +
          inner ℂ (B (x : H)) (x : H) =
        inner ℂ (T x) (x : H)) :
    T ≤ boundedPerturbedFriedrichsOperator J B hB := by
  apply boundedPerturbedFriedrichsOperator_extends_core
    J B hB hJinj hDense T coreLift hsection
  intro x v
  let q : T.domain → T.domain → ℂ := fun u w =>
    inner ℂ (coreLift u) (coreLift w) +
      inner ℂ (B (J (coreLift u))) (J (coreLift w))
  let t : T.domain → T.domain → ℂ := fun u w =>
    inner ℂ (T u) (w : H)
  have hBsymm : ∀ u w : H, inner ℂ (B u) w = inner ℂ u (B w) :=
    hB.isSymmetric
  have hqpol : ∀ u w : T.domain,
      q u w =
        (q (u + w) (u + w) - q (u - w) (u - w) -
            Complex.I * q (u + Complex.I • w) (u + Complex.I • w) +
          Complex.I * q (u - Complex.I • w) (u - Complex.I • w)) / 4 := by
    intro u w
    simp only [q, map_add, map_sub, map_smul, Submodule.coe_add,
      Submodule.coe_sub, Submodule.coe_smul, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_I, Complex.I_sq]
    rw [hBsymm (J (coreLift w)) (J (coreLift u))]
    ring
  have htpol : ∀ u w : T.domain,
      t u w =
        (t (u + w) (u + w) - t (u - w) (u - w) -
            Complex.I * t (u + Complex.I • w) (u + Complex.I • w) +
          Complex.I * t (u - Complex.I • w) (u - Complex.I • w)) / 4 := by
    intro u w
    simp only [t, LinearPMap.map_add, LinearPMap.map_sub, LinearPMap.map_smul,
      Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_I, Complex.I_sq]
    rw [hTformal w u]
    ring
  have hdiag' : ∀ u : T.domain, q u u = t u u := by
    intro u
    simpa only [q, t, hsection] using hdiag u
  have hcore : ∀ w : T.domain,
      inner ℂ (coreLift x) (coreLift w) +
          inner ℂ (B (x : H)) (w : H) =
        inner ℂ (T x) (w : H) := by
    intro w
    change q x w = t x w
    rw [hqpol, htpol]
    rw [hdiag', hdiag', hdiag', hdiag']
  let P : V → Prop := fun w =>
    inner ℂ (coreLift x) w + inner ℂ (B (x : H)) (J w) =
      inner ℂ (T x) (J w)
  apply DenseRange.induction_on (p := P) hcoreDense v
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro w
    change inner ℂ (coreLift x) (coreLift w) +
        inner ℂ (B (x : H)) (J (coreLift w)) =
      inner ℂ (T x) (J (coreLift w))
    rw [hsection]
    exact hcore w

end

end GaloisForLFunctions.HTGeometry
