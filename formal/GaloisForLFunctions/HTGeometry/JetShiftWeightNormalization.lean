import GaloisForLFunctions.HTGeometry.JetWeightAction
import GaloisForLFunctions.HTGeometry.JetFixedFieldShift

/-!
# Normalizing a shift under the weighted action

The equation a normalizing shift solves is isobaric: the derivative factor has weight zero and the
shift term `σ_M` has weight `M`.  So if `t` is a shift at level `M`, then `w_λ(t)` and `λ^M·t` solve
the same equation, and their difference `H` satisfies the *homogeneous* equation `Φ(H) = R'·H`,
which says exactly that `H/y₁` is fixed.

`H` has order below `M`, so as soon as fixed elements of order below `M` are constant — which is the
situation of a minimal nonconstant fixed element — the difference is a constant multiple of `y₁`:

`w_λ(t) = λ^M·t + γ(λ)·y₁`.

This is the normalization the descent needs: it pins the weight of every coefficient of a slice of
`t` up to the single `y₁` term.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The scaled shift solves the scaled equation.** -/
theorem jetSubstitution_weightScale_shift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 1 ≤ M) {lam : C} (h : lam ≠ 0) (t : ↥(jetPrefixField C M))
    (ht : jetSubstitutionPrefix R hR M t
      = substitutionDerivPrefix R hM * t - substitutionShiftPrefix R hM) :
    jetSubstitution R hR (weightScale h (t : JetField C Unit))
      = substitutionDeriv R * weightScale h (t : JetField C Unit)
        - algebraMap C (JetField C Unit) (lam ^ M) * substitutionShift R M := by
  have htJ : jetSubstitution R hR (t : JetField C Unit)
      = substitutionDeriv R * (t : JetField C Unit) - substitutionShift R M := by
    have hc := congrArg (fun z : ↥(jetPrefixField C M) =>
      (algebraMap ↥(jetPrefixField C M) (JetField C Unit) z)) ht
    simp only [map_sub, map_mul] at hc
    rw [← jetSubstitution_algebraMap_prefix] at hc
    exact hc
  rw [← weightScale_jetSubstitution h R hR, htJ, map_sub, map_mul,
    weightScale_substitutionDeriv, weightScale_substitutionShift]

/-- **The difference of a shift and its scaled multiple solves the homogeneous equation.** -/
theorem jetSubstitution_weightScale_sub (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 1 ≤ M) {lam : C} (h : lam ≠ 0) (t : ↥(jetPrefixField C M))
    (ht : jetSubstitutionPrefix R hR M t
      = substitutionDerivPrefix R hM * t - substitutionShiftPrefix R hM) :
    jetSubstitution R hR (weightScale h (t : JetField C Unit)
        - algebraMap C (JetField C Unit) (lam ^ M) * (t : JetField C Unit))
      = substitutionDeriv R * (weightScale h (t : JetField C Unit)
        - algebraMap C (JetField C Unit) (lam ^ M) * (t : JetField C Unit)) := by
  have htJ : jetSubstitution R hR (t : JetField C Unit)
      = substitutionDeriv R * (t : JetField C Unit) - substitutionShift R M := by
    have hc := congrArg (fun z : ↥(jetPrefixField C M) =>
      (algebraMap ↥(jetPrefixField C M) (JetField C Unit) z)) ht
    simp only [map_sub, map_mul] at hc
    rw [← jetSubstitution_algebraMap_prefix] at hc
    exact hc
  have hscaled := jetSubstitution_weightScale_shift R hR hM h t ht
  rw [map_sub, map_mul, hscaled, htJ, AlgHom.commutes]
  ring

/-- **The normalization.**  When fixed elements of order below `M` are constant, the scaled shift
differs from its multiple by a constant multiple of the first jet coordinate. -/
theorem exists_const_weightScale_shift_sub (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 2 ≤ M)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {lam : C} (h : lam ≠ 0) (t : ↥(jetPrefixField C M))
    (ht : jetSubstitutionPrefix R hR M t
      = substitutionDerivPrefix R (le_trans one_le_two hM) * t
        - substitutionShiftPrefix R (le_trans one_le_two hM)) :
    ∃ γ : C, weightScale h (t : JetField C Unit)
        - algebraMap C (JetField C Unit) (lam ^ M) * (t : JetField C Unit)
      = algebraMap C (JetField C Unit) γ * JetField.jet ((), 1) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  set H : JetField C Unit := weightScale h (t : JetField C Unit)
    - algebraMap C (JetField C Unit) (lam ^ M) * (t : JetField C Unit) with hHdef
  have hHmem : H ∈ jetPrefixField C M := by
    rw [hHdef]
    exact sub_mem (weightScale_mem_jetPrefixField h M t.2)
      (mul_mem (IntermediateField.algebraMap_mem _ _) t.2)
  have hHhom : jetSubstitution R hR H = substitutionDeriv R * H :=
    jetSubstitution_weightScale_sub R hR (le_trans one_le_two hM) h t ht
  -- the quotient by the first jet coordinate is fixed
  set g : JetField C Unit := H / (JetField.jet ((), 1) : JetField C Unit) with hgdef
  have hgfix : jetSubstitution R hR g = g := by
    rw [hgdef, map_div₀, hHhom, jetSubstitution_jet_one]
    field_simp
  have hgord : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) g = 0 := by
    intro j hj
    have hjM : M ≤ j := by omega
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz g
        (JetField.jet ((), 1) : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    have hmul : g * (JetField.jet ((), 1) : JetField C Unit) = H := by
      rw [hgdef]
      exact div_mul_cancel₀ H hy1
    rw [hmul] at hleib
    have hjet : JetField.pd ((), j) (JetField.jet ((), 1) : JetField C Unit) = 0 :=
      JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
    have hHj : JetField.pd ((), j) H = 0 := (mem_jetPrefixField_iff M H).mp hHmem j hjM
    rw [hHj, hjet, mul_zero, zero_add] at hleib
    exact (mul_eq_zero.mp hleib.symm).resolve_left hy1
  obtain ⟨γ, hγ⟩ := hfix g hgord hgfix
  refine ⟨γ, ?_⟩
  have : H = g * (JetField.jet ((), 1) : JetField C Unit) := by
    rw [hgdef]
    exact (div_mul_cancel₀ H hy1).symm
  rw [this, hγ]

end

end GaloisForLFunctions.HTGeometry
