import GaloisForLFunctions.HTGeometry.FiniteShadowCapacitySpectrum
import GaloisForLFunctions.HTGeometry.JetFieldConstantKernel
import GaloisForLFunctions.HTGeometry.JetHorizonAllDepthGauge

/-!
# The free differential rational field has no primitive of one

Differentiation strictly raises the jet order of a nonconstant element of the free differential
rational field, so a derivative is never a nonzero constant.  In particular the free field contains
no antiderivative of one: it carries no time coordinate.

This is exactly the hypothesis under which a derivative horizon of any depth has only constant
gauge freedom, so the depth-independent rigidity statement applies verbatim to points of the free
differential rational field — the canonical differentially generic setting.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open GaloisForLFunctions JetField

noncomputable section

variable {C ι : Type*} [Field C] [CharZero C] [Fintype ι]

omit [CharZero C] [Fintype ι] in
/-- A constant of the free differential rational field has vanishing derivative. -/
theorem deriv_eq_zero_of_mem_bot {u : JetField C ι}
    (hu : u ∈ (⊥ : IntermediateField C (JetField C ι))) : u′ = 0 := by
  rw [IntermediateField.mem_bot] at hu
  obtain ⟨c, rfl⟩ := hu
  exact JetField.deriv_algebraMap c

/-- **No primitive of one.**  No element of the free differential rational field has derivative
one. -/
theorem jetField_deriv_ne_one (u : JetField C ι) : u′ ≠ 1 := by
  intro hu
  by_cases hbot : u ∈ (⊥ : IntermediateField C (JetField C ι))
  · rw [deriv_eq_zero_of_mem_bot hbot] at hu
    exact zero_ne_one hu
  · refine deriv_notMem_bot_of_notMem_bot hbot ?_
    rw [hu]
    exact IntermediateField.one_mem _

/-! ### Depth-independent horizon rigidity on the free differential rational field -/

variable {κ : Type*} [Finite κ]

/-- **Depth-independent infinitesimal rigidity on the free field.**  A derivation of the free
differential rational field commuting with the derivation and killing the `n`-th derivatives of the
coordinates of a translation-rigid point kills the coordinates. -/
theorem jetField_derivation_apply_eq_zero_of_translationRigid
    (z : κ → JetField C ι) (hA : ∀ a : κ → C, IsTranslationSymmetry z a → a = 0)
    (D : Derivation C (JetField C ι) (JetField C ι)) (hcomm : ∀ x, D (x′) = (D x)′)
    {n : ℕ} (hn : 1 ≤ n) (hDz : ∀ i, D (differentialJet n (z i)) = 0) (i : κ) :
    D (z i) = 0 :=
  derivation_apply_eq_zero_of_translationRigid_depth jetField_deriv_ne_one
    (fun x hx => by
      obtain ⟨c, hc⟩ := jetField_mem_range_algebraMap_of_deriv_eq_zero hx
      exact ⟨c, hc⟩)
    z hA D hcomm hn hDz i

/-- **Depth-independent finite rigidity on the free field.**  A differential endomorphism fixing the
`n`-th derivatives of the coordinates of a translation-rigid point fixes the coordinates. -/
theorem jetField_apply_eq_self_of_translationRigid
    (z : κ → JetField C ι) (hA : ∀ a : κ → C, IsTranslationSymmetry z a → a = 0)
    (σ : JetField C ι →ₐ[C] JetField C ι) (hcomm : ∀ x, σ (x′) = (σ x)′)
    {n : ℕ} (hn : 1 ≤ n)
    (hfix : ∀ i, σ (differentialJet n (z i)) = differentialJet n (z i)) (i : κ) :
    σ (z i) = z i :=
  apply_eq_self_of_translationRigid_depth jetField_deriv_ne_one
    (fun x hx => by
      obtain ⟨c, hc⟩ := jetField_mem_range_algebraMap_of_deriv_eq_zero hx
      exact ⟨c, hc⟩)
    z hA σ hcomm hn hfix i

end

end GaloisForLFunctions.HTGeometry
