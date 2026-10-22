import GaloisForLFunctions.RHTower.Deninger.DeningerMilnorAmplitude
import GaloisForLFunctions.HTGeometry.MilnorKAlgebraicReduction
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality
import GaloisForLFunctions.HTGeometry.MilnorWittWittComparison
import GaloisForLFunctions.HTGeometry.MilnorKTameResidueFinite

/-!
# The real shape of Milnor `K`-theory in each degree

Realification kills torsion, so a graded piece all of whose elements are torsion realifies to zero.
Combined with the identification of the two bottom graded pieces this gives the two-term real
shape: degree zero is `ℝ`, degree one is `F^× ⊗ ℝ`, and every degree at least two vanishes as soon
as degree two is torsion.

* `deningerTorsionModule_tensorReal_eq_zero` : a torsion group realifies to zero.
* `deningerMilnorDegTensorReal_eq_zero` : **degree `2 + k` realifies to zero.**
* `deningerMilnorDegZeroRealEquiv`, `deningerMilnorDegOneRealEquiv` : the two bottom pieces.
-/

namespace RHTower

open scoped TensorProduct
open GaloisForLFunctions.HTGeometry

/-- **A torsion group realifies to zero.** -/
theorem deningerTorsionModule_tensorReal_eq_zero {A : Type*} [AddCommGroup A]
    (h : ∀ x : A, x ∈ torsionAddSubgroup A) (t : A ⊗[ℤ] ℝ) : t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul x r =>
      obtain ⟨n, hn, hnz⟩ := h x
      exact deningerTorsion_tmul_real_eq_zero hn hnz r
  | add x y hx hy => rw [hx, hy, add_zero]

variable (F : Type*) [Field F]

/-- **The real Milnor algebra vanishes in every degree at least two, as soon as degree two is
torsion.** -/
theorem deningerMilnorDegTensorReal_eq_zero
    (h2 : ∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2)) (k : ℕ)
    (t : MilnorKDeg F (2 + k) ⊗[ℤ] ℝ) : t = 0 :=
  deningerTorsionModule_tensorReal_eq_zero (milnorKDeg_mem_torsion_of_two F h2 k) t

/-- **The real Milnor algebra of an algebraic extension of the rationals vanishes in every degree
at least two**, given the torsion of degree two over every finite subextension. -/
theorem deningerMilnorRealVanishing_of_finiteSubextension {F : Type*} [Field F] [Algebra ℚ F]
    [Algebra.IsAlgebraic ℚ F]
    (hNF : ∀ K : IntermediateField ℚ F, FiniteDimensional ℚ K →
      ∀ x : MilnorKDeg K 2, x ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (k : ℕ) (t : MilnorKDeg F (2 + k) ⊗[ℤ] ℝ) : t = 0 :=
  deningerMilnorDegTensorReal_eq_zero F (milnorKDegTwo_torsion_of_finiteSubextension hNF) k t

/-- **Degree zero realifies to `ℝ`.** -/
noncomputable def deningerMilnorDegZeroRealEquiv : (MilnorKDeg F 0 ⊗[ℤ] ℝ) ≃ₗ[ℤ] ℝ :=
  (TensorProduct.congr (milnorDegZeroEquiv F).toIntLinearEquiv
    (LinearEquiv.refl ℤ ℝ)).trans (TensorProduct.lid ℤ ℝ)

/-- **Degree one realifies to `F^× ⊗ ℝ`.** -/
noncomputable def deningerMilnorDegOneRealEquiv :
    (MilnorKDeg F 1 ⊗[ℤ] ℝ) ≃ₗ[ℤ] (Additive Fˣ ⊗[ℤ] ℝ) :=
  TensorProduct.congr (milnorDegOneEquiv F).toIntLinearEquiv (LinearEquiv.refl ℤ ℝ)

section TameKernelForm

open IsDedekindDomain NumberField

/-- **The real Milnor algebra of an algebraic extension of the rationals vanishes in every degree at
least two, given only the torsion of the tame kernel of each finite subextension.**  This is the
card's `(1)` with its classical input reduced to Garland's theorem: everything between the tame
kernel and the conclusion — the tame symbols at the finite places, the finiteness of the residue
fields, the almost-everywhere vanishing, the reduction to number fields, and the passage from degree
two to all higher degrees — is proved. -/
theorem deningerMilnorRealVanishing_of_tameKernelTorsion {F : Type*} [Field F] [Algebra ℚ F]
    [Algebra.IsAlgebraic ℚ F]
    (hTK : ∀ (K : IntermediateField ℚ F) [FiniteDimensional ℚ K] [NumberField K],
      ∀ y ∈ tameKernel (fun v : HeightOneSpectrum (RingOfIntegers K) => tameDataAtPlace K v),
        y ∈ torsionAddSubgroup (MilnorKDeg K 2))
    (k : ℕ) (t : MilnorKDeg F (2 + k) ⊗[ℤ] ℝ) : t = 0 := by
  refine deningerMilnorRealVanishing_of_finiteSubextension (fun K hfd x => ?_) k t
  haveI hfd' : FiniteDimensional ℚ K := hfd
  haveI hnf : NumberField K :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
      to_finiteDimensional := by
        convert hfd using 2
        exact Subsingleton.elim _ _ }
  exact milnorKDegTwo_torsion_of_tameKernel_numberField K (@hTK K hfd' hnf) x

end TameKernelForm

end RHTower
