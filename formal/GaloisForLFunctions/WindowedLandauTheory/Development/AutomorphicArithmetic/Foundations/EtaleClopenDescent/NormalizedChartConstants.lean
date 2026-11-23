import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FinitePullbackNormalization
import GaloisForLFunctions.HTGeometry.BaseFieldCollapse
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! An empty set of coordinate restrictions contributes only constants
to a joined normalized chart cover. -/

noncomputable section

open GaloisForLFunctions.HTGeometry GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} (x : Fin (d + 1) → F)

@[simp] theorem rA_empty : rA k x ∅ = ⊥ := by
  unfold rA
  simp

private theorem integralClosure_bot_restrict [IsAlgClosed k] :
    (integralClosure (⊥ : Subalgebra k F) E).restrictScalars k = ⊥ := by
  let A : Subalgebra k F := ⊥
  have hsurj : Function.Surjective (Algebra.ofId k A) := by
    intro a
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp a.2
    exact ⟨c, Subtype.ext hc⟩
  letI : IsScalarTower k A E := IsScalarTower.of_algebraMap_eq fun c =>
    IsScalarTower.algebraMap_apply k F E c
  letI : Algebra.IsIntegral k A := Algebra.IsIntegral.of_surjective (Algebra.ofId k A) hsurj
  apply le_antisymm ?_ bot_le
  intro y hy
  have hint : IsIntegral k y := isIntegral_trans (A := A) y hy
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isIntegral hint
  exact Algebra.mem_bot.mpr ⟨c, hc.symm⟩

@[simp] theorem rB_empty [IsAlgClosed k] : rB k E x ∅ = ⊥ := by
  exact (congrArg (fun A : Subalgebra k F => (integralClosure A E).restrictScalars k)
    (rA_empty x)).trans integralClosure_bot_restrict

@[simp] theorem pullbackChartAlgebra_rB_empty [IsAlgClosed k] (j : E →ₐ[k] L) :
    pullbackChartAlgebra j (rB k E x ∅) = ⊥ := by
  rw [rB_empty]
  exact (congrArg (fun A : Subalgebra k L => (integralClosure A L).restrictScalars k)
    (Algebra.map_bot j)).trans (integralClosure_bot_restrict (F := L) (E := L))

end GlobalTheory.PD
