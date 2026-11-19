import GaloisForLFunctions.CurvesOverFiniteFields.MayerVietoris
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The Euler-characteristic step for two subspaces

For subspaces `M ≤ N` and `U` of `V` with `N/M` finite-dimensional, write
`χ(M) = dim (M ⊓ U) − dim V/(M ⊔ U)`. Then finiteness of both terms passes from `M` to `N` and
back (`euler_step`, `euler_step_down`), and `χ(N) = χ(M) + dim N/M`. The proof combines the
Mayer–Vietoris identity `finrank_quot_eq_add` with the additivity of dimensions along nested
subspaces (`finrank_eq_add_subQuot`) and along nested quotients (`finrank_quotient_eq_add`).
For a curve, `M, N` are the spaces of one chart for two divisors and `U` is the space of the
other chart.
-/

noncomputable section

namespace GaloisForLFunctions.CurvesOverFiniteFields

section Linear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Dimensions of nested finite-dimensional subspaces add along the quotient. -/
theorem finrank_eq_add_subQuot {A B : Submodule F V} (hAB : A ≤ B) [FiniteDimensional F B] :
    Module.finrank F B = Module.finrank F A + Module.finrank F (subQuot A B) := by
  have h := Submodule.finrank_quotient_add_finrank (A.comap B.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe hAB).finrank_eq] at h
  have h' : Module.finrank F (subQuot A B) + Module.finrank F A = Module.finrank F B := h
  omega

/-- The image of `T` in `V/S` is `T/S`. -/
def mapMkQEquiv (S T : Submodule F V) : subQuot S T ≃ₗ[F] T.map S.mkQ :=
  (Submodule.quotEquivOfEq _ _ (by ext x; simp [LinearMap.mem_ker])).trans
    (S.mkQ.comp T.subtype).quotKerEquivRange |>.trans
    (LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype]))

/-- Codimensions of nested subspaces add along the quotient. -/
theorem finrank_quotient_eq_add {S T : Submodule F V} (hST : S ≤ T)
    [FiniteDimensional F (V ⧸ S)] :
    Module.finrank F (V ⧸ S) = Module.finrank F (V ⧸ T) + Module.finrank F (subQuot S T) := by
  have h := Submodule.finrank_quotient_add_finrank (T.map S.mkQ)
  rw [(Submodule.quotientQuotientEquivQuotient S T hST).finrank_eq,
    ← (mapMkQEquiv S T).finrank_eq] at h
  omega

theorem finiteDimensional_of_le_subQuot {A B : Submodule F V} (hAB : A ≤ B)
    [FiniteDimensional F A] [FiniteDimensional F (subQuot A B)] : FiniteDimensional F B := by
  haveI : FiniteDimensional F (A.comap B.subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hAB).symm
  exact Module.Finite.of_submodule_quotient (A.comap B.subtype)

theorem finiteDimensional_quotient_of_subQuot {S T : Submodule F V} (hST : S ≤ T)
    [FiniteDimensional F (V ⧸ T)] [FiniteDimensional F (subQuot S T)] :
    FiniteDimensional F (V ⧸ S) := by
  haveI : FiniteDimensional F (T.map S.mkQ) := Module.Finite.equiv (mapMkQEquiv S T)
  haveI : FiniteDimensional F ((V ⧸ S) ⧸ T.map S.mkQ) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient S T hST).symm
  exact Module.Finite.of_submodule_quotient (T.map S.mkQ)

theorem finiteDimensional_quotient_of_le {S T : Submodule F V} (hST : S ≤ T)
    [FiniteDimensional F (V ⧸ S)] : FiniteDimensional F (V ⧸ T) :=
  Module.Finite.of_surjective (Submodule.factor hST) (Submodule.factor_surjective hST)

/-- **Euler characteristic step**: if `N/M` is finite-dimensional, then finiteness of
`M ⊓ U` and `V/(M ⊔ U)` passes to `N`, and `χ` grows by `dim N/M`. -/
theorem euler_step {M N U : Submodule F V} (hMN : M ≤ N) [FiniteDimensional F (subQuot M N)]
    [FiniteDimensional F (M ⊓ U : Submodule F V)] [FiniteDimensional F (V ⧸ (M ⊔ U))] :
    FiniteDimensional F (N ⊓ U : Submodule F V) ∧ FiniteDimensional F (V ⧸ (N ⊔ U)) ∧
      ((Module.finrank F (N ⊓ U : Submodule F V) : ℤ) - Module.finrank F (V ⧸ (N ⊔ U))) =
        ((Module.finrank F (M ⊓ U : Submodule F V) : ℤ) - Module.finrank F (V ⧸ (M ⊔ U))) +
          Module.finrank F (subQuot M N) := by
  haveI := finiteDimensional_subQuot_inf (M := M) (N := N) U
  haveI := finiteDimensional_subQuot_sup hMN U
  have hinf : M ⊓ U ≤ N ⊓ U := inf_le_inf_right U hMN
  have hsup : M ⊔ U ≤ N ⊔ U := sup_le_sup_right hMN U
  haveI hN : FiniteDimensional F (N ⊓ U : Submodule F V) := finiteDimensional_of_le_subQuot hinf
  haveI hQ : FiniteDimensional F (V ⧸ (N ⊔ U)) := finiteDimensional_quotient_of_le hsup
  refine ⟨hN, hQ, ?_⟩
  have h1 := finrank_eq_add_subQuot hinf
  have h2 := finrank_quotient_eq_add (V := V) hsup
  have h3 := finrank_quot_eq_add hMN U
  omega

/-- The reverse step: finiteness at `N` passes down to `M`. -/
theorem euler_step_down {M N U : Submodule F V} (hMN : M ≤ N) [FiniteDimensional F (subQuot M N)]
    [FiniteDimensional F (N ⊓ U : Submodule F V)] [FiniteDimensional F (V ⧸ (N ⊔ U))] :
    FiniteDimensional F (M ⊓ U : Submodule F V) ∧ FiniteDimensional F (V ⧸ (M ⊔ U)) := by
  haveI := finiteDimensional_subQuot_sup hMN U
  have hinf : M ⊓ U ≤ N ⊓ U := inf_le_inf_right U hMN
  have hsup : M ⊔ U ≤ N ⊔ U := sup_le_sup_right hMN U
  exact ⟨Submodule.finiteDimensional_of_le hinf, finiteDimensional_quotient_of_subQuot hsup⟩

end Linear

end GaloisForLFunctions.CurvesOverFiniteFields
