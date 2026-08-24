import GaloisForLFunctions.HTGeometry.MaurerCartanJetQuotient

/-!
# Maurer--Cartan jet Hasse principle

For every split jet evaluation and every subgroup of constant positions, quotient position and
normalized Maurer--Cartan velocity form complete local data. Every position/velocity packet glues
to one unique global jet class, and failure of triviality is witnessed in one of the two channels.
This applies directly to finite algebraic jets of every commutative group scheme.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

namespace SplitJetEvaluation

variable {J : Type u} {P : Type v} [CommGroup J] [CommGroup P]
variable (S : SplitJetEvaluation J P)

/-- The quotient Hasse map is induced by position and normalized velocity. -/
@[simp] theorem quotientSubgroupEquivPositionVelocity_mk
    (H : Subgroup P) (j : J) :
    S.quotientSubgroupEquivPositionVelocity H (QuotientGroup.mk j) =
      S.positionVelocityHom H j := by
  rfl

/-- Position and normalized velocity jointly detect equality modulo constant `H`-jets. -/
theorem positionVelocity_congr_hasse_iff
    (H : Subgroup P) (j k : J) :
    QuotientGroup.mk j =
        (QuotientGroup.mk k : J ⧸ H.map S.const) ↔
      QuotientGroup.mk (S.eval j) =
          (QuotientGroup.mk (S.eval k) : P ⧸ H) ∧
        S.normalize j = S.normalize k := by
  constructor
  · intro h
    have he := congrArg (S.quotientSubgroupEquivPositionVelocity H) h
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨hpos, hvel⟩
    apply (S.quotientSubgroupEquivPositionVelocity H).injective
    apply Prod.ext
    · exact hpos
    · exact hvel

/-- A jet class is trivial exactly when both quotient position and normalized velocity are. -/
theorem positionVelocityClass_eq_one_hasse_iff
    (H : Subgroup P) (j : J) :
    QuotientGroup.mk j = (1 : J ⧸ H.map S.const) ↔
      QuotientGroup.mk (S.eval j) = (1 : P ⧸ H) ∧
        S.normalize j = 1 := by
  simpa using S.positionVelocity_congr_hasse_iff H j 1

/-- Every nontrivial jet class has a position witness or a velocity witness. -/
theorem positionVelocityClass_ne_one_iff_localWitness
    (H : Subgroup P) (j : J) :
    QuotientGroup.mk j ≠ (1 : J ⧸ H.map S.const) ↔
      QuotientGroup.mk (S.eval j) ≠ (1 : P ⧸ H) ∨
        S.normalize j ≠ 1 := by
  constructor
  · intro h
    by_cases hp : QuotientGroup.mk (S.eval j) = (1 : P ⧸ H)
    · right
      intro hv
      exact h (S.positionVelocityClass_eq_one_hasse_iff H j |>.2 ⟨hp, hv⟩)
    · exact Or.inl hp
  · rintro (hp | hv) hzero
    · exact hp (S.positionVelocityClass_eq_one_hasse_iff H j |>.1 hzero).1
    · exact hv (S.positionVelocityClass_eq_one_hasse_iff H j |>.1 hzero).2

/-- Every local position/velocity packet has one unique global jet class. -/
theorem positionVelocityPacket_existsUnique_globalClass
    (H : Subgroup P) (q : P ⧸ H) (b : S.eval.ker) :
    ∃! x : J ⧸ H.map S.const,
      S.quotientSubgroupEquivPositionVelocity H x = (q, b) := by
  refine ⟨(S.quotientSubgroupEquivPositionVelocity H).symm (q, b),
    (S.quotientSubgroupEquivPositionVelocity H).apply_symm_apply (q, b), ?_⟩
  intro y hy
  apply (S.quotientSubgroupEquivPositionVelocity H).injective
  rw [hy, (S.quotientSubgroupEquivPositionVelocity H).apply_symm_apply]

/-- Every local packet has a global representative, unique modulo constant `H`-translation. -/
theorem positionVelocityPacket_exists_global_unique_mod_constant
    (H : Subgroup P) (q : P ⧸ H) (b : S.eval.ker) :
    ∃ j : J, S.positionVelocityHom H j = (q, b) ∧
      ∀ k, S.positionVelocityHom H k = (q, b) ↔
        k / j ∈ H.map S.const := by
  obtain ⟨j, hj⟩ := S.positionVelocityHom_surjective H (q, b)
  refine ⟨j, hj, fun k => ?_⟩
  rw [← hj, ← S.positionVelocityHom_ker H,
    MonoidHom.mem_ker, map_div, div_eq_one]

end SplitJetEvaluation

end

end GaloisForLFunctions.HTGeometry
