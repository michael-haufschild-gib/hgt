import GaloisForLFunctions.RHTower.CCMRationalIntegralFiniteAdeleCyclicQuotient
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleNonarchimedean

/-!
# Density of diagonal integers in rational integral finite adeles

The exact cyclic quotient law is upgraded to the topological statement needed
for finite-adelic quadrature.  Every class modulo an open additive subgroup is
represented by a literal diagonal integer.  Consequently the diagonal copy of
`ℤ` is dense in the compact group of integral finite adeles.
-/

noncomputable section

open scoped RestrictedProduct algebraMap Classical

namespace GaloisForLFunctions
namespace RHTower

/-- The congruence map sends an integer class to its literal diagonal adele
class.  Naming this reduction keeps later quotient proofs small. -/
theorem ccmRationalZModToIntegralFiniteAdeleQuotient_intCast
    (N : ℕ) (m : ℤ) :
    ccmRationalZModToIntegralFiniteAdeleQuotient N (m : ZMod N) =
      QuotientAddGroup.mk'
        (nsmulAddMonoidHom
          (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range
        (ccmRationalIntegralFiniteAdeleDiagonal m) := by
  rw [ccmRationalZModToIntegralFiniteAdeleQuotient]
  exact ZMod.lift_coe N
    ⟨ccmRationalIntegralFiniteAdeleQuotientDiagonal N,
      ccmRationalIntegralFiniteAdeleQuotientDiagonal_natCast_eq_zero N⟩ m

/-- Cardinal of every open quotient of integral finite adeles is nonzero. -/
theorem ccmRationalIntegralFiniteAdele_openQuotient_card_ne_zero
    (V : OpenAddSubgroup ccmRationalIntegralFiniteAdelesAddSubgroup) :
    Nat.card
      (ccmRationalIntegralFiniteAdelesAddSubgroup ⧸ V.toAddSubgroup) ≠ 0 :=
  Nat.card_pos.ne'

/-- Multiplication by cardinal of an open quotient lands inside defining open
subgroup. -/
theorem ccmRationalIntegralFiniteAdele_openQuotient_nsmulRange_le
    (V : OpenAddSubgroup ccmRationalIntegralFiniteAdelesAddSubgroup) :
    (nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup)
      (Nat.card
        (ccmRationalIntegralFiniteAdelesAddSubgroup ⧸ V.toAddSubgroup))).range ≤
      V := by
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change QuotientAddGroup.mk' V.toAddSubgroup
    (Nat.card
      (ccmRationalIntegralFiniteAdelesAddSubgroup ⧸ V.toAddSubgroup) • z) = 0
  rw [map_nsmul]
  exact card_nsmul_eq_zero'

/-- Every integral finite adele is congruent to a literal diagonal integer
modulo any open additive subgroup. -/
theorem ccmRationalIntegralFiniteAdele_exists_diagonal_mod_openAddSubgroup
    (V : OpenAddSubgroup ccmRationalIntegralFiniteAdelesAddSubgroup)
    (x : ccmRationalIntegralFiniteAdelesAddSubgroup) :
    ∃ m : ℤ, ccmRationalIntegralFiniteAdeleDiagonal m - x ∈ V := by
  let Q := ccmRationalIntegralFiniteAdelesAddSubgroup ⧸ V.toAddSubgroup
  let N := Nat.card Q
  have hN : N ≠ 0 :=
    ccmRationalIntegralFiniteAdele_openQuotient_card_ne_zero V
  have hNV :
      (nsmulAddMonoidHom
        (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range ≤ V := by
    exact ccmRationalIntegralFiniteAdele_openQuotient_nsmulRange_le V
  obtain ⟨r, hr⟩ :=
    ccmRationalZModToIntegralFiniteAdeleQuotient_surjective N hN
    (QuotientAddGroup.mk'
      (nsmulAddMonoidHom
        (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range x)
  have hr' :
      QuotientAddGroup.mk'
          (nsmulAddMonoidHom
            (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range
          (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) =
        QuotientAddGroup.mk'
          (nsmulAddMonoidHom
            (α := ccmRationalIntegralFiniteAdelesAddSubgroup) N).range x := by
    calc
      _ = ccmRationalZModToIntegralFiniteAdeleQuotient N
          ((r.val : ℤ) : ZMod N) := by
        exact
          (ccmRationalZModToIntegralFiniteAdeleQuotient_intCast N
            (r.val : ℤ)).symm
      _ = ccmRationalZModToIntegralFiniteAdeleQuotient N r := by
        congr 1
        simp
      _ = _ := hr
  refine ⟨(r.val : ℤ), hNV ?_⟩
  exact (QuotientAddGroup.eq_iff_sub_mem).mp hr'

/-- **Diagonal density law.** Literal integers are dense in the compact group
of rational integral finite adeles. -/
theorem ccmRationalIntegralFiniteAdeleDiagonal_denseRange :
    DenseRange ccmRationalIntegralFiniteAdeleDiagonal := by
  letI : NonarchimedeanAddGroup CCMRationalFiniteAdele :=
    ccmRationalFiniteAdele_nonarchimedeanAddGroup
  letI : NonarchimedeanAddGroup
      ccmRationalIntegralFiniteAdelesAddSubgroup :=
    nonarchimedeanAddGroup_addSubgroup
      ccmRationalIntegralFiniteAdelesAddSubgroup
  exact denseRange_of_openAddSubgroup_cosets
    ccmRationalIntegralFiniteAdeleDiagonal
    ccmRationalIntegralFiniteAdele_exists_diagonal_mod_openAddSubgroup

end RHTower
end GaloisForLFunctions
