import GaloisForLFunctions.RHTower.CCMRationalIntegralFiniteAdeleDiagonalDensity

/-!
# Finite cyclic Haar averaging on integral finite adeles

The literal diagonal representatives of `Ẑ / NẐ` make every quotient-class
function satisfy an exact finite cyclic averaging identity.  Haar invariance
then turns vanishing integral into vanishing sum of diagonal samples.  This is
the finite-place bridge from the CCM endpoint `ε₁` to the dual zero mode of a
periodic Poisson trace.
-/

noncomputable section

open MeasureTheory
open scoped RestrictedProduct algebraMap Classical BigOperators

namespace GaloisForLFunctions
namespace RHTower

private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

/-- Evaluation of the diagonal congruence map on canonical `ZMod` values. -/
theorem ccmRationalZModToIntegralFiniteAdeleQuotient_val
    (N : ℕ) [NeZero N] (r : ZMod N) :
    ccmRationalZModToIntegralFiniteAdeleQuotient N r =
      QuotientAddGroup.mk'
        (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range
        (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) := by
  simpa using
    ccmRationalZModToIntegralFiniteAdeleQuotient_intCast N (r.val : ℤ)

/-- Invariance under `N`-multiples implies constancy on quotient classes. -/
theorem ccmRationalIntegralFiniteAdele_classInvariant_of_nsmulInvariant
    (N : ℕ) (ψ : IntegralFiniteAdeles → ℂ)
    (hperiod : ∀ x z : IntegralFiniteAdeles, ψ (x + N • z) = ψ x) :
    ∀ {x y : IntegralFiniteAdeles},
      QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range x =
        QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range y →
      ψ x = ψ y := by
  intro x y hxy
  obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_iff_sub_mem).mp hxy
  have hsub : x - y = N • z := hz.symm
  have hx : x = N • z + y := (sub_eq_iff_eq_add).mp hsub
  calc
    ψ x = ψ (y + N • z) := by rw [hx, add_comm]
    _ = ψ y := hperiod y z

/-- **Finite cyclic averaging law.** The sum over all literal diagonal
representatives is independent of base point for every quotient-class
function. -/
theorem ccmRationalIntegralFiniteAdele_cyclicAverage_eq
    (N : ℕ) [NeZero N] (ψ : IntegralFiniteAdeles → ℂ)
    (hclass : ∀ {x y : IntegralFiniteAdeles},
      QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range x =
        QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range y →
      ψ x = ψ y)
    (x : IntegralFiniteAdeles) :
    ∑ r : ZMod N,
        ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ) + x) =
      ∑ r : ZMod N,
        ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) := by
  let q := QuotientAddGroup.mk'
    (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range
  obtain ⟨s, hs⟩ :=
    ccmRationalZModToIntegralFiniteAdeleQuotient_surjective N
      (NeZero.ne N) (q x)
  apply Finset.sum_equiv (Equiv.addRight s)
  · simp
  · intro r hr
    apply hclass
    calc
      q (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ) + x) =
          q (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) + q x :=
        map_add q _ _
      _ = ccmRationalZModToIntegralFiniteAdeleQuotient N r +
          ccmRationalZModToIntegralFiniteAdeleQuotient N s := by
        rw [ccmRationalZModToIntegralFiniteAdeleQuotient_val, hs]
      _ = ccmRationalZModToIntegralFiniteAdeleQuotient N (r + s) := by
        rw [map_add]
      _ = q (ccmRationalIntegralFiniteAdeleDiagonal ((r + s).val : ℤ)) :=
        ccmRationalZModToIntegralFiniteAdeleQuotient_val N (r + s)

/-- **Exact finite cyclic Haar quadrature.** Sum over all literal diagonal
residue representatives equals quotient cardinality times normalized Haar
integral. -/
theorem ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral
    (N : ℕ) [NeZero N] (ψ : IntegralFiniteAdeles → ℂ)
    (hψ : Integrable ψ ccmRationalIntegralFiniteAdelesHaar)
    (hclass : ∀ {x y : IntegralFiniteAdeles},
      QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range x =
        QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range y →
      ψ x = ψ y) :
    ∑ r : ZMod N,
      ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) =
        N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := by
  calc
    ∑ r : ZMod N,
        ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) =
        ∫ _ : IntegralFiniteAdeles,
          (∑ r : ZMod N,
            ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)))
          ∂ccmRationalIntegralFiniteAdelesHaar := by
        rw [integral_const, Measure.real,
          ccmRationalIntegralFiniteAdelesHaar_univ]
        simp
    _ = ∫ x : IntegralFiniteAdeles,
          (∑ r : ZMod N,
            ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ) + x))
          ∂ccmRationalIntegralFiniteAdelesHaar := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          (ccmRationalIntegralFiniteAdele_cyclicAverage_eq N ψ hclass x).symm
    _ = ∑ r : ZMod N,
          ∫ x : IntegralFiniteAdeles,
            ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ) + x)
            ∂ccmRationalIntegralFiniteAdelesHaar := by
        apply integral_finsetSum
        intro r hr
        exact hψ.comp_add_left _
    _ = ∑ _r : ZMod N,
          ∫ x : IntegralFiniteAdeles,
            ψ x ∂ccmRationalIntegralFiniteAdelesHaar := by
        apply Finset.sum_congr rfl
        intro r hr
        exact integral_add_left_eq_self ψ _
    _ = N • (∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]

/-- Vanishing corollary of exact finite cyclic Haar quadrature. -/
theorem ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_zero_of_integral_eq_zero
    (N : ℕ) [NeZero N] (ψ : IntegralFiniteAdeles → ℂ)
    (hψ : Integrable ψ ccmRationalIntegralFiniteAdelesHaar)
    (hclass : ∀ {x y : IntegralFiniteAdeles},
      QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range x =
        QuotientAddGroup.mk'
          (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range y →
      ψ x = ψ y)
    (hzero : ∫ x, ψ x ∂ccmRationalIntegralFiniteAdelesHaar = 0) :
    ∑ r : ZMod N,
      ψ (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ)) = 0 := by
  rw [ccmRationalIntegralFiniteAdele_cyclicSampleSum_eq_nsmul_integral
    N ψ hψ hclass, hzero, nsmul_zero]

end RHTower
end GaloisForLFunctions
