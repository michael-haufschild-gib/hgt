import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticResidueDuality
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Multiplicity-exact compact-support jet classes

For a Xi zero of multiplicity `m`, every derivative evaluation of order `< m` annihilates the
principal Xi ideal.  It therefore descends to compact-support cohomology.  These local jet classes
are constructed from the source quotient itself; divisor multiplicity enters only as the theorem
which certifies how many derivatives descend.

The construction supplies the multiplicity-sensitive refinement missing from zeroth evaluation
and is the local Grothendieck-residue part of ordinary/compact-support Poincare duality.
-/

open Complex

namespace RHTower

noncomputable section

/-- The `k`th jet of an entire source at `alpha`, as a linear functional. -/
def deningerEntireJet (alpha : ℂ) (k : ℕ) :
    DeningerEntire →ₗ[ℂ] ℂ where
  toFun F := iteratedDeriv k (F : ℂ → ℂ) alpha
  map_add' F G := by
    change
      iteratedDeriv k
          (fun z => (F : ℂ → ℂ) z + (G : ℂ → ℂ) z) alpha =
        iteratedDeriv k (F : ℂ → ℂ) alpha +
          iteratedDeriv k (G : ℂ → ℂ) alpha
    exact iteratedDeriv_add
      (F.2.analyticAt alpha).contDiffAt
      (G.2.analyticAt alpha).contDiffAt
  map_smul' c F := by
    change
      iteratedDeriv k (fun z => c * (F : ℂ → ℂ) z) alpha =
        c * iteratedDeriv k (F : ℂ → ℂ) alpha
    simpa only [smul_eq_mul] using
      (iteratedDeriv_fun_const_smul_field
        (x := alpha) (n := k) c (F : ℂ → ℂ))

@[simp]
theorem deningerEntireJet_apply
    (alpha : ℂ) (k : ℕ) (F : DeningerEntire) :
    deningerEntireJet alpha k F =
      iteratedDeriv k (F : ℂ → ℂ) alpha :=
  rfl

/--
Every jet strictly below the Xi multiplicity annihilates the source differential image.
-/
theorem deningerEntireJet_eq_zero_of_mem_XiIdeal
    (rho : XiDivisorSupport) {k : ℕ}
    (hk : k < xiSupportMultiplicity rho)
    {F : DeningerEntire} (hF : F ∈ deningerEntireXiIdeal) :
    deningerEntireJet (xiSpectralPointSupport rho) k F = 0 := by
  rw [deningerEntireXiIdeal, Ideal.mem_span_singleton'] at hF
  obtain ⟨G, hG⟩ := hF
  have hfun :
      (F : ℂ → ℂ) =
        fun z =>
          (G : ℂ → ℂ) z * XiC z := by
    funext z
    have hz := congrArg (fun H : DeningerEntire => H z) hG
    simpa only [deningerEntire_mul_apply, deningerEntireXi_apply] using hz.symm
  rw [deningerEntireJet_apply, hfun,
    show (fun z => (G : ℂ → ℂ) z * XiC z) =
        (G : ℂ → ℂ) * XiC by rfl,
    iteratedDeriv_mul
      (G.2.analyticAt (xiSpectralPointSupport rho)).contDiffAt
      (XiC_analytic (xiSpectralPointSupport rho)
        (Set.mem_univ _)).contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  have hsub : k - i < xiSupportMultiplicity rho :=
    lt_of_le_of_lt (Nat.sub_le k i) hk
  simp only [
    iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hsub,
    mul_zero]

/-- Multiplicity-bounded local jet indices. -/
abbrev DeningerArithmeticJetIndex (rho : XiDivisorSupport) :=
  Fin (xiSupportMultiplicity rho)

/--
The `k`th local jet descends through the Xi quotient to compact-support middle cohomology.
-/
def deningerArithmeticJetCompact
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    DeningerArithmeticH1Compact where
  toFun :=
    Quotient.lift
      (fun F : DeningerEntire =>
        deningerEntireJet (xiSpectralPointSupport rho) k F)
      (by
        intro F G hFG
        have hmem : F - G ∈ deningerEntireXiIdeal :=
          deningerEntireXiIdeal.quotientRel_def.mp hFG
        have hzero :=
          deningerEntireJet_eq_zero_of_mem_XiIdeal rho k.isLt hmem
        have hsub :=
          (deningerEntireJet (xiSpectralPointSupport rho) k).map_sub F G
        rw [hzero] at hsub
        exact sub_eq_zero.mp hsub.symm)
  map_add' := by
    rintro ⟨F⟩ ⟨G⟩
    exact
      (deningerEntireJet (xiSpectralPointSupport rho) k).map_add F G
  map_smul' := by
    rintro c ⟨F⟩
    exact
      (deningerEntireJet (xiSpectralPointSupport rho) k).map_smul c F

@[simp]
theorem deningerArithmeticJetCompact_class
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho)
    (F : DeningerEntire) :
    deningerArithmeticJetCompact rho k
        (deningerEntireH1Class F) =
      iteratedDeriv k (F : ℂ → ℂ)
        (xiSpectralPointSupport rho) :=
  rfl

/-- Zeroth compact jet agrees with the quotient evaluation character. -/
theorem deningerArithmeticJetCompact_zero
    (rho : XiDivisorSupport) :
    deningerArithmeticJetCompact rho
        ⟨0, xiSupportMultiplicity_pos rho⟩ =
      deningerArithmeticEvaluationCompact rho := by
  apply LinearMap.ext
  intro x
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  change
    iteratedDeriv 0 (F : ℂ → ℂ)
        (xiSpectralPointSupport rho) =
      F (xiSpectralPointSupport rho)
  rfl

end

end RHTower
