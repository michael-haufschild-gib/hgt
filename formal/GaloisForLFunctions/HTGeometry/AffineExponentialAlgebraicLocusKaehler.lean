import GaloisForLFunctions.HTGeometry.AffineExponentialAlgebraicLocusSubgroup
import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehler

/-!
# Kähler propagation on a principal open of an algebraic locus

A regular Kähler form that pulls back to zero at a complex mixed point vanishes generically on
that point's exact algebraic-number locus.  Concretely, there is one regular function nonzero at
the original point such that the form pulls back to zero at every locus point where this function
remains nonzero.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialAlgebraicLocusKaehler

open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialAlgebraicLocusPoint
open AffineExponentialAlgebraicLocusSubgroup
open AffineExponentialInvariantKaehler

noncomputable section

/-- If a regular Kähler form vanishes at a complex point, it vanishes at every point of the same
exact algebraic-number locus inside one principal open containing the original point. -/
theorem exists_principal_open_pointKaehlerMap_eq_zero
    {n : ℕ} (p : Point ℂ n)
    (w : Ω[CoordinateAlgebra (algebraicClosure ℚ ℂ) n⁄algebraicClosure ℚ ℂ])
    (hw : pointKaehlerMap (algebraicClosure ℚ ℂ) p w = 0) :
    ∃ g : CoordinateAlgebra (algebraicClosure ℚ ℂ) n,
      eval (k := algebraicClosure ℚ ℂ) p g ≠ 0 ∧
      ∀ r ∈ algebraicLocus p,
        eval (k := algebraicClosure ℚ ℂ) r g ≠ 0 →
          pointKaehlerMap (algebraicClosure ℚ ℂ) r w = 0 := by
  let J : Ideal (CoordinateAlgebra (algebraicClosure ℚ ℂ) n) :=
    algebraicLocusIdeal p
  letI : J.IsPrime := by
    simpa [J, algebraicLocusIdeal] using
      RingHom.ker_isPrime
        (eval (k := algebraicClosure ℚ ℂ) p).toRingHom
  letI coordinateCommRing : CommRing
      (CoordinateAlgebra (algebraicClosure ℚ ℂ) n) := inferInstance
  letI quotientCommRing : CommRing
      (CoordinateAlgebra (algebraicClosure ℚ ℂ) n ⧸ J) := inferInstance
  letI : IsDomain
      (CoordinateAlgebra (algebraicClosure ℚ ℂ) n ⧸ J) :=
    Ideal.Quotient.isDomain J
  let π := Ideal.Quotient.mkₐ (algebraicClosure ℚ ℂ) J
  let rhoP :
      (CoordinateAlgebra (algebraicClosure ℚ ℂ) n ⧸ J) →ₐ[algebraicClosure ℚ ℂ] ℂ :=
    Ideal.Quotient.liftₐ J (eval (k := algebraicClosure ℚ ℂ) p)
      (fun a ha => ha)
  have hrhoP : Function.Injective rhoP := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq]
    change eval (k := algebraicClosure ℚ ℂ) p (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  have hcompP : rhoP.comp π = eval (k := algebraicClosure ℚ ℂ) p := by
    rfl
  have hgeneric :
      algHomKaehlerMap rhoP (algHomKaehlerMap π w) = 0 := by
    rw [← algHomKaehlerMap_comp rhoP π w, hcompP]
    exact hw
  obtain ⟨s, hsne, hsw⟩ :=
    exists_nonzero_smul_eq_zero_of_algHomKaehlerMap_eq_zero
      rhoP hrhoP hgeneric
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨g, ?_, ?_⟩
  · intro hg
    apply hsne
    apply hrhoP
    change eval (k := algebraicClosure ℚ ℂ) p g = 0
    exact hg
  · intro r hr hrg
    let rhoR :
        (CoordinateAlgebra (algebraicClosure ℚ ℂ) n ⧸ J) →ₐ[algebraicClosure ℚ ℂ] ℂ :=
      Ideal.Quotient.liftₐ J (eval (k := algebraicClosure ℚ ℂ) r) (fun a ha => by
        apply hr a
        exact ha)
    have hcompR : rhoR.comp π = eval (k := algebraicClosure ℚ ℂ) r := by
      rfl
    have hzero : algHomKaehlerMap rhoR (algHomKaehlerMap π w) = 0 := by
      have hmap := congrArg (algHomKaehlerMap rhoR) hsw
      rw [map_zero, algHomKaehlerMap_smul] at hmap
      have hrhoRg : rhoR (Ideal.Quotient.mk J g) =
          eval (k := algebraicClosure ℚ ℂ) r g := rfl
      rw [hrhoRg] at hmap
      exact (smul_eq_zero.mp hmap).resolve_left hrg
    change algHomKaehlerMap (eval (k := algebraicClosure ℚ ℂ) r) w = 0
    rw [← hcompR, algHomKaehlerMap_comp]
    exact hzero

end

end AffineExponentialAlgebraicLocusKaehler
end GaloisForLFunctions.HTGeometry
