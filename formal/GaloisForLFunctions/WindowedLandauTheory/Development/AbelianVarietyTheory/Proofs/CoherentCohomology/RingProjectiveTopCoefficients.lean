import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTopCechCoefficients
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.RingPolynomialTwistScalars
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex

/-! In top Čech degree for a projective twist, the fully negative Laurent
coefficients detect whether a cochain is a boundary. -/

noncomputable section

open CategoryTheory HTGeometry

namespace GlobalTheory.SchemeCohomology.RingPolynomialCech

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι] [LinearOrder ι]

private theorem laurentCoeffs_add {e : ℕ} (c c' : (polyTwCech K ι PEmpty e).Cochain) (I : Finset ι) :
    laurentCoeffs (c + c') I = laurentCoeffs c I + laurentCoeffs c' I := by
  change (laurentLoc K ι PEmpty I (twValHom I (c I + c' I))).coeff = _
  rw [map_add, map_add, AddMonoidAlgebra.coeff_add] <;> rfl

/-- Extract the finitely many top coefficients from the section on the full intersection. -/
def topLaurentCoefficients (e p : ℕ) :
    (polyTwCech K ι PEmpty e).degreeCochains p →+ (TopLaurentExponents ι e → K) where
  toFun c a := laurentCoeffs c.1 Finset.univ a.1
  map_zero' := by
    funext a
    change (laurentLoc K ι PEmpty Finset.univ 0).coeff a.1 = 0
    rw [map_zero, AddMonoidAlgebra.coeff_zero] <;> rfl
  map_add' c c' := by
    funext a
    change laurentCoeffs (c.1 + c'.1) Finset.univ a.1 =
      laurentCoeffs c.1 Finset.univ a.1 + laurentCoeffs c'.1 Finset.univ a.1
    rw [laurentCoeffs_add] <;> rfl

theorem topLaurentCoefficients_scale (e p : ℕ) (r : K) (c : (polyTwCech K ι PEmpty e).degreeCochains p) :
    topLaurentCoefficients e p
      ⟨(polynomialTwistScale e r).onCochain c.1, (polynomialTwistScale e r).onCochain_isDeg c.2⟩ =
      r • topLaurentCoefficients e p c := by
  funext a
  change laurentCoeffs ((polynomialTwistScale e r).onCochain c.1) Finset.univ a.1 =
    r * laurentCoeffs c.1 Finset.univ a.1
  rw [laurentCoeffs_scale, Finsupp.smul_apply, smul_eq_mul]

/-- In top degree, a Laurent cochain is a boundary precisely when all of its
fully negative coefficients vanish. -/
theorem exact_topLaurentCoefficients (e p : ℕ) (hp : Fintype.card ι = p + 2) :
    Function.Exact ((polyTwCech K ι PEmpty e).cochainComplex.d p (p + 1))
      (topLaurentCoefficients (K := K) (ι := ι) e (p + 1)) := by
  let D := polyTwCech K ι PEmpty e
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro c
  change D.degreeCochains (p + 1) at c
  constructor
  · intro hc
    have hdc : D.d c.1 = 0 := by
      funext I
      have h : I.card ≤ Fintype.card ι := Finset.card_le_univ I
      exact D.d_isDeg c.2 I (by omega)
    have hcoeff (a : LaurentExp ι PEmpty) (ha : negSupp a = Finset.univ) :
        laurentCoeffs c.1 Finset.univ a = 0 := by
      by_contra hz
      have hmem := Finsupp.mem_support_iff.mpr hz
      have hadm := laurentLoc_mem_admSubgroup
        (c.1 Finset.univ : twPart (projGrading K ι PEmpty) (projCoord K ι PEmpty) Finset.univ e).2 a hmem
      exact hz (congrFun hc ⟨a, hadm.2, ha⟩)
    obtain ⟨b, hb, hbc⟩ := polyTwCech_exists_primitive c.2 hdc hcoeff
    refine ⟨(⟨b, hb⟩ : D.degreeCochains p), ?_⟩
    rw [FinsetCechDatum.cochainComplex_d_apply]
    exact Subtype.ext hbc
  · rintro ⟨b, rfl⟩
    rw [FinsetCechDatum.cochainComplex_d_apply]
    funext a
    exact polyTwCech_boundary_full_negative_coeff b.1 a.1 a.2.2

end GlobalTheory.SchemeCohomology.RingPolynomialCech
