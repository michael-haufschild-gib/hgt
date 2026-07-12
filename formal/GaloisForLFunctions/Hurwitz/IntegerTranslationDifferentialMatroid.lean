import GaloisForLFunctions.Hurwitz.ContinuedJointUpperEndDifferentialIndependence

/-!
# The Hurwitz integer-translation differential-matroid law

Under augmented rational independence of one base exponent from every integer-translation class,
the independent sets of the continued Hurwitz family are exactly the selections containing at
most one member from each class.
-/

open Complex Polynomial

namespace HurwitzJointLadder

open HurwitzLadder HurwitzJointOrbit HurwitzZetaContinuation GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped Differential

noncomputable section

/-- A family cannot be differentially independent when one coordinate jet is a base-scalar
multiple of a different coordinate. -/
theorem not_differentialIndependent_of_jet_eq_base_mul
    {K L ι : Type*} [CommRing K] [Nontrivial K] [CommRing L]
    [Algebra K L] [Differential L]
    {x : ι → L} {i j : ι} (hij : i ≠ j) (d : ℕ) (c : K)
    (hjet : differentialJet d (x i) = algebraMap K L c * x j) :
    ¬ DifferentialIndependent K x := by
  classical
  intro hx
  unfold DifferentialIndependent at hx
  rw [algebraicIndependent_iff] at hx
  let P : MvPolynomial (ι × ℕ) K :=
    MvPolynomial.X (i, d) - MvPolynomial.C c * MvPolynomial.X (j, 0)
  have hPRel : MvPolynomial.aeval
      (fun q : ι × ℕ => differentialJet q.2 (x q.1)) P = 0 := by
    simp [P, hjet]
  have hPzero : P = 0 := hx P hPRel
  let v : ι × ℕ → K := fun q => if q = (i, d) then 1 else 0
  have hidx : (j, 0) ≠ (i, d) := by
    intro h
    exact hij (congrArg Prod.fst h).symm
  have hEval : MvPolynomial.eval v P = 1 := by
    simp [P, v, hidx]
  rw [hPzero, map_zero] at hEval
  exact one_ne_zero hEval.symm

/-- **Hurwitz integer-translation differential-matroid law.**

`t : κ → ℂ` supplies one base exponent for each class, `classOf : I → κ` assigns indices to
classes, and `offset : I → ℕ` records the nonnegative integer shift from the class base.  For every
finite selection `f : J → I`, the corresponding continued Hurwitz elements are differentially
independent over `ℂ(a)` exactly when the selected class labels are injective. -/
theorem continued_hurwitz_integerTranslation_differentialMatroid_law
    {κ I J : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype J] [DecidableEq J]
    (t : κ → ℂ) (classOf : I → κ) (offset : I → ℕ) (f : J → I)
    (htQ : LinearIndependent ℚ (exponentFamily t)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun j => continuedHzetaUpperEndMero
        (t (classOf (f j)) + offset (f j))) ↔
      Function.Injective (classOf ∘ f) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  constructor
  · intro hDI j l hclass
    change classOf (f j) = classOf (f l) at hclass
    by_contra hjl
    let x : J → upperEndMeroField := fun q => continuedHzetaUpperEndMero
      (t (classOf (f q)) + offset (f q))
    rcases le_total (offset (f j)) (offset (f l)) with hjle | hljle
    · let d := offset (f l) - offset (f j)
      let sj : ℂ := t (classOf (f j)) + offset (f j)
      have hsjl : sj + d = t (classOf (f l)) + offset (f l) := by
        dsimp only [sj, d]
        rw [hclass]
        have hoff : offset (f l) = offset (f j) + (offset (f l) - offset (f j)) := by
          omega
        have hcast : ((offset (f l) : ℕ) : ℂ) =
            (offset (f j) : ℂ) + ((offset (f l) - offset (f j) : ℕ) : ℂ) := by
          exact_mod_cast hoff
        calc
          t (classOf (f l)) + (offset (f j) : ℂ) +
                ((offset (f l) - offset (f j) : ℕ) : ℂ) =
              t (classOf (f l)) + ((offset (f j) : ℂ) +
                ((offset (f l) - offset (f j) : ℕ) : ℂ)) := by ring
          _ = t (classOf (f l)) + (offset (f l) : ℂ) := by rw [← hcast]
      have hjet := differentialJet_continuedHzetaUpperEndMero_eq sj d
      rw [hsjl] at hjet
      let c : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval sj))
      have hcmap : algebraMap (RatFunc ℂ) upperEndMeroField c =
          upperEndPolyToMero
            (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval sj)) := by
        exact upperEndRatfuncToMero_algebraMap_polynomial _
      have hrel : differentialJet d (x j) =
          algebraMap (RatFunc ℂ) upperEndMeroField c * x l := by
        simpa only [x, sj, c, hcmap] using hjet
      exact (not_differentialIndependent_of_jet_eq_base_mul hjl d c hrel) hDI
    · let d := offset (f j) - offset (f l)
      let sl : ℂ := t (classOf (f l)) + offset (f l)
      have hslj : sl + d = t (classOf (f j)) + offset (f j) := by
        dsimp only [sl, d]
        rw [hclass]
        have hoff : offset (f j) = offset (f l) + (offset (f j) - offset (f l)) := by
          omega
        have hcast : ((offset (f j) : ℕ) : ℂ) =
            (offset (f l) : ℂ) + ((offset (f j) - offset (f l) : ℕ) : ℂ) := by
          exact_mod_cast hoff
        calc
          t (classOf (f l)) + (offset (f l) : ℂ) +
                ((offset (f j) - offset (f l) : ℕ) : ℂ) =
              t (classOf (f l)) + ((offset (f l) : ℂ) +
                ((offset (f j) - offset (f l) : ℕ) : ℂ)) := by ring
          _ = t (classOf (f l)) + (offset (f j) : ℂ) := by rw [← hcast]
      have hjet := differentialJet_continuedHzetaUpperEndMero_eq sl d
      rw [hslj] at hjet
      let c : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval sl))
      have hcmap : algebraMap (RatFunc ℂ) upperEndMeroField c =
          upperEndPolyToMero
            (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval sl)) := by
        exact upperEndRatfuncToMero_algebraMap_polynomial _
      have hrel : differentialJet d (x l) =
          algebraMap (RatFunc ℂ) upperEndMeroField c * x j := by
        simpa only [x, sl, c, hcmap] using hjet
      exact (not_differentialIndependent_of_jet_eq_base_mul
        (Ne.symm hjl) d c hrel) hDI
  · intro hclass
    let base : J → ℂ := fun j => t (classOf (f j))
    let shift : J → ℕ := fun j => offset (f j)
    have hbase : LinearIndependent ℚ (exponentFamily base) := by
      simpa [base, Function.comp_apply] using
        exponentFamily_linearIndependent_comp t htQ (classOf ∘ f) hclass
    have hsJ : LinearIndependent ℚ
        (exponentFamily (fun j => base j + shift j)) :=
      exponentFamily_linearIndependent_natShift base shift hbase
    simpa [base, shift] using
      continued_joint_hzeta_upperEnd_differentialIndependent_finite hsJ

end

end HurwitzJointLadder
