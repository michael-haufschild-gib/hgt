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
      change LinearIndependent ℚ (exponentFamily (t ∘ classOf ∘ f))
      exact exponentFamily_linearIndependent_comp t htQ (classOf ∘ f) hclass
    have hsJ : LinearIndependent ℚ
        (exponentFamily (fun j => base j + shift j)) :=
      exponentFamily_linearIndependent_natShift base shift hbase
    simpa [base, shift] using
      continued_joint_hzeta_upperEnd_differentialIndependent_finite hsJ

/-- Differential independence forces injectivity of the integer-translation class labels; this
direction uses only the derivative ladder and has no genericity hypothesis on the class bases. -/
theorem continued_hurwitz_integerTranslation_class_injective_of_differentialIndependent
    {κ I J : Type*} [Fintype J] [DecidableEq J]
    (t : κ → ℂ) (classOf : I → κ) (offset : I → ℕ) (f : J → I)
    (hDI :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ)
        (fun j => continuedHzetaUpperEndMero
          (t (classOf (f j)) + offset (f j)))) :
    Function.Injective (classOf ∘ f) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  intro j l hclass
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

/-- **Exact `ℂ/ℤ` partition-matroid law for continued Hurwitz values.**

For nonintegral representatives in pairwise distinct integer-residue classes, a finite selection
of arbitrary nonnegative integer translates is differentially independent over `ℂ(a)` exactly when
it selects at most one member from each residue class. -/
theorem continued_hurwitz_integerTranslation_differentialMatroid_law_of_integerResidueSeparated
    {κ I J : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype J] [DecidableEq J]
    (t : κ → ℂ) (classOf : I → κ) (offset : I → ℕ) (f : J → I)
    (hnonintegral : ∀ k, ∀ m : ℤ, t k ≠ (m : ℂ))
    (hseparated : ∀ k l, k ≠ l → ∀ m : ℤ, t k - t l ≠ (m : ℂ)) :
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
  · exact continued_hurwitz_integerTranslation_class_injective_of_differentialIndependent
      t classOf offset f
  · intro hclass
    let sJ : J → ℂ := fun j => t (classOf (f j)) + offset (f j)
    have hnonJ : ∀ j, ∀ m : ℤ, sJ j ≠ (m : ℂ) := by
      intro j m hm
      apply hnonintegral (classOf (f j)) (m - (offset (f j) : ℤ))
      push_cast
      linear_combination hm
    have hsepJ : ∀ j l, j ≠ l → ∀ m : ℤ, sJ j - sJ l ≠ (m : ℂ) := by
      intro j l hjl m hm
      have hclassne : classOf (f j) ≠ classOf (f l) := by
        intro h
        exact hjl (hclass h)
      apply hseparated (classOf (f j)) (classOf (f l)) hclassne
        (m - (offset (f j) : ℤ) + (offset (f l) : ℤ))
      dsimp only [sJ] at hm
      push_cast
      linear_combination hm
    simpa only [sJ] using
      continued_joint_hzeta_upperEnd_differentialIndependent_finite_of_integerResidueSeparated
        hnonJ hsepJ

/-- Two distinct continued Hurwitz functions whose exponents differ by an integer are
differentially dependent, regardless of the sign of that integer. -/
theorem continued_hzeta_not_differentialIndependent_of_integerDifference
    {I : Type*} [Fintype I] [DecidableEq I] (s : I → ℂ)
    {i j : I} (hij : i ≠ j) (m : ℤ) (hm : s i - s j = (m : ℂ)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    ¬ DifferentialIndependent (RatFunc ℂ)
      (fun q => continuedHzetaUpperEndMero (s q)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let x : I → upperEndMeroField := fun q => continuedHzetaUpperEndMero (s q)
  by_cases hm0 : 0 ≤ m
  · let d := m.toNat
    have hdcast : (d : ℂ) = (m : ℂ) := by
      dsimp only [d]
      have hnat : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm0
      exact_mod_cast hnat
    have hshift : s j + d = s i := by
      rw [hdcast]
      linear_combination -hm
    have hjet := differentialJet_continuedHzetaUpperEndMero_eq (s j) d
    rw [hshift] at hjet
    let c : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval (s j)))
    have hcmap : algebraMap (RatFunc ℂ) upperEndMeroField c =
        upperEndPolyToMero
          (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval (s j))) := by
      exact upperEndRatfuncToMero_algebraMap_polynomial _
    have hrel : differentialJet d (x j) =
        algebraMap (RatFunc ℂ) upperEndMeroField c * x i := by
      simpa only [x, c, hcmap] using hjet
    exact not_differentialIndependent_of_jet_eq_base_mul (Ne.symm hij) d c hrel
  · have hmneg : m < 0 := lt_of_not_ge hm0
    let d := (-m).toNat
    have hdcast : (d : ℂ) = -(m : ℂ) := by
      dsimp only [d]
      have hnat : (((-m).toNat : ℕ) : ℤ) = -m :=
        Int.toNat_of_nonneg (Int.neg_nonneg.mpr hmneg.le)
      exact_mod_cast hnat
    have hshift : s i + d = s j := by
      rw [hdcast]
      linear_combination hm
    have hjet := differentialJet_continuedHzetaUpperEndMero_eq (s i) d
    rw [hshift] at hjet
    let c : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval (s i)))
    have hcmap : algebraMap (RatFunc ℂ) upperEndMeroField c =
        upperEndPolyToMero
          (Polynomial.C ((-1 : ℂ) ^ d * (ascPochhammer ℂ d).eval (s i))) := by
      exact upperEndRatfuncToMero_algebraMap_polynomial _
    have hrel : differentialJet d (x i) =
        algebraMap (RatFunc ℂ) upperEndMeroField c * x j := by
      simpa only [x, c, hcmap] using hjet
    exact not_differentialIndependent_of_jet_eq_base_mul hij d c hrel

/-- **Intrinsic `ℂ/ℤ` differential-matroid law.**  For every finite family of nonintegral
exponents, joint differential independence of the continued Hurwitz functions is equivalent to
injectivity of their monodromy values `exp(-2π i s)`, hence to pairwise incongruence modulo `ℤ`. -/
theorem continued_hurwitz_intrinsic_residue_differentialMatroid_law
    {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (hnonintegral : ∀ i, ∀ m : ℤ, s i ≠ (m : ℂ)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => continuedHzetaUpperEndMero (s i)) ↔
      Function.Injective (fun i => HurwitzOrbit.monoScalar (s i)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  constructor
  · intro hDI i j hq
    by_contra hij
    obtain ⟨m, hm⟩ :=
      (monoScalar_eq_monoScalar_iff_integerDifference (s i) (s j)).mp hq
    exact (continued_hzeta_not_differentialIndependent_of_integerDifference
      s hij m hm) hDI
  · intro hq
    have hsep : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ) := by
      intro i j hij m hm
      apply hij
      apply hq
      exact (monoScalar_eq_monoScalar_iff_integerDifference (s i) (s j)).mpr ⟨m, hm⟩
    exact
      continued_joint_hzeta_upperEnd_differentialIndependent_finite_of_integerResidueSeparated
        hnonintegral hsep

/-- **Classical intrinsic `ℂ/ℤ` differential-matroid law.**  In the convergence half-plane, the
exact continued-Hurwitz classification transfers to the ordinary convergent Hurwitz series. -/
theorem hurwitz_intrinsic_residue_differentialMatroid_law
    {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℂ) (hs : ∀ i, 1 < (s i).re)
    (hnonintegral : ∀ i, ∀ m : ℤ, s i ≠ (m : ℂ)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => hzetaUpperEndMero (s i) (hs i)) ↔
      Function.Injective (fun i => HurwitzOrbit.monoScalar (s i)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  have heq : (fun i => continuedHzetaUpperEndMero (s i)) =
      fun i => hzetaUpperEndMero (s i) (hs i) := by
    funext i
    exact continuedHzetaUpperEndMero_eq_hzetaUpperEndMero (s i) (hs i)
  rw [← heq]
  exact continued_hurwitz_intrinsic_residue_differentialMatroid_law s hnonintegral

/-- A nonzero real number strictly between `-1` and `1` is not an integer, viewed in `ℂ`. -/
theorem ofReal_abs_lt_one_ne_int {r : ℝ} (hneg : -1 < r) (hpos : r < 1)
    (hr0 : r ≠ 0) (m : ℤ) : (r : ℂ) ≠ (m : ℂ) := by
  intro h
  have hre : r = (m : ℝ) := by
    have := congrArg Complex.re h
    simpa using this
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hc : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    linarith
  · subst m
    simp at hre
    exact hr0 hre
  · have hc : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    linarith

/-- **Closed rational example.**  The continued Hurwitz functions with exponents `1/2` and `1/3`
are jointly differentially algebraically independent over `ℂ(a)`. -/
theorem continued_hurwitz_oneHalf_oneThird_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i : Fin 2 => continuedHzetaUpperEndMero
        (if i = 0 then (1 / 2 : ℂ) else (1 / 3 : ℂ))) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let s : Fin 2 → ℂ := fun i => if i = 0 then (1 / 2 : ℂ) else (1 / 3 : ℂ)
  have hnon : ∀ i, ∀ m : ℤ, s i ≠ (m : ℂ) := by
    intro i m
    fin_cases i
    · simpa [s] using
        (ofReal_abs_lt_one_ne_int (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) m)
    · simpa [s] using
        (ofReal_abs_lt_one_ne_int (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
          (by norm_num) m)
  have hsep : ∀ i j, i ≠ j → ∀ m : ℤ, s i - s j ≠ (m : ℂ) := by
    intro i j hij m
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · intro hm
      apply ofReal_abs_lt_one_ne_int (r := (1 / 6 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num) m
      dsimp only [s] at hm
      norm_num at hm ⊢
      exact hm
    · intro hm
      apply ofReal_abs_lt_one_ne_int (r := (-1 / 6 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num) m
      dsimp only [s] at hm
      norm_num at hm ⊢
      exact hm
    · exact (hij rfl).elim
  simpa only [s] using
    continued_joint_hzeta_upperEnd_differentialIndependent_finite_of_integerResidueSeparated
      hnon hsep

/-- **Closed classical example.**  The ordinary convergent Hurwitz functions with exponents `3/2`
and `4/3` are jointly differentially algebraically independent over `ℂ(a)`. -/
theorem hurwitz_threeHalves_fourThirds_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i : Fin 2 => hzetaUpperEndMero
        (if i = 0 then (3 / 2 : ℂ) else (4 / 3 : ℂ))
        (by split <;> norm_num)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let s : Fin 2 → ℂ := fun i => if i = 0 then (3 / 2 : ℂ) else (4 / 3 : ℂ)
  have hs : ∀ i, 1 < (s i).re := by
    intro i
    fin_cases i <;> norm_num [s]
  have hnon : ∀ i, ∀ m : ℤ, s i ≠ (m : ℂ) := by
    intro i m
    fin_cases i
    · intro hm
      have hre := congrArg Complex.re hm
      norm_num [s] at hre
      have hm1 : (1 : ℤ) < m := by
        exact_mod_cast (show (1 : ℝ) < (m : ℝ) by linarith)
      have hm2 : m < (2 : ℤ) := by
        exact_mod_cast (show (m : ℝ) < (2 : ℝ) by linarith)
      omega
    · intro hm
      have hre := congrArg Complex.re hm
      norm_num [s] at hre
      have hm1 : (1 : ℤ) < m := by
        exact_mod_cast (show (1 : ℝ) < (m : ℝ) by linarith)
      have hm2 : m < (2 : ℤ) := by
        exact_mod_cast (show (m : ℝ) < (2 : ℝ) by linarith)
      omega
  rw [hurwitz_intrinsic_residue_differentialMatroid_law s hs hnon]
  intro i j hq
  by_contra hij
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference (s i) (s j)).mp hq
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · apply ofReal_abs_lt_one_ne_int (r := (1 / 6 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) m
    norm_num [s] at hm ⊢
    exact hm
  · apply ofReal_abs_lt_one_ne_int (r := (-1 / 6 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) m
    norm_num [s] at hm ⊢
    exact hm
  · exact (hij rfl).elim

end

end HurwitzJointLadder
