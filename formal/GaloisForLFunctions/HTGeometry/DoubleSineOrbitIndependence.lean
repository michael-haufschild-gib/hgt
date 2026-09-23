import GaloisForLFunctions.HTGeometry.DoubleSineOrbitIncrements
import GaloisForLFunctions.HTGeometry.DoubleSineHypertranscendenceAssembly

/-!
# The external orbit of a double-sine defect is differentially independent

The arbitrary-family differential criterion, run over a family of translates of the source rather
than over the source alone.

Every translate has the same two structural defects, translated; on the direction whose defect is
the cotangent of the second period that translation is a dilation of the outer cylinder
coordinate.  A nonzero constant character of the family is therefore a nonzero constant character
of a family of dilated cotangent models, and when the shifts lie in distinct classes modulo the
period lattice the separated obstruction forbids it from being a difference.

Hence translates in distinct classes are differentially independent over the two-cylinder field.
-/

open Filter Set Topology Complex Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance doiDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance doiComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance doiMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Dilation commutes with the iterated cylinder derivation. -/
theorem cylDeriv_iterate_ratFuncScale {K : Type*} [Field K] (lam : K) {s : K} (hs : s ≠ 0)
    (n : ℕ) (y : RatFunc K) :
    (cylDeriv lam)^[n] (ratFuncScale s hs y)
      = ratFuncScale s hs ((cylDeriv lam)^[n] y) := by
  rw [cylDeriv_iterate_eq, cylDeriv_iterate_eq, ratFuncEulerOp_iterate_ratFuncScale, map_mul,
    ratFuncScale_algebraMap_base]

variable {l : Fin 2 → ℂ}

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The external orbit of a double-sine defect is differentially independent.**  Translates of a
source with exact cotangent defects, by shifts in distinct classes modulo the period lattice, are
differentially independent over the two-cylinder function field. -/
theorem differentialIndependent_orbit_of_exact_defects (hl : LinearIndependent ℚ l)
    (ω : Fin 2 → ℂ) (hω0 : ω 0 ≠ 0) (hω1 : ω 1 ≠ 0)
    (hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0)
    (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hper0 : Complex.exp (l 0 * ω 0) = 1)
    (hper1 : Complex.exp (l 1 * ω 1) = 1)
    (htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1)
    (hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z)
    (M : meroField (Set.univ : Set ℂ)) (cst : ℂ)
    (hd0 : addTranslationMeroEquiv (ω 0) M - M = -periodCotMero (ω 1))
    (hd1 : addTranslationMeroEquiv (ω 1) M - M
      = -periodCotMero (ω 0) + ratMero (RatFunc.C cst))
    {κ : Type*} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ, sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1) :
    letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed hl).toAlgebra
    DifferentialIndependent (RatFunc (RatFunc ℂ))
      (fun j : κ => addTranslationMeroEquiv (sh j) M) := by
  classical
  letI : Differential (RatFunc ℂ) := cylinderDifferential (l 0)
  letI : Differential (RatFunc (RatFunc ℂ)) :=
    twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ) (l 1))
  letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
    (twoCylinderEmbed hl).toAlgebra
  have halg : ∀ y : RatFunc (RatFunc ℂ),
      algebraMap (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) y
        = twoCylinderEmbed hl y := fun _ => rfl
  letI : IsScalarTower ℂ (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := RatFunc (RatFunc ℂ))
      (A := meroField (Set.univ : Set ℂ)) fun c => ?_
    rw [halg]
    have hc : algebraMap ℂ (RatFunc (RatFunc ℂ)) c
        = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) c) :=
      IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c
    rw [hc, twoCylinderEmbed_coeff]
    exact ((cylinderEmbed hl 0).commutes c).symm
  letI : DifferentialAlgebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) := by
    refine ⟨fun y => ?_⟩
    rw [halg, halg]
    exact meroFieldDeriv_twoCylinderEmbed hl y
  -- the base automorphisms
  set q0 : ℂ := Complex.exp (l 1 * ω 0) with hq0def
  have hq0 : q0 ≠ 0 := Complex.exp_ne_zero _
  have hq0R : algebraMap ℂ (RatFunc ℂ) q0 ≠ 0 := by simpa using hq0
  set q1 : ℂ := Complex.exp (l 0 * ω 1) with hq1def
  have hq1 : q1 ≠ 0 := Complex.exp_ne_zero _
  set tau : Fin 2 → RatFunc (RatFunc ℂ) ≃+* RatFunc (RatFunc ℂ) :=
    ![ratFuncScaleEquiv_twoCylinderTranslationAction (algebraMap ℂ (RatFunc ℂ) q0) hq0R, cylinderCoeffScaleEquiv hq1]
    with htaudef
  set sigma : Fin 2 → meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
    fun i => addTranslationMeroEquiv (ω i) with hsigmadef
  -- the base increments of the untranslated source
  set c₀ : ℂ := -((Real.pi : ℂ) / ω 1 * Complex.I) with hc₀def
  set bb : Fin 2 → RatFunc (RatFunc ℂ) :=
    ![coeffExtend (K := RatFunc ℂ) (cotModel c₀),
      -algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
          (cotModel ((Real.pi : ℂ) / ω 0 * Complex.I))
        + algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
          (algebraMap ℂ (RatFunc ℂ) cst)] with hbbdef
  have hbb0 : twoCylinderEmbed hl (bb 0) = -periodCotMero (ω 1) := by
    have hcot : cotModel c₀ = -cotModel ((Real.pi : ℂ) / ω 1 * Complex.I) := by
      rw [hc₀def, show -((Real.pi : ℂ) / ω 1 * Complex.I)
          = (-1 : ℂ) * ((Real.pi : ℂ) / ω 1 * Complex.I) by ring, cotModel_mul_left]
      simp
    show twoCylinderEmbed hl (coeffExtend (K := RatFunc ℂ) (cotModel c₀)) = _
    rw [hcot, (coeffExtend (C := ℂ) (K := RatFunc ℂ)).map_neg, (twoCylinderEmbed hl).map_neg,
      ← periodCotMero_eq_twoCylinderEmbed_coeffExtend hl hω1 hl1]
  have hbb1 : twoCylinderEmbed hl (bb 1)
      = -periodCotMero (ω 0) + algebraMap ℂ (meroField (Set.univ : Set ℂ)) cst := by
    show twoCylinderEmbed hl (-algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
          (cotModel ((Real.pi : ℂ) / ω 0 * Complex.I))
        + algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
          (algebraMap ℂ (RatFunc ℂ) cst)) = _
    rw [(twoCylinderEmbed hl).map_add, (twoCylinderEmbed hl).map_neg,
      ← periodCotMero_eq_twoCylinderEmbed_coeff hl hω0 hl0, twoCylinderEmbed_coeff]
    congr 1
    exact (cylinderEmbed hl 0).commutes cst
  have hshiftBase : ∀ i : Fin 2, sigma i M = M + twoCylinderEmbed hl (bb i) := by
    intro i
    fin_cases i
    · show addTranslationMeroEquiv (ω 0) M = M + twoCylinderEmbed hl (bb 0)
      rw [hbb0]
      linear_combination hd0
    · show addTranslationMeroEquiv (ω 1) M = M + twoCylinderEmbed hl (bb 1)
      rw [hbb1]
      rw [ratMero_C] at hd1
      linear_combination hd1
  -- the translated family
  set b : Fin 2 → κ → RatFunc (RatFunc ℂ) := fun i j =>
    twoCylTranslate (q0 := Complex.exp (l 0 * sh j)) (q1 := Complex.exp (l 1 * sh j))
      (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) (bb i) with hbdef
  have hshift : ∀ (i : Fin 2) (j : κ),
      sigma i (addTranslationMeroEquiv (sh j) M)
        = addTranslationMeroEquiv (sh j) M
          + algebraMap (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) (b i j) := by
    intro i j
    have hcomm : sigma i (addTranslationMeroEquiv (sh j) M)
        = addTranslationMeroEquiv (sh j) (sigma i M) := by
      rw [hsigmadef]
      exact addTranslationMeroEquiv_comm (ω i) (sh j) M
    rw [hcomm, hshiftBase i, (addTranslationMeroEquiv (sh j)).map_add, halg, hbdef]
    congr 1
    exact addTranslationMeroEquiv_twoCylinderEmbed_general hl (sh j) (bb i)
  rw [automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
    (I := Fin 2) (κ := κ) (C := ℂ) (K := RatFunc (RatFunc ℂ))
    (L := meroField (Set.univ : Set ℂ)) tau sigma ?_ ?_ ?_ ?_
    (fun j : κ => addTranslationMeroEquiv (sh j) M) b hshift]
  · -- the character condition
    intro γ hγ k
    refine ⟨0, ?_⟩
    set lam' : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (l 1) with hlam'def
    set c₀' : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) c₀ with hc₀'def
    set σ : κ → RatFunc ℂ :=
      fun j => algebraMap ℂ (RatFunc ℂ) (Complex.exp (l 1 * sh j)) with hσdef
    have hσne : ∀ j, σ j ≠ 0 := by
      intro j
      rw [hσdef]
      simp [Complex.exp_ne_zero]
    have hCzero : ∀ c : ℂ, (algebraMap ℂ (RatFunc ℂ) c)′ = 0 := by
      intro c
      rw [cylinderDifferential_deriv (l 0), cylDeriv_algebraMap]
    have hb0coeff : ∀ j : κ, b 0 j
        = coeffExtend (K := RatFunc ℂ)
          (ratFuncScale (Complex.exp (l 1 * sh j)) (Complex.exp_ne_zero _) (cotModel c₀)) := by
      intro j
      rw [hbdef]
      show twoCylTranslate _ _ (coeffExtend (K := RatFunc ℂ) (cotModel c₀)) = _
      exact twoCylTranslate_coeffExtend _ _ (cotModel c₀)
    have hb0 : ∀ j : κ, b 0 j = ratFuncScale (σ j) (hσne j) (cotModel c₀') := by
      intro j
      rw [hb0coeff j, ← ratFuncScale_coeffExtend (Complex.exp_ne_zero (l 1 * sh j)),
        coeffExtend_cotModel]
    have hjets : ∀ (j : κ) (n : ℕ), differentialJet n (b 0 j)
        = ratFuncScale (σ j) (hσne j) ((cylDeriv lam')^[n] (cotModel c₀')) := by
      intro j n
      rw [hb0coeff j, differentialJet_twoCylinder (C := ℂ) (K := RatFunc ℂ) hCzero (l 1) n,
        ← hlam'def, ← ratFuncScale_coeffExtend (Complex.exp_ne_zero (l 1 * sh j)),
        coeffExtend_cotModel, ← hc₀'def, cylDeriv_iterate_ratFuncScale]
    have hsepR : ∀ i j : κ, i ≠ j → ∀ n : ℤ, (σ i)⁻¹ * algebraMap ℂ (RatFunc ℂ) q0 ^ n
        ≠ (σ j)⁻¹ := by
      intro i j hij n hcon
      refine separated_of_notMem_periodLattice (l := l) (ω := ω) hω1 hl1
        (hsep i j hij) n ?_
      refine (algebraMap ℂ (RatFunc ℂ)).injective ?_
      rw [map_mul, map_inv₀, map_inv₀, map_zpow₀]
      exact hcon
    have hγ' : Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ))
        (map_zero (algebraMap ℂ (RatFunc ℂ))) γ ≠ 0 := by
      intro hzero
      refine hγ ?_
      refine Finsupp.ext fun p => ?_
      have := congrArg (fun f : (κ × ℕ) →₀ RatFunc ℂ => f p) hzero
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      exact (algebraMap ℂ (RatFunc ℂ)).injective (by simpa using this)
    have htarget := not_dilationTelescoped_constantCharacter_separated
      (K := RatFunc ℂ) (algebraMap ℂ (RatFunc ℂ) q0) hq0R
      (fun n hn hcon => htor n hn (by
        refine (algebraMap ℂ (RatFunc ℂ)).injective ?_
        rw [map_zpow₀, map_one]
        exact hcon))
      (lam := lam') (c₀ := c₀')
      (by
        rw [hlam'def]
        have hl1ne : l 1 ≠ 0 := by
          rw [hl1]
          refine div_ne_zero ?_ hω1
          have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
        simpa using hl1ne)
      (by
        rw [hc₀'def, hc₀def]
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have : -((Real.pi : ℂ) / ω 1 * Complex.I) ≠ 0 := by
          rw [neg_ne_zero]
          exact mul_ne_zero (div_ne_zero hpi hω1) Complex.I_ne_zero
        simpa using this)
      σ hσne hsepR
      (Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ)) (map_zero (algebraMap ℂ (RatFunc ℂ))) γ)
      hγ' k
    have hchar : Finsupp.linearCombination (RatFunc (RatFunc ℂ))
          (fun p => differentialJet p.2 (b 0 p.1))
          (Finsupp.mapRange (algebraMap ℂ (RatFunc (RatFunc ℂ)))
            (map_zero (algebraMap ℂ (RatFunc (RatFunc ℂ)))) γ)
        = ∑ p ∈ (Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ))
              (map_zero (algebraMap ℂ (RatFunc ℂ))) γ).support,
            algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
              ((Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ))
                (map_zero (algebraMap ℂ (RatFunc ℂ))) γ) p) *
              ratFuncScale (σ p.1) (hσne p.1) ((cylDeriv lam')^[p.2] (cotModel c₀')) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum,
        Finsupp.support_mapRange_of_injective (map_zero (algebraMap ℂ (RatFunc (RatFunc ℂ)))) γ
          (algebraMap ℂ (RatFunc (RatFunc ℂ))).injective,
        Finsupp.support_mapRange_of_injective (map_zero (algebraMap ℂ (RatFunc ℂ))) γ
          (algebraMap ℂ (RatFunc ℂ)).injective]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, smul_eq_mul, hjets p.1 p.2]
      congr 1
    intro hcon
    refine htarget ?_
    rw [← hchar]
    exact hcon
  · intro i k
    fin_cases i
    · show addTranslationMeroEquiv (ω 0) (twoCylinderEmbed hl k)
        = twoCylinderEmbed hl (ratFuncScaleEquiv_twoCylinderTranslationAction (algebraMap ℂ (RatFunc ℂ) q0) hq0R k)
      exact addTranslationMeroEquiv_twoCylinderEmbed hl (ω 0) hper0 k
    · show addTranslationMeroEquiv (ω 1) (twoCylinderEmbed hl k)
        = twoCylinderEmbed hl (cylinderCoeffScaleEquiv hq1 k)
      exact addTranslationMeroEquiv_twoCylinderEmbed_coeff hl (ω 1) hper1 k
  · intro i y
    exact addTranslationMeroEquiv_deriv (ω i) y
  · intro i z
    exact addTranslationMeroEquiv_algebraMap_complex_self (ω i) z
  · intro z hz
    exact hfix z (hz 0) (hz 1)

/-! ### The imaginary-ray specialization -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The double-sine defect orbit is differentially independent.**  For periods `i a`, `i b` with
`a, b > 0` and `a/b` irrational, the translates of the constructed multiple-sine source by shifts in
distinct classes modulo the period lattice are differentially independent over the two-cylinder
function field. -/
theorem differentialIndependent_doubleSineOrbit_imaginaryRay {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) {κ : Type*} [DecidableEq κ] (sh : κ → ℂ)
    (hsep : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * (Complex.I * (a : ℂ)) + (n : ℂ) * (Complex.I * (b : ℂ))) :
    letI : Differential (RatFunc ℂ) :=
      cylinderDifferential (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)))
    letI : Differential (RatFunc (RatFunc ℂ)) :=
      twoCylinderDifferential (algebraMap ℂ (RatFunc ℂ)
        (2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))))
    letI : Algebra (RatFunc (RatFunc ℂ)) (meroField (Set.univ : Set ℂ)) :=
      (twoCylinderEmbed (linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr)).toAlgebra
    ∃ M : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (Complex.I * (a : ℂ)) M - M
          = -periodCotMero (Complex.I * (b : ℂ)) ∧
        DifferentialIndependent (RatFunc (RatFunc ℂ))
          (fun j : κ => addTranslationMeroEquiv (sh j) M) := by
  classical
  set ω : Fin 2 → ℂ := ![Complex.I * (a : ℂ), Complex.I * (b : ℂ)] with hωdef
  have hω0 : ω 0 = Complex.I * (a : ℂ) := by simp [hωdef]
  have hω1 : ω 1 = Complex.I * (b : ℂ) := by simp [hωdef]
  have haC : ((a : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt ha
  have hbC : ((b : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hb
  have hω0ne : ω 0 ≠ 0 := by
    rw [hω0]
    exact mul_ne_zero Complex.I_ne_zero haC
  have hω1ne : ω 1 ≠ 0 := by
    rw [hω1]
    exact mul_ne_zero Complex.I_ne_zero hbC
  set l : Fin 2 → ℂ :=
    ![2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (a : ℂ)),
      2 * (Real.pi : ℂ) * Complex.I / (Complex.I * (b : ℂ))] with hldef
  have hl : LinearIndependent ℚ l :=
    linearIndependent_cylinderFrequencies_imaginaryRay ha hb hirr
  have hl0 : l 0 = 2 * (Real.pi : ℂ) * Complex.I / ω 0 := by
    rw [hldef, hω0]
    simp
  have hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1 := by
    rw [hldef, hω1]
    simp
  have hper0 : Complex.exp (l 0 * ω 0) = 1 := by
    rw [hl0, div_mul_cancel₀ _ hω0ne]
    simp
  have hper1 : Complex.exp (l 1 * ω 1) = 1 := by
    rw [hl1, div_mul_cancel₀ _ hω1ne]
    simp
  have hprod : l 1 * ω 0 = 2 * (Real.pi : ℂ) * Complex.I * ((a / b : ℝ) : ℂ) := by
    rw [hl1, hω1, hω0]
    push_cast
    field_simp
  have htor : ∀ n : ℤ, n ≠ 0 → Complex.exp (l 1 * ω 0) ^ n ≠ 1 := by
    intro n hn
    rw [hprod]
    exact exp_two_pi_I_zpow_ne_one hirr hn
  have hfix : ∀ z : meroField (Set.univ : Set ℂ),
      addTranslationMeroEquiv (ω 0) z = z → addTranslationMeroEquiv (ω 1) z = z →
        ∃ w : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) w = z := by
    intro z h1 h2
    rw [hω0] at h1
    rw [hω1] at h2
    exact exists_constant_of_two_imaginaryPeriods_fixed hirr h1 h2
  obtain ⟨M, cst, hM0, hM1⟩ := exists_doubleSine_source_imaginaryRay ha hb
  refine ⟨M, hM0, ?_⟩
  have hsep' : ∀ i j : κ, i ≠ j → ∀ m n : ℤ,
      sh i - sh j ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1 := by
    intro i j hij m n
    rw [hω0, hω1]
    exact hsep i j hij m n
  exact differentialIndependent_orbit_of_exact_defects hl ω hω0ne hω1ne hl0 hl1 hper0 hper1
    htor hfix M cst (by rw [hω0, hω1]; exact hM0) (by rw [hω0, hω1]; exact hM1) sh hsep'

end

end GaloisForLFunctions.HTGeometry
