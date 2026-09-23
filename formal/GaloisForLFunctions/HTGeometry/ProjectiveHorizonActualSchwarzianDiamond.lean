import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianHorizonMeet
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetTailTransition

/-!
# The actual hypertranscendental projective-horizon diamond

For a hypertranscendental scalar over a differential field of constants, the direct and reciprocal
first derivative tails have an exact field-theoretic intersection: the differential field generated
by the Schwarzian.  Their join is the full order-zero jet field, while advancing either cutoff to
depth two collapses the intersection to the coefficient field.

The free-jet meet theorem already identifies the universal intersection.  The main work here is to
prove that the canonical evaluation of the free rational jet field at an actual HT jet family
commutes with the derivation, then transport the exact free meet to the actual carrier.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

open HTGeometry MvPolynomial

/-- Canonical evaluation of the free rational jet field commutes with total differentiation when
the coefficient field maps to differential constants. -/
theorem map_freeJetShift
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [Algebra C E] [Differential E]
    (hconst : ∀ c : C, (algebraMap C E c)′ = 0)
    (x : E) (hx : HypertranscendentalOver C x)
    (f : FreeScalarJetField C) :
    ((projectiveHorizonJetParametrization x hx (freeJetShift C f) :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E) =
      (((projectiveHorizonJetParametrization x hx f :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E))′ := by
  let J := IntermediateField.adjoin C
    (Set.range fun n : ℕ => differentialJet n x)
  let e := projectiveHorizonJetParametrization x hx
  let phi : FreeScalarJetField C →ₐ[C] E :=
    (IntermediateField.val J).comp e.toAlgHom
  change phi (freeJetShift C f) = Differential.deriv (phi f)
  have hpoly : ∀ p : FreeScalarJetPolynomial C,
      phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
        (freeJetShiftPolynomialDerivation C p)) =
      Differential.deriv
        (phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) p)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
        rw [show freeJetShiftPolynomialDerivation C (MvPolynomial.C c) = 0 from
          (freeJetShiftPolynomialDerivation C).map_algebraMap c,
          map_zero, map_zero]
        rw [show phi (algebraMap (FreeScalarJetPolynomial C)
          (FreeScalarJetField C) (MvPolynomial.C c)) = algebraMap C E c by
            calc
              phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
                  (MvPolynomial.C c)) =
                  phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
                    (algebraMap C (FreeScalarJetPolynomial C) c)) := by
                      rw [MvPolynomial.algebraMap_eq]
              _ = phi (algebraMap C (FreeScalarJetField C) c) := by
                    rw [IsScalarTower.algebraMap_apply C
                      (FreeScalarJetPolynomial C) (FreeScalarJetField C)]
              _ = algebraMap C E c := phi.commutes c]
        rw [hconst c]
    | add p q hp hq =>
        simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | mul_X p n hp =>
        have hn : phi (freeCoordinate C ℕ n) = differentialJet n x := by
          change ((e (freeCoordinate C ℕ n) : J) : E) = _
          exact projectiveHorizonJetParametrization_freeCoordinate x hx n
        have hns : phi (freeCoordinate C ℕ (n + 1)) = differentialJet (n + 1) x := by
          change ((e (freeCoordinate C ℕ (n + 1)) : J) : E) = _
          exact projectiveHorizonJetParametrization_freeCoordinate x hx (n + 1)
        have hnP : phi (algebraMap (FreeScalarJetPolynomial C)
            (FreeScalarJetField C) (MvPolynomial.X n)) = differentialJet n x := by
          simpa only [freeCoordinate] using hn
        have hnsP : phi (algebraMap (FreeScalarJetPolynomial C)
            (FreeScalarJetField C) (MvPolynomial.X (n + 1))) =
            differentialJet (n + 1) x := by
          simpa only [freeCoordinate] using hns
        simp only [smul_eq_mul, Derivation.leibniz, map_add, map_mul,
          freeJetShiftPolynomialDerivation_X, Differential.deriv.leibniz, hp]
        change phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) p) *
            phi (freeCoordinate C ℕ (n + 1)) +
          phi (freeCoordinate C ℕ n) *
            Differential.deriv
              (phi (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) p)) = _
        rw [hn, hns, hnP, differentialJet_succ]
  rcases IsLocalization.surj
    (nonZeroDivisors (FreeScalarJetPolynomial C)) f with ⟨⟨p, s⟩, hf⟩
  have hs0 : algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) s.1 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hphis0 : phi (algebraMap (FreeScalarJetPolynomial C)
      (FreeScalarJetField C) s.1) ≠ 0 := by
    intro hzero
    apply hs0
    apply phi.injective
    exact hzero.trans (map_zero phi).symm
  have hfree := congrArg (freeJetShift C) hf
  simp only [Derivation.leibniz, smul_eq_mul, freeJetShift_algebraMap] at hfree
  have hactual := congrArg Differential.deriv (congrArg phi hf)
  simp only [map_mul, Differential.deriv.leibniz, smul_eq_mul] at hactual
  have hfreephi := congrArg phi hfree
  simp only [map_add, map_mul] at hfreephi
  rw [hpoly p, hpoly s.1] at hfreephi
  apply (mul_left_cancel₀ hphis0)
  linear_combination hfreephi - hactual

/-- Canonical evaluation commutes with every iterated differential jet. -/
theorem map_differentialJet
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [Algebra C E] [Differential E]
    (hconst : ∀ c : C, (algebraMap C E c)′ = 0)
    (x : E) (hx : HypertranscendentalOver C x)
    (k : ℕ) (f : FreeScalarJetField C) :
    ((projectiveHorizonJetParametrization x hx (differentialJet k f) :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E) =
      differentialJet k
        ((projectiveHorizonJetParametrization x hx f :
          IntermediateField.adjoin C
            (Set.range fun n : ℕ => differentialJet n x)) : E) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [differentialJet_succ, freeScalarJetField_deriv_apply,
        map_freeJetShift hconst x hx, ih, differentialJet_succ]

/-! ## Coefficient base change of the free scalar jet -/

/-- Coefficient extension on the polynomial free scalar jet. -/
def freeScalarJetBaseChangePoly
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    FreeScalarJetPolynomial K →+* FreeScalarJetPolynomial L :=
  MvPolynomial.map (algebraMap K L)

theorem freeScalarJetBaseChangePoly_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Function.Injective (freeScalarJetBaseChangePoly K L) :=
  MvPolynomial.map_injective _ (algebraMap K L).injective

/-- Injective coefficient extension on the rational free scalar jet field. -/
def freeScalarJetBaseChange
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    FreeScalarJetField K →+* FreeScalarJetField L :=
  IsFractionRing.lift
    (g := (algebraMap (FreeScalarJetPolynomial L) (FreeScalarJetField L)).comp
      (freeScalarJetBaseChangePoly K L))
    (fun _ _ h => freeScalarJetBaseChangePoly_injective K L
      ((IsFractionRing.injective (FreeScalarJetPolynomial L) (FreeScalarJetField L)) h))

@[simp]
theorem freeScalarJetBaseChange_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : FreeScalarJetPolynomial K) :
    freeScalarJetBaseChange K L
        (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K) p) =
      algebraMap (FreeScalarJetPolynomial L) (FreeScalarJetField L)
        (freeScalarJetBaseChangePoly K L p) :=
  IsFractionRing.lift_algebraMap _ p

@[simp]
theorem freeScalarJetBaseChange_freeCoordinate
    {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ) :
    freeScalarJetBaseChange K L (freeCoordinate K ℕ n) =
      freeCoordinate L ℕ n := by
  rw [freeCoordinate, freeScalarJetBaseChange_algebraMap,
    freeScalarJetBaseChangePoly, MvPolynomial.map_X]
  rfl

theorem freeScalarJetBaseChangePoly_freeJetShift
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : FreeScalarJetPolynomial K) :
    freeScalarJetBaseChangePoly K L (freeJetShiftPolynomialDerivation K p) =
      freeJetShiftPolynomialDerivation L (freeScalarJetBaseChangePoly K L p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [show freeJetShiftPolynomialDerivation K (MvPolynomial.C c) = 0 from
        (freeJetShiftPolynomialDerivation K).map_algebraMap c,
        map_zero, freeScalarJetBaseChangePoly, MvPolynomial.map_C]
      exact ((freeJetShiftPolynomialDerivation L).map_algebraMap
        (algebraMap K L c)).symm
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p n hp =>
      simp only [smul_eq_mul, Derivation.leibniz, map_add, map_mul,
        freeScalarJetBaseChangePoly, MvPolynomial.map_X,
        freeJetShiftPolynomialDerivation_X]
      have hp' : MvPolynomial.map (algebraMap K L)
            (freeJetShiftPolynomialDerivation K p) =
          freeJetShiftPolynomialDerivation L
            (MvPolynomial.map (algebraMap K L) p) := by
        simpa only [freeScalarJetBaseChangePoly] using hp
      rw [hp']

/-- Coefficient extension commutes with the total scalar-jet shift. -/
theorem freeScalarJetBaseChange_freeJetShift
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : FreeScalarJetField K) :
    freeScalarJetBaseChange K L (freeJetShift K f) =
      freeJetShift L (freeScalarJetBaseChange K L f) := by
  let B := freeScalarJetBaseChange K L
  have hpoly : ∀ p : FreeScalarJetPolynomial K,
      B (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
          (freeJetShiftPolynomialDerivation K p)) =
        freeJetShift L
          (B (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K) p)) := by
    intro p
    rw [freeScalarJetBaseChange_algebraMap,
      freeScalarJetBaseChange_algebraMap,
      freeScalarJetBaseChangePoly_freeJetShift,
      freeJetShift_algebraMap]
  rcases IsLocalization.surj
    (nonZeroDivisors (FreeScalarJetPolynomial K)) f with ⟨⟨p, s⟩, hf⟩
  have hs0 : algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K) s.1 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hBs0 : B (algebraMap (FreeScalarJetPolynomial K)
      (FreeScalarJetField K) s.1) ≠ 0 := by
    intro hzero
    apply hs0
    apply B.injective
    exact hzero.trans (map_zero B).symm
  have hfree := congrArg (freeJetShift K) hf
  simp only [Derivation.leibniz, smul_eq_mul, freeJetShift_algebraMap] at hfree
  have htarget := congrArg (freeJetShift L) (congrArg B hf)
  simp only [map_mul, Derivation.leibniz, smul_eq_mul] at htarget
  have hsource := congrArg B hfree
  simp only [map_add, map_mul] at hsource
  rw [hpoly p, hpoly s.1] at hsource
  apply (mul_left_cancel₀ hBs0)
  linear_combination hsource - htarget

theorem freeScalarJetBaseChange_differentialJet
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (k : ℕ) (f : FreeScalarJetField K) :
    freeScalarJetBaseChange K L (differentialJet k f) =
      differentialJet k (freeScalarJetBaseChange K L f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [differentialJet_succ, freeScalarJetField_deriv_apply,
        freeScalarJetBaseChange_freeJetShift, ih, differentialJet_succ,
        freeScalarJetField_deriv_apply]

theorem freeScalarJetBaseChange_freeJetBase
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    freeScalarJetBaseChange K L (freeJetBase K) = freeJetBase L := by
  exact freeScalarJetBaseChange_freeCoordinate 0

theorem freeScalarJetBaseChange_freeJetSchwarzian
    {K L : Type*} [Field K] [CharZero K]
    [Field L] [CharZero L] [Algebra K L] :
    freeScalarJetBaseChange K L (freeJetSchwarzian K) =
      freeJetSchwarzian L := by
  rw [freeJetSchwarzian, freeJetSchwarzian, schwarzian, schwarzian]
  rw [freeJetBase_deriv3 K, freeJetBase_deriv2 K, freeJetBase_deriv K,
    freeJetBase_deriv3 L, freeJetBase_deriv2 L, freeJetBase_deriv L]
  simp only [map_sub, map_div₀, map_mul, map_pow,
    freeScalarJetBaseChange_freeCoordinate]
  congr 2
  norm_num [map_ofNat]

/-- Every formal Schwarzian jet is defined over the prime field and is preserved by arbitrary
coefficient extension. -/
theorem freeScalarJetBaseChange_schwarzianJet
    {K L : Type*} [Field K] [CharZero K]
    [Field L] [CharZero L] [Algebra K L]
    (k : ℕ) :
    freeScalarJetBaseChange K L
        (differentialJet k (freeJetSchwarzian K)) =
      differentialJet k (freeJetSchwarzian L) := by
  rw [freeScalarJetBaseChange_differentialJet,
    freeScalarJetBaseChange_freeJetSchwarzian]

/-- Actual evaluation is natural under coefficient extension. -/
theorem map_freeScalarJetBaseChange
    {K C E : Type*} [Field K] [CharZero K]
    [Field C] [CharZero C] [Field E]
    [Algebra K C] [Algebra C E] [Algebra K E] [IsScalarTower K C E]
    [Differential E]
    (x : E) (hxK : HypertranscendentalOver K x)
    (hxC : HypertranscendentalOver C x)
    (f : FreeScalarJetField K) :
    ((projectiveHorizonJetParametrization x hxC
          (freeScalarJetBaseChange K C f) :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E) =
      ((projectiveHorizonJetParametrization x hxK f :
        IntermediateField.adjoin K
          (Set.range fun n : ℕ => differentialJet n x)) : E) := by
  let JC := IntermediateField.adjoin C
    (Set.range fun n : ℕ => differentialJet n x)
  let JK := IntermediateField.adjoin K
    (Set.range fun n : ℕ => differentialJet n x)
  let eC := projectiveHorizonJetParametrization x hxC
  let eK := projectiveHorizonJetParametrization x hxK
  let phiC : FreeScalarJetField C →+* E :=
    (IntermediateField.val JC).toRingHom.comp eC.toRingHom
  let phiK : FreeScalarJetField K →+* E :=
    (IntermediateField.val JK).toRingHom.comp eK.toRingHom
  let B := freeScalarJetBaseChange K C
  have hhom : phiC.comp B = phiK := by
    apply IsFractionRing.ringHom_ext (A := FreeScalarJetPolynomial K)
    intro p
    have hpoly :
        (phiC.comp B).comp
            (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)) =
          phiK.comp
            (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)) := by
      apply MvPolynomial.ringHom_ext
      · intro k
        change phiC
            (B (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
              (MvPolynomial.C k))) =
          phiK (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
            (MvPolynomial.C k))
        rw [freeScalarJetBaseChange_algebraMap]
        simp only [freeScalarJetBaseChangePoly, MvPolynomial.map_C]
        rw [show algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
              (MvPolynomial.C (algebraMap K C k)) =
            algebraMap C (FreeScalarJetField C) (algebraMap K C k) by
          rw [← MvPolynomial.algebraMap_eq]
          exact (IsScalarTower.algebraMap_apply C
            (FreeScalarJetPolynomial C) (FreeScalarJetField C) _).symm,
          show algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
              (MvPolynomial.C k) = algebraMap K (FreeScalarJetField K) k by
            rw [← MvPolynomial.algebraMap_eq]
            exact (IsScalarTower.algebraMap_apply K
              (FreeScalarJetPolynomial K) (FreeScalarJetField K) _).symm]
        change ((eC (algebraMap C (FreeScalarJetField C) (algebraMap K C k)) : JC) : E) =
          ((eK (algebraMap K (FreeScalarJetField K) k) : JK) : E)
        rw [eC.commutes, eK.commutes]
        change algebraMap C E (algebraMap K C k) = algebraMap K E k
        exact (IsScalarTower.algebraMap_apply K C E k).symm
      · intro n
        change phiC
            (B (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
              (MvPolynomial.X n))) =
          phiK (algebraMap (FreeScalarJetPolynomial K) (FreeScalarJetField K)
            (MvPolynomial.X n))
        change phiC (B (freeCoordinate K ℕ n)) =
          phiK (freeCoordinate K ℕ n)
        rw [freeScalarJetBaseChange_freeCoordinate]
        change ((eC (freeCoordinate C ℕ n) : JC) : E) =
          ((eK (freeCoordinate K ℕ n) : JK) : E)
        rw [projectiveHorizonJetParametrization_freeCoordinate,
          projectiveHorizonJetParametrization_freeCoordinate]
    exact RingHom.congr_fun hpoly p
  exact RingHom.congr_fun hhom f

theorem map_freeJetBase
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [Algebra C E] [Differential E]
    (x : E) (hx : HypertranscendentalOver C x) :
    ((projectiveHorizonJetParametrization x hx (freeJetBase C) :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E) = x := by
  simpa only [freeJetBase, differentialJet_zero] using
    projectiveHorizonJetParametrization_freeCoordinate x hx 0

theorem map_freeJetSchwarzian
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [Algebra C E] [Differential E]
    (hconst : ∀ c : C, (algebraMap C E c)′ = 0)
    (x : E) (hx : HypertranscendentalOver C x) :
    ((projectiveHorizonJetParametrization x hx (freeJetSchwarzian C) :
        IntermediateField.adjoin C
          (Set.range fun n : ℕ => differentialJet n x)) : E) =
      schwarzian x := by
  let J := IntermediateField.adjoin C
    (Set.range fun n : ℕ => differentialJet n x)
  let e := projectiveHorizonJetParametrization x hx
  let phi : FreeScalarJetField C →ₐ[C] E :=
    (IntermediateField.val J).comp e.toAlgHom
  change phi (freeJetSchwarzian C) = schwarzian x
  rw [freeJetSchwarzian, schwarzian]
  change phi
      (differentialJet 3 (freeJetBase C) / differentialJet 1 (freeJetBase C) -
        (3 / 2 : FreeScalarJetField C) *
          (differentialJet 2 (freeJetBase C) /
            differentialJet 1 (freeJetBase C)) ^ (2 : ℕ)) =
    differentialJet 3 x / differentialJet 1 x -
      (3 / 2 : E) * (differentialJet 2 x / differentialJet 1 x) ^ (2 : ℕ)
  simp only [map_sub, map_div₀, map_mul, map_pow]
  have hbase : phi (freeJetBase C) = x := by
    change ((e (freeJetBase C) : J) : E) = x
    exact map_freeJetBase x hx
  have hj (k : ℕ) : phi (differentialJet k (freeJetBase C)) = differentialJet k x := by
    change ((e (differentialJet k (freeJetBase C)) : J) : E) = _
    rw [map_differentialJet hconst x hx, map_freeJetBase x hx]
  rw [hj 1, hj 2, hj 3]
  congr 2
  norm_num [map_ofNat]

/-- Every universal Schwarzian jet evaluates to the corresponding actual Schwarzian jet. -/
theorem map_freeJetSchwarzian_differentialJet_of_constants
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [Algebra C E] [Differential E]
    (hconst : ∀ c : C, (algebraMap C E c)′ = 0)
    (x : E) (hx : HypertranscendentalOver C x) (k : ℕ) :
    ((projectiveHorizonJetParametrization x hx
        (differentialJet k (freeJetSchwarzian C)) :
          IntermediateField.adjoin C
            (Set.range fun n : ℕ => differentialJet n x)) : E) =
      differentialJet k (schwarzian x) := by
  rw [map_differentialJet hconst x hx,
    map_freeJetSchwarzian hconst x hx]

theorem deriv_algebraMap_rat_eq_zero
    {E : Type*} [Field E] [CharZero E] [Differential E] (q : ℚ) :
    (algebraMap ℚ E q)′ = 0 := by
  rw [eq_ratCast (algebraMap ℚ E) q, Rat.cast_def]
  rw [Derivation.leibniz_div]
  simp

/-- Hypertranscendence descends from an arbitrary characteristic-zero coefficient field to the
prime field. -/
theorem hypertranscendentalOver_restrictRat
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E] [Differential E]
    {x : E} (hx : HypertranscendentalOver C x) :
    HypertranscendentalOver ℚ x := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  exact AlgebraicIndependent.restrictScalars
    (FaithfulSMul.algebraMap_injective ℚ C)
    ((hypertranscendentalOver_iff_differentialIndependent_singleton C x).mp hx)

/-- Every universal Schwarzian jet evaluates correctly over an arbitrary differential coefficient
field.  The constant-base restriction disappears because the entire Schwarzian tower is defined
over the prime field. -/
theorem map_freeJetSchwarzian_differentialJet
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E] [Differential E]
    (x : E) (hx : HypertranscendentalOver C x) (k : ℕ) :
    ((projectiveHorizonJetParametrization x hx
        (differentialJet k (freeJetSchwarzian C)) :
          IntermediateField.adjoin C
            (Set.range fun n : ℕ => differentialJet n x)) : E) =
      differentialJet k (schwarzian x) := by
  have hxQ : HypertranscendentalOver ℚ x :=
    hypertranscendentalOver_restrictRat hx
  calc
    ((projectiveHorizonJetParametrization x hx
        (differentialJet k (freeJetSchwarzian C)) :
          IntermediateField.adjoin C
            (Set.range fun n : ℕ => differentialJet n x)) : E) =
        ((projectiveHorizonJetParametrization x hx
          (freeScalarJetBaseChange ℚ C
            (differentialJet k (freeJetSchwarzian ℚ))) :
            IntermediateField.adjoin C
              (Set.range fun n : ℕ => differentialJet n x)) : E) := by
          rw [freeScalarJetBaseChange_schwarzianJet]
    _ = ((projectiveHorizonJetParametrization x hxQ
          (differentialJet k (freeJetSchwarzian ℚ)) :
            IntermediateField.adjoin ℚ
              (Set.range fun n : ℕ => differentialJet n x)) : E) :=
      map_freeScalarJetBaseChange x hxQ hx _
    _ = differentialJet k (schwarzian x) :=
      map_freeJetSchwarzian_differentialJet_of_constants
        deriv_algebraMap_rat_eq_zero x hxQ k

/-- Differential field generated by the actual Schwarzian jet family. -/
def actualSchwarzianDifferentialField
    (C : Type*) {E : Type*} [Field C] [Field E] [Algebra C E]
    [Differential E] (x : E) : IntermediateField C E :=
  IntermediateField.adjoin C
    (Set.range fun k : ℕ => differentialJet k (schwarzian x))

theorem jetTailField_deriv_mem
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    (x : E) (n : ℕ) {z : E} (hz : z ∈ jetTailField C x n) :
    z′ ∈ jetTailField C x n := by
  let J := jetTailField C x n
  let S : Set E := (fun m : ℕ => differentialJet m x) '' Set.Ici n
  change z ∈ IntermediateField.adjoin C S at hz
  change z′ ∈ J
  apply IntermediateField.adjoin_induction C
    (p := fun y _ => y′ ∈ J)
  · intro y hy
    change y ∈ S at hy
    rcases hy with ⟨m, hm, rfl⟩
    change (differentialJet m x)′ ∈ IntermediateField.adjoin C S
    have hm' : n ≤ m + 1 := by
      change n ≤ m at hm
      omega
    have hgen := IntermediateField.subset_adjoin C S
      (show differentialJet (m + 1) x ∈ S from ⟨m + 1, hm', rfl⟩)
    rw [← differentialJet_succ]
    exact hgen
  · intro c
    rw [DifferentialAlgebra.deriv_algebraMap]
    exact J.algebraMap_mem c′
  · intro y w hy hw hy' hw'
    rw [map_add]
    exact J.add_mem hy' hw'
  · intro y hy hy'
    rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
    rw [pow_two]
    exact J.mul_mem (J.neg_mem (J.mul_mem (J.inv_mem hy) (J.inv_mem hy))) hy'
  · intro y w hy hw hy' hw'
    rw [Differential.deriv.leibniz]
    exact J.add_mem (J.mul_mem hy hw') (J.mul_mem hw hy')
  · exact hz

theorem differentialJet_mem_jetTailField_of_mem
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    (x : E) (n : ℕ) {z : E} (hz : z ∈ jetTailField C x n)
    (k : ℕ) : differentialJet k z ∈ jetTailField C x n := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [differentialJet_succ]
      exact jetTailField_deriv_mem x n ih

theorem actualSchwarzianDifferentialField_le_inf
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    (x : E) (hx : HypertranscendentalOver C x) :
    actualSchwarzianDifferentialField C x ≤
      jetTailField C x 1 ⊓ jetTailField C x⁻¹ 1 := by
  have hs := hypertranscendentalOver_schwarzian_mem_inf_firstJetTail_inv x hx
  rw [actualSchwarzianDifferentialField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨k, rfl⟩
  exact ⟨differentialJet_mem_jetTailField_of_mem x 1 hs.1 k,
    differentialJet_mem_jetTailField_of_mem x⁻¹ 1 hs.2 k⟩

theorem inf_le_actualSchwarzianDifferentialField
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E]
    [Differential E]
    (x : E) (hx : HypertranscendentalOver C x) :
    jetTailField C x 1 ⊓ jetTailField C x⁻¹ 1 ≤
      actualSchwarzianDifferentialField C x := by
  intro z hz
  rw [IntermediateField.mem_inf] at hz
  let J0 := IntermediateField.adjoin C
    (Set.range fun n : ℕ => differentialJet n x)
  let e := projectiveHorizonJetParametrization x hx
  let phi : FreeScalarJetField C →ₐ[C] E :=
    (IntermediateField.val J0).comp e.toAlgHom
  have hzJ0 : z ∈ J0 := by
    change z ∈ IntermediateField.adjoin C
      (Set.range fun n : ℕ => differentialJet n x)
    rw [← jetTailField_zero_eq_adjoin_range C x]
    exact jetTailField_antitone C x (by omega) hz.1
  let z0 : J0 := ⟨z, hzJ0⟩
  let f : FreeScalarJetField C := e.symm z0
  have hraw : f ∈ freeJetRawTailField C 1 :=
    projectiveHorizonJetParametrization_symm_mem_freeJetRawTailField
      x hx 1 z0 hz.1
  have hrec : f ∈ freeJetReciprocalTailField C 1 :=
    projectiveHorizonJetParametrization_symm_mem_freeJetReciprocalTailField
      x hx 1 z0 hz.2
  have hfree : f ∈ schwarzianDifferentialField C := by
    rw [← jetTail_inf_eq_schwarzianDifferentialField]
    rw [IntermediateField.mem_inf]
    constructor
    · simpa only [freeJetRawTailField_eq_jetTailField] using hraw
    · simpa only [freeJetReciprocalTailField_eq_jetTailField_inv] using hrec
  have himage : phi f ∈ actualSchwarzianDifferentialField C x := by
    rw [schwarzianDifferentialField] at hfree
    apply IntermediateField.adjoin_induction C
      (p := fun y _ => phi y ∈ actualSchwarzianDifferentialField C x)
    · intro y hy
      change y ∈ Set.range (fun k : ℕ => differentialJet k (freeJetSchwarzian C)) at hy
      rcases hy with ⟨k, rfl⟩
      rw [show phi (differentialJet k (freeJetSchwarzian C)) =
          differentialJet k (schwarzian x) by
        change ((e (differentialJet k (freeJetSchwarzian C)) : J0) : E) = _
        exact map_freeJetSchwarzian_differentialJet x hx k]
      exact IntermediateField.subset_adjoin C _ (Set.mem_range_self k)
    · intro c
      rw [phi.commutes]
      exact (actualSchwarzianDifferentialField C x).algebraMap_mem c
    · intro y w hy hw hy' hw'
      rw [map_add]
      exact (actualSchwarzianDifferentialField C x).add_mem hy' hw'
    · intro y hy hy'
      rw [map_inv₀]
      exact (actualSchwarzianDifferentialField C x).inv_mem hy'
    · intro y w hy hw hy' hw'
      rw [map_mul]
      exact (actualSchwarzianDifferentialField C x).mul_mem hy' hw'
    · exact hfree
  have hphif : phi f = z := by
    change ((e (e.symm z0) : J0) : E) = z
    rw [e.apply_symm_apply]
  rwa [hphif] at himage

/-- Opposite actual first horizons meet exactly in the actual Schwarzian differential field. -/
theorem actual_projectiveHorizon_firstMeet_eq_schwarzianDifferentialField
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    (x : E) (hx : HypertranscendentalOver C x) :
    jetTailField C x 1 ⊓ jetTailField C x⁻¹ 1 =
      actualSchwarzianDifferentialField C x := by
  exact le_antisymm
    (inf_le_actualSchwarzianDifferentialField x hx)
    (actualSchwarzianDifferentialField_le_inf x hx)

/-- **Sharp actual projective-horizon diamond.**  Opposite first horizons join to the full intrinsic
jet field and meet exactly in projective curvature; advancing either horizon one further step
erases every common nonconstant rational differential observable. -/
theorem hypertranscendentalOver_projectiveHorizon_schwarzianDiamond
    {C E : Type*} [Field C] [CharZero C]
    [Field E] [CharZero E] [Algebra C E]
    [Differential C] [Differential E] [DifferentialAlgebra C E]
    (x : E) (hx : HypertranscendentalOver C x) :
    jetTailField C x 1 ⊔ jetTailField C x⁻¹ 1 = jetTailField C x 0 ∧
      jetTailField C x 1 ⊓ jetTailField C x⁻¹ 1 =
        actualSchwarzianDifferentialField C x ∧
      ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → (2 ≤ m ∨ 2 ≤ n) →
        jetTailField C x m ⊓ jetTailField C x⁻¹ n = ⊥ := by
  exact ⟨hypertranscendentalOver_sup_firstJetTail_inv_eq_zeroJetTail x hx,
    actual_projectiveHorizon_firstMeet_eq_schwarzianDifferentialField x hx,
    fun hm hn hdeep =>
      hypertranscendentalOver_jetTailField_inf_inv_eq_bot x hx hm hn hdeep⟩

end

end GaloisForLFunctions
