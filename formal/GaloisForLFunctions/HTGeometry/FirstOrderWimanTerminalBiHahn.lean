import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalBaseChange
import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalCharge
import GaloisForLFunctions.HTGeometry.MahlerHahnModel
import GaloisForLFunctions.HTGeometry.HahnFractionValuation
import GaloisForLFunctions.HTGeometry.DerivationPrescription

/-!
# Differential two-level Hahn realization of the terminal Wiman branch

The nested Laurent model embeds faithfully into a two-level Hahn field with rational value groups.
Both value-group Euler operators are genuine complex-linear derivations there.  The inner operator
intertwines the integer Laurent grading and detects the exact nonzero Wiman charge.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries PowerSeries
open scoped LaurentSeries

noncomputable section

abbrev FirstOrderTerminalInnerHahnField := HahnSeries ℚ ℂ

abbrev FirstOrderTerminalBiHahnCoefficientField :=
  AlgebraicClosure FirstOrderTerminalInnerHahnField

abbrev FirstOrderTerminalBiHahnField :=
  HahnSeries ℚ FirstOrderTerminalBiHahnCoefficientField

/-- Faithful coefficientwise transport from the nested Laurent branch to rational Hahn grades. -/
noncomputable def firstOrderTerminalBiHahnEmbedding :
    FirstOrderTerminalLaurentField →+* FirstOrderTerminalBiHahnField :=
  (laurentToHahn (k := FirstOrderTerminalBiHahnCoefficientField)).comp
    (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ)))

theorem firstOrderTerminalBiHahnEmbedding_injective :
    Function.Injective firstOrderTerminalBiHahnEmbedding :=
  (laurentToHahn (k := FirstOrderTerminalBiHahnCoefficientField)).injective.comp
    (firstOrderTerminalLaurentBaseChange_injective (laurentToHahn (k := ℂ)))

theorem laurentToHahn_single
    {k : Type*} [Field k] (e : ℤ) (c : k) :
    laurentToHahn (k := k) (HahnSeries.single e c) =
      HahnSeries.single (e : ℚ) c := by
  ext d
  by_cases hd : ∃ n : ℤ, (n : ℚ) = d
  · obtain ⟨n, rfl⟩ := hd
    rw [coeff_laurentToHahn]
    by_cases hn : n = e
    · subst n
      simp
    · rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
      simp [hn]
  · rw [coeff_laurentToHahn_of_not_int _ (fun n hn => hd ⟨n, hn⟩)]
    rw [HahnSeries.coeff_single]
    by_cases heq : d = (e : ℚ)
    · exact (hd ⟨e, heq.symm⟩).elim
    · simp [heq]

theorem laurentToHahn_algebraMap
    {k : Type*} [Field k] (c : k) :
    laurentToHahn (k := k) (algebraMap k (LaurentSeries k) c) =
      algebraMap k (HahnSeries ℚ k) c := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    laurentToHahn_single]
  change HahnSeries.single (0 : ℚ) c =
    HahnSeries.ofPowerSeries ℚ k (PowerSeries.C c)
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

theorem hahnSeriesRat_algebraMap_eq_C
    {k : Type*} [Field k] (c : k) :
    algebraMap k (HahnSeries ℚ k) c = HahnSeries.C c := by
  change HahnSeries.ofPowerSeries ℚ k (PowerSeries.C c) = HahnSeries.C c
  rw [HahnSeries.ofPowerSeries_C]

/-- Coefficient inclusion used by the original outer Laurent model. -/
noncomputable def firstOrderTerminalOuterCoefficientMap :
    FirstOrderTerminalCoefficientField →+* FirstOrderTerminalLaurentField :=
  algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField

/-- Coefficient inclusion used by the differential two-level Hahn target. -/
noncomputable def firstOrderTerminalBiHahnOuterCoefficientMap :
    FirstOrderTerminalBiHahnCoefficientField →+* FirstOrderTerminalBiHahnField :=
  algebraMap FirstOrderTerminalBiHahnCoefficientField FirstOrderTerminalBiHahnField

theorem firstOrderTerminalBiHahnEmbedding_single
    (e : ℤ) (c : FirstOrderTerminalCoefficientField) :
    firstOrderTerminalBiHahnEmbedding (HahnSeries.single e c) =
      HahnSeries.single (e : ℚ)
        (firstOrderTerminalCoefficientBaseChange (laurentToHahn (k := ℂ)) c) := by
  change laurentToHahn
      (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
        (HahnSeries.single e c)) = _
  rw [firstOrderTerminalLaurentBaseChange_single, laurentToHahn_single]

theorem firstOrderTerminalBiHahnEmbedding_inner_algebraMap
    (x : LaurentSeries ℂ) :
    firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x)) =
      firstOrderTerminalBiHahnOuterCoefficientMap
        (algebraMap FirstOrderTerminalInnerHahnField
          FirstOrderTerminalBiHahnCoefficientField
          (laurentToHahn (k := ℂ) x)) := by
  change laurentToHahn
      (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
        (firstOrderTerminalOuterCoefficientMap
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x))) = _
  rw [firstOrderTerminalOuterCoefficientMap]
  rw [firstOrderTerminalLaurentBaseChange_inner_algebraMap,
    laurentToHahn_algebraMap]
  rfl

/-- An arbitrary outer coefficient is transported to the corresponding constant in the
two-level Hahn target. -/
theorem firstOrderTerminalBiHahnEmbedding_outer_algebraMap
    (c : FirstOrderTerminalCoefficientField) :
    firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap c) =
      firstOrderTerminalBiHahnOuterCoefficientMap
        (firstOrderTerminalCoefficientBaseChange (laurentToHahn (k := ℂ)) c) := by
  change laurentToHahn
      (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
        (firstOrderTerminalOuterCoefficientMap c)) = _
  rw [firstOrderTerminalOuterCoefficientMap,
    firstOrderTerminalLaurentBaseChange_algebraMap,
    laurentToHahn_algebraMap]
  rfl

/-- The outer constant coefficient of a transported power series is its coefficient-field base
change. -/
theorem coeff_zero_firstOrderTerminalBiHahnEmbedding_coe
    (z : PowerSeries FirstOrderTerminalCoefficientField) :
    (firstOrderTerminalBiHahnEmbedding
      (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField z)).coeff 0 =
      firstOrderTerminalCoefficientBaseChange (laurentToHahn (k := ℂ))
        (PowerSeries.constantCoeff z) := by
  change (laurentToHahn
    (firstOrderTerminalLaurentBaseChange (laurentToHahn (k := ℂ))
      (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField z))).coeff 0 = _
  rw [show (0 : ℚ) = ((0 : ℤ) : ℚ) by norm_num,
    coeff_laurentToHahn, coeff_firstOrderTerminalLaurentBaseChange]
  congr 1
  change (HahnSeries.ofPowerSeries ℤ FirstOrderTerminalCoefficientField z).coeff 0 = _
  rw [PowerSeries.coeff_coe]
  exact congrFun PowerSeries.coeff_zero_eq_constantCoeff z

/-- Multiplication by an outer coefficient constant is multiplication by a constant power
series before passage to the outer Laurent field. -/
theorem firstOrderTerminalOuterCoefficientMap_mul_coe
    (c : FirstOrderTerminalCoefficientField)
    (z : PowerSeries FirstOrderTerminalCoefficientField) :
    firstOrderTerminalOuterCoefficientMap c *
        algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField z =
      algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
        FirstOrderTerminalLaurentField (PowerSeries.C c * z) := by
  rw [firstOrderTerminalOuterCoefficientMap, LaurentSeries.algebraMap_apply]
  change HahnSeries.single 0 c * HahnSeries.ofPowerSeries ℤ _ z =
    HahnSeries.ofPowerSeries ℤ _ (PowerSeries.C c * z)
  simpa [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply] using
    (map_mul (algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField) (PowerSeries.C c) z).symm

attribute [local instance 10000] HahnSeries.instAlgebra

noncomputable def firstOrderTerminalBiHahnCoefficientComplexMap :
    ℂ →+* FirstOrderTerminalBiHahnCoefficientField :=
  (algebraMap FirstOrderTerminalInnerHahnField
    FirstOrderTerminalBiHahnCoefficientField).comp
      (algebraMap ℂ FirstOrderTerminalInnerHahnField)

local instance firstOrderTerminalInnerHahnCharZero :
    CharZero FirstOrderTerminalInnerHahnField :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ FirstOrderTerminalInnerHahnField).injective

local instance firstOrderTerminalBiHahnCoefficientCharZero :
    CharZero FirstOrderTerminalBiHahnCoefficientField :=
  charZero_of_injective_algebraMap
    (algebraMap FirstOrderTerminalInnerHahnField
      FirstOrderTerminalBiHahnCoefficientField).injective

/-- Inner rational Hahn Euler derivation. -/
noncomputable def firstOrderTerminalInnerHahnEuler :
    Derivation ℂ FirstOrderTerminalInnerHahnField FirstOrderTerminalInnerHahnField :=
  hahnDerivationComplex ((Rat.castHom ℂ).toAddMonoidHom)

/-- Algebraic extension of the inner Euler derivation to the outer coefficient field. -/
noncomputable def firstOrderTerminalBiHahnCoefficientInnerEuler :
    Derivation ℂ FirstOrderTerminalBiHahnCoefficientField
      FirstOrderTerminalBiHahnCoefficientField := by
  letI : CharZero FirstOrderTerminalInnerHahnField :=
    charZero_of_injective_algebraMap
      (algebraMap ℂ FirstOrderTerminalInnerHahnField).injective
  letI : CharZero FirstOrderTerminalBiHahnCoefficientField :=
    charZero_of_injective_algebraMap
      (algebraMap FirstOrderTerminalInnerHahnField
        FirstOrderTerminalBiHahnCoefficientField).injective
  letI : Algebra.IsIntegral FirstOrderTerminalInnerHahnField
      FirstOrderTerminalBiHahnCoefficientField :=
    Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable FirstOrderTerminalInnerHahnField
      FirstOrderTerminalBiHahnCoefficientField := by infer_instance
  exact Classical.choose
    (exists_derivation_extension (K := ℂ) (F := FirstOrderTerminalInnerHahnField)
      (L := FirstOrderTerminalBiHahnCoefficientField)
      firstOrderTerminalInnerHahnEuler)

theorem firstOrderTerminalBiHahnCoefficientInnerEuler_algebraMap
    (x : FirstOrderTerminalInnerHahnField) :
    firstOrderTerminalBiHahnCoefficientInnerEuler
        (algebraMap FirstOrderTerminalInnerHahnField
          FirstOrderTerminalBiHahnCoefficientField x) =
      algebraMap FirstOrderTerminalInnerHahnField
        FirstOrderTerminalBiHahnCoefficientField
          (hahnGrade ((Rat.castHom ℂ).toAddMonoidHom) x) := by
  letI : CharZero FirstOrderTerminalInnerHahnField :=
    charZero_of_injective_algebraMap
      (algebraMap ℂ FirstOrderTerminalInnerHahnField).injective
  letI : CharZero FirstOrderTerminalBiHahnCoefficientField :=
    charZero_of_injective_algebraMap
      (algebraMap FirstOrderTerminalInnerHahnField
        FirstOrderTerminalBiHahnCoefficientField).injective
  letI : Algebra.IsIntegral FirstOrderTerminalInnerHahnField
      FirstOrderTerminalBiHahnCoefficientField :=
    Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable FirstOrderTerminalInnerHahnField
      FirstOrderTerminalBiHahnCoefficientField := by infer_instance
  exact Classical.choose_spec
    (exists_derivation_extension (K := ℂ) (F := FirstOrderTerminalInnerHahnField)
      (L := FirstOrderTerminalBiHahnCoefficientField)
      firstOrderTerminalInnerHahnEuler) x

/-- Inner Euler derivation lifted coefficientwise through the outer Hahn variable. -/
noncomputable def firstOrderTerminalBiHahnInnerEuler :
    Derivation ℂ FirstOrderTerminalBiHahnField FirstOrderTerminalBiHahnField :=
  hahnCoefficientDerivation firstOrderTerminalBiHahnCoefficientInnerEuler

@[simp] theorem coeff_firstOrderTerminalBiHahnInnerEuler
    (x : FirstOrderTerminalBiHahnField) (e : ℚ) :
    (firstOrderTerminalBiHahnInnerEuler x).coeff e =
      firstOrderTerminalBiHahnCoefficientInnerEuler (x.coeff e) :=
  coeff_hahnCoefficientDerivation _ _ _

/-- The coefficientwise inner Euler derivation preserves every outer Hahn grade. -/
theorem firstOrderTerminalBiHahnInnerEuler_single
    (e : ℚ) (c : FirstOrderTerminalBiHahnCoefficientField) :
    firstOrderTerminalBiHahnInnerEuler (HahnSeries.single e c) =
      HahnSeries.single e (firstOrderTerminalBiHahnCoefficientInnerEuler c) := by
  ext d
  rw [coeff_firstOrderTerminalBiHahnInnerEuler]
  by_cases hd : d = e
  · subst d
    simp
  · simp [HahnSeries.coeff_single, hd]

/-- Outer rational Hahn Euler derivation, restricted from coefficient-linear to complex-linear. -/
noncomputable def firstOrderTerminalBiHahnOuterEuler :
    Derivation ℂ FirstOrderTerminalBiHahnField FirstOrderTerminalBiHahnField :=
  (hahnDerivationBase
    ((Rat.castHom FirstOrderTerminalBiHahnCoefficientField).toAddMonoidHom)).restrictScalars ℂ

@[simp] theorem firstOrderTerminalBiHahnOuterEuler_apply
    (x : FirstOrderTerminalBiHahnField) :
    firstOrderTerminalBiHahnOuterEuler x =
      hahnGrade
        ((Rat.castHom FirstOrderTerminalBiHahnCoefficientField).toAddMonoidHom) x := rfl

theorem firstOrderTerminalBiHahnInnerEuler_algebraMap
    (c : FirstOrderTerminalBiHahnCoefficientField) :
    firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnOuterCoefficientMap c) =
      firstOrderTerminalBiHahnOuterCoefficientMap
          (firstOrderTerminalBiHahnCoefficientInnerEuler c) := by
  rw [firstOrderTerminalBiHahnOuterCoefficientMap]
  rw [hahnSeriesRat_algebraMap_eq_C, hahnSeriesRat_algebraMap_eq_C]
  ext e
  rw [coeff_firstOrderTerminalBiHahnInnerEuler]
  by_cases he : e = 0
  · subst e
    simp [HahnSeries.C_apply]
  · simp [HahnSeries.C_apply, he]

/-- The outer-zero coefficient of the inner Euler derivative of an outer constant times a power
series is the inner derivative of the transported constant coefficient. -/
theorem coeff_zero_firstOrderTerminalBiHahnInnerEuler_outer_mul_coe
    (c : FirstOrderTerminalCoefficientField)
    (z : PowerSeries FirstOrderTerminalCoefficientField) :
    (firstOrderTerminalBiHahnInnerEuler
      (firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap c *
          algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
            FirstOrderTerminalLaurentField z))).coeff 0 =
      firstOrderTerminalBiHahnCoefficientInnerEuler
        (firstOrderTerminalCoefficientBaseChange (laurentToHahn (k := ℂ))
          (c * PowerSeries.constantCoeff z)) := by
  rw [firstOrderTerminalOuterCoefficientMap_mul_coe,
    coeff_firstOrderTerminalBiHahnInnerEuler,
    coeff_zero_firstOrderTerminalBiHahnEmbedding_coe]
  congr 2
  rw [map_mul, PowerSeries.constantCoeff_C]

/-- Nonzero inner charge of the exact outer constant coefficient forces nonzero inner derivative
of the complete transported outer power series; higher outer terms cannot cancel its zero
coefficient. -/
theorem firstOrderTerminalBiHahnInnerEuler_outer_mul_coe_ne_zero
    (c : FirstOrderTerminalCoefficientField)
    (z : PowerSeries FirstOrderTerminalCoefficientField)
    (hcharge : firstOrderTerminalBiHahnInnerEuler
      (firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap
          (c * PowerSeries.constantCoeff z))) ≠ 0) :
    firstOrderTerminalBiHahnInnerEuler
      (firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap c *
          algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
            FirstOrderTerminalLaurentField z)) ≠ 0 := by
  rw [firstOrderTerminalBiHahnEmbedding_outer_algebraMap,
    firstOrderTerminalBiHahnInnerEuler_algebraMap] at hcharge
  have hcoeff : firstOrderTerminalBiHahnCoefficientInnerEuler
      (firstOrderTerminalCoefficientBaseChange (laurentToHahn (k := ℂ))
        (c * PowerSeries.constantCoeff z)) ≠ 0 :=
    (map_ne_zero firstOrderTerminalBiHahnOuterCoefficientMap).mp hcharge
  intro hzero
  apply hcoeff
  rw [← coeff_zero_firstOrderTerminalBiHahnInnerEuler_outer_mul_coe c z,
    hzero, HahnSeries.coeff_zero]

theorem hahnGrade_laurentToHahn (x : LaurentSeries ℂ) :
    hahnGrade ((Rat.castHom ℂ).toAddMonoidHom)
        (laurentToHahn (k := ℂ) x) =
      laurentToHahn (k := ℂ) (hahnGrade (Int.castAddHom ℂ) x) := by
  ext d
  by_cases hd : ∃ n : ℤ, (n : ℚ) = d
  · obtain ⟨n, rfl⟩ := hd
    rw [coeff_hahnGrade, coeff_laurentToHahn, coeff_laurentToHahn,
      coeff_hahnGrade]
    congr 1
  · rw [coeff_hahnGrade,
      coeff_laurentToHahn_of_not_int _ (fun n hn => hd ⟨n, hn⟩), mul_zero,
      coeff_laurentToHahn_of_not_int _ (fun n hn => hd ⟨n, hn⟩)]

/-- Inner Euler differentiation commutes with the faithful two-level Hahn transport on every inner
Laurent coefficient. -/
theorem firstOrderTerminalBiHahnInnerEuler_inner_algebraMap
    (x : LaurentSeries ℂ) :
    firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnEmbedding
          (firstOrderTerminalOuterCoefficientMap
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x))) =
      firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
            (hahnGrade (Int.castAddHom ℂ) x))) := by
  calc
    firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnEmbedding
          (firstOrderTerminalOuterCoefficientMap
            (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField x))) =
      firstOrderTerminalBiHahnInnerEuler
        (firstOrderTerminalBiHahnOuterCoefficientMap
          (algebraMap FirstOrderTerminalInnerHahnField
            FirstOrderTerminalBiHahnCoefficientField
            (laurentToHahn (k := ℂ) x))) :=
        congrArg firstOrderTerminalBiHahnInnerEuler
          (firstOrderTerminalBiHahnEmbedding_inner_algebraMap x)
    _ = firstOrderTerminalBiHahnOuterCoefficientMap
          (firstOrderTerminalBiHahnCoefficientInnerEuler
            (algebraMap FirstOrderTerminalInnerHahnField
              FirstOrderTerminalBiHahnCoefficientField
              (laurentToHahn (k := ℂ) x))) := by
        rw [firstOrderTerminalBiHahnInnerEuler_algebraMap]
    _ = firstOrderTerminalBiHahnOuterCoefficientMap
          (algebraMap FirstOrderTerminalInnerHahnField
            FirstOrderTerminalBiHahnCoefficientField
            (hahnGrade ((Rat.castHom ℂ).toAddMonoidHom)
              (laurentToHahn (k := ℂ) x))) := by
        rw [firstOrderTerminalBiHahnCoefficientInnerEuler_algebraMap]
    _ = firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
            (hahnGrade (Int.castAddHom ℂ) x))) := by
        rw [hahnGrade_laurentToHahn]
        exact (firstOrderTerminalBiHahnEmbedding_inner_algebraMap
          (hahnGrade (Int.castAddHom ℂ) x)).symm

/-- Exact Wiman input-times-coefficient charge remains nonzero after faithful two-level Hahn
transport and is detected by the inner Euler derivation. -/
theorem firstOrderTerminalBiHahnInnerEuler_charged_ne_zero
    (M a q N : ℕ) (hN : N ≠ 0) (hcharge : a < M + q)
    (z₀ : PowerSeries ℂ) (hz₀ : PowerSeries.constantCoeff z₀ ≠ 0) :
    firstOrderTerminalBiHahnInnerEuler
      (firstOrderTerminalBiHahnEmbedding
        (firstOrderTerminalOuterCoefficientMap
          (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
            (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ) *
              (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
                algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
                  ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀)))))) ≠ 0 := by
  rw [firstOrderTerminalBiHahnInnerEuler_inner_algebraMap]
  apply (map_ne_zero firstOrderTerminalBiHahnEmbedding).mpr
  apply (map_ne_zero firstOrderTerminalOuterCoefficientMap).mpr
  apply (map_ne_zero
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)).mpr
  exact hahnGrade_terminalWimanChargedCoefficient_ne_zero
    M a q N hN hcharge z₀ hz₀

theorem firstOrderTerminalBiHahnOuterEuler_single
    (e : ℚ) (c : FirstOrderTerminalBiHahnCoefficientField) :
    firstOrderTerminalBiHahnOuterEuler (HahnSeries.single e c) =
      HahnSeries.single e ((e : FirstOrderTerminalBiHahnCoefficientField) * c) := by
  ext d
  rw [firstOrderTerminalBiHahnOuterEuler_apply, coeff_hahnGrade]
  by_cases hd : d = e
  · subst d
    simp
  · simp [hd]

end

end GaloisForLFunctions.HTGeometry
