import GaloisForLFunctions.RHTower.XiTransverseShiftPrimeDefectValueReflection
import GaloisForLFunctions.RHTower.XiShiftPrimeReflectionCocycle

/-!
# Even-shift telescope for the actual completed Xi prime defect

The transverse source at shift `2m` is the finite sum of Dirichlet translates of the shift-two
filtered von Mangoldt source.  The existing shift-two value reflection identifies every summand
with the rationally corrected logarithmic-derivative defect of the actual completed `xi`.
Telescoping those values gives the exact correction for the direct `2m` logarithmic difference.

Consequently the source carrier is not merely analogous to an Xi expression: its upper-end germ
is the actual completed-Xi even-shift defect.  The arbitrary even-shift family therefore inherits
the exact pointed collision matroid, independence interface, and rank formula.
-/

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiEvenShiftUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiEvenShiftUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiEvenShiftUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiEvenShiftUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiEvenShiftCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiEvenShiftCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

/-! ## Source and value telescopes -/

/-- The shift-`2m` source is the sum of the first `m` even Dirichlet translates of the
shift-two source. -/
theorem xiTransverseShiftFiniteAbscissaSource_even_telescope (m : ℕ) :
    xiTransverseShiftFiniteAbscissaSource (2 * m) =
      ∑ j ∈ Finset.range m,
        finiteAbscissaDirichletShift ((2 * j : ℕ) : ℂ)
          (xiTransverseShiftFiniteAbscissaSource 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, xiTransverseShiftFiniteAbscissaSource_add, ih,
        Finset.sum_range_succ]

/-- The transverse shift-two source is exactly the previously constructed filtered von Mangoldt
finite-abscissa source. -/
theorem xiTransverseShiftFiniteAbscissaSource_two_eq_filteredVonMangoldt :
    xiTransverseShiftFiniteAbscissaSource 2 =
      filteredVonMangoldtFiniteAbscissaSource := by
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  change (ArithmeticFunction.vonMangoldt n : ℂ) -
      cpowWeight (2 : ℂ) n * (ArithmeticFunction.vonMangoldt n : ℂ) =
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      (1 - (n : ℂ) ^ (-(2 : ℂ)))
  simp only [cpowWeight]
  ring

/-- Filtered-von-Mangoldt form of the even source telescope. -/
theorem xiTransverseShiftFiniteAbscissaSource_even_telescope_filteredVonMangoldt
    (m : ℕ) :
    xiTransverseShiftFiniteAbscissaSource (2 * m) =
      ∑ j ∈ Finset.range m,
        finiteAbscissaDirichletShift ((2 * j : ℕ) : ℂ)
          filteredVonMangoldtFiniteAbscissaSource := by
  rw [xiTransverseShiftFiniteAbscissaSource_even_telescope]
  simp only [xiTransverseShiftFiniteAbscissaSource_two_eq_filteredVonMangoldt]

/-- The rational archimedean/boundary correction accumulated along the first `m` shift-two
steps. -/
def xiEvenShiftPrimeCorrection (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m,
    (1 / (s + (2 * j : ℕ) + 2) + 1 / (s + (2 * j : ℕ) + 1) -
      1 / (s + (2 * j : ℕ) - 1))

/-- The directly corrected shift-`2m` defect of the actual completed logarithmic derivative. -/
def xiEvenShiftPrimeDefect (m : ℕ) (s : ℂ) : ℂ :=
  logDeriv xi (s + (2 * m : ℕ)) - logDeriv xi s -
    xiEvenShiftPrimeCorrection m s

/-- **Completed-Xi value telescope.** The direct corrected shift-`2m` defect is exactly the sum
of the translated corrected shift-two defects. -/
theorem xiEvenShiftPrimeDefect_telescope (m : ℕ) (s : ℂ) :
    xiEvenShiftPrimeDefect m s =
      ∑ j ∈ Finset.range m, xiShiftTwoPrimeDefect (s + (2 * j : ℕ)) := by
  have hraw :
      (∑ j ∈ Finset.range m,
        (logDeriv xi (s + (2 * j : ℕ) + 2) -
          logDeriv xi (s + (2 * j : ℕ)))) =
        logDeriv xi (s + (2 * m : ℕ)) - logDeriv xi s := by
    let f : ℕ → ℂ := fun j => logDeriv xi (s + (2 * j : ℕ))
    calc
      (∑ j ∈ Finset.range m,
          (logDeriv xi (s + (2 * j : ℕ) + 2) -
            logDeriv xi (s + (2 * j : ℕ)))) =
          ∑ j ∈ Finset.range m, (f (j + 1) - f j) := by
            apply Finset.sum_congr rfl
            intro j _
            change (logDeriv xi (s + (2 * j : ℕ) + 2) -
                logDeriv xi (s + (2 * j : ℕ))) =
              logDeriv xi (s + (2 * (j + 1) : ℕ)) -
                logDeriv xi (s + (2 * j : ℕ))
            rw [show s + (2 * j : ℕ) + 2 =
                s + (2 * (j + 1) : ℕ) by
              push_cast
              ring]
      _ = f m - f 0 := Finset.sum_range_sub f m
      _ = logDeriv xi (s + (2 * m : ℕ)) - logDeriv xi s := by
        simp [f]
  rw [xiEvenShiftPrimeDefect, xiEvenShiftPrimeCorrection]
  calc
    logDeriv xi (s + (2 * m : ℕ)) - logDeriv xi s -
          ∑ j ∈ Finset.range m,
            (1 / (s + (2 * j : ℕ) + 2) + 1 / (s + (2 * j : ℕ) + 1) -
              1 / (s + (2 * j : ℕ) - 1)) =
        (∑ j ∈ Finset.range m,
          (logDeriv xi (s + (2 * j : ℕ) + 2) -
            logDeriv xi (s + (2 * j : ℕ)))) -
          ∑ j ∈ Finset.range m,
            (1 / (s + (2 * j : ℕ) + 2) + 1 / (s + (2 * j : ℕ) + 1) -
              1 / (s + (2 * j : ℕ) - 1)) := by rw [hraw]
    _ = ∑ j ∈ Finset.range m,
        ((logDeriv xi (s + (2 * j : ℕ) + 2) -
            logDeriv xi (s + (2 * j : ℕ))) -
          (1 / (s + (2 * j : ℕ) + 2) + 1 / (s + (2 * j : ℕ) + 1) -
            1 / (s + (2 * j : ℕ) - 1))) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ j ∈ Finset.range m, xiShiftTwoPrimeDefect (s + (2 * j : ℕ)) := by
          apply Finset.sum_congr rfl
          intro j _
          rfl

/-- Upper-end germ of the directly corrected actual completed-Xi shift-`2m` defect. -/
def xiEvenShiftPrimeDefectUpperEndGerm (m : ℕ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ => xiEvenShiftPrimeDefect m (-Complex.I * z)) :
    Germ upperEndFilter ℂ)

private theorem xiLogDerivShiftTwoPrimeDefectUpperEndGerm_eq_coe :
    xiLogDerivShiftTwoPrimeDefectUpperEndGerm =
      ((fun z : ℂ => xiShiftTwoPrimeDefect (-Complex.I * z)) :
        Germ upperEndFilter ℂ) := by
  rfl

/-- The completed-Xi even defect germ is the sum of upper-end translates of the actual shift-two
defect germ. -/
theorem xiEvenShiftPrimeDefectUpperEndGerm_telescope (m : ℕ) :
    xiEvenShiftPrimeDefectUpperEndGerm m =
      ∑ j ∈ Finset.range m,
        upperEndTranslateGerm (Complex.I * ((2 * j : ℕ) : ℂ))
          xiLogDerivShiftTwoPrimeDefectUpperEndGerm := by
  rw [xiLogDerivShiftTwoPrimeDefectUpperEndGerm_eq_coe]
  simp_rw [upperEndTranslateGerm_coe]
  rw [← Germ.coe_sum]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    simp only [Finset.sum_apply]
    change xiEvenShiftPrimeDefect m (-Complex.I * z) =
      ∑ j ∈ Finset.range m,
        xiShiftTwoPrimeDefect (-Complex.I * (z +
          Complex.I * ((2 * j : ℕ) : ℂ)))
    rw [xiEvenShiftPrimeDefect_telescope]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    have hI : -Complex.I * Complex.I = (1 : ℂ) := by
      rw [neg_mul, Complex.I_mul_I]
      norm_num
    calc
      -Complex.I * z + 2 * (j : ℂ) =
          -Complex.I * z + (-Complex.I * Complex.I) * (2 * (j : ℂ)) := by
            rw [hI, one_mul]
      _ = -Complex.I * (z + Complex.I * (2 * (j : ℂ))) := by ring

/-- **Actual completed-Xi even-shift reflection.** The analytic source carrier at shift `2m` is
exactly the direct rationally corrected shift-`2m` defect of the actual completed logarithmic
derivative, as an upper-end germ. -/
theorem xiTransverseEvenShiftUpperEndGerm_eq_xiEvenShiftPrimeDefect (m : ℕ) :
    finiteAbscissaLSeriesToUpperEndGerm
        (xiTransverseShiftFiniteAbscissaSource (2 * m)) =
      xiEvenShiftPrimeDefectUpperEndGerm m := by
  rw [xiTransverseShiftFiniteAbscissaSource_even_telescope_filteredVonMangoldt,
    map_sum, xiEvenShiftPrimeDefectUpperEndGerm_telescope]
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteAbscissaLSeriesToUpperEndGerm_dirichletShift]
  congr 1
  change filteredVonMangoldtUpperEndGerm =
    xiLogDerivShiftTwoPrimeDefectUpperEndGerm
  exact filteredVonMangoldtUpperEndGerm_eq_xiLogDerivShiftTwoPrimeDefect

/-! ## Exact matroid of the actual even-shift family -/

/-- Meromorphic carrier of the actual corrected completed-Xi shift-`2m` defect. Its source germ
is identified with the completed-Xi value expression above. -/
def xiEvenShiftPrimeDefectUpperEndCarrier (m : ℕ) : upperEndMeroField :=
  xiTransverseShiftUpperEndCarrier (2 * m)

/-- **Actual even-shift collision law.** For every indexed family of even completed-Xi defects,
zero grades are loops, repeated grades are parallel, and distinct positive grades are the only
differential directions. -/
theorem xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision
    {A : Type*} (grade : A → ℕ) :
    differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) =
      affinePointedCollisionMatroid grade 0 := by
  rw [show (fun a => xiEvenShiftPrimeDefectUpperEndCarrier (grade a)) =
      (fun a => xiTransverseShiftUpperEndCarrier (2 * grade a)) by
    funext a
    rfl]
  rw [xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision]
  apply Matroid.ext_indep
  · simp
  · intro I _
    rw [affinePointedCollisionMatroid_indep_iff,
      affinePointedCollisionMatroid_indep_iff]
    constructor
    · rintro ⟨hinj, hnonzero⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact hinj hi hj (congrArg (fun n => 2 * n) hij)
      · intro i hi hzero
        exact hnonzero i hi (by simp [hzero])
    · rintro ⟨hinj, hnonzero⟩
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact hinj hi hj (Nat.eq_of_mul_eq_mul_left (by norm_num) hij)
      · intro i hi
        exact mul_ne_zero (by norm_num) (hnonzero i hi)

/-- Prop interface for the actual even-shift family. -/
theorem xiEvenShiftPrimeDefectUpperEndCarrier_differentialIndependent_iff
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    DifferentialIndependent upperEndRationalCoordinateField
        (fun i : I => xiEvenShiftPrimeDefectUpperEndCarrier (grade i)) ↔
      Set.InjOn grade I ∧ ∀ i ∈ I, grade i ≠ 0 := by
  let x := fun a => xiEvenShiftPrimeDefectUpperEndCarrier (grade a)
  constructor
  · intro hI
    have hmatroid : (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField) x).Indep I :=
      (differentialFamilyMatroid_indep_iff x I).mpr hI
    rw [xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff] at hmatroid
    exact hmatroid
  · intro hI
    apply (differentialFamilyMatroid_indep_iff x I).mp
    rw [xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision,
      affinePointedCollisionMatroid_indep_iff]
    exact hI

/-- Exact differential rank of every actual even-shift completed-Xi packet. -/
theorem xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eRk
    {A : Type*} (grade : A → ℕ) (I : Set A) :
    (differentialFamilyMatroid
        (F := upperEndRationalCoordinateField)
        (fun a => xiEvenShiftPrimeDefectUpperEndCarrier (grade a))).eRk I =
      ((grade '' I) ∩ {m | m ≠ 0}).encard := by
  rw [xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision,
    affinePointedCollisionMatroid_eRk]

end

end RHTower
