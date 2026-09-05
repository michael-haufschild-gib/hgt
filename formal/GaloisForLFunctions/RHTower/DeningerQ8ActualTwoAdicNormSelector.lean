import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicMonogenic
import GaloisForLFunctions.HTGeometry.HenselDefectRoot
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.IntegralNormUnits
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Norm.Basic

/-!
# Dyadic norm selector for the literal SST quaternion field

For `u = (1 + √5) / 2`, `v = (1 + √41) / 2`, and the literal top radicand
`δ = 2 (u + 2) (35 + 12v)`, the approximation `y = u + 1` satisfies

`y² - (u + δy²) = (2y)² ε`

with `ε` divisible by two.  Hensel--Rychlik therefore produces a square root of
`u + δy²` in every dyadic completion.  The element with coordinates `(a,y)` in the
quadratic algebra `E[ω]/(ω²-δ)` has norm `a²-δy²=u`.  Thus the literal dyadic source
unit is a norm before any epsilon-factor or character formalism is invoked.
-/

namespace RHTower

open scoped NumberField Pointwise ValuativeRel Polynomial WithZero WithZeroMulInt
open IsDedekindDomain
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

local instance deningerQ8ActualTwoAdicNormSelectorLocalInst1 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
noncomputable local instance deningerQ8ActualTwoAdicNormSelectorLocalInst2 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance deningerQ8ActualTwoAdicNormSelectorLocalInst3 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance deningerQ8ActualTwoAdicNormSelectorLocalInst4 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance deningerQ8ActualTwoAdicNormSelectorLocalInst5 : NumberField K2 := NumberField.mk

noncomputable def q8BiquadTwoAdicV : 𝓞 K2 :=
  ⟨q8BiquadV, q8BiquadV_isIntegral⟩

theorem q8BiquadTwoAdicV_sq :
    q8BiquadTwoAdicV ^ 2 = q8BiquadTwoAdicV + 10 := by
  exact Subtype.ext q8BiquadV_sq

noncomputable def q8BiquadTwoAdicRadicand : 𝓞 K2 :=
  2 * (q8BiquadTwoAdicU + 2) * (35 + 12 * q8BiquadTwoAdicV)

/-- The integral-coordinate radicand is literally the defining top SST radicand. -/
theorem q8BiquadTwoAdicRadicand_eq_topRadicand :
    (q8BiquadTwoAdicRadicand : K2) =
      deningerQ8RootNumberNegOneTopRadicand := by
  have hR :
      2 * ((q8BiquadTwoAdicU : K2) + 2) =
        (deningerQ8RootNumberNegOneTopR : K2) := by
    have hucoe : (q8BiquadTwoAdicU : K2) = algebraMap K1 K2 q8BiquadU := rfl
    rw [hucoe]
    change 2 * (algebraMap K1 K2 q8BiquadU + 2) =
      algebraMap K1 K2 deningerQ8RootNumberNegOneTopR
    rw [← map_ofNat (algebraMap K1 K2) 2, ← map_add, ← map_mul]
    congr 1
    unfold q8BiquadU deningerQ8RootNumberNegOneTopR
    field_simp
    ring
  have hS :
      35 + 12 * (q8BiquadTwoAdicV : K2) =
        deningerQ8RootNumberNegOneTopS := by
    have hvcoe : (q8BiquadTwoAdicV : K2) = q8BiquadV := rfl
    rw [hvcoe]
    unfold q8BiquadV deningerQ8RootNumberNegOneTopS
    change 35 + 12 * ((1 + deningerQ8RootNumberNegOneSecondQuadraticRoot) / 2) =
      (41 : K2) + 6 * deningerQ8RootNumberNegOneSecondQuadraticRoot
    have htwo : (2 : K2) ≠ 0 := by norm_num
    field_simp [htwo]
    ring
  unfold q8BiquadTwoAdicRadicand deningerQ8RootNumberNegOneTopRadicand
  change 2 * ((q8BiquadTwoAdicU : K2) + 2) *
      (35 + 12 * (q8BiquadTwoAdicV : K2)) = _
  rw [hR, hS]

theorem q8BiquadTwoAdic_hensel_defect :
    let u := q8BiquadTwoAdicU
    let v := q8BiquadTwoAdicV
    let y := u + 1
    let ε := -2 * (17 + 9 * u + (6 + 3 * u) * v)
    y ^ 2 - (u + q8BiquadTwoAdicRadicand * y ^ 2) = (2 * y) ^ 2 * ε := by
  dsimp
  have hy : (q8BiquadTwoAdicU + 1) ^ 2 = 3 * q8BiquadTwoAdicU + 2 := by
    rw [show (q8BiquadTwoAdicU + 1) ^ 2 =
      q8BiquadTwoAdicU ^ 2 + 2 * q8BiquadTwoAdicU + 1 by ring,
      q8BiquadTwoAdicU_sq]
    ring
  have hu3 : q8BiquadTwoAdicU ^ 3 = 2 * q8BiquadTwoAdicU + 1 := by
    calc
      q8BiquadTwoAdicU ^ 3 = q8BiquadTwoAdicU * q8BiquadTwoAdicU ^ 2 := by ring
      _ = q8BiquadTwoAdicU * (q8BiquadTwoAdicU + 1) := by
        rw [q8BiquadTwoAdicU_sq]
      _ = 2 * q8BiquadTwoAdicU + 1 := by
        rw [mul_add, ← pow_two q8BiquadTwoAdicU, q8BiquadTwoAdicU_sq]
        ring
  rw [hy]
  unfold q8BiquadTwoAdicRadicand
  ring_nf
  rw [hu3, q8BiquadTwoAdicU_sq]
  ring

theorem exists_sq_q8BiquadTwoAdicU_of_map_two_mem
    {S : Type*} [CommRing S] [Nontrivial S]
    (I : Ideal S) [IsAdicComplete I S]
    (f : 𝓞 K2 →+* S) (h2 : f 2 ∈ I) :
    ∃ a : S,
      a ^ 2 = f q8BiquadTwoAdicU +
        f q8BiquadTwoAdicRadicand * (f (q8BiquadTwoAdicU + 1)) ^ 2 := by
  let u := q8BiquadTwoAdicU
  let v := q8BiquadTwoAdicV
  let y := u + 1
  let ε := -2 * (17 + 9 * u + (6 + 3 * u) * v)
  let A : S := f u + f q8BiquadTwoAdicRadicand * (f y) ^ 2
  let F : S[X] := Polynomial.X ^ 2 - Polynomial.C A
  have hε : f ε ∈ I := by
    have hneg : f (-2) ∈ I := by
      simpa using I.neg_mem h2
    dsimp [ε]
    rw [map_mul]
    exact I.mul_mem_right _ hneg
  have hder : Polynomial.eval (f y) (Polynomial.derivative F) = 2 * f y := by
    simp [F, one_add_one_eq_two]
  have hval : Polynomial.eval (f y) F = (2 * f y) ^ 2 * f ε := by
    have hdef := congrArg f q8BiquadTwoAdic_hensel_defect
    simpa [u, v, y, ε, A, F, map_ofNat] using hdef
  obtain ⟨z, _, hroot⟩ :=
    GaloisForLFunctions.HTGeometry.exists_isRoot_of_sq_dvd I hder hval hε
  refine ⟨f y + (2 * f y) * z, ?_⟩
  simpa [F, A, u, y, Polynomial.IsRoot, sub_eq_zero] using hroot

theorem exists_quadraticNorm_q8BiquadTwoAdicU_of_map_two_mem
    {S : Type*} [CommRing S] [Nontrivial S]
    (I : Ideal S) [IsAdicComplete I S]
    (f : 𝓞 K2 →+* S) (h2 : f 2 ∈ I) :
    ∃ w : QuadraticAlgebra S (f q8BiquadTwoAdicRadicand) 0,
      QuadraticAlgebra.norm w = f q8BiquadTwoAdicU := by
  obtain ⟨a, ha⟩ := exists_sq_q8BiquadTwoAdicU_of_map_two_mem I f h2
  let w : QuadraticAlgebra S (f q8BiquadTwoAdicRadicand) 0 :=
    ⟨a, f (q8BiquadTwoAdicU + 1)⟩
  refine ⟨w, ?_⟩
  rw [QuadraticAlgebra.norm_def]
  dsimp [w]
  rw [show a * a = a ^ 2 by ring, ha]
  ring

/-- The coordinate norm on a quadratic algebra is its determinant-defined algebra norm. -/
theorem quadraticAlgebra_algebraNorm_eq_norm
    {S : Type*} [CommRing S] (a b : S) (w : QuadraticAlgebra S a b) :
    Algebra.norm S w = QuadraticAlgebra.norm w := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis a b), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply]
  rw [QuadraticAlgebra.norm_def]
  simp [QuadraticAlgebra.basis]
  ring

/-- A quadratic coordinate algebra with relation `ω² = a` is the corresponding root algebra. -/
noncomputable def quadraticAlgebraAdjoinRootEquiv
    {S : Type*} [CommRing S] (a : S) :
    QuadraticAlgebra S a 0 ≃ₐ[S] AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a) := by
  let f : QuadraticAlgebra S a 0 →ₐ[S]
      AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a) :=
    QuadraticAlgebra.lift
      ⟨AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C a), by
        have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C a)
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_C] at h
        have hsq : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C a) ^ 2 =
            algebraMap S (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a)) a := by
          simpa using sub_eq_zero.mp h
        simpa only [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, pow_two]
          using hsq⟩
  let g : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a) →ₐ[S]
      QuadraticAlgebra S a 0 :=
    AdjoinRoot.liftAlgHom (Polynomial.X ^ 2 - Polynomial.C a)
      (Algebra.ofId S (QuadraticAlgebra S a 0)) QuadraticAlgebra.omega (by
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        change QuadraticAlgebra.omega ^ 2 -
          algebraMap S (QuadraticAlgebra S a 0) a = 0
        rw [show QuadraticAlgebra.omega ^ 2 =
          algebraMap S (QuadraticAlgebra S a 0) a by
            rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
            simpa using (Algebra.algebraMap_eq_smul_one a).symm]
        ring)
  exact AlgEquiv.ofAlgHom f g
    (by
      apply AdjoinRoot.algHom_ext
      simp [f, g])
    (by
      apply QuadraticAlgebra.algHom_ext
      simp [f, g])

section CompletedNorm

variable (place : NumberField.FinitePlace K2)

local notation "E2" =>
  GaloisForLFunctions.HTGeometry.ABHN.completion K2
    (GaloisForLFunctions.HTGeometry.ABHN.NumberFieldPlace.finite place)

local notation "K3" => deningerQ8RootNumberNegOneTopField

/-- Canonical completed scalar extension of the actual top SST field, in the literal
quadratic coordinates used by the Hensel norm witness. -/
noncomputable def q8BiquadCompletedTopScalarExtensionEquiv :
    TensorProduct K2 E2 K3 ≃ₐ[E2]
      QuadraticAlgebra E2
        ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2)) 0 :=
  (GaloisForLFunctions.HTGeometry.ABHN.adjoinRootScalarExtensionEquivOfMapEq
      K2 E2 deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (Polynomial.X ^ 2 - Polynomial.C
        ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2))) (by
          simp [deningerQ8RootNumberNegOneThirdQuadraticPolynomial,
            q8BiquadTwoAdicRadicand_eq_topRadicand])).trans
    (quadraticAlgebraAdjoinRootEquiv
      ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2))).symm

theorem exists_q8BiquadTwoAdicU_completedQuadraticNorm
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    ∃ w : QuadraticAlgebra E2
        ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2)) 0,
      QuadraticAlgebra.norm w = (algebraMap K2 E2) (q8BiquadTwoAdicU : K2) := by
  let g : 𝓞 K2 →+* E2 :=
    (algebraMap K2 E2).comp (algebraMap (𝓞 K2) K2)
  letI : (Valued.v : Valuation E2 ℤᵐ⁰).Compatible :=
    GaloisForLFunctions.HTGeometry.ABHN.numberFieldAdicCompletionValuationCompatible K2 place
  let f : 𝓞 K2 →+* (ValuativeRel.valuation E2).integer :=
      g.codRestrict (ValuativeRel.valuation E2).integer (fun x => by
    rw [Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation E2).vle_one_iff,
      (Valued.v : Valuation E2 ℤᵐ⁰).vle_one_iff]
    change Valued.v ((algebraMap K2 E2) (x : K2)) ≤ 1
    change Valued.v ((x : K2) : place.maximalIdeal.adicCompletion K2) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact place.maximalIdeal.valuation_le_one (K := K2) x)
  haveI : IsAdicComplete
      (IsLocalRing.maximalIdeal ((ValuativeRel.valuation E2).integer))
      ((ValuativeRel.valuation E2).integer) := by
    simpa [GaloisForLFunctions.HTGeometry.ABHN.completion] using
      GaloisForLFunctions.HTGeometry.ABHN.numberFieldFinitePlaceCompletion_isAdicComplete K2 place
  have hmaptwo : f 2 ∈
      IsLocalRing.maximalIdeal ((ValuativeRel.valuation E2).integer) := by
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (f 2)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change (ValuativeRel.valuation E2) (f 2 : E2) < 1
    rw [← (ValuativeRel.valuation E2).vlt_one_iff,
      (Valued.v : Valuation E2 ℤᵐ⁰).vlt_one_iff]
    change Valued.v ((algebraMap K2 E2) (2 : K2)) < 1
    change Valued.v ((2 : K2) : place.maximalIdeal.adicCompletion K2) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (place.maximalIdeal.valuation_lt_one_iff_mem (K := K2) 2).2 hplace
  obtain ⟨a, ha⟩ := exists_sq_q8BiquadTwoAdicU_of_map_two_mem
    (IsLocalRing.maximalIdeal ((ValuativeRel.valuation E2).integer)) f hmaptwo
  have haE := congrArg (fun x : (ValuativeRel.valuation E2).integer => (x : E2)) ha
  have haE' : (a : E2) ^ 2 =
      (algebraMap K2 E2) (q8BiquadTwoAdicU : K2) +
        (algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2) *
          ((algebraMap K2 E2) ((q8BiquadTwoAdicU + 1 : 𝓞 K2) : K2)) ^ 2 := by
    simpa [f, g] using haE
  let w : QuadraticAlgebra E2
      ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2)) 0 :=
    ⟨(a : E2), (algebraMap K2 E2) ((q8BiquadTwoAdicU + 1 : 𝓞 K2) : K2)⟩
  refine ⟨w, ?_⟩
  rw [QuadraticAlgebra.norm_def]
  dsimp [w]
  rw [show (a : E2) * a = (a : E2) ^ 2 by ring, haE']
  ring

/-- The dyadic source unit is represented by the actual determinant norm of the literal
quadratic algebra over the completed biquadratic field. -/
theorem exists_q8BiquadTwoAdicU_completedAlgebraNorm
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    ∃ w : QuadraticAlgebra E2
        ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2)) 0,
      Algebra.norm E2 w = (algebraMap K2 E2) (q8BiquadTwoAdicU : K2) := by
  obtain ⟨w, hw⟩ := exists_q8BiquadTwoAdicU_completedQuadraticNorm place hplace
  refine ⟨w, ?_⟩
  rw [quadraticAlgebra_algebraNorm_eq_norm]
  exact hw

/-- The dyadic source unit is an algebra norm from the canonical completed scalar extension
of the actual top SST number field. -/
theorem exists_q8BiquadTwoAdicU_completedTopScalarExtensionNorm
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    ∃ x : TensorProduct K2 E2 K3,
      Algebra.norm E2 x = (algebraMap K2 E2) (q8BiquadTwoAdicU : K2) := by
  obtain ⟨w, hw⟩ := exists_q8BiquadTwoAdicU_completedAlgebraNorm place hplace
  let e := q8BiquadCompletedTopScalarExtensionEquiv place
  refine ⟨e.symm w, ?_⟩
  have he := Algebra.norm_eq_of_algEquiv e (e.symm w)
  rw [e.apply_symm_apply] at he
  exact he.symm.trans hw

/-- The selected dyadic unit in the completed biquadratic field.  Its
inverse is literal: `u⁻¹ = u - 1`. -/
noncomputable def q8BiquadTwoAdicUCompletionUnit : E2ˣ where
  val := algebraMap K2 E2 (q8BiquadTwoAdicU : K2)
  inv := algebraMap K2 E2 ((q8BiquadTwoAdicU : K2) - 1)
  val_inv := by
    rw [← map_mul]
    have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
    change (q8BiquadTwoAdicU : K2) ^ 2 = (q8BiquadTwoAdicU : K2) + 1 at hu
    rw [mul_sub, mul_one, ← pow_two, hu]
    simp
  inv_val := by
    rw [← map_mul]
    have hu := congrArg (fun x : 𝓞 K2 => (x : K2)) q8BiquadTwoAdicU_sq
    change (q8BiquadTwoAdicU : K2) ^ 2 = (q8BiquadTwoAdicU : K2) + 1 at hu
    rw [sub_mul, one_mul, ← pow_two, hu]
    simp

/-- Unit-valued strengthening of the completed top-field norm witness.
This is the exact form consumed by genuine finite-place local reciprocity. -/
theorem exists_q8BiquadTwoAdicU_completedTopScalarExtensionUnitNorm
    (hplace : (2 : 𝓞 K2) ∈ place.maximalIdeal.asIdeal) :
    ∃ x : (TensorProduct K2 E2 K3)ˣ,
      Units.map (Algebra.norm E2) x =
        q8BiquadTwoAdicUCompletionUnit place := by
  obtain ⟨w, hw⟩ := exists_q8BiquadTwoAdicU_completedAlgebraNorm place hplace
  let uE := q8BiquadTwoAdicUCompletionUnit place
  have hwu : IsUnit w := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    rw [← quadraticAlgebra_algebraNorm_eq_norm, hw]
    exact uE.isUnit
  let wu : (QuadraticAlgebra E2
      ((algebraMap K2 E2) (q8BiquadTwoAdicRadicand : K2)) 0)ˣ := hwu.unit
  let e := q8BiquadCompletedTopScalarExtensionEquiv place
  let x : (TensorProduct K2 E2 K3)ˣ := Units.map e.symm.toMonoidHom wu
  refine ⟨x, ?_⟩
  apply Units.ext
  change Algebra.norm E2 (e.symm w) = algebraMap K2 E2 (q8BiquadTwoAdicU : K2)
  have he := Algebra.norm_eq_of_algEquiv e (e.symm w)
  rw [e.apply_symm_apply] at he
  exact he.symm.trans hw

end CompletedNorm

end
end RHTower
