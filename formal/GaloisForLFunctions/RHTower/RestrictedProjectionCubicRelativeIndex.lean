import GaloisForLFunctions.RHTower.RestrictedProjectionCubicTrace
import GaloisForLFunctions.HTGeometry.SignedGreedyEigenspaceMultiplicity
import GaloisForLFunctions.HTGeometry.LidskiiPowerTrace
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictedProjectionComplement (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  1 - R - P

omit [CompleteSpace H] in
theorem restrictedProjectionDisplacement_anticommutes_complement
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P) :
    restrictedProjectionDisplacement R P * restrictedProjectionComplement R P +
      restrictedProjectionComplement R P * restrictedProjectionDisplacement R P = 0 := by
  simpa [restrictedProjectionDisplacement, restrictedProjectionComplement] using
    (HTGeometry.twoProjection_difference_anticommutes_complement hR hP)

omit [CompleteSpace H] in
theorem restrictedProjectionDisplacement_sq_add_complement_sq
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P) :
    restrictedProjectionDisplacement R P * restrictedProjectionDisplacement R P +
      restrictedProjectionComplement R P * restrictedProjectionComplement R P = 1 := by
  simpa [restrictedProjectionDisplacement, restrictedProjectionComplement] using
    (HTGeometry.twoProjection_difference_sq_add_complement_sq hR hP)

omit [CompleteSpace H] in
theorem restrictedProjectionComplement_sq_apply_eigenvector
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (c : ℝ) {x : H}
    (hx : restrictedProjectionDisplacement R P x = (c : ℂ) • x) :
    restrictedProjectionComplement R P (restrictedProjectionComplement R P x) =
      ((1 - c ^ 2 : ℝ) : ℂ) • x := by
  have hsq := congrArg (fun T : H →L[ℂ] H => T x)
    (restrictedProjectionDisplacement_sq_add_complement_sq R P hR hP)
  change restrictedProjectionDisplacement R P (restrictedProjectionDisplacement R P x) +
      restrictedProjectionComplement R P (restrictedProjectionComplement R P x) = x at hsq
  rw [hx, map_smul, hx, smul_smul] at hsq
  have hc2 : (c : ℂ) * (c : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc2] at hsq
  have hsub : restrictedProjectionComplement R P (restrictedProjectionComplement R P x) =
      x - ((c ^ 2 : ℝ) : ℂ) • x := eq_sub_of_add_eq' hsq
  calc
    restrictedProjectionComplement R P (restrictedProjectionComplement R P x) =
        x - ((c ^ 2 : ℝ) : ℂ) • x := hsub
    _ = ((1 - c ^ 2 : ℝ) : ℂ) • x := by
      push_cast
      module

def restrictedProjectionComplementEigenspaceMap
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (c : ℝ) :
    Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ) →ₗ[ℂ]
      Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) ((-c : ℝ) : ℂ) where
  toFun x := ⟨restrictedProjectionComplement R P x, by
    rw [Module.End.mem_eigenspace_iff]
    have hanti := congrArg (fun T : H →L[ℂ] H => T x.1)
      (restrictedProjectionDisplacement_anticommutes_complement R P hR hP)
    change restrictedProjectionDisplacement R P (restrictedProjectionComplement R P x.1) +
      restrictedProjectionComplement R P (restrictedProjectionDisplacement R P x.1) = 0 at hanti
    have hx := Module.End.mem_eigenspace_iff.mp x.2
    change restrictedProjectionDisplacement R P x.1 = (c : ℂ) • x.1 at hx
    rw [hx, map_smul] at hanti
    calc
      restrictedProjectionDisplacement R P (restrictedProjectionComplement R P x.1) =
          -((c : ℂ) • restrictedProjectionComplement R P x.1) :=
        eq_neg_of_add_eq_zero_left hanti
      _ = ((-c : ℝ) : ℂ) • restrictedProjectionComplement R P x.1 := by
        push_cast
        module⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul _ _ _

omit [CompleteSpace H] in
theorem restrictedProjectionComplementEigenspaceMap_bijective
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    Function.Bijective (restrictedProjectionComplementEigenspaceMap R P hR hP c) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hCx : restrictedProjectionComplement R P x.1 =
        restrictedProjectionComplement R P y.1 := congrArg Subtype.val hxy
    have hCC := congrArg (restrictedProjectionComplement R P) hCx
    rw [restrictedProjectionComplement_sq_apply_eigenvector R P hR hP c
        (Module.End.mem_eigenspace_iff.mp x.2),
      restrictedProjectionComplement_sq_apply_eigenvector R P hR hP c
        (Module.End.mem_eigenspace_iff.mp y.2)] at hCC
    have hscaled := congrArg (fun z : H => (((1 - c ^ 2 : ℝ) : ℂ))⁻¹ • z) hCC
    have hinv : (((1 - c ^ 2 : ℝ) : ℂ))⁻¹ * ((1 - c ^ 2 : ℝ) : ℂ) = 1 :=
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc)
    rw [smul_smul, smul_smul, hinv, one_smul, one_smul] at hscaled
    exact hscaled
  · intro y
    let d : ℂ := ((1 - c ^ 2 : ℝ) : ℂ)
    have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hCyMem : restrictedProjectionComplement R P y.1 ∈
        Module.End.eigenspace
          (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ) := by
      let z := (restrictedProjectionComplementEigenspaceMap R P hR hP (-c)) y
      have hzval : (z : H) = restrictedProjectionComplement R P y.1 := rfl
      rw [← hzval]
      simpa using z.2
    let x : Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ) :=
      ⟨d⁻¹ • restrictedProjectionComplement R P y.1,
        (Module.End.eigenspace
          (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ)).smul_mem
            d⁻¹ hCyMem⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change restrictedProjectionComplement R P (d⁻¹ •
      restrictedProjectionComplement R P y.1) = y.1
    rw [map_smul,
      restrictedProjectionComplement_sq_apply_eigenvector R P hR hP (-c)
        (Module.End.mem_eigenspace_iff.mp y.2)]
    rw [show 1 - (-c) ^ 2 = 1 - c ^ 2 by ring]
    change d⁻¹ • d • y.1 = y.1
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul]

omit [CompleteSpace H] in
noncomputable def restrictedProjectionEigenspaceNegEquiv
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ) ≃ₗ[ℂ]
      Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) ((-c : ℝ) : ℂ) :=
  LinearEquiv.ofBijective (restrictedProjectionComplementEigenspaceMap R P hR hP c)
    (restrictedProjectionComplementEigenspaceMap_bijective R P hR hP c hc)

omit [CompleteSpace H] in
theorem finrank_restrictedProjectionDisplacement_eigenspace_eq_neg
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (c : ℂ)) =
      Module.finrank ℂ (Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) ((-c : ℝ) : ℂ)) :=
  (restrictedProjectionEigenspaceNegEquiv R P hR hP c hc).finrank_eq

theorem ncard_restrictedProjectionDisplacement_sgVal_fiber_eq_neg
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt)
    (c : ℝ) (hc0 : c ≠ 0) (hc : 1 - c ^ 2 ≠ 0) :
    Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
        (restrictedProjectionDisplacement R P) n = c} =
      Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
        (restrictedProjectionDisplacement R P) n = -c} := by
  let D := restrictedProjectionDisplacement R P
  have hcpt : IsCompactOperator D := hDelta.isCompactOperator
  have hDadj : ContinuousLinearMap.adjoint D = D :=
    adjoint_restrictedProjectionDisplacement R P hRadj hPadj
  have hsym : D.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hDadj
  rw [← ContinuousLinearMap.finrank_eigenspace_eq_ncard_sgVal_fiber hcpt hsym hc0,
    ← ContinuousLinearMap.finrank_eigenspace_eq_ncard_sgVal_fiber hcpt hsym
      (neg_ne_zero.mpr hc0)]
  simpa [D] using
    finrank_restrictedProjectionDisplacement_eigenspace_eq_neg R P hR hP c hc

/-- Nonzero, non-endpoint values in the signed-greedy spectrum. -/
def RestrictedProjectionGenericSpectralValue :=
  {c : ℝ // c ≠ 0 ∧ 1 - c ^ 2 ≠ 0}

/-- Signed-greedy indices belonging to the paired generic spectrum. -/
def restrictedProjectionGenericSpectralIndex (R P : H →L[ℂ] H) :=
  {n : ℕ //
    ContinuousLinearMap.sgVal (restrictedProjectionDisplacement R P) n ≠ 0 ∧
    1 - ContinuousLinearMap.sgVal (restrictedProjectionDisplacement R P) n ^ 2 ≠ 0}

/-- Generic signed spectral value attached to a generic index. -/
def restrictedProjectionGenericSpectralValue (R P : H →L[ℂ] H)
    (n : restrictedProjectionGenericSpectralIndex R P) :
    RestrictedProjectionGenericSpectralValue :=
  ⟨ContinuousLinearMap.sgVal (restrictedProjectionDisplacement R P) n.1, n.2⟩

/-- Negation preserves the nonzero, non-endpoint spectral-value type. -/
def restrictedProjectionGenericSpectralValueNeg :
    Equiv.Perm RestrictedProjectionGenericSpectralValue where
  toFun c := ⟨-c.1, neg_ne_zero.mpr c.2.1, by
    simpa [sq] using c.2.2⟩
  invFun c := ⟨-c.1, neg_ne_zero.mpr c.2.1, by
    simpa [sq] using c.2.2⟩
  left_inv c := by
    apply Subtype.ext
    simp
  right_inv c := by
    apply Subtype.ext
    simp

/-- A generic-value fiber is exactly the corresponding ordinary `sgVal` fiber. -/
def restrictedProjectionGenericFiberEquiv
    (R P : H →L[ℂ] H) (c : RestrictedProjectionGenericSpectralValue) :
    {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n = c} ≃
      {n : ℕ // ContinuousLinearMap.sgVal
        (restrictedProjectionDisplacement R P) n = c.1} where
  toFun n := ⟨n.1.1, congrArg Subtype.val n.2⟩
  invFun n := ⟨⟨n.1, by rw [n.2]; exact c.2⟩, by
    apply Subtype.ext
    exact n.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def restrictedProjectionGenericNegFiberEquiv
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt)
    (c : RestrictedProjectionGenericSpectralValue) :
    {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n = c} ≃
    {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n =
          restrictedProjectionGenericSpectralValueNeg c} := by
  have hsym : (restrictedProjectionDisplacement R P).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_restrictedProjectionDisplacement R P hRadj hPadj)
  have hposfin : Set.Finite {n : ℕ | ContinuousLinearMap.sgVal
      (restrictedProjectionDisplacement R P) n = c.1} :=
    ContinuousLinearMap.finite_sgVal_fiber hDelta.isCompactOperator hsym c.2.1
  have hnegfin : Set.Finite {n : ℕ | ContinuousLinearMap.sgVal
      (restrictedProjectionDisplacement R P) n =
        (restrictedProjectionGenericSpectralValueNeg c).1} := by
    simpa [restrictedProjectionGenericSpectralValueNeg] using
      (ContinuousLinearMap.finite_sgVal_fiber hDelta.isCompactOperator hsym
        (neg_ne_zero.mpr c.2.1))
  letI : Fintype {n : ℕ // ContinuousLinearMap.sgVal
      (restrictedProjectionDisplacement R P) n = c.1} :=
    Fintype.ofFinset hposfin.toFinset (fun n => by
      rw [Set.Finite.mem_toFinset]
      rfl)
  letI : Fintype {n : ℕ // ContinuousLinearMap.sgVal
      (restrictedProjectionDisplacement R P) n =
        (restrictedProjectionGenericSpectralValueNeg c).1} :=
    Fintype.ofFinset hnegfin.toFinset (fun n => by
      rw [Set.Finite.mem_toFinset]
      rfl)
  letI : Fintype {n : restrictedProjectionGenericSpectralIndex R P //
      restrictedProjectionGenericSpectralValue R P n = c} :=
    Fintype.ofEquiv _ (restrictedProjectionGenericFiberEquiv R P c).symm
  letI : Fintype {n : restrictedProjectionGenericSpectralIndex R P //
      restrictedProjectionGenericSpectralValue R P n =
        restrictedProjectionGenericSpectralValueNeg c} :=
    Fintype.ofEquiv _
      (restrictedProjectionGenericFiberEquiv R P
        (restrictedProjectionGenericSpectralValueNeg c)).symm
  apply Fintype.equivOfCardEq
  calc
    Fintype.card {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n = c} =
        Fintype.card {n : ℕ // ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n = c.1} :=
      Fintype.card_congr (restrictedProjectionGenericFiberEquiv R P c)
    _ = Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n = c.1} := by
      rw [Set.ncard_eq_toFinset_card _ hposfin]
      exact Fintype.card_ofFinset hposfin.toFinset (fun n => by
        rw [Set.Finite.mem_toFinset]
        rfl)
    _ = Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n =
            (restrictedProjectionGenericSpectralValueNeg c).1} := by
      simpa [restrictedProjectionGenericSpectralValueNeg] using
        (ncard_restrictedProjectionDisplacement_sgVal_fiber_eq_neg
          R P hR hP hRadj hPadj hDelta c.1 c.2.1 c.2.2)
    _ = Fintype.card {n : ℕ // ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n =
            (restrictedProjectionGenericSpectralValueNeg c).1} := by
      rw [Set.ncard_eq_toFinset_card _ hnegfin]
      exact (Fintype.card_ofFinset hnegfin.toFinset (fun n => by
        rw [Set.Finite.mem_toFinset]
        rfl)).symm
    _ = Fintype.card {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n =
          restrictedProjectionGenericSpectralValueNeg c} :=
      (Fintype.card_congr (restrictedProjectionGenericFiberEquiv R P
        (restrictedProjectionGenericSpectralValueNeg c))).symm

/-- Global pairing of all non-endpoint signed-greedy indices. -/
noncomputable def restrictedProjectionGenericSpectralNegEquiv
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    Equiv.Perm (restrictedProjectionGenericSpectralIndex R P) :=
  (Equiv.sigmaFiberEquiv (restrictedProjectionGenericSpectralValue R P)).symm |>.trans
    ((Equiv.sigmaCongr restrictedProjectionGenericSpectralValueNeg fun c =>
      restrictedProjectionGenericNegFiberEquiv
        R P hR hP hRadj hPadj hDelta c).trans
      (Equiv.sigmaFiberEquiv (restrictedProjectionGenericSpectralValue R P)))

theorem restrictedProjectionGenericSpectralNegEquiv_value
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt)
    (n : restrictedProjectionGenericSpectralIndex R P) :
    (restrictedProjectionGenericSpectralValue R P
      (restrictedProjectionGenericSpectralNegEquiv
        R P hR hP hRadj hPadj hDelta n)).1 =
      -(restrictedProjectionGenericSpectralValue R P n).1 := by
  let p := (Equiv.sigmaFiberEquiv
    (restrictedProjectionGenericSpectralValue R P)).symm n
  let E : (Σ c : RestrictedProjectionGenericSpectralValue,
      {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n = c}) ≃
      (Σ c : RestrictedProjectionGenericSpectralValue,
      {n : restrictedProjectionGenericSpectralIndex R P //
        restrictedProjectionGenericSpectralValue R P n = c}) :=
    Equiv.sigmaCongr restrictedProjectionGenericSpectralValueNeg fun c =>
      restrictedProjectionGenericNegFiberEquiv
        R P hR hP hRadj hPadj hDelta c
  let s := E p
  have hpval : p.1 = restrictedProjectionGenericSpectralValue R P n := rfl
  change (restrictedProjectionGenericSpectralValue R P s.2.1).1 =
    -(restrictedProjectionGenericSpectralValue R P n).1
  calc
    (restrictedProjectionGenericSpectralValue R P s.2.1).1 = s.1.1 :=
      congrArg Subtype.val s.2.2
    _ = -p.1.1 := rfl
    _ = -(restrictedProjectionGenericSpectralValue R P n).1 := by rw [hpval]

theorem tsum_restrictedProjectionGenericSpectralValue_cube_eq_zero
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    ∑' n : restrictedProjectionGenericSpectralIndex R P,
      ((restrictedProjectionGenericSpectralValue R P n).1 : ℂ) ^ 3 = 0 := by
  let E := restrictedProjectionGenericSpectralNegEquiv
    R P hR hP hRadj hPadj hDelta
  let f : restrictedProjectionGenericSpectralIndex R P → ℂ := fun n =>
    ((restrictedProjectionGenericSpectralValue R P n).1 : ℂ) ^ 3
  have hreindex : (∑' n, f (E n)) = ∑' n, f n := E.tsum_eq f
  have hneg : (∑' n, f (E n)) = -(∑' n, f n) := by
    calc
      (∑' n, f (E n)) = ∑' n, -f n := by
        apply tsum_congr
        intro n
        dsimp [f]
        rw [restrictedProjectionGenericSpectralNegEquiv_value
          R P hR hP hRadj hPadj hDelta n]
        push_cast
        ring
      _ = -(∑' n, f n) := tsum_neg
  have hselfneg : (∑' n, f n) = -(∑' n, f n) := hreindex.symm.trans hneg
  have htwo : (2 : ℂ) * (∑' n, f n) = 0 := by
    linear_combination hselfneg
  have htwo_ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

theorem summable_restrictedProjectionDisplacement_sgVal_cube
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    Summable fun n : ℕ =>
      ((ContinuousLinearMap.sgVal (restrictedProjectionDisplacement R P) n : ℝ) : ℂ) ^ 3 := by
  let D := restrictedProjectionDisplacement R P
  have hcpt : IsCompactOperator D := hDelta.isCompactOperator
  have hsym : D.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_restrictedProjectionDisplacement R P hRadj hPadj)
  have hSch : MemSchattenClass 2 D :=
    (memSchattenClass_two_iff_isHilbertSchmidt D).mpr hDelta
  have hsquare : Summable fun n : ℕ => approxNumber D n ^ (2 : ℕ) := by
    refine hSch.congr fun n => ?_
    norm_num [Real.rpow_two]
  apply Summable.of_norm_bounded hsquare
  intro n
  have habs_le : |ContinuousLinearMap.sgVal D n| ≤ 1 := by
    calc
      |ContinuousLinearMap.sgVal D n| = ContinuousLinearMap.orthSup D
          (ContinuousLinearMap.sgVec D) n := ContinuousLinearMap.abs_sgVal hcpt hsym n
      _ ≤ ‖D‖ := ContinuousLinearMap.orthSup_le_opNorm D _ n
      _ ≤ 1 := by
        exact HTGeometry.norm_twoProjection_difference_le_one R P hR hP hRadj hPadj
  have happrox_le : approxNumber D n ≤ 1 := by
    calc
      approxNumber D n = singVal D n := approxNumber_eq_singVal hcpt n
      _ = |ContinuousLinearMap.sgVal D n| :=
        (abs_sgVal_eq_singVal hcpt hsym n).symm
      _ ≤ 1 := habs_le
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_sgVal_eq_singVal hcpt hsym n,
    ← approxNumber_eq_singVal hcpt n]
  nlinarith [approxNumber_nonneg D n]

theorem tsum_restrictedProjectionDisplacement_sgVal_cube_eq_endpoint_ncard
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    ∑' n : ℕ,
        ((ContinuousLinearMap.sgVal (restrictedProjectionDisplacement R P) n : ℝ) : ℂ) ^ 3 =
      (Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n = 1} : ℂ) -
      (Set.ncard {n : ℕ | ContinuousLinearMap.sgVal
          (restrictedProjectionDisplacement R P) n = -1} : ℂ) := by
  classical
  let D := restrictedProjectionDisplacement R P
  let f : ℕ → ℂ := fun n => ((ContinuousLinearMap.sgVal D n : ℝ) : ℂ) ^ 3
  let generic : Set ℕ := {n |
    ContinuousLinearMap.sgVal D n ≠ 0 ∧
    1 - ContinuousLinearMap.sgVal D n ^ 2 ≠ 0}
  let plusSet : Set ℕ := {n | ContinuousLinearMap.sgVal D n = 1}
  let minusSet : Set ℕ := {n | ContinuousLinearMap.sgVal D n = -1}
  have hcpt : IsCompactOperator D := hDelta.isCompactOperator
  have hsym : D.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_restrictedProjectionDisplacement R P hRadj hPadj)
  have hsum : Summable f := by
    simpa [f, D] using
      summable_restrictedProjectionDisplacement_sgVal_cube
        R P hR hP hRadj hPadj hDelta
  have hgeneric : ∑' n : generic, f n = 0 := by
    change ∑' n : restrictedProjectionGenericSpectralIndex R P,
      ((restrictedProjectionGenericSpectralValue R P n).1 : ℂ) ^ 3 = 0
    exact tsum_restrictedProjectionGenericSpectralValue_cube_eq_zero
      R P hR hP hRadj hPadj hDelta
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl generic
  have hcompl : ∑' n : (genericᶜ : Set ℕ), f n = ∑' n : ℕ, f n := by
    rw [hgeneric, zero_add] at hsplit
    exact hsplit
  have hplusfinite : plusSet.Finite := by
    exact ContinuousLinearMap.finite_sgVal_fiber hcpt hsym (by norm_num)
  have hminusfinite : minusSet.Finite := by
    exact ContinuousLinearMap.finite_sgVal_fiber hcpt hsym (by norm_num)
  have hsupp : Function.support (genericᶜ.indicator f) ⊆
      (↑(hplusfinite.toFinset ∪ hminusfinite.toFinset) : Set ℕ) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hncomp : n ∈ genericᶜ := by
      by_contra hncomp
      exact hn (Set.indicator_of_notMem hncomp f)
    have hfne : f n ≠ 0 := by
      simpa [Set.indicator_of_mem hncomp] using hn
    have hc0 : ContinuousLinearMap.sgVal D n ≠ 0 := by
      intro hc0
      apply hfne
      simp [f, hc0]
    have hend : 1 - ContinuousLinearMap.sgVal D n ^ 2 = 0 := by
      by_contra hend
      exact hncomp ⟨hc0, hend⟩
    have hsq : ContinuousLinearMap.sgVal D n ^ 2 = 1 := by linarith
    rcases sq_eq_one_iff.mp hsq with hplus | hminus
    · simp only [Finset.mem_coe, Finset.mem_union, Set.Finite.mem_toFinset]
      exact Or.inl hplus
    · simp only [Finset.mem_coe, Finset.mem_union, Set.Finite.mem_toFinset]
      exact Or.inr hminus
  have hdisjoint : Disjoint hplusfinite.toFinset hminusfinite.toFinset := by
    rw [Finset.disjoint_left]
    intro n hnplus hnminus
    have hp : ContinuousLinearMap.sgVal D n = 1 := by
      exact (Set.Finite.mem_toFinset hplusfinite).mp hnplus
    have hm : ContinuousLinearMap.sgVal D n = -1 := by
      exact (Set.Finite.mem_toFinset hminusfinite).mp hnminus
    linarith
  have hplusSum : ∑ n ∈ hplusfinite.toFinset, genericᶜ.indicator f n =
      (Set.ncard plusSet : ℂ) := by
    calc
      ∑ n ∈ hplusfinite.toFinset, genericᶜ.indicator f n =
          ∑ _n ∈ hplusfinite.toFinset, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hp : ContinuousLinearMap.sgVal D n = 1 :=
          (Set.Finite.mem_toFinset hplusfinite).mp hn
        have hncomp : n ∈ genericᶜ := by
          intro hgen
          exact hgen.2 (by simp [hp])
        rw [Set.indicator_of_mem hncomp]
        simp [f, hp]
      _ = (hplusfinite.toFinset.card : ℂ) := by simp
      _ = (Set.ncard plusSet : ℂ) := by
        rw [Set.ncard_eq_toFinset_card plusSet hplusfinite]
  have hminusSum : ∑ n ∈ hminusfinite.toFinset, genericᶜ.indicator f n =
      -(Set.ncard minusSet : ℂ) := by
    calc
      ∑ n ∈ hminusfinite.toFinset, genericᶜ.indicator f n =
          ∑ _n ∈ hminusfinite.toFinset, (-1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hm : ContinuousLinearMap.sgVal D n = -1 :=
          (Set.Finite.mem_toFinset hminusfinite).mp hn
        have hncomp : n ∈ genericᶜ := by
          intro hgen
          exact hgen.2 (by simp [hm])
        rw [Set.indicator_of_mem hncomp]
        norm_num [f, hm]
      _ = -(hminusfinite.toFinset.card : ℂ) := by simp
      _ = -(Set.ncard minusSet : ℂ) := by
        rw [Set.ncard_eq_toFinset_card minusSet hminusfinite]
  calc
    ∑' n : ℕ, f n = ∑' n : (genericᶜ : Set ℕ), f n := hcompl.symm
    _ = ∑' n : ℕ, genericᶜ.indicator f n := tsum_subtype genericᶜ f
    _ = ∑ n ∈ hplusfinite.toFinset ∪ hminusfinite.toFinset,
          genericᶜ.indicator f n := tsum_eq_sum' hsupp
    _ = (Set.ncard plusSet : ℂ) - (Set.ncard minusSet : ℂ) := by
      rw [Finset.sum_union hdisjoint, hplusSum, hminusSum]
      ring
    _ = _ := by rfl

/-- Relative index of a Hilbert--Schmidt pair of orthogonal projections, expressed by its two
endpoint eigenspaces. -/
def restrictedProjectionRelativeIndex (R P : H →L[ℂ] H) : ℤ :=
  (Module.finrank ℂ (Module.End.eigenspace
      (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (1 : ℂ)) : ℤ) -
  (Module.finrank ℂ (Module.End.eigenspace
      (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) ((-1 : ℝ) : ℂ)) : ℤ)

theorem opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect R P) =
      (restrictedProjectionRelativeIndex R P : ℂ) := by
  let D := restrictedProjectionDisplacement R P
  have hcpt : IsCompactOperator D := hDelta.isCompactOperator
  have hsym : D.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_restrictedProjectionDisplacement R P hRadj hPadj)
  have hDD : (D ∘L D).IsHilbertSchmidt := hDelta.comp_left D
  have hfactor : D ^ 3 = (D ∘L D) ∘L D := by
    simp [pow_succ, ContinuousLinearMap.mul_def]
  have hLidskii : ContinuousLinearMap.opTrace (D ^ 3) =
      ∑' n : ℕ, ((ContinuousLinearMap.sgVal D n : ℝ) : ℂ) ^ 3 :=
    ContinuousLinearMap.opTrace_pow_eq_tsum_sgVal_pow
      hcpt hsym (m := 3) (by norm_num) hDD hDelta hfactor
  have hsum := tsum_restrictedProjectionDisplacement_sgVal_cube_eq_endpoint_ncard
    R P hR hP hRadj hPadj hDelta
  have hplusrank : Module.finrank ℂ (Module.End.eigenspace
        (D : H →ₗ[ℂ] H) (1 : ℂ)) =
      Set.ncard {n : ℕ | ContinuousLinearMap.sgVal D n = 1} :=
    ContinuousLinearMap.finrank_eigenspace_eq_ncard_sgVal_fiber
      hcpt hsym (by norm_num)
  have hminusrank : Module.finrank ℂ (Module.End.eigenspace
        (D : H →ₗ[ℂ] H) ((-1 : ℝ) : ℂ)) =
      Set.ncard {n : ℕ | ContinuousLinearMap.sgVal D n = -1} := by
    simpa using
      (ContinuousLinearMap.finrank_eigenspace_eq_ncard_sgVal_fiber
        hcpt hsym (c := (-1 : ℝ)) (by norm_num))
  rw [restrictedProjectionCubicDefect]
  change ContinuousLinearMap.opTrace (D ^ 3) = _
  rw [hLidskii, hsum]
  simp only [restrictedProjectionRelativeIndex, Int.cast_sub, Int.cast_natCast]
  change
    (Set.ncard {n : ℕ | ContinuousLinearMap.sgVal D n = 1} : ℂ) -
      (Set.ncard {n : ℕ | ContinuousLinearMap.sgVal D n = -1} : ℂ) =
    (Module.finrank ℂ (Module.End.eigenspace (D : H →ₗ[ℂ] H) (1 : ℂ)) : ℂ) -
      (Module.finrank ℂ (Module.End.eigenspace
        (D : H →ₗ[ℂ] H) ((-1 : ℝ) : ℂ)) : ℂ)
  rw [hplusrank, hminusrank]

omit [CompleteSpace H] in
theorem mem_range_restrictedProjection_iff_apply_eq
    (Q : H →L[ℂ] H) (hQ : IsIdempotentElem Q) (x : H) :
    x ∈ LinearMap.range (Q : H →ₗ[ℂ] H) ↔ Q x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    have hQQ := congrArg (fun T : H →L[ℂ] H => T y) hQ
    exact hQQ
  · intro hx
    exact ⟨x, hx⟩

theorem restrictedProjectionComplement_apply_eq_zero_of_one_eigenvector
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    {x : H} (hx : restrictedProjectionDisplacement R P x = x) :
    restrictedProjectionComplement R P x = 0 := by
  have henergy := HTGeometry.norm_twoProjection_difference_sq_add_complement_sq
    R P hR hP hRadj hPadj x
  change ‖restrictedProjectionDisplacement R P x‖ ^ 2 +
      ‖restrictedProjectionComplement R P x‖ ^ 2 = ‖x‖ ^ 2 at henergy
  rw [hx] at henergy
  have hnorm : ‖restrictedProjectionComplement R P x‖ = 0 := by
    nlinarith [norm_nonneg (restrictedProjectionComplement R P x)]
  exact norm_eq_zero.mp hnorm

theorem restrictedProjectionComplement_apply_eq_zero_of_neg_one_eigenvector
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    {x : H} (hx : restrictedProjectionDisplacement R P x = -x) :
    restrictedProjectionComplement R P x = 0 := by
  have henergy := HTGeometry.norm_twoProjection_difference_sq_add_complement_sq
    R P hR hP hRadj hPadj x
  change ‖restrictedProjectionDisplacement R P x‖ ^ 2 +
      ‖restrictedProjectionComplement R P x‖ ^ 2 = ‖x‖ ^ 2 at henergy
  rw [hx, norm_neg] at henergy
  have hnorm : ‖restrictedProjectionComplement R P x‖ = 0 := by
    nlinarith [norm_nonneg (restrictedProjectionComplement R P x)]
  exact norm_eq_zero.mp hnorm

theorem eigenspace_restrictedProjectionDisplacement_one_eq_range_inf_ker
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P) :
    Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) (1 : ℂ) =
      LinearMap.range (R : H →ₗ[ℂ] H) ⊓ LinearMap.ker (P : H →ₗ[ℂ] H) := by
  ext x
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_inf,
    mem_range_restrictedProjection_iff_apply_eq R hR x, LinearMap.mem_ker]
  constructor
  · intro hx
    have hDx : restrictedProjectionDisplacement R P x = x := by simpa using hx
    have hCx := restrictedProjectionComplement_apply_eq_zero_of_one_eigenvector
      R P hR hP hRadj hPadj hDx
    change R x - P x = x at hDx
    change x - R x - P x = 0 at hCx
    have hsum : x = R x + P x := by
      calc
        x = (x - R x - P x) + (R x + P x) := by abel
        _ = R x + P x := by rw [hCx, zero_add]
    have hPneg : -P x = P x := by
      calc
        -P x = (R x - P x) - R x := by abel
        _ = x - R x := by rw [hDx]
        _ = (R x + P x) - R x := congrArg (fun z : H => z - R x) hsum
        _ = P x := by abel
    have htwoP : (2 : ℂ) • P x = 0 := by
      rw [two_smul]
      calc
        P x + P x = P x - (-P x) := by abel
        _ = P x - P x := by rw [hPneg]
        _ = 0 := sub_self _
    have hPx : P x = 0 :=
      (smul_eq_zero.mp htwoP).resolve_left (by norm_num)
    have hRx : R x = x := by simpa [hPx] using hDx
    exact ⟨hRx, hPx⟩
  · rintro ⟨hRx, hPx⟩
    have hPx' : P x = 0 := hPx
    change R x - P x = (1 : ℂ) • x
    rw [hRx, hPx', sub_zero, one_smul]

theorem eigenspace_restrictedProjectionDisplacement_neg_one_eq_range_inf_ker
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P) :
    Module.End.eigenspace
        (restrictedProjectionDisplacement R P : H →ₗ[ℂ] H) ((-1 : ℝ) : ℂ) =
      LinearMap.range (P : H →ₗ[ℂ] H) ⊓ LinearMap.ker (R : H →ₗ[ℂ] H) := by
  ext x
  rw [Module.End.mem_eigenspace_iff, Submodule.mem_inf,
    mem_range_restrictedProjection_iff_apply_eq P hP x, LinearMap.mem_ker]
  constructor
  · intro hx
    have hDx : restrictedProjectionDisplacement R P x = -x := by
      simpa using hx
    have hCx := restrictedProjectionComplement_apply_eq_zero_of_neg_one_eigenvector
      R P hR hP hRadj hPadj hDx
    change R x - P x = -x at hDx
    change x - R x - P x = 0 at hCx
    have hsum : x = R x + P x := by
      calc
        x = (x - R x - P x) + (R x + P x) := by abel
        _ = R x + P x := by rw [hCx, zero_add]
    have hRneg : R x = -R x := by
      calc
        R x = (R x - P x) + P x := by abel
        _ = -x + P x := by rw [hDx]
        _ = -(R x + P x) + P x := congrArg (fun z : H => -z + P x) hsum
        _ = -R x := by abel
    have htwoR : (2 : ℂ) • R x = 0 := by
      rw [two_smul]
      calc
        R x + R x = R x - (-R x) := by abel
        _ = R x - R x := by rw [← hRneg]
        _ = 0 := sub_self _
    have hRx : R x = 0 :=
      (smul_eq_zero.mp htwoR).resolve_left (by norm_num)
    have hPx : P x = x := by
      have hsum' := hsum
      rw [hRx, zero_add] at hsum'
      exact hsum'.symm
    exact ⟨hPx, hRx⟩
  · rintro ⟨hPx, hRx⟩
    have hRx' : R x = 0 := hRx
    change R x - P x = (((-1 : ℝ) : ℂ)) • x
    rw [hRx', hPx, zero_sub]
    push_cast
    module

theorem restrictedProjectionRelativeIndex_eq_intersection_finrank_sub
    (R P : H →L[ℂ] H) (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P) :
    restrictedProjectionRelativeIndex R P =
      (Module.finrank ℂ
          ↥(LinearMap.range (R : H →ₗ[ℂ] H) ⊓ LinearMap.ker (P : H →ₗ[ℂ] H)) : ℤ) -
      (Module.finrank ℂ
          ↥(LinearMap.range (P : H →ₗ[ℂ] H) ⊓ LinearMap.ker (R : H →ₗ[ℂ] H)) : ℤ) := by
  rw [restrictedProjectionRelativeIndex,
    eigenspace_restrictedProjectionDisplacement_one_eq_range_inf_ker
      R P hR hP hRadj hPadj,
    eigenspace_restrictedProjectionDisplacement_neg_one_eq_range_inf_ker
      R P hR hP hRadj hPadj]

end RHTower
