import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionAnalyticLaw
import GaloisForLFunctions.HTGeometry.UniversalHausdorffQuotient
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Multiple-Gamma marked period action law

This module formalizes the marked `Z^3` translation presentation with periods
`1, i, 2i + pi/m`, its cofinal boundary `1, i, 2i`, the exact kernels and image closures,
the compatible affine involution, and the rank/depth ledger.
-/

open Set Topology Complex ContinuousMonoidHom QuotientAddGroup
open scoped Pointwise BigOperators

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-- Marked source lattice `Z^3`. -/
abbrev MultipleGammaPeriodSource := Fin 3 → ℤ

/-- Finite marked period family `(1, i, 2i + pi/m)`. -/
def finiteMultipleGammaPeriods (m : ℕ+) : Fin 3 → ℂ :=
  ![1, Complex.I, 2 * Complex.I + (Real.pi / (m : ℝ) : ℝ)]

/-- Boundary marked period family `(1, i, 2i)`. -/
def boundaryMultipleGammaPeriods : Fin 3 → ℂ :=
  ![1, Complex.I, 2 * Complex.I]

/-- Period realization `p_m : Z^3 → C` for finite `m`. -/
def finiteMultipleGammaPeriodMap (m : ℕ+) : MultipleGammaPeriodSource →+ ℂ where
  toFun n := ∑ j, (n j : ℂ) * finiteMultipleGammaPeriods m j
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

/-- Boundary period realization `p_infinity : Z^3 → C`. -/
def boundaryMultipleGammaPeriodMap : MultipleGammaPeriodSource →+ ℂ where
  toFun n := ∑ j, (n j : ℂ) * boundaryMultipleGammaPeriods j
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem finiteMultipleGammaPeriodMap_apply (m : ℕ+) (n : MultipleGammaPeriodSource) :
    finiteMultipleGammaPeriodMap m n =
      (n 0 : ℂ) + (n 1 : ℂ) * Complex.I +
        (n 2 : ℂ) * (2 * Complex.I + (Real.pi / (m : ℝ) : ℝ)) := by
  simp [finiteMultipleGammaPeriodMap, finiteMultipleGammaPeriods, Fin.sum_univ_succ]
  ring

theorem boundaryMultipleGammaPeriodMap_apply (n : MultipleGammaPeriodSource) :
    boundaryMultipleGammaPeriodMap n =
      (n 0 : ℂ) + (n 1 : ℂ) * Complex.I + (n 2 : ℂ) * (2 * Complex.I) := by
  simp [boundaryMultipleGammaPeriodMap, boundaryMultipleGammaPeriods, Fin.sum_univ_succ]
  ring

/-- Real marked subgroup `Z + (pi/m)Z`. -/
def finiteMultipleGammaRealPeriods (m : ℕ+) : AddSubgroup ℝ :=
  AddSubgroup.closure ({1, Real.pi / (m : ℝ)} : Set ℝ)

/-- Integral imaginary period subgroup. -/
abbrev multipleGammaIntegerPeriods : AddSubgroup ℝ :=
  AddSubgroup.zmultiples 1

/-- Subgroup of `C` with prescribed real and imaginary coordinate subgroups. -/
def complexAxisPeriodSubgroup (A B : AddSubgroup ℝ) : AddSubgroup ℂ :=
  (A.prod B).comap Complex.equivRealProdAddHom.toAddMonoidHom

/-- Finite marked image subgroup `Lambda_m`. -/
def finiteMultipleGammaPeriodSubgroup (m : ℕ+) : AddSubgroup ℂ :=
  (finiteMultipleGammaPeriodMap m).range

/-- Boundary marked image subgroup `Lambda_infinity`. -/
def boundaryMultipleGammaPeriodSubgroup : AddSubgroup ℂ :=
  boundaryMultipleGammaPeriodMap.range

/-- The finite image is exactly `(Z + (pi/m)Z) + iZ`. -/
theorem finiteMultipleGammaPeriodSubgroup_eq_axes (m : ℕ+) :
    finiteMultipleGammaPeriodSubgroup m =
      complexAxisPeriodSubgroup (finiteMultipleGammaRealPeriods m) multipleGammaIntegerPeriods := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    change (finiteMultipleGammaPeriodMap m n).re ∈ finiteMultipleGammaRealPeriods m ∧
      (finiteMultipleGammaPeriodMap m n).im ∈ multipleGammaIntegerPeriods
    rw [finiteMultipleGammaPeriodMap_apply]
    constructor
    · rw [finiteMultipleGammaRealPeriods, AddSubgroup.mem_closure_pair]
      refine ⟨n 0, n 2, ?_⟩
      simp
    · refine ⟨n 1 + 2 * n 2, ?_⟩
      simp [multipleGammaIntegerPeriods]
      ring
  · intro hz
    change z.re ∈ finiteMultipleGammaRealPeriods m ∧
      z.im ∈ multipleGammaIntegerPeriods at hz
    rw [finiteMultipleGammaRealPeriods, AddSubgroup.mem_closure_pair] at hz
    rcases hz.1 with ⟨a, c, hac⟩
    rcases hz.2 with ⟨b, hb⟩
    let n : MultipleGammaPeriodSource := ![a, b - 2 * c, c]
    refine ⟨n, Complex.ext ?_ ?_⟩
    · rw [finiteMultipleGammaPeriodMap_apply]
      simpa [n] using hac
    · rw [finiteMultipleGammaPeriodMap_apply]
      convert hb using 1 <;> simp [n] <;> push_cast <;> ring

/-- The boundary image is exactly `Z + iZ`. -/
theorem boundaryMultipleGammaPeriodSubgroup_eq_axes :
    boundaryMultipleGammaPeriodSubgroup =
      complexAxisPeriodSubgroup multipleGammaIntegerPeriods multipleGammaIntegerPeriods := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    change (boundaryMultipleGammaPeriodMap n).re ∈ multipleGammaIntegerPeriods ∧
      (boundaryMultipleGammaPeriodMap n).im ∈ multipleGammaIntegerPeriods
    rw [boundaryMultipleGammaPeriodMap_apply]
    constructor
    · exact ⟨n 0, by simp [multipleGammaIntegerPeriods]⟩
    · exact ⟨n 1 + 2 * n 2, by simp [multipleGammaIntegerPeriods]; ring⟩
  · intro hz
    change z.re ∈ multipleGammaIntegerPeriods ∧
      z.im ∈ multipleGammaIntegerPeriods at hz
    rcases hz.1 with ⟨a, ha⟩
    rcases hz.2 with ⟨b, hb⟩
    let n : MultipleGammaPeriodSource := ![a, b, 0]
    refine ⟨n, Complex.ext ?_ ?_⟩
    · rw [boundaryMultipleGammaPeriodMap_apply]
      simpa [n] using ha
    · rw [boundaryMultipleGammaPeriodMap_apply]
      simpa [n] using hb

/-- `Z + (pi/m)Z` is dense in `R`. -/
theorem finiteMultipleGammaRealPeriods_dense (m : ℕ+) :
    Dense (finiteMultipleGammaRealPeriods m : Set ℝ) := by
  rw [finiteMultipleGammaRealPeriods, dense_addSubgroupClosure_pair_iff]
  simpa using irrational_pi.div_natCast m (by exact m.ne_zero)

/-- The finite marked image has closure `R + iZ`. -/
theorem finiteMultipleGammaPeriodSubgroup_topologicalClosure (m : ℕ+) :
    (finiteMultipleGammaPeriodSubgroup m).topologicalClosure =
      complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods := by
  rw [finiteMultipleGammaPeriodSubgroup_eq_axes]
  apply SetLike.ext'
  simp only [AddSubgroup.topologicalClosure_coe, complexAxisPeriodSubgroup,
    AddSubgroup.coe_comap, AddSubgroup.coe_prod]
  change closure ((finiteMultipleGammaRealPeriods m : Set ℝ) ×ℂ
      (multipleGammaIntegerPeriods : Set ℝ)) =
    (Set.univ ×ℂ (multipleGammaIntegerPeriods : Set ℝ))
  rw [Complex.closure_reProdIm]
  have hreal : closure (finiteMultipleGammaRealPeriods m : Set ℝ) = Set.univ :=
    (finiteMultipleGammaRealPeriods_dense m).closure_eq
  have hint : IsClosed (multipleGammaIntegerPeriods : Set ℝ) := by
    simpa [multipleGammaIntegerPeriods, AddSubgroup.coe_zmultiples] using
      Real.isClosed_range_intCast
  rw [hreal, hint.closure_eq]

/-- The boundary image is closed. -/
theorem boundaryMultipleGammaPeriodSubgroup_isClosed :
    IsClosed (boundaryMultipleGammaPeriodSubgroup : Set ℂ) := by
  rw [boundaryMultipleGammaPeriodSubgroup_eq_axes]
  have hint : IsClosed (multipleGammaIntegerPeriods : Set ℝ) := by
    simpa [multipleGammaIntegerPeriods, AddSubgroup.coe_zmultiples] using
      Real.isClosed_range_intCast
  exact (hint.prod hint).preimage Complex.equivRealProdCLM.continuous

/-- The identity continuous additive equivalence maps every subgroup to itself. -/
theorem addSubgroup_map_continuousAddEquiv_refl (A : AddSubgroup ℂ) :
    A.map (ContinuousAddEquiv.refl ℂ).toAddEquiv.toAddMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    change y = x at hxy
    simpa [← hxy] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Quotienting a complex axis-product subgroup is the product of the two real quotients. -/
def complexAxisQuotientEquivProduct (A B : AddSubgroup ℝ) :
    (ℂ ⧸ complexAxisPeriodSubgroup A B) ≃ₜ+ ((ℝ ⧸ A) × (ℝ ⧸ B)) := by
  let e : ℂ ≃ₜ+ ℝ × ℝ := Complex.equivRealProdCLM.toContinuousAddEquiv
  have hmap : (complexAxisPeriodSubgroup A B).map e.toAddEquiv.toAddMonoidHom = A.prod B := by
    rw [complexAxisPeriodSubgroup]
    exact AddSubgroup.map_comap_eq_self_of_surjective e.surjective (A.prod B)
  exact (quotientContinuousAddEquiv e (complexAxisPeriodSubgroup A B) (A.prod B) hmap).trans
    (quotientProdContinuousAddEquiv A B)

/-- A product with a subsingleton additive factor is continuously additively equivalent to its
second factor. -/
def dropSubsingletonLeftContinuousAddEquiv
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [AddCommGroup A] [AddCommGroup B] [Subsingleton A] : (A × B) ≃ₜ+ B where
  toFun := Prod.snd
  invFun b := (0, b)
  left_inv x := by ext <;> simp [Subsingleton.elim x.1 0]
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

/-- Universal Hausdorff observer of the finite marked quotient, before identifying the circle. -/
abbrev finiteMultipleGammaHausdorffObserver (m : ℕ+) :=
  ℂ ⧸ (finiteMultipleGammaPeriodSubgroup m).topologicalClosure

/-- Boundary coarse quotient, already Hausdorff. -/
abbrev boundaryMultipleGammaCoarseQuotient :=
  ℂ ⧸ boundaryMultipleGammaPeriodSubgroup

/-- Finite universal Hausdorff observer is exactly the real additive circle `R/Z`. -/
def finiteMultipleGammaHausdorffObserverEquivAddCircle (m : ℕ+) :
    finiteMultipleGammaHausdorffObserver m ≃ₜ+ AddCircle (1 : ℝ) := by
  let e₀ : finiteMultipleGammaHausdorffObserver m ≃ₜ+
      (ℂ ⧸ complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods) :=
    quotientContinuousAddEquiv (ContinuousAddEquiv.refl ℂ)
      (finiteMultipleGammaPeriodSubgroup m).topologicalClosure
      (complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods) (by
        rw [addSubgroup_map_continuousAddEquiv_refl,
          finiteMultipleGammaPeriodSubgroup_topologicalClosure])
  let e₁ := complexAxisQuotientEquivProduct (⊤ : AddSubgroup ℝ) multipleGammaIntegerPeriods
  letI : Subsingleton (ℝ ⧸ (⊤ : AddSubgroup ℝ)) :=
    QuotientAddGroup.subsingleton_quotient_top
  exact e₀.trans <| e₁.trans <|
    (dropSubsingletonLeftContinuousAddEquiv
      (A := ℝ ⧸ (⊤ : AddSubgroup ℝ)) (B := AddCircle (1 : ℝ)))

/-- Boundary coarse quotient is exactly the two-dimensional real torus. -/
def boundaryMultipleGammaCoarseQuotientEquivTorus :
    boundaryMultipleGammaCoarseQuotient ≃ₜ+
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  let e₀ : boundaryMultipleGammaCoarseQuotient ≃ₜ+
      (ℂ ⧸ complexAxisPeriodSubgroup multipleGammaIntegerPeriods
        multipleGammaIntegerPeriods) :=
    quotientContinuousAddEquiv (ContinuousAddEquiv.refl ℂ)
      boundaryMultipleGammaPeriodSubgroup
      (complexAxisPeriodSubgroup multipleGammaIntegerPeriods multipleGammaIntegerPeriods) (by
        rw [addSubgroup_map_continuousAddEquiv_refl,
          boundaryMultipleGammaPeriodSubgroup_eq_axes])
  exact e₀.trans <|
    complexAxisQuotientEquivProduct multipleGammaIntegerPeriods multipleGammaIntegerPeriods

/-- The boundary quotient is compact. -/
theorem boundaryMultipleGammaCoarseQuotient_compactSpace :
    CompactSpace boundaryMultipleGammaCoarseQuotient := by
  exact boundaryMultipleGammaCoarseQuotientEquivTorus.toHomeomorph.symm.compactSpace

/-- The boundary quotient is Hausdorff. -/
theorem boundaryMultipleGammaCoarseQuotient_t2Space :
    T2Space boundaryMultipleGammaCoarseQuotient := by
  exact (quotient_t2Space_iff_isClosed boundaryMultipleGammaPeriodSubgroup).mpr
    boundaryMultipleGammaPeriodSubgroup_isClosed

/-- The real subgroup `Z + (pi/m)Z` is proper despite being dense. -/
theorem finiteMultipleGammaRealPeriods_ne_top (m : ℕ+) :
    finiteMultipleGammaRealPeriods m ≠ ⊤ := by
  intro htop
  have hmem : Real.pi / (2 * (m : ℝ)) ∈ finiteMultipleGammaRealPeriods m := by
    rw [htop]
    trivial
  rw [finiteMultipleGammaRealPeriods, AddSubgroup.mem_closure_pair] at hmem
  rcases hmem with ⟨a, c, hac⟩
  have hodd : 2 * c - 1 ≠ 0 := by omega
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hscaled : 2 * (a : ℝ) * (m : ℕ) + (2 * (c : ℝ) - 1) * Real.pi = 0 := by
    simp only [zsmul_eq_mul, Int.cast_one] at hac
    field_simp [hmR] at hac
    linear_combination hac
  have hoddR : ((2 * c - 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hodd
  have hpi : Real.pi = (((-2 * a * (m : ℤ)) : ℤ) : ℝ) / ((2 * c - 1 : ℤ) : ℝ) := by
    rw [eq_div_iff hoddR]
    push_cast
    linear_combination hscaled
  exact irrational_pi.ne_rational (-2 * a * (m : ℤ)) (2 * c - 1) hpi

/-- The finite real marked period subgroup is not closed. -/
theorem finiteMultipleGammaRealPeriods_not_isClosed (m : ℕ+) :
    ¬ IsClosed (finiteMultipleGammaRealPeriods m : Set ℝ) := by
  intro hclosed
  apply finiteMultipleGammaRealPeriods_ne_top m
  apply SetLike.coe_injective
  rw [AddSubgroup.coe_top, ← (finiteMultipleGammaRealPeriods_dense m).closure_eq,
    hclosed.closure_eq]

/-- The finite complex marked period subgroup is not closed. -/
theorem finiteMultipleGammaPeriodSubgroup_not_isClosed (m : ℕ+) :
    ¬ IsClosed (finiteMultipleGammaPeriodSubgroup m : Set ℂ) := by
  intro hclosed
  have hclosure : (finiteMultipleGammaPeriodSubgroup m).topologicalClosure =
      finiteMultipleGammaPeriodSubgroup m := by
    apply SetLike.coe_injective
    simpa only [AddSubgroup.topologicalClosure_coe] using hclosed.closure_eq
  have hEq : finiteMultipleGammaPeriodSubgroup m =
      complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods := by
    rw [← hclosure]
    exact finiteMultipleGammaPeriodSubgroup_topologicalClosure m
  apply finiteMultipleGammaRealPeriods_ne_top m
  ext x
  rw [finiteMultipleGammaPeriodSubgroup_eq_axes] at hEq
  have hz := SetLike.ext_iff.mp hEq (x : ℂ)
  change (x ∈ finiteMultipleGammaRealPeriods m ∧
      (0 : ℝ) ∈ multipleGammaIntegerPeriods) ↔
    (x ∈ (⊤ : AddSubgroup ℝ) ∧ (0 : ℝ) ∈ multipleGammaIntegerPeriods) at hz
  simpa using hz

/-- Finite coarse quotient is not `T₁`. -/
theorem finiteMultipleGammaCoarseQuotient_not_t1Space (m : ℕ+) :
    ¬ T1Space (ℂ ⧸ finiteMultipleGammaPeriodSubgroup m) := by
  rw [QuotientAddGroup.t1Space_iff]
  exact finiteMultipleGammaPeriodSubgroup_not_isClosed m

/-- Finite coarse quotient is not Hausdorff. -/
theorem finiteMultipleGammaCoarseQuotient_not_t2Space (m : ℕ+) :
    ¬ T2Space (ℂ ⧸ finiteMultipleGammaPeriodSubgroup m) := by
  rw [quotient_t2Space_iff_isClosed]
  exact finiteMultipleGammaPeriodSubgroup_not_isClosed m

/-- Boundary relation vector `(0,-2,1)`. -/
def boundaryMultipleGammaRelation : MultipleGammaPeriodSource := ![0, -2, 1]

/-- Exact finite stabilizer: the period realization is faithful. -/
theorem finiteMultipleGammaPeriodMap_ker (m : ℕ+) :
    (finiteMultipleGammaPeriodMap m).ker = ⊥ := by
  apply bot_unique
  intro n hn
  have h := hn
  rw [AddMonoidHom.mem_ker, finiteMultipleGammaPeriodMap_apply] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  norm_num at hre him
  have hc : n 2 = 0 := by
    by_contra hc
    have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
    have hnR : (n 2 : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp [hmR] at hre
    have hpi : Real.pi = ((-(n 0) * (m : ℤ) : ℤ) : ℝ) / (n 2 : ℝ) := by
      field_simp [hnR]
      push_cast at ⊢
      nlinarith
    exact irrational_pi.ne_rational (-(n 0) * (m : ℤ)) (n 2) hpi
  have ha : n 0 = 0 := by
    push_cast at hre
    simpa [hc] using hre
  have hb : n 1 = 0 := by
    push_cast at him
    simpa [hc] using him
  funext j
  fin_cases j <;> assumption

/-- Exact boundary stabilizer `Z(0,-2,1)`. -/
theorem boundaryMultipleGammaPeriodMap_ker :
    boundaryMultipleGammaPeriodMap.ker =
      AddSubgroup.zmultiples boundaryMultipleGammaRelation := by
  ext n
  constructor
  · intro hn
    rw [AddMonoidHom.mem_ker, boundaryMultipleGammaPeriodMap_apply] at hn
    have hre := congrArg Complex.re hn
    have him := congrArg Complex.im hn
    norm_num at hre him
    have hreZ : n 0 = 0 := by exact_mod_cast hre
    have himCast : ((n 1 + n 2 * 2 : ℤ) : ℝ) = 0 := by
      push_cast
      exact him
    have himZ : n 1 + n 2 * 2 = 0 := by exact_mod_cast himCast
    refine ⟨n 2, ?_⟩
    funext j
    fin_cases j
    · simp [boundaryMultipleGammaRelation]
      exact hreZ.symm
    · simp [boundaryMultipleGammaRelation]
      omega
    · simp [boundaryMultipleGammaRelation]
  · rintro ⟨k, rfl⟩
    rw [AddMonoidHom.mem_ker, map_zsmul]
    simp [boundaryMultipleGammaRelation, boundaryMultipleGammaPeriodMap_apply]

/-- Translation-action stabilizer at an object. -/
def markedTranslationStabilizer (p : MultipleGammaPeriodSource →+ ℂ) (z : ℂ) :
    AddSubgroup MultipleGammaPeriodSource where
  carrier := {n | z + p n = z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    have hpa : p a = 0 := by exact add_left_cancel (ha.trans (add_zero z).symm)
    have hpb : p b = 0 := by exact add_left_cancel (hb.trans (add_zero z).symm)
    simp [hpa, hpb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg] at ha ⊢
    have hp : p a = 0 := add_left_cancel (ha.trans (add_zero z).symm)
    simp [hp]

/-- Every object stabilizer is canonically the kernel of the marked period map. -/
theorem markedTranslationStabilizer_eq_ker
    (p : MultipleGammaPeriodSource →+ ℂ) (z : ℂ) :
    markedTranslationStabilizer p z = p.ker := by
  ext n
  simp [markedTranslationStabilizer, AddMonoidHom.mem_ker]

/-- Affine reflection center, finite stage. -/
def finiteMultipleGammaReflectionCenter (m : ℕ+) : ℂ :=
  finiteMultipleGammaPeriods m 1 + finiteMultipleGammaPeriods m 2

/-- Affine reflection center, boundary. -/
def boundaryMultipleGammaReflectionCenter : ℂ :=
  boundaryMultipleGammaPeriods 1 + boundaryMultipleGammaPeriods 2

/-- The marked finite action center is exactly the independently defined analytic center. -/
theorem finiteMultipleGammaReflectionCenter_eq_analytic (m : ℕ+) :
    finiteMultipleGammaReflectionCenter m = finiteMultipleGammaAnalyticReflectionCenter m := by
  simp [finiteMultipleGammaReflectionCenter, finiteMultipleGammaAnalyticReflectionCenter,
    finiteMultipleGammaPeriods, finiteMultipleGammaFunctionPeriods]

/-- The marked boundary action center is exactly the independently defined analytic center. -/
theorem boundaryMultipleGammaReflectionCenter_eq_analytic :
    boundaryMultipleGammaReflectionCenter = boundaryMultipleGammaAnalyticReflectionCenter := by
  simp [boundaryMultipleGammaReflectionCenter, boundaryMultipleGammaAnalyticReflectionCenter,
    boundaryMultipleGammaPeriods, boundaryMultipleGammaFunctionPeriods]

/-- Independent finite product reflection uses the same center as the groupoid involution. -/
theorem finiteMultipleGammaProduct_reflection_at_actionCenter (m : ℕ+) (z : ℂ) :
    multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m)
        (finiteMultipleGammaReflectionCenter m - z) =
      (multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z)⁻¹ := by
  rw [finiteMultipleGammaReflectionCenter_eq_analytic]
  exact finiteMultipleGammaProduct_reflection m z

/-- Independent boundary product reflection uses the same center as the groupoid involution. -/
theorem boundaryMultipleGammaProduct_reflection_at_actionCenter (z : ℂ) :
    multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods
        (boundaryMultipleGammaReflectionCenter - z) =
      (multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods z)⁻¹ := by
  rw [boundaryMultipleGammaReflectionCenter_eq_analytic]
  exact boundaryMultipleGammaProduct_reflection z

/-- Reflection reverses every finite marked translation arrow. -/
theorem finiteMultipleGamma_reflection_translation (m : ℕ+)
    (n : MultipleGammaPeriodSource) (z : ℂ) :
    finiteMultipleGammaReflectionCenter m - (z + finiteMultipleGammaPeriodMap m n) =
      (finiteMultipleGammaReflectionCenter m - z) + finiteMultipleGammaPeriodMap m (-n) := by
  simp only [map_neg]
  abel

/-- Reflection reverses every boundary marked translation arrow. -/
theorem boundaryMultipleGamma_reflection_translation
    (n : MultipleGammaPeriodSource) (z : ℂ) :
    boundaryMultipleGammaReflectionCenter - (z + boundaryMultipleGammaPeriodMap n) =
      (boundaryMultipleGammaReflectionCenter - z) + boundaryMultipleGammaPeriodMap (-n) := by
  simp only [map_neg]
  abel

/-- The arrow reflection is involutive. -/
theorem markedTranslationArrow_reflection_involutive
    (c z : ℂ) (n : MultipleGammaPeriodSource) :
    (-(-n), c - (c - z)) = (n, z) := by simp

end

end HTGeometry
end GaloisForLFunctions
