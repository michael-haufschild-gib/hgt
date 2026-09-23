import GaloisForLFunctions.RHTower.CCMRationalMoritaHilbertQuaternionic
import GaloisForLFunctions.RHTower.KRealConjugateFinrank
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Quaternionic Real structure on the rational CCM Hilbert operator ideal

Conjugation by the intrinsic antiunitary on the single CCM Morita fiber defines an isometric
conjugate-linear algebra involution on bounded operators. It preserves Hilbert--Schmidt and
trace-class operators, conjugates ordinary operator trace, and has exactly the bounded
quaternionic-linear operators as fixed points.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

open ContinuousLinearMap

def ccmRationalMoritaHilbertOperatorRealLinearMap
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    CCMRationalMoritaHilbert →ₗ[ℂ] CCMRationalMoritaHilbert where
  toFun f :=
    -ccmRationalMoritaHilbertReflection
      (T (ccmRationalMoritaHilbertReflection f))
  map_add' f g := by
    rw [ccmRationalMoritaHilbertReflection_add, map_add,
      ccmRationalMoritaHilbertReflection_add]
    abel_nf
  map_smul' z f := by
    rw [ccmRationalMoritaHilbertReflection_smul, map_smul,
      ccmRationalMoritaHilbertReflection_smul]
    simp

def ccmRationalMoritaHilbertOperatorRealStructure
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert :=
  (ccmRationalMoritaHilbertOperatorRealLinearMap T).mkContinuous ‖T‖ fun f => by
    change ‖-ccmRationalMoritaHilbertReflection
      (T (ccmRationalMoritaHilbertReflection f))‖ ≤ ‖T‖ * ‖f‖
    rw [norm_neg, ccmRationalMoritaHilbertReflection_norm]
    simpa [ccmRationalMoritaHilbertReflection_norm] using
      T.le_opNorm (ccmRationalMoritaHilbertReflection f)

@[simp]
theorem ccmRationalMoritaHilbertOperatorRealStructure_apply
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert)
    (f : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure T f =
      -ccmRationalMoritaHilbertReflection
        (T (ccmRationalMoritaHilbertReflection f)) :=
  rfl

theorem ccmRationalMoritaHilbertOperatorRealStructure_add
    (S T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure (S + T) =
      ccmRationalMoritaHilbertOperatorRealStructure S +
        ccmRationalMoritaHilbertOperatorRealStructure T := by
  ext f
  simp only [ccmRationalMoritaHilbertOperatorRealStructure_apply, add_apply]
  rw [ccmRationalMoritaHilbertReflection_add]
  abel_nf

theorem ccmRationalMoritaHilbertOperatorRealStructure_smul
    (z : ℂ) (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure (z • T) =
      star z • ccmRationalMoritaHilbertOperatorRealStructure T := by
  ext f
  simp [ccmRationalMoritaHilbertOperatorRealStructure_apply,
    ccmRationalMoritaHilbertReflection_smul]

theorem ccmRationalMoritaHilbertOperatorRealStructure_sq
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure
      (ccmRationalMoritaHilbertOperatorRealStructure T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  change -ccmRationalMoritaHilbertReflection
    (-ccmRationalMoritaHilbertReflection
      (T (ccmRationalMoritaHilbertReflection
        (ccmRationalMoritaHilbertReflection f)))) = T f
  rw [ccmRationalMoritaHilbertReflection_sq, map_neg,
    ccmRationalMoritaHilbertReflection_neg]
  simp [ccmRationalMoritaHilbertReflection_sq]

theorem ccmRationalMoritaHilbertOperatorRealStructure_one :
    ccmRationalMoritaHilbertOperatorRealStructure 1 = 1 := by
  ext f
  simp [ccmRationalMoritaHilbertOperatorRealStructure_apply,
    ccmRationalMoritaHilbertReflection_sq]

theorem ccmRationalMoritaHilbertOperatorRealStructure_comp
    (S T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure (S ∘L T) =
      ccmRationalMoritaHilbertOperatorRealStructure S ∘L
        ccmRationalMoritaHilbertOperatorRealStructure T := by
  apply ContinuousLinearMap.ext
  intro f
  change -ccmRationalMoritaHilbertReflection
      (S (T (ccmRationalMoritaHilbertReflection f))) =
    -ccmRationalMoritaHilbertReflection
      (S (ccmRationalMoritaHilbertReflection
        (-ccmRationalMoritaHilbertReflection
          (T (ccmRationalMoritaHilbertReflection f)))))
  rw [ccmRationalMoritaHilbertReflection_neg,
    ccmRationalMoritaHilbertReflection_sq]
  simp

theorem ccmRationalMoritaHilbertOperatorRealStructure_norm_le
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ‖ccmRationalMoritaHilbertOperatorRealStructure T‖ ≤ ‖T‖ := by
  unfold ccmRationalMoritaHilbertOperatorRealStructure
  apply LinearMap.mkContinuous_norm_le _ (norm_nonneg T)

theorem ccmRationalMoritaHilbertOperatorRealStructure_norm
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ‖ccmRationalMoritaHilbertOperatorRealStructure T‖ = ‖T‖ := by
  apply le_antisymm
  · exact ccmRationalMoritaHilbertOperatorRealStructure_norm_le T
  · calc
      ‖T‖ = ‖ccmRationalMoritaHilbertOperatorRealStructure
          (ccmRationalMoritaHilbertOperatorRealStructure T)‖ := by
        rw [ccmRationalMoritaHilbertOperatorRealStructure_sq]
      _ ≤ ‖ccmRationalMoritaHilbertOperatorRealStructure T‖ :=
        ccmRationalMoritaHilbertOperatorRealStructure_norm_le _

def ccmRationalMoritaHilbertOperatorRealIsometry :
    (CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) ≃ₗᵢ⋆[ℂ]
      (CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) where
  toFun := ccmRationalMoritaHilbertOperatorRealStructure
  invFun := ccmRationalMoritaHilbertOperatorRealStructure
  left_inv := ccmRationalMoritaHilbertOperatorRealStructure_sq
  right_inv := ccmRationalMoritaHilbertOperatorRealStructure_sq
  map_add' := ccmRationalMoritaHilbertOperatorRealStructure_add
  map_smul' := ccmRationalMoritaHilbertOperatorRealStructure_smul
  norm_map' := ccmRationalMoritaHilbertOperatorRealStructure_norm

theorem ccmRationalMoritaHilbertOperatorRealStructure_fixed_iff
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure T = T ↔
      ∀ f, T (ccmRationalMoritaHilbertReflection f) =
        ccmRationalMoritaHilbertReflection (T f) := by
  constructor
  · intro h f
    have hf := congrArg
      (fun S : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert =>
        S (ccmRationalMoritaHilbertReflection f)) h
    change -ccmRationalMoritaHilbertReflection
      (T (ccmRationalMoritaHilbertReflection
        (ccmRationalMoritaHilbertReflection f))) =
      T (ccmRationalMoritaHilbertReflection f) at hf
    rw [ccmRationalMoritaHilbertReflection_sq, map_neg,
      ccmRationalMoritaHilbertReflection_neg] at hf
    simpa using hf.symm
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    rw [ccmRationalMoritaHilbertOperatorRealStructure_apply, h,
      ccmRationalMoritaHilbertReflection_sq]
    simp

def ccmRationalMoritaHilbertBasis :
    HilbertBasis CCMRationalUnit ℂ CCMRationalMoritaHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp]
theorem ccmRationalMoritaHilbertBasis_apply (q : CCMRationalUnit) :
    ccmRationalMoritaHilbertBasis q = lp.single 2 q (1 : ℂ) := by
  rw [← ccmRationalMoritaHilbertBasis.repr_symm_single]
  rfl

theorem ccmRationalMoritaHilbertReflection_basis
    (q : CCMRationalUnit) :
    ccmRationalMoritaHilbertReflection
      (ccmRationalMoritaHilbertBasis q) =
        -ccmRationalUnitSign q • ccmRationalMoritaHilbertBasis (-q) := by
  ext r
  rw [ccmRationalMoritaHilbertBasis_apply,
    ccmRationalMoritaHilbertBasis_apply]
  rw [ccmRationalMoritaHilbertReflection_apply]
  change ccmRationalUnitSign r *
      star ((lp.single 2 q (1 : ℂ) : CCMRationalMoritaHilbert) (-r)) =
    (-ccmRationalUnitSign q) *
      (lp.single 2 (-q) (1 : ℂ) : CCMRationalMoritaHilbert) r
  simp only [lp.single_apply, Pi.single_apply]
  by_cases h : -q = r
  · subst r
    simp
  · have hnr : -r ≠ q := by
      intro hneg
      apply h
      have hrq : r = -q := by
        simpa using congrArg Neg.neg hneg
      exact hrq.symm
    have hr : r ≠ -q := by simpa [eq_comm] using h
    simp [hnr, hr]

theorem ccmRationalMoritaHilbertOperatorRealStructure_basis_norm
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert)
    (q : CCMRationalUnit) :
    ‖ccmRationalMoritaHilbertOperatorRealStructure T
      (ccmRationalMoritaHilbertBasis q)‖ =
        ‖T (ccmRationalMoritaHilbertBasis (-q))‖ := by
  rw [ccmRationalMoritaHilbertOperatorRealStructure_apply, norm_neg,
    ccmRationalMoritaHilbertReflection_norm,
    ccmRationalMoritaHilbertReflection_basis, map_smul, norm_smul,
    norm_neg, ccmRationalUnitSign_norm, one_mul]

theorem ccmRationalMoritaHilbertOperatorRealStructure_isHilbertSchmidt
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsHilbertSchmidt) :
    (ccmRationalMoritaHilbertOperatorRealStructure T).IsHilbertSchmidt := by
  apply ContinuousLinearMap.isHilbertSchmidt_of_summable
    ccmRationalMoritaHilbertBasis
  have hsum := hT.summable ccmRationalMoritaHilbertBasis
  have hneg :
      Summable (fun q : CCMRationalUnit =>
        ‖T (ccmRationalMoritaHilbertBasis (-q))‖ ^ (2 : ℕ)) := by
    have ht :=
      (Equiv.neg CCMRationalUnit).summable_iff.mpr hsum
    exact ht.congr (fun q => by
      dsimp only [Function.comp_apply]
      rw [Equiv.neg_apply])
  exact hneg.congr fun q => by
    rw [ccmRationalMoritaHilbertOperatorRealStructure_basis_norm]

theorem ccmRationalMoritaHilbertOperatorRealStructure_hsNormSq
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsHilbertSchmidt) :
    hsNormSq (ccmRationalMoritaHilbertOperatorRealStructure T) =
      hsNormSq T := by
  have hα :=
    ccmRationalMoritaHilbertOperatorRealStructure_isHilbertSchmidt hT
  rw [ContinuousLinearMap.hsNormSq_eq hα ccmRationalMoritaHilbertBasis,
    ContinuousLinearMap.hsNormSq_eq hT ccmRationalMoritaHilbertBasis]
  rw [← (Equiv.neg CCMRationalUnit).tsum_eq]
  apply tsum_congr
  intro q
  rw [ccmRationalMoritaHilbertOperatorRealStructure_basis_norm,
    Equiv.neg_apply, neg_neg]

theorem ccmRationalMoritaHilbertOperatorRealStructure_hsNorm
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsHilbertSchmidt) :
    hsNorm (ccmRationalMoritaHilbertOperatorRealStructure T) =
      hsNorm T := by
  unfold hsNorm
  rw [ccmRationalMoritaHilbertOperatorRealStructure_hsNormSq hT]

theorem ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsTraceClass) :
    (ccmRationalMoritaHilbertOperatorRealStructure T).IsTraceClass := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT
  rw [hfac, ccmRationalMoritaHilbertOperatorRealStructure_comp]
  exact
    (ccmRationalMoritaHilbertOperatorRealStructure_isHilbertSchmidt hA).comp_isTraceClass
      (ccmRationalMoritaHilbertOperatorRealStructure_isHilbertSchmidt hB)

theorem ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass_iff
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert} :
    (ccmRationalMoritaHilbertOperatorRealStructure T).IsTraceClass ↔
      T.IsTraceClass := by
  constructor
  · intro hα
    have hαα :=
      ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass hα
    rwa [ccmRationalMoritaHilbertOperatorRealStructure_sq] at hαα
  · exact ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass

theorem ccmRationalMoritaHilbertOperatorRealStructure_memSchattenClass_one
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : _root_.RHTower.MemSchattenClass 1 T) :
    _root_.RHTower.MemSchattenClass 1
      (ccmRationalMoritaHilbertOperatorRealStructure T) :=
  _root_.RHTower.IsTraceClass.memSchattenClass_one
    (ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass
      (_root_.RHTower.MemSchattenClass.one_isTraceClass hT))

theorem ccmRationalMoritaHilbertOperatorRealStructure_memSchattenClass_one_iff
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert} :
    _root_.RHTower.MemSchattenClass 1
        (ccmRationalMoritaHilbertOperatorRealStructure T) ↔
      _root_.RHTower.MemSchattenClass 1 T := by
  constructor
  · intro hα
    have hαα :=
      ccmRationalMoritaHilbertOperatorRealStructure_memSchattenClass_one hα
    rwa [ccmRationalMoritaHilbertOperatorRealStructure_sq] at hαα
  · exact ccmRationalMoritaHilbertOperatorRealStructure_memSchattenClass_one

theorem ccmRationalMoritaHilbert_opTrace_eq_tsum_basis
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsTraceClass) :
    opTrace T =
      ∑' q, inner ℂ (ccmRationalMoritaHilbertBasis q)
        (T (ccmRationalMoritaHilbertBasis q)) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB
    ccmRationalMoritaHilbertBasis

@[simp]
theorem ccmRationalMoritaHilbert_inner_basis
    (q : CCMRationalUnit) (f : CCMRationalMoritaHilbert) :
    inner ℂ (ccmRationalMoritaHilbertBasis q) f = f q := by
  rw [← ccmRationalMoritaHilbertBasis.repr_apply_apply]
  rfl

theorem ccmRationalMoritaHilbertOperatorRealStructure_inner_basis
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert)
    (q : CCMRationalUnit) :
    inner ℂ (ccmRationalMoritaHilbertBasis q)
        (ccmRationalMoritaHilbertOperatorRealStructure T
          (ccmRationalMoritaHilbertBasis q)) =
      star (inner ℂ (ccmRationalMoritaHilbertBasis (-q))
        (T (ccmRationalMoritaHilbertBasis (-q)))) := by
  rw [ccmRationalMoritaHilbert_inner_basis,
    ccmRationalMoritaHilbert_inner_basis]
  rw [ccmRationalMoritaHilbertOperatorRealStructure_apply,
    ccmRationalMoritaHilbertReflection_basis, map_smul]
  rw [ccmRationalMoritaHilbertReflection_smul]
  change -(star (-ccmRationalUnitSign q) *
    ccmRationalMoritaHilbertReflection
      (T (ccmRationalMoritaHilbertBasis (-q))) q) =
    star (T (ccmRationalMoritaHilbertBasis (-q)) (-q))
  rw [ccmRationalMoritaHilbertReflection_apply]
  rw [show star (-ccmRationalUnitSign q) =
      -ccmRationalUnitSign q by simp]
  calc
    -(-ccmRationalUnitSign q *
        (ccmRationalUnitSign q *
          star (T (ccmRationalMoritaHilbertBasis (-q)) (-q)))) =
      (ccmRationalUnitSign q * ccmRationalUnitSign q) *
        star (T (ccmRationalMoritaHilbertBasis (-q)) (-q)) := by ring
    _ = star (T (ccmRationalMoritaHilbertBasis (-q)) (-q)) := by
      rw [ccmRationalUnitSign_sq, one_mul]

theorem ccmRationalMoritaHilbertOperatorRealStructure_opTrace
    {T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    (hT : T.IsTraceClass) :
    opTrace (ccmRationalMoritaHilbertOperatorRealStructure T) =
      star (opTrace T) := by
  have hα :=
    ccmRationalMoritaHilbertOperatorRealStructure_isTraceClass hT
  rw [ccmRationalMoritaHilbert_opTrace_eq_tsum_basis hα,
    ccmRationalMoritaHilbert_opTrace_eq_tsum_basis hT]
  rw [tsum_star]
  rw [← (Equiv.neg CCMRationalUnit).tsum_eq]
  apply tsum_congr
  intro q
  rw [ccmRationalMoritaHilbertOperatorRealStructure_inner_basis,
    Equiv.neg_apply, neg_neg]

theorem ccmRationalMoritaHilbertOperatorRealStructure_hasRankLE
    {F : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert}
    {n : ℕ} (hF : _root_.RHTower.HasRankLE F n) :
    _root_.RHTower.HasRankLE
      (ccmRationalMoritaHilbertOperatorRealStructure F) n := by
  obtain ⟨V, hVfinite, hVrank, hVmem⟩ := hF
  let J :=
    ccmRationalMoritaHilbertQuaternionicIsometry.toLinearEquiv
  let W : Submodule ℂ CCMRationalMoritaHilbert :=
    V.map J.toLinearMap
  have hsub :
      V ≃ₗ⋆[ℂ] W :=
    J.submoduleMap V
  have hWfinite : FiniteDimensional ℂ W := by
    letI := hVfinite
    exact Module.Finite.of_surjective hsub.toLinearMap hsub.surjective
  refine ⟨W, hWfinite, ?_, ?_⟩
  · rw [← finrank_eq_of_conjugateLinearEquiv hsub]
    exact hVrank
  · intro x
    change -ccmRationalMoritaHilbertReflection
      (F (ccmRationalMoritaHilbertReflection x)) ∈ W
    change -J (F (J x)) ∈ W
    refine ⟨-F (J x), V.neg_mem (hVmem (J x)), ?_⟩
    exact J.map_neg (F (J x))

theorem ccmRationalMoritaHilbertOperatorRealStructure_sub
    (S T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertOperatorRealStructure (S - T) =
      ccmRationalMoritaHilbertOperatorRealStructure S -
        ccmRationalMoritaHilbertOperatorRealStructure T := by
  have hneg :
      ccmRationalMoritaHilbertOperatorRealStructure (-T) =
        -ccmRationalMoritaHilbertOperatorRealStructure T := by
    simpa using ccmRationalMoritaHilbertOperatorRealStructure_smul
      (-1 : ℂ) T
  rw [sub_eq_add_neg, ccmRationalMoritaHilbertOperatorRealStructure_add,
    hneg]
  simp [sub_eq_add_neg]

theorem ccmRationalMoritaHilbertOperatorRealStructure_approxNumber_le
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert)
    (n : ℕ) :
    _root_.RHTower.approxNumber
        (ccmRationalMoritaHilbertOperatorRealStructure T) n ≤
      _root_.RHTower.approxNumber T n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hFlt⟩ :=
    _root_.RHTower.exists_hasRankLE_norm_sub_lt T n
      (lt_add_of_pos_right _ hε)
  have hαF :=
    ccmRationalMoritaHilbertOperatorRealStructure_hasRankLE hF
  have hle :=
    _root_.RHTower.approxNumber_le
      (ccmRationalMoritaHilbertOperatorRealStructure T) n
      (ccmRationalMoritaHilbertOperatorRealStructure F) hαF
  rw [← ccmRationalMoritaHilbertOperatorRealStructure_sub,
    ccmRationalMoritaHilbertOperatorRealStructure_norm] at hle
  exact hle.trans hFlt.le

theorem ccmRationalMoritaHilbertOperatorRealStructure_approxNumber
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert)
    (n : ℕ) :
    _root_.RHTower.approxNumber
        (ccmRationalMoritaHilbertOperatorRealStructure T) n =
      _root_.RHTower.approxNumber T n := by
  apply le_antisymm
  · exact ccmRationalMoritaHilbertOperatorRealStructure_approxNumber_le T n
  · calc
      _ = _root_.RHTower.approxNumber
          (ccmRationalMoritaHilbertOperatorRealStructure
            (ccmRationalMoritaHilbertOperatorRealStructure T)) n := by
        rw [ccmRationalMoritaHilbertOperatorRealStructure_sq]
      _ ≤ _ :=
        ccmRationalMoritaHilbertOperatorRealStructure_approxNumber_le
          (ccmRationalMoritaHilbertOperatorRealStructure T) n

theorem ccmRationalMoritaHilbertOperatorRealStructure_traceNorm
    (T : CCMRationalMoritaHilbert →L[ℂ] CCMRationalMoritaHilbert) :
    _root_.RHTower.traceNorm CCMRationalMoritaHilbert
        (ccmRationalMoritaHilbertOperatorRealStructure T) =
      _root_.RHTower.traceNorm CCMRationalMoritaHilbert T := by
  unfold _root_.RHTower.traceNorm
  exact tsum_congr fun n =>
    ccmRationalMoritaHilbertOperatorRealStructure_approxNumber T n

end RHTower
end GaloisForLFunctions
