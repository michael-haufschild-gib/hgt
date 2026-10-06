import GaloisForLFunctions.HTGeometry.HilbertClosedRange
import GaloisForLFunctions.HTGeometry.CompactOperatorBoundedBelow
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum

/-!
# Compact--cofinal formation fusion

A compact local reporter and a cofinal reporter jointly control a Hilbert source exactly when the
cofinal reporter has closed range and finite kernel and the compact reporter separates that kernel.
The same retained cofinal carrier supports a relative scalar defect which can vanish without
breaking reconstruction.
-/

open Filter Topology Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H Y Z : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]

/-- Uniform joint observability of two formation reporters. -/
def IsJointlyBoundedBelow (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : H, c * ‖x‖ ≤ ‖(A.prod R) x‖

/-- The retained cofinal reporter has closed range and finite residual kernel. -/
def IsCofinalTransducer (R : H →L[ℂ] Z) : Prop :=
  IsClosed (Set.range R) ∧ FiniteDimensional ℂ (LinearMap.ker (R : H →ₗ[ℂ] Z))

omit [CompleteSpace Y] [CompleteSpace Z] in
/-- A jointly bounded compact/cofinal packet has finite residual kernel. -/
theorem finiteDimensional_ker_of_compact_jointlyBoundedBelow
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) :
    FiniteDimensional ℂ (LinearMap.ker (R : H →ₗ[ℂ] Z)) := by
  obtain ⟨c, hc, hbound⟩ := hjoint
  let K : Submodule ℂ H := LinearMap.ker (R : H →ₗ[ℂ] Z)
  apply finiteDimensional_of_isCompactOperator_of_bounded_below hA K R.isClosed_ker hc
  intro x hx
  have hxR : R x = 0 := hx
  have h := hbound x
  simpa [ContinuousLinearMap.prod_apply, Prod.norm_def, hxR] using h

omit [CompleteSpace Y] in
/-- A jointly bounded compact/cofinal packet forces the cofinal reporter to have closed range. -/
theorem isClosed_range_of_compact_jointlyBoundedBelow
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) :
    IsClosed (Set.range R) := by
  by_contra hclosed
  let Rt := ContinuousLinearMap.transverseRestriction R
  have hRtInj : Function.Injective Rt :=
    ContinuousLinearMap.transverseRestriction_injective R
  have hRtNotClosed : ¬ IsClosed (Set.range Rt) := by
    rwa [ContinuousLinearMap.range_transverseRestriction]
  obtain ⟨u, huNorm, huZero⟩ :=
    (hasApproximateUnitKernel_iff_not_isClosed_range Rt hRtInj).2 hRtNotClosed
  let At : ((LinearMap.ker (R : H →ₗ[ℂ] Z))ᗮ : Submodule ℂ H) →L[ℂ] Y :=
    A ∘L (LinearMap.ker (R : H →ₗ[ℂ] Z))ᗮ.subtypeL
  have hAtCompact : IsCompactOperator At := hA.comp_clm _
  have hmem : ∀ n, At (u n) ∈ closure (At '' Metric.closedBall 0 1) := by
    intro n
    refine subset_closure ⟨u n, ?_, rfl⟩
    simp [Metric.mem_closedBall, dist_eq_norm, huNorm n]
  obtain ⟨a, _ha, phi, hphi, hAtConv⟩ :=
    (hAtCompact.isCompact_closure_image_closedBall 1).tendsto_subseq hmem
  have hRConv : Tendsto (fun n => Rt (u (phi n))) atTop (nhds 0) :=
    huZero.comp hphi.tendsto_atTop
  have hAtCauchy : CauchySeq (fun n => At (u (phi n))) := hAtConv.cauchySeq
  have hRCauchy : CauchySeq (fun n => Rt (u (phi n))) := hRConv.cauchySeq
  obtain ⟨c, hc, hbound⟩ := hjoint
  have huCauchy : CauchySeq (fun n => u (phi n)) := by
    rw [Metric.cauchySeq_iff] at hAtCauchy hRCauchy ⊢
    intro eps heps
    obtain ⟨NA, hNA⟩ := hAtCauchy (c * eps) (mul_pos hc heps)
    obtain ⟨NR, hNR⟩ := hRCauchy (c * eps) (mul_pos hc heps)
    refine ⟨max NA NR, ?_⟩
    intro m hm n hn
    have hmA : NA ≤ m := le_trans (le_max_left _ _) hm
    have hnA : NA ≤ n := le_trans (le_max_left _ _) hn
    have hmR : NR ≤ m := le_trans (le_max_right _ _) hm
    have hnR : NR ≤ n := le_trans (le_max_right _ _) hn
    have hAeps := hNA m hmA n hnA
    have hReps := hNR m hmR n hnR
    let w : H := (u (phi m) : H) - (u (phi n) : H)
    have hpair := hbound w
    have hpairLt : ‖(A.prod R) w‖ < c * eps := by
      rw [ContinuousLinearMap.prod_apply, Prod.norm_def, max_lt_iff]
      constructor
      · simpa [At, w, dist_eq_norm, map_sub] using hAeps
      · simpa [Rt, w, dist_eq_norm, map_sub] using hReps
    have hwlt : ‖w‖ < eps := by nlinarith
    simpa [w, Subtype.dist_eq, dist_eq_norm] using hwlt
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete huCauchy
  have hvNorm : ‖v‖ = 1 := by
    apply tendsto_nhds_unique (hv.norm)
    simpa only [huNorm] using tendsto_const_nhds
  have hvZero : Rt v = 0 := by
    apply tendsto_nhds_unique (Rt.continuous.continuousAt.tendsto.comp hv)
    exact hRConv
  have : v = 0 := hRtInj (by simpa using hvZero)
  rw [this, norm_zero] at hvNorm
  norm_num at hvNorm

omit [CompleteSpace Y] in
/-- Necessity half of compact--cofinal fusion. -/
theorem cofinalTransducer_of_compact_jointlyBoundedBelow
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hA : IsCompactOperator A) (hjoint : IsJointlyBoundedBelow A R) :
    IsCofinalTransducer R :=
  ⟨isClosed_range_of_compact_jointlyBoundedBelow A R hA hjoint,
    finiteDimensional_ker_of_compact_jointlyBoundedBelow A R hA hjoint⟩

/-- Closed cofinal range plus finite residual separation produces an exact common recovery map. -/
theorem exists_commonRecovery_of_cofinalTransducer
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hR : IsCofinalTransducer R)
    (hAker : ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0) :
    ∃ L : (Y × Z) →L[ℂ] H, ∀ x : H, L ((A.prod R) x) = x := by
  let K : Submodule ℂ H := LinearMap.ker (R : H →ₗ[ℂ] Z)
  let Rt : (Kᗮ : Submodule ℂ H) →L[ℂ] Z :=
    ContinuousLinearMap.transverseRestriction R
  have hRtInj : Function.Injective Rt :=
    ContinuousLinearMap.transverseRestriction_injective R
  have hRtClosed : IsClosed (Set.range Rt) := by
    rw [ContinuousLinearMap.range_transverseRestriction]
    exact hR.1
  letI : CompleteSpace Rt.range := hRtClosed.completeSpace_coe
  let RtInv : Rt.range →L[ℂ] (Kᗮ : Submodule ℂ H) :=
    Rt.leftInverse_of_injective_of_isClosed_range hRtInj hRtClosed
  let S : Z →L[ℂ] H :=
    (Kᗮ).subtypeL ∘L RtInv ∘L Rt.range.orthogonalProjectionOnto
  have hS (x : H) : S (R x) = (Kᗮ).starProjection x := by
    let xperp : (Kᗮ : Submodule ℂ H) := Kᗮ.orthogonalProjectionOnto x
    have hRsplit : Rt xperp = R x := by
      apply sub_eq_zero.mp
      change R (xperp : H) - R x = 0
      rw [← map_sub]
      apply LinearMap.mem_ker.mp
      change (xperp : H) - x ∈ K
      have hxsplit := K.starProjection_add_starProjection_orthogonal x
      change K.starProjection x + (xperp : H) = x at hxsplit
      rw [← hxsplit]
      simp
    have hmem : R x ∈ Rt.range := ⟨xperp, hRsplit⟩
    have hproj : Rt.range.orthogonalProjectionOnto (R x) = ⟨R x, hmem⟩ :=
      Rt.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨R x, hmem⟩
    change ((RtInv (Rt.range.orthogonalProjectionOnto (R x)) :
      (Kᗮ : Submodule ℂ H)) : H) = (Kᗮ).starProjection x
    rw [hproj]
    have hRtRangeInj : Function.Injective Rt.rangeRestrict := by
      intro a b hab
      exact hRtInj (congrArg Subtype.val hab)
    have hinv := Rt.rangeRestrict.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr hRtRangeInj) xperp
    have hInv : RtInv ⟨R x, hmem⟩ = xperp := by
      change Rt.rangeRestrict.leftInverse ⟨R x, hmem⟩ = xperp
      rw [show ⟨R x, hmem⟩ = Rt.rangeRestrict xperp by
        apply Subtype.ext
        exact hRsplit.symm]
      exact hinv
    simpa [xperp] using congrArg Subtype.val hInv
  let AK : K →L[ℂ] Y := A ∘L K.subtypeL
  have hAKInj : Function.Injective AK := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hAker ((x : H) - (y : H))
    · exact K.sub_mem x.property y.property
    · simpa [AK, map_sub] using sub_eq_zero.mpr hxy
  letI : FiniteDimensional ℂ K := hR.2
  letI : FiniteDimensional ℂ AK.range :=
    FiniteDimensional.of_surjective AK.toLinearMap.rangeRestrict (by
      intro y
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩)
  have hAKClosed : IsClosed (Set.range AK) := by
    exact AK.range.closed_of_finiteDimensional
  letI : CompleteSpace AK.range := hAKClosed.completeSpace_coe
  let AKInv : AK.range →L[ℂ] K :=
    AK.leftInverse_of_injective_of_isClosed_range hAKInj hAKClosed
  let J : Y →L[ℂ] H :=
    K.subtypeL ∘L AKInv ∘L AK.range.orthogonalProjectionOnto
  have hJ (x : K) : J (A x) = x := by
    have hmem : A x ∈ AK.range := ⟨x, rfl⟩
    have hproj : AK.range.orthogonalProjectionOnto (A x) = ⟨A x, hmem⟩ :=
      AK.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, hmem⟩
    change ((AKInv (AK.range.orthogonalProjectionOnto (A x)) : K) : H) = x
    rw [hproj]
    have hAKRangeInj : Function.Injective AK.rangeRestrict := by
      intro a b hab
      exact hAKInj (congrArg Subtype.val hab)
    have hinv := AK.rangeRestrict.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr hAKRangeInj) x
    have hInv : AKInv ⟨A x, hmem⟩ = x := by
      change AK.rangeRestrict.leftInverse ⟨A x, hmem⟩ = x
      rw [show ⟨A x, hmem⟩ = AK.rangeRestrict x by
        apply Subtype.ext
        rfl]
      exact hinv
    exact congrArg Subtype.val hInv
  let L : (Y × Z) →L[ℂ] H := J.coprod (S - J ∘L A ∘L S)
  refine ⟨L, ?_⟩
  intro x
  let u : K := K.orthogonalProjectionOnto x
  have hxsplit : (u : H) + (Kᗮ).starProjection x = x := by
    exact K.starProjection_add_starProjection_orthogonal x
  calc
    L ((A.prod R) x) = J (A x) + S (R x) - J (A (S (R x))) := by
      simp only [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
        sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
      abel
    _ = J (A x) + (Kᗮ).starProjection x -
        J (A ((Kᗮ).starProjection x)) := by rw [hS]
    _ = J (A u) + (Kᗮ).starProjection x := by
      have hxminus : x - (Kᗮ).starProjection x = (u : H) := by
        exact sub_eq_iff_eq_add.mpr hxsplit.symm
      calc
        J (A x) + (Kᗮ).starProjection x - J (A ((Kᗮ).starProjection x)) =
            J (A x - A ((Kᗮ).starProjection x)) + (Kᗮ).starProjection x := by
              rw [map_sub]
              abel
        _ = J (A u) + (Kᗮ).starProjection x := by rw [← map_sub, hxminus]
    _ = (u : H) + (Kᗮ).starProjection x := by rw [hJ]
    _ = x := hxsplit

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- Exact recovery gives a quantitative joint lower bound. -/
theorem jointlyBoundedBelow_of_commonRecovery
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (L : (Y × Z) →L[ℂ] H)
    (hL : ∀ x : H, L ((A.prod R) x) = x) :
    IsJointlyBoundedBelow A R := by
  let c : ℝ := (‖L‖ + 1)⁻¹
  have hden : 0 < ‖L‖ + 1 := by positivity
  refine ⟨c, inv_pos.mpr hden, ?_⟩
  intro x
  change (‖L‖ + 1)⁻¹ * ‖x‖ ≤ ‖(A.prod R) x‖
  rw [inv_mul_le_iff₀ hden]
  calc
    ‖x‖ = ‖L ((A.prod R) x)‖ := by rw [hL]
    _ ≤ ‖L‖ * ‖(A.prod R) x‖ := L.le_opNorm _
    _ ≤ (‖L‖ + 1) * ‖(A.prod R) x‖ := by
      gcongr
      norm_num

/-- Sufficiency half: a cofinal transducer plus finite residual separation reconstructs the source. -/
theorem jointlyBoundedBelow_of_cofinalTransducer
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hR : IsCofinalTransducer R)
    (hAker : ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0) :
    IsJointlyBoundedBelow A R := by
  obtain ⟨L, hL⟩ := exists_commonRecovery_of_cofinalTransducer A R hR hAker
  exact jointlyBoundedBelow_of_commonRecovery A R L hL

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- Joint observability separates the residual kernel of either reporter. -/
theorem separates_ker_of_jointlyBoundedBelow
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z)
    (hjoint : IsJointlyBoundedBelow A R) :
    ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0 := by
  obtain ⟨c, hc, hbound⟩ := hjoint
  intro x hxR hxA
  have h := hbound x
  have hxR0 : R x = 0 := hxR
  have hzero : ‖(A.prod R) x‖ = 0 := by
    simp [ContinuousLinearMap.prod_apply, hxA, hxR0]
  rw [hzero] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])

/-- **Compact--cofinal formation theorem.** A compact local packet and a retained cofinal packet
jointly reconstruct exactly when the cofinal packet has closed range and finite kernel and the
compact packet separates that residual kernel. -/
theorem compactCofinal_jointlyBoundedBelow_iff
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (hA : IsCompactOperator A) :
    IsJointlyBoundedBelow A R ↔
      IsCofinalTransducer R ∧
        ∀ x : H, x ∈ LinearMap.ker (R : H →ₗ[ℂ] Z) → A x = 0 → x = 0 := by
  constructor
  · intro hjoint
    exact ⟨cofinalTransducer_of_compact_jointlyBoundedBelow A R hA hjoint,
      separates_ker_of_jointlyBoundedBelow A R hjoint⟩
  · rintro ⟨hR, hsep⟩
    exact jointlyBoundedBelow_of_cofinalTransducer A R hR hsep

/-- Coordinate action on the compact local formation channel. -/
def transportLocalFormation (A : H →L[ℂ] Y)
    (U : H ≃L[ℂ] H) (V : Y ≃L[ℂ] Y) : H →L[ℂ] Y :=
  V.toContinuousLinearMap ∘L A ∘L U.symm.toContinuousLinearMap

/-- Coordinate action on the cofinal structural channel. -/
def transportCofinalFormation (R : H →L[ℂ] Z)
    (U : H ≃L[ℂ] H) (W : Z ≃L[ℂ] Z) : H →L[ℂ] Z :=
  W.toContinuousLinearMap ∘L R ∘L U.symm.toContinuousLinearMap

/-- Lift of a common recovery kernel through the same coordinate action. -/
def transportCommonRecovery (L : (Y × Z) →L[ℂ] H)
    (U : H ≃L[ℂ] H) (V : Y ≃L[ℂ] Y) (W : Z ≃L[ℂ] Z) :
    (Y × Z) →L[ℂ] H :=
  U.toContinuousLinearMap ∘L L ∘L (V.symm.prodCongr W.symm).toContinuousLinearMap

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- **Functional-equation information neutrality.** Any invertible coordinate action on source and
reporter spaces lifts through the common recovery kernel, so exact reconstructible information is
neither created nor destroyed. -/
theorem transportCommonRecovery_recovers
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (L : (Y × Z) →L[ℂ] H)
    (hL : ∀ x : H, L ((A.prod R) x) = x)
    (U : H ≃L[ℂ] H) (V : Y ≃L[ℂ] Y) (W : Z ≃L[ℂ] Z) :
    ∀ x : H,
      transportCommonRecovery L U V W
        (((transportLocalFormation A U V).prod (transportCofinalFormation R U W)) x) = x := by
  intro x
  simp only [transportCommonRecovery, transportLocalFormation, transportCofinalFormation,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  change U (L (V.symm (V (A (U.symm x))), W.symm (W (R (U.symm x))))) = x
  rw [V.symm_apply_apply, W.symm_apply_apply]
  have hrec := hL (U.symm x)
  simp only [ContinuousLinearMap.prod_apply] at hrec
  rw [hrec, U.apply_symm_apply]

/-- Structural carrier together with a scalar relative defect carried by the same transducer. -/
def carrierDefectPacket (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (delta : ℂ) :
    H →L[ℂ] ((Y × Z) × Z) :=
  (A.prod R).prod (delta • R)

/-- Recovery from the retained structural coordinates, independently of the defect coordinate. -/
def carrierDefectRecovery (L : (Y × Z) →L[ℂ] H) : ((Y × Z) × Z) →L[ℂ] H :=
  L ∘L ContinuousLinearMap.fst ℂ (Y × Z) Z

omit [CompleteSpace H] [CompleteSpace Y] [CompleteSpace Z] in
/-- **Carrier--defect bifurcation.** The relative defect may change or vanish while the common
recovery law remains exact because structural carrier and defect are distinct coordinates. -/
theorem carrierDefectRecovery_recovers
    (A : H →L[ℂ] Y) (R : H →L[ℂ] Z) (L : (Y × Z) →L[ℂ] H)
    (hL : ∀ x : H, L ((A.prod R) x) = x) (delta : ℂ) :
    ∀ x : H, carrierDefectRecovery L (carrierDefectPacket A R delta x) = x := by
  intro x
  simpa [carrierDefectRecovery, carrierDefectPacket, ContinuousLinearMap.prod_apply] using hL x

end

end GaloisForLFunctions.HTGeometry
