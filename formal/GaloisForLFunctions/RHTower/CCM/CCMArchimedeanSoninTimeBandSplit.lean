import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninToeplitzKernel
import GaloisForLFunctions.RHTower.SoninTimeBandSchatten

/-!
# The generic Sonin part as a positive part minus the time-band part

At cutoff one let `P`, `P̂` be the physical and Fourier cutoffs on `L²(ℝ)^ev`, `Q = 1 - P`,
`Q̂ = 1 - P̂`, and `S` the Sonin projection.  The generic part splits as

`G = M - A`,   `M = Q Q̂ Q - S`,   `A = P P̂ + P̂ P - P P̂ P`.

* `M ≥ 0`: `⟨v, M v⟩ = ‖Q̂ Q v‖² - ‖S v‖²` and `S v = S Q̂ Q v`.
* `A` is trace class (time-band products), hence so is `M = G + A`.
* For every bounded `T`, `Re Tr(T G T†) ≥ -Re Tr(T A T†)`.
* `Re Tr(M ϑ_u) ≤ Tr M`, since `2 - ϑ_u - ϑ_u† = (1 - ϑ_u)(1 - ϑ_u)†`; with `Tr G = 0` this gives
  `Re Tr(G ϑ_u) ≤ Re Tr A - Re Tr(A ϑ_u)`.
* For `u ≥ 0` the scaling `ϑ_u` enlarges supports, `P ϑ_u P = P ϑ_u`, so
  `Tr(A ϑ_u) = Tr(P P̂ ϑ_u)`.
-/

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

local notation "Pc" => evenIndicatorCutoff 1
local notation "Rc" => evenFourierCutoff 1
local notation "Sc" => evenCentralSoninProjection 1

/-- The time-band part `A = P P̂ + P̂ P - P P̂ P`. -/
def ccmSoninTimeBandPart : evenSubspace →L[ℂ] evenSubspace :=
  Pc * Rc + Rc * Pc - Pc * Rc * Pc

/-- The positive part `M = Q Q̂ Q - S`. -/
def ccmSoninGenericPositivePart : evenSubspace →L[ℂ] evenSubspace :=
  (1 - Pc) * (1 - Rc) * (1 - Pc) - Sc

local notation "Mp" => ccmSoninGenericPositivePart

/-- **`G = M - A`.** -/
theorem ccmSoninGenericPartAt_one_eq :
    ccmSoninGenericPartAt 1 = ccmSoninGenericPositivePart - ccmSoninTimeBandPart := by
  simp only [ccmSoninGenericPartAt, ccmSoninGenericPositivePart, ccmSoninTimeBandPart, mul_sub,
    sub_mul, one_mul, mul_one, evenIndicatorCutoff_mul_self]
  abel

/-! ## Positivity of `M` -/

/-- For a self-adjoint idempotent `E`, `⟨x, E y⟩ = ⟨E x, E y⟩`. -/
theorem inner_apply_eq_of_adjoint_eq_of_mul_self {E : evenSubspace →L[ℂ] evenSubspace}
    (hadj : ContinuousLinearMap.adjoint E = E) (hidem : E * E = E) (x y : evenSubspace) :
    ⟪x, E y⟫_ℂ = ⟪E x, E y⟫_ℂ := by
  have h := ContinuousLinearMap.adjoint_inner_left E (E y) x
  rw [hadj] at h
  rw [h]
  change ⟪x, E y⟫_ℂ = ⟪x, (E * E) y⟫_ℂ
  rw [hidem]

theorem adjoint_one_sub_evenIndicatorCutoff :
    ContinuousLinearMap.adjoint (1 - Pc) = 1 - Pc :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp ((IsSelfAdjoint.one _).sub
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenIndicatorCutoff 1)))

theorem adjoint_one_sub_evenFourierCutoff :
    ContinuousLinearMap.adjoint (1 - Rc) = 1 - Rc :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mp ((IsSelfAdjoint.one _).sub
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenFourierCutoff 1)))

theorem one_sub_evenIndicatorCutoff_mul_self : (1 - Pc) * (1 - Pc) = 1 - Pc := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, evenIndicatorCutoff_mul_self]
  abel

theorem one_sub_evenFourierCutoff_mul_self : (1 - Rc) * (1 - Rc) = 1 - Rc := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, evenFourierCutoff_mul_self]
  abel

/-- `S Q̂ Q = S`. -/
theorem evenCentralSoninProjection_mul_complements : Sc * (1 - Rc) * (1 - Pc) = Sc := by
  rw [mul_sub Sc, mul_one, evenCentralSoninProjection_mul_evenFourierCutoff, sub_zero, mul_sub,
    mul_one, evenCentralSoninProjection_mul_evenIndicatorCutoff, sub_zero]

/-- **`M ≥ 0`.** -/
theorem re_inner_ccmSoninGenericPositivePart_nonneg (v : evenSubspace) :
    0 ≤ (⟪v, ccmSoninGenericPositivePart v⟫_ℂ).re := by
  set w := (1 - Rc) ((1 - Pc) v)
  have hQ : ⟪v, ((1 - Pc) * (1 - Rc) * (1 - Pc)) v⟫_ℂ = ⟪w, w⟫_ℂ := by
    have h1 := ContinuousLinearMap.adjoint_inner_left (1 - Pc) ((1 - Rc) ((1 - Pc) v)) v
    rw [adjoint_one_sub_evenIndicatorCutoff] at h1
    change ⟪v, (1 - Pc) ((1 - Rc) ((1 - Pc) v))⟫_ℂ = _
    rw [← h1]
    exact inner_apply_eq_of_adjoint_eq_of_mul_self adjoint_one_sub_evenFourierCutoff
      one_sub_evenFourierCutoff_mul_self _ _
  have hS : ⟪v, Sc v⟫_ℂ = ⟪Sc v, Sc v⟫_ℂ :=
    inner_apply_eq_of_adjoint_eq_of_mul_self (adjoint_evenCentralSoninProjection 1)
      (evenCentralSoninProjection_mul_self 1) _ _
  have hSw : Sc v = Sc w := by
    change Sc v = (Sc * (1 - Rc) * (1 - Pc)) v
    rw [evenCentralSoninProjection_mul_complements]
  have hle : ‖Sc w‖ ≤ ‖w‖ := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact Submodule.norm_starProjection_apply_le _ w
  have h1 : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by exact inner_self_eq_norm_sq (𝕜 := ℂ) w
  have h2 : (⟪Sc w, Sc w⟫_ℂ).re = ‖Sc w‖ ^ 2 := by exact inner_self_eq_norm_sq (𝕜 := ℂ) (Sc w)
  rw [ccmSoninGenericPositivePart, _root_.sub_apply, inner_sub_right, hQ, hS, hSw,
    Complex.sub_re, h1, h2]
  nlinarith [norm_nonneg (Sc w)]

theorem adjoint_ccmSoninGenericPositivePart :
    ContinuousLinearMap.adjoint ccmSoninGenericPositivePart = ccmSoninGenericPositivePart := by
  have hQ := ContinuousLinearMap.isSelfAdjoint_iff'.mpr adjoint_one_sub_evenIndicatorCutoff
  have hR := ContinuousLinearMap.isSelfAdjoint_iff'.mpr adjoint_one_sub_evenFourierCutoff
  have hS := ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenCentralSoninProjection 1)
  have hQRQ := hR.conjugate (1 - Pc)
  rw [hQ.star_eq] at hQRQ
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mp (hQRQ.sub hS)

/-! ## Trace-class membership -/

theorem memSchattenClass_one_sub' {S T : evenSubspace →L[ℂ] evenSubspace}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (S - T) := by
  have hT' := memSchattenClass_one_smul hT (-1)
  rw [neg_one_smul] at hT'
  rw [sub_eq_add_neg]
  exact memSchattenClass_one_add (hS.isCompactOperator one_pos) (hT'.isCompactOperator one_pos)
    hS hT'

theorem memSchattenClass_one_add' {S T : evenSubspace →L[ℂ] evenSubspace}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (S + T) :=
  memSchattenClass_one_add (hS.isCompactOperator one_pos) (hT.isCompactOperator one_pos) hS hT

/-- `P P̂` is trace class on the even carrier. -/
theorem memSchattenClass_one_evenIndicatorCutoff_mul_evenFourierCutoff :
    MemSchattenClass 1 (Pc * Rc) := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1) *
      fourierCutoff (centralInterval 1) (measurableSet_centralInterval 1)
  have hmap : Set.MapsTo T evenSubspace evenSubspace := fun f hf =>
    indicatorCutoff_central_mapsTo_evenSubspace 1 (fourierCutoff_central_mapsTo_evenSubspace 1 hf)
  have hr := memSchattenClass_one_restrict evenSubspace T hmap
    (memSchattenClass_one_indicatorCutoff_fourierCutoff_central 1 1 one_pos)
  convert hr using 1
  exact ContinuousLinearMap.ext fun f => Subtype.ext rfl

/-- `P̂ P` is trace class on the even carrier. -/
theorem memSchattenClass_one_evenFourierCutoff_mul_evenIndicatorCutoff :
    MemSchattenClass 1 (Rc * Pc) := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    fourierCutoff (centralInterval 1) (measurableSet_centralInterval 1) *
      indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
  have hmap : Set.MapsTo T evenSubspace evenSubspace := fun f hf =>
    fourierCutoff_central_mapsTo_evenSubspace 1 (indicatorCutoff_central_mapsTo_evenSubspace 1 hf)
  have hr := memSchattenClass_one_restrict evenSubspace T hmap
    (memSchattenClass_one_fourierCutoff_indicatorCutoff_central 1 1 one_pos)
  convert hr using 1
  exact ContinuousLinearMap.ext fun f => Subtype.ext rfl

theorem memSchattenClass_one_ccmSoninTimeBandPart : MemSchattenClass 1 ccmSoninTimeBandPart :=
  memSchattenClass_one_sub'
    (memSchattenClass_one_add' memSchattenClass_one_evenIndicatorCutoff_mul_evenFourierCutoff
      memSchattenClass_one_evenFourierCutoff_mul_evenIndicatorCutoff)
    (memSchattenClass_one_comp_right memSchattenClass_one_evenIndicatorCutoff_mul_evenFourierCutoff
      Pc)

theorem memSchattenClass_one_ccmSoninGenericPositivePart :
    MemSchattenClass 1 ccmSoninGenericPositivePart := by
  have h : ccmSoninGenericPositivePart = ccmSoninGenericPartAt 1 + ccmSoninTimeBandPart := by
    rw [ccmSoninGenericPartAt_one_eq]
    abel
  rw [h]
  exact memSchattenClass_one_add' (memSchattenClass_one_ccmSoninGenericPartAt one_pos)
    memSchattenClass_one_ccmSoninTimeBandPart

/-! ## Trace inequalities -/

/-- `Re Tr(T M T†) ≥ 0` for every bounded `T`: the diagonal of `T M T†` is `⟨T† b, M T† b⟩`. -/
theorem re_opTrace_conj_ccmSoninGenericPositivePart_nonneg
    (T : evenSubspace →L[ℂ] evenSubspace) :
    0 ≤ (opTrace (T ∘L ccmSoninGenericPositivePart ∘L ContinuousLinearMap.adjoint T)).re := by
  have hX : MemSchattenClass 1 (T ∘L ccmSoninGenericPositivePart ∘L ContinuousLinearMap.adjoint T) :=
    memSchattenClass_one_comp_left
      (memSchattenClass_one_comp_right memSchattenClass_one_ccmSoninGenericPositivePart _) T
  unfold opTrace
  rw [Complex.re_tsum hX.one_summable_inner_diag]
  refine tsum_nonneg fun i => ?_
  rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left]
  exact re_inner_ccmSoninGenericPositivePart_nonneg _

theorem opTrace_conj_sub {T X Y : evenSubspace →L[ℂ] evenSubspace}
    (hX : MemSchattenClass 1 X) (hY : MemSchattenClass 1 Y) :
    opTrace (T ∘L (X - Y) ∘L ContinuousLinearMap.adjoint T) =
      opTrace (T ∘L X ∘L ContinuousLinearMap.adjoint T) -
        opTrace (T ∘L Y ∘L ContinuousLinearMap.adjoint T) := by
  have hX' := memSchattenClass_one_comp_left (memSchattenClass_one_comp_right hX
    (ContinuousLinearMap.adjoint T)) T
  have hY' := memSchattenClass_one_comp_left (memSchattenClass_one_comp_right hY
    (ContinuousLinearMap.adjoint T)) T
  rw [← opTrace_sub_of_mem (isTraceClass_mem_hsTraceIdeal hX'.one_isTraceClass)
    (isTraceClass_mem_hsTraceIdeal hY'.one_isTraceClass)]
  congr 1
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- **Generic trace bounded below by the time-band trace.**
`Re Tr(T G T†) ≥ -Re Tr(T A T†)`. -/
theorem neg_re_opTrace_conj_ccmSoninTimeBandPart_le (T : evenSubspace →L[ℂ] evenSubspace) :
    -(opTrace (T ∘L ccmSoninTimeBandPart ∘L ContinuousLinearMap.adjoint T)).re ≤
      (opTrace (T ∘L ccmSoninGenericPartAt 1 ∘L ContinuousLinearMap.adjoint T)).re := by
  rw [ccmSoninGenericPartAt_one_eq, opTrace_conj_sub memSchattenClass_one_ccmSoninGenericPositivePart
    memSchattenClass_one_ccmSoninTimeBandPart, Complex.sub_re]
  linarith [re_opTrace_conj_ccmSoninGenericPositivePart_nonneg T]

theorem ccmScalingTrace_sub {X Y : evenSubspace →L[ℂ] evenSubspace}
    (hX : MemSchattenClass 1 X) (hY : MemSchattenClass 1 Y) (u : ℝ) :
    ccmScalingTrace (X - Y) u = ccmScalingTrace X u - ccmScalingTrace Y u := by
  unfold ccmScalingTrace
  rw [← opTrace_sub_of_mem
    (isTraceClass_mem_hsTraceIdeal (memSchattenClass_one_comp_right hX _).one_isTraceClass)
    (isTraceClass_mem_hsTraceIdeal (memSchattenClass_one_comp_right hY _).one_isTraceClass),
    ContinuousLinearMap.sub_comp]

/-- `ϑ_u ϑ_u† = 1`. -/
theorem ccmLogDilation_comp_adjoint (u : ℝ) :
    ccmLogDilation u ∘L ContinuousLinearMap.adjoint (ccmLogDilation u) =
      ContinuousLinearMap.id ℂ evenSubspace := by
  rw [adjoint_ccmLogDilation, ccmLogDilation_comp, add_neg_cancel, ccmLogDilation_zero]

/-- **`Re Tr(M ϑ_u) ≤ Tr M`**, from `Re Tr((1 - ϑ_u) M (1 - ϑ_u)†) ≥ 0`. -/
theorem re_ccmScalingTrace_ccmSoninGenericPositivePart_le (u : ℝ) :
    (ccmScalingTrace Mp u).re ≤ (ccmScalingTrace Mp 0).re := by
  have hM := memSchattenClass_one_ccmSoninGenericPositivePart
  have hpos := re_opTrace_conj_ccmSoninGenericPositivePart_nonneg
    (ContinuousLinearMap.id ℂ evenSubspace - ccmLogDilation u)
  have hexp : (ContinuousLinearMap.id ℂ evenSubspace - ccmLogDilation u) ∘L Mp ∘L
      ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ evenSubspace - ccmLogDilation u) =
        Mp - ccmLogDilation u ∘L Mp - Mp ∘L ccmLogDilation (-u) +
          ccmLogDilation u ∘L Mp ∘L ccmLogDilation (-u) := by
    rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_id,
      adjoint_ccmLogDilation]
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    abel
  have mem : ∀ {X : evenSubspace →L[ℂ] evenSubspace}, MemSchattenClass 1 X →
      X ∈ hsTraceIdeal evenSubspace := fun h => isTraceClass_mem_hsTraceIdeal h.one_isTraceClass
  have hVM := memSchattenClass_one_comp_left hM (ccmLogDilation u)
  have hMV := memSchattenClass_one_comp_right hM (ccmLogDilation (-u))
  have hVMV := memSchattenClass_one_comp_left hMV (ccmLogDilation u)
  rw [hexp, opTrace_add_of_mem (sub_mem (sub_mem (mem hM) (mem hVM)) (mem hMV)) (mem hVMV),
    opTrace_sub_of_mem (sub_mem (mem hM) (mem hVM)) (mem hMV),
    opTrace_sub_of_mem (mem hM) (mem hVM)] at hpos
  have h1 : opTrace (ccmLogDilation u ∘L Mp) = ccmScalingTrace Mp u :=
    hM.one_opTrace_comp_comm _
  have h2 : opTrace (Mp ∘L ccmLogDilation (-u)) = conj (ccmScalingTrace Mp u) := by
    rw [conj_ccmScalingTrace hM, adjoint_ccmSoninGenericPositivePart]
    rfl
  have h3 : opTrace (ccmLogDilation u ∘L Mp ∘L ccmLogDilation (-u)) = ccmScalingTrace Mp 0 := by
    rw [hMV.one_opTrace_comp_comm, ContinuousLinearMap.comp_assoc, ccmLogDilation_comp,
      neg_add_cancel]
    rfl
  have h0 : opTrace Mp = ccmScalingTrace Mp 0 := by
    rw [ccmScalingTrace, ccmLogDilation_zero, ContinuousLinearMap.comp_id]
  rw [h1, h2, h3, h0] at hpos
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re] at hpos
  linarith

/-- **`Re Tr(G ϑ_u) ≤ Re Tr(A ϑ_0) - Re Tr(A ϑ_u)`.** -/
theorem re_ccmSoninToeplitzKernel_le (u : ℝ) :
    (ccmSoninToeplitzKernel 1 u).re ≤
      (ccmScalingTrace ccmSoninTimeBandPart 0).re - (ccmScalingTrace ccmSoninTimeBandPart u).re := by
  have hsplit : ∀ v, ccmSoninToeplitzKernel 1 v =
      ccmScalingTrace ccmSoninGenericPositivePart v - ccmScalingTrace ccmSoninTimeBandPart v := by
    intro v
    rw [ccmSoninToeplitzKernel, ccmSoninGenericPartAt_one_eq,
      ccmScalingTrace_sub memSchattenClass_one_ccmSoninGenericPositivePart
        memSchattenClass_one_ccmSoninTimeBandPart]
  have h0 := ccmSoninToeplitzKernel_zero (Λ := 1) one_pos
  rw [hsplit] at h0
  have hM0 : ccmScalingTrace ccmSoninGenericPositivePart 0 =
      ccmScalingTrace ccmSoninTimeBandPart 0 := sub_eq_zero.mp h0
  rw [hsplit, Complex.sub_re]
  have := re_ccmScalingTrace_ccmSoninGenericPositivePart_le u
  rw [hM0] at this
  linarith

/-! ## Support enlargement: `P ϑ_u P = P ϑ_u` for `u ≥ 0` -/

theorem ccmLogDilation_eq_evenDilationCLM (u : ℝ) :
    ccmLogDilation u = evenDilationCLM (Real.exp (-u)) (Real.exp_pos (-u)) := rfl

/-- For `u ≥ 0`, `P ϑ_u P = P ϑ_u`. -/
theorem evenIndicatorCutoff_mul_ccmLogDilation_mul_evenIndicatorCutoff {u : ℝ} (hu : 0 ≤ u) :
    Pc * ccmLogDilation u * Pc = Pc * ccmLogDilation u := by
  have h := evenIndicatorCutoff_mul_evenDilationCLM 1 (Real.exp (-u)) (Real.exp_pos (-u))
  rw [mul_one] at h
  have hle : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  rw [ccmLogDilation_eq_evenDilationCLM, h, mul_assoc,
    evenIndicatorCutoff_mul_of_le _ _ hle]

/-- **For `u ≥ 0`, `Tr(A ϑ_u) = Tr(P P̂ ϑ_u)`.** -/
theorem ccmScalingTrace_ccmSoninTimeBandPart_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    ccmScalingTrace ccmSoninTimeBandPart u = ccmScalingTrace (Pc * Rc) u := by
  have hPR := memSchattenClass_one_evenIndicatorCutoff_mul_evenFourierCutoff
  have hRP := memSchattenClass_one_evenFourierCutoff_mul_evenIndicatorCutoff
  have hPRP : MemSchattenClass 1 (Pc * Rc * Pc) := memSchattenClass_one_comp_right hPR Pc
  have hadd : ccmScalingTrace (Pc * Rc + Rc * Pc) u =
      ccmScalingTrace (Pc * Rc) u + ccmScalingTrace (Rc * Pc) u := by
    unfold ccmScalingTrace
    rw [ContinuousLinearMap.add_comp, opTrace_add_of_memSchattenClass_one
      (memSchattenClass_one_comp_right hPR _) (memSchattenClass_one_comp_right hRP _)]
  -- `Tr(P̂ P ϑ_u) = Tr(P̂ P ϑ_u P) = Tr(P P̂ P ϑ_u)`
  have hRP_eq : ccmScalingTrace (Rc * Pc) u = ccmScalingTrace (Pc * Rc * Pc) u := by
    have hX : MemSchattenClass 1 (Rc * Pc * ccmLogDilation u) :=
      memSchattenClass_one_comp_right hRP _
    calc ccmScalingTrace (Rc * Pc) u = opTrace (Rc * (Pc * ccmLogDilation u)) := by
          rw [ccmScalingTrace]
          change opTrace ((Rc * Pc) * ccmLogDilation u) = _
          rw [mul_assoc]
      _ = opTrace (Rc * (Pc * ccmLogDilation u * Pc)) := by
          rw [evenIndicatorCutoff_mul_ccmLogDilation_mul_evenIndicatorCutoff hu]
      _ = opTrace (Rc * Pc * ccmLogDilation u * Pc) := by simp only [mul_assoc]
      _ = opTrace (Pc * (Rc * Pc * ccmLogDilation u)) := (hX.one_opTrace_comp_comm Pc).symm
      _ = ccmScalingTrace (Pc * Rc * Pc) u := by
          rw [ccmScalingTrace]
          change _ = opTrace ((Pc * Rc * Pc) * ccmLogDilation u)
          simp only [mul_assoc]
  rw [ccmSoninTimeBandPart, ccmScalingTrace_sub (memSchattenClass_one_add' hPR hRP) hPRP, hadd,
    hRP_eq]
  ring

end RHTower
