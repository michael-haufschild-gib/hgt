import GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona
import GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace
import GaloisForLFunctions.HTGeometry.TraceOneDensityPurity

/-!
# The purification–boundary-transfer interchange anomaly

Let `T` be a positive injective trace-one operator with a pure purification `P = |Ψ⟩⟨Ψ|`,
`Tr_R P = T`, and let `E_ε(X) = X(εI + X)⁻¹` be the singular boundary transfer.  Completing and
then closing the source record gives `Tr_R E_ε(cP) = c/(ε+c) T`, because `P² = P`; closing and then
completing gives `E_ε(cT)`.  The interchange anomaly is
`𝒜_{ε,c}(T) = E_ε(cT) - c/(ε+c) T`.

* **(PBTIA-A)** `𝒜_{ε,c}(T) ≥ 0`, with spectral symbol `c²λ(1-λ)/((ε+cλ)(ε+c))`; the residual
  `E_ε(cT) - 𝒜 = c/(ε+c) T` tends to `T` in trace norm.
* **(PBTIA-B)** `𝒜_{ε,c}(T) → I - T` strongly for every `c`, but in the boundary corona
  `‖[𝒜_{•,c}] - [𝒜_{•,d}]‖ = |√c - √d|/(√c + √d)`, so `[𝒜_{•,c}] = [𝒜_{•,d}]` iff `c = d`.
* **(PBTIA-C)** the residuals of all scales have the same trace-norm boundary `T`.
-/

open Filter Topology Set
open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower GaloisForLFunctions.RHTower

/-! ## Completion of a pure state and closure of the source record -/

section Pure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Boundary transfer of a scaled orthogonal projection: `E_ε(cP) = c/(ε+c) P`. -/
theorem positiveBoundaryTransfer_smul_of_idempotent {P : E →L[ℂ] E} (hP : P.IsPositive)
    (hidem : P ∘L P = P) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    positiveBoundaryTransfer (c • P) ε = (c / (ε + c)) • P := by
  have hid : IsIdempotentElem P := by
    rw [IsIdempotentElem, ContinuousLinearMap.mul_def, hidem]
  have hsub := hid.spectrum_subset ℝ
  have hsa : IsSelfAdjoint P := hP.isSelfAdjoint
  rw [positiveBoundaryTransfer_smul hP hc hε, positiveBoundaryTransfer,
    cfc_congr (g := fun x : ℝ => (c / (ε + c)) * x), cfc_const_mul_id (c / (ε + c)) P]
  intro x hx
  rcases hsub hx with h | h
  · rw [h]
    simp
  · rw [Set.mem_singleton_iff.1 h]
    simp only [mul_one]
    field_simp

omit [CompleteSpace E] in
theorem rankOne_comp_rankOne_self_of_norm_eq_one {Ψ : E} (hΨ : ‖Ψ‖ = 1) :
    rankOne ℂ Ψ Ψ ∘L rankOne ℂ Ψ Ψ = rankOne ℂ Ψ Ψ := by
  rw [rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K, hΨ]
  simp

/-- **(PBTIA.5), completion of the pure source.**  `E_ε(c|Ψ⟩⟨Ψ|) = c/(ε+c) |Ψ⟩⟨Ψ|`. -/
theorem positiveBoundaryTransfer_smul_rankOne_self {Ψ : E} (hΨ : ‖Ψ‖ = 1) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) :
    positiveBoundaryTransfer (c • rankOne ℂ Ψ Ψ) ε = (c / (ε + c)) • rankOne ℂ Ψ Ψ :=
  positiveBoundaryTransfer_smul_of_idempotent (isPositive_rankOne_self Ψ)
    (rankOne_comp_rankOne_self_of_norm_eq_one hΨ) hc hε

end Pure

section PartialTrace

variable {ι : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Closing the source record is linear: `Tr_R(rX) = r Tr_R X`. -/
theorem IsPartialTrace.real_smul {X : lp (fun _ : ι => K) 2 →L[ℂ] lp (fun _ : ι => K) 2}
    {R : K →L[ℂ] K} (h : IsPartialTrace X R) (r : ℝ) : IsPartialTrace (r • X) (r • R) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r X, RCLike.real_smul_eq_coe_smul (K := ℂ) r R]
  refine ⟨memSchattenClass_one_smul h.1 _, fun B => ?_⟩
  rw [smul_comp, smul_comp, RHTower.opTrace_smul, RHTower.opTrace_smul, h.2 B]

/-- **(PBTIA.4)–(PBTIA.5).**  For a unit purification `Tr_R |Ψ⟩⟨Ψ| = T`, closing the dilated
source gives `cT`, while closing its completion gives `c/(ε+c) T`. -/
theorem isPartialTrace_completion_square {Ψ : lp (fun _ : ι => K) 2} (hΨ : ‖Ψ‖ = 1)
    {T : K →L[ℂ] K} (h : IsPartialTrace (rankOne ℂ Ψ Ψ) T) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    IsPartialTrace (c • rankOne ℂ Ψ Ψ) (c • T) ∧
      IsPartialTrace (positiveBoundaryTransfer (c • rankOne ℂ Ψ Ψ) ε) ((c / (ε + c)) • T) := by
  refine ⟨h.real_smul c, ?_⟩
  have key := positiveBoundaryTransfer_smul_rankOne_self hΨ hc hε
  rw [show positiveBoundaryTransfer (c • rankOne ℂ Ψ Ψ) ε = (c / (ε + c)) • rankOne ℂ Ψ Ψ
    from key]
  exact h.real_smul _

end PartialTrace

/-! ## The interchange anomaly -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interchange anomaly `𝒜_{ε,c}(T) = E_ε(cT) - c/(ε+c) T`. -/
def interchangeAnomaly (T : H →L[ℂ] H) (c ε : ℝ) : H →L[ℂ] H :=
  positiveBoundaryTransfer (c • T) ε - (c / (ε + c)) • T

/-- **(PBTIA.6).**  The anomaly is the defect of the completion/closure square: completing after
closing minus closing after completing. -/
theorem interchangeAnomaly_eq_square {ι : Type*} {Ψ : lp (fun _ : ι => H) 2} (hΨ : ‖Ψ‖ = 1)
    {T : H →L[ℂ] H} (h : IsPartialTrace (rankOne ℂ Ψ Ψ) T) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    {R₁ R₂ : H →L[ℂ] H} (h₁ : IsPartialTrace (c • rankOne ℂ Ψ Ψ) R₁)
    (h₂ : IsPartialTrace (positiveBoundaryTransfer (c • rankOne ℂ Ψ Ψ) ε) R₂) :
    interchangeAnomaly T c ε = positiveBoundaryTransfer R₁ ε - R₂ := by
  obtain ⟨hs₁, hs₂⟩ := isPartialTrace_completion_square hΨ h hc hε
  rw [h₁.unique hs₁, h₂.unique hs₂, interchangeAnomaly]

/-- **(PBTIA.8).**  Subtracting the anomaly leaves the residual `c/(ε+c) T`. -/
theorem positiveBoundaryTransfer_sub_interchangeAnomaly (T : H →L[ℂ] H) (c ε : ℝ) :
    positiveBoundaryTransfer (c • T) ε - interchangeAnomaly T c ε = (c / (ε + c)) • T :=
  sub_sub_cancel _ _

/-- The anomaly symbol `λ/(ε/c + λ) - c/(ε+c) λ = c²λ(1-λ)/((ε+cλ)(ε+c))`. -/
theorem anomalySymbol_eq {c ε x : ℝ} (hc : 0 < c) (hε : 0 < ε) (hx : 0 ≤ x) :
    x / (ε / c + x) - c / (ε + c) * x =
      c ^ 2 * x * (1 - x) / ((ε + c * x) * (ε + c)) := by
  have h1 : 0 < ε + c * x := by positivity
  have h2 : 0 < ε / c + x := by positivity
  rw [div_add' _ _ _ hc.ne', div_div_eq_mul_div]
  field_simp
  ring

/-- **(PBTIA.10).**  The anomaly symbol is nonnegative on `[0, 1]`. -/
theorem anomalySymbol_nonneg {c ε x : ℝ} (hc : 0 < c) (hε : 0 < ε) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x / (ε / c + x) - c / (ε + c) * x := by
  rw [anomalySymbol_eq hc hε hx0]
  have : 0 ≤ 1 - x := by linarith
  positivity

theorem interchangeAnomaly_eq_cfc {T : H →L[ℂ] H} (hT : T.IsPositive) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) :
    interchangeAnomaly T c ε = cfc (fun x : ℝ => x / (ε / c + x) - c / (ε + c) * x) T := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hsa : IsSelfAdjoint T := hT.isSelfAdjoint
  rw [interchangeAnomaly, positiveBoundaryTransfer_smul hT hc hε, positiveBoundaryTransfer,
    cfc_sub (fun x : ℝ => x / (ε / c + x)) (fun x : ℝ => c / (ε + c) * x) T
      (continuousOn_transferSymbol (fun x hx => (hspec hx).1) (by positivity)) (by fun_prop),
    cfc_const_mul_id (c / (ε + c)) T]

/-- **(PBTIA.1).**  A positive trace-one density satisfies `0 ≤ T ≤ I`. -/
theorem isPositive_one_sub_of_norm_le_one {T : H →L[ℂ] H} (hT : T.IsPositive) (hn : ‖T‖ ≤ 1) :
    (1 - T).IsPositive := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hsa : IsSelfAdjoint T := hT.isSelfAdjoint
  have h : 0 ≤ cfc (fun x : ℝ => 1 - x) T :=
    cfc_nonneg fun x hx => by linarith [(hspec hx).2]
  rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x) T, cfc_const (1 : ℝ) T, cfc_id' ℝ T,
    map_one] at h
  exact (nonneg_iff_isPositive _).1 h

/-- **Theorem PBTIA-A, (PBTIA.7).**  The interchange anomaly of a positive contraction is
positive. -/
theorem interchangeAnomaly_isPositive {T : H →L[ℂ] H} (hT : T.IsPositive) (hn : ‖T‖ ≤ 1)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : (interchangeAnomaly T c ε).IsPositive := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hsa : IsSelfAdjoint T := hT.isSelfAdjoint
  rw [← nonneg_iff_isPositive, interchangeAnomaly_eq_cfc hT hc hε]
  exact cfc_nonneg fun x hx => anomalySymbol_nonneg hc hε (hspec hx).1 ((hspec hx).2.trans hn)

/-- **(PBTIA.11).**  `‖c/(ε+c) T - T‖₁ = ε/(ε+c) ‖T‖₁`. -/
theorem traceNorm_residual_sub (T : H →L[ℂ] H) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    traceNorm H ((c / (ε + c)) • T - T) = ε / (ε + c) * traceNorm H T := by
  have h1 : (c / (ε + c)) • T - T = (-(ε / (ε + c))) • T := by
    rw [show -(ε / (ε + c)) = c / (ε + c) - 1 by field_simp; ring, sub_smul, one_smul]
  rw [h1, RCLike.real_smul_eq_coe_smul (K := ℂ), traceNorm_smul, RCLike.norm_ofReal, abs_neg,
    abs_of_pos (by positivity)]

/-- **(PBTIA.9).**  The residual `c/(ε+c) T` tends to `T` in trace norm. -/
theorem tendsto_traceNorm_residual_sub (T : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => traceNorm H ((c / (ε + c)) • T - T)) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ => ε / (ε + c) * traceNorm H T) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => ε / (ε + c) * traceNorm H T) 0 :=
      (continuousAt_id.div (continuousAt_id.add continuousAt_const) (by simpa using hc.ne')).mul
        continuousAt_const
    simpa using hcont.tendsto
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (traceNorm_residual_sub T hc hε).symm

/-- **Theorem PBTIA-C, (PBTIA.18).**  The residuals of two scales merge in trace norm. -/
theorem tendsto_traceNorm_residual_sub_residual (T : H →L[ℂ] H) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) :
    Tendsto (fun ε => traceNorm H ((c / (ε + c)) • T - (d / (ε + d)) • T)) (𝓝[>] 0) (𝓝 0) := by
  have heq : ∀ ε : ℝ, traceNorm H ((c / (ε + c)) • T - (d / (ε + d)) • T) =
      |c / (ε + c) - d / (ε + d)| * traceNorm H T := fun ε => by
    rw [← sub_smul, RCLike.real_smul_eq_coe_smul (K := ℂ), traceNorm_smul, RCLike.norm_ofReal]
  simp_rw [heq]
  have hcont : ContinuousAt (fun ε : ℝ => |c / (ε + c) - d / (ε + d)| * traceNorm H T) 0 :=
    (((continuousAt_const.div (continuousAt_id.add continuousAt_const)
      (by simpa using hc.ne')).sub (continuousAt_const.div (continuousAt_id.add continuousAt_const)
        (by simpa using hd.ne'))).abs).mul continuousAt_const
  have h0 : |c / (0 + c) - d / (0 + d)| * traceNorm H T = 0 := by
    rw [zero_add, zero_add, div_self hc.ne', div_self hd.ne', sub_self, abs_zero, zero_mul]
  have := hcont.tendsto
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **Theorem PBTIA-B, (PBTIA.12).**  For injective `T` the anomaly tends strongly to `I - T`. -/
theorem tendsto_interchangeAnomaly_apply {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hinj : Function.Injective T) {c : ℝ} (hc : 0 < c) (v : H) :
    Tendsto (fun ε => interchangeAnomaly T c ε v) (𝓝[>] 0) (𝓝 (v - T v)) := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
  have hcT := isPositive_real_smul hT hc.le
  have hinj' : Function.Injective (c • T) := fun x y hxy => by
    have h : c • T x = c • T y := hxy
    exact hinj (smul_right_injective H hc.ne' h)
  have hF := positiveBoundaryTransfer_tendsto_id hcT.isSelfAdjoint hinj'
    (spectrum_subset_Icc_of_isPositive hcT) v
  have hcoef : Tendsto (fun ε : ℝ => c / (ε + c)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun ε : ℝ => c / (ε + c)) 0 :=
      continuousAt_const.div (continuousAt_id.add continuousAt_const) (by simpa using hc.ne')
    have := hcont.tendsto
    rw [zero_add, div_self hc.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun ε : ℝ => (c / (ε + c)) • T v) (𝓝[>] 0) (𝓝 (T v)) := by
    simpa using hcoef.smul_const (T v)
  exact (hF.sub hR).congr fun ε => rfl

/-! ## Anomaly histories in the boundary corona -/

omit [CompleteSpace H] in
theorem norm_residualCoefficient_smul_le (T : H →L[ℂ] H) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ‖(c / (ε + c)) • T‖ ≤ ‖T‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (by positivity)).2 (by linarith))

/-- The residual history `ε ↦ c/(ε+c) T` in `C_b((0,1], K(H))`. -/
def residualHistory (T : H →L[ℂ] H) (hcpt : IsCompactOperator T) {c : ℝ} (hc : 0 < c) :
    ApertureHistory H :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ε => CompactOps.mk ((c / ((ε : ℝ) + c)) • T) (hcpt.smul _),
      by
        refine continuous_iff_continuousAt.2 fun ε => ?_
        refine Metric.tendsto_nhds.2 fun r hr => ?_
        have hcont : ContinuousAt (fun η : ℝ => (c / (η + c)) • T) ε :=
          (continuousAt_const.div (continuousAt_id.add continuousAt_const)
            (ne_of_gt (add_pos ε.2.1 hc))).smul continuousAt_const
        have hev := (Metric.tendsto_nhds.1 hcont) r hr
        filter_upwards [(continuous_subtype_val.tendsto ε).eventually hev] with η hη
        exact hη⟩
    (2 * ‖T‖) fun ε η => by
      calc dist _ _ ≤ ‖CompactOps.mk ((c / ((ε : ℝ) + c)) • T) (hcpt.smul _)‖ +
            ‖CompactOps.mk ((c / ((η : ℝ) + c)) • T) (hcpt.smul _)‖ := dist_le_norm_add_norm _ _
        _ ≤ ‖T‖ + ‖T‖ := add_le_add (norm_residualCoefficient_smul_le T hc ε.2.1) (norm_residualCoefficient_smul_le T hc η.2.1)
        _ = 2 * ‖T‖ := by ring

/-- The anomaly history `ε ↦ 𝒜_{ε,c}(T)`. -/
def anomalyHistory (T : H →L[ℂ] H) (hT : T.IsPositive) (hcpt : IsCompactOperator T) {c : ℝ}
    (hc : 0 < c) : ApertureHistory H :=
  transferHistory (c • T) (isPositive_real_smul hT hc.le) (hcpt.smul c) - residualHistory T hcpt hc

theorem anomalyHistory_apply (T : H →L[ℂ] H) (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    {c : ℝ} (hc : 0 < c) (ε : Aperture) :
    (anomalyHistory T hT hcpt hc ε).op = interchangeAnomaly T c ε := rfl

theorem residualHistory_sub_mem (T : H →L[ℂ] H) (hcpt : IsCompactOperator T) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    residualHistory T hcpt hc - residualHistory T hcpt hd ∈ vanishingHistories H := by
  change Tendsto (fun ε => ‖(residualHistory T hcpt hc - residualHistory T hcpt hd) ε‖)
    apertureClosing (𝓝 0)
  have heq : ∀ ε : Aperture, ‖(residualHistory T hcpt hc - residualHistory T hcpt hd) ε‖ =
      |c / ((ε : ℝ) + c) - d / ((ε : ℝ) + d)| * ‖T‖ := fun ε => by
    change ‖(c / ((ε : ℝ) + c)) • T - (d / ((ε : ℝ) + d)) • T‖ = _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  simp_rw [heq]
  have hcont : ContinuousAt (fun ε : ℝ => |c / (ε + c) - d / (ε + d)| * ‖T‖) 0 :=
    (((continuousAt_const.div (continuousAt_id.add continuousAt_const)
      (by simpa using hc.ne')).sub (continuousAt_const.div (continuousAt_id.add continuousAt_const)
        (by simpa using hd.ne'))).abs).mul continuousAt_const
  have h0 : |c / (0 + c) - d / (0 + d)| * ‖T‖ = 0 := by
    rw [zero_add, zero_add, div_self hc.ne', div_self hd.ne', sub_self, abs_zero, zero_mul]
  have hlim := hcont.tendsto
  rw [h0] at hlim
  exact (hlim.mono_left nhdsWithin_le_nhds).comp tendsto_comap

/-- In the boundary corona the anomaly germ differs from the scale germ by a vanishing history. -/
theorem anomalyGerm_sub_eq_scaleGerm_sub {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hcpt : IsCompactOperator T) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (anomalyHistory T hT hcpt hc : BoundaryCorona H) - anomalyHistory T hT hcpt hd =
      scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd := by
  have h0 : ((residualHistory T hcpt hc : BoundaryCorona H) - residualHistory T hcpt hd) = 0 := by
    rw [← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
    exact residualHistory_sub_mem T hcpt hc hd
  rw [anomalyHistory, anomalyHistory, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, scaleGerm,
    scaleGerm]
  rw [show ∀ a b r₁ r₂ : BoundaryCorona H, (a - r₁) - (b - r₂) = (a - b) - (r₁ - r₂) from
    fun _ _ _ _ => by abel, h0, sub_zero]

/-- **Theorem PBTIA-B, (PBTIA.13).**  `‖[𝒜_{•,c}] - [𝒜_{•,d}]‖ = |√c - √d|/(√c + √d)`. -/
theorem norm_anomalyGerm_sub {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) :
    ‖(anomalyHistory T hT hcpt hc : BoundaryCorona H) - anomalyHistory T hT hcpt hd‖ =
      |germContrast c d| := by
  rw [anomalyGerm_sub_eq_scaleGerm_sub hT hcpt hc hd, norm_scaleGerm_sub hT hcpt hinj hH hc hd]

/-- **(PBTIA.14).**  Two anomaly germs agree iff the scales agree. -/
theorem anomalyGerm_eq_iff {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) :
    (anomalyHistory T hT hcpt hc : BoundaryCorona H) = anomalyHistory T hT hcpt hd ↔ c = d := by
  constructor
  · intro h
    have h0 := norm_anomalyGerm_sub hT hcpt hinj hH hc hd
    rwa [h, sub_self, norm_zero, eq_comm, abs_eq_zero,
      germContrast_eq_zero_iff hc.le hd.le (by positivity)] at h0
  · rintro rfl
    rfl

/-- **(PBTIA.19)–(PBTIA.20).**  A polarization has the fixed theta anomaly germ `[𝒜_{•,1}]` iff
`c = 1`. -/
theorem anomalyGerm_eq_theta_iff {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) {c : ℝ} (hc : 0 < c) :
    (anomalyHistory T hT hcpt hc : BoundaryCorona H) = anomalyHistory T hT hcpt one_pos ↔
      c = 1 :=
  anomalyGerm_eq_iff hT hcpt hinj hH hc one_pos

/-- **(PBTIA.17).**  For direct/reflected scales `pᵃ`, `p⁻ᵃ`, the oriented anomaly distance is
`(pᵃ-1)/(pᵃ+1) = tanh(a log p/2)`. -/
theorem germContrast_rpow_reflection {p : ℝ} (hp : 0 < p) (a : ℝ) :
    germContrast (p ^ a) (p ^ (-a)) = (p ^ a - 1) / (p ^ a + 1) ∧
      germContrast (p ^ a) (p ^ (-a)) = Real.tanh (a * Real.log p / 2) := by
  have hA : 0 < p ^ a := Real.rpow_pos_of_pos hp a
  have hs : Real.sqrt (p ^ a) = Real.exp (a * Real.log p / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq hA.le (Real.exp_pos _).le, ← Real.exp_add,
      show a * Real.log p / 2 + a * Real.log p / 2 = Real.log p * a by ring,
      Real.rpow_def_of_pos hp]
  have hs' : Real.sqrt (p ^ (-a)) = Real.exp (-(a * Real.log p / 2)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.rpow_pos_of_pos hp _).le (Real.exp_pos _).le,
      ← Real.exp_add, show -(a * Real.log p / 2) + -(a * Real.log p / 2) = Real.log p * (-a) by
        ring, Real.rpow_def_of_pos hp]
  have hexp : Real.exp (a * Real.log p / 2) * Real.exp (a * Real.log p / 2) = p ^ a := by
    rw [← Real.exp_add, show a * Real.log p / 2 + a * Real.log p / 2 = Real.log p * a by ring,
      Real.rpow_def_of_pos hp]
  have he := Real.exp_pos (a * Real.log p / 2)
  have hkey : germContrast (p ^ a) (p ^ (-a)) = Real.tanh (a * Real.log p / 2) := by
    rw [germContrast, hs, hs', Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    field_simp
  refine ⟨?_, hkey⟩
  rw [hkey, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← hexp]
  field_simp

/-- **(PBTIA.21).**  Functional-equation invariance of the anomaly germ forces `a = 0`. -/
theorem anomalyGerm_rpow_reflection_iff {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hcpt : IsCompactOperator T) (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H)
    {p : ℝ} (hp : 1 < p) (a : ℝ) :
    (anomalyHistory T hT hcpt (Real.rpow_pos_of_pos (zero_lt_one.trans hp) a) : BoundaryCorona H) =
        anomalyHistory T hT hcpt (Real.rpow_pos_of_pos (zero_lt_one.trans hp) (-a)) ↔ a = 0 := by
  rw [anomalyGerm_eq_iff hT hcpt hinj hH, Real.rpow_right_inj (zero_lt_one.trans hp) hp.ne']
  constructor
  · intro h
    linarith
  · rintro rfl
    simp

end GaloisForLFunctions.HTGeometry
